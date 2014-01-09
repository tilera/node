// Copyright 2012 the V8 project authors. All rights reserved.
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above
//       copyright notice, this list of conditions and the following
//       disclaimer in the documentation and/or other materials provided
//       with the distribution.
//     * Neither the name of Google Inc. nor the names of its
//       contributors may be used to endorse or promote products derived
//       from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#include <limits.h>  // For LONG_MIN, LONG_MAX.

#include "v8.h"

#if defined(V8_TARGET_ARCH_TILEGX)

#include "bootstrapper.h"
#include "codegen.h"
#include "debug.h"
#include "runtime.h"

namespace v8 {
namespace internal {

MacroAssembler::MacroAssembler(Isolate* arg_isolate, void* buffer, int size)
    : Assembler(arg_isolate, buffer, size),
      generating_stub_(false),
      allow_stub_calls_(true),
      has_frame_(false) {
  if (isolate() != NULL) {
    code_object_ = Handle<Object>(isolate()->heap()->undefined_value(),
                                  isolate());
  }
}

void MacroAssembler::LoadRoot(Register destination,
                              Heap::RootListIndex index) {
  ld(destination, MemOperand(kRootRegister, index << kPointerSizeLog2));
}


void MacroAssembler::LoadRoot(Register destination,
                              Heap::RootListIndex index,
                              Condition cond,
                              Register src1, const Operand& src2) {
  Branch(3, NegateCondition(cond), src1, src2);
  ld(destination, MemOperand(s6, index << kPointerSizeLog2));
}

void MacroAssembler::StoreRoot(Register source,
                               Heap::RootListIndex index) {
  st(source, MemOperand(s6, index << kPointerSizeLog2));
}

void MacroAssembler::StoreRoot(Register source,
                               Heap::RootListIndex index,
                               Condition cond,
                               Register src1, const Operand& src2) {
  Branch(3, NegateCondition(cond), src1, src2);
  st(source, MemOperand(s6, index << kPointerSizeLog2));
}

void MacroAssembler::LoadHeapObject(Register result,
                                    Handle<HeapObject> object) {
  ALLOW_HANDLE_DEREF(isolate(), "using raw address");
  if (isolate()->heap()->InNewSpace(*object)) {
    Handle<JSGlobalPropertyCell> cell =
        isolate()->factory()->NewJSGlobalPropertyCell(object);
    li(result, Operand(cell));
    ld(result, FieldMemOperand(result, JSGlobalPropertyCell::kValueOffset));
  } else {
    li(result, Operand(object));
  }
}

// Push and pop all registers that can hold pointers.
void MacroAssembler::PushSafepointRegisters() {
  // Safepoints expect a block of kNumSafepointRegisters values on the
  // stack, so adjust the stack for unsaved registers.
  const int num_unsaved = kNumSafepointRegisters - kNumSafepointSavedRegisters;
  ASSERT(num_unsaved >= 0);
  if (num_unsaved > 0) {
    Subu(sp, sp, Operand(num_unsaved * kPointerSize));
  }
  MultiPush(kSafepointSavedRegisters);
}

void MacroAssembler::PopSafepointRegisters() {
  const int num_unsaved = kNumSafepointRegisters - kNumSafepointSavedRegisters;
  MultiPop(kSafepointSavedRegisters);
  if (num_unsaved > 0) {
    Addu(sp, sp, Operand(num_unsaved * kPointerSize));
  }
}

void MacroAssembler::PushSafepointRegistersAndDoubles() { UNREACHABLE(); }


void MacroAssembler::PopSafepointRegistersAndDoubles() { UNREACHABLE(); }


void MacroAssembler::StoreToSafepointRegistersAndDoublesSlot(Register src,
                                                             Register dst) {
  st(src, SafepointRegistersAndDoublesSlot(dst));
}

void MacroAssembler::StoreToSafepointRegisterSlot(Register src, Register dst) {
  st(src, SafepointRegisterSlot(dst));
}

void MacroAssembler::LoadFromSafepointRegisterSlot(Register dst, Register src) {
  ld(dst, SafepointRegisterSlot(src));
}

int MacroAssembler::SafepointRegisterStackIndex(int reg_code) {
  return kSafepointRegisterStackIndexMap[reg_code];
}

MemOperand MacroAssembler::SafepointRegisterSlot(Register reg) {
  return MemOperand(sp, SafepointRegisterStackIndex(reg.code()) * kPointerSize);
}

MemOperand MacroAssembler::SafepointRegistersAndDoublesSlot(Register reg) { UNREACHABLE(); return MemOperand(fp); }


void MacroAssembler::InNewSpace(Register object,
                                Register scratch,
                                Condition cc,
                                Label* branch) {
  ASSERT(cc == eq || cc == ne);
  And(scratch, object, Operand(ExternalReference::new_space_mask(isolate())));
  Branch(branch, cc, scratch,
         Operand(ExternalReference::new_space_start(isolate())));
}


void MacroAssembler::RecordWriteField(
    Register object,
    int offset,
    Register value,
    Register dst,
    RAStatus ra_status,
    SaveFPRegsMode save_fp,
    RememberedSetAction remembered_set_action,
    SmiCheck smi_check) {
  ASSERT(!AreAliased(value, dst, t8, object));
  // First, check if a write barrier is even needed. The tests below
  // catch stores of Smis.
  Label done;

  // Skip barrier if writing a smi.
  if (smi_check == INLINE_SMI_CHECK) {
    JumpIfSmi(value, &done);
  }

  // Although the object register is tagged, the offset is relative to the start
  // of the object, so so offset must be a multiple of kPointerSize.
  ASSERT(IsAligned(offset, kPointerSize));

  Addu(dst, object, Operand(offset - kHeapObjectTag));
  if (emit_debug_code()) {
    Label ok;
    And(t8, dst, Operand((1 << kPointerSizeLog2) - 1));
    Branch(&ok, eq, t8, Operand(zero));
    stop("Unaligned cell in write barrier");
    bind(&ok);
  }

  RecordWrite(object,
              dst,
              value,
              ra_status,
              save_fp,
              remembered_set_action,
              OMIT_SMI_CHECK);

  bind(&done);

  // Clobber clobbered input registers when running with the debug-code flag
  // turned on to provoke errors.
  if (emit_debug_code()) {
    li(value, Operand(BitCast<int64_t>(kZapValue + 4)));
    li(dst, Operand(BitCast<int64_t>(kZapValue + 8)));
  }
}


// Will clobber 4 registers: object, address, scratch, ip.  The
// register 'object' contains a heap object pointer.  The heap object
// tag is shifted away.
void MacroAssembler::RecordWrite(Register object,
                                 Register address,
                                 Register value,
                                 RAStatus ra_status,
                                 SaveFPRegsMode fp_mode,
                                 RememberedSetAction remembered_set_action,
                                 SmiCheck smi_check) {
  ASSERT(!AreAliased(object, address, value, t8));
  ASSERT(!AreAliased(object, address, value, t9));
  // The compiled code assumes that record write doesn't change the
  // context register, so we check that none of the clobbered
  // registers are cp.
  ASSERT(!address.is(cp) && !value.is(cp));

  if (emit_debug_code()) {
    ld(at, MemOperand(address));
    Assert(
        eq, "Wrong address or value passed to RecordWrite", at, Operand(value));
  }

  Label done;

  if (smi_check == INLINE_SMI_CHECK) {
    ASSERT_EQ(0, kSmiTag);
    JumpIfSmi(value, &done);
  }

  CheckPageFlag(value,
                value,  // Used as scratch.
                MemoryChunk::kPointersToHereAreInterestingMask,
                eq,
                &done);
  CheckPageFlag(object,
                value,  // Used as scratch.
                MemoryChunk::kPointersFromHereAreInterestingMask,
                eq,
                &done);

  // Record the actual write.
  if (ra_status == kRAHasNotBeenSaved) {
    push(ra);
  }
  RecordWriteStub stub(object, value, address, remembered_set_action, fp_mode);
  CallStub(&stub);
  if (ra_status == kRAHasNotBeenSaved) {
    pop(ra);
  }

  bind(&done);

  // Clobber clobbered registers when running with the debug-code flag
  // turned on to provoke errors.
  if (emit_debug_code()) {
    li(address, Operand(BitCast<int64_t>(kZapValue + 12)));
    li(value, Operand(BitCast<int64_t>(kZapValue + 16)));
  }
}

void MacroAssembler::RememberedSetHelper(Register object,  // For debug tests.
                                         Register address,
                                         Register scratch,
                                         SaveFPRegsMode fp_mode,
                                         RememberedSetFinalAction and_then) {
  Label done;
  if (emit_debug_code()) {
    Label ok;
    JumpIfNotInNewSpace(object, scratch, &ok);
    stop("Remembered set pointer is in new space");
    bind(&ok);
  }
  // Load store buffer top.
  ExternalReference store_buffer =
      ExternalReference::store_buffer_top(isolate());
  li(t8, Operand(store_buffer));
  ld(scratch, MemOperand(t8));
  // Store pointer to buffer and increment buffer top.
  st(address, MemOperand(scratch));
  Addu(scratch, scratch, kPointerSize);
  // Write back new top of buffer.
  st(scratch, MemOperand(t8));
  // Call stub on end of buffer.
  // Check for end of buffer.
  And(t8, scratch, Operand(StoreBuffer::kStoreBufferOverflowBit));
  if (and_then == kFallThroughAtEnd) {
    Branch(&done, eq, t8, Operand(zero));
  } else {
    ASSERT(and_then == kReturnAtEnd);
    Ret(eq, t8, Operand(zero));
  }
  push(lr);
  StoreBufferOverflowStub store_buffer_overflow =
      StoreBufferOverflowStub(fp_mode);
  CallStub(&store_buffer_overflow);
  pop(lr);
  bind(&done);
  if (and_then == kReturnAtEnd) {
    Ret();
  }
}


// -----------------------------------------------------------------------------
// Allocation support.


void MacroAssembler::CheckAccessGlobalProxy(Register holder_reg,
                                            Register scratch,
                                            Label* miss) {
  Label same_contexts;

  ASSERT(!holder_reg.is(scratch));
  ASSERT(!holder_reg.is(at));
  ASSERT(!scratch.is(at));

  // Load current lexical context from the stack frame.
  ld(scratch, MemOperand(fp, StandardFrameConstants::kContextOffset));
  // In debug mode, make sure the lexical context is set.
#ifdef DEBUG
  Check(ne, "we should not have an empty lexical context",
      scratch, Operand(zero));
#endif

  // Load the native context of the current context.
  int offset =
      Context::kHeaderSize + Context::GLOBAL_OBJECT_INDEX * kPointerSize;
  ld(scratch, FieldMemOperand(scratch, offset));
  ld(scratch, FieldMemOperand(scratch, GlobalObject::kNativeContextOffset));

  // Check the context is a native context.
  if (emit_debug_code()) {
    push(holder_reg);  // Temporarily save holder on the stack.
    // Read the first word and compare to the native_context_map.
    ld(holder_reg, FieldMemOperand(scratch, HeapObject::kMapOffset));
    LoadRoot(at, Heap::kNativeContextMapRootIndex);
    Check(eq, "JSGlobalObject::native_context should be a native context.",
          holder_reg, Operand(at));
    pop(holder_reg);  // Restore holder.
  }

  // Check if both contexts are the same.
  ld(at, FieldMemOperand(holder_reg, JSGlobalProxy::kNativeContextOffset));
  Branch(&same_contexts, eq, scratch, Operand(at));

  // Check the context is a native context.
  if (emit_debug_code()) {
    push(holder_reg);  // Temporarily save holder on the stack.
    move(holder_reg, at);  // Move at to its holding place.
    LoadRoot(at, Heap::kNullValueRootIndex);
    Check(ne, "JSGlobalProxy::context() should not be null.",
          holder_reg, Operand(at));

    ld(holder_reg, FieldMemOperand(holder_reg, HeapObject::kMapOffset));
    LoadRoot(at, Heap::kNativeContextMapRootIndex);
    Check(eq, "JSGlobalObject::native_context should be a native context.",
          holder_reg, Operand(at));
    // Restore at is not needed. at is reloaded below.
    pop(holder_reg);  // Restore holder.
    // Restore at to holder's context.
    ld(at, FieldMemOperand(holder_reg, JSGlobalProxy::kNativeContextOffset));
  }

  // Check that the security token in the calling global object is
  // compatible with the security token in the receiving global
  // object.
  int token_offset = Context::kHeaderSize +
                     Context::SECURITY_TOKEN_INDEX * kPointerSize;

  move(at2, at);
  ld(scratch, FieldMemOperand(scratch, token_offset));
  move(at, at2);
  ld(at, FieldMemOperand(at, token_offset));
  Branch(miss, ne, scratch, Operand(at));

  bind(&same_contexts);
}


void MacroAssembler::GetNumberHash(Register reg0, Register scratch) {
  // First of all we assign the hash seed to scratch.
  LoadRoot(scratch, Heap::kHashSeedRootIndex);
  SmiUntag(scratch);

  // Xor original key with a seed.
  xor_(reg0, reg0, scratch);

  // Compute the hash code from the untagged key.  This must be kept in sync
  // with ComputeIntegerHash in utils.h.
  //
  // hash = ~hash + (hash << 15);
  nor(scratch, reg0, zero);
  sllx(at, reg0, 15);
  add(reg0, scratch, at);

  // hash = hash ^ (hash >> 12);
  srlx(at, reg0, 12);
  xor_(reg0, reg0, at);

  // hash = hash + (hash << 2);
  sllx(at, reg0, 2);
  add(reg0, reg0, at);

  // hash = hash ^ (hash >> 4);
  srlx(at, reg0, 4);
  xor_(reg0, reg0, at);

  // hash = hash * 2057;
  sllx(scratch, reg0, 11);
  sllx(at, reg0, 3);
  add(reg0, reg0, at);
  add(reg0, reg0, scratch);

  // hash = hash ^ (hash >> 16);
  srlx(at, reg0, 16);
  xor_(reg0, reg0, at);
}

void MacroAssembler::LoadFromNumberDictionary(Label* miss,
                                              Register elements,
                                              Register key,
                                              Register result,
                                              Register reg0,
                                              Register reg1,
                                              Register reg2) {
  // Register use:
  //
  // elements - holds the slow-case elements of the receiver on entry.
  //            Unchanged unless 'result' is the same register.
  //
  // key      - holds the smi key on entry.
  //            Unchanged unless 'result' is the same register.
  //
  //
  // result   - holds the result on exit if the load succeeded.
  //            Allowed to be the same as 'key' or 'result'.
  //            Unchanged on bailout so 'key' or 'result' can be used
  //            in further computation.
  //
  // Scratch registers:
  //
  // reg0 - holds the untagged key on entry and holds the hash once computed.
  //
  // reg1 - Used to hold the capacity mask of the dictionary.
  //
  // reg2 - Used for the index into the dictionary.
  // at   - Temporary (avoid MacroAssembler instructions also using 'at').
  Label done;

  GetNumberHash(reg0, reg1);

  // Compute the capacity mask.
  ld(reg1, FieldMemOperand(elements, SeededNumberDictionary::kCapacityOffset));
  sra(reg1, reg1, kSmiTagSize + kSmiShiftSize);
  Subu(reg1, reg1, Operand(1));

  // Generate an unrolled loop that performs a few probes before giving up.
  static const int kProbes = 4;
  for (int i = 0; i < kProbes; i++) {
    // Use reg2 for index calculations and keep the hash intact in reg0.
    move(reg2, reg0);
    // Compute the masked index: (hash + i + i * i) & mask.
    if (i > 0) {
      Addu(reg2, reg2, Operand(SeededNumberDictionary::GetProbeOffset(i)));
    }
    and_(reg2, reg2, reg1);

    // Scale the index by multiplying by the element size.
    ASSERT(SeededNumberDictionary::kEntrySize == 3);
    sll(at, reg2, 1);  // 2x.
    add(reg2, reg2, at);  // reg2 = reg2 * 3.

    // Check if the key is identical to the name.
    sll(at, reg2, kPointerSizeLog2);
    add(reg2, elements, at);

    ld(at, FieldMemOperand(reg2, SeededNumberDictionary::kElementsStartOffset));
    if (i != kProbes - 1) {
      Branch(&done, eq, key, Operand(at));
    } else {
      Branch(miss, ne, key, Operand(at));
    }
  }

  bind(&done);
  // Check that the value is a normal property.
  // reg2: elements + (index * kPointerSize).
  const int kDetailsOffset =
      SeededNumberDictionary::kElementsStartOffset + 2 * kPointerSize;
  ld(reg1, FieldMemOperand(reg2, kDetailsOffset));
  And(at, reg1, Operand(Smi::FromInt(PropertyDetails::TypeField::kMask)));
  Branch(miss, ne, at, Operand(zero));

  // Get the value at the masked, scaled index and return.
  const int kValueOffset =
      SeededNumberDictionary::kElementsStartOffset + kPointerSize;
  ld(result, FieldMemOperand(reg2, kValueOffset));
}


// ---------------------------------------------------------------------------
// Instruction macros.

void MacroAssembler::Addu(Register rd, Register rs, const Operand& rt) {
  if (rt.is_reg()) {
    add(rd, rs, rt.rm());
  } else {
    if (is_lintn(rt.imm64_, 16) && !MustUseReg(rt.rmode_)) {
      addli(rd, rs, rt.imm64_);
    } else {
      // li handles the relocation.
      ASSERT(!rs.is(at));
      li(at, rt);
      add(rd, rs, at);
    }
  }
}

void MacroAssembler::Subu(Register rd, Register rs, const Operand& rt) 
{
  if (rt.is_reg()) {
    sub(rd, rs, rt.rm());
  } else {
    if (is_lintn(rt.imm64_, 16) && !MustUseReg(rt.rmode_)) {
      addli(rd, rs, -rt.imm64_);
    } else {
      // li handles the relocation.
      ASSERT(!rs.is(at));
      li(at, rt);
      sub(rd, rs, at);
    }
  }
}

void MacroAssembler::Mul(Register rd, Register rs, const Operand& rt) {
  //FIXME
  if (rt.is_reg()) {
    mulx(rd, rs, rt.rm());
  } else {
    // li handles the relocation.
    ASSERT(!rs.is(at));
    li(at, rt);
    mulx(rd, rs, at);
  }
}

void MacroAssembler::Mult(Register rs, const Operand& rt) { UNREACHABLE(); }


void MacroAssembler::Multu(Register rs, const Operand& rt) { UNREACHABLE(); }


void MacroAssembler::Div(Register rs, const Operand& rt) { UNREACHABLE(); }


void MacroAssembler::Divu(Register rs, const Operand& rt) { UNREACHABLE(); }


void MacroAssembler::And(Register rd, Register rs, const Operand& rt) {
  if (rt.is_reg()) {
    and_(rd, rs, rt.rm());
  } else {
    if (is_lintn(rt.imm64_, 8) && !MustUseReg(rt.rmode_)) {
      andi(rd, rs, rt.imm64_);
    } else {
      // li handles the relocation.
      ASSERT(!rs.is(at));
      li(at, rt);
      and_(rd, rs, at);
    }
  }
}


void MacroAssembler::Or(Register rd, Register rs, const Operand& rt) {
  if (rt.is_reg()) {
    or_(rd, rs, rt.rm());
  } else {
    if (is_lintn(rt.imm64_, 8) && !MustUseReg(rt.rmode_)) {
      ori(rd, rs, rt.imm64_);
    } else {
      // li handles the relocation.
      ASSERT(!rs.is(at));
      li(at, rt);
      or_(rd, rs, at);
    }
  }
}


void MacroAssembler::Xor(Register rd, Register rs, const Operand& rt) {
  if (rt.is_reg()) {
    xor_(rd, rs, rt.rm());
  } else {
    if (is_lintn(rt.imm64_, 8) && !MustUseReg(rt.rmode_)) {
      xori(rd, rs, rt.imm64_);
    } else {
      // li handles the relocation.
      ASSERT(!rs.is(at));
      li(at, rt);
      xor_(rd, rs, at);
    }
  }
}


void MacroAssembler::Nor(Register rd, Register rs, const Operand& rt) {
  if (rt.is_reg()) {
    nor(rd, rs, rt.rm());
  } else {
    // li handles the relocation.
    ASSERT(!rs.is(at));
    li(at, rt);
    nor(rd, rs, at);
  }
}

void MacroAssembler::Neg(Register rs, const Operand& rt) {
  ASSERT(rt.is_reg());
  ASSERT(!at.is(rs));
  ASSERT(!at.is(rt.rm()));
  li(at, -1);
  xor_(rs, rt.rm(), at);
}

void MacroAssembler::Slt(Register rd, Register rs, const Operand& rt) { UNREACHABLE(); }


void MacroAssembler::Sltu(Register rd, Register rs, const Operand& rt) { UNREACHABLE(); }


void MacroAssembler::Ror(Register rd, Register rs, const Operand& rt) { UNREACHABLE(); }

//------------Pseudo-instructions-------------

void MacroAssembler::li(Register rd, Operand j, int line, LiFlags mode) {
  ASSERT(!j.is_reg());
  if (MustUseReg(j.rmode_)) {
    RecordRelocInfo(j.rmode_, j.imm64_);
  }

  if (j.rmode_ == RelocInfo::EMBEDDED_OBJECT) {
    moveli(rd, (j.imm64_ >> 32) & 0xFFFF, line);
    shl16insli(rd, rd, (j.imm64_ >> 16) & 0xFFFF, line);
    shl16insli(rd, rd, j.imm64_ & 0xFFFF, line);
    return;
  }

  if (is_lintn(j.imm64_, 48)) {
    moveli(rd, (j.imm64_ >> 32) & 0xFFFF, line);
    shl16insli(rd, rd, (j.imm64_ >> 16) & 0xFFFF, line);
    shl16insli(rd, rd, j.imm64_ & 0xFFFF, line);
  } else {
    moveli(rd, (j.imm64_ >> 48) & 0xFFFF, line);
    shl16insli(rd, rd, (j.imm64_ >> 32) & 0xFFFF, line);
    shl16insli(rd, rd, (j.imm64_ >> 16) & 0xFFFF, line);
    shl16insli(rd, rd, j.imm64_ & 0xFFFF, line);
  }
}


void MacroAssembler::MultiPush(RegList regs) {
  int16_t num_to_push = NumberOfBitsSet(regs);
  int16_t stack_offset = num_to_push * kPointerSize;

  Subu(sp, sp, Operand(stack_offset));
  for (int16_t i = kNumRegisters - 1; i >= 0; i--) {
    if ((regs & (1L << i)) != 0) {
      stack_offset -= kPointerSize;
      st(ToRegister(i), MemOperand(sp, stack_offset));
    }
  }
}


void MacroAssembler::MultiPushReversed(RegList regs) {
  int16_t num_to_push = NumberOfBitsSet(regs);
  int16_t stack_offset = num_to_push * kPointerSize;

  Subu(sp, sp, Operand(stack_offset));
  for (int16_t i = 0; i < kNumRegisters; i++) {
    if ((regs & (1L << i)) != 0) {
      stack_offset -= kPointerSize;
      st(ToRegister(i), MemOperand(sp, stack_offset));
    }
  }
}


void MacroAssembler::MultiPop(RegList regs) {
  int16_t stack_offset = 0;

  for (int16_t i = 0; i < kNumRegisters; i++) {
    if ((regs & (1L << i)) != 0) {
      ld(ToRegister(i), MemOperand(sp, stack_offset));
      stack_offset += kPointerSize;
    }
  }
  addli(sp, sp, stack_offset);
}

void MacroAssembler::MultiPopReversed(RegList regs) { UNREACHABLE(); }


void MacroAssembler::MultiPushFPU(RegList regs) { UNREACHABLE(); }


void MacroAssembler::MultiPushReversedFPU(RegList regs) { UNREACHABLE(); }


void MacroAssembler::MultiPopFPU(RegList regs) { UNREACHABLE(); }


void MacroAssembler::MultiPopReversedFPU(RegList regs) { UNREACHABLE(); }


void MacroAssembler::FlushICache(Register address, unsigned instructions) { UNREACHABLE(); }

void MacroAssembler::Jalr(Label* L) {
  BlockTrampolinePoolScope block_trampoline_pool(this);

  uint64_t imm64;
  imm64 = jump_address(L);
  { BlockGrowBufferScope block_buf_growth(this);
    // Buffer growth (and relocation) must be blocked for internal references
    // until associated instructions are emitted and available to be patched.
    RecordRelocInfo(RelocInfo::INTERNAL_REFERENCE);
    moveli(at, (imm64 >> 32) & 0xFFFF);
    shl16insli(at, at, (imm64 >> 16) & 0xFFFF);
    shl16insli(at, at, imm64 & 0xFFFF);
  }
  jalr(at);
}

void MacroAssembler::J(Label* L) {
  BlockTrampolinePoolScope block_trampoline_pool(this);

  { BlockGrowBufferScope block_buf_growth(this);
    // Buffer growth (and relocation) must be blocked for internal references
    // until associated instructions are emitted and available to be patched.
    RecordRelocInfo(RelocInfo::INTERNAL_REFERENCE);
    j(shifted_branch_offset(L, true));
  }
}

void MacroAssembler::Jr(Label* L) {

  uint64_t imm64 = jump_address(L);
  {
    // Buffer growth (and relocation) must be blocked for internal references
    // until associated instructions are emitted and available to be patched.
    RecordRelocInfo(RelocInfo::INTERNAL_REFERENCE);
    moveli(at, (imm64 >> 32) & 0xFFFF);
    shl16insli(at, at, (imm64 >> 16) & 0xFFFF);
    shl16insli(at, at, imm64 & 0xFFFF);
  }
  jr(at);
}

// Emulated condtional branches do not emit a nop in the branch delay slot.
//
// BRANCH_ARGS_CHECK checks that conditional jump arguments are correct.
#define BRANCH_ARGS_CHECK(cond, rs, rt) ASSERT(                        \
    (cond == cc_always && rs.is(zero) && rt.rm().is(zero)) ||          \
    (cond != cc_always && (!rs.is(zero) || !rt.rm().is(zero))))


void MacroAssembler::Branch(int16_t offset) {
  b(offset);
}


void MacroAssembler::Branch(int16_t offset, Condition cond, Register rs,
                            const Operand& rt) {
  BranchShort(offset, cond, rs, rt);
}


void MacroAssembler::Branch(Label* L) {
  if (L->is_bound()) {
    if (is_near(L)) {
      BranchShort(L);
    } else {
      Jr(L);
    }
  } 
  
  BranchShort(L);
}

void MacroAssembler::Branch(Label* L, Condition cond, Register rs,
                            const Operand& rt) {
  if (L->is_bound()) {
    if (is_near(L)) {
      BranchShort(L, cond, rs, rt);
    } else {
      Label skip;
      Condition neg_cond = NegateCondition(cond);
      BranchShort(&skip, neg_cond, rs, rt);
      Jr(L);
      bind(&skip);
    }
  } else
    BranchShort(L, cond, rs, rt);
}

void MacroAssembler::BranchShort(int16_t offset) {
  b(offset);
}

void MacroAssembler::BranchShort(Label* L) {
  // We use branch_offset as an argument for the branch instructions to be sure
  // it is called just before generating the branch instruction, as needed.
  b(shifted_branch_offset(L));
}

void MacroAssembler::BranchShort(int16_t offset, Condition cond, Register rs,
                                 const Operand& rt) {
  BRANCH_ARGS_CHECK(cond, rs, rt);
  ASSERT(!rs.is(zero));
  Register r2 = no_reg;
  Register scratch = at2;

  if (rt.is_reg()) {
    // NOTE: 'at' can be clobbered by Branch but it is legal to use it as rs or
    // rt.
    BlockTrampolinePoolScope block_trampoline_pool(this);
    r2 = rt.rm_;
    switch (cond) {
      case cc_always:
        b(offset);
        break;
      case eq:
        if (r2.is(zero)) {
          beqz(rs, offset);
        } else {
          cmpeq(scratch, r2, rs);
          bnez(scratch, offset);
        }
        break;
      case ne:
        if (r2.is(zero)) {
          bnez(rs, offset);
        } else {
          cmpne(scratch, r2, rs);
          bnez(scratch, offset);
        }
        break;
      // Signed comparison.
      case greater:
        if (r2.is(zero)) {
          bgtz(rs, offset);
        } else {
          cmplts(scratch, r2, rs);
          bnez(scratch, offset);
        }
        break;
      case greater_equal:
        if (r2.is(zero)) {
          bgez(rs, offset);
        } else {
          cmplts(scratch, rs, r2);
          beqz(scratch, offset);
        }
        break;
      case less:
        if (r2.is(zero)) {
          bltz(rs, offset);
        } else {
          cmplts(scratch, rs, r2);
          bnez(scratch, offset);
        }
        break;
      case less_equal:
        if (r2.is(zero)) {
          blez(rs, offset);
        } else {
          cmplts(scratch, r2, rs);
          beqz(scratch, offset);
        }
        break;
      // Unsigned comparison.
      case Ugreater:
        if (r2.is(zero)) {
          bgtz(rs, offset);
        } else {
          cmpltu(scratch, r2, rs);
          bnez(scratch, offset);
        }
        break;
      case Ugreater_equal:
        if (r2.is(zero)) {
          bgez(rs, offset);
        } else {
          cmpltu(scratch, rs, r2);
          beqz(scratch, offset);
        }
        break;
      case Uless:
        if (r2.is(zero)) {
          // No code needs to be emitted.
          return;
        } else {
          cmpltu(scratch, rs, r2);
          bnez(scratch, offset);
        }
        break;
      case Uless_equal:
        if (r2.is(zero)) {
          b(offset);
        } else {
          cmpltu(scratch, r2, rs);
          beqz(scratch, offset);
        }
        break;
      default:
        UNREACHABLE();
    }
  } else {
    // Be careful to always use shifted_branch_offset only just before the
    // branch instruction, as the location will be remember for patching the
    // target.
    BlockTrampolinePoolScope block_trampoline_pool(this);
    switch (cond) {
      case cc_always:
        b(offset);
        break;
      case eq:
        // We don't want any other register but scratch clobbered.
        if (rt.imm64_ == 0) {
          beqz(rs, offset);
        } else {
          ASSERT(!scratch.is(rs));
          r2 = scratch;
          li(r2, rt);
	  cmpeq(scratch, rs, r2);
          bnez(scratch, offset);
        }
        break;
      case ne:
        // We don't want any other register but scratch clobbered.
        if (rt.imm64_ == 0) {
          bnez(rs, offset);
        } else {
          ASSERT(!scratch.is(rs));
          r2 = scratch;
          li(r2, rt);
	  cmpne(scratch, rs, r2);
          bnez(scratch, offset);
        }
        break;
      // Signed comparison.
      case greater:
        if (rt.imm64_ == 0) {
          bgtz(rs, offset);
        } else {
          r2 = scratch;
          li(r2, rt);
          cmplts(scratch, r2, rs);
          bnez(scratch, offset);
        }
        break;
      case greater_equal:
        if (rt.imm64_ == 0) {
          bgez(rs, offset);
        } else if (is_lintn(rt.imm64_, 8)) {
          cmpltsi(scratch, rs, rt.imm64_);
          beqz(scratch, offset);
        } else {
          r2 = scratch;
          li(r2, rt);
          cmplts(scratch, rs, r2);
          beqz(scratch, offset);
        }
        break;
      case less:
        if (rt.imm64_ == 0) {
          bltz(rs, offset);
        } else if (is_lintn(rt.imm64_, 8)) {
          cmpltsi(scratch, rs, rt.imm64_);
          bnez(scratch, offset);
        } else {
          r2 = scratch;
          li(r2, rt);
          cmplts(scratch, rs, r2);
          bnez(scratch, offset);
        }
        break;
      case less_equal:
        if (rt.imm64_ == 0) {
          blez(rs, offset);
        } else {
          r2 = scratch;
          li(r2, rt);
          cmplts(scratch, r2, rs);
          beqz(scratch, offset);
       }
       break;
      // Unsigned comparison.
      case Ugreater:
        if (rt.imm64_ == 0) {
          bgtz(rs, offset);
        } else {
          r2 = scratch;
          li(r2, rt);
          cmpltu(scratch, r2, rs);
          bnez(scratch, offset);
        }
        break;
      case Ugreater_equal:
        if (rt.imm64_ == 0) {
          bgez(rs, offset);
        } else if (is_lintn(rt.imm64_, 8)) {
          cmpltui(scratch, rs, rt.imm64_);
          beqz(scratch, offset);
        } else {
          r2 = scratch;
          li(r2, rt);
          cmpltu(scratch, rs, r2);
          beqz(scratch, offset);
        }
        break;
      case Uless:
        if (rt.imm64_ == 0) {
          // No code needs to be emitted.
          return;
        } else if (is_lintn(rt.imm64_, 8)) {
          cmpltui(scratch, rs, rt.imm64_);
          bnez(scratch, offset);
        } else {
          r2 = scratch;
          li(r2, rt);
          cmpltu(scratch, rs, r2);
          bnez(scratch, offset);
        }
        break;
      case Uless_equal:
        if (rt.imm64_ == 0) {
          b(offset);
        } else {
          r2 = scratch;
          li(r2, rt);
          cmpltu(scratch, r2, rs);
          beqz(scratch, offset);
        }
        break;
      default:
        UNREACHABLE();
    }
  }
}

void MacroAssembler::BranchShort(Label* L, Condition cond, Register rs,
                                 const Operand& rt) {
  BRANCH_ARGS_CHECK(cond, rs, rt);

  int32_t offset = 0;
  Register r2 = no_reg;
  Register scratch = at2;
  if (rt.is_reg()) {
    r2 = rt.rm_;
    // Be careful to always use shifted_branch_offset only just before the
    // branch instruction, as the location will be remember for patching the
    // target.
    switch (cond) {
      case cc_always:
        offset = shifted_branch_offset(L);
        b(offset);
        break;
      case eq:
        if (r2.is(zero)) {
          offset = shifted_branch_offset(L);
          beqz(rs, offset);
	} else {
          cmpeq(scratch, r2, rs);
          offset = shifted_branch_offset(L);
          bnez(scratch, offset);
	}
        break;
      case ne:
        if (r2.is(zero)) {
          offset = shifted_branch_offset(L);
          bnez(rs, offset);
	} else {
          cmpne(scratch, r2, rs);
          offset = shifted_branch_offset(L);
          bnez(scratch, offset);
	}
        break;
      // Signed comparison.
      case greater:
        if (r2.is(zero)) {
          offset = shifted_branch_offset(L);
          bgtz(rs, offset);
        } else {
          cmplts(scratch, r2, rs);
          offset = shifted_branch_offset(L);
          bnez(scratch, offset);
        }
        break;
      case greater_equal:
        if (r2.is(zero)) {
          offset = shifted_branch_offset(L);
          bgez(rs, offset);
        } else {
          cmplts(scratch, rs, r2);
          offset = shifted_branch_offset(L);
          beqz(scratch, offset);
        }
        break;
      case less:
        if (r2.is(zero)) {
          offset = shifted_branch_offset(L);
          bltz(rs, offset);
        } else {
          cmplts(scratch, rs, r2);
          offset = shifted_branch_offset(L);
          bnez(scratch, offset);
        }
        break;
      case less_equal:
        if (r2.is(zero)) {
          offset = shifted_branch_offset(L);
          blez(rs, offset);
        } else {
          cmplts(scratch, r2, rs);
          offset = shifted_branch_offset(L);
          beqz(scratch, offset);
        }
        break;
      // Unsigned comparison.
      case Ugreater:
        if (r2.is(zero)) {
          offset = shifted_branch_offset(L);
          bgtz(rs, offset);
        } else {
          cmpltu(scratch, r2, rs);
          offset = shifted_branch_offset(L);
          bnez(scratch, offset);
        }
        break;
      case Ugreater_equal:
        if (r2.is(zero)) {
          offset = shifted_branch_offset(L);
          bgez(rs, offset);
        } else {
          cmpltu(scratch, rs, r2);
          offset = shifted_branch_offset(L);
          beqz(scratch, offset);
        }
        break;
      case Uless:
        if (r2.is(zero)) {
          // No code needs to be emitted.
          return;
        } else {
          cmpltu(scratch, rs, r2);
          offset = shifted_branch_offset(L);
          bnez(scratch, offset);
        }
        break;
      case Uless_equal:
        if (r2.is(zero)) {
          offset = shifted_branch_offset(L);
          b(offset);
        } else {
          cmpltu(scratch, r2, rs);
          offset = shifted_branch_offset(L);
          beqz(scratch, offset);
        }
        break;
      default:
        UNREACHABLE();
    }
  } else {
    // Be careful to always use shifted_branch_offset only just before the
    // branch instruction, as the location will be remember for patching the
    // target.
    switch (cond) {
      case cc_always:
        offset = shifted_branch_offset(L);
        b(offset);
        break;
      case eq:
        if (rt.imm64_ == 0) {
          offset = shifted_branch_offset(L);
          beqz(rs, offset);
	} else {
          ASSERT(!scratch.is(rs));
          r2 = scratch;
          li(r2, rt);
	  cmpeq(scratch, rs, r2);
          offset = shifted_branch_offset(L);
          bnez(scratch, offset);
	}
        break;
      case ne:
        if (rt.imm64_ == 0) {
          offset = shifted_branch_offset(L);
          bnez(rs, offset);
	} else {
          ASSERT(!scratch.is(rs));
          r2 = scratch;
          li(r2, rt);
	  cmpne(scratch, rs, r2);
          offset = shifted_branch_offset(L);
          bnez(scratch, offset);
	}
        break;
      // Signed comparison.
      case greater:
        if (rt.imm64_ == 0) {
          offset = shifted_branch_offset(L);
          bgtz(rs, offset);
        } else {
          ASSERT(!scratch.is(rs));
          r2 = scratch;
          li(r2, rt);
          cmplts(scratch, r2, rs);
          offset = shifted_branch_offset(L);
          bnez(scratch, offset);
        }
        break;
      case greater_equal:
        if (rt.imm64_ == 0) {
          offset = shifted_branch_offset(L);
          bgez(rs, offset);
        } else if (is_lintn(rt.imm64_, 8)) {
          cmpltsi(scratch, rs, rt.imm64_);
          offset = shifted_branch_offset(L);
          beqz(scratch, offset);
        } else {
          ASSERT(!scratch.is(rs));
          r2 = scratch;
          li(r2, rt);
          cmplts(scratch, rs, r2);
          offset = shifted_branch_offset(L);
          beqz(scratch, offset);
        }
        break;
      case less:
        if (rt.imm64_ == 0) {
          offset = shifted_branch_offset(L);
          bltz(rs, offset);
        } else if (is_lintn(rt.imm64_, 8)) {
          cmpltsi(scratch, rs, rt.imm64_);
          offset = shifted_branch_offset(L);
          bnez(scratch, offset);
        } else {
          ASSERT(!scratch.is(rs));
          r2 = scratch;
          li(r2, rt);
          cmplts(scratch, rs, r2);
          offset = shifted_branch_offset(L);
          bnez(scratch, offset);
        }
        break;
      case less_equal:
        if (rt.imm64_ == 0) {
          offset = shifted_branch_offset(L);
          blez(rs, offset);
        } else {
          ASSERT(!scratch.is(rs));
          r2 = scratch;
          li(r2, rt);
          cmplts(scratch, r2, rs);
          offset = shifted_branch_offset(L);
          beqz(scratch, offset);
        }
        break;
      // Unsigned comparison.
      case Ugreater:
        if (rt.imm64_ == 0) {
          offset = shifted_branch_offset(L);
          bgtz(rs, offset);
        } else {
          ASSERT(!scratch.is(rs));
          r2 = scratch;
          li(r2, rt);
          cmpltu(scratch, r2, rs);
          offset = shifted_branch_offset(L);
          bnez(scratch, offset);
        }
        break;
      case Ugreater_equal:
        if (rt.imm64_ == 0) {
          offset = shifted_branch_offset(L);
          bgez(rs, offset);
        } else if (is_lintn(rt.imm64_, 8)) {
          cmpltui(scratch, rs, rt.imm64_);
          offset = shifted_branch_offset(L);
          beqz(scratch, offset);
        } else {
          ASSERT(!scratch.is(rs));
          r2 = scratch;
          li(r2, rt);
          cmpltu(scratch, rs, r2);
          offset = shifted_branch_offset(L);
          beqz(scratch, offset);
        }
        break;
     case Uless:
        if (rt.imm64_ == 0) {
          // No code needs to be emitted.
          return;
        } else if (is_lintn(rt.imm64_, 8)) {
          cmpltui(scratch, rs, rt.imm64_);
          offset = shifted_branch_offset(L);
          bnez(scratch, offset);
        } else {
          ASSERT(!scratch.is(rs));
          r2 = scratch;
          li(r2, rt);
          cmpltu(scratch, rs, r2);
          offset = shifted_branch_offset(L);
          bnez(scratch, offset);
        }
        break;
      case Uless_equal:
        if (rt.imm64_ == 0) {
          offset = shifted_branch_offset(L);
          b(offset);
        } else {
          ASSERT(!scratch.is(rs));
          r2 = scratch;
          li(r2, rt);
          cmpltu(scratch, r2, rs);
          offset = shifted_branch_offset(L);
          beqz(scratch, offset);
        }
        break;
      default:
        UNREACHABLE();
    }
  }
  // Check that offset could actually hold on an int16_t.
  ASSERT(is_intn(offset, 17));
}

void MacroAssembler::Branch(Label* L,
                            Condition cond,
                            Register rs,
                            Heap::RootListIndex index) {
  LoadRoot(at, index);
  Branch(L, cond, rs, Operand(at));
}

void MacroAssembler::BranchAndLink(int16_t offset) {
  BranchAndLinkShort(offset);
}

void MacroAssembler::BranchAndLink(int16_t offset, Condition cond, Register rs,
                                   const Operand& rt) {
  BranchAndLinkShort(offset, cond, rs, rt);
}

void MacroAssembler::BranchAndLink(Label* L) {
  if (L->is_bound()) {
    if (is_near(L)) {
      BranchAndLinkShort(L);
    } else {
      Jalr(L);
    }
  } else {
    if (is_trampoline_emitted()) {
      Jalr(L);
    } else {
      BranchAndLinkShort(L);
    }
  }
}

void MacroAssembler::BranchAndLink(Label* L, Condition cond, Register rs,
                                   const Operand& rt) {
  if (L->is_bound()) {
    if (is_near(L)) {
      BranchAndLinkShort(L, cond, rs, rt);
    } else {
      Label skip;
      Condition neg_cond = NegateCondition(cond);
      BranchShort(&skip, neg_cond, rs, rt);
      Jalr(L);
      bind(&skip);
    }
  } else {
    if (is_trampoline_emitted()) {
      Label skip;
      Condition neg_cond = NegateCondition(cond);
      BranchShort(&skip, neg_cond, rs, rt);
      Jalr(L);
      bind(&skip);
    } else {
      BranchAndLinkShort(L, cond, rs, rt);
    }
  }
}

void MacroAssembler::BranchAndLinkShort(Label* L) {
  jal(shifted_branch_offset(L, true));
}

void MacroAssembler::Jump(Register target,
                          Condition cond,
                          Register rs,
                          const Operand& rt) {
  if (cond == cc_always) {
    jr(target);
  } else {
    BRANCH_ARGS_CHECK(cond, rs, rt);
    Branch(2, NegateCondition(cond), rs, rt);
    jr(target);
  }
}


void MacroAssembler::Jump(intptr_t target,
                          RelocInfo::Mode rmode,
                          Condition cond,
                          Register rs,
                          const Operand& rt) {
  Label skip;
  if (cond != cc_always) {
    Branch(&skip, NegateCondition(cond), rs, rt);
  }
  // The first instruction of 'li' may be placed in the delay slot.
  // This is not an issue, t9 is expected to be clobbered anyway.
  li(t9, Operand(target, rmode));
  Jump(t9, al, zero, Operand(zero));
  bind(&skip);
}


void MacroAssembler::Jump(Address target,
                          RelocInfo::Mode rmode,
                          Condition cond,
                          Register rs,
                          const Operand& rt) {
  ASSERT(!RelocInfo::IsCodeTarget(rmode));
  Jump(reinterpret_cast<intptr_t>(target), rmode, cond, rs, rt);
}


void MacroAssembler::Jump(Handle<Code> code,
                          RelocInfo::Mode rmode,
                          Condition cond,
                          Register rs,
                          const Operand& rt) {
  ASSERT(RelocInfo::IsCodeTarget(rmode));
  ALLOW_HANDLE_DEREF(isolate(), "embedding raw address");
  Jump(reinterpret_cast<intptr_t>(code.location()), rmode, cond, rs, rt);
}


int MacroAssembler::CallSize(Register target,
                             Condition cond,
                             Register rs,
                             const Operand& rt) {
  int size = 0;

  if (cond == cc_always) {
    size += 1;
  } else {
    size += 2;
  }

  return size * kInstrSize;
}


void MacroAssembler::Call(Register target,
                          Condition cond,
                          Register rs,
                          const Operand& rt) {
  BlockTrampolinePoolScope block_trampoline_pool(this);
  Label start;
  bind(&start);
  if (cond == cc_always) {
    jalr(target);
  } else {
    BRANCH_ARGS_CHECK(cond, rs, rt);
    Branch(2, NegateCondition(cond), rs, rt);
    jalr(target);
  }

  ASSERT_EQ(CallSize(target, cond, rs, rt),
            SizeOfCodeGeneratedSince(&start));
}

int MacroAssembler::CallSize(Address target,
                             RelocInfo::Mode rmode,
                             Condition cond,
                             Register rs,
                             const Operand& rt) {
  int size = CallSize(at, cond, rs, rt);
  return size + 3 * kInstrSize;
} 

void MacroAssembler::Call(Address target,
                          RelocInfo::Mode rmode,
                          Condition cond,
                          Register rs,
                          const Operand& rt) {
  BlockTrampolinePoolScope block_trampoline_pool(this);
  Label start;
  bind(&start);
  int64_t target_int = reinterpret_cast<int64_t>(target);
  // Must record previous source positions before the
  // li() generates a new code target.
  positions_recorder()->WriteRecordedPositions();
  li(t9, Operand(target_int, rmode), CONSTANT_SIZE);
  Call(t9, cond, rs, rt);
  ASSERT_EQ(CallSize(target, rmode, cond, rs, rt),
            SizeOfCodeGeneratedSince(&start));
}

int MacroAssembler::CallSize(Handle<Code> code,
                             RelocInfo::Mode rmode,
                             TypeFeedbackId ast_id,
                             Condition cond,
                             Register rs,
                             const Operand& rt) {
  ALLOW_HANDLE_DEREF(isolate(), "using raw address");
  return CallSize(reinterpret_cast<Address>(code.location()),
      rmode, cond, rs, rt);
}


void MacroAssembler::Call(Handle<Code> code,
                          RelocInfo::Mode rmode,
                          TypeFeedbackId ast_id,
                          Condition cond,
                          Register rs,
                          const Operand& rt) {
  BlockTrampolinePoolScope block_trampoline_pool(this);
  Label start;
  bind(&start);
  ASSERT(RelocInfo::IsCodeTarget(rmode));
  if (rmode == RelocInfo::CODE_TARGET && !ast_id.IsNone()) {
    SetRecordedAstId(ast_id);
    rmode = RelocInfo::CODE_TARGET_WITH_ID;
  }
  ALLOW_HANDLE_DEREF(isolate(), "embedding raw address");
  Call(reinterpret_cast<Address>(code.location()), rmode, cond, rs, rt);
  ASSERT_EQ(CallSize(code, rmode, ast_id, cond, rs, rt),
            SizeOfCodeGeneratedSince(&start));
}


void MacroAssembler::Ret(Condition cond,
                         Register rs,
                         const Operand& rt) {
  Jump(lr, cond, rs, rt);
}


void MacroAssembler::DropAndRet(int drop) {
  addli(sp, sp, drop * kPointerSize);
  Ret();
}

void MacroAssembler::DropAndRet(int drop,
                                Condition cond,
                                Register r1,
                                const Operand& r2) {
  // Both Drop and Ret need to be conditional.
  Label skip;
  if (cond != cc_always) {
    Branch(&skip, NegateCondition(cond), r1, r2);
  }

  Drop(drop);
  Ret();

  if (cond != cc_always) {
    bind(&skip);
  }
}

void MacroAssembler::Drop(int count,
                          Condition cond,
                          Register reg,
                          const Operand& op) {
  if (count <= 0) {
    return;
  }

  Label skip;

  if (cond != al) {
     Branch(&skip, NegateCondition(cond), reg, op);
  }

  addli(sp, sp, count * kPointerSize);

  if (cond != al) {
    bind(&skip);
  }
}

void MacroAssembler::Swap(Register reg1,
                          Register reg2,
                          Register scratch) {
  if (scratch.is(no_reg)) {
    Xor(reg1, reg1, Operand(reg2));
    Xor(reg2, reg2, Operand(reg1));
    Xor(reg1, reg1, Operand(reg2));
  } else {
    move(scratch, reg1);
    move(reg1, reg2);
    move(reg2, scratch);
  }
}

void MacroAssembler::Call(Label* target) {
  BranchAndLink(target);
}

void MacroAssembler::Push(Handle<Object> handle) {
  li(at, Operand(handle));
  push(at);
}

#ifdef ENABLE_DEBUGGER_SUPPORT

void MacroAssembler::DebugBreak() {
  PrepareCEntryArgs(0);
  PrepareCEntryFunction(ExternalReference(Runtime::kDebugBreak, isolate()));
  CEntryStub ces(1);
  ASSERT(AllowThisStubCall(&ces));
  Call(ces.GetCode(isolate()), RelocInfo::DEBUG_BREAK);
}

#endif  // ENABLE_DEBUGGER_SUPPORT


// ---------------------------------------------------------------------------
// Exception handling.

void MacroAssembler::PushTryHandler(StackHandler::Kind kind,
                                    int handler_index) {
  // Adjust this code if not the case.
  STATIC_ASSERT(StackHandlerConstants::kSize == 5 * kPointerSize);
  STATIC_ASSERT(StackHandlerConstants::kNextOffset == 0 * kPointerSize);
  STATIC_ASSERT(StackHandlerConstants::kCodeOffset == 1 * kPointerSize);
  STATIC_ASSERT(StackHandlerConstants::kStateOffset == 2 * kPointerSize);
  STATIC_ASSERT(StackHandlerConstants::kContextOffset == 3 * kPointerSize);
  STATIC_ASSERT(StackHandlerConstants::kFPOffset == 4 * kPointerSize);

  // For the JSEntry handler, we must preserve r0-r4
  // t1-t3 are available. We will build up the handler from the bottom by
  // pushing on the stack.
  // Set up the code object (t1) and the state (t2) for pushing.
  unsigned state =
      StackHandler::IndexField::encode(handler_index) |
      StackHandler::KindField::encode(kind);
  li(t1, Operand(CodeObject()), __LINE__);
  li(t2, Operand(state), __LINE__);

  // Push the frame pointer, context, state, and code object.
  if (kind == StackHandler::JS_ENTRY) {
    ASSERT_EQ(Smi::FromInt(0), 0);
    // The second zero indicates no context.
    // The first zero is the NULL frame pointer.
    // The operands are reversed to match the order of MultiPush/Pop.
    Push(zero, zero, t2, t1);
  } else {
    MultiPush(t1.bit() | t2.bit() | cp.bit() | fp.bit());
  }

  // Link the current handler as the next handler.
  li(t2, Operand(ExternalReference(Isolate::kHandlerAddress, isolate())));
  ld(t1, MemOperand(t2));
  push(t1);
  // Set this new handler as the current one.
  st(sp, MemOperand(t2), __LINE__);
}


void MacroAssembler::PopTryHandler() {
  STATIC_ASSERT(StackHandlerConstants::kNextOffset == 0);
  pop(r1);
  Addu(sp, sp, Operand(StackHandlerConstants::kSize - kPointerSize));
  li(at, Operand(ExternalReference(Isolate::kHandlerAddress, isolate())));
  st(r1, MemOperand(at));
}


void MacroAssembler::JumpToHandlerEntry() {
  // Compute the handler entry address and jump to it.  The handler table is
  // a fixed array of (smi-tagged) code offsets.
  // v0 = exception, a1 = code object, a2 = state.
  ld(r3, FieldMemOperand(r1, Code::kHandlerTableOffset));  // Handler table.
  Addu(r3, r3, Operand(FixedArray::kHeaderSize - kHeapObjectTag));
  srl(r2, r2, StackHandler::kKindWidth);  // Handler index.
  sll(r2, r2, kPointerSizeLog2);
  Addu(r2, r3, r2);
  ld(r2, MemOperand(r2));  // Smi-tagged offset.
  Addu(r1, r1, Operand(Code::kHeaderSize - kHeapObjectTag));  // Code start.
  sra(at, r2, kSmiTagSize + kSmiShiftSize);
  Addu(at, at, r1);
  Jump(at);  // Jump.
}


void MacroAssembler::Throw(Register value) {
  // Adjust this code if not the case.
  STATIC_ASSERT(StackHandlerConstants::kSize == 5 * kPointerSize);
  STATIC_ASSERT(StackHandlerConstants::kNextOffset == 0);
  STATIC_ASSERT(StackHandlerConstants::kCodeOffset == 1 * kPointerSize);
  STATIC_ASSERT(StackHandlerConstants::kStateOffset == 2 * kPointerSize);
  STATIC_ASSERT(StackHandlerConstants::kContextOffset == 3 * kPointerSize);
  STATIC_ASSERT(StackHandlerConstants::kFPOffset == 4 * kPointerSize);

  // The exception is expected in v0.
  Move(r0, value);

  // Drop the stack pointer to the top of the top handler.
  li(r3, Operand(ExternalReference(Isolate::kHandlerAddress,
                                   isolate())));
  ld(sp, MemOperand(r3));

  // Restore the next handler.
  pop(r2);
  st(r2, MemOperand(r3));

  // Get the code object (a1) and state (a2).  Restore the context and frame
  // pointer.
  MultiPop(r1.bit() | r2.bit() | cp.bit() | fp.bit());

  // If the handler is a JS frame, restore the context to the frame.
  // (kind == ENTRY) == (fp == 0) == (cp == 0), so we could test either fp
  // or cp.
  Label done;
  Branch(&done, eq, cp, Operand(zero));
  st(cp, MemOperand(fp, StandardFrameConstants::kContextOffset));
  bind(&done);

  JumpToHandlerEntry();
}

void MacroAssembler::ThrowUncatchable(Register value) {
  // Adjust this code if not the case.
  STATIC_ASSERT(StackHandlerConstants::kSize == 5 * kPointerSize);
  STATIC_ASSERT(StackHandlerConstants::kNextOffset == 0 * kPointerSize);
  STATIC_ASSERT(StackHandlerConstants::kCodeOffset == 1 * kPointerSize);
  STATIC_ASSERT(StackHandlerConstants::kStateOffset == 2 * kPointerSize);
  STATIC_ASSERT(StackHandlerConstants::kContextOffset == 3 * kPointerSize);
  STATIC_ASSERT(StackHandlerConstants::kFPOffset == 4 * kPointerSize);

  // The exception is expected in r0.
  if (!value.is(r0)) {
    move(r0, value);
  }
  // Drop the stack pointer to the top of the top stack handler.
  li(r3, Operand(ExternalReference(Isolate::kHandlerAddress, isolate())));
  ld(sp, MemOperand(r3));

  // Unwind the handlers until the ENTRY handler is found.
  Label fetch_next, check_kind;
  jmp(&check_kind);
  bind(&fetch_next);
  ld(sp, MemOperand(sp, StackHandlerConstants::kNextOffset));

  bind(&check_kind);
  STATIC_ASSERT(StackHandler::JS_ENTRY == 0);
  ld(r2, MemOperand(sp, StackHandlerConstants::kStateOffset));
  And(r2, r2, Operand(StackHandler::KindField::kMask));
  Branch(&fetch_next, ne, r2, Operand(zero));

  // Set the top handler address to next handler past the top ENTRY handler.
  pop(r2);
  st(r2, MemOperand(r3));

  // Get the code object (a1) and state (a2).  Clear the context and frame
  // pointer (0 was saved in the handler).
  MultiPop(r1.bit() | r2.bit() | cp.bit() | fp.bit());

  JumpToHandlerEntry();
}


void MacroAssembler::Allocate(int object_size,
                              Register result,
                              Register scratch1,
                              Register scratch2,
                              Label* gc_required,
                              AllocationFlags flags) {
  if (!FLAG_inline_new) {
    if (emit_debug_code()) {
      // Trash the registers to simulate an allocation failure.
      li(result, 0x7091);
      li(scratch1, 0x7191);
      li(scratch2, 0x7291);
    }
    jmp(gc_required);
    return;
  }

  ASSERT(!result.is(scratch1));
  ASSERT(!result.is(scratch2));
  ASSERT(!scratch1.is(scratch2));
  ASSERT(!scratch1.is(t9));
  ASSERT(!scratch2.is(t9));
  ASSERT(!result.is(t9));

  // Make object size into bytes.
  if ((flags & SIZE_IN_WORDS) != 0) {
    object_size *= kPointerSize;
  }
  ASSERT_EQ(0, (int)(object_size & kObjectAlignmentMask));

  // Check relative positions of allocation top and limit addresses.
  // ARM adds additional checks to make sure the ldm instruction can be
  // used. On MIPS we don't have ldm so we don't need additional checks either.
  ExternalReference allocation_top =
      AllocationUtils::GetAllocationTopReference(isolate(), flags);
  ExternalReference allocation_limit =
      AllocationUtils::GetAllocationLimitReference(isolate(), flags);

  intptr_t top   =
      reinterpret_cast<intptr_t>(allocation_top.address());
  intptr_t limit =
      reinterpret_cast<intptr_t>(allocation_limit.address());
  ASSERT((limit - top) == kPointerSize);

  // Set up allocation top address and object size registers.
  Register topaddr = scratch1;
  Register obj_size_reg = scratch2;
  li(topaddr, Operand(allocation_top));
  li(obj_size_reg, Operand(object_size));

  // This code stores a temporary value in t9.
  if ((flags & RESULT_CONTAINS_TOP) == 0) {
    // Load allocation top into result and allocation limit into t9.
    ld(result, MemOperand(topaddr));
    ld(t9, MemOperand(topaddr, kPointerSize));
  } else {
    if (emit_debug_code()) {
      // Assert that result actually contains top on entry. t9 is used
      // immediately below so this use of t9 does not cause difference with
      // respect to register content between debug and release mode.
      ld(t9, MemOperand(topaddr));
      Check(eq, "Unexpected allocation top", result, Operand(t9));
    }
    // Load allocation limit into t9. Result already contains allocation top.
    ld(t9, MemOperand(topaddr, limit - top));
  }

  // Calculate new top and bail out if new space is exhausted. Use result
  // to calculate the new top.
  Addu(scratch2, result, Operand(obj_size_reg));
  Branch(gc_required, Ugreater, scratch2, Operand(t9));
  st(scratch2, MemOperand(topaddr));

  // Tag object if requested.
  if ((flags & TAG_OBJECT) != 0) {
    Addu(result, result, Operand(kHeapObjectTag));
  }
}


void MacroAssembler::Allocate(Register object_size,
                              Register result,
                              Register scratch1,
                              Register scratch2,
                              Label* gc_required,
                              AllocationFlags flags) {
  if (!FLAG_inline_new) {
    if (emit_debug_code()) {
      // Trash the registers to simulate an allocation failure.
      li(result, 0x7091);
      li(scratch1, 0x7191);
      li(scratch2, 0x7291);
    }
    jmp(gc_required);
    return;
  }

  ASSERT(!result.is(scratch1));
  ASSERT(!result.is(scratch2));
  ASSERT(!scratch1.is(scratch2));
  ASSERT(!object_size.is(t9));
  ASSERT(!scratch1.is(t9) && !scratch2.is(t9) && !result.is(t9));

  // Check relative positions of allocation top and limit addresses.
  // ARM adds additional checks to make sure the ldm instruction can be
  // used. On MIPS we don't have ldm so we don't need additional checks either.
  ExternalReference allocation_top =
      AllocationUtils::GetAllocationTopReference(isolate(), flags);
  ExternalReference allocation_limit =
      AllocationUtils::GetAllocationLimitReference(isolate(), flags);
  intptr_t top   =
      reinterpret_cast<intptr_t>(allocation_top.address());
  intptr_t limit =
      reinterpret_cast<intptr_t>(allocation_limit.address());
  ASSERT((limit - top) == kPointerSize);

  // Set up allocation top address and object size registers.
  Register topaddr = scratch1;
  li(topaddr, Operand(allocation_top));

  // This code stores a temporary value in t9.
  if ((flags & RESULT_CONTAINS_TOP) == 0) {
    // Load allocation top into result and allocation limit into t9.
    ld(result, MemOperand(topaddr));
    ld(t9, MemOperand(topaddr, kPointerSize));
  } else {
    if (emit_debug_code()) {
      // Assert that result actually contains top on entry. t9 is used
      // immediately below so this use of t9 does not cause difference with
      // respect to register content between debug and release mode.
      ld(t9, MemOperand(topaddr));
      Check(eq, "Unexpected allocation top", result, Operand(t9));
    }
    // Load allocation limit into t9. Result already contains allocation top.
    ld(t9, MemOperand(topaddr, limit - top));
  }

  // Calculate new top and bail out if new space is exhausted. Use result
  // to calculate the new top. Object size may be in words so a shift is
  // required to get the number of bytes.
  if ((flags & SIZE_IN_WORDS) != 0) {
    sll(scratch2, object_size, kPointerSizeLog2);
    Addu(scratch2, result, scratch2);
  } else {
    Addu(scratch2, result, Operand(object_size));
  }
  Branch(gc_required, Ugreater, scratch2, Operand(t9));

  // Update allocation top. result temporarily holds the new top.
  if (emit_debug_code()) {
    And(t9, scratch2, Operand(kObjectAlignmentMask));
    Check(eq, "Unaligned allocation in new space", t9, Operand(zero));
  }
  st(scratch2, MemOperand(topaddr));

  // Tag object if requested.
  if ((flags & TAG_OBJECT) != 0) {
    Addu(result, result, Operand(kHeapObjectTag));
  }
}


void MacroAssembler::UndoAllocationInNewSpace(Register object,
                                              Register scratch) {
  ExternalReference new_space_allocation_top =
      ExternalReference::new_space_allocation_top_address(isolate());

  // Make sure the object has no tag before resetting top.
  And(object, object, Operand(~kHeapObjectTagMask));
#ifdef DEBUG
  // Check that the object un-allocated is below the current top.
  li(scratch, Operand(new_space_allocation_top));
  ld(scratch, MemOperand(scratch));
  Check(less, "Undo allocation of non allocated memory",
      object, Operand(scratch));
#endif
  // Write the address of the object to un-allocate as the current top.
  li(scratch, Operand(new_space_allocation_top));
  st(object, MemOperand(scratch));
}

void MacroAssembler::InitializeNewString(Register string,
                                         Register length,
                                         Heap::RootListIndex map_index,
                                         Register scratch1,
                                         Register scratch2) {
  sll(scratch1, length, 32);
  LoadRoot(scratch2, map_index);
  st(scratch1, FieldMemOperand(string, String::kLengthOffset));
  li(scratch1, Operand(String::kEmptyHashField));
  st(scratch2, FieldMemOperand(string, HeapObject::kMapOffset));
  st(scratch1, FieldMemOperand(string, String::kHashFieldOffset));
}

void MacroAssembler::AllocateTwoByteString(Register result,
                                           Register length,
                                           Register scratch1,
                                           Register scratch2,
                                           Register scratch3,
                                           Label* gc_required) {
  // Calculate the number of bytes needed for the characters in the string while
  // observing object alignment.
  ASSERT((SeqTwoByteString::kHeaderSize & kObjectAlignmentMask) == 0);
  sll(scratch1, length, 1);  // Length in bytes, not chars.
  addi(scratch1, scratch1,
       kObjectAlignmentMask + SeqTwoByteString::kHeaderSize);
  And(scratch1, scratch1, Operand(~kObjectAlignmentMask));

  // Allocate two-byte string in new space.
  Allocate(scratch1,
           result,
           scratch2,
           scratch3,
           gc_required,
           TAG_OBJECT);

  // Set the map, length and hash field.
  InitializeNewString(result,
                      length,
                      Heap::kStringMapRootIndex,
                      scratch1,
                      scratch2);
}

void MacroAssembler::AllocateAsciiString(Register result,
                                         Register length,
                                         Register scratch1,
                                         Register scratch2,
                                         Register scratch3,
                                         Label* gc_required) {
  // Calculate the number of bytes needed for the characters in the string
  // while observing object alignment.
  ASSERT((SeqOneByteString::kHeaderSize & kObjectAlignmentMask) == 0);
  ASSERT(kCharSize == 1);
  addli(scratch1, length, kObjectAlignmentMask + SeqOneByteString::kHeaderSize);
  And(scratch1, scratch1, Operand(~kObjectAlignmentMask));

  // Allocate ASCII string in new space.
  Allocate(scratch1,
           result,
           scratch2,
           scratch3,
           gc_required,
           TAG_OBJECT);

  // Set the map, length and hash field.
  InitializeNewString(result,
                      length,
                      Heap::kAsciiStringMapRootIndex,
                      scratch1,
                      scratch2);
}


void MacroAssembler::AllocateTwoByteConsString(Register result,
                                               Register length,
                                               Register scratch1,
                                               Register scratch2,
                                               Label* gc_required) {
  Allocate(ConsString::kSize, result, scratch1, scratch2, gc_required,
           TAG_OBJECT);
  InitializeNewString(result,
                      length,
                      Heap::kConsStringMapRootIndex,
                      scratch1,
                      scratch2);
}


void MacroAssembler::AllocateAsciiConsString(Register result,
                                             Register length,
                                             Register scratch1,
                                             Register scratch2,
                                             Label* gc_required) {
  Label allocate_new_space, install_map;
  AllocationFlags flags = TAG_OBJECT;

  ExternalReference high_promotion_mode = ExternalReference::
      new_space_high_promotion_mode_active_address(isolate());
  li(scratch1, Operand(high_promotion_mode));
  ld(scratch1, MemOperand(scratch1, 0));
  Branch(&allocate_new_space, eq, scratch1, Operand(zero));

  Allocate(ConsString::kSize,
           result,
           scratch1,
           scratch2,
           gc_required,
           static_cast<AllocationFlags>(flags | PRETENURE_OLD_POINTER_SPACE));

  jmp(&install_map);

  bind(&allocate_new_space);
  Allocate(ConsString::kSize,
           result,
           scratch1,
           scratch2,
           gc_required,
           flags);

  bind(&install_map);

  InitializeNewString(result,
                      length,
                      Heap::kConsAsciiStringMapRootIndex,
                      scratch1,
                      scratch2);
}


void MacroAssembler::AllocateTwoByteSlicedString(Register result,
                                                 Register length,
                                                 Register scratch1,
                                                 Register scratch2,
                                                 Label* gc_required) {
  Allocate(SlicedString::kSize, result, scratch1, scratch2, gc_required,
           TAG_OBJECT);

  InitializeNewString(result,
                      length,
                      Heap::kSlicedStringMapRootIndex,
                      scratch1,
                      scratch2);
}

void MacroAssembler::AllocateAsciiSlicedString(Register result,
                                               Register length,
                                               Register scratch1,
                                               Register scratch2,
                                               Label* gc_required) {
  Allocate(SlicedString::kSize, result, scratch1, scratch2, gc_required,
           TAG_OBJECT);

  InitializeNewString(result,
                      length,
                      Heap::kSlicedAsciiStringMapRootIndex,
                      scratch1,
                      scratch2);
}

// Allocates a heap number or jumps to the label if the young space is full and
// a scavenge is needed.
void MacroAssembler::AllocateHeapNumber(Register result,
                                        Register scratch1,
                                        Register scratch2,
                                        Register heap_number_map,
                                        Label* need_gc,
                                        TaggingMode tagging_mode) {
  // Allocate an object in the heap for the heap number and tag it as a heap
  // object.
  Allocate(HeapNumber::kSize, result, scratch1, scratch2, need_gc,
           tagging_mode == TAG_RESULT ? TAG_OBJECT : NO_ALLOCATION_FLAGS);

  // Store heap number map in the allocated object.
  AssertRegisterIsRoot(heap_number_map, Heap::kHeapNumberMapRootIndex);
  if (tagging_mode == TAG_RESULT) {
    st(heap_number_map, FieldMemOperand(result, HeapObject::kMapOffset));
  } else {
    st(heap_number_map, MemOperand(result, HeapObject::kMapOffset));
  }
}

void MacroAssembler::GetLeastBitsFromSmi(Register dst,
                                         Register src,
                                         int num_least_bits) {
  bfextu(dst, src, kSmiTagSize + kSmiShiftSize, kSmiTagSize + kSmiShiftSize + num_least_bits - 1);
}


void MacroAssembler::GetLeastBitsFromInt32(Register dst,
                                           Register src,
                                           int num_least_bits) {
  And(dst, src, Operand((1 << num_least_bits) - 1));
}

void MacroAssembler::AdduAndCheckForOverflow(Register dst,
                                             Register left,
                                             Register right,
                                             Register overflow_dst,
                                             Register scratch) {
  ASSERT(!dst.is(overflow_dst));
  ASSERT(!dst.is(scratch));
  ASSERT(!overflow_dst.is(scratch));
  ASSERT(!overflow_dst.is(left));
  ASSERT(!overflow_dst.is(right));

  if (left.is(right) && dst.is(left)) {
    ASSERT(!dst.is(t9));
    ASSERT(!scratch.is(t9));
    ASSERT(!left.is(t9));
    ASSERT(!right.is(t9));
    ASSERT(!overflow_dst.is(t9));
    move(t9, right);
    right = t9;
  }

  if (dst.is(left)) {
    move(scratch, left);  // Preserve left.
    add(dst, left, right);  // Left is overwritten.
    xor_(scratch, dst, scratch);  // Original left.
    xor_(overflow_dst, dst, right);
    and_(overflow_dst, overflow_dst, scratch);
  } else if (dst.is(right)) {
    move(scratch, right);  // Preserve right.
    add(dst, left, right);  // Right is overwritten.
    xor_(scratch, dst, scratch);  // Original right.
    xor_(overflow_dst, dst, left);
    and_(overflow_dst, overflow_dst, scratch);
  } else {
    add(dst, left, right);
    xor_(overflow_dst, dst, left);
    xor_(scratch, dst, right);
    and_(overflow_dst, scratch, overflow_dst);
  }
}


void MacroAssembler::SubuAndCheckForOverflow(Register dst,
                                             Register left,
                                             Register right,
                                             Register overflow_dst,
                                             Register scratch) {
  ASSERT(!dst.is(overflow_dst));
  ASSERT(!dst.is(scratch));
  ASSERT(!overflow_dst.is(scratch));
  ASSERT(!overflow_dst.is(left));
  ASSERT(!overflow_dst.is(right));
  ASSERT(!scratch.is(left));
  ASSERT(!scratch.is(right));

  // This happens with some crankshaft code. Since Subu works fine if
  // left == right, let's not make that restriction here.
  if (left.is(right)) {
    move(dst, zero);
    move(overflow_dst, zero);
    return;
  }

  if (dst.is(left)) {
    move(scratch, left);  // Preserve left.
    sub(dst, left, right);  // Left is overwritten.
    xor_(overflow_dst, dst, scratch);  // scratch is original left.
    xor_(scratch, scratch, right);  // scratch is original left.
    and_(overflow_dst, scratch, overflow_dst);
  } else if (dst.is(right)) {
    move(scratch, right);  // Preserve right.
    sub(dst, left, right);  // Right is overwritten.
    xor_(overflow_dst, dst, left);
    xor_(scratch, left, scratch);  // Original right.
    and_(overflow_dst, scratch, overflow_dst);
  } else {
    sub(dst, left, right);
    xor_(overflow_dst, dst, left);
    xor_(scratch, left, right);
    and_(overflow_dst, scratch, overflow_dst);
  }
}

// Copies a fixed number of fields of heap objects from src to dst.
void MacroAssembler::CopyFields(Register dst,
                                Register src,
                                RegList temps,
                                int field_count) {
  ASSERT((temps & dst.bit()) == 0);
  ASSERT((temps & src.bit()) == 0);
  // Primitive implementation using only one temporary register.

  Register tmp = no_reg;
  // Find a temp register in temps list.
  for (int i = 0; i < kNumRegisters; i++) {
    if ((temps & (1L << i)) != 0) {
      tmp.code_ = i;
      break;
    }
  }
  ASSERT(!tmp.is(no_reg));
  ASSERT(!tmp.is(at));

  for (int i = 0; i < field_count; i++) {
    ld(tmp, FieldMemOperand(src, i * kPointerSize));
    st(tmp, FieldMemOperand(dst, i * kPointerSize));
  }
}

void MacroAssembler::CopyBytes(Register src,
                               Register dst,
                               Register length,
                               Register scratch) {
  Label align_loop, align_loop_1, word_loop, byte_loop, byte_loop_1, done;

  // Align src before copying in word size chunks.
  bind(&align_loop);
  Branch(&done, eq, length, Operand(zero));
  bind(&align_loop_1);
  And(scratch, src, kPointerSize - 1);
  Branch(&word_loop, eq, scratch, Operand(zero));
  ld1u(scratch, MemOperand(src));
  Addu(src, src, 1);
  st1(scratch, MemOperand(dst));
  Addu(dst, dst, 1);
  Subu(length, length, Operand(1));
  Branch(&byte_loop_1, ne, length, Operand(zero));

  // Copy bytes in word size chunks.
  bind(&word_loop);
  if (emit_debug_code()) {
    And(scratch, src, kPointerSize - 1);
    Assert(eq, "Expecting alignment for CopyBytes",
        scratch, Operand(zero));
  }
  Branch(&byte_loop, lt, length, Operand(kPointerSize));
  ld(scratch, MemOperand(src));
  Addu(src, src, kPointerSize);

  // TODO(kalmard) check if this can be optimized to use sw in most cases.
  // Can't use unaligned access - copy byte by byte.
  st1(scratch, MemOperand(dst, 0));
  srl(scratch, scratch, 8);
  st1(scratch, MemOperand(dst, 1));
  srl(scratch, scratch, 8);
  st1(scratch, MemOperand(dst, 2));
  srl(scratch, scratch, 8);
  st1(scratch, MemOperand(dst, 3));
  srl(scratch, scratch, 8);
  st1(scratch, MemOperand(dst, 4));
  srl(scratch, scratch, 8);
  st1(scratch, MemOperand(dst, 5));
  srl(scratch, scratch, 8);
  st1(scratch, MemOperand(dst, 6));
  srl(scratch, scratch, 8);
  st1(scratch, MemOperand(dst, 7));
  Addu(dst, dst, 8);

  Subu(length, length, Operand(kPointerSize));
  Branch(&word_loop);

  // Copy the last bytes if any left.
  bind(&byte_loop);
  Branch(&done, eq, length, Operand(zero));
  bind(&byte_loop_1);
  ld1u(scratch, MemOperand(src));
  Addu(src, src, 1);
  st1(scratch, MemOperand(dst));
  Addu(dst, dst, 1);
  Subu(length, length, Operand(1));
  Branch(&byte_loop_1, ne, length, Operand(zero));
  bind(&done);
}

void MacroAssembler::InitializeFieldsWithFiller(Register start_offset,
                                                Register end_offset,
                                                Register filler) {
  Label loop, entry;
  Branch(&entry);
  bind(&loop);
  st(filler, MemOperand(start_offset));
  Addu(start_offset, start_offset, kPointerSize);
  bind(&entry);
  Branch(&loop, lt, start_offset, Operand(end_offset));
}


void MacroAssembler::CheckFastElements(Register map,
                                       Register scratch,
                                       Label* fail) {
  STATIC_ASSERT(FAST_SMI_ELEMENTS == 0);
  STATIC_ASSERT(FAST_HOLEY_SMI_ELEMENTS == 1);
  STATIC_ASSERT(FAST_ELEMENTS == 2);
  STATIC_ASSERT(FAST_HOLEY_ELEMENTS == 3);
  ld1u(scratch, FieldMemOperand(map, Map::kBitField2Offset));
  Branch(fail, hi, scratch,
         Operand(Map::kMaximumBitField2FastHoleyElementValue));
}


void MacroAssembler::CheckFastObjectElements(Register map,
                                             Register scratch,
                                             Label* fail) {
  STATIC_ASSERT(FAST_SMI_ELEMENTS == 0);
  STATIC_ASSERT(FAST_HOLEY_SMI_ELEMENTS == 1);
  STATIC_ASSERT(FAST_ELEMENTS == 2);
  STATIC_ASSERT(FAST_HOLEY_ELEMENTS == 3);
  ld1u(scratch, FieldMemOperand(map, Map::kBitField2Offset));
  Branch(fail, ls, scratch,
         Operand(Map::kMaximumBitField2FastHoleySmiElementValue));
  Branch(fail, hi, scratch,
         Operand(Map::kMaximumBitField2FastHoleyElementValue));
}


void MacroAssembler::CheckFastSmiElements(Register map,
                                          Register scratch,
                                          Label* fail) {
  STATIC_ASSERT(FAST_SMI_ELEMENTS == 0);
  STATIC_ASSERT(FAST_HOLEY_SMI_ELEMENTS == 1);
  ld1u(scratch, FieldMemOperand(map, Map::kBitField2Offset));
  Branch(fail, hi, scratch,
         Operand(Map::kMaximumBitField2FastHoleySmiElementValue));
}


void MacroAssembler::StoreNumberToDoubleElements(Register value_reg,
                                                 Register key_reg,
                                                 Register elements_reg,
                                                 Register scratch1,
                                                 Register scratch2,
                                                 Register scratch3,
                                                 Register scratch4,
                                                 Label* fail,
                                                 int elements_offset) {
  Label smi_value, maybe_nan, have_double_value, is_nan, done;
  Register mantissa_reg = scratch2;
  Register exponent_reg = scratch3;

  // Handle smi values specially.
  JumpIfSmi(value_reg, &smi_value);

  // Ensure that the object is a heap number
  CheckMap(value_reg,
           scratch1,
           Heap::kHeapNumberMapRootIndex,
           fail,
           DONT_DO_SMI_CHECK);

  // Check for nan: all NaN values have a value greater (signed) than 0x7ff00000
  // in the exponent.
  li(scratch1, Operand(0x7FF0000000000000L));
  ld(exponent_reg, FieldMemOperand(value_reg, HeapNumber::kValueOffset));
  Branch(&maybe_nan, ge, exponent_reg, Operand(scratch1));

  ld(mantissa_reg, FieldMemOperand(value_reg, HeapNumber::kMantissaOffset));

  bind(&have_double_value);
  sra(scratch1, key_reg, 32);
  sll(scratch1, scratch1, kDoubleSizeLog2);
  Addu(scratch1, scratch1, elements_reg);
  st(exponent_reg, FieldMemOperand(
     scratch1, FixedDoubleArray::kHeaderSize - elements_offset));
  jmp(&done);

  bind(&maybe_nan);
  // Could be NaN or Infinity. If fraction is not zero, it's NaN, otherwise
  // it's an Infinity, and the non-NaN code path applies.
  Branch(&is_nan, gt, exponent_reg, Operand(scratch1));
  Branch(&have_double_value, eq, exponent_reg, Operand(0x7FF0000000000000L));
  bind(&is_nan);
  // Load canonical NaN for storing into the double array.
  uint64_t nan_int64 = BitCast<uint64_t>(
      FixedDoubleArray::canonical_not_the_hole_nan_as_double());
  li(exponent_reg, Operand(nan_int64));
  jmp(&have_double_value);

  bind(&smi_value);
  Addu(scratch1, elements_reg,
      Operand(FixedDoubleArray::kHeaderSize - kHeapObjectTag -
              elements_offset));
  sra(scratch2, key_reg, 32);
  sll(scratch2, scratch2, kDoubleSizeLog2);
  Addu(scratch1, scratch1, scratch2);
  // scratch1 is now effective address of the double element

  FloatingPointHelper::Destination destination;
  destination = FloatingPointHelper::kCoreRegisters;

  Register untagged_value = elements_reg;
  SmiUntag(untagged_value, value_reg);
  FloatingPointHelper::ConvertIntToDouble(this,
                                          untagged_value,
                                          destination,
                                          mantissa_reg,
                                          exponent_reg,
                                          scratch4);
  st(mantissa_reg, MemOperand(scratch1));
  bind(&done);
}

void MacroAssembler::CompareMapAndBranch(Register obj,
                                         Register scratch,
                                         Handle<Map> map,
                                         Label* early_success,
                                         Condition cond,
                                         Label* branch_to) {
  ld(scratch, FieldMemOperand(obj, HeapObject::kMapOffset));
  CompareMapAndBranch(scratch, map, early_success, cond, branch_to);
}


void MacroAssembler::CompareMapAndBranch(Register obj_map,
                                         Handle<Map> map,
                                         Label* early_success,
                                         Condition cond,
                                         Label* branch_to) {
  Branch(branch_to, cond, obj_map, Operand(map));
}

void MacroAssembler::CheckMap(Register obj,
                              Register scratch,
                              Handle<Map> map,
                              Label* fail,
                              SmiCheckType smi_check_type) {
  if (smi_check_type == DO_SMI_CHECK) {
    JumpIfSmi(obj, fail);
  }
  Label success;
  CompareMapAndBranch(obj, scratch, map, &success, ne, fail);
  bind(&success);
}

void MacroAssembler::DispatchMap(Register obj,
                                 Register scratch,
                                 Handle<Map> map,
                                 Handle<Code> success,
                                 SmiCheckType smi_check_type) {
  Label fail;
  if (smi_check_type == DO_SMI_CHECK) {
    JumpIfSmi(obj, &fail);
  }
  ld(scratch, FieldMemOperand(obj, HeapObject::kMapOffset));
  Jump(success, RelocInfo::CODE_TARGET, eq, scratch, Operand(map));
  bind(&fail);
}

void MacroAssembler::CheckMap(Register obj,
                              Register scratch,
                              Heap::RootListIndex index,
                              Label* fail,
                              SmiCheckType smi_check_type) {
  if (smi_check_type == DO_SMI_CHECK) {
    JumpIfSmi(obj, fail);
  }
  ld(scratch, FieldMemOperand(obj, HeapObject::kMapOffset));
  LoadRoot(at, index);
  Branch(fail, ne, scratch, Operand(at));
}

void MacroAssembler::SetCallKind(Register dst, CallKind call_kind) {
  // This macro takes the dst register to make the code more readable
  // at the call sites. However, the dst register has to be t1 to
  // follow the calling convention which requires the call type to be
  // in t1.
  ASSERT(dst.is(t1));
  if (call_kind == CALL_AS_FUNCTION) {
    li(dst, Operand(Smi::FromInt(1)));
  } else {
    li(dst, Operand(Smi::FromInt(0)));
  }
}

// -----------------------------------------------------------------------------
// JavaScript invokes.

void MacroAssembler::InvokePrologue(const ParameterCount& expected,
                                    const ParameterCount& actual,
                                    Handle<Code> code_constant,
                                    Register code_reg,
                                    Label* done,
                                    bool* definitely_mismatches,
                                    InvokeFlag flag,
                                    const CallWrapper& call_wrapper,
                                    CallKind call_kind) {
  bool definitely_matches = false;
  *definitely_mismatches = false;
  Label regular_invoke;

  // Check whether the expected and actual arguments count match. If not,
  // setup registers according to contract with ArgumentsAdaptorTrampoline:
  //  r0: actual arguments count
  //  r1: function (passed through to callee)
  //  r2: expected arguments count
  //  r3: callee code entry

  // The code below is made a lot easier because the calling code already sets
  // up actual and expected registers according to the contract if values are
  // passed in registers.
  ASSERT(actual.is_immediate() || actual.reg().is(r0));
  ASSERT(expected.is_immediate() || expected.reg().is(r2));
  ASSERT((!code_constant.is_null() && code_reg.is(no_reg)) || code_reg.is(r3));

  if (expected.is_immediate()) {
    ASSERT(actual.is_immediate());
    if (expected.immediate() == actual.immediate()) {
      definitely_matches = true;
    } else {
      li(r0, Operand(actual.immediate()));
      const int sentinel = SharedFunctionInfo::kDontAdaptArgumentsSentinel;
      if (expected.immediate() == sentinel) {
        // Don't worry about adapting arguments for builtins that
        // don't want that done. Skip adaption code by making it look
        // like we have a match between expected and actual number of
        // arguments.
        definitely_matches = true;
      } else {
        *definitely_mismatches = true;
        li(a2, Operand(expected.immediate()));
      }
    }
  } else if (actual.is_immediate()) {
    Branch(&regular_invoke, eq, expected.reg(), Operand(actual.immediate()));
    li(r0, Operand(actual.immediate()));
  } else {
    Branch(&regular_invoke, eq, expected.reg(), Operand(actual.reg()));
  }

  if (!definitely_matches) {
    if (!code_constant.is_null()) {
      li(r3, Operand(code_constant));
      addli(r3, r3, Code::kHeaderSize - kHeapObjectTag);
    }

    Handle<Code> adaptor =
        isolate()->builtins()->ArgumentsAdaptorTrampoline();
    if (flag == CALL_FUNCTION) {
      call_wrapper.BeforeCall(CallSize(adaptor));
      SetCallKind(t1, call_kind);
      Call(adaptor);
      call_wrapper.AfterCall();
      if (!*definitely_mismatches) {
        Branch(done);
      }
    } else {
      SetCallKind(t1, call_kind);
      Jump(adaptor, RelocInfo::CODE_TARGET);
    }
    bind(&regular_invoke);
  }
}

void MacroAssembler::InvokeCode(Register code,
                                const ParameterCount& expected,
                                const ParameterCount& actual,
                                InvokeFlag flag,
                                const CallWrapper& call_wrapper,
                                CallKind call_kind) {
  // You can't call a function without a valid frame.
  ASSERT(flag == JUMP_FUNCTION || has_frame());

  Label done;

  bool definitely_mismatches = false;
  InvokePrologue(expected, actual, Handle<Code>::null(), code,
                 &done, &definitely_mismatches, flag,
                 call_wrapper, call_kind);
  if (!definitely_mismatches) {
    if (flag == CALL_FUNCTION) {
      call_wrapper.BeforeCall(CallSize(code));
      SetCallKind(t1, call_kind);
      Call(code);
      call_wrapper.AfterCall();
    } else {
      ASSERT(flag == JUMP_FUNCTION);
      SetCallKind(t1, call_kind);
      Jump(code);
    }
    // Continue here if InvokePrologue does handle the invocation due to
    // mismatched parameter counts.
    bind(&done);
  }
}


void MacroAssembler::InvokeCode(Handle<Code> code,
                                const ParameterCount& expected,
                                const ParameterCount& actual,
                                RelocInfo::Mode rmode,
                                InvokeFlag flag,
                                CallKind call_kind) {
  // You can't call a function without a valid frame.
  ASSERT(flag == JUMP_FUNCTION || has_frame());

  Label done;

  bool definitely_mismatches = false;
  InvokePrologue(expected, actual, code, no_reg,
                 &done, &definitely_mismatches, flag,
                 NullCallWrapper(), call_kind);
  if (!definitely_mismatches) {
    if (flag == CALL_FUNCTION) {
      SetCallKind(t1, call_kind);
      Call(code, rmode);
    } else {
      SetCallKind(t1, call_kind);
      Jump(code, rmode);
    }
    // Continue here if InvokePrologue does handle the invocation due to
    // mismatched parameter counts.
    bind(&done);
  }
}


void MacroAssembler::InvokeFunction(Register function,
                                    const ParameterCount& actual,
                                    InvokeFlag flag,
                                    const CallWrapper& call_wrapper,
                                    CallKind call_kind) {
  // You can't call a function without a valid frame.
  ASSERT(flag == JUMP_FUNCTION || has_frame());

  // Contract with called JS functions requires that function is passed in a1.
  ASSERT(function.is(r1));
  Register expected_reg = r2;
  Register code_reg = r3;

  ld(code_reg, FieldMemOperand(r1, JSFunction::kSharedFunctionInfoOffset));
  ld(cp, FieldMemOperand(r1, JSFunction::kContextOffset));
  ld4s(expected_reg,
      FieldMemOperand(code_reg,
                      SharedFunctionInfo::kFormalParameterCountOffset));
  //sra(expected_reg, expected_reg, kSmiTagSize + kSmiShiftSize);
  ld(code_reg, FieldMemOperand(r1, JSFunction::kCodeEntryOffset));

  ParameterCount expected(expected_reg);
  InvokeCode(code_reg, expected, actual, flag, call_wrapper, call_kind);
}


void MacroAssembler::InvokeFunction(Handle<JSFunction> function,
                                    const ParameterCount& expected,
                                    const ParameterCount& actual,
                                    InvokeFlag flag,
                                    const CallWrapper& call_wrapper,
                                    CallKind call_kind) {
  // You can't call a function without a valid frame.
  ASSERT(flag == JUMP_FUNCTION || has_frame());

  // Get the function and setup the context.
  LoadHeapObject(a1, function);
  ld(cp, FieldMemOperand(a1, JSFunction::kContextOffset));

  // We call indirectly through the code field in the function to
  // allow recompilation to take effect without changing any of the
  // call sites.
  ld(a3, FieldMemOperand(a1, JSFunction::kCodeEntryOffset));
  InvokeCode(a3, expected, actual, flag, call_wrapper, call_kind);
}


// ---------------------------------------------------------------------------
// Support functions.

void MacroAssembler::TryGetFunctionPrototype(Register function,
                                             Register result,
                                             Register scratch,
                                             Label* miss,
                                             bool miss_on_bound_function) {
  // Check that the receiver isn't a smi.
  JumpIfSmi(function, miss);

  // Check that the function really is a function.  Load map into result reg.
  GetObjectType(function, result, scratch);
  Branch(miss, ne, scratch, Operand(JS_FUNCTION_TYPE));

  if (miss_on_bound_function) {
    ld(scratch,
       FieldMemOperand(function, JSFunction::kSharedFunctionInfoOffset));
    ld4u(scratch,
       FieldMemOperand(scratch, SharedFunctionInfo::kCompilerHintsOffset));
    And(scratch, scratch,
        Operand(1 << SharedFunctionInfo::kBoundFunction));
    Branch(miss, ne, scratch, Operand(zero));
  }

  // Make sure that the function has an instance prototype.
  Label non_instance;
  ld1u(scratch, FieldMemOperand(result, Map::kBitFieldOffset));
  And(scratch, scratch, Operand(1 << Map::kHasNonInstancePrototype));
  Branch(&non_instance, ne, scratch, Operand(zero));

  // Get the prototype or initial map from the function.
  ld(result,
     FieldMemOperand(function, JSFunction::kPrototypeOrInitialMapOffset));

  // If the prototype or initial map is the hole, don't return it and
  // simply miss the cache instead. This will allow us to allocate a
  // prototype object on-demand in the runtime system.
  LoadRoot(t8, Heap::kTheHoleValueRootIndex);
  Branch(miss, eq, result, Operand(t8));

  // If the function does not have an initial map, we're done.
  Label done;
  GetObjectType(result, scratch, scratch);
  Branch(&done, ne, scratch, Operand(MAP_TYPE));

  // Get the prototype from the initial map.
  ld(result, FieldMemOperand(result, Map::kPrototypeOffset));
  jmp(&done);

  // Non-instance prototype: Fetch prototype from constructor field
  // in initial map.
  bind(&non_instance);
  ld(result, FieldMemOperand(result, Map::kConstructorOffset));

  // All done.
  bind(&done);
}


// -----------------------------------------------------------------------------
// Runtime calls.

void MacroAssembler::CallStub(CodeStub* stub,
                              TypeFeedbackId ast_id,
                              Condition cond,
                              Register r1,
                              const Operand& r2) {
  ASSERT(AllowThisStubCall(stub));  // Stub calls are not allowed in some stubs.
  Call(stub->GetCode(isolate()), RelocInfo::CODE_TARGET, ast_id, cond, r1, r2);
}


bool MacroAssembler::AllowThisStubCall(CodeStub* stub) {
  if (!has_frame_ && stub->SometimesSetsUpAFrame()) return false;
  return allow_stub_calls_ || stub->CompilingCallsToThisStubIsGCSafe(isolate());
}


void MacroAssembler::TailCallStub(CodeStub* stub) {
  ASSERT(allow_stub_calls_ ||
         stub->CompilingCallsToThisStubIsGCSafe(isolate()));
  Jump(stub->GetCode(isolate()), RelocInfo::CODE_TARGET);
}

static unsigned long AddressOffset(ExternalReference ref0, ExternalReference ref1) {
  return ref0.address() - ref1.address();
}

void MacroAssembler::CallApiFunctionAndReturn(ExternalReference function,
                                              int stack_space,
                                              bool returns_handle,
                                              int return_value_offset_from_fp) {
  ExternalReference next_address =
      ExternalReference::handle_scope_next_address(isolate());
  const int kNextOffset = 0;
  const long kLimitOffset = AddressOffset(
      ExternalReference::handle_scope_limit_address(isolate()),
      next_address);
  const int kLevelOffset = AddressOffset(
      ExternalReference::handle_scope_level_address(isolate()),
      next_address);

  // Allocate HandleScope in callee-save registers.
  li(s3, Operand(next_address));
  ld(s0, MemOperand(s3, kNextOffset));
  ld(s1, MemOperand(s3, kLimitOffset));
  ld(s2, MemOperand(s3, kLevelOffset));
  Addu(s2, s2, Operand(1));
  st(s2, MemOperand(s3, kLevelOffset));

  if (FLAG_log_timer_events) {
    FrameScope frame(this, StackFrame::MANUAL);
    PushSafepointRegisters();
    PrepareCallCFunction(1, a0);
    li(a0, Operand(ExternalReference::isolate_address(isolate())));
    CallCFunction(ExternalReference::log_enter_external_function(isolate()), 1);
    PopSafepointRegisters();
  }

#if 0
  // The O32 ABI requires us to pass a pointer in a0 where the returned struct
  // (4 bytes) will be placed. This is also built into the Simulator.
  // Set up the pointer to the returned value (a0). It was allocated in
  // EnterExitFrame.
  if (returns_handle) {
    addli(a0, fp, ExitFrameConstants::kStackSpaceOffset);
  }
#endif

  // Native call returns to the DirectCEntry stub which redirects to the
  // return address pushed on stack (could have moved after GC).
  // DirectCEntry stub itself is generated early and never moves.
  DirectCEntryStub stub;
  stub.GenerateCall(this, function);

  if (FLAG_log_timer_events) {
    FrameScope frame(this, StackFrame::MANUAL);
    PushSafepointRegisters();
    PrepareCallCFunction(1, a0);
    li(a0, Operand(ExternalReference::isolate_address(isolate())));
    CallCFunction(ExternalReference::log_leave_external_function(isolate()), 1);
    PopSafepointRegisters();
  }

  Label promote_scheduled_exception;
  Label delete_allocated_handles;
  Label leave_exit_frame;
  Label return_value_loaded;

  if (returns_handle) {
    Label load_return_value;

    Branch(&load_return_value, eq, v0, Operand(zero));
    // Dereference returned value.
    ld(v0, MemOperand(v0));
    Branch(&return_value_loaded);
    bind(&load_return_value);
  }
  // Load value from ReturnValue.
  ld(v0, MemOperand(fp, return_value_offset_from_fp*kPointerSize));
  bind(&return_value_loaded);

  // No more valid handles (the result handle was the last one). Restore
  // previous handle scope.
  st(s0, MemOperand(s3, kNextOffset));
  if (emit_debug_code()) {
    ld(a1, MemOperand(s3, kLevelOffset));
    Check(eq, "Unexpected level after return from api call", a1, Operand(s2));
  }
  Subu(s2, s2, Operand(1));
  st(s2, MemOperand(s3, kLevelOffset));
  ld(at, MemOperand(s3, kLimitOffset));
  Branch(&delete_allocated_handles, ne, s1, Operand(at));

  // Check if the function scheduled an exception.
  bind(&leave_exit_frame);
  LoadRoot(t0, Heap::kTheHoleValueRootIndex);
  li(at, Operand(ExternalReference::scheduled_exception_address(isolate())));
  ld(t1, MemOperand(at));
  Branch(&promote_scheduled_exception, ne, t0, Operand(t1));
  li(s0, Operand(stack_space));
  LeaveExitFrame(false, s0, true);

  bind(&promote_scheduled_exception);
  TailCallExternalReference(
      ExternalReference(Runtime::kPromoteScheduledException, isolate()),
      0,
      1);

  // HandleScope limit has changed. Delete allocated extensions.
  bind(&delete_allocated_handles);
  st(s1, MemOperand(s3, kLimitOffset));
  move(s0, v0);
  move(a0, v0);
  PrepareCallCFunction(1, s1);
  li(a0, Operand(ExternalReference::isolate_address(isolate())));
  CallCFunction(ExternalReference::delete_handle_scope_extensions(isolate()),
      1);
  move(v0, s0);
  jmp(&leave_exit_frame);
}


void MacroAssembler::IllegalOperation(int num_arguments) {
  if (num_arguments > 0) {
    addli(sp, sp, num_arguments * kPointerSize);
  }
  LoadRoot(v0, Heap::kUndefinedValueRootIndex);
}

void MacroAssembler::IndexFromHash(Register hash,
                                   Register index) {
  // If the hash field contains an array index pick it out. The assert checks
  // that the constants for the maximum number of digits for an array index
  // cached in the hash field and the number of bits reserved for it does not
  // conflict.
  ASSERT(TenToThe(String::kMaxCachedArrayIndexLength) <
         (1 << String::kArrayIndexValueBits));
  // We want the smi-tagged index in key.  kArrayIndexValueMask has zeros in
  // the low kHashShift bits.
  STATIC_ASSERT(kSmiTag == 0);
  bfextu(hash, hash, String::kHashShift, String::kHashShift + String::kArrayIndexValueBits - 1);
  sll(index, hash, kSmiTagSize + kSmiShiftSize);
}

void MacroAssembler::CallRuntime(const Runtime::Function* f,
                                 int num_arguments) {
  // All parameters are on the stack. v0 has the return value after call.

  // If the expected number of arguments of the runtime function is
  // constant, we check that the actual number of arguments match the
  // expectation.
  if (f->nargs >= 0 && f->nargs != num_arguments) {
    IllegalOperation(num_arguments);
    return;
  }

  // TODO(1236192): Most runtime routines don't need the number of
  // arguments passed in because it is constant. At some point we
  // should remove this need and make the runtime routine entry code
  // smarter.
  PrepareCEntryArgs(num_arguments);
  PrepareCEntryFunction(ExternalReference(f, isolate()));
  CEntryStub stub(1);
  CallStub(&stub);
}


void MacroAssembler::CallRuntimeSaveDoubles(Runtime::FunctionId id) {
  const Runtime::Function* function = Runtime::FunctionForId(id);
  PrepareCEntryArgs(function->nargs);
  PrepareCEntryFunction(ExternalReference(function, isolate()));
  CEntryStub stub(1, kDontSaveFPRegs);
  CallStub(&stub);
}

void MacroAssembler::CallRuntime(Runtime::FunctionId fid, int num_arguments) {
  CallRuntime(Runtime::FunctionForId(fid), num_arguments);
}

void MacroAssembler::CallExternalReference(const ExternalReference& ext,
                                           int num_arguments) {
  PrepareCEntryArgs(num_arguments);
  PrepareCEntryFunction(ext);

  CEntryStub stub(1);
  CallStub(&stub, TypeFeedbackId::None(), al, zero, Operand(zero));
}


void MacroAssembler::TailCallExternalReference(const ExternalReference& ext,
                                               int num_arguments,
                                               int result_size) {
  // TODO(1236192): Most runtime routines don't need the number of
  // arguments passed in because it is constant. At some point we
  // should remove this need and make the runtime routine entry code
  // smarter.
  PrepareCEntryArgs(num_arguments);
  JumpToExternalReference(ext);
}

void MacroAssembler::TailCallRuntime(Runtime::FunctionId fid,
                                     int num_arguments,
                                     int result_size) {
  TailCallExternalReference(ExternalReference(fid, isolate()),
                            num_arguments,
                            result_size);
}

void MacroAssembler::JumpToExternalReference(const ExternalReference& builtin) {
  PrepareCEntryFunction(builtin);
  CEntryStub stub(1);
  Jump(stub.GetCode(isolate()),
       RelocInfo::CODE_TARGET,
       al,
       zero,
       Operand(zero));
}


void MacroAssembler::InvokeBuiltin(Builtins::JavaScript id,
                                   InvokeFlag flag,
                                   const CallWrapper& call_wrapper) {
  // You can't call a builtin without a valid frame.
  ASSERT(flag == JUMP_FUNCTION || has_frame());

  GetBuiltinEntry(t9, id);
  if (flag == CALL_FUNCTION) {
    call_wrapper.BeforeCall(CallSize(t9));
    SetCallKind(t1, CALL_AS_METHOD);
    Call(t9);
    call_wrapper.AfterCall();
  } else {
    ASSERT(flag == JUMP_FUNCTION);
    SetCallKind(t1, CALL_AS_METHOD);
    Jump(t9);
  }
}


void MacroAssembler::GetBuiltinFunction(Register target,
                                        Builtins::JavaScript id) {
  // Load the builtins object into target register.
  ld(target, MemOperand(cp, Context::SlotOffset(Context::GLOBAL_OBJECT_INDEX)));
  ld(target, FieldMemOperand(target, GlobalObject::kBuiltinsOffset));
  // Load the JavaScript builtin function from the builtins object.
  ld(target, FieldMemOperand(target,
                          JSBuiltinsObject::OffsetOfFunctionWithId(id)));
}

void MacroAssembler::GetBuiltinEntry(Register target, Builtins::JavaScript id) {
  ASSERT(!target.is(a1));
  GetBuiltinFunction(a1, id);
  // Load the code entry point from the builtins object.
  ld(target, FieldMemOperand(a1, JSFunction::kCodeEntryOffset));
}

void MacroAssembler::SetCounter(StatsCounter* counter, int value,
                                Register scratch1, Register scratch2) {
  if (FLAG_native_code_counters && counter->Enabled()) {
    li(scratch1, Operand(value));
    li(scratch2, Operand(ExternalReference(counter)));
    st(scratch1, MemOperand(scratch2));
  }
}

void MacroAssembler::IncrementCounter(StatsCounter* counter, int value,
                                      Register scratch1, Register scratch2) {
  ASSERT(value > 0);
  if (FLAG_native_code_counters && counter->Enabled()) {
    li(scratch2, Operand(ExternalReference(counter)));
    ld(scratch1, MemOperand(scratch2));
    Addu(scratch1, scratch1, Operand(value));
    st(scratch1, MemOperand(scratch2));
  }
}

void MacroAssembler::DecrementCounter(StatsCounter* counter, int value,
                                      Register scratch1, Register scratch2) {
  ASSERT(value > 0);
  if (FLAG_native_code_counters && counter->Enabled()) {
    li(scratch2, Operand(ExternalReference(counter)));
    ld(scratch1, MemOperand(scratch2));
    Subu(scratch1, scratch1, Operand(value));
    st(scratch1, MemOperand(scratch2));
  }
}

// -----------------------------------------------------------------------------
// Debugging.

void MacroAssembler::Assert(Condition cc, const char* msg,
                            Register rs, Operand rt) {
  if (emit_debug_code())
    Check(cc, msg, rs, rt);
}


void MacroAssembler::AssertRegisterIsRoot(Register reg,
                                          Heap::RootListIndex index) {
  if (emit_debug_code()) {
    LoadRoot(at, index);
    Check(eq, "Register did not match expected root", reg, Operand(at));
  }
}


void MacroAssembler::AssertFastElements(Register elements) {
  if (emit_debug_code()) {
    ASSERT(!elements.is(at));
    Label ok;
    push(elements);
    ld(elements, FieldMemOperand(elements, HeapObject::kMapOffset));
    LoadRoot(at, Heap::kFixedArrayMapRootIndex);
    Branch(&ok, eq, elements, Operand(at));
    LoadRoot(at, Heap::kFixedDoubleArrayMapRootIndex);
    Branch(&ok, eq, elements, Operand(at));
    LoadRoot(at, Heap::kFixedCOWArrayMapRootIndex);
    Branch(&ok, eq, elements, Operand(at));
    Abort("JSObject with fast elements map has slow elements");
    bind(&ok);
    pop(elements);
  }
}


void MacroAssembler::Check(Condition cc, const char* msg,
                           Register rs, Operand rt) {
  Label L;
  Branch(&L, cc, rs, rt);
  Abort(msg);
  // Will not return here.
  bind(&L);
}

void MacroAssembler::Abort(const char* msg) {
  Label abort_start;
  bind(&abort_start);
  // We want to pass the msg string like a smi to avoid GC
  // problems, however msg is not guaranteed to be aligned
  // properly. Instead, we pass an aligned pointer that is
  // a proper v8 smi, but also pass the alignment difference
  // from the real pointer as a smi.
  intptr_t p1 = reinterpret_cast<intptr_t>(msg);
  intptr_t p0 = (p1 & ~kSmiTagMask) + kSmiTag;
  ASSERT(reinterpret_cast<Object*>(p0)->IsSmi());
#ifdef DEBUG
  if (msg != NULL) {
    RecordComment("Abort message: ");
    RecordComment(msg);
  }
#endif

  li(a0, Operand(p0));
  push(a0);
  li(a0, Operand(Smi::FromInt(p1 - p0)));
  push(a0);
  // Disable stub call restrictions to always allow calls to abort.
  if (!has_frame_) {
    // We don't actually want to generate a pile of code for this, so just
    // claim there is a stack frame, without generating one.
    FrameScope scope(this, StackFrame::NONE);
    CallRuntime(Runtime::kAbort, 2);
  } else {
    CallRuntime(Runtime::kAbort, 2);
  }
  // Will not return here.
  if (is_trampoline_pool_blocked()) {
    // If the calling code cares about the exact number of
    // instructions generated, we insert padding here to keep the size
    // of the Abort macro constant.
    // Currently in debug mode with debug_code enabled the number of
    // generated instructions is 14, so we use this as a maximum value.
    static const int kExpectedAbortInstructions = 14;
    int abort_instructions = InstructionsGeneratedSince(&abort_start);
    ASSERT(abort_instructions <= kExpectedAbortInstructions);
    while (abort_instructions++ < kExpectedAbortInstructions) {
      nop();
    }
  }
}

void MacroAssembler::LoadContext(Register dst, int context_chain_length) {
  if (context_chain_length > 0) {
    // Move up the chain of contexts to the context containing the slot.
    ld(dst, MemOperand(cp, Context::SlotOffset(Context::PREVIOUS_INDEX)));
    for (int i = 1; i < context_chain_length; i++) {
      ld(dst, MemOperand(dst, Context::SlotOffset(Context::PREVIOUS_INDEX)));
    }
  } else {
    // Slot is in the current function context.  Move it into the
    // destination register in case we store into it (the write barrier
    // cannot be allowed to destroy the context in esi).
    Move(dst, cp);
  }
}


void MacroAssembler::LoadTransitionedArrayMapConditional(
    ElementsKind expected_kind,
    ElementsKind transitioned_kind,
    Register map_in_out,
    Register scratch,
    Label* no_map_match) {
  // Load the global or builtins object from the current context.
  ld(scratch,
     MemOperand(cp, Context::SlotOffset(Context::GLOBAL_OBJECT_INDEX)));
  ld(scratch, FieldMemOperand(scratch, GlobalObject::kNativeContextOffset));

  // Check that the function's map is the same as the expected cached map.
  ld(scratch,
     MemOperand(scratch,
                Context::SlotOffset(Context::JS_ARRAY_MAPS_INDEX)));
  size_t offset = expected_kind * kPointerSize +
      FixedArrayBase::kHeaderSize;
  ld(at, FieldMemOperand(scratch, offset));
  Branch(no_map_match, ne, map_in_out, Operand(at));

  // Use the transitioned cached map.
  offset = transitioned_kind * kPointerSize +
      FixedArrayBase::kHeaderSize;
  ld(map_in_out, FieldMemOperand(scratch, offset));
}

void MacroAssembler::LoadInitialArrayMap(
    Register function_in, Register scratch,
    Register map_out, bool can_have_holes) {
  ASSERT(!function_in.is(map_out));
  Label done;
  ld(map_out, FieldMemOperand(function_in,
                              JSFunction::kPrototypeOrInitialMapOffset));
  if (!FLAG_smi_only_arrays) {
    ElementsKind kind = can_have_holes ? FAST_HOLEY_ELEMENTS : FAST_ELEMENTS;
    LoadTransitionedArrayMapConditional(FAST_SMI_ELEMENTS,
                                        kind,
                                        map_out,
                                        scratch,
                                        &done);
  } else if (can_have_holes) {
    LoadTransitionedArrayMapConditional(FAST_SMI_ELEMENTS,
                                        FAST_HOLEY_SMI_ELEMENTS,
                                        map_out,
                                        scratch,
                                        &done);
  }
  bind(&done);
}

void MacroAssembler::LoadGlobalFunction(int index, Register function) {
  // Load the global or builtins object from the current context.
  ld(function,
     MemOperand(cp, Context::SlotOffset(Context::GLOBAL_OBJECT_INDEX)));
  // Load the native context from the global or builtins object.
  ld(function, FieldMemOperand(function,
                               GlobalObject::kNativeContextOffset));
  // Load the function from the native context.
  ld(function, MemOperand(function, Context::SlotOffset(index)));
}

void MacroAssembler::LoadArrayFunction(Register function) {
  // Load the global or builtins object from the current context.
  ld(function,
     MemOperand(cp, Context::SlotOffset(Context::GLOBAL_OBJECT_INDEX)));
  // Load the global context from the global or builtins object.
  ld(function,
     FieldMemOperand(function, GlobalObject::kGlobalContextOffset));
  // Load the array function from the native context.
  ld(function,
     MemOperand(function, Context::SlotOffset(Context::ARRAY_FUNCTION_INDEX)));
}

void MacroAssembler::LoadGlobalFunctionInitialMap(Register function,
                                                  Register map,
                                                  Register scratch) {
  // Load the initial map. The global functions all have initial maps.
  ld(map, FieldMemOperand(function, JSFunction::kPrototypeOrInitialMapOffset));
  if (emit_debug_code()) {
    Label ok, fail;
    CheckMap(map, scratch, Heap::kMetaMapRootIndex, &fail, DO_SMI_CHECK);
    Branch(&ok);
    bind(&fail);
    Abort("Global functions must have initial map");
    bind(&ok);
  }
}

void MacroAssembler::EnterFrame(StackFrame::Type type) {
  addi(sp, sp, -5 * kPointerSize);
  li(t8, Operand(Smi::FromInt(type)));
  li(t9, Operand(CodeObject()), CONSTANT_SIZE);
  st(lr, MemOperand(sp, 4 * kPointerSize));
  st(fp, MemOperand(sp, 3 * kPointerSize));
  st(cp, MemOperand(sp, 2 * kPointerSize));
  st(t8, MemOperand(sp, 1 * kPointerSize));
  st(t9, MemOperand(sp, 0 * kPointerSize));
  addi(fp, sp, 3 * kPointerSize);
}


void MacroAssembler::LeaveFrame(StackFrame::Type type) {
  move(sp, fp);
  ld(fp, MemOperand(sp, 0 * kPointerSize));
  ld(lr, MemOperand(sp, 1 * kPointerSize));
  addi(sp, sp, 2 * kPointerSize);
}

void MacroAssembler::EnterExitFrame(bool save_doubles,
                                    int stack_space) {
  // Set up the frame structure on the stack.
  STATIC_ASSERT(2 * kPointerSize == ExitFrameConstants::kCallerSPDisplacement);
  STATIC_ASSERT(1 * kPointerSize == ExitFrameConstants::kCallerPCOffset);
  STATIC_ASSERT(0 * kPointerSize == ExitFrameConstants::kCallerFPOffset);

  // This is how the stack will look:
  // fp + 2 (==kCallerSPDisplacement) - old stack's end
  // [fp + 1 (==kCallerPCOffset)] - saved old ra
  // [fp + 0 (==kCallerFPOffset)] - saved old fp
  // [fp - 1 (==kSPOffset)] - sp of the called function
  // [fp - 2 (==kCodeOffset)] - CodeObject
  // fp - (2 + stack_space + alignment) == sp == [fp - kSPOffset] - top of the
  //   new stack (will contain saved ra)

  // Save registers.
  addi(sp, sp, -4 * kPointerSize);
  st(lr, MemOperand(sp, 3 * kPointerSize));
  st(fp, MemOperand(sp, 2 * kPointerSize));
  addi(fp, sp, 2 * kPointerSize);  // Set up new frame pointer.

  if (emit_debug_code()) {
    st(zero, MemOperand(fp, ExitFrameConstants::kSPOffset));
  }

  // Accessed from ExitFrame::code_slot.
  li(t8, Operand(CodeObject()), CONSTANT_SIZE);
  st(t8, MemOperand(fp, ExitFrameConstants::kCodeOffset));

  // Save the frame pointer and the context in top.
  li(t8, Operand(ExternalReference(Isolate::kCEntryFPAddress, isolate())));
  st(fp, MemOperand(t8));
  li(t8, Operand(ExternalReference(Isolate::kContextAddress, isolate())));
  st(cp, MemOperand(t8));

  const int frame_alignment = MacroAssembler::ActivationFrameAlignment();

  // Reserve place for the return address, stack space and an optional slot
  // (used by the DirectCEntryStub to hold the return value if a struct is
  // returned) and align the frame preparing for calling the runtime function.
  ASSERT(stack_space >= 0);
  Subu(sp, sp, Operand((stack_space + 2) * kPointerSize));
  if (frame_alignment > 0) {
    ASSERT(IsPowerOf2(frame_alignment));
    And(sp, sp, Operand(-frame_alignment));  // Align stack.
  }

  // Set the exit frame sp value to point just before the return address
  // location.
  addi(at2, sp, kPointerSize);
  st(at2, MemOperand(fp, ExitFrameConstants::kSPOffset));
}

void MacroAssembler::LeaveExitFrame(bool save_doubles,
                                    Register argument_count,
                                    bool do_return) {

  // Clear top frame.
  li(t8, Operand(ExternalReference(Isolate::kCEntryFPAddress, isolate())));
  st(zero, MemOperand(t8));

  // Restore current context from top and clear it in debug mode.
  li(t8, Operand(ExternalReference(Isolate::kContextAddress, isolate())));
  ld(cp, MemOperand(t8));
#ifdef DEBUG
  st(r3, MemOperand(t8));
#endif

  // Pop the arguments, restore registers, and return.
  move(sp, fp);  // Respect ABI stack constraint.
  ld(fp, MemOperand(sp, ExitFrameConstants::kCallerFPOffset));
  ld(lr, MemOperand(sp, ExitFrameConstants::kCallerPCOffset));

  if (argument_count.is_valid()) {
    sll(t8, argument_count, kPointerSizeLog2);
    add(sp, sp, t8);
  }

  if (do_return) {
    addi(sp, sp, 16);
    Ret();
  }
  addi(sp, sp, 16);
}

int MacroAssembler::ActivationFrameAlignment() {
#if defined(V8_HOST_ARCH_TILEGX)
  // Running on the real platform. Use the alignment as mandated by the local
  // environment.
  // Note: This will break if we ever start generating snapshots on one TileGX
  // platform for another TileGX platform with a different alignment.
  return OS::ActivationFrameAlignment();
#else  // defined(V8_HOST_ARCH_TILEGX)
  // No Simulator support for TileGX
  UNREACHABLE();
  return -1;
#endif  // defined(V8_HOST_ARCH_TILEGX)
}


void MacroAssembler::AssertStackIsAligned() {
  if (emit_debug_code()) {
    const int frame_alignment = ActivationFrameAlignment();
    const int frame_alignment_mask = frame_alignment - 1;

    if (frame_alignment > kPointerSize) {
      Label alignment_as_expected;
      ASSERT(IsPowerOf2(frame_alignment));
      andi(at, sp, frame_alignment_mask);
      Branch(&alignment_as_expected, eq, at, Operand(zero));
      // Don't use Check here, as it will call Runtime_Abort re-entering here.
      stop("Unexpected stack alignment");
      bind(&alignment_as_expected);
    }
  }
}

void MacroAssembler::UntagAndJumpIfSmi(Register dst,
                                       Register src,
                                       Label* smi_case) {
  move(at2, src);
  SmiUntag(dst, src);
  JumpIfSmi(at2, smi_case, at);
}

void MacroAssembler::UntagAndJumpIfNotSmi(Register dst,
                                          Register src,
                                          Label* non_smi_case) {
  move(at2, src);
  SmiUntag(dst, src);
  JumpIfNotSmi(at2, non_smi_case, at);
}

void MacroAssembler::JumpIfSmi(Register value,
                               Label* smi_label,
                               Register scratch) {
  ASSERT_EQ(0, kSmiTag);
  andi(scratch, value, kSmiTagMask);
  Branch(smi_label, eq, scratch, Operand(zero));
}

void MacroAssembler::JumpIfNotHeapNumber(Register object,
                                         Register heap_number_map,
                                         Register scratch,
                                         Label* on_not_heap_number) {
  ld(scratch, FieldMemOperand(object, HeapObject::kMapOffset));
  AssertRegisterIsRoot(heap_number_map, Heap::kHeapNumberMapRootIndex);
  Branch(on_not_heap_number, ne, scratch, Operand(heap_number_map));
}

void MacroAssembler::JumpIfNotSmi(Register value,
                                  Label* not_smi_label,
                                  Register scratch) {
  ASSERT_EQ(0, kSmiTag);
  andi(scratch, value, kSmiTagMask);
  Branch(not_smi_label, ne, scratch, Operand(zero));
}

void MacroAssembler::JumpIfNotBothSmi(Register reg1,
                                      Register reg2,
                                      Label* on_not_both_smi) {
  STATIC_ASSERT(kSmiTag == 0);
  ASSERT_EQ(1, (int)kSmiTagMask);
  or_(at, reg1, reg2);
  JumpIfNotSmi(at, on_not_both_smi);
}

void MacroAssembler::JumpIfEitherSmi(Register reg1,
                                     Register reg2,
                                     Label* on_either_smi) {
  STATIC_ASSERT(kSmiTag == 0);
  ASSERT_EQ(1, (int)kSmiTagMask);
  // Both Smi tags must be 1 (not Smi).
  and_(at, reg1, reg2);
  JumpIfSmi(at, on_either_smi);
}

void MacroAssembler::AssertNotSmi(Register object) {
  if (emit_debug_code()) {
    STATIC_ASSERT(kSmiTag == 0);
    andi(at, object, kSmiTagMask);
    Check(ne, "Operand is a smi", at, Operand(zero));
  }
}

void MacroAssembler::AssertSmi(Register object) {
  if (emit_debug_code()) {
    STATIC_ASSERT(kSmiTag == 0);
    andi(at, object, kSmiTagMask);
    Check(eq, "Operand is a smi", at, Operand(zero));
  }
}

void MacroAssembler::AssertString(Register object) {
  if (emit_debug_code()) {
    STATIC_ASSERT(kSmiTag == 0);
    And(t0, object, Operand(kSmiTagMask));
    Check(ne, "Operand is a smi and not a string", t0, Operand(zero));
    push(object);
    ld(object, FieldMemOperand(object, HeapObject::kMapOffset));
    ld1u(object, FieldMemOperand(object, Map::kInstanceTypeOffset));
    Check(lo, "Operand is not a string", object, Operand(FIRST_NONSTRING_TYPE));
    pop(object);
  }
}

void MacroAssembler::AssertName(Register object) {
  if (emit_debug_code()) {
    STATIC_ASSERT(kSmiTag == 0);
    And(t0, object, Operand(kSmiTagMask));
    Check(ne, "Operand is a smi and not a name", t0, Operand(zero));
    push(object);
    ld(object, FieldMemOperand(object, HeapObject::kMapOffset));
    ld1u(object, FieldMemOperand(object, Map::kInstanceTypeOffset));
    Check(le, "Operand is not a name", object, Operand(LAST_NAME_TYPE));
    pop(object);
  }
}

void MacroAssembler::AssertRootValue(Register src,
                                     Heap::RootListIndex root_value_index,
                                     const char* message) {
  if (emit_debug_code()) {
    ASSERT(!src.is(at));
    LoadRoot(at, root_value_index);
    Check(eq, message, src, Operand(at));
  }
}


void MacroAssembler::JumpIfNonSmisNotBothSequentialAsciiStrings(
    Register first,
    Register second,
    Register scratch1,
    Register scratch2,
    Label* failure) {
  // Test that both first and second are sequential ASCII strings.
  // Assume that they are non-smis.
  ld(scratch1, FieldMemOperand(first, HeapObject::kMapOffset));
  ld(scratch2, FieldMemOperand(second, HeapObject::kMapOffset));
  ld1u(scratch1, FieldMemOperand(scratch1, Map::kInstanceTypeOffset));
  ld1u(scratch2, FieldMemOperand(scratch2, Map::kInstanceTypeOffset));

  JumpIfBothInstanceTypesAreNotSequentialAscii(scratch1,
                                               scratch2,
                                               scratch1,
                                               scratch2,
                                               failure);
}

void MacroAssembler::JumpIfNotBothSequentialAsciiStrings(Register first,
                                                         Register second,
                                                         Register scratch1,
                                                         Register scratch2,
                                                         Label* failure) {
  // Check that neither is a smi.
  STATIC_ASSERT(kSmiTag == 0);
  And(scratch1, first, Operand(second));
  JumpIfSmi(scratch1, failure);
  JumpIfNonSmisNotBothSequentialAsciiStrings(first,
                                             second,
                                             scratch1,
                                             scratch2,
                                             failure);
}

void MacroAssembler::JumpIfBothInstanceTypesAreNotSequentialAscii(
    Register first,
    Register second,
    Register scratch1,
    Register scratch2,
    Label* failure) {
  int kFlatAsciiStringMask =
      kIsNotStringMask | kStringEncodingMask | kStringRepresentationMask;
  int kFlatAsciiStringTag = ASCII_STRING_TYPE;
  li(scratch1, Operand(kFlatAsciiStringMask));
  and_(scratch1, first, scratch1);
  Branch(failure, ne, scratch1, Operand(kFlatAsciiStringTag));
  li(scratch2, Operand(kFlatAsciiStringMask));
  and_(scratch2, second, scratch2);
  Branch(failure, ne, scratch2, Operand(kFlatAsciiStringTag));
}


void MacroAssembler::JumpIfInstanceTypeIsNotSequentialAscii(Register type,
                                                            Register scratch,
                                                            Label* failure) {
  int kFlatAsciiStringMask =
      kIsNotStringMask | kStringEncodingMask | kStringRepresentationMask;
  int kFlatAsciiStringTag = ASCII_STRING_TYPE;
  And(scratch, type, Operand(kFlatAsciiStringMask));
  Branch(failure, ne, scratch, Operand(kFlatAsciiStringTag));
}

static const int kRegisterPassedArguments = 10;

int MacroAssembler::CalculateStackPassedWords(int num_reg_arguments) {
  int stack_passed_words = 0;

  // Up to ten simple arguments are passed in registers r0..r9.
  if (num_reg_arguments > kRegisterPassedArguments) {
    stack_passed_words += num_reg_arguments - kRegisterPassedArguments;
  }
  return stack_passed_words;
}

void MacroAssembler::PrepareCallCFunction(int num_reg_arguments,
                                          Register scratch) {
  int frame_alignment = ActivationFrameAlignment();

  // Up to ten simple arguments are passed in registers r0..r9.
  // Remaining arguments are pushed on the stack.
  int stack_passed_arguments = CalculateStackPassedWords(num_reg_arguments);
  if (frame_alignment > kPointerSize) {
    // Make stack end at alignment and make room for num_arguments - 4 words
    // and the original value of sp.
    move(scratch, sp);
    Subu(sp, sp, Operand((stack_passed_arguments + 1) * kPointerSize));
    ASSERT(IsPowerOf2(frame_alignment));
    And(sp, sp, Operand(-frame_alignment));
    st(scratch, MemOperand(sp, stack_passed_arguments * kPointerSize));
    // TileGX special stack reserve area on the bottom of stack.
    addi(sp, sp, -16);
  } else {
    Subu(sp, sp, Operand((stack_passed_arguments + 2 ) * kPointerSize));
  }
}

void MacroAssembler::CallCFunction(ExternalReference function,
                                   int num_arguments) {
  li(t8, Operand(function));
  CallCFunctionHelper(t8, num_arguments);
}


void MacroAssembler::CallCFunction(Register function,
                                   int num_arguments) {
  CallCFunctionHelper(function, num_arguments);
}

void MacroAssembler::CallCFunctionHelper(Register function,
                                         int num_reg_arguments) {
  ASSERT(has_frame());
  // Make sure that the stack is aligned before calling a C function unless
  // running in the simulator. The simulator has its own alignment check which
  // provides more information.
  // The argument stots are presumed to have been set up by
  // PrepareCallCFunction. The C function must be called via t9, for mips ABI.

#if defined(V8_HOST_ARCH_TILEGX)
  if (emit_debug_code()) {
    int frame_alignment = OS::ActivationFrameAlignment();
    int frame_alignment_mask = frame_alignment - 1;
    if (frame_alignment > kPointerSize) {
      ASSERT(IsPowerOf2(frame_alignment));
      Label alignment_as_expected;
      And(at, sp, Operand(frame_alignment_mask));
      Branch(&alignment_as_expected, eq, at, Operand(zero));
      // Don't use Check here, as it will call Runtime_Abort possibly
      // re-entering here.
      stop("Unexpected alignment in CallCFunction");
      bind(&alignment_as_expected);
    }
  }
#endif  // V8_HOST_ARCH_TILEGX

  Call(function);

  int stack_passed_arguments = CalculateStackPassedWords(num_reg_arguments);

  if (OS::ActivationFrameAlignment() > kPointerSize) {
    // Restore TileGX special stack zone first.
    addi(sp, sp, 16);
    ld(sp, MemOperand(sp, stack_passed_arguments * kPointerSize));
  } else {
    Addu(sp, sp, Operand((stack_passed_arguments + 2) * kPointerSize));
  }
}

#undef BRANCH_ARGS_CHECK


void MacroAssembler::CheckPageFlag(
    Register object,
    Register scratch,
    int mask,
    Condition cc,
    Label* condition_met) {
  And(scratch, object, Operand(~Page::kPageAlignmentMask));
  ld4u(scratch, MemOperand(scratch, MemoryChunk::kFlagsOffset));
  And(scratch, scratch, Operand(mask));
  Branch(condition_met, cc, scratch, Operand(zero));
}


void MacroAssembler::CheckMapDeprecated(Handle<Map> map,
                                        Register scratch,
                                        Label* if_deprecated) {
  if (map->CanBeDeprecated()) {
    li(scratch, Operand(map));
    ld(scratch, FieldMemOperand(scratch, Map::kBitField3Offset));
    And(scratch, scratch, Operand(Smi::FromInt(Map::Deprecated::kMask)));
    Branch(if_deprecated, ne, scratch, Operand(zero));
  }
}


void MacroAssembler::JumpIfBlack(Register object,
                                 Register scratch0,
                                 Register scratch1,
                                 Label* on_black) {
  HasColor(object, scratch0, scratch1, on_black, 1, 0);  // kBlackBitPattern.
  ASSERT(strcmp(Marking::kBlackBitPattern, "10") == 0);
}


void MacroAssembler::HasColor(Register object,
                              Register bitmap_scratch,
                              Register mask_scratch,
                              Label* has_color,
                              int first_bit,
                              int second_bit) {
  ASSERT(!AreAliased(object, bitmap_scratch, mask_scratch, t8));
  ASSERT(!AreAliased(object, bitmap_scratch, mask_scratch, t9));

  GetMarkBits(object, bitmap_scratch, mask_scratch);

  Label other_color, word_boundary;
  ld(t9, MemOperand(bitmap_scratch, MemoryChunk::kHeaderSize));
  And(t8, t9, Operand(mask_scratch));
  Branch(&other_color, first_bit == 1 ? eq : ne, t8, Operand(zero));
  // Shift left 1 by adding.
  Addu(mask_scratch, mask_scratch, Operand(mask_scratch));
  Branch(&word_boundary, eq, mask_scratch, Operand(zero));
  And(t8, t9, Operand(mask_scratch));
  Branch(has_color, second_bit == 1 ? ne : eq, t8, Operand(zero));
  jmp(&other_color);

  bind(&word_boundary);
  ld(t9, MemOperand(bitmap_scratch, MemoryChunk::kHeaderSize + kPointerSize));
  And(t9, t9, Operand(1));
  Branch(has_color, second_bit == 1 ? ne : eq, t9, Operand(zero));
  bind(&other_color);
}

// Detect some, but not all, common pointer-free objects.  This is used by the
// incremental write barrier which doesn't care about oddballs (they are always
// marked black immediately so this code is not hit).
void MacroAssembler::JumpIfDataObject(Register value,
                                      Register scratch,
                                      Label* not_data_object) {
  ASSERT(!AreAliased(value, scratch, t8, no_reg));
  Label is_data_object;
  ld(scratch, FieldMemOperand(value, HeapObject::kMapOffset));
  LoadRoot(t8, Heap::kHeapNumberMapRootIndex);
  Branch(&is_data_object, eq, t8, Operand(scratch));
  ASSERT(kIsIndirectStringTag == 1 && kIsIndirectStringMask == 1);
  ASSERT(kNotStringTag == 0x80 && kIsNotStringMask == 0x80);
  // If it's a string and it's not a cons string then it's an object containing
  // no GC pointers.
  ld1u(scratch, FieldMemOperand(scratch, Map::kInstanceTypeOffset));
  And(t8, scratch, Operand(kIsIndirectStringMask | kIsNotStringMask));
  Branch(not_data_object, ne, t8, Operand(zero));
  bind(&is_data_object);
}


void MacroAssembler::GetMarkBits(Register addr_reg,
                                 Register bitmap_reg,
                                 Register mask_reg) {
  ASSERT(!AreAliased(addr_reg, bitmap_reg, mask_reg, no_reg));
  And(bitmap_reg, addr_reg, Operand(~Page::kPageAlignmentMask));
  bfextu(mask_reg, addr_reg, kPointerSizeLog2, kPointerSizeLog2 + Bitmap::kBitsPerCellLog2 - 1);
  const int kLowBits = kPointerSizeLog2 + Bitmap::kBitsPerCellLog2;
  bfextu(t8, addr_reg, kLowBits, kLowBits + kPageSizeBits - kLowBits - 1);
  sll(t8, t8, kPointerSizeLog2);
  Addu(bitmap_reg, bitmap_reg, t8);
  li(t8, Operand(1));
  sll(mask_reg, t8, mask_reg);
}


void MacroAssembler::EnsureNotWhite(
    Register value,
    Register bitmap_scratch,
    Register mask_scratch,
    Register load_scratch,
    Label* value_is_white_and_not_data) {
  ASSERT(!AreAliased(value, bitmap_scratch, mask_scratch, t8));
  GetMarkBits(value, bitmap_scratch, mask_scratch);

  // If the value is black or grey we don't need to do anything.
  ASSERT(strcmp(Marking::kWhiteBitPattern, "00") == 0);
  ASSERT(strcmp(Marking::kBlackBitPattern, "10") == 0);
  ASSERT(strcmp(Marking::kGreyBitPattern, "11") == 0);
  ASSERT(strcmp(Marking::kImpossibleBitPattern, "01") == 0);

  Label done;

  // Since both black and grey have a 1 in the first position and white does
  // not have a 1 there we only need to check one bit.
  ld(load_scratch, MemOperand(bitmap_scratch, MemoryChunk::kHeaderSize));
  And(t8, mask_scratch, load_scratch);
  Branch(&done, ne, t8, Operand(zero));

  // FIXME
  if (0 && emit_debug_code()) {
    // Check for impossible bit pattern.
    Label ok;
    // sll may overflow, making the check conservative.
    sll(t8, mask_scratch, 1);
    And(t8, load_scratch, t8);
    Branch(&ok, eq, t8, Operand(zero));
    stop("Impossible marking bit pattern");
    bind(&ok);
  }

  // Value is white.  We check whether it is data that doesn't need scanning.
  // Currently only checks for HeapNumber and non-cons strings.
  Register map = load_scratch;  // Holds map while checking type.
  Register length = load_scratch;  // Holds length of object after testing type.
  Label is_data_object;

  // Check for heap-number
  ld(map, FieldMemOperand(value, HeapObject::kMapOffset));
  LoadRoot(t8, Heap::kHeapNumberMapRootIndex);
  {
    Label skip;
    Branch(&skip, ne, t8, Operand(map));
    li(length, HeapNumber::kSize);
    Branch(&is_data_object);
    bind(&skip);
  }

  // Check for strings.
  ASSERT(kIsIndirectStringTag == 1 && kIsIndirectStringMask == 1);
  ASSERT(kNotStringTag == 0x80 && kIsNotStringMask == 0x80);
  // If it's a string and it's not a cons string then it's an object containing
  // no GC pointers.
  Register instance_type = load_scratch;
  ld1u(instance_type, FieldMemOperand(map, Map::kInstanceTypeOffset));
  And(t8, instance_type, Operand(kIsIndirectStringMask | kIsNotStringMask));
  Branch(value_is_white_and_not_data, ne, t8, Operand(zero));
  // It's a non-indirect (non-cons and non-slice) string.
  // If it's external, the length is just ExternalString::kSize.
  // Otherwise it's String::kHeaderSize + string->length() * (1 or 2).
  // External strings are the only ones with the kExternalStringTag bit
  // set.
  ASSERT_EQ(0, kSeqStringTag & kExternalStringTag);
  ASSERT_EQ(0, kConsStringTag & kExternalStringTag);
  And(t8, instance_type, Operand(kExternalStringTag));
  {
    Label skip;
    Branch(&skip, eq, t8, Operand(zero));
    li(length, ExternalString::kSize);
    Branch(&is_data_object);
    bind(&skip);
  }

  // Sequential string, either ASCII or UC16.
  // For ASCII (char-size of 1) we shift the smi tag away to get the length.
  // For UC16 (char-size of 2) we just leave the smi tag in place, thereby
  // getting the length multiplied by 2.
  ASSERT(kOneByteStringTag == 4 && kStringEncodingMask == 4);
  ASSERT(kSmiTag == 0 && kSmiTagSize == 1);
  ld(t9, FieldMemOperand(value, String::kLengthOffset));
  And(t8, instance_type, Operand(kStringEncodingMask));
  {
    Label skip;
    srl(t9, t9, 32);
    sll(t9, t9, 1);
    Branch(&skip, eq, t8, Operand(zero));
    srl(t9, t9, 1);
    bind(&skip);
  }
  Addu(length, t9, Operand(SeqString::kHeaderSize + kObjectAlignmentMask));
  And(length, length, Operand(~kObjectAlignmentMask));

  bind(&is_data_object);
  // Value is a data object, and it is white.  Mark it black.  Since we know
  // that the object is white we can make it black by flipping one bit.
  ld(t8, MemOperand(bitmap_scratch, MemoryChunk::kHeaderSize));
  Or(t8, t8, Operand(mask_scratch));
  st(t8, MemOperand(bitmap_scratch, MemoryChunk::kHeaderSize));

  And(bitmap_scratch, bitmap_scratch, Operand(~Page::kPageAlignmentMask));
  ld4u(t8, MemOperand(bitmap_scratch, MemoryChunk::kLiveBytesOffset));
  Addu(t8, t8, Operand(length));
  st4(t8, MemOperand(bitmap_scratch, MemoryChunk::kLiveBytesOffset));

  bind(&done);
}


void MacroAssembler::LoadInstanceDescriptors(Register map,
                                             Register descriptors) {
  ld(descriptors, FieldMemOperand(map, Map::kDescriptorsOffset));
}


void MacroAssembler::NumberOfOwnDescriptors(Register dst, Register map) {
  ld(dst, FieldMemOperand(map, Map::kBitField3Offset));
  DecodeField<Map::NumberOfOwnDescriptorsBits>(dst);
}


void MacroAssembler::EnumLength(Register dst, Register map) {
  STATIC_ASSERT(Map::EnumLengthBits::kShift == 0);
  ld(dst, FieldMemOperand(map, Map::kBitField3Offset));
  And(dst, dst, Operand(Smi::FromInt(Map::EnumLengthBits::kMask)));
}

void MacroAssembler::CheckEnumCache(Register null_value, Label* call_runtime) {
  Register  empty_fixed_array_value = t2;
  LoadRoot(empty_fixed_array_value, Heap::kEmptyFixedArrayRootIndex);
  Label next, start;
  move(a2, a0);

  // Check if the enum length field is properly initialized, indicating that
  // there is an enum cache.
  ld(a1, FieldMemOperand(a2, HeapObject::kMapOffset));

  EnumLength(a3, a1);
  Branch(call_runtime, eq, a3, Operand(Smi::FromInt(Map::kInvalidEnumCache)));

  jmp(&start);

  bind(&next);
  ld(a1, FieldMemOperand(a2, HeapObject::kMapOffset));

  // For all objects but the receiver, check that the cache is empty.
  EnumLength(a3, a1);
  Branch(call_runtime, ne, a3, Operand(Smi::FromInt(0)));

  bind(&start);

  // Check that there are no elements. Register r2 contains the current JS
  // object we've reached through the prototype chain.
  ld(a2, FieldMemOperand(a2, JSObject::kElementsOffset));
  Branch(call_runtime, ne, a2, Operand(empty_fixed_array_value));

  ld(a2, FieldMemOperand(a1, Map::kPrototypeOffset));
  Branch(&next, ne, a2, Operand(null_value));
}


void MacroAssembler::ClampUint8(Register output_reg, Register input_reg) {
  ASSERT(!output_reg.is(input_reg));
  Label done;
  li(output_reg, Operand(255));
  // Normal branch: nop in delay slot.
  Branch(&done, gt, input_reg, Operand(output_reg));
  // Use delay slot in this branch.
  move(output_reg, zero);  // In delay slot.
  Branch(&done, lt, input_reg, Operand(zero));
  move(output_reg, input_reg);  // Value is in range 0..255.
  bind(&done);
}

void MacroAssembler::ClampDoubleToUint8(Register result_reg,
                                        Register input_reg,
                                        Register temp_reg,
                                        Register temp_reg1,
                                        Register temp_reg2) {
  Label above_zero;
  Label done;
  Label in_bounds;

  fdouble_add_flags(temp_reg, input_reg, zero);
  bfextu(temp_reg, temp_reg, 28, 28); // gt
  Branch(&above_zero, ne, temp_reg, Operand(zero));

  // Double value is less than zero, NaN or Inf, return 0.
  move(result_reg, zero);
  Branch(&done);

  // Double value is >= 255, return 255.
  bind(&above_zero);
  li(temp_reg, Operand(0x406fe00000000000L));
  fdouble_add_flags(temp_reg, input_reg, temp_reg);
  bfextu(temp_reg, temp_reg, 27, 27); // le
  Branch(&in_bounds, ne, temp_reg, Operand(zero));
  li(result_reg, Operand(255));
  Branch(&done);

  // In 0-255 range, round and truncate.
  bind(&in_bounds);
  //cvt_w_d(temp_reg, input_reg);
  move(result_reg, input_reg);
  ConvertToInt32(zero, result_reg, input_reg, temp_reg, temp_reg1, temp_reg2, NULL, true, false);
  bind(&done);
}

void MacroAssembler::TestJSArrayForAllocationSiteInfo(
    Register receiver_reg,
    Register scratch_reg,
    Condition cond,
    Label* allocation_info_present) {
  Label no_info_available;
  ExternalReference new_space_start =
      ExternalReference::new_space_start(isolate());
  ExternalReference new_space_allocation_top =
      ExternalReference::new_space_allocation_top_address(isolate());
  Addu(scratch_reg, receiver_reg,
       Operand(JSArray::kSize + AllocationSiteInfo::kSize - kHeapObjectTag));
  Branch(&no_info_available, lt, scratch_reg, Operand(new_space_start));
  li(at, Operand(new_space_allocation_top));
  ld(at, MemOperand(at));
  Branch(&no_info_available, gt, scratch_reg, Operand(at));
  ld(scratch_reg, MemOperand(scratch_reg, -AllocationSiteInfo::kSize));
  Branch(allocation_info_present, cond, scratch_reg,
      Operand(Handle<Map>(isolate()->heap()->allocation_site_info_map())));
  bind(&no_info_available);
}

void MacroAssembler::GetObjectType(Register object,
                                   Register map,
                                   Register type_reg) {
  ld(map, FieldMemOperand(object, HeapObject::kMapOffset));
  ld1u(type_reg, FieldMemOperand(map, Map::kInstanceTypeOffset));
}

void MacroAssembler::SmiTagCheckOverflow(Register reg, Register overflow) {
  ASSERT(!reg.is(overflow));
  move(overflow, reg);  // Save original value.
  SmiTag(reg);
  xor_(overflow, overflow, reg);  // Overflow if (value ^ 2 * value) < 0.
}


void MacroAssembler::SmiTagCheckOverflow(Register dst,
                                         Register src,
                                         Register overflow) {
  if (dst.is(src)) {
    // Fall back to slower case.
    SmiTagCheckOverflow(dst, overflow);
  } else {
    ASSERT(!dst.is(src));
    ASSERT(!dst.is(overflow));
    ASSERT(!src.is(overflow));
    SmiTag(dst, src);
    xor_(overflow, dst, src);  // Overflow if (value ^ 2 * value) < 0.
  }
}

void MacroAssembler::IsObjectJSStringType(Register object,
                                          Register scratch,
                                          Label* fail) {
  ASSERT(kNotStringTag != 0);

  ld(scratch, FieldMemOperand(object, HeapObject::kMapOffset));
  ld1u(scratch, FieldMemOperand(scratch, Map::kInstanceTypeOffset));
  And(scratch, scratch, Operand(kIsNotStringMask));
  Branch(fail, ne, scratch, Operand(zero));
}


void MacroAssembler::IsObjectNameType(Register object,
                                      Register scratch,
                                      Label* fail) {
  ld(scratch, FieldMemOperand(object, HeapObject::kMapOffset));
  ld1u(scratch, FieldMemOperand(scratch, Map::kInstanceTypeOffset));
  Branch(fail, hi, scratch, Operand(LAST_NAME_TYPE));
}

void MacroAssembler::IsInstanceJSObjectType(Register map,
                                            Register scratch,
                                            Label* fail) {
  ld1u(scratch, FieldMemOperand(map, Map::kInstanceTypeOffset));
  Branch(fail, lt, scratch, Operand(FIRST_NONCALLABLE_SPEC_OBJECT_TYPE));
  Branch(fail, gt, scratch, Operand(LAST_NONCALLABLE_SPEC_OBJECT_TYPE));
}

void MacroAssembler::IsObjectJSObjectType(Register heap_object,
                                          Register map,
                                          Register scratch,
                                          Label* fail) {
  ld(map, FieldMemOperand(heap_object, HeapObject::kMapOffset));
  IsInstanceJSObjectType(map, scratch, fail);
}

void MacroAssembler::PatchRelocatedValue(Register li_location,
                                         Register scratch,
                                         Register new_value) {
  ld(scratch, MemOperand(li_location));
  // At this point scratch is a lui(at, ...) instruction.
  if (emit_debug_code()) {
    //FIXME
#if 0
    And(scratch, scratch, kOpcodeMask);
    Check(eq, "The instruction to patch should be a lui.",
        scratch, Operand(LUI));
#endif
    ld(scratch, MemOperand(li_location));
  }
  srl(t9, new_value, kImm16Bits);
  bfins(scratch, t9, 0, kImm16Bits - 1);
  st(scratch, MemOperand(li_location));

  ld(scratch, MemOperand(li_location, kInstrSize));
  // scratch is now ori(at, ...).
  if (emit_debug_code()) {
    //FIXME
#if 0
    And(scratch, scratch, kOpcodeMask);
    Check(eq, "The instruction to patch should be an ori.",
        scratch, Operand(ORI));
#endif
    ld(scratch, MemOperand(li_location, kInstrSize));
  }
  bfins(scratch, new_value, 0, kImm16Bits - 1);
  st(scratch, MemOperand(li_location, kInstrSize));

  // Update the I-cache so the new lui and ori can be executed.
  FlushICache(li_location, 2);
}

void MacroAssembler::GetRelocatedValue(Register li_location,
                                       Register value,
                                       Register scratch) {
  ld(value, MemOperand(li_location));
  if (emit_debug_code()) {
    //FIXME
#if 0
    And(value, value, kOpcodeMask);
    Check(eq, "The instruction should be a lui.",
        value, Operand(LUI));
#endif
    ld(value, MemOperand(li_location));
  }

  // value now holds a lui instruction. Extract the immediate.
  sll(value, value, kImm16Bits);

  ld(scratch, MemOperand(li_location, kInstrSize));
  if (emit_debug_code()) {
    //FIXME
#if 0
    And(scratch, scratch, kOpcodeMask);
    Check(eq, "The instruction should be an ori.",
        scratch, Operand(ORI));
#endif
    ld(scratch, MemOperand(li_location, kInstrSize));
  }
  // "scratch" now holds an ori instruction. Extract the immediate.
  // FIXME
  li(at, Operand(kImm16Mask));
  and_(scratch, scratch, at);

  // Merge the results.
  or_(value, value, scratch);
}

// Tries to get a signed int32 out of a double precision floating point heap
// number. Rounds towards 0. Branch to 'not_int32' if the double is out of the
// 32bits signed integer range.
// This method implementation differs from the ARM version for performance
// reasons.
void MacroAssembler::ConvertToInt32(Register source,
                                    Register dest,
                                    Register scratch1,
                                    Register scratch2,
                                    Register scratch3,
                                    Register scratch4,
				    Label *not_int32,
				    bool gcc_mode,
				    bool need_load) {
  if (gcc_mode) {
  Label done, cont, cont_1, cont_2;
  if (need_load)
    ld(dest, FieldMemOperand(source, HeapNumber::kValueOffset));

  bfextu(scratch1, dest, 52, 62);
  moveli(scratch4, 1054);
  cmples(scratch3, scratch1, scratch4);
  srl(scratch2, dest, 63);
  bfextu(scratch4, dest, 0, 51);
  Branch(&cont, ne, scratch3, Operand(zero));

  moveli(dest, 2047);
  cmpne(scratch4, scratch4, zero);
  cmpeq(scratch1, scratch1, dest);
  and_(scratch1, scratch1, scratch4);
  Branch(&cont_2, eq, scratch1, Operand(zero));

  bind(&cont_1);
  moveli(dest, 32767);
  shl16insli(dest, dest, -1);
  Branch(&done);

  bind(&cont);
  moveli(dest, 1022);
  cmples(scratch3, scratch1, dest);
  move(dest, zero);
  Branch(&done, ne, scratch3, Operand(zero));
  moveli(dest, 1);
  moveli(scratch3, 1075);
  sll(dest, dest, 52);
  subx(scratch1, scratch3, scratch1);
  or_(dest, scratch4, dest);
  srl(dest, dest, scratch1);
  addxi(dest, dest, 0);
  subx(scratch1, zero, dest);
  movn(dest, scratch1, scratch2);
  srlx(scratch1, dest, 31);
  cmpeq(scratch1, scratch1, scratch2);
  Branch(&done, ne, scratch1, Operand(zero));

  bind(&cont_2);
  moveli(dest, -1);
  sll(dest, dest, 31);
  Branch(&cont_1, eq, scratch2, Operand(zero));

  bind(&done);
  } else {

  Label right_exponent, done;
  // Get exponent word (ENDIAN issues).
  ld(scratch1, FieldMemOperand(source, HeapNumber::kValueOffset));
  // Get exponent alone in scratch2.
  And(scratch2, scratch1, Operand(0x7FFL << 52));
  // Load dest with zero.  We use this either for the final shift or
  // for the answer.
  move(dest, zero);
  // Check whether the exponent matches a 32 bit signed int that is not a Smi.
  // A non-Smi integer is 1.xxx * 2^30 so the exponent is 30 (biased).  This is
  // the exponent that we are fastest at and also the highest exponent we can
  // handle here.
  const uint64_t non_smi_exponent = 1053L << 52;
  // If we have a match of the int32-but-not-Smi exponent then skip some logic.
  Branch(&right_exponent, eq, scratch2, Operand(non_smi_exponent));
  // If the exponent is higher than that then go to not_int32 case.  This
  // catches numbers that don't fit in a signed int32, infinities and NaNs.
  Branch(not_int32, gt, scratch2, Operand(non_smi_exponent));

  // We know the exponent is smaller than 30 (biased).  If it is less than
  // 0 (biased) then the number is smaller in magnitude than 1.0 * 2^0, i.e.
  // it rounds to zero.
  const uint64_t zero_exponent = 1023L << 52;
  Subu(scratch2, scratch2, Operand(zero_exponent));
  // Dest already has a Smi zero.
  Branch(&done, lt, scratch2, Operand(zero));

  // We have a shifted exponent between 0 and 30 in scratch2.
  srl(dest, scratch2, 52);
  // We now have the exponent in dest.  Subtract from 30 to get
  // how much to shift down.
  addi(at, zero, 30);
  sub(dest, at, dest);

  bind(&right_exponent);

  // On entry, dest has final downshift, scratch has original sign/exp/mant.
  // Save sign bit in top bit of dest.
  And(scratch2, scratch1, Operand(0x8000000000000000L));
  Or(dest, dest, Operand(scratch2));
  // Put back the implicit 1, just above mantissa field.
  Or(scratch1, scratch1, Operand(1L << 52));

  // Shift up the mantissa bits to take up the space the exponent used to
  // take. We just orred in the implicit bit so that took care of one and
  // we want to leave the sign bit 0 so we subtract 2 bits from the shift
  // distance. But we want to clear the sign-bit so shift one more bit
  // left, then shift right one bit.
  //const int shift_distance = HeapNumber::kNonMantissaBitsInTopWord - 2;
  //sll(scratch1, scratch1, shift_distance + 1);
  //srl(scratch1, scratch1, 32 + 1);
  bfextu(scratch1, scratch1, 22, 52);


  // Move down according to the exponent.
  srl(scratch1, scratch1, dest);
  // Prepare the negative version of our integer.
  sub(scratch2, zero, scratch1);
  // Trick to check sign bit (msb) held in dest, count leading zero.
  // 0 indicates negative, save negative version with conditional move.
  clz(dest, dest);
  movz(scratch1, scratch2, dest);
  move(dest, scratch1);

  bind(&done);
  }
}

void MacroAssembler::EmitOutOfInt32RangeTruncate(Register result,
                                                 Register input,
                                                 Register scratch) {
  Label done, normal_exponent, restore_sign;
  // Extract the biased exponent in result.
  bfextu(result, input, 52, 62);

  // Check for Infinity and NaNs, which should return 0.
  Subu(scratch, result, 0x7FF);
  movz(result, zero, scratch);
  Branch(&done, eq, scratch, Operand(zero));

  // Express exponent as delta to (number of mantissa bits + 31).
  Subu(result,
       result,
       Operand(HeapNumber::kExponentBias + HeapNumber::kMantissaBits + 31));

  // If the delta is strictly positive, all bits would be shifted away,
  // which means that we can return 0.
  Branch(&normal_exponent, le, result, Operand(zero));
  move(result, zero);
  Branch(&done);

  bind(&normal_exponent);
  const int kShiftBase = HeapNumber::kNonMantissaBitsInTopWord - 1;
  // Calculate shift.
  Addu(scratch, result, Operand(kShiftBase + HeapNumber::kMantissaBits));

  // Save the sign.
  Register sign = result;
  result = no_reg;
  And(sign, input, Operand(0x8000000000000000L));

  // Set the implicit 1 before the mantissa part in input.
  Or(input, input, Operand(1L << 52));

  sll(scratch, input, scratch);
  srl(input, scratch, 32);

  // Restore sign if necessary.
  move(scratch, sign);
  result = sign;
  sign = no_reg;
  Subu(result, zero, input);
  movz(result, input, scratch);
  bind(&done);
}

bool AreAliased(Register r1, Register r2, Register r3, Register r4) {
  if (r1.is(r2)) return true;
  if (r1.is(r3)) return true;
  if (r1.is(r4)) return true;
  if (r2.is(r3)) return true;
  if (r2.is(r4)) return true;
  if (r3.is(r4)) return true;
  return false;
}

CodePatcher::CodePatcher(byte* address, int instructions)
    : address_(address),
      size_(instructions * Assembler::kInstrSize),
      masm_(NULL, address, size_ + Assembler::kGap) {
  // Create a new macro assembler pointing to the address of the code to patch.
  // The size is adjusted with kGap on order for the assembler to generate size
  // bytes of instructions without failing with buffer size constraints.
  ASSERT(masm_.reloc_info_writer.pos() == address_ + size_ + Assembler::kGap);
}


CodePatcher::~CodePatcher() {
  // Indicate that code has changed.
  CPU::FlushICache(address_, size_);

  // Check that the code was patched as expected.
  ASSERT(masm_.pc_ == address_ + size_);
  ASSERT(masm_.reloc_info_writer.pos() == address_ + size_ + Assembler::kGap);
}


void CodePatcher::Emit(Instr instr) {
  masm()->emit(instr);
}

void CodePatcher::Emit(Address addr) {
  masm()->emit(reinterpret_cast<Instr>(addr));
}

void CodePatcher::ChangeBranchCondition(Condition cond) {
  Instr instr = Assembler::instr_at(masm_.pc_);
  ASSERT(Assembler::IsBranch(instr));
  // Currently only the 'eq' and 'ne' cond values are supported and the simple
  // branch instructions (with opcode being the branch type).
  // There are some special cases (see Assembler::IsBranch()) so extending this
  // would be tricky.
  ASSERT(Assembler::IsBnez(instr) || Assembler::IsBeqz(instr));
  instr = (instr & ~create_BrType_X1(-1)) | ((cond == eq) ?
                                             create_BrType_X1(BEQZ_BRANCH_OPCODE_X1)
                                             : create_BrType_X1(BNEZ_BRANCH_OPCODE_X1));
  masm_.emit(instr);
}

} }  // namespace v8::internal

#endif  // V8_TARGET_ARCH_TILEGX
