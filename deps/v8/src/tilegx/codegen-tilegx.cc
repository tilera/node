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

#include "v8.h"

#if defined(V8_TARGET_ARCH_TILEGX)

#include "codegen.h"
#include "macro-assembler.h"
#include "simulator-tilegx.h"

namespace v8 {
namespace internal {


UnaryMathFunction CreateTranscendentalFunction(TranscendentalCache::Type type) {
  switch (type) {
    case TranscendentalCache::SIN: return &sin;
    case TranscendentalCache::COS: return &cos;
    case TranscendentalCache::TAN: return &tan;
    case TranscendentalCache::LOG: return &log;
    default: UNIMPLEMENTED();
  }
  return NULL;
}


#define __ masm.


#if defined(USE_SIMULATOR)
byte* fast_exp_mips_machine_code = NULL;
double fast_exp_simulator(double x) {
  return Simulator::current(Isolate::Current())->CallFP(
      fast_exp_mips_machine_code, x, 0);
}
#endif


UnaryMathFunction CreateExpFunction() {
  return &exp;
}


#undef __


UnaryMathFunction CreateSqrtFunction() {
  return &sqrt;
}

// -------------------------------------------------------------------------
// Platform-specific RuntimeCallHelper functions.

void StubRuntimeCallHelper::BeforeCall(MacroAssembler* masm) const {
  masm->EnterFrame(StackFrame::INTERNAL);
  ASSERT(!masm->has_frame());
  masm->set_has_frame(true);
}


void StubRuntimeCallHelper::AfterCall(MacroAssembler* masm) const {
  masm->LeaveFrame(StackFrame::INTERNAL);
  ASSERT(masm->has_frame());
  masm->set_has_frame(false);
}

// -------------------------------------------------------------------------
// Code generators

#define __ ACCESS_MASM(masm)

void ElementsTransitionGenerator::GenerateMapChangeElementsTransition(
    MacroAssembler* masm, AllocationSiteMode mode,
    Label* allocation_site_info_found) {
  // ----------- S t a t e -------------
  //  -- a0    : value
  //  -- a1    : key
  //  -- a2    : receiver
  //  -- ra    : return address
  //  -- a3    : target map, scratch for subsequent call
  //  -- t0    : scratch (elements)
  // -----------------------------------
  if (mode == TRACK_ALLOCATION_SITE) {
    ASSERT(allocation_site_info_found != NULL);
    masm->TestJSArrayForAllocationSiteInfo(a2, t0, eq,
                                           allocation_site_info_found);
  }

  // Set transitioned map.
  __ st(a3, FieldMemOperand(a2, HeapObject::kMapOffset));
  __ RecordWriteField(a2,
                      HeapObject::kMapOffset,
                      a3,
                      t5,
                      kRAHasNotBeenSaved,
                      kDontSaveFPRegs,
                      EMIT_REMEMBERED_SET,
                      OMIT_SMI_CHECK);
}


void ElementsTransitionGenerator::GenerateSmiToDouble(
    MacroAssembler* masm, AllocationSiteMode mode, Label* fail) {
  // ----------- S t a t e -------------
  //  -- a0    : value
  //  -- a1    : key
  //  -- a2    : receiver
  //  -- ra    : return address
  //  -- a3    : target map, scratch for subsequent call
  //  -- t0    : scratch (elements)
  // -----------------------------------
  Label loop, entry, convert_hole, gc_required, only_change_map, done;

  Register scratch = t6;

  if (mode == TRACK_ALLOCATION_SITE) {
    masm->TestJSArrayForAllocationSiteInfo(a2, t0, eq, fail);
  }

  // Check for empty arrays, which only require a map transition and no changes
  // to the backing store.
  __ ld(t0, FieldMemOperand(a2, JSObject::kElementsOffset));
  __ LoadRoot(at, Heap::kEmptyFixedArrayRootIndex);
  __ Branch(&only_change_map, eq, at, Operand(t0));

  __ push(ra);
  __ ld(t1, FieldMemOperand(t0, FixedArray::kLengthOffset));
  // t0: source FixedArray
  // t1: number of elements (smi-tagged)

  // Allocate new FixedDoubleArray.
  __ sra(scratch, t1, 32);
  __ sll(scratch, scratch, 3);
  __ Addu(scratch, scratch, FixedDoubleArray::kHeaderSize);
  __ Allocate(scratch, t2, t3, t5, &gc_required, NO_ALLOCATION_FLAGS);
  // t2: destination FixedDoubleArray, not tagged as heap object

  // Set destination FixedDoubleArray's length and map.
  __ LoadRoot(t5, Heap::kFixedDoubleArrayMapRootIndex);
  __ st(t1, MemOperand(t2, FixedDoubleArray::kLengthOffset));
  __ st(t5, MemOperand(t2, HeapObject::kMapOffset));
  // Update receiver's map.

  __ st(a3, FieldMemOperand(a2, HeapObject::kMapOffset));
  __ RecordWriteField(a2,
                      HeapObject::kMapOffset,
                      a3,
                      t5,
                      kRAHasBeenSaved,
                      kDontSaveFPRegs,
                      OMIT_REMEMBERED_SET,
                      OMIT_SMI_CHECK);
  // Replace receiver's backing store with newly created FixedDoubleArray.
  __ Addu(a3, t2, Operand(kHeapObjectTag));
  __ st(a3, FieldMemOperand(a2, JSObject::kElementsOffset));
  __ RecordWriteField(a2,
                      JSObject::kElementsOffset,
                      a3,
                      t5,
                      kRAHasBeenSaved,
                      kDontSaveFPRegs,
                      EMIT_REMEMBERED_SET,
                      OMIT_SMI_CHECK);


  // Prepare for conversion loop.
  __ Addu(a3, t0, Operand(FixedArray::kHeaderSize - kHeapObjectTag));
  __ Addu(t3, t2, Operand(FixedDoubleArray::kHeaderSize));
  __ sra(t2, t1, 32);
  __ sll(t2, t2, 3);
  __ Addu(t2, t2, t3);
  __ li(t0, Operand(kHoleNanInt64));
  //__ li(t1, Operand(kHoleNanUpper32));
  // t0: kHoleNanLower32
  // t1: kHoleNanUpper32
  // t2: end of destination FixedDoubleArray, not tagged
  // t3: begin of FixedDoubleArray element fields, not tagged

  __ Branch(&entry);

  __ bind(&only_change_map);
  __ st(a3, FieldMemOperand(a2, HeapObject::kMapOffset));
  __ RecordWriteField(a2,
                      HeapObject::kMapOffset,
                      a3,
                      t5,
                      kRAHasNotBeenSaved,
                      kDontSaveFPRegs,
                      OMIT_REMEMBERED_SET,
                      OMIT_SMI_CHECK);
  __ Branch(&done);

  // Call into runtime if GC is required.
  __ bind(&gc_required);
  __ pop(ra);
  __ Branch(fail);

  // Convert and copy elements.
  __ bind(&loop);
  __ ld(t5, MemOperand(a3));
  __ Addu(a3, a3, kDoubleSize);
  // t5: current element
  __ UntagAndJumpIfNotSmi(t5, t5, &convert_hole);

  FloatingPointHelper::ConvertIntToDouble(masm, t5,
     FloatingPointHelper::kCoreRegisters, at, at2, t1);
  __ st(at, MemOperand(t3));
  __ Addu(t3, t3, kDoubleSize);

  __ Branch(&entry);

  // Hole found, store the-hole NaN.
  __ bind(&convert_hole);
  if (FLAG_debug_code) {
    // Restore a "smi-untagged" heap object.
    __ SmiTag(t5);
    __ Or(t5, t5, Operand(1));
    __ LoadRoot(at, Heap::kTheHoleValueRootIndex);
    __ Assert(eq, "object found in smi-only array", at, Operand(t5));
  }
  __ st(t0, MemOperand(t3));
  //__ st(t1, MemOperand(t3, kIntSize));  // exponent
  __ Addu(t3, t3, kDoubleSize);

  __ bind(&entry);
  __ Branch(&loop, lt, t3, Operand(t2));

  __ pop(ra);
  __ bind(&done);
}


void ElementsTransitionGenerator::GenerateDoubleToObject(
    MacroAssembler* masm, AllocationSiteMode mode, Label* fail) {
  // ----------- S t a t e -------------
  //  -- a0    : value
  //  -- a1    : key
  //  -- a2    : receiver
  //  -- ra    : return address
  //  -- a3    : target map, scratch for subsequent call
  //  -- t0    : scratch (elements)
  // -----------------------------------
  Label entry, loop, convert_hole, gc_required, only_change_map;

  if (mode == TRACK_ALLOCATION_SITE) {
    masm->TestJSArrayForAllocationSiteInfo(a2, t0, eq, fail);
  }

  // Check for empty arrays, which only require a map transition and no changes
  // to the backing store.
  __ ld(t0, FieldMemOperand(a2, JSObject::kElementsOffset));
  __ LoadRoot(at, Heap::kEmptyFixedArrayRootIndex);
  __ Branch(&only_change_map, eq, at, Operand(t0));

  __ MultiPush(a0.bit() | a1.bit() | a2.bit() | a3.bit() | ra.bit());

  __ ld(t1, FieldMemOperand(t0, FixedArray::kLengthOffset));
  // t0: source FixedArray
  // t1: number of elements (smi-tagged)

  // Allocate new FixedArray.
  __ sra(a0, t1, 32);
  __ sll(a0, a0, 3);
  __ Addu(a0, a0, FixedDoubleArray::kHeaderSize);
  __ Allocate(a0, t2, t3, t5, &gc_required, NO_ALLOCATION_FLAGS);
  // t2: destination FixedArray, not tagged as heap object
  // Set destination FixedDoubleArray's length and map.
  __ LoadRoot(t5, Heap::kFixedArrayMapRootIndex);
  __ st(t1, MemOperand(t2, FixedDoubleArray::kLengthOffset));
  __ st(t5, MemOperand(t2, HeapObject::kMapOffset));

  // Prepare for conversion loop.
  __ Addu(t0, t0, Operand(FixedDoubleArray::kHeaderSize - kHeapObjectTag));
  __ Addu(a3, t2, Operand(FixedArray::kHeaderSize));
  __ Addu(t2, t2, Operand(kHeapObjectTag));
  __ sra(t1, t1, 32);
  __ sll(t1, t1, 3);
  __ Addu(t1, a3, t1);
  __ LoadRoot(t3, Heap::kTheHoleValueRootIndex);
  __ LoadRoot(t5, Heap::kHeapNumberMapRootIndex);
  // Using offsetted addresses.
  // a3: begin of destination FixedArray element fields, not tagged
  // t0: begin of source FixedDoubleArray element fields, not tagged, +4
  // t1: end of destination FixedArray, not tagged
  // t2: destination FixedArray
  // t3: the-hole pointer
  // t5: heap number map
  __ Branch(&entry);

  // Call into runtime if GC is required.
  __ bind(&gc_required);
  __ MultiPop(a0.bit() | a1.bit() | a2.bit() | a3.bit() | ra.bit());

  __ Branch(fail);

  __ bind(&loop);
  __ ld(a1, MemOperand(t0));
  __ Addu(t0, t0, kDoubleSize);
  // a1: current element's upper 32 bit
  // t0: address of next element's upper 32 bit
  __ Branch(&convert_hole, eq, a1, Operand(kHoleNanInt64));

  // Non-hole double, copy value into a heap number.
  __ AllocateHeapNumber(a2, a0, t6, t5, &gc_required);
  // a2: new heap number
  __ st(a1, FieldMemOperand(a2, HeapNumber::kValueOffset));
  __ move(a0, a3);
  __ st(a2, MemOperand(a3));
  __ Addu(a3, a3, kPointerSize);
  __ RecordWrite(t2,
                 a0,
                 a2,
                 kRAHasBeenSaved,
                 kDontSaveFPRegs,
                 EMIT_REMEMBERED_SET,
                 OMIT_SMI_CHECK);
  __ Branch(&entry);

  // Replace the-hole NaN with the-hole pointer.
  __ bind(&convert_hole);
  __ st(t3, MemOperand(a3));
  __ Addu(a3, a3, kDoubleSize);

  __ bind(&entry);
  __ Branch(&loop, lt, a3, Operand(t1));

  __ MultiPop(a2.bit() | a3.bit() | a0.bit() | a1.bit());
  // Replace receiver's backing store with newly created and filled FixedArray.
  __ st(t2, FieldMemOperand(a2, JSObject::kElementsOffset));
  __ RecordWriteField(a2,
                      JSObject::kElementsOffset,
                      t2,
                      t5,
                      kRAHasBeenSaved,
                      kDontSaveFPRegs,
                      EMIT_REMEMBERED_SET,
                      OMIT_SMI_CHECK);
  __ pop(ra);

  __ bind(&only_change_map);
  // Update receiver's map.
  __ st(a3, FieldMemOperand(a2, HeapObject::kMapOffset));
  __ RecordWriteField(a2,
                      HeapObject::kMapOffset,
                      a3,
                      t5,
                      kRAHasNotBeenSaved,
                      kDontSaveFPRegs,
                      OMIT_REMEMBERED_SET,
                      OMIT_SMI_CHECK);
}


void StringCharLoadGenerator::Generate(MacroAssembler* masm,
                                       Register string,
                                       Register index,
                                       Register result,
                                       Label* call_runtime) {
  // Fetch the instance type of the receiver into result register.
  __ ld(result, FieldMemOperand(string, HeapObject::kMapOffset));
  __ ld1u(result, FieldMemOperand(result, Map::kInstanceTypeOffset));

  // We need special handling for indirect strings.
  Label check_sequential;
  __ And(at, result, Operand(kIsIndirectStringMask));
  __ Branch(&check_sequential, eq, at, Operand(zero));

  // Dispatch on the indirect string shape: slice or cons.
  Label cons_string;
  __ And(at, result, Operand(kSlicedNotConsMask));
  __ Branch(&cons_string, eq, at, Operand(zero));

  // Handle slices.
  Label indirect_string_loaded;
  __ ld(result, FieldMemOperand(string, SlicedString::kOffsetOffset));
  __ ld(string, FieldMemOperand(string, SlicedString::kParentOffset));
  __ sra(at, result, 32);
  __ Addu(index, index, at);
  __ jmp(&indirect_string_loaded);

  // Handle cons strings.
  // Check whether the right hand side is the empty string (i.e. if
  // this is really a flat string in a cons string). If that is not
  // the case we would rather go to the runtime system now to flatten
  // the string.
  __ bind(&cons_string);
  __ ld(result, FieldMemOperand(string, ConsString::kSecondOffset));
  __ LoadRoot(at, Heap::kempty_stringRootIndex);
  __ Branch(call_runtime, ne, result, Operand(at));
  // Get the first of the two strings and load its instance type.
  __ ld(string, FieldMemOperand(string, ConsString::kFirstOffset));

  __ bind(&indirect_string_loaded);
  __ ld(result, FieldMemOperand(string, HeapObject::kMapOffset));
  __ ld1u(result, FieldMemOperand(result, Map::kInstanceTypeOffset));

  // Distinguish sequential and external strings. Only these two string
  // representations can reach here (slices and flat cons strings have been
  // reduced to the underlying sequential or external string).
  Label external_string, check_encoding;
  __ bind(&check_sequential);
  STATIC_ASSERT(kSeqStringTag == 0);
  __ And(at, result, Operand(kStringRepresentationMask));
  __ Branch(&external_string, ne, at, Operand(zero));

  // Prepare sequential strings
  STATIC_ASSERT(SeqTwoByteString::kHeaderSize == SeqOneByteString::kHeaderSize);
  __ Addu(string,
          string,
          SeqTwoByteString::kHeaderSize - kHeapObjectTag);
  __ jmp(&check_encoding);

  // Handle external strings.
  __ bind(&external_string);
  if (FLAG_debug_code) {
    // Assert that we do not have a cons or slice (indirect strings) here.
    // Sequential strings have already been ruled out.
    __ And(at, result, Operand(kIsIndirectStringMask));
    __ Assert(eq, "external string expected, but not found",
        at, Operand(zero));
  }
  // Rule out short external strings.
  STATIC_CHECK(kShortExternalStringTag != 0);
  __ And(at, result, Operand(kShortExternalStringMask));
  __ Branch(call_runtime, ne, at, Operand(zero));
  __ ld(string, FieldMemOperand(string, ExternalString::kResourceDataOffset));

  Label ascii, done;
  __ bind(&check_encoding);
  STATIC_ASSERT(kTwoByteStringTag == 0);
  __ And(at, result, Operand(kStringEncodingMask));
  __ Branch(&ascii, ne, at, Operand(zero));
  // Two-byte string.
  __ sll(at, index, 1);
  __ Addu(at, string, at);
  __ ld2u(result, MemOperand(at));
  __ jmp(&done);
  __ bind(&ascii);
  // Ascii string.
  __ Addu(at, string, index);
  __ ld1u(result, MemOperand(at));
  __ bind(&done);
}


#if 0
static MemOperand ExpConstant(int index, Register base) {
  return MemOperand(base, index * kDoubleSize);
}
#endif


void MathExpGenerator::EmitMathExp(MacroAssembler* masm,
                                   DoubleRegister input,
                                   DoubleRegister result,
                                   DoubleRegister double_scratch1,
                                   DoubleRegister double_scratch2,
                                   Register temp1,
                                   Register temp2,
                                   Register temp3) {
  UNREACHABLE();
}


// nop(CODE_AGE_MARKER_NOP)
static const uint64_t kCodeAgePatchFirstInstruction = 0x3004339fd1483000L;

static byte* GetNoCodeAgeSequence(uint32_t* length) {
  // The sequence of instructions that is patched out for aging code is the
  // following boilerplate stack-building prologue that is found in FUNCTIONS
  static bool initialized = false;
  static uint64_t sequence[kNoCodeAgeSequenceLength];
  byte* byte_sequence = reinterpret_cast<byte*>(sequence);
  *length = kNoCodeAgeSequenceLength * Assembler::kInstrSize;
  if (!initialized) {
    CodePatcher patcher(byte_sequence, kNoCodeAgeSequenceLength);
    patcher.masm()->Push(ra, fp, cp, a1);
    patcher.masm()->LoadRoot(at, Heap::kUndefinedValueRootIndex);
    patcher.masm()->Addu(fp, sp, Operand(2 * kPointerSize));
    initialized = true;
  }
  return byte_sequence;
}

bool Code::IsYoungSequence(byte* sequence) {
  uint32_t young_length;
  byte* young_sequence = GetNoCodeAgeSequence(&young_length);
  bool result = !memcmp(sequence, young_sequence, young_length);
  ASSERT(result ||
         Memory::uint64_at(sequence) == kCodeAgePatchFirstInstruction);
  return result;
}


void Code::GetCodeAgeAndParity(byte* sequence, Age* age,
                               MarkingParity* parity) {
  if (IsYoungSequence(sequence)) {
    *age = kNoAge;
    *parity = NO_MARKING_PARITY;
  } else {
    Address target_address = Memory::Address_at(
        sequence + Assembler::kInstrSize * (kNoCodeAgeSequenceLength - 1));
    Code* stub = GetCodeFromTargetAddress(target_address);
    GetCodeAgeAndParity(stub, age, parity);
  }
}


void Code::PatchPlatformCodeAge(byte* sequence,
                                Code::Age age,
                                MarkingParity parity) {
  uint32_t young_length;
  byte* young_sequence = GetNoCodeAgeSequence(&young_length);
  if (age == kNoAge) {
    CopyBytes(sequence, young_sequence, young_length);
    CPU::FlushICache(sequence, young_length);
  } else {
    Code* stub = GetCodeAgeStub(age, parity);
    CodePatcher patcher(sequence, young_length / Assembler::kInstrSize);
    // Mark this code sequence for FindPlatformCodeAgeSequence()
    patcher.masm()->nop(Assembler::CODE_AGE_MARKER_NOP);

    patcher.masm()->nop();
    patcher.masm()->nop();
    patcher.masm()->nop();
    patcher.masm()->nop();

    // Save the function's original return address
    // (it will be clobbered by Call(t9))
    patcher.masm()->move(at, ra);
    // Load the stub address to t9 and call it
    patcher.masm()->li(t9,
        Operand(reinterpret_cast<uint64_t>(stub->instruction_start())));
    patcher.masm()->Call(t9);
    // Record the stub address in the empty space for GetCodeAgeAndParity()
    patcher.masm()->dq(reinterpret_cast<uint64_t>(stub->instruction_start()));
  }
}


#undef __

} }  // namespace v8::internal

#endif  // V8_TARGET_ARCH_TILEGX
