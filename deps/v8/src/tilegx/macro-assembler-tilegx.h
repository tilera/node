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

#ifndef V8_TILEGX_MACRO_ASSEMBLER_TILEGX_H_
#define V8_TILEGX_MACRO_ASSEMBLER_TILEGX_H_

#include "assembler.h"
#include "tilegx/assembler-tilegx.h"
#include "v8globals.h"

namespace v8 {
namespace internal {

// Flags used for AllocateHeapNumber
enum TaggingMode {
  // Tag the result.
  TAG_RESULT,
  // Don't tag
  DONT_TAG_RESULT
};

// Flags used for the li macro-assembler function.
enum LiFlags {
  // If the constant value can be represented in just 16 bits, then
  // optimize the li to use a single instruction, rather than lui/ori pair.
  OPTIMIZE_SIZE = 0,
  // Always use 2 instructions (lui/ori pair), even if the constant could
  // be loaded with just one, so that this value is patchable later.
  CONSTANT_SIZE = 1
};

enum RememberedSetAction { EMIT_REMEMBERED_SET, OMIT_REMEMBERED_SET };
enum SmiCheck { INLINE_SMI_CHECK, OMIT_SMI_CHECK };
enum RAStatus { kRAHasNotBeenSaved, kRAHasBeenSaved };

bool AreAliased(Register r1, Register r2, Register r3, Register r4);

inline MemOperand ContextOperand(Register context, int index) {
  return MemOperand(context, Context::SlotOffset(index));
}

inline MemOperand GlobalObjectOperand()  {
  return ContextOperand(cp, Context::GLOBAL_OBJECT_INDEX);
}

// Generate a MemOperand for loading a field from an object.
inline MemOperand FieldMemOperand(Register object, int offset) {
  return MemOperand(object, offset - kHeapObjectTag);
}

// Generate a MemOperand for storing arguments 11..N on the stack
// when calling CallCFunction().
inline MemOperand CFunctionArgumentOperand(int index) {
  ASSERT(index > kArgByRegNum);
  // Argument 5 takes the slot just past the four Arg-slots.
  int offset = (index - kArgByRegNum - 1) * kPointerSize + kStackLowReserve;
  return MemOperand(sp, offset);
}

// MacroAssembler implements a collection of frequently used macros.
class MacroAssembler: public Assembler {
 public:
  // The isolate parameter can be NULL if the macro assembler should
  // not use isolate-dependent functionality. In this case, it's the
  // responsibility of the caller to never invoke such function on the
  // macro assembler.
  MacroAssembler(Isolate* isolate, void* buffer, int size);

  enum RememberedSetFinalAction {
    kReturnAtEnd,
    kFallThroughAtEnd
  };

  // Activation support.
  void EnterFrame(StackFrame::Type type);
  void LeaveFrame(StackFrame::Type type);

  // Patch the relocated value (lui/ori pair).
  void PatchRelocatedValue(Register li_location,
                           Register scratch,
			   Register scratch2,
                           Register new_value);
  // Get the relocatad value (loaded data) from the lui/ori pair.
  void GetRelocatedValue(Register li_location,
                         Register value,
                         Register scratch,
			 Register scratch2);

  // Arguments macros.
#define COND_TYPED_ARGS Condition cond, Register r1, const Operand& r2

  // Cases when relocation is not needed.
#define DECLARE_NORELOC_PROTOTYPE(Name, target_type) \
  void Name(target_type target); \
  void Name(target_type target, \
            COND_TYPED_ARGS); \

#define DECLARE_BRANCH_PROTOTYPES(Name) \
  DECLARE_NORELOC_PROTOTYPE(Name, Label*) \
  DECLARE_NORELOC_PROTOTYPE(Name, int16_t)

  DECLARE_BRANCH_PROTOTYPES(Branch)
  DECLARE_BRANCH_PROTOTYPES(BranchAndLink)

#undef DECLARE_BRANCH_PROTOTYPES
#undef COND_TYPED_ARGS

  // Invoke specified builtin JavaScript function. Adds an entry to
  // the unresolved list if the name does not resolve.
  void InvokeBuiltin(Builtins::JavaScript id,
                     InvokeFlag flag,
                     const CallWrapper& call_wrapper = NullCallWrapper());

  // Store the function for the given builtin in the target register.
  void GetBuiltinFunction(Register target, Builtins::JavaScript id);

  // Store the code object for the given builtin in the target register and
  // setup the function in a1.
  void GetBuiltinEntry(Register target, Builtins::JavaScript id);

  Handle<Object> CodeObject() {
    ASSERT(!code_object_.is_null());
    return code_object_;
  }

  // Check if instance type is sequential ASCII string and jump to label if
  // it is not.
  void JumpIfInstanceTypeIsNotSequentialAscii(Register type,
                                              Register scratch,
                                              Label* failure);

  // Test that both first and second are sequential ASCII strings.
  // Assume that they are non-smis.
  void JumpIfNonSmisNotBothSequentialAsciiStrings(Register first,
                                                  Register second,
                                                  Register scratch1,
                                                  Register scratch2,
                                                  Label* failure);

  // Test that both first and second are sequential ASCII strings.
  // Check that they are non-smis.
  void JumpIfNotBothSequentialAsciiStrings(Register first,
                                           Register second,
                                           Register scratch1,
                                           Register scratch2,
                                           Label* failure);

  void ClampUint8(Register output_reg, Register input_reg);

  void ClampDoubleToUint8(Register result_reg,
                          DoubleRegister input_reg,
                          Register temp_reg,
                          Register temp_reg1,
                          Register temp_reg2,
			  Register temp_reg3);

  void LoadInstanceDescriptors(Register map, Register descriptors);
  void EnumLength(Register dst, Register map);
  void NumberOfOwnDescriptors(Register dst, Register map);

  template<typename Field>
  void DecodeField(Register reg) {
    static const int shift = Field::kShift + kSmiShift;
    static const int mask = Field::kMask >> Field::kShift;
    srl(reg, reg, shift);
    And(reg, reg, Operand(mask));
    sll(reg, reg, kSmiShift);
  }

  // Untag the source value into destination and jump if source is a smi.
  // Souce and destination can be the same register.
  void UntagAndJumpIfSmi(Register dst, Register src, Label* smi_case);

  // Untag the source value into destination and jump if source is not a smi.
  // Souce and destination can be the same register.
  void UntagAndJumpIfNotSmi(Register dst, Register src, Label* non_smi_case);

  // Jump the register contains a smi.
  void JumpIfSmi(Register value,
                 Label* smi_label,
                 Register scratch = at);

  // Jump if the register contains a non-smi.
  void JumpIfNotSmi(Register value,
                    Label* not_smi_label,
                    Register scratch = at);

  // Jump if either of the registers contain a non-smi.
  void JumpIfNotBothSmi(Register reg1, Register reg2, Label* on_not_both_smi);
  // Jump if either of the registers contain a smi.
  void JumpIfEitherSmi(Register reg1, Register reg2, Label* on_either_smi);

  void PrepareCallCFunction(int num_reg_arguments,
                            Register scratch);

  // Helper for finding the mark bits for an address.  Afterwards, the
  // bitmap register points at the word with the mark bits and the mask
  // the position of the first bit.  Leaves addr_reg unchanged.
  inline void GetMarkBits(Register addr_reg,
                          Register bitmap_reg,
                          Register mask_reg);

  void CheckEnumCache(Register null_value, Label* call_runtime);

  void TestJSArrayForAllocationSiteInfo(Register receiver_reg,
                                        Register scratch_reg,
                                        Condition cond,
                                        Label* allocation_info_present);

  // Arguments 1-4 are placed in registers a0 thru a3 respectively.
  // Arguments 5..n are stored to stack using following:
  //  sw(t0, CFunctionArgumentOperand(5));

  // Calls a C function and cleans up the space for arguments allocated
  // by PrepareCallCFunction. The called function is not allowed to trigger a
  // garbage collection, since that might move the code and invalidate the
  // return address (unless this is somehow accounted for by the called
  // function).
  void CallCFunction(ExternalReference function, int num_arguments);
  void CallCFunction(Register function, int num_arguments);

  // Detects conservatively whether an object is data-only, i.e. it does need to
  // be scanned by the garbage collector.
  void JumpIfDataObject(Register value,
                        Register scratch,
                        Label* not_data_object);

  void JumpIfBothInstanceTypesAreNotSequentialAscii(
      Register first_object_instance_type,
      Register second_object_instance_type,
      Register scratch1,
      Register scratch2,
      Label* failure);

  // Check if an object has a given incremental marking color.
  void HasColor(Register object,
                Register scratch0,
                Register scratch1,
                Label* has_color,
                int first_bit,
                int second_bit);

  void JumpIfBlack(Register object,
                   Register scratch0,
                   Register scratch1,
                   Label* on_black);

  // Checks the color of an object.  If the object is already grey or black
  // then we just fall through, since it is already live.  If it is white and
  // we can determine that it doesn't need to be scanned, then we just mark it
  // black and fall through.  For the rest we jump to the label so the
  // incremental marker can fix its assumptions.
  void EnsureNotWhite(Register object,
                      Register scratch1,
                      Register scratch2,
                      Register scratch3,
                      Label* object_is_white_and_not_data);

  // -------------------------------------------------------------------------
  // Debugging.

  // Calls Abort(msg) if the condition cc is not satisfied.
  // Use --debug_code to enable.
  void Assert(Condition cc, const char* msg, Register rs, Operand rt);
  void AssertRegisterIsRoot(Register reg, Heap::RootListIndex index);
  void AssertFastElements(Register elements);

  // Like Assert(), but always enabled.
  void Check(Condition cc, const char* msg, Register rs, Operand rt);

  // Print a message to stdout and abort execution.
  void Abort(const char* msg);

  // Abort execution if argument is a smi, enabled via --debug-code.
  void AssertNotSmi(Register object);
  void AssertSmi(Register object);

  // Abort execution if argument is not a string, enabled via --debug-code.
  void AssertString(Register object);

  // Abort execution if argument is not a name, enabled via --debug-code.
  void AssertName(Register object);

  // Abort execution if argument is not the root value with the given index,
  // enabled via --debug-code.
  void AssertRootValue(Register src,
                       Heap::RootListIndex root_value_index,
                       const char* message);

  void JumpIfNotHeapNumber(Register object,
                           Register heap_number_map,
                           Register scratch,
                           Label* on_not_heap_number);

  // Debug Purpose
  void set_generating_stub(bool value) { generating_stub_ = value; }
  bool generating_stub() { return generating_stub_; }
  void set_allow_stub_calls(bool value) { allow_stub_calls_ = value; }
  bool allow_stub_calls() { return allow_stub_calls_; }
  void set_has_frame(bool value) { has_frame_ = value; }
  bool has_frame() { return has_frame_; }
  inline bool AllowThisStubCall(CodeStub* stub);

  // -------------------------------------------------------------------------
  // Smi utilities.

  void SmiTag(Register reg) {
    sll(reg, reg, kSmiTagSize + kSmiShiftSize);
  }

  // Test for overflow < 0: use BranchOnOverflow() or BranchOnNoOverflow().
  void SmiTagCheckOverflow(Register reg, Register overflow);
  void SmiTagCheckOverflow(Register dst, Register src, Register overflow);

  void SmiTag(Register dst, Register src) {
    sll(dst, src, kSmiTagSize + kSmiShiftSize);
  }

  void SmiUntag(Register reg) {
    sra(reg, reg, kSmiTagSize + kSmiShiftSize);
    //srl(reg, reg, kSmiTagSize + kSmiShiftSize);
  }

  void SmiUntag(Register dst, Register src) {
    sra(dst, src, kSmiTagSize + kSmiShiftSize);
    //srl(dst, src, kSmiTagSize + kSmiShiftSize);
  }

  void SmiUntagUnsigned(Register reg) {
    srl(reg, reg, kSmiTagSize + kSmiShiftSize);
    //sra(reg, reg, kSmiTagSize + kSmiShiftSize);
  }

  void SmiUntagUnsigned(Register dst, Register src) {
    srl(dst, src, kSmiTagSize + kSmiShiftSize);
    //sra(dst, src, kSmiTagSize + kSmiShiftSize); 
  }

  // Helper for throwing exceptions.  Compute a handler address and jump to
  // it.  See the implementation for register usage.
  void JumpToHandlerEntry();

  // Propagates an uncatchable exception to the top of the current JS stack's
  // handler chain.
  void ThrowUncatchable(Register value);

  // ---------------------------------------------------------------------------
  // Allocation support.

  // Allocate an object in new space or old pointer space. The object_size is
  // specified either in bytes or in words if the allocation flag SIZE_IN_WORDS
  // is passed. If the space is exhausted control continues at the gc_required
  // label. The allocated object is returned in result. If the flag
  // tag_allocated_object is true the result is tagged as as a heap object.
  // All registers are clobbered also when control continues at the gc_required
  // label.
  void Allocate(int object_size,
                Register result,
                Register scratch1,
                Register scratch2,
                Label* gc_required,
                AllocationFlags flags);

  void Allocate(Register object_size,
                Register result,
                Register scratch1,
                Register scratch2,
                Label* gc_required,
                AllocationFlags flags);

  // Undo allocation in new space. The object passed and objects allocated after
  // it will no longer be allocated. The caller must make sure that no pointers
  // are left to the object(s) no longer allocated as they would be invalid when
  // allocation is undone.
  void UndoAllocationInNewSpace(Register object, Register scratch);


  void AllocateTwoByteString(Register result,
                             Register length,
                             Register scratch1,
                             Register scratch2,
                             Register scratch3,
                             Label* gc_required);
  void AllocateAsciiString(Register result,
                           Register length,
                           Register scratch1,
                           Register scratch2,
                           Register scratch3,
                           Label* gc_required);
  void AllocateTwoByteConsString(Register result,
                                 Register length,
                                 Register scratch1,
                                 Register scratch2,
                                 Label* gc_required);
  void AllocateAsciiConsString(Register result,
                               Register length,
                               Register scratch1,
                               Register scratch2,
                               Label* gc_required);
  void AllocateTwoByteSlicedString(Register result,
                                   Register length,
                                   Register scratch1,
                                   Register scratch2,
                                   Label* gc_required);
  void AllocateAsciiSlicedString(Register result,
                                 Register length,
                                 Register scratch1,
                                 Register scratch2,
                                 Label* gc_required);

  // Allocates a heap number or jumps to the gc_required label if the young
  // space is full and a scavenge is needed. All registers are clobbered also
  // when control continues at the gc_required label.
  void AllocateHeapNumber(Register result,
                          Register scratch1,
                          Register scratch2,
                          Register heap_number_map,
                          Label* gc_required,
                          TaggingMode tagging_mode = TAG_RESULT);

  // ---------------------------------------------------------------------------
  // Instruction macros.

#define DEFINE_INSTRUCTION(instr)                                              \
  void instr(Register rd, Register rs, const Operand& rt);                     \
  void instr(Register rd, Register rs, Register rt) {                          \
    instr(rd, rs, Operand(rt));                                                \
  }                                                                            \
  void instr(Register rs, Register rt, int32_t j) {                            \
    instr(rs, rt, Operand(j));                                                 \
  }

#define DEFINE_INSTRUCTION2(instr)                                             \
  void instr(Register rs, const Operand& rt);                                  \
  void instr(Register rs, Register rt) {                                       \
    instr(rs, Operand(rt));                                                    \
  }                                                                            \
  void instr(Register rs, int32_t j) {                                         \
    instr(rs, Operand(j));                                                     \
  }

  DEFINE_INSTRUCTION(Addu);
  DEFINE_INSTRUCTION(Subu);
  DEFINE_INSTRUCTION(Mul);
  DEFINE_INSTRUCTION2(Mult);
  DEFINE_INSTRUCTION2(Multu);
  DEFINE_INSTRUCTION2(Div);
  DEFINE_INSTRUCTION2(Divu);

  DEFINE_INSTRUCTION(And);
  DEFINE_INSTRUCTION(Or);
  DEFINE_INSTRUCTION(Xor);
  DEFINE_INSTRUCTION(Nor);
  DEFINE_INSTRUCTION2(Neg);

  DEFINE_INSTRUCTION(Slt);
  DEFINE_INSTRUCTION(Sltu);

  // MIPS32 R2 instruction macro.
  DEFINE_INSTRUCTION(Ror);

#undef DEFINE_INSTRUCTION
#undef DEFINE_INSTRUCTION2

  // ---------------------------------------------------------------------------
  // Pseudo-instructions.

  // Load int32 in the rd register.
  void li(Register rd, Operand j, int line = 0, LiFlags mode = CONSTANT_SIZE);
  inline void li(Register rd, int64_t j, int line = 0, LiFlags mode = CONSTANT_SIZE) {
    li(rd, Operand(j), line, mode);
  }
  inline void li(Register dst, Handle<Object> value,
                 int line = 0, LiFlags mode = CONSTANT_SIZE) {
    li(dst, Operand(value), line, mode);
  }
  inline void li(DoubleRegister rd, int64_t j, int line = 0, LiFlags mode = CONSTANT_SIZE) {
    Register srd = Register::from_code(rd.code());
    li(srd, Operand(j), line, mode);
  }
  void li(DoubleRegister rd, Operand j, int line = 0, LiFlags mode = CONSTANT_SIZE) {
    Register rdd = Register::from_code(rd.code());
    li(rdd, j, line, mode);
  }

  // Push multiple registers on the stack.
  // Registers are saved in numerical order, with higher numbered registers
  // saved in higher memory addresses.
  void MultiPush(RegList regs);
  void MultiPushReversed(RegList regs);

  void MultiPushFPU(RegList regs);
  void MultiPushReversedFPU(RegList regs);

  // Pops multiple values from the stack and load them in the
  // registers specified in regs. Pop order is the opposite as in MultiPush.
  void MultiPop(RegList regs);
  void MultiPopReversed(RegList regs);

  void MultiPopFPU(RegList regs);
  void MultiPopReversedFPU(RegList regs);

  // Flush the I-cache from asm code. You should use CPU::FlushICache from C.
  // Does not handle errors.
  void FlushICache(Register address, unsigned instructions);

  // Jump unconditionally to given label.
  void jmp(Label* L) {
    Branch(L);
  }

  // Jump, Call, and Ret pseudo instructions implementing inter-working.
#define COND_ARGS Condition cond = al, Register rs = zero, \
  const Operand& rt = Operand(zero)

  void Jump(Register target, COND_ARGS);
  void Jump(intptr_t target, RelocInfo::Mode rmode, COND_ARGS);
  void Jump(Address target, RelocInfo::Mode rmode, COND_ARGS);
  void Jump(Handle<Code> code, RelocInfo::Mode rmode, COND_ARGS);
  static int CallSize(Register target, COND_ARGS);
  void Call(Register target, COND_ARGS);
  static int CallSize(Address target, RelocInfo::Mode rmode, COND_ARGS);
  void Call(Address target, RelocInfo::Mode rmode, COND_ARGS);
  int CallSize(Handle<Code> code,
               RelocInfo::Mode rmode = RelocInfo::CODE_TARGET,
               TypeFeedbackId ast_id = TypeFeedbackId::None(),
               COND_ARGS);
  void Call(Handle<Code> code,
            RelocInfo::Mode rmode = RelocInfo::CODE_TARGET,
            TypeFeedbackId ast_id = TypeFeedbackId::None(),
            COND_ARGS);
  void Ret(COND_ARGS);

  void Branch(Label* L,
              Condition cond,
              Register rs,
              Heap::RootListIndex index);

  void Branch(Label* L,
              Condition cond,
              DoubleRegister rs,
              Heap::RootListIndex index) {
    Branch(L, cond, Register::from_code(rs.code()), index); }

  void Branch(Label* L,
	      Condition cond,
	      DoubleRegister rs,
	      Operand op) {
    Branch(L, cond, Register::from_code(rs.code()), op); }

  void BranchF(Label* target,
	       Label* nan,
	       Condition cc,
	       DoubleRegister cmp1,
	       DoubleRegister cmp2);

#undef COND_ARGS

  void Call(Label* target);

  inline void Move(Register dst, Register src) {
    if (!dst.is(src)) {
      move(dst, src);
    }
  }

  // Lower case push() for compatibility with arch-independent code.
  void push(Register src) {
    addi(sp, sp, -kPointerSize);
    st(src, sp);
  }

  void push(DoubleRegister src) {
    addi(sp, sp, -kPointerSize);
    st(src, sp);
  }

  void pop(Register dst) {
    ld(dst, sp);
    addi(sp, sp, kPointerSize);
  }

  void pop(DoubleRegister dst) {
    ld(dst, sp);
    addi(sp, sp, kPointerSize);
  }


  // Pop two registers. Pops rightmost register first (from lower address).
  void Pop(Register src1, Register src2) {
    ASSERT(!src1.is(src2));
    ld(src2, MemOperand(sp, 0 * kPointerSize));
    ld(src1, MemOperand(sp, 1 * kPointerSize));
    Addu(sp, sp, 2 * kPointerSize);
  }

  // Pop three registers. Pops rightmost register first (from lower address).
  void Pop(Register src1, Register src2, Register src3) {
    ld(src3, MemOperand(sp, 0 * kPointerSize));
    ld(src2, MemOperand(sp, 1 * kPointerSize));
    ld(src1, MemOperand(sp, 2 * kPointerSize));
    Addu(sp, sp, 3 * kPointerSize);
  }

  void Pop(uint32_t count = 1) {
    Addu(sp, sp, Operand(count * kPointerSize));
  }

  // Push a handle.
  void Push(Handle<Object> handle);
  void Push(Smi* smi) { Push(Handle<Smi>(smi, isolate())); }

  // Push two registers. Pushes leftmost register first (to highest address).
  void Push(Register src1, Register src2) {
    Subu(sp, sp, Operand(2 * kPointerSize));
    st(src1, MemOperand(sp, 1 * kPointerSize));
    st(src2, MemOperand(sp, 0 * kPointerSize));
  }

  // Push three registers. Pushes leftmost register first (to highest address).
  void Push(Register src1, Register src2, Register src3) {
    Subu(sp, sp, Operand(3 * kPointerSize));
    st(src1, MemOperand(sp, 2 * kPointerSize));
    st(src2, MemOperand(sp, 1 * kPointerSize));
    st(src3, MemOperand(sp, 0 * kPointerSize));
  }

  // Push four registers. Pushes leftmost register first (to highest address).
  void Push(Register src1, Register src2, Register src3, Register src4) {
    Subu(sp, sp, Operand(4 * kPointerSize));
    st(src1, MemOperand(sp, 3 * kPointerSize));
    st(src2, MemOperand(sp, 2 * kPointerSize));
    st(src3, MemOperand(sp, 1 * kPointerSize));
    st(src4, MemOperand(sp, 0 * kPointerSize));
  }

  // Convert the HeapNumber pointed to by source to a 32bits signed integer
  // dest. If the HeapNumber does not fit into a 32bits signed integer branch
  // to not_int32 label. If FPU is available double_scratch is used but not
  // scratch2.
  void ConvertToInt32(Register source,
                      Register dest,
                      Register scratch,
                      Register scratch2,
                      Register scratch3,
                      Register scratch4,
		      Label *not_int32,
		      bool gcc_mode = false,
		      bool need_load = true);

  // Helper for EmitECMATruncate.
  // This will truncate a floating-point value outside of the singed 32bit
  // integer range to a 32bit signed integer.
  // Expects the double value loaded in input_high and input_low.
  // Exits with the answer in 'result'.
  // Note that this code does not work for values in the 32bit range!
  void EmitOutOfInt32RangeTruncate(Register result,
                                   Register input,
                                   Register scratch);

  // Convert Double to Int64, rounding to zero
  void ConvertToInt64(Register source,
                      Register dest,
                      Register scratch1,
                      Register scratch2,
                      Register scratch3,
                      Register scratch4,
		      Register scratch5,
                      bool need_load = true);

  // Check if the map of an object is equal to a specified map and branch to a
  // specified target if equal. Skip the smi check if not required (object is
  // known to be a heap object)
  void DispatchMap(Register obj,
                   Register scratch,
                   Handle<Map> map,
                   Handle<Code> success,
                   SmiCheckType smi_check_type);

  void DropAndRet(int drop);

  void DropAndRet(int drop,
                  Condition cond,
                  Register reg,
                  const Operand& op);

  void Swap(Register reg1, Register reg2, Register scratch = no_reg);
  // Emit code to discard a non-negative number of pointer-sized elements
  // from the stack, clobbering only the sp register.
  void Drop(int count,
            Condition cond = cc_always,
            Register reg = no_reg,
            const Operand& op = Operand(no_reg));

  void TryGetFunctionPrototype(Register function,
                               Register result,
                               Register scratch,
                               Label* miss,
                               bool miss_on_bound_function = false);

  void RetOnOverflow(Register overflow_check) {
    Ret(lt, overflow_check, Operand(zero));
  }

  void RetOnNoOverflow(Register overflow_check) {
    Ret(ge, overflow_check, Operand(zero));
  }

  // See comments at the beginning of CEntryStub::Generate.
  inline void PrepareCEntryArgs(int num_args) {
    li(s0, num_args);
    li(s1, (num_args - 1) * kPointerSize);
  }

  inline void PrepareCEntryFunction(const ExternalReference& ref) {
    li(s2, Operand(ref));
  }

  // Call a code stub.
  void CallStub(CodeStub* stub,
                TypeFeedbackId ast_id = TypeFeedbackId::None(),
                Condition cond = cc_always,
                Register r1 = zero,
                const Operand& r2 = Operand(zero));
  // Tail call a code stub (jump).
  void TailCallStub(CodeStub* stub);

  void CallJSExitStub(CodeStub* stub);

  // Call a runtime routine.
  void CallRuntime(const Runtime::Function* f, int num_arguments);
  void CallRuntimeSaveDoubles(Runtime::FunctionId id);

  // Convenience function: Same as above, but takes the fid instead.
  void CallRuntime(Runtime::FunctionId fid, int num_arguments);

  int CalculateStackPassedWords(int num_reg_arguments);

  // Convenience function: call an external reference.
  void CallExternalReference(const ExternalReference& ext,
                             int num_arguments);


  void SetCounter(StatsCounter* counter, int value,
                  Register scratch1, Register scratch2);
  void IncrementCounter(StatsCounter* counter, int value,
                        Register scratch1, Register scratch2);
  void DecrementCounter(StatsCounter* counter, int value,
                        Register scratch1, Register scratch2);

  // Tail call of a runtime routine (jump).
  // Like JumpToExternalReference, but also takes care of passing the number
  // of parameters.
  void TailCallExternalReference(const ExternalReference& ext,
                                 int num_arguments,
                                 int result_size);

  // Convenience function: tail call a runtime routine (jump).
  void TailCallRuntime(Runtime::FunctionId fid,
                       int num_arguments,
                       int result_size);

  // -------------------------------------------------------------------------
  // Exception handling.
  
  void CheckFastElements(Register map,
                         Register scratch,
                         Label* fail);

  // Check if a map for a JSObject indicates that the object can have both smi
  // and HeapObject elements.  Jump to the specified label if it does not.
  void CheckFastObjectElements(Register map,
                               Register scratch,
                               Label* fail);

  // Check if a map for a JSObject indicates that the object has fast smi only
  // elements.  Jump to the specified label if it does not.
  void CheckFastSmiElements(Register map,
                            Register scratch,
                            Label* fail);

  // Compare an object's map with the specified map and its transitioned
  // elements maps if mode is ALLOW_ELEMENT_TRANSITION_MAPS. Jumps to
  // "branch_to" if the result of the comparison is "cond". If multiple map
  // compares are required, the compare sequences branches to early_success.
  void CompareMapAndBranch(Register obj,
                           Register scratch,
                           Handle<Map> map,
                           Label* early_success,
                           Condition cond,
                           Label* branch_to,
                           CompareMapMode mode = REQUIRE_EXACT_MAP);

  // As above, but the map of the object is already loaded into the register
  // which is preserved by the code generated.
  void CompareMapAndBranch(Register obj_map,
                           Handle<Map> map,
                           Label* early_success,
                           Condition cond,
                           Label* branch_to,
                           CompareMapMode mode = REQUIRE_EXACT_MAP);

  void StoreNumberToDoubleElements(Register value_reg,
                                   Register key_reg,
                                   // All regs below here overwritten.
                                   Register elements_reg,
                                   Register scratch1,
                                   Register scratch2,
                                   Register scratch3,
                                   Register scratch4,
                                   Label* fail,
                                   int elements_offset = 0);

  void SetCallKind(Register dst, CallKind kind);

  void InitializeNewString(Register string,
                           Register length,
                           Heap::RootListIndex map_index,
                           Register scratch1,
                           Register scratch2);

  // Invoke the JavaScript function in the given register. Changes the
  // current context to the context in the function before invoking.
  void InvokeFunction(Register function,
                      const ParameterCount& actual,
                      InvokeFlag flag,
                      const CallWrapper& call_wrapper,
                      CallKind call_kind);

  void InvokeFunction(Handle<JSFunction> function,
                      const ParameterCount& expected,
                      const ParameterCount& actual,
                      InvokeFlag flag,
                      const CallWrapper& call_wrapper,
                      CallKind call_kind);

  // Invoke the JavaScript function code by either calling or jumping.
  void InvokeCode(Register code,
                  const ParameterCount& expected,
                  const ParameterCount& actual,
                  InvokeFlag flag,
                  const CallWrapper& call_wrapper,
                  CallKind call_kind);

  void InvokeCode(Handle<Code> code,
                  const ParameterCount& expected,
                  const ParameterCount& actual,
                  RelocInfo::Mode rmode,
                  InvokeFlag flag,
                  CallKind call_kind);

  // Helper functions for generating invokes.
  void InvokePrologue(const ParameterCount& expected,
                      const ParameterCount& actual,
                      Handle<Code> code_constant,
                      Register code_reg,
                      Label* done,
                      bool* definitely_mismatches,
                      InvokeFlag flag,
                      const CallWrapper& call_wrapper,
                      CallKind call_kind);

  // Copies a fixed number of fields of heap objects from src to dst.
  void CopyFields(Register dst, Register src, RegList temps, int field_count);

  // Copies a number of bytes from src to dst. All registers are clobbered. On
  // exit src and dst will point to the place just after where the last byte was
  // read or written and length will be zero.
  void CopyBytes(Register src,
                 Register dst,
                 Register length,
                 Register scratch);

  // Initialize fields with filler values.  Fields starting at |start_offset|
  // not including end_offset are overwritten with the value in |filler|.  At
  // the end the loop, |start_offset| takes the value of |end_offset|.
  void InitializeFieldsWithFiller(Register start_offset,
                                  Register end_offset,
                                  Register filler);

  // Calls an API function.  Allocates HandleScope, extracts returned value
  // from handle and propagates exceptions.  Restores context.  stack_space
  // - space to be unwound on exit (includes the call JS arguments space and
  // the additional space allocated for the fast call).
  void CallApiFunctionAndReturn(ExternalReference function, int stack_space);

  // Jump to the builtin routine.
  void JumpToExternalReference(const ExternalReference& builtin);

  // Generates code for reporting that an illegal operation has
  // occurred.
  void IllegalOperation(int num_arguments);

  // Load and check the instance type of an object for being a string.
  // Loads the type into the second argument register.
  // Returns a condition that will be enabled if the object was a string.
  Condition IsObjectStringType(Register obj,
                               Register type,
                               Register result) {
    ld(type, FieldMemOperand(obj, HeapObject::kMapOffset));
    ld1u(type, FieldMemOperand(type, Map::kInstanceTypeOffset));
    And(type, type, Operand(kIsNotStringMask));
    ASSERT_EQ(0, kStringTag);
    return eq;
  }

  void IndexFromHash(Register hash, Register index);

  // Get the number of least significant bits from a register.
  void GetLeastBitsFromSmi(Register dst, Register src, int num_least_bits);
  void GetLeastBitsFromInt32(Register dst, Register src, int mun_least_bits);

  // -------------------------------------------------------------------------
  // Overflow handling functions.
  // Usage: first call the appropriate arithmetic function, then call one of the
  // jump functions with the overflow_dst register as the second parameter.

  void AddAndCheckForOverflow(Register dst,
                              Register left,
                              Register right,
                              Register overflow_dst,
                              Register scratch,
                              bool is_32bit);
  void AdduAndCheckForOverflow(Register dst,
                               Register left,
                               Register right,
                               Register overflow_dst,
                               Register scratch = at) {
    AddAndCheckForOverflow(dst, left, right,
			   overflow_dst, scratch, false);
  }
  void AddiAndCheckForOverflow(Register dst,
                               Register left,
                               Register right,
                               Register overflow_dst,
                               Register scratch = at) {
    AddAndCheckForOverflow(dst, left, right,
                           overflow_dst, scratch, true);
  }

  void SubAndCheckForOverflow(Register dst,
			      Register left,
			      Register right,
			      Register overflow_dst,
			      Register scratch,
                              bool is_32bit);
  void SubuAndCheckForOverflow(Register dst,
                               Register left,
                               Register right,
                               Register overflow_dst,
                               Register scratch = at) {
    SubAndCheckForOverflow(dst, left, right,
			   overflow_dst, scratch, false);
  }
  void SubiAndCheckForOverflow(Register dst,
                               Register left,
                               Register right,
                               Register overflow_dst,
                               Register scratch = at) {
    SubAndCheckForOverflow(dst, left, right,
                           overflow_dst, scratch, true);
  }

  void BranchOnOverflow(Label* label,
                        Register overflow_check) {
    Branch(label, lt, overflow_check, Operand(zero));
  }

  void BranchOnNoOverflow(Label* label,
                          Register overflow_check) {
    Branch(label, ge, overflow_check, Operand(zero));
  }

  // Check if the map of an object is equal to a specified map and branch to
  // label if not. Skip the smi check if not required (object is known to be a
  // heap object). If mode is ALLOW_ELEMENT_TRANSITION_MAPS, then also match
  // against maps that are ElementsKind transition maps of the specificed map.
  void CheckMap(Register obj,
                Register scratch,
                Handle<Map> map,
                Label* fail,
		SmiCheckType smi_check_type,
		CompareMapMode mode = REQUIRE_EXACT_MAP);


  void CheckMap(Register obj,
                Register scratch,
                Heap::RootListIndex index,
                Label* fail,
                SmiCheckType smi_check_type);

  // Push a new try handler and link into try handler chain.
  void PushTryHandler(StackHandler::Kind kind, int handler_index);

  // Unlink the stack handler on top of the stack from the try handler chain.
  // Must preserve the result register.
  void PopTryHandler();

  void GetObjectType(Register function,
                     Register map,
                     Register type_reg);

  // Passes thrown value to the handler of top of the try handler chain.
  void Throw(Register value);

  void LoadContext(Register dst, int context_chain_length);

  // Conditionally load the cached Array transitioned map of type
  // transitioned_kind from the native context if the map in register
  // map_in_out is the cached Array map in the native context of
  // expected_kind.
  void LoadTransitionedArrayMapConditional(
      ElementsKind expected_kind,
      ElementsKind transitioned_kind,
      Register map_in_out,
      Register scratch,
      Label* no_map_match);

  // Load the initial map for new Arrays from a JSFunction.
  void LoadInitialArrayMap(Register function_in,
                           Register scratch,
                           Register map_out,
                           bool can_have_holes);

  void LoadGlobalFunction(int index, Register function);
  void LoadArrayFunction(Register function);

  // Load the initial map from the global function. The registers
  // function and map can be the same, function is then overwritten.
  void LoadGlobalFunctionInitialMap(Register function,
                                    Register map,
                                    Register scratch);


  void InitializeRootRegister() {
    ExternalReference roots_array_start =
        ExternalReference::roots_array_start(isolate());
    li(kRootRegister, Operand(roots_array_start));
  }

  // Load an object from the root table.
  void LoadRoot(Register destination,
                Heap::RootListIndex index);
  void LoadRoot(Register destination,
                Heap::RootListIndex index,
                Condition cond, Register src1, const Operand& src2);


  // Store an object to the root table.
  void StoreRoot(Register source,
                 Heap::RootListIndex index);
  void StoreRoot(Register source,
                 Heap::RootListIndex index,
                 Condition cond, Register src1, const Operand& src2);

  void LoadHeapObject(Register dst, Handle<HeapObject> object);

  void LoadObject(Register result, Handle<Object> object) {
    ALLOW_HANDLE_DEREF(isolate(), "heap object check");
    if (object->IsHeapObject()) {
      LoadHeapObject(result, Handle<HeapObject>::cast(object));
    } else {
      li(result, Operand(object));
    }
  }


  // Get the actual activation frame alignment for target environment.
  static int ActivationFrameAlignment();

  // Make sure the stack is aligned. Only emits code in debug mode.
  void AssertStackIsAligned();

  // Enter exit frame.
  // argc - argument count to be dropped by LeaveExitFrame.
  // save_doubles - saves FPU registers on stack, currently disabled.
  // stack_space - extra stack space.
  void EnterExitFrame(bool save_doubles,
                      int stack_space = 0);

  // Leave the current exit frame.
  void LeaveExitFrame(bool save_doubles,
                      Register arg_count,
                      bool do_return = false);

  // Push and pop the registers that can hold pointers, as defined by the
  // RegList constant kSafepointSavedRegisters.
  void PushSafepointRegisters();
  void PopSafepointRegisters();
  void PushSafepointRegistersAndDoubles();
  void PopSafepointRegistersAndDoubles();
  // Store value in register src in the safepoint stack slot for
  // register dst.
  void StoreToSafepointRegisterSlot(Register src, Register dst);
  void StoreToSafepointRegistersAndDoublesSlot(Register src, Register dst);
  // Load the value of the src register from its safepoint stack slot
  // into register dst.
  void LoadFromSafepointRegisterSlot(Register dst, Register src);

  // Notify the garbage collector that we wrote a pointer into an object.
  // |object| is the object being stored into, |value| is the object being
  // stored.  value and scratch registers are clobbered by the operation.
  // The offset is the offset from the start of the object, not the offset from
  // the tagged HeapObject pointer.  For use with FieldOperand(reg, off).
  void RecordWriteField(
      Register object,
      int offset,
      Register value,
      Register scratch,
      RAStatus ra_status,
      SaveFPRegsMode save_fp,
      RememberedSetAction remembered_set_action = EMIT_REMEMBERED_SET,
      SmiCheck smi_check = INLINE_SMI_CHECK);

  // As above, but the offset has the tag presubtracted.  For use with
  // MemOperand(reg, off).
  inline void RecordWriteContextSlot(
      Register context,
      int offset,
      Register value,
      Register scratch,
      RAStatus ra_status,
      SaveFPRegsMode save_fp,
      RememberedSetAction remembered_set_action = EMIT_REMEMBERED_SET,
      SmiCheck smi_check = INLINE_SMI_CHECK) {
    RecordWriteField(context,
                     offset + kHeapObjectTag,
                     value,
                     scratch,
                     ra_status,
                     save_fp,
                     remembered_set_action,
                     smi_check);
  }

  // For a given |object| notify the garbage collector that the slot |address|
  // has been written.  |value| is the object being stored. The value and
  // address registers are clobbered by the operation.
  void RecordWrite(
      Register object,
      Register address,
      Register value,
      RAStatus ra_status,
      SaveFPRegsMode save_fp,
      RememberedSetAction remembered_set_action = EMIT_REMEMBERED_SET,
      SmiCheck smi_check = INLINE_SMI_CHECK);

  // Record in the remembered set the fact that we have a pointer to new space
  // at the address pointed to by the addr register.  Only works if addr is not
  // in new space.
  void RememberedSetHelper(Register object,  // Used for debug code.
                           Register addr,
                           Register scratch,
                           SaveFPRegsMode save_fp,
                           RememberedSetFinalAction and_then);

  void CheckPageFlag(Register object,
                     Register scratch,
                     int mask,
                     Condition cc,
                     Label* condition_met);

  void CheckMapDeprecated(Handle<Map> map,
                          Register scratch,
                          Label* if_deprecated);

  // Check if object is in new space.  Jumps if the object is not in new space.
  // The register scratch can be object itself, but it will be clobbered.
  void JumpIfNotInNewSpace(Register object,
                           Register scratch,
                           Label* branch) {
    InNewSpace(object, scratch, ne, branch);
  }

  // Check if object is in new space.  Jumps if the object is in new space.
  // The register scratch can be object itself, but scratch will be clobbered.
  void JumpIfInNewSpace(Register object,
                        Register scratch,
                        Label* branch) {
    InNewSpace(object, scratch, eq, branch);
  }

  // ---------------------------------------------------------------------------
  // Inline caching support.

  // Generate code for checking access rights - used for security checks
  // on access to global objects across environments. The holder register
  // is left untouched, whereas both scratch registers are clobbered.
  void CheckAccessGlobalProxy(Register holder_reg,
                              Register scratch,
                              Label* miss);

  void GetNumberHash(Register reg0, Register scratch);

  void LoadFromNumberDictionary(Label* miss,
                                Register elements,
                                Register key,
                                Register result,
                                Register reg0,
                                Register reg1,
                                Register reg2);

  void IsObjectJSObjectType(Register heap_object,
                            Register map,
                            Register scratch,
                            Label* fail);

  void IsInstanceJSObjectType(Register map,
                              Register scratch,
                              Label* fail);

  void IsObjectJSStringType(Register object,
                            Register scratch,
                            Label* fail);

  void IsObjectNameType(Register object,
                        Register scratch,
                        Label* fail);


#ifdef ENABLE_DEBUGGER_SUPPORT
  // -------------------------------------------------------------------------
  // Debugger Support.

  void DebugBreak();
#endif

  void Jr(Label* L);

 private:
  static const int kSmiShift = kSmiTagSize + kSmiShiftSize;

  void CallCFunctionHelper(Register function,
                           int num_reg_arguments);
  void BranchShort(Label* L);
  void BranchShort(Label* L, Condition cond, Register rs, const Operand& rt);
  void BranchShort(int16_t offset);
  void BranchShort(int16_t offset, Condition cond, Register rs, const Operand& rt);

  void BranchAndLinkShort(int16_t offset){UNREACHABLE();}
  void BranchAndLinkShort(int16_t offset, Condition cond, Register rs,
                          const Operand& rt){UNREACHABLE();}
  void BranchAndLinkShort(Label* L);
  void BranchAndLinkShort(Label* L, Condition cond, Register rs,
                          const Operand& rt){UNREACHABLE();}
  void J(Label* L);
  void Jalr(Label* L);

  bool generating_stub_;
  bool allow_stub_calls_;
  bool has_frame_;

  // This handle will be patched with the code object on installation.
  Handle<Object> code_object_;

  static int SafepointRegisterStackIndex(int reg_code);
  MemOperand SafepointRegisterSlot(Register reg);
  MemOperand SafepointRegistersAndDoublesSlot(Register reg);

  // Helper for implementing JumpIfNotInNewSpace and JumpIfInNewSpace.
  void InNewSpace(Register object,
                  Register scratch,
                  Condition cond,  // eq for new space, ne otherwise.
                  Label* branch);

  // Needs access to SafepointRegisterStackIndex for compiled frame
  // traversal.
  friend class StandardFrame;
};

// The code patcher is used to patch (typically) small parts of code e.g. for
// debugging and other types of instrumentation. When using the code patcher
// the exact number of bytes specified must be emitted. It is not legal to emit
// relocation information. If any of these constraints are violated it causes
// an assertion to fail.
class CodePatcher {
 public:
  CodePatcher(byte* address, int instructions);
  virtual ~CodePatcher();

  // Macro assembler to emit code.
  MacroAssembler* masm() { return &masm_; }

  // Emit an instruction directly.
  void Emit(Instr instr);

  // Emit an address directly.
  void Emit(Address addr);

  // Change the condition part of an instruction leaving the rest of the current
  // instruction unchanged.
  void ChangeBranchCondition(Condition cond);

 private:
  byte* address_;  // The address of the code being patched.
  int size_;  // Number of bytes of the expected patch size.
  MacroAssembler masm_;  // Macro assembler used to generate the code.
};

#ifdef GENERATED_CODE_COVERAGE
#define CODE_COVERAGE_STRINGIFY(x) #x
#define CODE_COVERAGE_TOSTRING(x) CODE_COVERAGE_STRINGIFY(x)
#define __FILE_LINE__ __FILE__ ":" CODE_COVERAGE_TOSTRING(__LINE__)
#define ACCESS_MASM(masm) masm->stop(__FILE_LINE__); masm->
#else
#define ACCESS_MASM(masm) masm->
#endif

} }  // namespace v8::internal

#endif  // V8_TILEGX_MACRO_ASSEMBLER_TILEGX_H_
