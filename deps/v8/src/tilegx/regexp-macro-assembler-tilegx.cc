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

#include "unicode.h"
#include "log.h"
#include "code-stubs.h"
#include "regexp-stack.h"
#include "macro-assembler.h"
#include "regexp-macro-assembler.h"
#include "tilegx/regexp-macro-assembler-tilegx.h"

namespace v8 {
namespace internal {

#ifndef V8_INTERPRETED_REGEXP
/*
 * This assembler uses the following register assignment convention
 * - t7 : Temporarily stores the index of capture start after a matching pass
 *        for a global regexp.
 * - t1 : Pointer to current code object (Code*) including heap object tag.
 * - t2 : Current position in input, as negative offset from end of string.
 *        Please notice that this is the byte offset, not the character offset!
 * - t3 : Currently loaded character. Must be loaded using
 *        LoadCurrentCharacter before using any of the dispatch methods.
 * - t4 : Points to tip of backtrack stack
 * - t5 : Unused.
 * - t6 : End of input (points to byte after last character in input).
 * - fp : Frame pointer. Used to access arguments, local variables and
 *         RegExp registers.
 * - sp : Points to tip of C stack.
 *
 * The remaining registers are free for computations.
 * Each call to a public method should retain this convention.
 *
 * The stack will have the following structure:
 *
 *  - fp[64]  Isolate* isolate   (address of the current isolate)
 *  - fp[60]  direct_call  (if 1, direct call from JavaScript code,
 *                          if 0, call through the runtime system).
 *  - fp[56]  stack_area_base (High end of the memory area to use as
 *                             backtracking stack).
 *  - fp[52]  capture array size (may fit multiple sets of matches)
 *  - fp[48]  int* capture_array (int[num_saved_registers_], for output).
 *  - fp[44]  secondary link/return address used by native call.
 *  --- sp when called ---
 *  - fp[40]  return address      (lr).
 *  - fp[36]  old frame pointer   (r11).
 *  - fp[0..32]  backup of registers s0..s7.
 *  --- frame pointer ----
 *  - fp[-4]  end of input       (address of end of string).
 *  - fp[-8]  start of input     (address of first character in string).
 *  - fp[-12] start index        (character index of start).
 *  - fp[-16] void* input_string (location of a handle containing the string).
 *  - fp[-20] success counter    (only for global regexps to count matches).
 *  - fp[-24] Offset of location before start of input (effectively character
 *            position -1). Used to initialize capture registers to a
 *            non-position.
 *  - fp[-28] At start (if 1, we are starting at the start of the
 *    string, otherwise 0)
 *  - fp[-32] register 0         (Only positions must be stored in the first
 *  -         register 1          num_saved_registers_ registers)
 *  -         ...
 *  -         register num_registers-1
 *  --- sp ---
 *
 * The first num_saved_registers_ registers are initialized to point to
 * "character -1" in the string (i.e., char_size() bytes before the first
 * character of the string). The remaining registers start out as garbage.
 *
 * The data up to the return address must be placed there by the calling
 * code and the remaining arguments are passed in registers, e.g. by calling the
 * code entry as cast to a function with the signature:
 * int (*match)(String* input_string,
 *              int start_index,
 *              Address start,
 *              Address end,
 *              Address secondary_return_address,  // Only used by native call.
 *              int* capture_output_array,
 *              byte* stack_area_base,
 *              bool direct_call = false)
 * The call is performed by NativeRegExpMacroAssembler::Execute()
 * (in regexp-macro-assembler.cc) via the CALL_GENERATED_REGEXP_CODE macro
 * in mips/simulator-mips.h.
 * When calling as a non-direct call (i.e., from C++ code), the return address
 * area is overwritten with the ra register by the RegExp code. When doing a
 * direct call from generated code, the return address is placed there by
 * the calling code, as in a normal exit frame.
 */

#define __ ACCESS_MASM(masm_)

RegExpMacroAssemblerTILEGX::RegExpMacroAssemblerTILEGX(
    Mode mode,
    int registers_to_save,
    Zone* zone)
    : NativeRegExpMacroAssembler(zone),
      masm_(new MacroAssembler(Isolate::Current(), NULL, kRegExpCodeSize)),
      mode_(mode),
      num_registers_(registers_to_save),
      num_saved_registers_(registers_to_save),
      entry_label_(),
      start_label_(),
      success_label_(),
      backtrack_label_(),
      exit_label_(),
      internal_failure_label_() {
	      UNIMPLEMENTED();
}


RegExpMacroAssemblerTILEGX::~RegExpMacroAssemblerTILEGX() {
  delete masm_;
  // Unuse labels in case we throw away the assembler without calling GetCode.
  entry_label_.Unuse();
  start_label_.Unuse();
  success_label_.Unuse();
  backtrack_label_.Unuse();
  exit_label_.Unuse();
  check_preempt_label_.Unuse();
  stack_overflow_label_.Unuse();
  internal_failure_label_.Unuse();
}


int RegExpMacroAssemblerTILEGX::stack_limit_slack()  {
  return RegExpStack::kStackLimitSlack;
}


void RegExpMacroAssemblerTILEGX::AdvanceCurrentPosition(int by) {
	UNIMPLEMENTED();
}


void RegExpMacroAssemblerTILEGX::AdvanceRegister(int reg, int by) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::Backtrack() { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::Bind(Label* label) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckCharacter(uint32_t c, Label* on_equal) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckCharacterGT(uc16 limit, Label* on_greater) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckAtStart(Label* on_at_start) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckNotAtStart(Label* on_not_at_start) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckCharacterLT(uc16 limit, Label* on_less) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckCharacters(Vector<const uc16> str,
                                               int cp_offset,
                                               Label* on_failure,
                                               bool check_end_of_string) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckGreedyLoop(Label* on_equal) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckNotBackReferenceIgnoreCase(
    int start_reg,
    Label* on_no_match) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckNotBackReference(
    int start_reg,
    Label* on_no_match) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckNotCharacter(uint32_t c,
                                                 Label* on_not_equal) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckCharacterAfterAnd(uint32_t c,
                                                      uint32_t mask,
                                                      Label* on_equal) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckNotCharacterAfterAnd(uint32_t c,
                                                         uint32_t mask,
                                                         Label* on_not_equal) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckNotCharacterAfterMinusAnd(
    uc16 c,
    uc16 minus,
    uc16 mask,
    Label* on_not_equal) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckCharacterInRange(
    uc16 from,
    uc16 to,
    Label* on_in_range) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckCharacterNotInRange(
    uc16 from,
    uc16 to,
    Label* on_not_in_range) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckBitInTable(
    Handle<ByteArray> table,
    Label* on_bit_set) { UNIMPLEMENTED(); }


bool RegExpMacroAssemblerTILEGX::CheckSpecialCharacterClass(uc16 type,
                                                          Label* on_no_match) { UNIMPLEMENTED(); return false;}


void RegExpMacroAssemblerTILEGX::Fail() { UNIMPLEMENTED(); }


Handle<HeapObject> RegExpMacroAssemblerTILEGX::GetCode(Handle<String> source) { UNIMPLEMENTED();
  CodeDesc code_desc;
  masm_->GetCode(&code_desc);
  Handle<Code> code = isolate()->factory()->NewCode(
      code_desc, Code::ComputeFlags(Code::REGEXP), masm_->CodeObject());
  LOG(masm_->isolate(), RegExpCodeCreateEvent(*code, *source));
  return Handle<HeapObject>::cast(code);
}

void RegExpMacroAssemblerTILEGX::GoTo(Label* to) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::IfRegisterGE(int reg,
                                            int comparand,
                                            Label* if_ge) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::IfRegisterLT(int reg,
                                            int comparand,
                                            Label* if_lt) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::IfRegisterEqPos(int reg,
                                               Label* if_eq) { UNIMPLEMENTED(); }


RegExpMacroAssembler::IrregexpImplementation
    RegExpMacroAssemblerTILEGX::Implementation() { return kTILEGXImplementation; }


void RegExpMacroAssemblerTILEGX::LoadCurrentCharacter(int cp_offset,
                                                    Label* on_end_of_input,
                                                    bool check_bounds,
                                                    int characters) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::PopCurrentPosition() { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::PopRegister(int register_index) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::PushBacktrack(Label* label) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::PushCurrentPosition() { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::PushRegister(int register_index,
                                            StackCheckFlag check_stack_limit) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::ReadCurrentPositionFromRegister(int reg) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::ReadStackPointerFromRegister(int reg) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::SetCurrentPositionFromEnd(int by) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::SetRegister(int register_index, int to) { UNIMPLEMENTED(); }


bool RegExpMacroAssemblerTILEGX::Succeed() { UNIMPLEMENTED(); return false;}


void RegExpMacroAssemblerTILEGX::WriteCurrentPositionToRegister(int reg,
                                                              int cp_offset) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::ClearRegisters(int reg_from, int reg_to) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::WriteStackPointerToRegister(int reg) { UNIMPLEMENTED(); }


bool RegExpMacroAssemblerTILEGX::CanReadUnaligned() {
  return false;
}


// Private methods:

void RegExpMacroAssemblerTILEGX::CallCheckStackGuardState(Register scratch) { UNIMPLEMENTED(); }

int RegExpMacroAssemblerTILEGX::CheckStackGuardState(Address* return_address,
                                                   Code* re_code,
                                                   Address re_frame) { UNIMPLEMENTED(); return -1;}


MemOperand RegExpMacroAssemblerTILEGX::register_location(int register_index) { UNIMPLEMENTED(); return MemOperand(r0); }


void RegExpMacroAssemblerTILEGX::CheckPosition(int cp_offset,
                                             Label* on_outside_input) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::BranchOrBacktrack(Label* to,
                                                 Condition condition,
                                                 Register rs,
                                                 const Operand& rt) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::SafeCall(Label* to,
                                        Condition cond,
                                        Register rs,
                                        const Operand& rt) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::SafeReturn() { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::SafeCallTarget(Label* name) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::Push(Register source) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::Pop(Register target) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckPreemption() { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CheckStackLimit() { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::CallCFunctionUsingStub(
    ExternalReference function,
    int num_arguments) { UNIMPLEMENTED(); }


void RegExpMacroAssemblerTILEGX::LoadCurrentCharacterUnchecked(int cp_offset,
                                                             int characters) { UNIMPLEMENTED(); }


#undef __

#endif  // V8_INTERPRETED_REGEXP

}}  // namespace v8::internal

#endif  // V8_TARGET_ARCH_TILEGX
