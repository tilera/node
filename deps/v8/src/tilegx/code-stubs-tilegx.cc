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

#include "bootstrapper.h"
#include "builtins-decls.h"
#include "code-stubs.h"
#include "codegen.h"
#include "regexp-macro-assembler.h"
#include "stub-cache.h"

namespace v8 {
namespace internal {

#define __ ACCESS_MASM(masm)

void FastCloneShallowArrayStub::InitializeInterfaceDescriptor(
    Isolate* isolate,
    CodeStubInterfaceDescriptor* descriptor) {
  static Register registers[] = { a3, a2, a1 };
  descriptor->register_param_count_ = 3;
  descriptor->register_params_ = registers;
  descriptor->stack_parameter_count_ = NULL;
  descriptor->deoptimization_handler_ =
      Runtime::FunctionForId(Runtime::kCreateArrayLiteralShallow)->entry;
}


void FastCloneShallowObjectStub::InitializeInterfaceDescriptor(
    Isolate* isolate,
    CodeStubInterfaceDescriptor* descriptor) {
  static Register registers[] = { a3, a2, a1, a0 };
  descriptor->register_param_count_ = 4;
  descriptor->register_params_ = registers;
  descriptor->stack_parameter_count_ = NULL;
  descriptor->deoptimization_handler_ =
      Runtime::FunctionForId(Runtime::kCreateObjectLiteralShallow)->entry;
}


void KeyedLoadFastElementStub::InitializeInterfaceDescriptor(
    Isolate* isolate,
    CodeStubInterfaceDescriptor* descriptor) {
  static Register registers[] = { a1, a0 };
  descriptor->register_param_count_ = 2;
  descriptor->register_params_ = registers;
  descriptor->deoptimization_handler_ =
      FUNCTION_ADDR(KeyedLoadIC_MissFromStubFailure);
}


void KeyedStoreFastElementStub::InitializeInterfaceDescriptor(
    Isolate* isolate,
    CodeStubInterfaceDescriptor* descriptor) {
  static Register registers[] = { a2, a1, a0 };
  descriptor->register_param_count_ = 3;
  descriptor->register_params_ = registers;
  descriptor->deoptimization_handler_ =
      FUNCTION_ADDR(KeyedStoreIC_MissFromStubFailure);
}


void TransitionElementsKindStub::InitializeInterfaceDescriptor(
    Isolate* isolate,
    CodeStubInterfaceDescriptor* descriptor) {
  static Register registers[] = { a0, a1 };
  descriptor->register_param_count_ = 2;
  descriptor->register_params_ = registers;
  Address entry =
      Runtime::FunctionForId(Runtime::kTransitionElementsKind)->entry;
  descriptor->deoptimization_handler_ = FUNCTION_ADDR(entry);
}


void CompareNilICStub::InitializeInterfaceDescriptor(
    Isolate* isolate,
    CodeStubInterfaceDescriptor* descriptor) {
  static Register registers[] = { a0 };
  descriptor->register_param_count_ = 1;
  descriptor->register_params_ = registers;
  descriptor->deoptimization_handler_ =
      FUNCTION_ADDR(CompareNilIC_Miss);
  descriptor->miss_handler_ =
      ExternalReference(IC_Utility(IC::kCompareNilIC_Miss), isolate);
}


static void InitializeArrayConstructorDescriptor(
    Isolate* isolate,
    CodeStubInterfaceDescriptor* descriptor,
    int constant_stack_parameter_count) {
  // register state
  // a0 -- number of arguments
  // a1 -- function
  // a2 -- type info cell with elements kind
  static Register registers[] = { a2 };
  descriptor->register_param_count_ = 1;
  if (constant_stack_parameter_count != 0) {
    // stack param count needs (constructor pointer, and single argument)
    descriptor->stack_parameter_count_ = &a0;
  }
  descriptor->hint_stack_parameter_count_ = constant_stack_parameter_count;
  descriptor->register_params_ = registers;
  descriptor->function_mode_ = JS_FUNCTION_STUB_MODE;
  descriptor->deoptimization_handler_ =
      FUNCTION_ADDR(ArrayConstructor_StubFailure);
}


void ArrayNoArgumentConstructorStub::InitializeInterfaceDescriptor(
    Isolate* isolate,
    CodeStubInterfaceDescriptor* descriptor) {
  InitializeArrayConstructorDescriptor(isolate, descriptor, 0);
}


void ArraySingleArgumentConstructorStub::InitializeInterfaceDescriptor(
    Isolate* isolate,
    CodeStubInterfaceDescriptor* descriptor) {
  InitializeArrayConstructorDescriptor(isolate, descriptor, 1);
}


void ArrayNArgumentsConstructorStub::InitializeInterfaceDescriptor(
    Isolate* isolate,
    CodeStubInterfaceDescriptor* descriptor) {
  InitializeArrayConstructorDescriptor(isolate, descriptor, -1);
}


// Check if the operand is a heap number.
static void EmitCheckForHeapNumber(MacroAssembler* masm, Register operand,
                                   Register scratch1, Register scratch2,
                                   Label* not_a_heap_number) {
  __ ld(scratch1, FieldMemOperand(operand, HeapObject::kMapOffset));
  __ LoadRoot(scratch2, Heap::kHeapNumberMapRootIndex);
  __ Branch(not_a_heap_number, ne, scratch1, Operand(scratch2));
}

void HydrogenCodeStub::GenerateLightweightMiss(MacroAssembler* masm) {
  // Update the static counter each time a new code stub is generated.
  Isolate* isolate = masm->isolate();
  isolate->counters()->code_stubs()->Increment();

  CodeStubInterfaceDescriptor* descriptor = GetInterfaceDescriptor(isolate);
  int param_count = descriptor->register_param_count_;
  {
    // Call the runtime system in a fresh internal frame.
    FrameScope scope(masm, StackFrame::INTERNAL);
    ASSERT(descriptor->register_param_count_ == 0 ||
           a0.is(descriptor->register_params_[param_count - 1]));
    // Push arguments
    for (int i = 0; i < param_count; ++i) {
      __ push(descriptor->register_params_[i]);
    }
    ExternalReference miss = descriptor->miss_handler_;
    __ CallExternalReference(miss, descriptor->register_param_count_);
  }

  __ Ret();
}


void ToNumberStub::Generate(MacroAssembler* masm) {
  // The ToNumber stub takes one argument in a0.
  Label check_heap_number, call_builtin;
  __ JumpIfNotSmi(a0, &check_heap_number);
  __ Ret();

  __ bind(&check_heap_number);
  EmitCheckForHeapNumber(masm, a0, a1, t0, &call_builtin);
  __ Ret();

  __ bind(&call_builtin);
  __ push(a0);
  __ InvokeBuiltin(Builtins::TO_NUMBER, JUMP_FUNCTION);
}


void FastNewClosureStub::Generate(MacroAssembler* masm) {
  // Create a new closure from the given function info in new
  // space. Set the context to the current context in cp.
  Counters* counters = masm->isolate()->counters();

  Label gc;

  // Pop the function info from the stack.
  __ pop(a3);

  // Attempt to allocate new JSFunction in new space.
  __ Allocate(JSFunction::kSize, v0, a1, a2, &gc, TAG_OBJECT);

  __ IncrementCounter(counters->fast_new_closure_total(), 1, t2, t3);

  int map_index = Context::FunctionMapIndex(language_mode_, is_generator_);

  // Compute the function map in the current native context and set that
  // as the map of the allocated object.
  __ ld(a2, MemOperand(cp, Context::SlotOffset(Context::GLOBAL_OBJECT_INDEX)));
  __ ld(a2, FieldMemOperand(a2, GlobalObject::kNativeContextOffset));
  __ ld(t1, MemOperand(a2, Context::SlotOffset(map_index)));
  __ st(t1, FieldMemOperand(v0, HeapObject::kMapOffset));

  // Initialize the rest of the function. We don't have to update the
  // write barrier because the allocated object is in new space.
  __ LoadRoot(a1, Heap::kEmptyFixedArrayRootIndex);
  __ LoadRoot(t1, Heap::kTheHoleValueRootIndex);
  __ st(a1, FieldMemOperand(v0, JSObject::kPropertiesOffset));
  __ st(a1, FieldMemOperand(v0, JSObject::kElementsOffset));
  __ st(t1, FieldMemOperand(v0, JSFunction::kPrototypeOrInitialMapOffset));
  __ st(a3, FieldMemOperand(v0, JSFunction::kSharedFunctionInfoOffset));
  __ st(cp, FieldMemOperand(v0, JSFunction::kContextOffset));
  __ st(a1, FieldMemOperand(v0, JSFunction::kLiteralsOffset));

  // Initialize the code pointer in the function to be the one
  // found in the shared function info object.
  // But first check if there is an optimized version for our context.
  Label check_optimized;
  Label install_unoptimized;
  if (FLAG_cache_optimized_code) {
    __ ld(a1,
          FieldMemOperand(a3, SharedFunctionInfo::kOptimizedCodeMapOffset));
    __ And(at, a1, a1);
    __ Branch(&check_optimized, ne, at, Operand(zero));
  }
  __ bind(&install_unoptimized);
  __ LoadRoot(t0, Heap::kUndefinedValueRootIndex);
  __ st(t0, FieldMemOperand(v0, JSFunction::kNextFunctionLinkOffset));
  __ ld(a3, FieldMemOperand(a3, SharedFunctionInfo::kCodeOffset));
  __ Addu(a3, a3, Operand(Code::kHeaderSize - kHeapObjectTag));

  // Return result. The argument function info has been popped already.
  __ st(a3, FieldMemOperand(v0, JSFunction::kCodeEntryOffset));
  __ Ret();

  __ bind(&check_optimized);

  __ IncrementCounter(counters->fast_new_closure_try_optimized(), 1, t2, t3);

  // a2 holds native context, a1 points to fixed array of 3-element entries
  // (native context, optimized code, literals).
  // The optimized code map must never be empty, so check the first elements.
  Label install_optimized;
  // Speculatively move code object into t0.
  __ ld(t0, FieldMemOperand(a1, FixedArray::kHeaderSize + kPointerSize));
  __ ld(t1, FieldMemOperand(a1, FixedArray::kHeaderSize));
  __ Branch(&install_optimized, eq, a2, Operand(t1));

  // Iterate through the rest of map backwards.  t0 holds an index as a Smi.
  Label loop;
  __ ld(t0, FieldMemOperand(a1, FixedArray::kLengthOffset));
  __ bind(&loop);
  // Do not double check first entry.
  __ Branch(&install_unoptimized, eq, t0,
            Operand(Smi::FromInt(SharedFunctionInfo::kEntryLength)));
  __ Subu(t0, t0, Operand(Smi::FromInt(
		  SharedFunctionInfo::kEntryLength))); // Skip an entry.
  __ Addu(t1, a1, Operand(FixedArray::kHeaderSize - kHeapObjectTag));
  __ sra(at, t0, 32);
  __ sll(at, at, kPointerSizeLog2);
  __ Addu(t1, t1, Operand(at));
  __ ld(t1, MemOperand(t1));
  __ Branch(&loop, ne, a2, Operand(t1));
  // Hit: fetch the optimized code.
  __ Addu(t1, a1, Operand(FixedArray::kHeaderSize - kHeapObjectTag));
  __ sra(at, t0, 32);
  __ sll(at, at, kPointerSizeLog2);
  __ Addu(t1, t1, Operand(at));
  __ Addu(t1, t1, Operand(kPointerSize));
  __ ld(t0, MemOperand(t1));

  __ bind(&install_optimized);
  __ IncrementCounter(counters->fast_new_closure_install_optimized(),
                      1, t2, t3);

  // TODO(fschneider): Idea: store proper code pointers in the map and either
  // unmangle them on marking or do nothing as the whole map is discarded on
  // major GC anyway.
  __ Addu(t0, t0, Operand(Code::kHeaderSize - kHeapObjectTag));
  __ st(t0, FieldMemOperand(v0, JSFunction::kCodeEntryOffset));

  // Now link a function into a list of optimized functions.
  __ ld(t0, ContextOperand(a2, Context::OPTIMIZED_FUNCTIONS_LIST));

  __ st(t0, FieldMemOperand(v0, JSFunction::kNextFunctionLinkOffset));
  // No need for write barrier as JSFunction (eax) is in the new space.

  __ st(v0, ContextOperand(a2, Context::OPTIMIZED_FUNCTIONS_LIST));
  // Store JSFunction (eax) into edx before issuing write barrier as
  // it clobbers all the registers passed.
  __ move(t0, v0);
  __ RecordWriteContextSlot(
      a2,
      Context::SlotOffset(Context::OPTIMIZED_FUNCTIONS_LIST),
      t0,
      a1,
      kRAHasNotBeenSaved,
      kDontSaveFPRegs);

  // Return result. The argument function info has been popped already.
  __ Ret();

  // Create a new closure through the slower runtime call.
  __ bind(&gc);
  __ LoadRoot(t0, Heap::kFalseValueRootIndex);
  __ Push(cp, a3, t0);
  __ TailCallRuntime(Runtime::kNewClosure, 3, 1);
}


void FastNewContextStub::Generate(MacroAssembler* masm) {
  // Try to allocate the context in new space.
  Label gc;
  int length = slots_ + Context::MIN_CONTEXT_SLOTS;

  // Attempt to allocate the context in new space.
  __ Allocate(FixedArray::SizeFor(length), v0, a1, a2, &gc, TAG_OBJECT);

  // Load the function from the stack.
  __ ld(a3, MemOperand(sp, 0));

  // Set up the object header.
  __ LoadRoot(a1, Heap::kFunctionContextMapRootIndex);
  __ li(a2, Operand(Smi::FromInt(length)));
  __ st(a2, FieldMemOperand(v0, FixedArray::kLengthOffset));
  __ st(a1, FieldMemOperand(v0, HeapObject::kMapOffset));

  // Set up the fixed slots, copy the global object from the previous context.
  __ ld(a2, MemOperand(cp, Context::SlotOffset(Context::GLOBAL_OBJECT_INDEX)));
  __ li(a1, Operand(Smi::FromInt(0)));
  __ st(a3, MemOperand(v0, Context::SlotOffset(Context::CLOSURE_INDEX)));
  __ st(cp, MemOperand(v0, Context::SlotOffset(Context::PREVIOUS_INDEX)));
  __ st(a1, MemOperand(v0, Context::SlotOffset(Context::EXTENSION_INDEX)));
  __ st(a2, MemOperand(v0, Context::SlotOffset(Context::GLOBAL_OBJECT_INDEX)));

  // Initialize the rest of the slots to undefined.
  __ LoadRoot(a1, Heap::kUndefinedValueRootIndex);
  for (int i = Context::MIN_CONTEXT_SLOTS; i < length; i++) {
    __ st(a1, MemOperand(v0, Context::SlotOffset(i)));
  }

  // Remove the on-stack argument and return.
  __ move(cp, v0);
  __ DropAndRet(1);

  // Need to collect. Call into runtime system.
  __ bind(&gc);
  __ TailCallRuntime(Runtime::kNewFunctionContext, 1, 1);
}


void FastNewBlockContextStub::Generate(MacroAssembler* masm) {
  // Stack layout on entry:
  //
  // [sp]: function.
  // [sp + kPointerSize]: serialized scope info

  // Try to allocate the context in new space.
  Label gc;
  int length = slots_ + Context::MIN_CONTEXT_SLOTS;
  __ Allocate(FixedArray::SizeFor(length), v0, a1, a2, &gc, TAG_OBJECT);

  // Load the function from the stack.
  __ ld(a3, MemOperand(sp, 0));

  // Load the serialized scope info from the stack.
  __ ld(a1, MemOperand(sp, 1 * kPointerSize));

  // Set up the object header.
  __ LoadRoot(a2, Heap::kBlockContextMapRootIndex);
  __ st(a2, FieldMemOperand(v0, HeapObject::kMapOffset));
  __ li(a2, Operand(Smi::FromInt(length)));
  __ st(a2, FieldMemOperand(v0, FixedArray::kLengthOffset));

  // If this block context is nested in the native context we get a smi
  // sentinel instead of a function. The block context should get the
  // canonical empty function of the native context as its closure which
  // we still have to look up.
  Label after_sentinel;
  __ JumpIfNotSmi(a3, &after_sentinel);
  if (FLAG_debug_code) {
    const char* message = "Expected 0 as a Smi sentinel";
    __ Assert(eq, message, a3, Operand(zero));
  }
  __ ld(a3, GlobalObjectOperand());
  __ ld(a3, FieldMemOperand(a3, GlobalObject::kNativeContextOffset));
  __ ld(a3, ContextOperand(a3, Context::CLOSURE_INDEX));
  __ bind(&after_sentinel);

  // Set up the fixed slots, copy the global object from the previous context.
  __ ld(a2, ContextOperand(cp, Context::GLOBAL_OBJECT_INDEX));
  __ st(a3, ContextOperand(v0, Context::CLOSURE_INDEX));
  __ st(cp, ContextOperand(v0, Context::PREVIOUS_INDEX));
  __ st(a1, ContextOperand(v0, Context::EXTENSION_INDEX));
  __ st(a2, ContextOperand(v0, Context::GLOBAL_OBJECT_INDEX));

  // Initialize the rest of the slots to the hole value.
  __ LoadRoot(a1, Heap::kTheHoleValueRootIndex);
  for (int i = 0; i < slots_; i++) {
    __ st(a1, ContextOperand(v0, i + Context::MIN_CONTEXT_SLOTS));
  }

  // Remove the on-stack argument and return.
  __ move(cp, v0);
  __ DropAndRet(2);

  // Need to collect. Call into runtime system.
  __ bind(&gc);
  __ TailCallRuntime(Runtime::kPushBlockContext, 2, 1);
}


// Takes a Smi and converts to an IEEE 64 bit floating point value in two
// registers.  The format is 1 sign bit, 11 exponent bits (biased 1023) and
// 52 fraction bits (20 in the first word, 32 in the second).  Zeros is a
// scratch register.  Destroys the source register.  No GC occurs during this
// stub so you don't have to set up the frame.
class ConvertToDoubleStub : public PlatformCodeStub {
 public:
  ConvertToDoubleStub(Register result_reg,
                      Register source_reg,
                      Register scratch_reg1,
                      Register scratch_reg2,
                      bool is_signed = true)
      : result_(result_reg),
        source_(source_reg),
        scratch1_(scratch_reg1),
        scratch2_(scratch_reg2),
        is_signed_(is_signed) { }

 private:
  Register result_;
  Register source_;
  Register scratch1_;
  Register scratch2_;
  bool is_signed_;

  Major MajorKey() { return ConvertToDouble; }
  int MinorKey() {
    // Encode the parameters in a unique 16 bit value.
    return result_.code() +
           (source_.code() << 5) +
           (scratch1_.code() << 10) + 
           (scratch2_.code() << 15);
  }

  void Generate(MacroAssembler* masm);
};


void ConvertToDoubleStub::Generate(MacroAssembler* masm) {
  // Convert from Smi to integer.
  if (is_signed_)
    __ sra(source_, source_, kSmiTagSize + kSmiShiftSize);
  else
    __ srl(source_, source_, kSmiTagSize + kSmiShiftSize);

  // {
  __ cmpltsi(result_, source_, 0);
  __ sub(scratch1_, zero, source_);
  // }
  // {
  __ moveli(scratch2_, 539);
  __ movn(source_, scratch1_, result_);
  // }
  // {
  __ sll(scratch2_, scratch2_, 8);
  __ sll(scratch1_, source_, 4);
  // }
  __ bfins(scratch2_, result_, 20, 20);
  __ fdouble_pack1(source_, scratch1_, scratch2_);
  __ fdouble_pack2(source_, scratch1_, zero);
  __ move(result_, source_);
  __ Ret();
}


void FloatingPointHelper::LoadSmis(MacroAssembler* masm,
                                   FloatingPointHelper::Destination destination,
                                   Register scratch1,
                                   Register scratch2,
                                   Register scratch3) {
  ASSERT(destination == kCoreRegisters);
  // Write Smi from a0 to a3 and a2 in double format.
  __ move(scratch3, a0);
  ConvertToDoubleStub stub1(a3, scratch3, scratch1, scratch2);
  __ push(ra);
  __ Call(stub1.GetCode(masm->isolate()));
  // Write Smi from a1 to a1 and a0 in double format.
  __ move(scratch3, a1);
  ConvertToDoubleStub stub2(a2, scratch3, scratch1, scratch2);
  __ Call(stub2.GetCode(masm->isolate()));
  __ pop(ra);
}


void FloatingPointHelper::LoadNumber(MacroAssembler* masm,
                                     Destination destination,
                                     Register object,
                                     Register dst,
                                     Register heap_number_map,
                                     Register scratch1,
                                     Register scratch2,
                                     Register scratch3,
                                     Label* not_number) {
  __ AssertRootValue(heap_number_map,
                     Heap::kHeapNumberMapRootIndex,
                     "HeapNumberMap register clobbered.");

  Label is_smi, done;

  // Smi-check
  __ UntagAndJumpIfSmi(scratch1, object, &is_smi);
  // Heap number check
  __ JumpIfNotHeapNumber(object, heap_number_map, scratch1, not_number);

  // Handle loading a double from a heap number.
  ASSERT(destination == kCoreRegisters);
  // Load the double from heap number to dst in double format.
  __ ld(dst, FieldMemOperand(object, HeapNumber::kValueOffset));
  __ Branch(&done);

  // Handle loading a double from a smi.
  __ bind(&is_smi);

  ASSERT(destination == kCoreRegisters);
  // Write smi to dst double format.
  __ move(scratch1, object);
  ConvertToDoubleStub stub(dst, scratch1, scratch2, scratch3);
  __ push(ra);
  __ Call(stub.GetCode(masm->isolate()));
  __ pop(ra);

  __ bind(&done);
}


void FloatingPointHelper::ConvertNumberToInt32(MacroAssembler* masm,
                                               Register object,
                                               Register dst,
                                               Register heap_number_map,
                                               Register scratch1,
                                               Register scratch2,
                                               Register scratch3,
                                               Register scratch4,
                                               Label* not_number) {
  __ AssertRootValue(heap_number_map,
                     Heap::kHeapNumberMapRootIndex,
                     "HeapNumberMap register clobbered.");
  Label done;
  Label not_in_int32_range;

  __ UntagAndJumpIfSmi(dst, object, &done);
  __ ld(scratch1, FieldMemOperand(object, HeapNumber::kMapOffset));
  __ Branch(not_number, ne, scratch1, Operand(heap_number_map));
  __ ConvertToInt32(object,
                    dst,
                    scratch1,
                    scratch2,
                    scratch3,
                    scratch4,
		    &not_in_int32_range);

  __ jmp(&done);

  __ bind(&not_in_int32_range);
  __ ld(scratch1, FieldMemOperand(object, HeapNumber::kValueOffset));

  __ EmitOutOfInt32RangeTruncate(dst,
                                 scratch1,
                                 scratch2);
  __ bind(&done);
}


void FloatingPointHelper::ConvertIntToDouble(MacroAssembler* masm,
                                             Register int_scratch,
                                             Destination destination,
                                             Register dst,
                                             Register scratch2,
                                             Register scratch3) {
  ASSERT(!int_scratch.is(scratch2));
  ASSERT(!int_scratch.is(scratch3));
  ASSERT(!int_scratch.is(dst));

  // {
  __ cmpltsi(dst, int_scratch, 0);
  __ sub(scratch2, zero, int_scratch);
  // }
  // {
  __ moveli(scratch3, 539);
  __ movn(int_scratch, scratch2, dst);
  // }
  // {
  __ sll(scratch3, scratch3, 8);
  __ sll(scratch2, int_scratch, 4);
  // }
  __ bfins(scratch3, dst, 20, 20);
  __ fdouble_pack1(dst, scratch2, scratch3);
  __ fdouble_pack2(dst, scratch2, zero);
}

void FloatingPointHelper::ConvertUIntToDouble(MacroAssembler* masm,
                                             Register input,
                                             Destination destination,
                                             Register dst,
                                             Register scratch) {
  ASSERT(!input.is(scratch));
  ASSERT(!input.is(dst));

  // {
  __ moveli(dst, 539);
  __ moveli(scratch, 0);
  // }
  // {
  __ bfins(scratch, input, 4, 35);
  __ sll(input, dst, 8);
  // }
  __ fdouble_pack1(dst, scratch, input);
  __ fdouble_pack2(dst, scratch, zero);
}

void FloatingPointHelper::LoadNumberAsInt32Double(MacroAssembler* masm,
                                                  Register object,
                                                  Destination destination,
                                                  Register dst,
                                                  Register heap_number_map,
                                                  Register scratch1,
                                                  Register scratch2,
                                                  Register scratch3,
                                                  Label* not_int32) {
  ASSERT(!scratch1.is(object) && !scratch2.is(object) && !scratch3.is(object));
  ASSERT(!scratch1.is(scratch2) && !scratch1.is(scratch3));
  ASSERT(!scratch2.is(scratch3));
  ASSERT(!heap_number_map.is(object) &&
         !heap_number_map.is(scratch1) &&
         !heap_number_map.is(scratch2) &&
         !heap_number_map.is(scratch3));

  Label done, obj_is_not_smi;

  __ JumpIfNotSmi(object, &obj_is_not_smi);
  __ SmiUntag(scratch1, object);
  ConvertIntToDouble(masm, scratch1, destination, dst, scratch2, scratch3);
  __ Branch(&done);

  __ bind(&obj_is_not_smi);
  __ AssertRootValue(heap_number_map,
                     Heap::kHeapNumberMapRootIndex,
                     "HeapNumberMap register clobbered.");
  __ JumpIfNotHeapNumber(object, heap_number_map, scratch1, not_int32);

  // Load the double value in the destination registers.
  bool save_registers = object.is(dst);
  if (save_registers) {
    // Save both output registers, because the other one probably holds
    // an important value too.
    __ push(dst);
  }

  __ ld(dst, FieldMemOperand(object, HeapNumber::kValueOffset));
#if 0
  if (object.is(dst)) {
    __ lw(dst_exponent, FieldMemOperand(object, HeapNumber::kExponentOffset));
    __ lw(dst_mantissa, FieldMemOperand(object, HeapNumber::kMantissaOffset));
  } else {
    __ lw(dst_mantissa, FieldMemOperand(object, HeapNumber::kMantissaOffset));
    __ lw(dst_exponent, FieldMemOperand(object, HeapNumber::kExponentOffset));
  }
#endif

  // Check for 0 and -0.
  Label zero_label;
  __ And(scratch1, dst, Operand(~0x8000000000000000L));
  __ Branch(&zero_label, eq, scratch1, Operand(zero));

  // Check that the value can be exactly represented by a 32-bit integer.
  // Jump to not_int32 if that's not the case.
  Label restore_input_and_miss;
  DoubleIs32BitInteger(masm, dst, scratch1, scratch2, &restore_input_and_miss);

  // dst_* were trashed. Reload the double value.
  if (save_registers) {
    __ pop(dst);
  }

  __ ld(dst, FieldMemOperand(object, HeapNumber::kValueOffset));

#if 0
  if (object.is(dst_mantissa)) {
  __ lw(dst_exponent, FieldMemOperand(object, HeapNumber::kExponentOffset));
    __ lw(dst_mantissa, FieldMemOperand(object, HeapNumber::kMantissaOffset));
  } else {
    __ lw(dst_mantissa, FieldMemOperand(object, HeapNumber::kMantissaOffset));
    __ lw(dst_exponent, FieldMemOperand(object, HeapNumber::kExponentOffset));
  }
#endif

  __ Branch(&done);

  __ bind(&restore_input_and_miss);
  if (save_registers) {
    __ pop(dst);
  }
  __ Branch(not_int32);

  __ bind(&zero_label);
  if (save_registers) {
    __ Drop(1);
  }

  __ bind(&done);
}

void FloatingPointHelper::DoubleIs32BitInteger(MacroAssembler* masm,
                                               Register src,
                                               Register dst,
                                               Register scratch,
                                               Label* not_int32) {
  // Get exponent alone in scratch.
  __ bfextu(scratch, src, 52, 62);

  // Substract the bias from the exponent.
  __ Subu(scratch, scratch, Operand(HeapNumber::kExponentBias));

  // src1: higher (exponent) part of the double value.
  // src2: lower (mantissa) part of the double value.
  // scratch: unbiased exponent.

  // Fast cases. Check for obvious non 32-bit integer values.
  // Negative exponent cannot yield 32-bit integers.
  __ Branch(not_int32, lt, scratch, Operand(zero));
  // Exponent greater than 31 cannot yield 32-bit integers.
  // Also, a positive value with an exponent equal to 31 is outside of the
  // signed 32-bit integer range.
  // Another way to put it is that if (exponent - signbit) > 30 then the
  // number cannot be represented as an int32.
  Register tmp = dst;
  __ srl(at, src, 63);
  __ sub(tmp, scratch, at);
  __ Branch(not_int32, gt, tmp, Operand(30));
  // - Bits [21:0] in the mantissa are not null.
  __ And(tmp, src, 0x3FFFFF);
  __ Branch(not_int32, ne, tmp, Operand(zero));

  // Otherwise the exponent needs to be big enough to shift left all the
  // non zero bits left. So we need the (30 - exponent) last bits of the
  // 31 higher bits of the mantissa to be null.
  // Because bits [21:0] are null, we can check instead that the
  // (32 - exponent) last bits of the 32 higher bits of the mantissa are null.

  // Get the 32 higher bits of the mantissa in dst.
  __ sll(dst, src, HeapNumber::kNonMantissaBitsInTopWord);
  __ srl(dst, dst, 32);

  // Create the mask and test the lower bits (of the higher bits).
  __ li(at, 32);
  __ sub(scratch, at, scratch);
  __ li(src, 1);
  __ sll(src, src, scratch);
  __ Subu(src, src, Operand(1));
  __ And(src, dst, src);
  __ Branch(not_int32, ne, src, Operand(zero));
}

void FloatingPointHelper::LoadNumberAsInt32(MacroAssembler* masm,
                                            Register object,
                                            Register dst,
                                            Register heap_number_map,
                                            Register scratch1,
                                            Register scratch2,
                                            Register scratch3,
                                            Label* not_int32) {
  ASSERT(!dst.is(object));
  ASSERT(!scratch1.is(object) && !scratch2.is(object) && !scratch3.is(object));
  ASSERT(!scratch1.is(scratch2) &&
         !scratch1.is(scratch3) &&
         !scratch2.is(scratch3));

  Label done, maybe_undefined;

  __ UntagAndJumpIfSmi(dst, object, &done);

  __ AssertRootValue(heap_number_map,
                     Heap::kHeapNumberMapRootIndex,
                     "HeapNumberMap register clobbered.");

  __ JumpIfNotHeapNumber(object, heap_number_map, scratch1, &maybe_undefined);

  // Load the double value in the destination registers.
  __ ld(scratch1, FieldMemOperand(object, HeapNumber::kValueOffset));

  // Check for 0 and -0.
  __ And(dst, scratch1, Operand(~0x8000000000000000L));
  __ Branch(&done, eq, dst, Operand(zero));

  DoubleIs32BitInteger(masm, scratch1, dst, scratch3, not_int32);

  __ li(scratch1, 1);
  // Registers state after DoubleIs32BitInteger.
  // dst: mantissa[51:20].
  // scratch2: 1

  // Shift back the higher bits of the mantissa.
  __ srl(dst, dst, scratch3);
  // Set the implicit first bit.
  __ li(at, 32);
  __ sub(scratch3, at, scratch3);
  __ sll(scratch1, scratch1, scratch3);
  __ Or(dst, dst, scratch1);
  // Set the sign.
  __ ld(scratch1, FieldMemOperand(object, HeapNumber::kValueOffset));
  __ And(scratch1, scratch1, Operand(0x8000000000000000L));
  Label skip_sub;
  __ Branch(&skip_sub, ge, scratch1, Operand(zero));
  __ Subu(dst, zero, dst);
  __ bind(&skip_sub);

  __ Branch(&done);

  __ bind(&maybe_undefined);
  __ LoadRoot(at, Heap::kUndefinedValueRootIndex);
  __ Branch(not_int32, ne, object, Operand(at));
  // |undefined| is truncated to 0.
  __ li(dst, Operand(Smi::FromInt(0)));
  // Fall through.

  __ bind(&done);

}


void FloatingPointHelper::CallCCodeForDoubleOperation(
    MacroAssembler* masm,
    Token::Value op,
    Register heap_number_result,
    Register scratch) {
  // Using core registers:
  //
  // Incoming:
  // a2: Left value
  // a3: Right value
  //
  // we need to move them to a0/a1.

  // Assert that heap_number_result is saved.
  // We currently always use s0 to pass it.
  ASSERT(heap_number_result.is(s0));

  __ move(a0, a2);
  __ move(a1, a3);

  // Push the current return address before the C call.
  __ push(ra);
  __ PrepareCallCFunction(2, scratch);
  {
    AllowExternalCallThatCantCauseGC scope(masm);
    __ CallCFunction(
        ExternalReference::double_fp_operation(op, masm->isolate()), 2);
  }

  // Double returned in registers v0 and v1.
  __ st(v0, FieldMemOperand(heap_number_result, HeapNumber::kValueOffset));

  // Place heap_number_result in v0 and return to the pushed return address.
  __ pop(ra);
  __ move(v0, heap_number_result);
  __ Ret();
}

// Handle the case where the lhs and rhs are the same object.
// Equality is almost reflexive (everything but NaN), so this is a test
// for "identity and not NaN".
static void EmitIdenticalObjectComparison(MacroAssembler* masm,
                                          Label* slow,
                                          Condition cc) {
  Label not_identical;
  Label heap_number, return_equal;
  Register exp_mask_reg = t5;

  __ Branch(&not_identical, ne, a0, Operand(a1));

  __ li(exp_mask_reg, Operand(0x7FF0000000000000L));

  // Test for NaN. Sadly, we can't just compare to factory->nan_value(),
  // so we do the second best thing - test it ourselves.
  // They are both equal and they are not both Smis so both of them are not
  // Smis. If it's not a heap number, then return equal.
  if (cc == less || cc == greater) {
    __ GetObjectType(a0, t4, t4);
    __ Branch(slow, greater, t4, Operand(FIRST_SPEC_OBJECT_TYPE));
  } else {
    __ GetObjectType(a0, t4, t4);
    __ Branch(&heap_number, eq, t4, Operand(HEAP_NUMBER_TYPE));
    // Comparing JS objects with <=, >= is complicated.
    if (cc != eq) {
    __ Branch(slow, greater, t4, Operand(FIRST_SPEC_OBJECT_TYPE));
      // Normally here we fall through to return_equal, but undefined is
      // special: (undefined == undefined) == true, but
      // (undefined <= undefined) == false!  See ECMAScript 11.8.5.
      if (cc == less_equal || cc == greater_equal) {
        __ Branch(&return_equal, ne, t4, Operand(ODDBALL_TYPE));
        __ LoadRoot(t2, Heap::kUndefinedValueRootIndex);
        __ Branch(&return_equal, ne, a0, Operand(t2));
        if (cc == le) {
          // undefined <= undefined should fail.
          __ li(v0, Operand(GREATER));
        } else  {
          // undefined >= undefined should fail.
          __ li(v0, Operand(LESS));
        }
        __ Ret();
      }
    }
  }

  __ bind(&return_equal);

  if (cc == less) {
    __ li(v0, Operand(GREATER));  // Things aren't less than themselves.
  } else if (cc == greater) {
    __ li(v0, Operand(LESS));     // Things aren't greater than themselves.
  } else {
    __ move(v0, zero);         // Things are <=, >=, ==, === themselves.
  }
  __ Ret();

  // For less and greater we don't have to check for NaN since the result of
  // x < x is false regardless.  For the others here is some code to check
  // for NaN.
  if (cc != lt && cc != gt) {
    __ bind(&heap_number);
    // It is a heap number, so return non-equal if it's NaN and equal if it's
    // not NaN.

    // The representation of NaN values has all exponent bits (52..62) set,
    // and not all mantissa bits (0..51) clear.
    // Read top bits of double representation (second word of value).
    __ ld(t2, FieldMemOperand(a0, HeapNumber::kValueOffset));
    // Test that exponent bits are all set.
    __ And(t3, t2, Operand(exp_mask_reg));
    // If all bits not set (ne cond), then not a NaN, objects are equal.
    __ Branch(&return_equal, ne, t3, Operand(exp_mask_reg));

    // Shift out flag and all exponent bits, retaining only mantissa.
    __ sll(v0, t2, HeapNumber::kNonMantissaBitsInTopWord);
    // For equal we already have the right value in v0:  Return zero (equal)
    // if all bits in mantissa are zero (it's an Infinity) and non-zero if
    // not (it's a NaN).  For <= and >= we need to load v0 with the failing
    // value if it's a NaN.
    if (cc != eq) {
      // All-zero means Infinity means equal.
      __ Ret(eq, v0, Operand(zero));
      if (cc == le) {
        __ li(v0, Operand(GREATER));  // NaN <= NaN should fail.
      } else {
        __ li(v0, Operand(LESS));     // NaN >= NaN should fail.
      }
    }
    __ Ret();
  }
  // No fall through here.

  __ bind(&not_identical);
}


static void EmitSmiNonsmiComparison(MacroAssembler* masm,
                                    Register lhs,
                                    Register rhs,
                                    Label* both_loaded_as_doubles,
                                    Label* slow,
                                    bool strict) {
  ASSERT((lhs.is(a0) && rhs.is(a1)) ||
         (lhs.is(a1) && rhs.is(a0)));

  Label lhs_is_smi;
  __ JumpIfSmi(lhs, &lhs_is_smi);
  // Rhs is a Smi.
  // Check whether the non-smi is a heap number.
  __ GetObjectType(lhs, t4, t4);
  if (strict) {
    // If lhs was not a number and rhs was a Smi then strict equality cannot
    // succeed. Return non-equal (lhs is already not zero).
    __ move(at, r0);
    __ move(r0, lhs);
    __ Ret(ne, t4, Operand(HEAP_NUMBER_TYPE));
    __ move(r0, at);
  } else {
    // Smi compared non-strictly with a non-Smi non-heap-number. Call
    // the runtime.
    __ Branch(slow, ne, t4, Operand(HEAP_NUMBER_TYPE));
  }

#if 0
  // Rhs is a smi, lhs is a number.
  // Convert smi rhs to double.
  __ sra(at, rhs, kSmiTagSize);
  __ mtc1(at, f14);
  __ cvt_d_w(f14, f14);
  __ ldc1(f12, FieldMemOperand(lhs, HeapNumber::kValueOffset));
#else
    // Load lhs to a double in a2, a3.
    __ ld(a1, FieldMemOperand(lhs, HeapNumber::kValueOffset));

    // Write Smi from rhs to a1 and a0 in double format. t5 is scratch.
    __ move(t6, rhs);
    ConvertToDoubleStub stub1(a0, t6, t7, t8);
    __ push(ra);
    __ Call(stub1.GetCode(masm->isolate()));
    __ pop(ra);
#endif

  // We now have both loaded as doubles.
  __ jmp(both_loaded_as_doubles);

  __ bind(&lhs_is_smi);
  // Lhs is a Smi.  Check whether the non-smi is a heap number.
  __ GetObjectType(rhs, t4, t4);
  if (strict) {
    // If lhs was not a number and rhs was a Smi then strict equality cannot
    // succeed. Return non-equal.
    __ move(at, r0);
    __ li(r0, Operand(1));
    __ Ret(ne, t4, Operand(HEAP_NUMBER_TYPE));
    __ move(r0, at);
  } else {
    // Smi compared non-strictly with a non-Smi non-heap-number. Call
    // the runtime.
    __ Branch(slow, ne, t4, Operand(HEAP_NUMBER_TYPE));
  }

#if 0
  // Lhs is a smi, rhs is a number.
  // Convert smi lhs to double.
  __ sra(at, lhs, kSmiTagSize);
  __ mtc1(at, f12);
  __ cvt_d_w(f12, f12);
  __ ldc1(f14, FieldMemOperand(rhs, HeapNumber::kValueOffset));
  // Fall through to both_loaded_as_doubles.
#else
  // Convert lhs to a double format. t5 is scratch.
  __ move(t6, lhs);
  ConvertToDoubleStub stub2(a1, t6, t7, t8);
  __ push(ra);
  __ Call(stub2.GetCode(masm->isolate()));
  __ pop(ra);
  // Load rhs to a double in a1, a0.
  __ ld(a0, FieldMemOperand(rhs, HeapNumber::kValueOffset));
#endif
}


static void EmitStrictTwoHeapObjectCompare(MacroAssembler* masm,
                                           Register lhs,
                                           Register rhs) {
    // If either operand is a JS object or an oddball value, then they are
    // not equal since their pointers are different.
    // There is no test for undetectability in strict equality.
    STATIC_ASSERT(LAST_TYPE == LAST_SPEC_OBJECT_TYPE);
    Label first_non_object;
    // Get the type of the first operand into a2 and compare it with
    // FIRST_SPEC_OBJECT_TYPE.
    __ GetObjectType(lhs, a2, a2);
    __ Branch(&first_non_object, less, a2, Operand(FIRST_SPEC_OBJECT_TYPE));

    // Return non-zero.
    Label return_not_equal;
    __ bind(&return_not_equal);
    __ li(r0, Operand(1));
    __ Ret();

    __ bind(&first_non_object);
    // Check for oddballs: true, false, null, undefined.
    __ Branch(&return_not_equal, eq, a2, Operand(ODDBALL_TYPE));

    __ GetObjectType(rhs, a3, a3);
    __ Branch(&return_not_equal, greater, a3, Operand(FIRST_SPEC_OBJECT_TYPE));

    // Check for oddballs: true, false, null, undefined.
    __ Branch(&return_not_equal, eq, a3, Operand(ODDBALL_TYPE));

    // Now that we have the types we might as well check for
    // internalized-internalized.
    // Ensure that no non-strings have the internalized bit set.
    STATIC_ASSERT(LAST_TYPE < kNotStringTag + kIsInternalizedMask);
    STATIC_ASSERT(kInternalizedTag != 0);
    __ And(t2, a2, Operand(a3));
    __ And(t0, t2, Operand(kIsInternalizedMask));
    __ Branch(&return_not_equal, ne, t0, Operand(zero));
}


static void EmitCheckForTwoHeapNumbers(MacroAssembler* masm,
                                       Register lhs,
                                       Register rhs,
                                       Label* both_loaded_as_doubles,
                                       Label* not_heap_numbers,
                                       Label* slow) {
  __ GetObjectType(lhs, a3, a2);
  __ Branch(not_heap_numbers, ne, a2, Operand(HEAP_NUMBER_TYPE));
  __ ld(a2, FieldMemOperand(rhs, HeapObject::kMapOffset));
  // If first was a heap number & second wasn't, go to slow case.
  __ Branch(slow, ne, a3, Operand(a2));

  __ ld(a1, FieldMemOperand(lhs, HeapNumber::kValueOffset));
  __ ld(a0, FieldMemOperand(rhs, HeapNumber::kValueOffset));

  __ jmp(both_loaded_as_doubles);
}


// Fast negative check for internalized-to-internalized equality.
static void EmitCheckForInternalizedStringsOrObjects(MacroAssembler* masm,
                                                     Register lhs,
                                                     Register rhs,
                                                     Label* possible_strings,
                                                     Label* not_both_strings) {
  ASSERT((lhs.is(a0) && rhs.is(a1)) ||
         (lhs.is(a1) && rhs.is(a0)));

  // a2 is object type of lhs.
  // Ensure that no non-strings have the internalized bit set.
  Label object_test;
  STATIC_ASSERT(kInternalizedTag != 0);
  __ And(at, a2, Operand(kIsNotStringMask));
  __ Branch(&object_test, ne, at, Operand(zero));
  __ And(at, a2, Operand(kIsInternalizedMask));
  __ Branch(possible_strings, eq, at, Operand(zero));
  __ GetObjectType(rhs, a3, a3);
  __ Branch(not_both_strings, ge, a3, Operand(FIRST_NONSTRING_TYPE));
  __ And(at, a3, Operand(kIsInternalizedMask));
  __ Branch(possible_strings, eq, at, Operand(zero));

  // Both are internalized strings. We already checked they weren't the same
  // pointer so they are not equal.
  __ li(r0, Operand(1));   // Non-zero indicates not equal.
  __ Ret();

  __ bind(&object_test);
  __ Branch(not_both_strings, lt, a2, Operand(FIRST_SPEC_OBJECT_TYPE));
  __ GetObjectType(rhs, a2, a3);
  __ Branch(not_both_strings, lt, a3, Operand(FIRST_SPEC_OBJECT_TYPE));

  // If both objects are undetectable, they are equal.  Otherwise, they
  // are not equal, since they are different objects and an object is not
  // equal to undefined.
  __ ld(a3, FieldMemOperand(lhs, HeapObject::kMapOffset));
  __ ld1u(a2, FieldMemOperand(a2, Map::kBitFieldOffset));
  __ ld1u(a3, FieldMemOperand(a3, Map::kBitFieldOffset));
  __ and_(a0, a2, a3);
  __ And(a0, a0, Operand(1 << Map::kIsUndetectable));
  __ xori(r0, a0, 1 << Map::kIsUndetectable);
  __ Ret();
}


void NumberToStringStub::GenerateLookupNumberStringCache(MacroAssembler* masm,
                                                         Register object,
                                                         Register result,
                                                         Register scratch1,
                                                         Register scratch2,
                                                         Register scratch3,
                                                         bool object_is_smi,
                                                         Label* not_found) {
  // Use of registers. Register result is used as a temporary.
  Register number_string_cache = result;
  Register mask = scratch3;

  // Load the number string cache.
  __ LoadRoot(number_string_cache, Heap::kNumberStringCacheRootIndex);

  // Make the hash mask from the length of the number string cache. It
  // contains two elements (number and string) for each cache entry.
  __ ld(mask, FieldMemOperand(number_string_cache, FixedArray::kLengthOffset));
  // Divide length by two (length is a smi).
  __ sra(mask, mask, 32 + 1);
  __ Addu(mask, mask, -1);  // Make mask.

  // Calculate the entry in the number string cache. The hash value in the
  // number string cache for smis is just the smi value, and the hash for
  // doubles is the xor of the upper and lower words. See
  // Heap::GetNumberStringCache.
  Isolate* isolate = masm->isolate();
  Label is_smi;
  Label load_result_from_cache;
  if (!object_is_smi) {
    __ JumpIfSmi(object, &is_smi);
#if 0
    __ CheckMap(object,
                scratch1,
                Heap::kHeapNumberMapRootIndex,
                not_found,
                DONT_DO_SMI_CHECK);

    STATIC_ASSERT(8 == kDoubleSize);
    __ Addu(scratch1,
            object,
            Operand(HeapNumber::kValueOffset - kHeapObjectTag));
    __ ld(scratch2, MemOperand(scratch1, kPointerSize));
    __ ld(scratch1, MemOperand(scratch1, 0));
    __ Xor(scratch1, scratch1, Operand(scratch2));
    __ And(scratch1, scratch1, Operand(mask));

    // Calculate address of entry in string cache: each entry consists
    // of two pointer sized fields.
    __ sll(scratch1, scratch1, kPointerSizeLog2 + 1);
    __ Addu(scratch1, number_string_cache, scratch1);

    Register probe = mask;
    __ ld(probe,
           FieldMemOperand(scratch1, FixedArray::kHeaderSize));
    __ JumpIfSmi(probe, not_found);
    __ ldc1(f12, FieldMemOperand(object, HeapNumber::kValueOffset));
    __ ldc1(f14, FieldMemOperand(probe, HeapNumber::kValueOffset));
    __ BranchF(&load_result_from_cache, NULL, eq, f12, f14);
    __ Branch(not_found);
#endif
      // Note that there is no cache check for non-FPU case, even though
      // it seems there could be. May be a tiny opimization for non-FPU
      // cores.
      __ Branch(not_found);
  }

  __ bind(&is_smi);
  Register scratch = scratch1;
  __ sra(scratch, object, 32);   // Shift away the tag.
  __ And(scratch, mask, Operand(scratch));

  // Calculate address of entry in string cache: each entry consists
  // of two pointer sized fields.
  __ sll(scratch, scratch, kPointerSizeLog2 + 1);
  __ Addu(scratch, number_string_cache, scratch);

  // Check if the entry is the smi we are looking for.
  Register probe = mask;
  __ ld(probe, FieldMemOperand(scratch, FixedArray::kHeaderSize));
  __ Branch(not_found, ne, object, Operand(probe));

  // Get the result from the cache.
  __ bind(&load_result_from_cache);
  __ ld(result,
         FieldMemOperand(scratch, FixedArray::kHeaderSize + kPointerSize));

  __ IncrementCounter(isolate->counters()->number_to_string_native(),
                      1,
                      scratch1,
                      scratch2);
}


void NumberToStringStub::Generate(MacroAssembler* masm) {
  Label runtime;

  __ ld(a1, MemOperand(sp, 0));

  // Generate code to lookup number in the number string cache.
  GenerateLookupNumberStringCache(masm, a1, v0, a2, a3, t0, false, &runtime);
  __ DropAndRet(1);

  __ bind(&runtime);
  // Handle number to string in the runtime system if not found in the cache.
  __ TailCallRuntime(Runtime::kNumberToString, 1, 1);
}


static void ICCompareStub_CheckInputType(MacroAssembler* masm,
                                         Register input,
                                         Register scratch,
                                         CompareIC::State expected,
                                         Label* fail) {
  Label ok;
  if (expected == CompareIC::SMI) {
    __ JumpIfNotSmi(input, fail);
  } else if (expected == CompareIC::NUMBER) {
    __ JumpIfSmi(input, &ok);
    __ CheckMap(input, scratch, Heap::kHeapNumberMapRootIndex, fail,
                DONT_DO_SMI_CHECK);
  }
  // We could be strict about internalized/string here, but as long as
  // hydrogen doesn't care, the stub doesn't have to care either.
  __ bind(&ok);
}

void EmitNanCheck(MacroAssembler* masm, Condition cc) {
  // Lhs and rhs are already loaded to GP registers.
  __ move(t0, a0);  // a0 rhs.
  __ move(t1, a1);  // a1 lhs.

  Label one_is_nan, neither_is_nan;
  Label lhs_not_nan_exp_mask_is_loaded;

  Register exp_mask_reg = t4;
  __ li(exp_mask_reg, 0x7FF0000000000000L);
  __ and_(t5, t1, exp_mask_reg);
  __ Branch(&lhs_not_nan_exp_mask_is_loaded, ne, t5, Operand(exp_mask_reg));

  __ sll(t5, t1, HeapNumber::kNonMantissaBitsInTopWord);
  __ Branch(&one_is_nan, ne, t5, Operand(zero));

  __ li(exp_mask_reg, 0x7FF0000000000000L);
  __ bind(&lhs_not_nan_exp_mask_is_loaded);
  __ and_(t5, r0, exp_mask_reg);

  __ Branch(&neither_is_nan, ne, t5, Operand(exp_mask_reg));

  __ sll(t5, t0, HeapNumber::kNonMantissaBitsInTopWord);
  __ Branch(&one_is_nan, ne, t5, Operand(zero));

  __ Branch(&neither_is_nan);

  __ bind(&one_is_nan);
  // NaN comparisons always fail.
  // Load whatever we need in v0 to make the comparison fail.

  if (cc == lt || cc == le) {
    __ li(v0, Operand(GREATER));
  } else {
    __ li(v0, Operand(LESS));
  }
  __ Ret();

  __ bind(&neither_is_nan);
}

static void EmitTwoNonNanDoubleComparison(MacroAssembler* masm, Condition cc) {

  Label return_result_not_equal, return_result_equal;
  if (cc == eq) {
    // Doubles are not equal unless they have the same bit pattern.
    // Exception: 0 and -0.

    // Lhs and rhs are already loaded to GP registers.
    __ move(t0, a0);  // a0 rhs.
    __ move(t1, a1);  // a1 lhs.

    __ sub(v0, t0, t1);
    __ Branch(&return_result_equal, eq, v0, Operand(zero));
    // 0, -0 case.
    __ sll(t0, t0, 1);
    __ sll(t1, t1, 1);
    __ or_(t4, t0, t1);

    __ Branch(&return_result_not_equal, ne, t4, Operand(zero));

    __ bind(&return_result_equal);

    __ li(v0, Operand(EQUAL));
    __ Ret();
  }

  __ bind(&return_result_not_equal);

  __ push(ra);
  __ PrepareCallCFunction(2, t4);

  AllowExternalCallThatCantCauseGC scope(masm);
  __ CallCFunction(ExternalReference::compare_doubles(masm->isolate()), 2);
  __ pop(ra);  // Because this function returns int, result is in v0.
  __ Ret();
}

// On entry a1 and a2 are the values to be compared.
// On exit a0 is 0, positive or negative to indicate the result of
// the comparison.
void ICCompareStub::GenerateGeneric(MacroAssembler* masm) {
  Register lhs = a1;
  Register rhs = a0;
  Condition cc = GetCondition();

  Label miss;
  ICCompareStub_CheckInputType(masm, lhs, a2, left_, &miss);
  ICCompareStub_CheckInputType(masm, rhs, a3, right_, &miss);

  Label slow;  // Call builtin.
  Label not_smis, both_loaded_as_doubles;

  Label not_two_smis, smi_done;
  __ Or(a2, a1, a0);
  __ JumpIfNotSmi(a2, &not_two_smis);
  __ sra(a1, a1, 32);
  __ sra(a0, a0, 32);
  __ sub(v0, a1, a0);
  __ Ret();
  __ bind(&not_two_smis);

  // NOTICE! This code is only reached after a smi-fast-case check, so
  // it is certain that at least one operand isn't a smi.

  // Handle the case where the objects are identical.  Either returns the answer
  // or goes to slow.  Only falls through if the objects were not identical.
  EmitIdenticalObjectComparison(masm, &slow, cc);

  // If either is a Smi (we know that not both are), then they can only
  // be strictly equal if the other is a HeapNumber.
  STATIC_ASSERT(kSmiTag == 0);
  ASSERT_EQ(0, Smi::FromInt(0));
  __ And(t2, lhs, Operand(rhs));
  __ JumpIfNotSmi(t2, &not_smis, t0);
  // One operand is a smi. EmitSmiNonsmiComparison generates code that can:
  // 1) Return the answer.
  // 2) Go to slow.
  // 3) Fall through to both_loaded_as_doubles.
  // 4) Jump to rhs_not_nan.
  // In cases 3 and 4 we have found out we were dealing with a number-number
  // comparison and the numbers have been loaded into f12 and f14 as doubles,
  // or in GP registers (a0, a1, a2, a3) depending on the presence of the FPU.
  EmitSmiNonsmiComparison(masm, lhs, rhs,
                          &both_loaded_as_doubles, &slow, strict());

  __ bind(&both_loaded_as_doubles);
  // f12, f14 are the double representations of the left hand side
  // and the right hand side if we have FPU. Otherwise a2, a3 represent
  // left hand side and a0, a1 represent right hand side.

  Isolate* isolate = masm->isolate();
#if 0
  Label nan;
  __ li(t0, Operand(LESS));
  __ li(t1, Operand(GREATER));
  __ li(t2, Operand(EQUAL));

  // Check if either rhs or lhs is NaN.
  __ BranchF(NULL, &nan, eq, f12, f14);

  // Check if LESS condition is satisfied. If true, move conditionally
  // result to v0.
  __ c(OLT, D, f12, f14);
  __ Movt(v0, t0);
  // Use previous check to store conditionally to v0 oposite condition
  // (GREATER). If rhs is equal to lhs, this will be corrected in next
  // check.
  __ Movf(v0, t1);
  // Check if EQUAL condition is satisfied. If true, move conditionally
  // result to v0.
  __ c(EQ, D, f12, f14);
  __ Movt(v0, t2);

  __ Ret();

  __ bind(&nan);
  // NaN comparisons always fail.
  // Load whatever we need in v0 to make the comparison fail.
  if (cc == lt || cc == le) {
    __ li(v0, Operand(GREATER));
  } else {
    __ li(v0, Operand(LESS));
  }
  __ Ret();
#else
  // Checks for NaN in the doubles we have loaded.  Can return the answer or
  // fall through if neither is a NaN.  Also binds rhs_not_nan.
  EmitNanCheck(masm, cc);

  // Compares two doubles that are not NaNs. Returns the answer.
  // Never falls through.
  EmitTwoNonNanDoubleComparison(masm, cc);
#endif

  __ bind(&not_smis);
  // At this point we know we are dealing with two different objects,
  // and neither of them is a Smi. The objects are in lhs_ and rhs_.
  if (strict()) {
    // This returns non-equal for some object types, or falls through if it
    // was not lucky.
    EmitStrictTwoHeapObjectCompare(masm, lhs, rhs);
  }

  Label check_for_internalized_strings;
  Label flat_string_check;
  // Check for heap-number-heap-number comparison. Can jump to slow case,
  // or load both doubles and jump to the code that handles
  // that case. If the inputs are not doubles then jumps to
  // check_for_internalized_strings.
  // In this case a2 will contain the type of lhs_.
  EmitCheckForTwoHeapNumbers(masm,
                             lhs,
                             rhs,
                             &both_loaded_as_doubles,
                             &check_for_internalized_strings,
                             &flat_string_check);

  __ bind(&check_for_internalized_strings);
  if (cc == eq && !strict()) {
    // Returns an answer for two internalized strings or two
    // detectable objects.
    // Otherwise jumps to string case or not both strings case.
    // Assumes that a2 is the type of lhs_ on entry.
    EmitCheckForInternalizedStringsOrObjects(
        masm, lhs, rhs, &flat_string_check, &slow);
  }

  // Check for both being sequential ASCII strings, and inline if that is the
  // case.
  __ bind(&flat_string_check);

  __ JumpIfNonSmisNotBothSequentialAsciiStrings(lhs, rhs, a2, a3, &slow);

  __ IncrementCounter(isolate->counters()->string_compare_native(), 1, a2, a3);
  if (cc == eq) {
    StringCompareStub::GenerateFlatAsciiStringEquals(masm,
                                                     lhs,
                                                     rhs,
                                                     a2,
                                                     a3,
                                                     t0);
  } else {
    StringCompareStub::GenerateCompareFlatAsciiStrings(masm,
                                                       lhs,
                                                       rhs,
                                                       a2,
                                                       a3,
                                                       t0,
                                                       t1);
  }
  // Never falls through to here.

  __ bind(&slow);
  // Prepare for call to builtin. Push object pointers, a0 (lhs) first,
  // a1 (rhs) second.
  __ Push(lhs, rhs);
  // Figure out which native to call and setup the arguments.
  Builtins::JavaScript native;
  if (cc == eq) {
    native = strict() ? Builtins::STRICT_EQUALS : Builtins::EQUALS;
  } else {
    native = Builtins::COMPARE;
    int ncr;  // NaN compare result.
    if (cc == lt || cc == le) {
      ncr = GREATER;
    } else {
      ASSERT(cc == gt || cc == ge);  // Remaining cases.
      ncr = LESS;
    }

   __ li(a0, Operand(Smi::FromInt(ncr)));
    __ push(a0);
  }

  // Call the native; it returns -1 (less), 0 (equal), or 1 (greater)
  // tagged as a small integer.
  __ InvokeBuiltin(native, JUMP_FUNCTION);

  __ bind(&miss);
  GenerateMiss(masm);
}

// The stub expects its argument in the tos_ register and returns its result in
// it, too: zero for false, and a non-zero value for true.
void ToBooleanStub::Generate(MacroAssembler* masm) {
  Label patch;
  const Register map = t5.is(tos_) ? t3 : t5;

  // undefined -> false.
  CheckOddball(masm, UNDEFINED, Heap::kUndefinedValueRootIndex, false);

  // Boolean -> its value.
  CheckOddball(masm, BOOLEAN, Heap::kFalseValueRootIndex, false);
  CheckOddball(masm, BOOLEAN, Heap::kTrueValueRootIndex, true);

  // 'null' -> false.
  CheckOddball(masm, NULL_TYPE, Heap::kNullValueRootIndex, false);

  if (types_.Contains(SMI)) {
    // Smis: 0 -> false, all other -> true
    __ And(at, tos_, kSmiTagMask);
    // tos_ contains the correct return value already
    __ Ret(eq, at, Operand(zero));
  } else if (types_.NeedsMap()) {
    // If we need a map later and have a Smi -> patch.
    __ JumpIfSmi(tos_, &patch);
  }

  if (types_.NeedsMap()) {
    __ ld(map, FieldMemOperand(tos_, HeapObject::kMapOffset));

    if (types_.CanBeUndetectable()) {
      __ ld1u(at2, FieldMemOperand(map, Map::kBitFieldOffset));
      __ And(at, at2, Operand(1 << Map::kIsUndetectable));
      // Undetectable -> false.
      __ movn(tos_, zero, at);
      __ Ret(ne, at, Operand(zero));
    }
  }

  if (types_.Contains(SPEC_OBJECT)) {
    // Spec object -> true.
    __ ld1u(at, FieldMemOperand(map, Map::kInstanceTypeOffset));
    // tos_ contains the correct non-zero return value already.
    __ Ret(ge, at, Operand(FIRST_SPEC_OBJECT_TYPE));
  }

  if (types_.Contains(STRING)) {
    // String value -> false iff empty.
    __ ld1u(at, FieldMemOperand(map, Map::kInstanceTypeOffset));
    Label skip;
    __ Branch(&skip, ge, at, Operand(FIRST_NONSTRING_TYPE));
    __ ld(tos_, FieldMemOperand(tos_, String::kLengthOffset));
    __ Ret();  // the string length is OK as the return value
    __ bind(&skip);
  }

  if (types_.Contains(HEAP_NUMBER)) {
    // Heap number -> false iff +0, -0, or NaN.
    Label not_heap_number;
    __ LoadRoot(at, Heap::kHeapNumberMapRootIndex);
    __ Branch(&not_heap_number, ne, map, Operand(at));
    Label zero_or_nan, number;

    __ ld(at, FieldMemOperand(tos_, HeapNumber::kValueOffset));
    __ li(at2, Operand(0x7FF0000000000000L));
    __ and_(t6, at, at2);
    __ Branch(&zero_or_nan, eq, t6, Operand(zero));

    // at is still with HeapNumber.
    // at2 is still with 0x7FF0000000000000L.
    __ Branch(&zero_or_nan, gt, at, Operand(at2));

    __ Branch(&number);
    // "tos_" is a register, and contains a non zero value by default.
    // Hence we only need to overwrite "tos_" with zero to return false for
    // FP_ZERO or FP_NAN cases. Otherwise, by default it returns true.
    __ bind(&zero_or_nan);
    __ move(tos_, zero);
    __ bind(&number);
    __ Ret();
    __ bind(&not_heap_number);
  }

  __ bind(&patch);
  GenerateTypeTransition(masm);
}


void ToBooleanStub::CheckOddball(MacroAssembler* masm,
                                 Type type,
                                 Heap::RootListIndex value,
                                 bool result) {
  if (types_.Contains(type)) {
    // If we see an expected oddball, return its ToBoolean value tos_.
    __ LoadRoot(at, value);
    __ Subu(at, at, tos_);  // This is a check for equality for the movz below.
    // The value of a root is never NULL, so we can avoid loading a non-null
    // value into tos_ when we want to return 'true'.
    if (!result) {
      __ movz(tos_, zero, at);
    }
    __ Ret(eq, at, Operand(zero));
  }
}


void ToBooleanStub::GenerateTypeTransition(MacroAssembler* masm) {
  __ Move(a3, tos_);
  __ li(a2, Operand(Smi::FromInt(tos_.code())));
  __ li(a1, Operand(Smi::FromInt(types_.ToByte())));
  __ Push(a3, a2, a1);
  // Patch the caller to an appropriate specialized stub and return the
  // operation result to the caller of the stub.
  __ TailCallExternalReference(
      ExternalReference(IC_Utility(IC::kToBoolean_Patch), masm->isolate()),
      3,
      1);
}


void StoreBufferOverflowStub::Generate(MacroAssembler* masm) {
  // We don't allow a GC during a store buffer overflow so there is no need to
  // store the registers in any particular way, but we do have to store and
  // restore them.
  __ MultiPush(kJSCallerSaved | lr.bit());
  const int argument_count = 1;
  const Register scratch = r1;

  AllowExternalCallThatCantCauseGC scope(masm);
  __ PrepareCallCFunction(argument_count, scratch);
  __ li(r0, Operand(ExternalReference::isolate_address(masm->isolate())));
  __ CallCFunction(
      ExternalReference::store_buffer_overflow_function(masm->isolate()),
      argument_count);
  __ MultiPop(kJSCallerSaved | lr.bit());

  __ Ret();
}


void UnaryOpStub::PrintName(StringStream* stream) {
  const char* op_name = Token::Name(op_);
  const char* overwrite_name = NULL;  // Make g++ happy.
  switch (mode_) {
    case UNARY_NO_OVERWRITE: overwrite_name = "Alloc"; break;
    case UNARY_OVERWRITE: overwrite_name = "Overwrite"; break;
  }
  stream->Add("UnaryOpStub_%s_%s_%s",
              op_name,
              overwrite_name,
              UnaryOpIC::GetName(operand_type_));
}


// TODO(svenpanne): Use virtual functions instead of switch.
void UnaryOpStub::Generate(MacroAssembler* masm) {
  switch (operand_type_) {
    case UnaryOpIC::UNINITIALIZED:
      GenerateTypeTransition(masm);
      break;
    case UnaryOpIC::SMI:
      GenerateSmiStub(masm);
      break;
    case UnaryOpIC::NUMBER:
      GenerateNumberStub(masm);
      break;
    case UnaryOpIC::GENERIC:
      GenerateGenericStub(masm);
      break;
  }
}


void UnaryOpStub::GenerateTypeTransition(MacroAssembler* masm) {
  // Argument is in a0 and v0 at this point, so we can overwrite a0.
  __ move(a3, a0);
  __ li(a2, Operand(Smi::FromInt(op_)));
  __ li(a1, Operand(Smi::FromInt(mode_)));
  __ li(a0, Operand(Smi::FromInt(operand_type_)));
  __ Push(a3, a2, a1, a0);

  __ TailCallExternalReference(
      ExternalReference(IC_Utility(IC::kUnaryOp_Patch), masm->isolate()), 4, 1);
}


// TODO(svenpanne): Use virtual functions instead of switch.
void UnaryOpStub::GenerateSmiStub(MacroAssembler* masm) {
  switch (op_) {
    case Token::SUB:
      GenerateSmiStubSub(masm);
      break;
    case Token::BIT_NOT:
      GenerateSmiStubBitNot(masm);
      break;
    default:
      UNREACHABLE();
  }
}


void UnaryOpStub::GenerateSmiStubSub(MacroAssembler* masm) {
  Label non_smi, slow;
  GenerateSmiCodeSub(masm, &non_smi, &slow);
  __ bind(&non_smi);
  __ bind(&slow);
  GenerateTypeTransition(masm);
}


void UnaryOpStub::GenerateSmiStubBitNot(MacroAssembler* masm) {
  Label non_smi;
  GenerateSmiCodeBitNot(masm, &non_smi);
  __ bind(&non_smi);
  GenerateTypeTransition(masm);
}


void UnaryOpStub::GenerateSmiCodeSub(MacroAssembler* masm,
                                     Label* non_smi,
                                     Label* slow) {
  __ JumpIfNotSmi(a0, non_smi);

  // The result of negating zero or the smallest negative smi is not a smi.
  __ And(t0, a0, Operand(~0x8000000000000000L));
  __ Branch(slow, eq, t0, Operand(zero));

  // Return '0 - value'.
  __ sub(v0, zero, a0);
  __ Ret();
}


void UnaryOpStub::GenerateSmiCodeBitNot(MacroAssembler* masm,
                                        Label* non_smi) {
  __ JumpIfNotSmi(a0, non_smi);

  // Flip bits and revert inverted smi-tag.
  __ Neg(v0, a0);
  __ And(v0, v0, Operand(0xFFFFFFFF00000000L));
  __ Ret();
}

// TODO(svenpanne): Use virtual functions instead of switch.
void UnaryOpStub::GenerateNumberStub(MacroAssembler* masm) {
  switch (op_) {
    case Token::SUB:
      GenerateNumberStubSub(masm);
      break;
    case Token::BIT_NOT:
      GenerateNumberStubBitNot(masm);
      break;
    default:
      UNREACHABLE();
  }
}


void UnaryOpStub::GenerateNumberStubSub(MacroAssembler* masm) {
  Label non_smi, slow, call_builtin;
  GenerateSmiCodeSub(masm, &non_smi, &call_builtin);
  __ bind(&non_smi);
  GenerateHeapNumberCodeSub(masm, &slow);
  __ bind(&slow);
  GenerateTypeTransition(masm);
  __ bind(&call_builtin);
  GenerateGenericCodeFallback(masm);
}


void UnaryOpStub::GenerateNumberStubBitNot(MacroAssembler* masm) {
  Label non_smi, slow;
  GenerateSmiCodeBitNot(masm, &non_smi);
  __ bind(&non_smi);
  GenerateHeapNumberCodeBitNot(masm, &slow);
  __ bind(&slow);
  GenerateTypeTransition(masm);
}


void UnaryOpStub::GenerateHeapNumberCodeSub(MacroAssembler* masm,
                                            Label* slow) {
  EmitCheckForHeapNumber(masm, a0, a1, t2, slow);
  // a0 is a heap number.  Get a new heap number in a1.
  if (mode_ == UNARY_OVERWRITE) {
    __ ld(a2, FieldMemOperand(a0, HeapNumber::kValueOffset));
    __ Xor(a2, a2, Operand(0x8000000000000000L));  // Flip sign.
    __ st(a2, FieldMemOperand(a0, HeapNumber::kValueOffset));
  } else {
    Label slow_allocate_heapnumber, heapnumber_allocated;
    __ AllocateHeapNumber(a1, a2, a3, t2, &slow_allocate_heapnumber);
    __ jmp(&heapnumber_allocated);

    __ bind(&slow_allocate_heapnumber);
    {
      FrameScope scope(masm, StackFrame::INTERNAL);
      __ push(a0);
      __ CallRuntime(Runtime::kNumberAlloc, 0);
      __ move(a1, v0);
      __ pop(a0);
    }

    __ bind(&heapnumber_allocated);
    __ ld(a2, FieldMemOperand(a0, HeapNumber::kValueOffset));
    __ Xor(a2, a2, Operand(0x8000000000000000L));  // Flip sign.
    __ st(a2, FieldMemOperand(a1, HeapNumber::kValueOffset));
    __ move(v0, a1);
  }
  __ Ret();
}


void UnaryOpStub::GenerateHeapNumberCodeBitNot( MacroAssembler* masm,
    Label* slow) {
  Label impossible;

  EmitCheckForHeapNumber(masm, a0, a1, t2, slow);
  // Convert the heap number in a0 to an untagged integer in a1.
  __ ConvertToInt32(a0, a1, a2, a3, r4, r5, slow);

  __ Neg(a1, a1);

  // Tag the result as a smi and we're done.
  __ SmiTag(v0, a1);
  __ Ret();
}


// TODO(svenpanne): Use virtual functions instead of switch.
void UnaryOpStub::GenerateGenericStub(MacroAssembler* masm) {
  switch (op_) {
    case Token::SUB:
      GenerateGenericStubSub(masm);
      break;
    case Token::BIT_NOT:
      GenerateGenericStubBitNot(masm);
      break;
    default:
      UNREACHABLE();
  }
}


void UnaryOpStub::GenerateGenericStubSub(MacroAssembler* masm) {
  Label non_smi, slow;
  GenerateSmiCodeSub(masm, &non_smi, &slow);
  __ bind(&non_smi);
  GenerateHeapNumberCodeSub(masm, &slow);
  __ bind(&slow);
  GenerateGenericCodeFallback(masm);
}


void UnaryOpStub::GenerateGenericStubBitNot(MacroAssembler* masm) {
  Label non_smi, slow;
  GenerateSmiCodeBitNot(masm, &non_smi);
  __ bind(&non_smi);
  GenerateHeapNumberCodeBitNot(masm, &slow);
  __ bind(&slow);
  GenerateGenericCodeFallback(masm);
}


void UnaryOpStub::GenerateGenericCodeFallback(
    MacroAssembler* masm) {
  // Handle the slow case by jumping to the JavaScript builtin.
  __ push(a0);
  switch (op_) {
    case Token::SUB:
      __ InvokeBuiltin(Builtins::UNARY_MINUS, JUMP_FUNCTION);
      break;
    case Token::BIT_NOT:
      __ InvokeBuiltin(Builtins::BIT_NOT, JUMP_FUNCTION);
      break;
    default:
      UNREACHABLE();
  }
}


void BinaryOpStub::Initialize() {
  platform_specific_bit_ = true;  // FPU is a base requirement for V8.
}


void BinaryOpStub::GenerateTypeTransition(MacroAssembler* masm) {
  Label get_result;

  __ Push(a1, a0);

  __ li(a2, Operand(Smi::FromInt(MinorKey())));
  __ push(a2);

  __ TailCallExternalReference(
      ExternalReference(IC_Utility(IC::kBinaryOp_Patch),
                        masm->isolate()),
      3,
      1);
}


void BinaryOpStub::GenerateTypeTransitionWithSavedArgs(
    MacroAssembler* masm) {
  UNREACHABLE();
}


void BinaryOpStub_GenerateSmiSmiOperation(MacroAssembler* masm,
                                          Token::Value op) {
  Register left = a1;
  Register right = a0;

  Register scratch1 = t0;
  Register scratch2 = t1;
  Register scratch3 = t2;

  ASSERT(right.is(a0));
  STATIC_ASSERT(kSmiTag == 0);

  __ move(t3, v0);
  Label not_smi_result;
  switch (op) {
    case Token::ADD:
      __ AdduAndCheckForOverflow(v0, left, right, scratch1);
      __ RetOnNoOverflow(scratch1);
      // No need to revert anything - right and left are intact.
      break;
    case Token::SUB:
      __ SubuAndCheckForOverflow(v0, left, right, scratch1);
      __ RetOnNoOverflow(scratch1);
      // No need to revert anything - right and left are intact.
      break;
    case Token::MUL: {
      __ mul_hs_hs(scratch1, left, right);
      // Check for overflowing the smi range - no overflow if higher 33 bits of
      // the result are identical.
      __ sra(scratch2, scratch1, 32);
      __ bfexts(scratch3, scratch1, 31, 31); // now 0 or -1
      //      __ sra(scratch3, scratch1, 30);
      __ Branch(&not_smi_result, ne, scratch3, Operand(scratch2));
      __ sll(scratch1, scratch1, 32); // Convert to Smi
      // Go slow on zero result to handle -0.
      __ move(v0, scratch1);
      __ Ret(ne, v0, Operand(zero));
      __ move(v0, t3);
      // We need -0 if we were multiplying a negative number with 0 to get 0.
      // We know one of them was zero.
      __ Addu(scratch2, right, left);
      Label skip;
      // ARM uses the 'pl' condition, which is 'ge'.
      // Negating it results in 'lt'.
      __ Branch(&skip, lt, scratch2, Operand(zero));
      ASSERT(Smi::FromInt(0) == 0);
      __ move(v0, zero);  // Return smi 0 if the non-zero one was positive.
      __ Ret();
      __ bind(&skip);
      // We fall through here if we multiplied a negative number with 0, because
      // that would mean we should produce -0.
      }
      break;
      // For DIV/MOD, call C function, not JIT support for TileGX.
    case Token::DIV:
    case Token::MOD:
      break;
    case Token::BIT_OR:
      __ or_(v0, left, right);
      __ Ret();
      break;
    case Token::BIT_AND:
      __ and_(v0, left, right);
      __ Ret();
      break;
    case Token::BIT_XOR:
      __ xor_(v0, left, right);
      __ Ret();
      break;
    case Token::SAR:
      __ GetLeastBitsFromSmi(scratch1, right, 5);
      __ sra(scratch1, left, scratch1);
      // Smi tag result.
      __ And(v0, scratch1, Operand(0xFFFFFFFF00000000L));
      __ Ret();
      break;
    case Token::SHR:
      __ SmiUntag32(scratch1, left);
      __ GetLeastBitsFromSmi(scratch2, right, 5);
      __ srl(scratch1, scratch1, scratch2);
      __ bfexts(at2, scratch1, 0, 31);
      __ Branch(&not_smi_result, lt, at2, Operand(zero));
      __ SmiTag(v0, scratch1);
      __ Ret();
      break;
    case Token::SHL:
      // Remove tags from operands.
      __ SmiUntag32(scratch1, left);
      __ GetLeastBitsFromSmi(scratch2, right, 5);
      __ sll(scratch1, scratch1, scratch2);
      __ SmiTag(v0, scratch1);
      __ Ret();
      break;
    default:
      UNREACHABLE();
  }
  __ move(v0, t3);
  __ bind(&not_smi_result);
}


void BinaryOpStub_GenerateHeapResultAllocation(MacroAssembler* masm,
                                               Register result,
                                               Register heap_number_map,
                                               Register scratch1,
                                               Register scratch2,
                                               Label* gc_required,
                                               OverwriteMode mode);


void BinaryOpStub_GenerateFPOperation(MacroAssembler* masm,
                                      BinaryOpIC::TypeInfo left_type,
                                      BinaryOpIC::TypeInfo right_type,
                                      bool smi_operands,
                                      Label* not_numbers,
                                      Label* gc_required,
                                      Label* miss,
                                      Token::Value op,
                                      OverwriteMode mode) {
  Register left = a1;
  Register right = a0;
  Register scratch1 = t3;
  Register scratch2 = t5;
  Register scratch3 = t0;
  Register scratch4 = t1;

  ASSERT(smi_operands || (not_numbers != NULL));
  if (smi_operands) {
    __ AssertSmi(left);
    __ AssertSmi(right);
  }
  if (left_type == BinaryOpIC::SMI) {
    __ JumpIfNotSmi(left, miss);
  }
  if (right_type == BinaryOpIC::SMI) {
    __ JumpIfNotSmi(right, miss);
  }

  Register heap_number_map = t2;
  __ LoadRoot(heap_number_map, Heap::kHeapNumberMapRootIndex);

  switch (op) {
    case Token::ADD:
    case Token::SUB:
    case Token::MUL:
    case Token::DIV:
    case Token::MOD: {
      // Load left and right operands into f12 and f14 or a0/a1 and a2/a3
      // depending on operation.
      FloatingPointHelper::Destination destination = FloatingPointHelper::kCoreRegisters;

      // Allocate new heap number for result.
      Register result = s0;
      BinaryOpStub_GenerateHeapResultAllocation(
          masm, result, heap_number_map, scratch1, scratch2, gc_required, mode);

      // Load the operands.
      if (smi_operands) {
        FloatingPointHelper::LoadSmis(masm, destination, scratch1, scratch2, scratch3);
      } else {
        // Load right operand to f14 or a2/a3.
        if (right_type == BinaryOpIC::INT32) {
          FloatingPointHelper::LoadNumberAsInt32Double(
              masm, right, destination, a3, heap_number_map,
              scratch1, scratch2, scratch3, miss);
        } else {
          Label* fail = (right_type == BinaryOpIC::NUMBER) ? miss : not_numbers;
          FloatingPointHelper::LoadNumber(
              masm, destination, right, a3, heap_number_map,
              scratch1, scratch2, scratch3, fail);
        }
        // Load left operand to f12 or a0/a1. This keeps a0/a1 intact if it
        // jumps to |miss|.
        if (left_type == BinaryOpIC::INT32) {
          FloatingPointHelper::LoadNumberAsInt32Double(
              masm, left, destination, a2, heap_number_map,
              scratch1, scratch2, scratch3, miss);
        } else {
          Label* fail = (left_type == BinaryOpIC::NUMBER) ? miss : not_numbers;
          FloatingPointHelper::LoadNumber(
              masm, destination, left, a2, heap_number_map,
              scratch1, scratch2, scratch3, fail);
        }
      }

      // Calculate the result.
      // Call the C function to handle the double operation.
      FloatingPointHelper::CallCCodeForDoubleOperation(masm,
                                                       op,
                                                       result,
                                                       scratch1);
      if (FLAG_debug_code) {
        __ stop("Unreachable code.");
      }

      break;
    }
    case Token::BIT_OR:
    case Token::BIT_XOR:
    case Token::BIT_AND:
    case Token::SAR:
    case Token::SHR:
    case Token::SHL: {
      if (smi_operands) {
        __ SmiUntag(a3, left);
        __ SmiUntag(a2, right);
      } else {
        // Convert operands to 32-bit integers. Right in a2 and left in a3.
        FloatingPointHelper::ConvertNumberToInt32(masm,
                                                  left,
                                                  a3,
                                                  heap_number_map,
                                                  scratch1,
                                                  scratch2,
                                                  scratch3,
                                                  scratch4,
                                                  not_numbers);
        FloatingPointHelper::ConvertNumberToInt32(masm,
                                                  right,
                                                  a2,
                                                  heap_number_map,
                                                  scratch1,
                                                  scratch2,
                                                  scratch3,
                                                  scratch4,
                                                  not_numbers);
      }
      Label result_not_a_smi;
      switch (op) {
        case Token::BIT_OR:
          __ Or(a2, a3, Operand(a2));
          break;
        case Token::BIT_XOR:
          __ Xor(a2, a3, Operand(a2));
          break;
        case Token::BIT_AND:
          __ And(a2, a3, Operand(a2));
          break;
        case Token::SAR:
          // Use only the 5 least significant bits of the shift count.
          __ GetLeastBitsFromInt32(a2, a2, 5);
          __ sra(a2, a3, a2);
          break;
        case Token::SHR:
          // Use only the 5 least significant bits of the shift count,
	  // and get rid of the upper sign bits (if any) of the value.
          __ GetLeastBitsFromInt32(a2, a2, 5);
          __ bfextu(a3, a3, 0, 31);
          __ srl(a2, a3, a2);
          // Check if result is negative, after sign extending.  This 
	  // can only happen for a shift by zero of a negative value.
          __ bfexts(a2, a2, 0, 31);
          __ Branch(&result_not_a_smi, lt, a2, Operand(zero));
          break;
        case Token::SHL:
          // Use only the 5 least significant bits of the shift count.
          __ GetLeastBitsFromInt32(a2, a2, 5);
          __ sll(a2, a3, a2);
          break;
        default:
          UNREACHABLE();
      }
      __ SmiTag(v0, a2);
      __ Ret();

      // Allocate new heap number for result.
      __ bind(&result_not_a_smi);
      Register result = scratch4;
      if (smi_operands) {
        __ AllocateHeapNumber(
            result, scratch1, scratch2, heap_number_map, gc_required);
      } else {
        BinaryOpStub_GenerateHeapResultAllocation(
            masm, result, heap_number_map, scratch1, scratch2, gc_required,
            mode);
      }

      // a2: Answer as signed int32.
      // scratch4: Heap number to write answer into.

      __ move(v0, scratch4);

      __ sll(a2, a2, 32);
      ConvertToDoubleStub i2d(at2, a2, a3, r4, false);
      __ push(lr);
      __ Call(i2d.GetCode(masm->isolate()));
      __ pop(lr);
      __ st(at2, FieldMemOperand(v0, HeapNumber::kValueOffset));
      __ Ret();

      break;
    }
    default:
      UNREACHABLE();
  }
}


// Generate the smi code. If the operation on smis are successful this return is
// generated. If the result is not a smi and heap number allocation is not
// requested the code falls through. If number allocation is requested but a
// heap number cannot be allocated the code jumps to the label gc_required.
void BinaryOpStub_GenerateSmiCode(
    MacroAssembler* masm,
    Label* use_runtime,
    Label* gc_required,
    Token::Value op,
    BinaryOpStub::SmiCodeGenerateHeapNumberResults allow_heapnumber_results,
    OverwriteMode mode) {
  Label not_smis;

  Register left = a1;
  Register right = a0;
  Register scratch1 = t3;

  // Perform combined smi check on both operands.
  __ Or(scratch1, left, Operand(right));
  STATIC_ASSERT(kSmiTag == 0);
  __ JumpIfNotSmi(scratch1, &not_smis);

  // If the smi-smi operation results in a smi return is generated.
  BinaryOpStub_GenerateSmiSmiOperation(masm, op);

  // If heap number results are possible generate the result in an allocated
  // heap number.
  if (allow_heapnumber_results == BinaryOpStub::ALLOW_HEAPNUMBER_RESULTS) {
    BinaryOpStub_GenerateFPOperation(
        masm, BinaryOpIC::UNINITIALIZED, BinaryOpIC::UNINITIALIZED, true,
        use_runtime, gc_required, &not_smis, op, mode);
  }
  __ bind(&not_smis);
}


void BinaryOpStub::GenerateSmiStub(MacroAssembler* masm) {
  Label not_smis, call_runtime;

  if (result_type_ == BinaryOpIC::UNINITIALIZED ||
      result_type_ == BinaryOpIC::SMI) {
    // Only allow smi results.
    BinaryOpStub_GenerateSmiCode(
        masm, &call_runtime, NULL, op_, NO_HEAPNUMBER_RESULTS, mode_);
  } else {
    // Allow heap number result and don't make a transition if a heap number
    // cannot be allocated.
    BinaryOpStub_GenerateSmiCode(
        masm, &call_runtime, &call_runtime, op_, ALLOW_HEAPNUMBER_RESULTS,
        mode_);
  }

  // Code falls through if the result is not returned as either a smi or heap
  // number.
  GenerateTypeTransition(masm);

  __ bind(&call_runtime);
    GenerateRegisterArgsPush(masm);
    GenerateCallRuntime(masm);
}


void BinaryOpStub::GenerateBothStringStub(MacroAssembler* masm) {
  Label call_runtime;
  ASSERT(left_type_ == BinaryOpIC::STRING && right_type_ == BinaryOpIC::STRING);
  ASSERT(op_ == Token::ADD);
  // If both arguments are strings, call the string add stub.
  // Otherwise, do a transition.

  // Registers containing left and right operands respectively.
  Register left = a1;
  Register right = a0;

  // Test if left operand is a string.
  __ JumpIfSmi(left, &call_runtime);
  __ GetObjectType(left, a2, a2);
  __ Branch(&call_runtime, ge, a2, Operand(FIRST_NONSTRING_TYPE));

  // Test if right operand is a string.
  __ JumpIfSmi(right, &call_runtime);
  __ GetObjectType(right, a2, a2);
  __ Branch(&call_runtime, ge, a2, Operand(FIRST_NONSTRING_TYPE));

  StringAddStub string_add_stub(NO_STRING_CHECK_IN_STUB);
  GenerateRegisterArgsPush(masm);
  __ TailCallStub(&string_add_stub);

  __ bind(&call_runtime);
  GenerateTypeTransition(masm);
}


void BinaryOpStub::GenerateInt32Stub(MacroAssembler* masm) {
  // The int32 case is identical to the Smi case.  We avoid creating this
  // ic state on TileGX, just like what x64 has done.
  UNREACHABLE();
}


void BinaryOpStub::GenerateOddballStub(MacroAssembler* masm) {
  Label call_runtime;

  if (op_ == Token::ADD) {
    // Handle string addition here, because it is the only operation
    // that does not do a ToNumber conversion on the operands.
    GenerateAddStrings(masm);
  }

  // Convert oddball arguments to numbers.
  Label check, done;
  __ LoadRoot(t0, Heap::kUndefinedValueRootIndex);
  __ Branch(&check, ne, a1, Operand(t0));
  if (Token::IsBitOp(op_)) {
    __ li(a1, Operand(Smi::FromInt(0)));
  } else {
    __ LoadRoot(a1, Heap::kNanValueRootIndex);
  }
  __ jmp(&done);
  __ bind(&check);
  __ LoadRoot(t0, Heap::kUndefinedValueRootIndex);
  __ Branch(&done, ne, a0, Operand(t0));
  if (Token::IsBitOp(op_)) {
    __ li(a0, Operand(Smi::FromInt(0)));
  } else {
    __ LoadRoot(a0, Heap::kNanValueRootIndex);
  }
  __ bind(&done);

  GenerateNumberStub(masm);
}


void BinaryOpStub::GenerateNumberStub(MacroAssembler* masm) {
  Label call_runtime, transition;
  BinaryOpStub_GenerateFPOperation(
      masm, left_type_, right_type_, false,
      &transition, &call_runtime, &transition, op_, mode_);

  __ bind(&transition);
  GenerateTypeTransition(masm);

  __ bind(&call_runtime);

  GenerateRegisterArgsPush(masm);
  GenerateCallRuntime(masm);
}


void BinaryOpStub::GenerateGeneric(MacroAssembler* masm) {
  Label call_runtime, call_string_add_or_runtime, transition;

  BinaryOpStub_GenerateSmiCode(
      masm, &call_runtime, &call_runtime, op_, ALLOW_HEAPNUMBER_RESULTS, mode_);

  BinaryOpStub_GenerateFPOperation(
      masm, left_type_, right_type_, false,
      &call_string_add_or_runtime, &call_runtime, &transition, op_, mode_);

  __ bind(&transition);
  GenerateTypeTransition(masm);

  __ bind(&call_string_add_or_runtime);
  if (op_ == Token::ADD) {
    GenerateAddStrings(masm);
  }

  __ bind(&call_runtime);
  GenerateRegisterArgsPush(masm);
  GenerateCallRuntime(masm);
}


void BinaryOpStub::GenerateAddStrings(MacroAssembler* masm) {
  ASSERT(op_ == Token::ADD);
  Label left_not_string, call_runtime;

  Register left = a1;
  Register right = a0;

  // Check if left argument is a string.
  __ JumpIfSmi(left, &left_not_string);
  __ GetObjectType(left, a2, a2);
  __ Branch(&left_not_string, ge, a2, Operand(FIRST_NONSTRING_TYPE));

  StringAddStub string_add_left_stub(NO_STRING_CHECK_LEFT_IN_STUB);
  GenerateRegisterArgsPush(masm);
  __ TailCallStub(&string_add_left_stub);

  // Left operand is not a string, test right.
  __ bind(&left_not_string);
  __ JumpIfSmi(right, &call_runtime);
  __ GetObjectType(right, a2, a2);
  __ Branch(&call_runtime, ge, a2, Operand(FIRST_NONSTRING_TYPE));

  StringAddStub string_add_right_stub(NO_STRING_CHECK_RIGHT_IN_STUB);
  GenerateRegisterArgsPush(masm);
  __ TailCallStub(&string_add_right_stub);

  // At least one argument is not a string.
  __ bind(&call_runtime);
}


void BinaryOpStub_GenerateHeapResultAllocation(MacroAssembler* masm,
                                               Register result,
                                               Register heap_number_map,
                                               Register scratch1,
                                               Register scratch2,
                                               Label* gc_required,
                                               OverwriteMode mode) {
  // Code below will scratch result if allocation fails. To keep both arguments
  // intact for the runtime call result cannot be one of these.
  ASSERT(!result.is(a0) && !result.is(a1));

  if (mode == OVERWRITE_LEFT || mode == OVERWRITE_RIGHT) {
    Label skip_allocation, allocated;
    Register overwritable_operand = mode == OVERWRITE_LEFT ? a1 : a0;
    // If the overwritable operand is already an object, we skip the
    // allocation of a heap number.
    __ JumpIfNotSmi(overwritable_operand, &skip_allocation);
    // Allocate a heap number for the result.
    __ AllocateHeapNumber(
        result, scratch1, scratch2, heap_number_map, gc_required);
    __ Branch(&allocated);
    __ bind(&skip_allocation);
    // Use object holding the overwritable operand for result.
    __ move(result, overwritable_operand);
    __ bind(&allocated);
  } else {
    ASSERT(mode == NO_OVERWRITE);
    __ AllocateHeapNumber(
        result, scratch1, scratch2, heap_number_map, gc_required);
  }
}

void BinaryOpStub::GenerateRegisterArgsPush(MacroAssembler* masm) {
  __ Push(a1, a0);
}



void TranscendentalCacheStub::Generate(MacroAssembler* masm) {
  // Untagged case: double input in f4, double result goes
  //   into f4.
  // Tagged case: tagged input on top of stack and in a0,
  //   tagged result (heap number) goes into v0.

  Label input_not_smi;
  Label loaded;
  Label calculate;
  Label invalid_cache;
  const Register scratch0 = t5;
  const Register scratch1 = t3;
  const Register scratch2 = t6;
  const Register cache_entry = a0;
  const bool tagged = (argument_type_ == TAGGED);

  __ bind(&calculate);
  Counters* counters = masm->isolate()->counters();
  __ IncrementCounter(
      counters->transcendental_cache_miss(), 1, scratch0, scratch1);
  if (tagged) {
    __ bind(&invalid_cache);
    __ TailCallExternalReference(ExternalReference(RuntimeFunction(),
                                                   masm->isolate()),
                                 1,
                                 1);
  } else {
    Label no_update;
    Label skip_cache;

    // Call C function to calculate the result and update the cache.
    // a0: precalculated cache entry address.
    // a2 and a3: parts of the double value.
    // Store a0, a2 and a3 on stack for later before calling C function.
    __ Push(a3, a2, cache_entry);
    GenerateCallCFunction(masm, scratch0);
    __ move(scratch2, v0);

    // Try to update the cache. If we cannot allocate a
    // heap number, we return the result without updating.
    __ Pop(a3, a2, cache_entry);
    __ LoadRoot(t1, Heap::kHeapNumberMapRootIndex);
    __ AllocateHeapNumber(t2, scratch0, scratch1, t1, &no_update);
    __ st(scratch2, FieldMemOperand(t2, HeapNumber::kValueOffset));

    __ st(a2, MemOperand(cache_entry, 0 * kPointerSize));
    __ st(a3, MemOperand(cache_entry, 1 * kPointerSize));
    __ st(t2, MemOperand(cache_entry, 2 * kPointerSize));

    __ move(v0, cache_entry);
    __ Ret();


    __ bind(&no_update);
    __ move(v0, scratch2);

    // We return the value in f4 without adding it to the cache, but
    // we cause a scavenging GC so that future allocations will succeed.
    {
      FrameScope scope(masm, StackFrame::INTERNAL);

      // Allocate an aligned object larger than a HeapNumber.
      ASSERT(4 * kPointerSize >= HeapNumber::kSize);
      __ li(scratch0, Operand(4 * kPointerSize));
      __ push(scratch0);
      __ CallRuntimeSaveDoubles(Runtime::kAllocateInNewSpace);
    }
    __ Ret();
  }
}


void TranscendentalCacheStub::GenerateCallCFunction(MacroAssembler* masm,
                                                    Register scratch) {
  __ push(ra);
  __ PrepareCallCFunction(2, scratch);

  AllowExternalCallThatCantCauseGC scope(masm);
  Isolate* isolate = masm->isolate();
  switch (type_) {
    case TranscendentalCache::SIN:
      __ CallCFunction(
          ExternalReference::math_sin_double_function(isolate),
          1);
      break;
    case TranscendentalCache::COS:
      __ CallCFunction(
          ExternalReference::math_cos_double_function(isolate),
          1);
      break;
    case TranscendentalCache::TAN:
      __ CallCFunction(ExternalReference::math_tan_double_function(isolate),
          1);
      break;
    case TranscendentalCache::LOG:
      __ CallCFunction(
          ExternalReference::math_log_double_function(isolate),
          1);
      break;
    default:
      UNIMPLEMENTED();
      break;
  }
  __ pop(ra);
}


Runtime::FunctionId TranscendentalCacheStub::RuntimeFunction() {
  switch (type_) {
    // Add more cases when necessary.
    case TranscendentalCache::SIN: return Runtime::kMath_sin;
    case TranscendentalCache::COS: return Runtime::kMath_cos;
    case TranscendentalCache::TAN: return Runtime::kMath_tan;
    case TranscendentalCache::LOG: return Runtime::kMath_log;
    default:
      UNIMPLEMENTED();
      return Runtime::kAbort;
  }
}


void StackCheckStub::Generate(MacroAssembler* masm) {
  __ TailCallRuntime(Runtime::kStackGuard, 0, 1);
}


void InterruptStub::Generate(MacroAssembler* masm) {
  __ TailCallRuntime(Runtime::kInterrupt, 0, 1);
}


void MathPowStub::Generate(MacroAssembler* masm) {

  ASSERT(exponent_type_ == ON_STACK);
  __ TailCallRuntime(Runtime::kMath_pow_cfunction, 2, 1);

  // Shouldn't be executed.
  __ bpt();
}


bool CEntryStub::NeedsImmovableCode() {
  return true;
}


bool CEntryStub::IsPregenerated() {
  return (!save_doubles_ || ISOLATE->fp_stubs_generated()) &&
          result_size_ == 1;
}


void CodeStub::GenerateStubsAheadOfTime(Isolate* isolate) {
  CEntryStub::GenerateAheadOfTime(isolate);
  StoreBufferOverflowStub::GenerateFixedRegStubsAheadOfTime(isolate);
  StubFailureTrampolineStub::GenerateAheadOfTime(isolate);
  RecordWriteStub::GenerateFixedRegStubsAheadOfTime(isolate);
  if (FLAG_optimize_constructed_arrays) {
    ArrayConstructorStubBase::GenerateStubsAheadOfTime(isolate);
  }
}


void CodeStub::GenerateFPStubs(Isolate* isolate) {
  SaveFPRegsMode mode = kDontSaveFPRegs;
  CEntryStub save_doubles(1, mode);
  StoreBufferOverflowStub stub(mode);
  // These stubs might already be in the snapshot, detect that and don't
  // regenerate, which would lead to code stub initialization state being messed
  // up.
  Code* save_doubles_code;
  if (!save_doubles.FindCodeInCache(&save_doubles_code, isolate)) {
    save_doubles_code = *save_doubles.GetCode(isolate);
  }
  Code* store_buffer_overflow_code;
  if (!stub.FindCodeInCache(&store_buffer_overflow_code, isolate)) {
      store_buffer_overflow_code = *stub.GetCode(isolate);
  }
  save_doubles_code->set_is_pregenerated(true);
  store_buffer_overflow_code->set_is_pregenerated(true);
  isolate->set_fp_stubs_generated(true);
}


void CEntryStub::GenerateAheadOfTime(Isolate* isolate) {
  CEntryStub stub(1, kDontSaveFPRegs);
  Handle<Code> code = stub.GetCode(isolate);
  code->set_is_pregenerated(true);
}

static void JumpIfOOM(MacroAssembler* masm,
                      Register value,
                      Register scratch,
                      Label* oom_label) {
  STATIC_ASSERT(Failure::OUT_OF_MEMORY_EXCEPTION == 3);
  STATIC_ASSERT(kFailureTag == 3);
  __ andi(scratch, value, 0xf);
  __ Branch(oom_label, eq, scratch, Operand(0xf));
}

void CEntryStub::GenerateCore(MacroAssembler* masm,
                              Label* throw_normal_exception,
                              Label* throw_termination_exception,
                              Label* throw_out_of_memory_exception,
                              bool do_gc,
                              bool always_allocate) {
  // r0: result parameter for PerformGC, if any
  // s0: number of arguments including receiver (C callee-saved)
  // s1: pointer to the first argument          (C callee-saved)
  // s2: pointer to builtin function            (C callee-saved)

  Isolate* isolate = masm->isolate();

  __ info(__LINE__);
  if (do_gc) {
    __ PrepareCallCFunction(1, r1);
    __ CallCFunction(ExternalReference::perform_gc_function(isolate), 1);
  }

  ExternalReference scope_depth =
      ExternalReference::heap_always_allocate_scope_depth(isolate);
  if (always_allocate) {
    __ li(r0, Operand(scope_depth));
    __ ld(r1, MemOperand(r0));
    __ Addu(r1, r1, Operand(1));
    __ st(r1, MemOperand(r0));
  }

  // Prepare arguments for C routine.
  // a0 = argc
  __ move(r0, s0);
  // a1 = argv (set in the delay slot after find_lr below).

  // We are calling compiled C/C++ code. a0 and a1 hold our two arguments. We
  // also need to reserve the 4 argument slots on the stack.

  __ AssertStackIsAligned();

  __ li(r2, Operand(ExternalReference::isolate_address(isolate)));

  // To let the GC traverse the return address of the exit frames, we need to
  // know where the return address is. The CEntryStub is unmovable, so
  // we can store the address on the stack to be able to find it again and
  // we never have to restore it, because it will not change.
  { Assembler::BlockTrampolinePoolScope block_trampoline_pool(masm);
    // This branch-and-link sequence is needed to find the current PC on mips,
    // saved to the ra register.
    // Use masm-> here instead of the double-underscore macro since extra
    // coverage code can interfere with the proper calculation of ra.
    masm->move(r1, s1);
    masm->lnk(lr);

    // Adjust the value in lr to point to the correct return location, 2nd
    // instruction past the real call into C code (the jalr(t9)), and push it.
    // This is the return address of the exit frame.
    const int kNumInstructionsToJump = 4;
    masm->Addu(lr, lr, kNumInstructionsToJump * kPointerSize);
    masm->st(lr, MemOperand(sp));  // This spot was reserved in EnterExitFrame.
    // Stack space reservation moved to the branch delay slot below.
    // Stack is still aligned.

    masm->addi(sp, sp, -16);
    // Call the C routine.
    masm->jalr(s2);
  }

  if (always_allocate) {
    // It's okay to clobber a2 and a3 here. v0 & v1 contain result.
    __ li(r2, Operand(scope_depth));
    __ ld(r3, MemOperand(r2));
    __ Subu(r3, r3, Operand(1));
    __ st(r3, MemOperand(r2));
  }

  // Check for failure result.
  Label failure_returned;
  STATIC_ASSERT(((kFailureTag + 1) & kFailureTagMask) == 0);
  __ addi(r2, r0, 1);
  __ andi(t0, r2, kFailureTagMask);
  __ addi(sp, sp, 16);
  __ Branch(&failure_returned, eq, t0, Operand(zero));


  // Exit C frame and return.
  // r0: result
  // sp: stack pointer
  // fp: frame pointer
  __ LeaveExitFrame(save_doubles_, s0, true);

  // Check if we should retry or throw exception.
  Label retry;
  __ bind(&failure_returned);
  STATIC_ASSERT(Failure::RETRY_AFTER_GC == 0);
  __ andi(t0, r0, ((1 << kFailureTypeTagSize) - 1) << kFailureTagSize);
  __ Branch(&retry, eq, t0, Operand(zero));

  // Special handling of out of memory exceptions.
  JumpIfOOM(masm, r0, t0, throw_out_of_memory_exception);

  // Retrieve the pending exception.
  __ li(t0, Operand(ExternalReference(Isolate::kPendingExceptionAddress,
                                      isolate)));
  __ ld(r0, MemOperand(t0));

  // See if we just retrieved an OOM exception.
  JumpIfOOM(masm, r0, t0, throw_out_of_memory_exception);

  // Clear the pending exception.
  __ LoadRoot(r3, Heap::kTheHoleValueRootIndex);
  //__ li(r3, Operand(isolate->factory()->the_hole_value()));
  __ li(t0, Operand(ExternalReference(Isolate::kPendingExceptionAddress,
                                      isolate)));
  __ st(r3, MemOperand(t0));

  // Special handling of termination exceptions which are uncatchable
  // by javascript code.
  __ LoadRoot(t0, Heap::kTerminationExceptionRootIndex);
  __ Branch(throw_termination_exception, eq, r0, Operand(t0));

  // Handle normal exception.
  __ jmp(throw_normal_exception);

  __ bind(&retry);
  // Last failure (v0) will be moved to (a0) for parameter when retrying.
}


void CEntryStub::Generate(MacroAssembler* masm) {
  __ info(__LINE__);
  // Called from JavaScript; parameters are on stack as if calling JS function
  // s0: number of arguments including receiver
  // s1: size of arguments excluding receiver
  // s2: pointer to builtin function
  // fp: frame pointer    (restored after C call)
  // sp: stack pointer    (restored as callee's sp after C call)
  // cp: current context  (C callee-saved)

  // NOTE: Invocations of builtins may return failure objects
  // instead of a proper result. The builtin entry handles
  // this by performing a garbage collection and retrying the
  // builtin once.

  // NOTE: s0-s2 hold the arguments of this function instead of r0-r2.
  // The reason for this is that these arguments would need to be saved anyway
  // so it's faster to set them up directly.
  // See MacroAssembler::PrepareCEntryArgs and PrepareCEntryFunction.

  // Compute the argv pointer in a callee-saved register.
  __ Addu(s1, sp, s1);

  // Enter the exit frame that transitions from JavaScript to C++.
  FrameScope scope(masm, StackFrame::MANUAL);
  __ EnterExitFrame(save_doubles_);

  // s0: number of arguments (C callee-saved)
  // s1: pointer to first argument (C callee-saved)
  // s2: pointer to builtin function (C callee-saved)

  Label throw_normal_exception;
  Label throw_termination_exception;
  Label throw_out_of_memory_exception;

  // Call into the runtime system.
  GenerateCore(masm,
               &throw_normal_exception,
               &throw_termination_exception,
               &throw_out_of_memory_exception,
               false,
               false);

  // Do space-specific GC and retry runtime call.
  GenerateCore(masm,
               &throw_normal_exception,
               &throw_termination_exception,
               &throw_out_of_memory_exception,
               true,
               false);

  // Do full GC and retry runtime call one final time.
  Failure* failure = Failure::InternalError();
  __ li(r0, Operand(reinterpret_cast<int64_t>(failure)));
  GenerateCore(masm,
               &throw_normal_exception,
               &throw_termination_exception,
               &throw_out_of_memory_exception,
               true,
               true);

  __ bind(&throw_out_of_memory_exception);
  // Set external caught exception to false.
  Isolate* isolate = masm->isolate();
  ExternalReference external_caught(Isolate::kExternalCaughtExceptionAddress,
                                    isolate);
  __ move(at, r0);
  __ li(r0, Operand(false, RelocInfo::NONE32));
  __ li(r2, Operand(external_caught));
  __ st(r0, MemOperand(r2));

  // Set pending exception and v0 to out of memory exception.
  Label already_have_failure;
  JumpIfOOM(masm, at, t0, &already_have_failure);
  Failure* out_of_memory = Failure::OutOfMemoryException(0x1);
  __ li(at, Operand(reinterpret_cast<int64_t>(out_of_memory)));
  __ bind(&already_have_failure);
  __ move(r0, at);
  __ li(r2, Operand(ExternalReference(Isolate::kPendingExceptionAddress,
                                      isolate)));
  __ st(r0, MemOperand(r2));
  // Fall through to the next label.

  __ bind(&throw_termination_exception);
  __ ThrowUncatchable(r0);

  __ bind(&throw_normal_exception);
  __ Throw(r0);
}

void JSEntryStub::GenerateBody(MacroAssembler* masm, bool is_construct) {
  Label invoke, handler_entry, exit;
  Isolate* isolate = masm->isolate();

  // Registers:
  // r0: entry address
  // r1: function
  // r2: receiver
  // r3: argc
  // r4: args

  // Save callee saved registers on the stack.
  __ MultiPush(kCalleeSaved | fp.bit() | lr.bit());

  __ InitializeRootRegister();

  // We build an EntryFrame.
  __ li(t3, Operand(-1));  // Push a bad frame pointer to fail if it is used.
  int marker = is_construct ? StackFrame::ENTRY_CONSTRUCT : StackFrame::ENTRY;
  __ li(t2, Operand(Smi::FromInt(marker)));
  __ li(t1, Operand(Smi::FromInt(marker)));
  __ li(t0, Operand(ExternalReference(Isolate::kCEntryFPAddress,
                                      isolate)));
  __ ld(t0, MemOperand(t0), __LINE__);
  __ Push(t3, t2, t1, t0);
  // Set up frame pointer for the frame to be pushed.
  __ addi(fp, sp, -EntryFrameConstants::kCallerFPOffset, __LINE__);

  // Registers:
  // r0: entry_address
  // r1: function
  // r2: receiver_pointer
  // r3: argc
  // r4: argv
  //
  // Stack:
  // caller fp          |
  // function slot      | entry frame
  // context slot       |
  // bad fp (0xff...f)  |
  // callee saved registers + lr

  // If this is the outermost JS call, set js_entry_sp value.
  Label non_outermost_js;
  ExternalReference js_entry_sp(Isolate::kJSEntrySPAddress, isolate);
  __ li(t1, Operand(ExternalReference(js_entry_sp)), __LINE__);
  __ ld(t2, MemOperand(t1), __LINE__);
  __ Branch(&non_outermost_js, ne, t2, Operand(zero));
  __ st(fp, MemOperand(t1), __LINE__);
  __ li(t0, Operand(Smi::FromInt(StackFrame::OUTERMOST_JSENTRY_FRAME)));
  Label cont;
  __ b(&cont);
  __ bind(&non_outermost_js);
  __ li(t0, Operand(Smi::FromInt(StackFrame::INNER_JSENTRY_FRAME)));
  __ bind(&cont);
  __ push(t0);

  // Jump to a faked try block that does the invoke, with a faked catch
  // block that sets the pending exception.
  __ jmp(&invoke);
  __ bind(&handler_entry);
  handler_offset_ = handler_entry.pos();
  // Caught exception: Store result (exception) in the pending exception
  // field in the JSEnv and return a failure sentinel.  Coming in here the
  // fp will be invalid because the PushTryHandler below sets it to 0 to
  // signal the existence of the JSEntry frame.
  __ li(t0, Operand(ExternalReference(Isolate::kPendingExceptionAddress,
                                      isolate)));
  __ st(r0, MemOperand(t0));  // We come back from 'invoke'. result is in v0.
  __ li(r0, Operand(reinterpret_cast<int64_t>(Failure::Exception())), __LINE__);
  __ b(&exit, __LINE__);  // b exposes branch delay slot.

  // Invoke: Link this frame into the handler chain.  There's only one
  // handler block in this code object, so its index is 0.
  __ bind(&invoke);
  __ PushTryHandler(StackHandler::JS_ENTRY, 0);
  // If an exception not caught by another handler occurs, this handler
  // returns control to the code after the bal(&invoke) above, which
  // restores all kCalleeSaved registers (including cp and fp) to their
  // saved values before returning a failure to C.

  // Clear any pending exceptions.
  __ LoadRoot(t1, Heap::kTheHoleValueRootIndex);
  __ li(t0, Operand(ExternalReference(Isolate::kPendingExceptionAddress,
                                      isolate)));
  __ st(t1, MemOperand(t0), __LINE__);

  // Invoke the function by calling through JS entry trampoline builtin.
  // Notice that we cannot store a reference to the trampoline code directly in
  // this stub, because runtime stubs are not traversed when doing GC.

  // Registers:
  // a0: entry_address
  // a1: function
  // a2: receiver_pointer
  // a3: argc
  // a4: argv
  //
  // Stack:
  // handler frame
  // entry frame
  // callee saved registers + ra
  // 4 args slots
  // args

  if (is_construct) {
    ExternalReference construct_entry(Builtins::kJSConstructEntryTrampoline,
                                      isolate);
    __ li(t0, Operand(construct_entry), __LINE__);
  } else {
    ExternalReference entry(Builtins::kJSEntryTrampoline, masm->isolate());
    __ li(t0, Operand(entry), __LINE__);
  }
  __ ld(t0, MemOperand(t0), __LINE__);  // Deref address.

  // Call JSEntryTrampoline.
  __ addli(t0, t0, Code::kHeaderSize - kHeapObjectTag, __LINE__);
  __ Call(t0);

  // Unlink this frame from the handler chain.
  __ PopTryHandler();

  __ bind(&exit);  // v0 holds result
  // Check if the current stack frame is marked as the outermost JS frame.
  Label non_outermost_js_2;
  __ pop(t1);
  __ Branch(&non_outermost_js_2,
            ne,
            t1,
            Operand(Smi::FromInt(StackFrame::OUTERMOST_JSENTRY_FRAME)));
  __ li(t1, Operand(ExternalReference(js_entry_sp)), __LINE__);
  __ st(zero, MemOperand(t1), __LINE__);
  __ bind(&non_outermost_js_2);

  // Restore the top frame descriptors from the stack.
  __ pop(t1);
  __ li(t0, Operand(ExternalReference(Isolate::kCEntryFPAddress,
                                      isolate)));
  __ st(t1, MemOperand(t0));

  // Reset the stack to the callee saved registers.
  __ addi(sp, sp, -EntryFrameConstants::kCallerFPOffset);

  // Restore callee saved registers from the stack.
  __ MultiPop(kCalleeSaved | fp.bit() | lr.bit());
  // Return.
  __ Jump(lr);
}


// Uses registers a0 to t0.
// Expected input (depending on whether args are in registers or on the stack):
// * object: a0 or at sp + 1 * kPointerSize.
// * function: a1 or at sp.
//
// An inlined call site may have been generated before calling this stub.
// In this case the offset to the inline site to patch is passed on the stack,
// in the safepoint slot for register t0.
void InstanceofStub::Generate(MacroAssembler* masm) {
  // Call site inlining and patching implies arguments in registers.
  ASSERT(HasArgsInRegisters() || !HasCallSiteInlineCheck());
  // ReturnTrueFalse is only implemented for inlined call sites.
  ASSERT(!ReturnTrueFalseObject() || HasCallSiteInlineCheck());

  // Fixed register usage throughout the stub:
  const Register object = a0;  // Object (lhs).
  Register map = a3;  // Map of the object.
  const Register function = a1;  // Function (rhs).
  const Register prototype = t0;  // Prototype of the function.
  const Register inline_site = t5;
  const Register scratch = a2;

  const int32_t kDeltaToLoadBoolResult = 5 * kPointerSize;

  Label slow, loop, is_instance, is_not_instance, not_js_object;

  if (!HasArgsInRegisters()) {
    __ ld(object, MemOperand(sp, 1 * kPointerSize));
    __ ld(function, MemOperand(sp, 0));
  }

  // Check that the left hand is a JS object and load map.
  __ JumpIfSmi(object, &not_js_object);
  __ IsObjectJSObjectType(object, map, scratch, &not_js_object);

  // If there is a call site cache don't look in the global cache, but do the
  // real lookup and update the call site cache.
  if (!HasCallSiteInlineCheck()) {
    Label miss;
    __ LoadRoot(at, Heap::kInstanceofCacheFunctionRootIndex);
    __ Branch(&miss, ne, function, Operand(at));
    __ LoadRoot(at, Heap::kInstanceofCacheMapRootIndex);
    __ Branch(&miss, ne, map, Operand(at));
    __ LoadRoot(v0, Heap::kInstanceofCacheAnswerRootIndex);
    __ DropAndRet(HasArgsInRegisters() ? 0 : 2);

    __ bind(&miss);
  }

  // Get the prototype of the function.
  __ TryGetFunctionPrototype(function, prototype, scratch, &slow, true);

  // Check that the function prototype is a JS object.
  __ JumpIfSmi(prototype, &slow);
  __ IsObjectJSObjectType(prototype, scratch, scratch, &slow);

  // Update the global instanceof or call site inlined cache with the current
  // map and function. The cached answer will be set when it is known below.
  if (!HasCallSiteInlineCheck()) {
    __ StoreRoot(function, Heap::kInstanceofCacheFunctionRootIndex);
    __ StoreRoot(map, Heap::kInstanceofCacheMapRootIndex);
  } else {
    ASSERT(HasArgsInRegisters());
    // Patch the (relocated) inlined map check.

    // The offset was stored in t0 safepoint slot.
    // (See LCodeGen::DoDeferredLInstanceOfKnownGlobal).
    __ LoadFromSafepointRegisterSlot(scratch, t0);
    __ Subu(inline_site, ra, scratch);
    // Get the map location in scratch and patch it.
    UNREACHABLE();
    __ GetRelocatedValue(inline_site, scratch, v1);  // v1 used as scratch.
    __ st(map, FieldMemOperand(scratch, JSGlobalPropertyCell::kValueOffset));
  }

  // Register mapping: a3 is object map and t0 is function prototype.
  // Get prototype of object into a2.
  __ ld(scratch, FieldMemOperand(map, Map::kPrototypeOffset));

  // We don't need map any more. Use it as a scratch register.
  Register scratch2 = map;
  map = no_reg;

  // Loop through the prototype chain looking for the function prototype.
  __ LoadRoot(scratch2, Heap::kNullValueRootIndex);
  __ bind(&loop);
  __ Branch(&is_instance, eq, scratch, Operand(prototype));
  __ Branch(&is_not_instance, eq, scratch, Operand(scratch2));
  __ ld(scratch, FieldMemOperand(scratch, HeapObject::kMapOffset));
  __ ld(scratch, FieldMemOperand(scratch, Map::kPrototypeOffset));
  __ Branch(&loop);

  __ bind(&is_instance);
  ASSERT(Smi::FromInt(0) == 0);
  if (!HasCallSiteInlineCheck()) {
    __ move(v0, zero);
    __ StoreRoot(v0, Heap::kInstanceofCacheAnswerRootIndex);
  } else {
    // Patch the call site to return true.
    __ LoadRoot(v0, Heap::kTrueValueRootIndex);
    __ Addu(inline_site, inline_site, Operand(kDeltaToLoadBoolResult));
    // Get the boolean result location in scratch and patch it.
    UNREACHABLE();
    __ PatchRelocatedValue(inline_site, scratch, v0);

    if (!ReturnTrueFalseObject()) {
      ASSERT_EQ(Smi::FromInt(0), 0);
      __ move(v0, zero);
    }
  }
  __ DropAndRet(HasArgsInRegisters() ? 0 : 2);

  __ bind(&is_not_instance);
  if (!HasCallSiteInlineCheck()) {
    __ li(v0, Operand(Smi::FromInt(1)));
    __ StoreRoot(v0, Heap::kInstanceofCacheAnswerRootIndex);
  } else {
    // Patch the call site to return false.
    __ LoadRoot(v0, Heap::kFalseValueRootIndex);
    __ Addu(inline_site, inline_site, Operand(kDeltaToLoadBoolResult));
    // Get the boolean result location in scratch and patch it.
    UNREACHABLE();
    __ PatchRelocatedValue(inline_site, scratch, v0);

    if (!ReturnTrueFalseObject()) {
      __ li(v0, Operand(Smi::FromInt(1)));
    }
  }

  __ DropAndRet(HasArgsInRegisters() ? 0 : 2);

  Label object_not_null, object_not_null_or_smi;
  __ bind(&not_js_object);
  // Before null, smi and string value checks, check that the rhs is a function
  // as for a non-function rhs an exception needs to be thrown.
  __ JumpIfSmi(function, &slow);
  __ GetObjectType(function, scratch2, scratch);
  __ Branch(&slow, ne, scratch, Operand(JS_FUNCTION_TYPE));

  // Null is not instance of anything.
  __ Branch(&object_not_null,
            ne,
            scratch,
            Operand(masm->isolate()->factory()->null_value()));
  __ li(v0, Operand(Smi::FromInt(1)));
  __ DropAndRet(HasArgsInRegisters() ? 0 : 2);

  __ bind(&object_not_null);
  // Smi values are not instances of anything.
  __ JumpIfNotSmi(object, &object_not_null_or_smi);
  __ li(v0, Operand(Smi::FromInt(1)));
  __ DropAndRet(HasArgsInRegisters() ? 0 : 2);

  __ bind(&object_not_null_or_smi);
  // String values are not instances of anything.
  __ IsObjectJSStringType(object, scratch, &slow);
  __ li(v0, Operand(Smi::FromInt(1)));
  __ DropAndRet(HasArgsInRegisters() ? 0 : 2);

  // Slow-case.  Tail call builtin.
  __ bind(&slow);
  if (!ReturnTrueFalseObject()) {
    if (HasArgsInRegisters()) {
      __ Push(a0, a1);
    }
  __ InvokeBuiltin(Builtins::INSTANCE_OF, JUMP_FUNCTION);
  } else {
    {
      FrameScope scope(masm, StackFrame::INTERNAL);
      __ Push(a0, a1);
      __ InvokeBuiltin(Builtins::INSTANCE_OF, CALL_FUNCTION);
    }
    __ move(at2, v0);
    __ LoadRoot(v0, Heap::kTrueValueRootIndex);
    __ DropAndRet(HasArgsInRegisters() ? 0 : 2, eq, at2, Operand(zero));
    __ LoadRoot(v0, Heap::kFalseValueRootIndex);
    __ DropAndRet(HasArgsInRegisters() ? 0 : 2);
  }
}


void FunctionPrototypeStub::Generate(MacroAssembler* masm) {
  Label miss;
  Register receiver;
  if (kind() == Code::KEYED_LOAD_IC) {
    // ----------- S t a t e -------------
    //  -- ra    : return address
    //  -- a0    : key
    //  -- a1    : receiver
    // -----------------------------------
    __ Branch(&miss, ne, a0,
        Operand(masm->isolate()->factory()->prototype_string()));
    receiver = a1;
  } else {
    ASSERT(kind() == Code::LOAD_IC);
    // ----------- S t a t e -------------
    //  -- a2    : name
    //  -- ra    : return address
    //  -- a0    : receiver
    //  -- sp[0] : receiver
    // -----------------------------------
    receiver = a0;
  }

  StubCompiler::GenerateLoadFunctionPrototype(masm, receiver, a3, t0, &miss);
  __ bind(&miss);
  StubCompiler::TailCallBuiltin(masm, StubCompiler::MissBuiltin(kind()));
}

void StringLengthStub::Generate(MacroAssembler* masm) {
  Label miss;
  Register receiver;
  if (kind() == Code::KEYED_LOAD_IC) {
    // ----------- S t a t e -------------
    //  -- ra    : return address
    //  -- a0    : key
    //  -- a1    : receiver
    // -----------------------------------
    __ Branch(&miss, ne, a0,
        Operand(masm->isolate()->factory()->length_string()));
    receiver = a1;
  } else {
    ASSERT(kind() == Code::LOAD_IC);
    // ----------- S t a t e -------------
    //  -- a2    : name
    //  -- ra    : return address
    //  -- a0    : receiver
    //  -- sp[0] : receiver
    // -----------------------------------
    receiver = a0;
  }

  StubCompiler::GenerateLoadStringLength(masm, receiver, a3, t0, &miss,
                                         support_wrapper_);

  __ bind(&miss);
  StubCompiler::TailCallBuiltin(masm, StubCompiler::MissBuiltin(kind()));
}

void StoreArrayLengthStub::Generate(MacroAssembler* masm) {
  // This accepts as a receiver anything JSArray::SetElementsLength accepts
  // (currently anything except for external arrays which means anything with
  // elements of FixedArray type).  Value must be a number, but only smis are
  // accepted as the most common case.
  Label miss;

  Register receiver;
  Register value;
  if (kind() == Code::KEYED_STORE_IC) {
    // ----------- S t a t e -------------
    //  -- ra    : return address
    //  -- a0    : value
    //  -- a1    : key
    //  -- a2    : receiver
    // -----------------------------------
    __ Branch(&miss, ne, a1,
        Operand(masm->isolate()->factory()->length_string()));
    receiver = a2;
    value = a0;
  } else {
    ASSERT(kind() == Code::STORE_IC);
    // ----------- S t a t e -------------
    //  -- ra    : return address
    //  -- a0    : value
    //  -- a1    : receiver
    //  -- a2    : key
    // -----------------------------------
    receiver = a1;
    value = a0;
  }
  Register scratch = a3;

  // Check that the receiver isn't a smi.
  __ JumpIfSmi(receiver, &miss);

  // Check that the object is a JS array.
  __ GetObjectType(receiver, scratch, scratch);
  __ Branch(&miss, ne, scratch, Operand(JS_ARRAY_TYPE));

  // Check that elements are FixedArray.
  // We rely on StoreIC_ArrayLength below to deal with all types of
  // fast elements (including COW).
  __ ld(scratch, FieldMemOperand(receiver, JSArray::kElementsOffset));
  __ GetObjectType(scratch, scratch, scratch);
  __ Branch(&miss, ne, scratch, Operand(FIXED_ARRAY_TYPE));

  // Check that the array has fast properties, otherwise the length
  // property might have been redefined.
  __ ld(scratch, FieldMemOperand(receiver, JSArray::kPropertiesOffset));
  __ ld(scratch, FieldMemOperand(scratch, FixedArray::kMapOffset));
  __ LoadRoot(at, Heap::kHashTableMapRootIndex);
  __ Branch(&miss, eq, scratch, Operand(at));

  // Check that value is a smi.
  __ JumpIfNotSmi(value, &miss);

  // Prepare tail call to StoreIC_ArrayLength.
  __ Push(receiver, value);

  ExternalReference ref =
      ExternalReference(IC_Utility(IC::kStoreIC_ArrayLength), masm->isolate());
  __ TailCallExternalReference(ref, 2, 1);

  __ bind(&miss);

  StubCompiler::TailCallBuiltin(masm, StubCompiler::MissBuiltin(kind()));
}



Register InstanceofStub::left() { return a0; }


Register InstanceofStub::right() { return a1; }


void LoadFieldStub::Generate(MacroAssembler* masm) {
  StubCompiler::DoGenerateFastPropertyLoad(masm, v0, reg_, inobject_, index_);
  __ Ret();
}


void ArgumentsAccessStub::GenerateReadElement(MacroAssembler* masm) {
  // The displacement is the offset of the last parameter (if any)
  // relative to the frame pointer.
  const int kDisplacement =
      StandardFrameConstants::kCallerSPOffset - kPointerSize;

  // Check that the key is a smiGenerateReadElement.
  Label slow;
  __ JumpIfNotSmi(a1, &slow);

  // Check if the calling frame is an arguments adaptor frame.
  Label adaptor;
  __ ld(a2, MemOperand(fp, StandardFrameConstants::kCallerFPOffset));
  __ ld(a3, MemOperand(a2, StandardFrameConstants::kContextOffset));
  __ Branch(&adaptor,
            eq,
            a3,
            Operand(Smi::FromInt(StackFrame::ARGUMENTS_ADAPTOR)));

  // Check index (a1) against formal parameters count limit passed in
  // through register a0. Use unsigned comparison to get negative
  // check for free.
  __ Branch(&slow, hs, a1, Operand(a0));

  // Read the argument from the stack and return it.
  __ sub(a3, a0, a1);
  __ sra(t3, a3, 32);
  __ sll(t3, t3, kPointerSizeLog2);
  __ Addu(a3, fp, Operand(t3));
  __ ld(v0, MemOperand(a3, kDisplacement));
  __ Ret();

  // Arguments adaptor case: Check index (a1) against actual arguments
  // limit found in the arguments adaptor frame. Use unsigned
  // comparison to get negative check for free.
  __ bind(&adaptor);
  __ ld(a0, MemOperand(a2, ArgumentsAdaptorFrameConstants::kLengthOffset));
  __ Branch(&slow, Ugreater_equal, a1, Operand(a0));

  // Read the argument from the adaptor frame and return it.
  __ sub(a3, a0, a1);
  __ sra(t3, a3, 32);
  __ sll(t3, t3, kPointerSizeLog2);
  __ Addu(a3, a2, Operand(t3));
  __ ld(v0, MemOperand(a3, kDisplacement));
  __ Ret();

  // Slow-case: Handle non-smi or out-of-bounds access to arguments
  // by calling the runtime system.
  __ bind(&slow);
  __ push(a1);
  __ TailCallRuntime(Runtime::kGetArgumentsProperty, 1, 1);
}


void ArgumentsAccessStub::GenerateNewNonStrictSlow(MacroAssembler* masm) {
  // sp[0] : number of parameters
  // sp[4] : receiver displacement
  // sp[8] : function
  // Check if the calling frame is an arguments adaptor frame.
  Label runtime;
  __ ld(a3, MemOperand(fp, StandardFrameConstants::kCallerFPOffset));
  __ ld(a2, MemOperand(a3, StandardFrameConstants::kContextOffset));
  __ Branch(&runtime,
            ne,
            a2,
            Operand(Smi::FromInt(StackFrame::ARGUMENTS_ADAPTOR)));

  // Patch the arguments.length and the parameters pointer in the current frame.
  __ ld(a2, MemOperand(a3, ArgumentsAdaptorFrameConstants::kLengthOffset));
  __ st(a2, MemOperand(sp, 0 * kPointerSize));
  __ sra(a2, a2, 32);
  __ sll(t3, a2, 3);
  __ Addu(a3, a3, Operand(t3));
  __ addli(a3, a3, StandardFrameConstants::kCallerSPOffset);
  __ st(a3, MemOperand(sp, 1 * kPointerSize));

  __ bind(&runtime);
  __ TailCallRuntime(Runtime::kNewArgumentsFast, 3, 1);
}


void ArgumentsAccessStub::GenerateNewNonStrictFast(MacroAssembler* masm) {
  // Stack layout:
  //  sp[0] : number of parameters (tagged)
  //  sp[4] : address of receiver argument
  //  sp[8] : function
  // Registers used over whole function:
  //  t2 : allocated object (tagged)
  //  t5 : mapped parameter count (tagged)

  __ ld(a1, MemOperand(sp, 0 * kPointerSize));
  // a1 = parameter count (tagged)

  // Check if the calling frame is an arguments adaptor frame.
  Label runtime;
  Label adaptor_frame, try_allocate;
  __ ld(a3, MemOperand(fp, StandardFrameConstants::kCallerFPOffset));
  __ ld(a2, MemOperand(a3, StandardFrameConstants::kContextOffset));
  __ Branch(&adaptor_frame,
            eq,
            a2,
            Operand(Smi::FromInt(StackFrame::ARGUMENTS_ADAPTOR)));

  // No adaptor, parameter count = argument count.
  __ move(a2, a1);
  __ b(&try_allocate);
  __ nop();   // Branch delay slot nop.

  // We have an adaptor frame. Patch the parameters pointer.
  __ bind(&adaptor_frame);
  __ ld(a2, MemOperand(a3, ArgumentsAdaptorFrameConstants::kLengthOffset));
  __ sra(t6, a2, 32);
  __ sll(t6, t6, 3);
  __ Addu(a3, a3, Operand(t6));
  __ Addu(a3, a3, Operand(StandardFrameConstants::kCallerSPOffset));
  __ st(a3, MemOperand(sp, 1 * kPointerSize));

  // a1 = parameter count (tagged)
  // a2 = argument count (tagged)
  // Compute the mapped parameter count = min(a1, a2) in a1.
  Label skip_min;
  __ Branch(&skip_min, lt, a1, Operand(a2));
  __ move(a1, a2);
  __ bind(&skip_min);

  __ bind(&try_allocate);

  // Compute the sizes of backing store, parameter map, and arguments object.
  // 1. Parameter map, has 2 extra words containing context and backing store.
  const int kParameterMapHeaderSize =
      FixedArray::kHeaderSize + 2 * kPointerSize;
  // If there are no mapped parameters, we do not need the parameter_map.
  Label param_map_size;
  ASSERT_EQ(0, Smi::FromInt(0));
  __ move(t5, zero);  // In delay slot: param map size = 0 when a1 == 0.
  __ Branch(&param_map_size, eq, a1, Operand(zero));
  __ sra(t5, a1, 32);
  __ sll(t5, t5, 3);
  __ addli(t5, t5, kParameterMapHeaderSize);
  __ bind(&param_map_size);

  // 2. Backing store.
  __ sra(t6, a2, 32);
  __ sll(t6, t6, 3);
  __ Addu(t5, t5, Operand(t6));
  __ Addu(t5, t5, Operand(FixedArray::kHeaderSize));

  // 3. Arguments object.
  __ Addu(t5, t5, Operand(Heap::kArgumentsObjectSize));

  // Do the allocation of all three objects in one go.
  __ Allocate(t5, v0, a3, t0, &runtime, TAG_OBJECT);

  // v0 = address of new object(s) (tagged)
  // a2 = argument count (tagged)
  // Get the arguments boilerplate from the current native context into t0.
  const int kNormalOffset =
      Context::SlotOffset(Context::ARGUMENTS_BOILERPLATE_INDEX);
  const int kAliasedOffset =
      Context::SlotOffset(Context::ALIASED_ARGUMENTS_BOILERPLATE_INDEX);

  __ ld(t0, MemOperand(cp, Context::SlotOffset(Context::GLOBAL_OBJECT_INDEX)));
  __ ld(t0, FieldMemOperand(t0, GlobalObject::kNativeContextOffset));
  Label skip2_ne, skip2_eq;
  __ Branch(&skip2_ne, ne, a1, Operand(zero));
  __ ld(t0, MemOperand(t0, kNormalOffset));
  __ bind(&skip2_ne);

  __ Branch(&skip2_eq, eq, a1, Operand(zero));
  __ ld(t0, MemOperand(t0, kAliasedOffset));
  __ bind(&skip2_eq);

  // v0 = address of new object (tagged)
  // a1 = mapped parameter count (tagged)
  // a2 = argument count (tagged)
  // t0 = address of boilerplate object (tagged)
  // Copy the JS object part.
  for (int i = 0; i < JSObject::kHeaderSize; i += kPointerSize) {
    __ ld(a3, FieldMemOperand(t0, i));
    __ st(a3, FieldMemOperand(v0, i));
  }

  // Set up the callee in-object property.
  STATIC_ASSERT(Heap::kArgumentsCalleeIndex == 1);
  __ ld(a3, MemOperand(sp, 2 * kPointerSize));
  const int kCalleeOffset = JSObject::kHeaderSize +
      Heap::kArgumentsCalleeIndex * kPointerSize;
  __ st(a3, FieldMemOperand(v0, kCalleeOffset));

  // Use the length (smi tagged) and set that as an in-object property too.
  STATIC_ASSERT(Heap::kArgumentsLengthIndex == 0);
  const int kLengthOffset = JSObject::kHeaderSize +
      Heap::kArgumentsLengthIndex * kPointerSize;
  __ st(a2, FieldMemOperand(v0, kLengthOffset));

  // Set up the elements pointer in the allocated arguments object.
  // If we allocated a parameter map, t0 will point there, otherwise
  // it will point to the backing store.
  __ Addu(t0, v0, Operand(Heap::kArgumentsObjectSize));
  __ st(t0, FieldMemOperand(v0, JSObject::kElementsOffset));

  // v0 = address of new object (tagged)
  // a1 = mapped parameter count (tagged)
  // a2 = argument count (tagged)
  // t0 = address of parameter map or backing store (tagged)
  // Initialize parameter map. If there are no mapped arguments, we're done.
  Label skip_parameter_map;
  Label skip3;
  __ Branch(&skip3, ne, a1, Operand(Smi::FromInt(0)));
  // Move backing store address to a3, because it is
  // expected there when filling in the unmapped arguments.
  __ move(a3, t0);
  __ bind(&skip3);

  __ Branch(&skip_parameter_map, eq, a1, Operand(Smi::FromInt(0)));

  __ LoadRoot(t2, Heap::kNonStrictArgumentsElementsMapRootIndex);
  __ st(t2, FieldMemOperand(t0, FixedArray::kMapOffset));
  __ Addu(t2, a1, Operand(Smi::FromInt(2)));
  __ st(t2, FieldMemOperand(t0, FixedArray::kLengthOffset));
  __ st(cp, FieldMemOperand(t0, FixedArray::kHeaderSize + 0 * kPointerSize));
  __ sra(t6, a1, 32);
  __ sll(t6, t6, 3);
  __ Addu(t2, t0, Operand(t6));
  __ Addu(t2, t2, Operand(kParameterMapHeaderSize));
  __ st(t2, FieldMemOperand(t0, FixedArray::kHeaderSize + 1 * kPointerSize));

  // Copy the parameter slots and the holes in the arguments.
  // We need to fill in mapped_parameter_count slots. They index the context,
  // where parameters are stored in reverse order, at
  //   MIN_CONTEXT_SLOTS .. MIN_CONTEXT_SLOTS+parameter_count-1
  // The mapped parameter thus need to get indices
  //   MIN_CONTEXT_SLOTS+parameter_count-1 ..
  //       MIN_CONTEXT_SLOTS+parameter_count-mapped_parameter_count
  // We loop from right to left.
  Label parameters_loop, parameters_test;
  __ move(t2, a1);
  __ ld(t5, MemOperand(sp, 0 * kPointerSize));
  __ Addu(t5, t5, Operand(Smi::FromInt(Context::MIN_CONTEXT_SLOTS)));
  __ Subu(t5, t5, Operand(a1));
  __ LoadRoot(t3, Heap::kTheHoleValueRootIndex);
  __ sra(t6, t2, 32);
  __ sll(t6, t6, 3);
  __ Addu(a3, t0, Operand(t6));
  __ Addu(a3, a3, Operand(kParameterMapHeaderSize));

  // t2 = loop variable (tagged)
  // a1 = mapping index (tagged)
  // a3 = address of backing store (tagged)
  // t0 = address of parameter map (tagged)
  // t1 = temporary scratch (a.o., for address calculation)
  // t3 = the hole value
  __ jmp(&parameters_test);

  __ bind(&parameters_loop);
  __ Subu(t2, t2, Operand(Smi::FromInt(1)));
  __ sra(t1, t2, 32);
  __ sll(t1, t1, 3);
  __ Addu(t1, t1, Operand(kParameterMapHeaderSize - kHeapObjectTag));
  __ Addu(t6, t0, t1);
  __ st(t5, MemOperand(t6));
  __ Subu(t1, t1, Operand(kParameterMapHeaderSize - FixedArray::kHeaderSize));
  __ Addu(t6, a3, t1);
  __ st(t3, MemOperand(t6));
  __ Addu(t5, t5, Operand(Smi::FromInt(1)));
  __ bind(&parameters_test);
  __ Branch(&parameters_loop, ne, t2, Operand(Smi::FromInt(0)));

  __ bind(&skip_parameter_map);
  // a2 = argument count (tagged)
  // a3 = address of backing store (tagged)
  // t1 = scratch
  // Copy arguments header and remaining slots (if there are any).
  __ LoadRoot(t1, Heap::kFixedArrayMapRootIndex);
  __ st(t1, FieldMemOperand(a3, FixedArray::kMapOffset));
  __ st(a2, FieldMemOperand(a3, FixedArray::kLengthOffset));

  Label arguments_loop, arguments_test;
  __ move(t5, a1);
  __ ld(t0, MemOperand(sp, 1 * kPointerSize));
  __ sra(t6, t5, 32);
  __ sll(t6, t6, 3);
  __ Subu(t0, t0, Operand(t6));
  __ jmp(&arguments_test);

  __ bind(&arguments_loop);
  __ Subu(t0, t0, Operand(kPointerSize));
  __ ld(t2, MemOperand(t0, 0));
  __ sra(t6, t5, 32);
  __ sll(t6, t6, 3);
  __ Addu(t1, a3, Operand(t6));
  __ st(t2, FieldMemOperand(t1, FixedArray::kHeaderSize));
  __ Addu(t5, t5, Operand(Smi::FromInt(1)));

  __ bind(&arguments_test);
  __ Branch(&arguments_loop, lt, t5, Operand(a2));

  // Return and remove the on-stack parameters.
  __ DropAndRet(3);

  // Do the runtime call to allocate the arguments object.
  // a2 = argument count (tagged)
  __ bind(&runtime);
  __ st(a2, MemOperand(sp, 0 * kPointerSize));  // Patch argument count.
  __ TailCallRuntime(Runtime::kNewArgumentsFast, 3, 1);
}


void ArgumentsAccessStub::GenerateNewStrict(MacroAssembler* masm) {
  // sp[0] : number of parameters
  // sp[4] : receiver displacement
  // sp[8] : function
  // Check if the calling frame is an arguments adaptor frame.
  Label adaptor_frame, try_allocate, runtime;
  __ ld(a2, MemOperand(fp, StandardFrameConstants::kCallerFPOffset));
  __ ld(a3, MemOperand(a2, StandardFrameConstants::kContextOffset));
  __ Branch(&adaptor_frame,
            eq,
            a3,
            Operand(Smi::FromInt(StackFrame::ARGUMENTS_ADAPTOR)));

  // Get the length from the frame.
  __ ld(a1, MemOperand(sp, 0));
  __ Branch(&try_allocate);

  // Patch the arguments.length and the parameters pointer.
  __ bind(&adaptor_frame);
  __ ld(a1, MemOperand(a2, ArgumentsAdaptorFrameConstants::kLengthOffset));
  __ st(a1, MemOperand(sp, 0));
  __ sra(at, a1, 32);
  __ sll(at, at, kPointerSizeLog2);
  __ Addu(a3, a2, Operand(at));

  __ Addu(a3, a3, Operand(StandardFrameConstants::kCallerSPOffset));
  __ st(a3, MemOperand(sp, 1 * kPointerSize));

  // Try the new space allocation. Start out with computing the size
  // of the arguments object and the elements array in words.
  Label add_arguments_object;
  __ bind(&try_allocate);
  __ Branch(&add_arguments_object, eq, a1, Operand(zero));
  __ sra(a1, a1, 32);

  __ Addu(a1, a1, Operand(FixedArray::kHeaderSize / kPointerSize));
  __ bind(&add_arguments_object);
  __ Addu(a1, a1, Operand(Heap::kArgumentsObjectSizeStrict / kPointerSize));

  // Do the allocation of both objects in one go.
  __ Allocate(a1, v0, a2, a3, &runtime,
              static_cast<AllocationFlags>(TAG_OBJECT | SIZE_IN_WORDS));

  // Get the arguments boilerplate from the current native context.
  __ ld(t0, MemOperand(cp, Context::SlotOffset(Context::GLOBAL_OBJECT_INDEX)));
  __ ld(t0, FieldMemOperand(t0, GlobalObject::kNativeContextOffset));
  __ ld(t0, MemOperand(t0, Context::SlotOffset(
      Context::STRICT_MODE_ARGUMENTS_BOILERPLATE_INDEX)));

  // Copy the JS object part.
  __ CopyFields(v0, t0, a3.bit(), JSObject::kHeaderSize / kPointerSize);

  // Get the length (smi tagged) and set that as an in-object property too.
  STATIC_ASSERT(Heap::kArgumentsLengthIndex == 0);
  __ ld(a1, MemOperand(sp, 0 * kPointerSize));
  __ st(a1, FieldMemOperand(v0, JSObject::kHeaderSize +
      Heap::kArgumentsLengthIndex * kPointerSize));

  Label done;
  __ Branch(&done, eq, a1, Operand(zero));

  // Get the parameters pointer from the stack.
  __ ld(a2, MemOperand(sp, 1 * kPointerSize));

  // Set up the elements pointer in the allocated arguments object and
  // initialize the header in the elements fixed array.
  __ Addu(t0, v0, Operand(Heap::kArgumentsObjectSizeStrict));
  __ st(t0, FieldMemOperand(v0, JSObject::kElementsOffset));
  __ LoadRoot(a3, Heap::kFixedArrayMapRootIndex);
  __ st(a3, FieldMemOperand(t0, FixedArray::kMapOffset));
  __ st(a1, FieldMemOperand(t0, FixedArray::kLengthOffset));
  // Untag the length for the loop.
  __ sra(a1, a1, 32);

  // Copy the fixed array slots.
  Label loop;
  // Set up t0 to point to the first array slot.
  __ Addu(t0, t0, Operand(FixedArray::kHeaderSize - kHeapObjectTag));
  __ bind(&loop);
  // Pre-decrement a2 with kPointerSize on each iteration.
  // Pre-decrement in order to skip receiver.
  __ Addu(a2, a2, Operand(-kPointerSize));
  __ ld(a3, MemOperand(a2));
  // Post-increment t0 with kPointerSize on each iteration.
  __ st(a3, MemOperand(t0));
  __ Addu(t0, t0, Operand(kPointerSize));
  __ Subu(a1, a1, Operand(1));
  __ Branch(&loop, ne, a1, Operand(zero));

  // Return and remove the on-stack parameters.
  __ bind(&done);
  __ DropAndRet(3);

  // Do the runtime call to allocate the arguments object.
  __ bind(&runtime);
  __ TailCallRuntime(Runtime::kNewStrictArgumentsFast, 3, 1);
}


void RegExpExecStub::Generate(MacroAssembler* masm) {
  // Just jump directly to runtime if native RegExp is not selected at compile
  // time or if regexp entry in generated code is turned off runtime switch or
  // at compilation.
#ifdef V8_INTERPRETED_REGEXP
  __ TailCallRuntime(Runtime::kRegExpExec, 4, 1);
#else  // V8_INTERPRETED_REGEXP

  UNREACHABLE();
  // Stack frame on entry.
  //  sp[0]: last_match_info (expected JSArray)
  //  sp[4]: previous index
  //  sp[8]: subject string
  //  sp[12]: JSRegExp object

  const int kLastMatchInfoOffset = 0 * kPointerSize;
  const int kPreviousIndexOffset = 1 * kPointerSize;
  const int kSubjectOffset = 2 * kPointerSize;
  const int kJSRegExpOffset = 3 * kPointerSize;

  Isolate* isolate = masm->isolate();

  Label runtime;
  // Allocation of registers for this function. These are in callee save
  // registers and will be preserved by the call to the native RegExp code, as
  // this code is called using the normal C calling convention. When calling
  // directly from generated code the native RegExp code will not do a GC and
  // therefore the content of these registers are safe to use after the call.
  // MIPS - using s0..s2, since we are not using CEntry Stub.
  Register subject = s0;
  Register regexp_data = s1;
  Register last_match_info_elements = s2;

  // Ensure that a RegExp stack is allocated.
  ExternalReference address_of_regexp_stack_memory_address =
      ExternalReference::address_of_regexp_stack_memory_address(
          isolate);
  ExternalReference address_of_regexp_stack_memory_size =
      ExternalReference::address_of_regexp_stack_memory_size(isolate);
  __ li(a0, Operand(address_of_regexp_stack_memory_size));
  __ ld(a0, MemOperand(a0, 0));
  __ Branch(&runtime, eq, a0, Operand(zero));

  // Check that the first argument is a JSRegExp object.
  __ ld(a0, MemOperand(sp, kJSRegExpOffset));
  STATIC_ASSERT(kSmiTag == 0);
  __ JumpIfSmi(a0, &runtime);
  __ GetObjectType(a0, a1, a1);
  __ Branch(&runtime, ne, a1, Operand(JS_REGEXP_TYPE));

  // Check that the RegExp has been compiled (data contains a fixed array).
  __ ld(regexp_data, FieldMemOperand(a0, JSRegExp::kDataOffset));
  if (FLAG_debug_code) {
    __ And(t0, regexp_data, Operand(kSmiTagMask));
    __ Check(nz,
             "Unexpected type for RegExp data, FixedArray expected",
             t0,
             Operand(zero));
    __ GetObjectType(regexp_data, a0, a0);
    __ Check(eq,
             "Unexpected type for RegExp data, FixedArray expected",
             a0,
             Operand(FIXED_ARRAY_TYPE));
  }

  // regexp_data: RegExp data (FixedArray)
  // Check the type of the RegExp. Only continue if type is JSRegExp::IRREGEXP.
  __ ld(a0, FieldMemOperand(regexp_data, JSRegExp::kDataTagOffset));
  __ Branch(&runtime, ne, a0, Operand(Smi::FromInt(JSRegExp::IRREGEXP)));

  // regexp_data: RegExp data (FixedArray)
  // Check that the number of captures fit in the static offsets vector buffer.
  __ ld(a2,
         FieldMemOperand(regexp_data, JSRegExp::kIrregexpCaptureCountOffset));
  // Check (number_of_captures + 1) * 2 <= offsets vector size
  // Or          number_of_captures * 2 <= offsets vector size - 2
  // Multiplying by 2 comes for free since a2 is smi-tagged.
  STATIC_ASSERT(kSmiTag == 0);
  STATIC_ASSERT(kSmiTagSize + kSmiShiftSize == 32);
  STATIC_ASSERT(Isolate::kJSRegexpStaticOffsetsVectorSize >= 2);
  __ Branch(
      &runtime, hi, a2, Operand(Isolate::kJSRegexpStaticOffsetsVectorSize - 2));

  // Reset offset for possibly sliced string.
  __ move(t0, zero);
  __ ld(subject, MemOperand(sp, kSubjectOffset));
  __ JumpIfSmi(subject, &runtime);
  __ move(a3, subject);  // Make a copy of the original subject string.
  __ ld(a0, FieldMemOperand(subject, HeapObject::kMapOffset));
  __ ld1u(a0, FieldMemOperand(a0, Map::kInstanceTypeOffset));
  // subject: subject string
  // a3: subject string
  // a0: subject string instance type
  // regexp_data: RegExp data (FixedArray)
  // Handle subject string according to its encoding and representation:
  // (1) Sequential string?  If yes, go to (5).
  // (2) Anything but sequential or cons?  If yes, go to (6).
  // (3) Cons string.  If the string is flat, replace subject with first string.
  //     Otherwise bailout.
  // (4) Is subject external?  If yes, go to (7).
  // (5) Sequential string.  Load regexp code according to encoding.
  // (E) Carry on.
  /// [...]

  // Deferred code at the end of the stub:
  // (6) Not a long external string?  If yes, go to (8).
  // (7) External string.  Make it, offset-wise, look like a sequential string.
  //     Go to (5).
  // (8) Short external string or not a string?  If yes, bail out to runtime.
  // (9) Sliced string.  Replace subject with parent.  Go to (4).

  Label seq_string /* 5 */, external_string /* 7 */,
        check_underlying /* 4 */, not_seq_nor_cons /* 6 */,
        not_long_external /* 8 */;

  // (1) Sequential string?  If yes, go to (5).
  __ And(a1,
         a0,
         Operand(kIsNotStringMask |
                 kStringRepresentationMask |
                 kShortExternalStringMask));
  STATIC_ASSERT((kStringTag | kSeqStringTag) == 0);
  __ Branch(&seq_string, eq, a1, Operand(zero));  // Go to (5).

  // (2) Anything but sequential or cons?  If yes, go to (6).
  STATIC_ASSERT(kConsStringTag < kExternalStringTag);
  STATIC_ASSERT(kSlicedStringTag > kExternalStringTag);
  STATIC_ASSERT(kIsNotStringMask > kExternalStringTag);
  STATIC_ASSERT(kShortExternalStringTag > kExternalStringTag);
  // Go to (6).
  __ Branch(&not_seq_nor_cons, ge, a1, Operand(kExternalStringTag));

  // (3) Cons string.  Check that it's flat.
  // Replace subject with first string and reload instance type.
  __ ld(a0, FieldMemOperand(subject, ConsString::kSecondOffset));
  __ LoadRoot(a1, Heap::kempty_stringRootIndex);
  __ Branch(&runtime, ne, a0, Operand(a1));
  __ ld(subject, FieldMemOperand(subject, ConsString::kFirstOffset));

  // (4) Is subject external?  If yes, go to (7).
  __ bind(&check_underlying);
  __ ld(a0, FieldMemOperand(subject, HeapObject::kMapOffset));
  __ ld1u(a0, FieldMemOperand(a0, Map::kInstanceTypeOffset));
  STATIC_ASSERT(kSeqStringTag == 0);
  __ And(at, a0, Operand(kStringRepresentationMask));
  // The underlying external string is never a short external string.
  STATIC_CHECK(ExternalString::kMaxShortLength < ConsString::kMinLength);
  STATIC_CHECK(ExternalString::kMaxShortLength < SlicedString::kMinLength);
  __ Branch(&external_string, ne, at, Operand(zero));  // Go to (7).

  // (5) Sequential string.  Load regexp code according to encoding.
  __ bind(&seq_string);
  // subject: sequential subject string (or look-alike, external string)
  // a3: original subject string
  // Load previous index and check range before a3 is overwritten.  We have to
  // use a3 instead of subject here because subject might have been only made
  // to look like a sequential string when it actually is an external string.
  __ ld(a1, MemOperand(sp, kPreviousIndexOffset));
  __ JumpIfNotSmi(a1, &runtime);
  __ ld(a3, FieldMemOperand(a3, String::kLengthOffset));
  __ Branch(&runtime, ls, a3, Operand(a1));
  __ sra(a1, a1, 32);  // Untag the Smi.

  STATIC_ASSERT(kStringEncodingMask == 4);
  STATIC_ASSERT(kOneByteStringTag == 4);
  STATIC_ASSERT(kTwoByteStringTag == 0);
  __ And(a0, a0, Operand(kStringEncodingMask));  // Non-zero for ASCII.
  __ ld(t9, FieldMemOperand(regexp_data, JSRegExp::kDataAsciiCodeOffset));
  __ sra(a3, a0, 2);  // a3 is 1 for ASCII, 0 for UC16 (used below).
  __ ld(t1, FieldMemOperand(regexp_data, JSRegExp::kDataUC16CodeOffset));
  __ movz(t9, t1, a0);  // If UC16 (a0 is 0), replace t9 w/kDataUC16CodeOffset.

  // (E) Carry on.  String handling is done.
  // t9: irregexp code
  // Check that the irregexp code has been generated for the actual string
  // encoding. If it has, the field contains a code object otherwise it contains
  // a smi (code flushing support).
  __ JumpIfSmi(t9, &runtime);

  // a1: previous index
  // a3: encoding of subject string (1 if ASCII, 0 if two_byte);
  // t9: code
  // subject: Subject string
  // regexp_data: RegExp data (FixedArray)
  // All checks done. Now push arguments for native regexp code.
  __ IncrementCounter(isolate->counters()->regexp_entry_native(),
                      1, a0, a2);

  // Isolates: note we add an additional parameter here (isolate pointer).
  const int kRegExpExecuteArguments = 9;
  const int kParameterRegisters = 4;
  __ EnterExitFrame(false, kRegExpExecuteArguments - kParameterRegisters);

  // Stack pointer now points to cell where return address is to be written.
  // Arguments are before that on the stack or in registers, meaning we
  // treat the return address as argument 5. Thus every argument after that
  // needs to be shifted back by 1. Since DirectCEntryStub will handle
  // allocating space for the c argument slots, we don't need to calculate
  // that into the argument positions on the stack. This is how the stack will
  // look (sp meaning the value of sp at this moment):
  // [sp + 5] - Argument 9
  // [sp + 4] - Argument 8
  // [sp + 3] - Argument 7
  // [sp + 2] - Argument 6
  // [sp + 1] - Argument 5
  // [sp + 0] - saved ra

  // Argument 9: Pass current isolate address.
  // CFunctionArgumentOperand handles MIPS stack argument slots.
  __ li(a0, Operand(ExternalReference::isolate_address(isolate)));
  __ st(a0, MemOperand(sp, 5 * kPointerSize));

  // Argument 8: Indicate that this is a direct call from JavaScript.
  __ li(a0, Operand(1));
  __ st(a0, MemOperand(sp, 4 * kPointerSize));

  // Argument 7: Start (high end) of backtracking stack memory area.
  __ li(a0, Operand(address_of_regexp_stack_memory_address));
  __ ld(a0, MemOperand(a0, 0));
  __ li(a2, Operand(address_of_regexp_stack_memory_size));
  __ ld(a2, MemOperand(a2, 0));
  __ add(a0, a0, a2);
  __ st(a0, MemOperand(sp, 3 * kPointerSize));

  // Argument 6: Set the number of capture registers to zero to force global
  // regexps to behave as non-global.  This does not affect non-global regexps.
  __ move(a0, zero);
  __ st(a0, MemOperand(sp, 2 * kPointerSize));

  // Argument 5: static offsets vector buffer.
  __ li(a0, Operand(
        ExternalReference::address_of_static_offsets_vector(isolate)));
  __ st(a0, MemOperand(sp, 1 * kPointerSize));

  // For arguments 4 and 3 get string length, calculate start of string data
  // and calculate the shift of the index (0 for ASCII and 1 for two byte).
  __ Addu(t2, subject, Operand(SeqString::kHeaderSize - kHeapObjectTag));
  __ Xor(a3, a3, Operand(1));  // 1 for 2-byte str, 0 for 1-byte.
  // Load the length from the original subject string from the previous stack
  // frame. Therefore we have to use fp, which points exactly to two pointer
  // sizes below the previous sp. (Because creating a new stack frame pushes
  // the previous fp onto the stack and moves up sp by 2 * kPointerSize.)
  __ ld(subject, MemOperand(fp, kSubjectOffset + 2 * kPointerSize));
  // If slice offset is not 0, load the length from the original sliced string.
  // Argument 4, a3: End of string data
  // Argument 3, a2: Start of string data
  // Prepare start and end index of the input.
  __ sll(t1, t0, a3);
  __ add(t0, t2, t1);
  __ sll(t1, a1, a3);
  __ add(a2, t0, t1);

  __ ld(t2, FieldMemOperand(subject, String::kLengthOffset));
  __ sra(t2, t2, 32);
  __ sll(t1, t2, a3);
  __ add(a3, t0, t1);
  // Argument 2 (a1): Previous index.
  // Already there

  // Argument 1 (a0): Subject string.
  __ move(a0, subject);

  // Locate the code entry and call it.
  __ Addu(t9, t9, Operand(Code::kHeaderSize - kHeapObjectTag));
  DirectCEntryStub stub;
  stub.GenerateCall(masm, t9);

  __ LeaveExitFrame(false, no_reg);

  // v0: result
  // subject: subject string (callee saved)
  // regexp_data: RegExp data (callee saved)
  // last_match_info_elements: Last match info elements (callee saved)
  // Check the result.
  Label success;
  __ Branch(&success, eq, v0, Operand(1));
  // We expect exactly one result since we force the called regexp to behave
  // as non-global.
  Label failure;
  __ Branch(&failure, eq, v0, Operand(NativeRegExpMacroAssembler::FAILURE));
  // If not exception it can only be retry. Handle that in the runtime system.
  __ Branch(&runtime, ne, v0, Operand(NativeRegExpMacroAssembler::EXCEPTION));
  // Result must now be exception. If there is no pending exception already a
  // stack overflow (on the backtrack stack) was detected in RegExp code but
  // haven't created the exception yet. Handle that in the runtime system.
  // TODO(592): Rerunning the RegExp to get the stack overflow exception.
  //__ li(a1, Operand(isolate->factory()->the_hole_value()));
  __ LoadRoot(a1, Heap::kTheHoleValueRootIndex);
  __ li(a2, Operand(ExternalReference(Isolate::kPendingExceptionAddress,
                                      isolate)));
  __ ld(v0, MemOperand(a2, 0));
  __ Branch(&runtime, eq, v0, Operand(a1));

  __ st(a1, MemOperand(a2, 0));  // Clear pending exception.

  // Check if the exception is a termination. If so, throw as uncatchable.
  __ LoadRoot(at, Heap::kTerminationExceptionRootIndex);
  Label termination_exception;
  __ Branch(&termination_exception, eq, v0, Operand(at));

  __ Throw(v0);

  __ bind(&termination_exception);
  __ ThrowUncatchable(v0);

  __ bind(&failure);
  // For failure and exception return null.
  __ li(v0, Operand(isolate->factory()->null_value()));
  __ DropAndRet(4);

  // Process the result from the native regexp code.
  __ bind(&success);
  __ ld(a1,
         FieldMemOperand(regexp_data, JSRegExp::kIrregexpCaptureCountOffset));
  // Calculate number of capture registers (number_of_captures + 1) * 2.
  // Multiplying by 2 comes for free since r1 is smi-tagged.
  STATIC_ASSERT(kSmiTag == 0);
  STATIC_ASSERT(kSmiTagSize + kSmiShiftSize == 32);
  __ Addu(a1, a1, Operand(Smi::FromInt(2)));  // a1 was a smi.
  __ sra(a1, a1, 31);

  __ ld(a0, MemOperand(sp, kLastMatchInfoOffset));
  __ JumpIfSmi(a0, &runtime);
  __ GetObjectType(a0, a2, a2);
  __ Branch(&runtime, ne, a2, Operand(JS_ARRAY_TYPE));
  // Check that the JSArray is in fast case.
  __ ld(last_match_info_elements,
        FieldMemOperand(a0, JSArray::kElementsOffset));
  __ ld(a0, FieldMemOperand(last_match_info_elements, HeapObject::kMapOffset));
  __ LoadRoot(at, Heap::kFixedArrayMapRootIndex);
  __ Branch(&runtime, ne, a0, Operand(at));
  // Check that the last match info has space for the capture registers and the
  // additional information.
  __ ld(a0,
        FieldMemOperand(last_match_info_elements, FixedArray::kLengthOffset));
  __ Addu(a2, a1, Operand(RegExpImpl::kLastMatchOverhead));
  __ sra(at, a0, 32);
  __ Branch(&runtime, gt, a2, Operand(at));

  // a1: number of capture registers
  // subject: subject string
  // Store the capture count.
  __ sll(a2, a1, kSmiTagSize + kSmiShiftSize);  // To smi.
  __ st(a2, FieldMemOperand(last_match_info_elements,
                             RegExpImpl::kLastCaptureCountOffset));
  // Store last subject and last input.
  __ st(subject,
         FieldMemOperand(last_match_info_elements,
                         RegExpImpl::kLastSubjectOffset));
  __ move(a2, subject);
  __ RecordWriteField(last_match_info_elements,
                      RegExpImpl::kLastSubjectOffset,
                      subject,
                      t3,
                      kRAHasNotBeenSaved,
                      kDontSaveFPRegs);
  __ move(subject, a2);
  __ st(subject,
         FieldMemOperand(last_match_info_elements,
                         RegExpImpl::kLastInputOffset));
  __ RecordWriteField(last_match_info_elements,
                      RegExpImpl::kLastInputOffset,
                      subject,
                      t3,
                      kRAHasNotBeenSaved,
                      kDontSaveFPRegs);

  // Get the static offsets vector filled by the native regexp code.
  ExternalReference address_of_static_offsets_vector =
      ExternalReference::address_of_static_offsets_vector(isolate);
  __ li(a2, Operand(address_of_static_offsets_vector));

  // a1: number of capture registers
  // a2: offsets vector
  Label next_capture, done;
  // Capture register counter starts from number of capture registers and
  // counts down until wrapping after zero.
  __ Addu(a0,
         last_match_info_elements,
         Operand(RegExpImpl::kFirstCaptureOffset - kHeapObjectTag));
  __ bind(&next_capture);
  __ Subu(a1, a1, Operand(1));
  __ Branch(&done, lt, a1, Operand(zero));
  // Read the value from the static offsets vector buffer.
  __ ld(a3, MemOperand(a2, 0));
  __ addli(a2, a2, kPointerSize);
  // Store the smi value in the last match info.
  __ sll(a3, a3, 32);  // Convert to Smi.
  __ st(a3, MemOperand(a0, 0));
  __ addli(a0, a0, kPointerSize);  // In branch delay slot.
  __ Branch(&next_capture);

  __ bind(&done);

  // Return last match info.
  __ ld(v0, MemOperand(sp, kLastMatchInfoOffset));
  __ DropAndRet(4);

  // Do the runtime call to execute the regexp.
  __ bind(&runtime);
  __ TailCallRuntime(Runtime::kRegExpExec, 4, 1);

  // Deferred code for string handling.
  // (6) Not a long external string?  If yes, go to (8).
  __ bind(&not_seq_nor_cons);
  // Go to (8).
  __ Branch(&not_long_external, gt, a1, Operand(kExternalStringTag));

  // (7) External string.  Make it, offset-wise, look like a sequential string.
  __ bind(&external_string);
  __ ld(a0, FieldMemOperand(subject, HeapObject::kMapOffset));
  __ ld1u(a0, FieldMemOperand(a0, Map::kInstanceTypeOffset));
  if (FLAG_debug_code) {
    // Assert that we do not have a cons or slice (indirect strings) here.
    // Sequential strings have already been ruled out.
    __ And(at, a0, Operand(kIsIndirectStringMask));
    __ Assert(eq,
              "external string expected, but not found",
              at,
              Operand(zero));
  }
  __ ld(subject,
        FieldMemOperand(subject, ExternalString::kResourceDataOffset));
  // Move the pointer so that offset-wise, it looks like a sequential string.
  STATIC_ASSERT(SeqTwoByteString::kHeaderSize == SeqOneByteString::kHeaderSize);
  __ Subu(subject,
          subject,
          SeqTwoByteString::kHeaderSize - kHeapObjectTag);
  __ jmp(&seq_string);    // Go to (5).

  // (8) Short external string or not a string?  If yes, bail out to runtime.
  __ bind(&not_long_external);
  STATIC_ASSERT(kNotStringTag != 0 && kShortExternalStringTag !=0);
  __ And(at, a1, Operand(kIsNotStringMask | kShortExternalStringMask));
  __ Branch(&runtime, ne, at, Operand(zero));

  // (9) Sliced string.  Replace subject with parent.  Go to (4).
  // Load offset into t0 and replace subject string with parent.
  __ ld(t0, FieldMemOperand(subject, SlicedString::kOffsetOffset));
  __ sra(t0, t0, 32);
  __ ld(subject, FieldMemOperand(subject, SlicedString::kParentOffset));
  __ jmp(&check_underlying);  // Go to (4).
#endif  // V8_INTERPRETED_REGEXP
}


void RegExpConstructResultStub::Generate(MacroAssembler* masm) {
  const int kMaxInlineLength = 100;
  Label slowcase;
  Label done;
  __ ld(a1, MemOperand(sp, kPointerSize * 2));
  STATIC_ASSERT(kSmiTag == 0);
  STATIC_ASSERT(kSmiTagSize == 1);
  __ JumpIfNotSmi(a1, &slowcase);
  __ Branch(&slowcase, hi, a1, Operand(Smi::FromInt(kMaxInlineLength)));
  // Smi-tagging is equivalent to multiplying by 2.
  // Allocate RegExpResult followed by FixedArray with size in ebx.
  // JSArray:   [Map][empty properties][Elements][Length-smi][index][input]
  // Elements:  [Map][Length][..elements..]
  // Size of JSArray with two in-object properties and the header of a
  // FixedArray.
  int objects_size =
      (JSRegExpResult::kSize + FixedArray::kHeaderSize) / kPointerSize;
  __ sra(t1, a1, kSmiTagSize + kSmiShiftSize);
  __ Addu(a2, t1, Operand(objects_size));
  __ Allocate(
      a2,  // In: Size, in words.
      v0,  // Out: Start of allocation (tagged).
      a3,  // Scratch register.
      t0,  // Scratch register.
      &slowcase,
      static_cast<AllocationFlags>(TAG_OBJECT | SIZE_IN_WORDS));
  // v0: Start of allocated area, object-tagged.
  // a1: Number of elements in array, as smi.
  // t1: Number of elements, untagged.

  // Set JSArray map to global.regexp_result_map().
  // Set empty properties FixedArray.
  // Set elements to point to FixedArray allocated right after the JSArray.
  // Interleave operations for better latency.
  __ ld(a2, ContextOperand(cp, Context::GLOBAL_OBJECT_INDEX));
  __ Addu(a3, v0, Operand(JSRegExpResult::kSize));
  __ li(t0, Operand(masm->isolate()->factory()->empty_fixed_array()));
  __ ld(a2, FieldMemOperand(a2, GlobalObject::kNativeContextOffset));
  __ st(a3, FieldMemOperand(v0, JSObject::kElementsOffset));
  __ ld(a2, ContextOperand(a2, Context::REGEXP_RESULT_MAP_INDEX));
  __ st(t0, FieldMemOperand(v0, JSObject::kPropertiesOffset));
  __ st(a2, FieldMemOperand(v0, HeapObject::kMapOffset));

  // Set input, index and length fields from arguments.
  __ ld(a1, MemOperand(sp, kPointerSize * 0));
  __ ld(a2, MemOperand(sp, kPointerSize * 1));
  __ ld(t2, MemOperand(sp, kPointerSize * 2));
  __ st(a1, FieldMemOperand(v0, JSRegExpResult::kInputOffset));
  __ st(a2, FieldMemOperand(v0, JSRegExpResult::kIndexOffset));
  __ st(t2, FieldMemOperand(v0, JSArray::kLengthOffset));

  // Fill out the elements FixedArray.
  // v0: JSArray, tagged.
  // a3: FixedArray, tagged.
  // t1: Number of elements in array, untagged.

  // Set map.
  __ li(a2, Operand(masm->isolate()->factory()->fixed_array_map()));
  __ st(a2, FieldMemOperand(a3, HeapObject::kMapOffset));
  // Set FixedArray length.
  __ sll(t2, t1, 32);
  __ st(t2, FieldMemOperand(a3, FixedArray::kLengthOffset));
  // Fill contents of fixed-array with undefined.
  __ LoadRoot(a2, Heap::kUndefinedValueRootIndex);
  __ Addu(a3, a3, Operand(FixedArray::kHeaderSize - kHeapObjectTag));
  // Fill fixed array elements with undefined.
  // v0: JSArray, tagged.
  // a2: undefined.
  // a3: Start of elements in FixedArray.
  // t1: Number of elements to fill.
  Label loop;
  __ sll(t1, t1, kPointerSizeLog2);  // Convert num elements to num bytes.
  __ add(t1, t1, a3);  // Point past last element to store.
  __ bind(&loop);
  __ Branch(&done, ge, a3, Operand(t1));  // Break when a3 past end of elem.
  __ st(a2, MemOperand(a3));
  __ addli(a3, a3, kPointerSize);  // In branch delay slot.
  __ Branch(&loop);

  __ bind(&done);
  __ DropAndRet(3);

  __ bind(&slowcase);
  __ TailCallRuntime(Runtime::kRegExpConstructResult, 3, 1);
}


static void GenerateRecordCallTargetNoArray(MacroAssembler* masm) {
  // Cache the called function in a global property cell.  Cache states
  // are uninitialized, monomorphic (indicated by a JSFunction), and
  // megamorphic.
  // a1 : the function to call
  // a2 : cache cell for call target
  ASSERT(!FLAG_optimize_constructed_arrays);
  Label done;

  ASSERT_EQ(*TypeFeedbackCells::MegamorphicSentinel(masm->isolate()),
            masm->isolate()->heap()->undefined_value());
  ASSERT_EQ(*TypeFeedbackCells::UninitializedSentinel(masm->isolate()),
            masm->isolate()->heap()->the_hole_value());

  // Load the cache state into a3.
  __ ld(a3, FieldMemOperand(a2, JSGlobalPropertyCell::kValueOffset));

  // A monomorphic cache hit or an already megamorphic state: invoke the
  // function without changing the state.
  __ Branch(&done, eq, a3, Operand(a1));
  __ LoadRoot(at, Heap::kUndefinedValueRootIndex);
  __ Branch(&done, eq, a3, Operand(at));

  // A monomorphic miss (i.e, here the cache is not uninitialized) goes
  // megamorphic.
  __ LoadRoot(at2, Heap::kTheHoleValueRootIndex);

  // An uninitialized cache is patched with the function.
  // Store a1 in the delay slot. This may or may not get overwritten depending
  // on the result of the comparison.
  __ st(a1, FieldMemOperand(a2, JSGlobalPropertyCell::kValueOffset));

  __ Branch(&done, eq, a3, Operand(at2));
  // No need for a write barrier here - cells are rescanned.

  // MegamorphicSentinel is an immortal immovable object (undefined) so no
  // write-barrier is needed.
  __ LoadRoot(at2, Heap::kUndefinedValueRootIndex);
  __ st(at2, FieldMemOperand(a2, JSGlobalPropertyCell::kValueOffset));

  __ bind(&done);
}


static void GenerateRecordCallTarget(MacroAssembler* masm) {
  // Cache the called function in a global property cell.  Cache states
  // are uninitialized, monomorphic (indicated by a JSFunction), and
  // megamorphic.
  // a1 : the function to call
  // a2 : cache cell for call target
  ASSERT(FLAG_optimize_constructed_arrays);
  Label initialize, done, miss, megamorphic, not_array_function;

  ASSERT_EQ(*TypeFeedbackCells::MegamorphicSentinel(masm->isolate()),
            masm->isolate()->heap()->undefined_value());
  ASSERT_EQ(*TypeFeedbackCells::UninitializedSentinel(masm->isolate()),
            masm->isolate()->heap()->the_hole_value());

  // Load the cache state into a3.
  __ ld(a3, FieldMemOperand(a2, JSGlobalPropertyCell::kValueOffset));

  // A monomorphic cache hit or an already megamorphic state: invoke the
  // function without changing the state.
  __ Branch(&done, eq, a3, Operand(a1));
  __ LoadRoot(at, Heap::kUndefinedValueRootIndex);
  __ Branch(&done, eq, a3, Operand(at));

  // Special handling of the Array() function, which caches not only the
  // monomorphic Array function but the initial ElementsKind with special
  // sentinels
  Handle<Object> terminal_kind_sentinel =
      TypeFeedbackCells::MonomorphicArraySentinel(masm->isolate(),
                                                  LAST_FAST_ELEMENTS_KIND);
  __ JumpIfNotSmi(a3, &miss);
  __ Branch(&miss, gt, a3, Operand(terminal_kind_sentinel));
  // Make sure the function is the Array() function
  __ LoadArrayFunction(a3);
  __ Branch(&megamorphic, ne, a1, Operand(a3));
  __ jmp(&done);

  __ bind(&miss);

  // A monomorphic miss (i.e, here the cache is not uninitialized) goes
  // megamorphic.
  __ LoadRoot(at, Heap::kTheHoleValueRootIndex);
  __ Branch(&initialize, eq, a3, Operand(at));
  // MegamorphicSentinel is an immortal immovable object (undefined) so no
  // write-barrier is needed.
  __ bind(&megamorphic);
  __ LoadRoot(at2, Heap::kUndefinedValueRootIndex);
  __ st(at2, FieldMemOperand(a2, JSGlobalPropertyCell::kValueOffset));
  __ jmp(&done);

  // An uninitialized cache is patched with the function or sentinel to
  // indicate the ElementsKind if function is the Array constructor.
  __ bind(&initialize);
  // Make sure the function is the Array() function
  __ LoadArrayFunction(a3);
  __ Branch(&not_array_function, ne, a1, Operand(a3));

  // The target function is the Array constructor, install a sentinel value in
  // the constructor's type info cell that will track the initial ElementsKind
  // that should be used for the array when its constructed.
  Handle<Object> initial_kind_sentinel =
      TypeFeedbackCells::MonomorphicArraySentinel(masm->isolate(),
          GetInitialFastElementsKind());
  __ li(a3, Operand(initial_kind_sentinel));
  __ st(a3, FieldMemOperand(a2, JSGlobalPropertyCell::kValueOffset));
  __ Branch(&done);

  __ bind(&not_array_function);
  __ st(a1, FieldMemOperand(a2, JSGlobalPropertyCell::kValueOffset));
  // No need for a write barrier here - cells are rescanned.

  __ bind(&done);
}

void CallFunctionStub::Generate(MacroAssembler* masm) {
  // a1 : the function to call
  // a2 : cache cell for call target
  Label slow, non_function;

  // The receiver might implicitly be the global object. This is
  // indicated by passing the hole as the receiver to the call
  // function stub.
  if (ReceiverMightBeImplicit()) {
    Label call;
    // Get the receiver from the stack.
    // function, receiver [, arguments]
    __ ld(t0, MemOperand(sp, argc_ * kPointerSize));
    // Call as function is indicated with the hole.
    __ LoadRoot(at, Heap::kTheHoleValueRootIndex);
    __ Branch(&call, ne, t0, Operand(at));
    // Patch the receiver on the stack with the global receiver object.
    __ ld(a3,
          MemOperand(cp, Context::SlotOffset(Context::GLOBAL_OBJECT_INDEX)));
    __ ld(a3, FieldMemOperand(a3, GlobalObject::kGlobalReceiverOffset));
    __ st(a3, MemOperand(sp, argc_ * kPointerSize));
    __ bind(&call);
  }

  // Check that the function is really a JavaScript function.
  // a1: pushed function (to be verified)
  __ JumpIfSmi(a1, &non_function);
  // Get the map of the function object.
  __ GetObjectType(a1, a3, a3);
  __ Branch(&slow, ne, a3, Operand(JS_FUNCTION_TYPE));

  if (RecordCallTarget()) {
    if (FLAG_optimize_constructed_arrays) {
      GenerateRecordCallTarget(masm);
    } else {
      GenerateRecordCallTargetNoArray(masm);
    }
  }

  // Fast-case: Invoke the function now.
  // a1: pushed function
  ParameterCount actual(argc_);

  if (ReceiverMightBeImplicit()) {
    Label call_as_function;
    __ LoadRoot(at, Heap::kTheHoleValueRootIndex);
    __ Branch(&call_as_function, eq, t0, Operand(at));
    __ InvokeFunction(a1,
                      actual,
                      JUMP_FUNCTION,
                      NullCallWrapper(),
                      CALL_AS_METHOD);
    __ bind(&call_as_function);
  }
  __ InvokeFunction(a1,
                    actual,
                    JUMP_FUNCTION,
                    NullCallWrapper(),
                    CALL_AS_FUNCTION);

  // Slow-case: Non-function called.
  __ bind(&slow);
  if (RecordCallTarget()) {
    // If there is a call target cache, mark it megamorphic in the
    // non-function case.  MegamorphicSentinel is an immortal immovable
    // object (undefined) so no write barrier is needed.
    ASSERT_EQ(*TypeFeedbackCells::MegamorphicSentinel(masm->isolate()),
              masm->isolate()->heap()->undefined_value());
    __ LoadRoot(at2, Heap::kUndefinedValueRootIndex);
    __ st(at2, FieldMemOperand(a2, JSGlobalPropertyCell::kValueOffset));
  }
  // Check for function proxy.
  __ Branch(&non_function, ne, a3, Operand(JS_FUNCTION_PROXY_TYPE));
  __ push(a1);  // Put proxy as additional argument.
  __ li(a0, Operand(argc_ + 1, RelocInfo::NONE32));
  __ li(a2, Operand(0, RelocInfo::NONE32));
  __ GetBuiltinEntry(a3, Builtins::CALL_FUNCTION_PROXY);
  __ SetCallKind(t1, CALL_AS_METHOD);
  {
    Handle<Code> adaptor =
      masm->isolate()->builtins()->ArgumentsAdaptorTrampoline();
    __ Jump(adaptor, RelocInfo::CODE_TARGET);
  }

  // CALL_NON_FUNCTION expects the non-function callee as receiver (instead
  // of the original receiver from the call site).
  __ bind(&non_function);
  __ st(a1, MemOperand(sp, argc_ * kPointerSize));
  __ li(a0, Operand(argc_));  // Set up the number of arguments.
  __ move(a2, zero);
  __ GetBuiltinEntry(a3, Builtins::CALL_NON_FUNCTION);
  __ SetCallKind(t1, CALL_AS_METHOD);
  __ Jump(masm->isolate()->builtins()->ArgumentsAdaptorTrampoline(),
          RelocInfo::CODE_TARGET);
}

void CallConstructStub::Generate(MacroAssembler* masm) {
  // a0 : number of arguments
  // a1 : the function to call
  // a2 : cache cell for call target
  Label slow, non_function_call;

  // Check that the function is not a smi.
  __ JumpIfSmi(a1, &non_function_call);
  // Check that the function is a JSFunction.
  __ GetObjectType(a1, a3, a3);
  __ Branch(&slow, ne, a3, Operand(JS_FUNCTION_TYPE));

  if (RecordCallTarget()) {
    if (FLAG_optimize_constructed_arrays) {
      GenerateRecordCallTarget(masm);
    } else {
      GenerateRecordCallTargetNoArray(masm);
    }
  }

  // Jump to the function-specific construct stub.
  Register jmp_reg = FLAG_optimize_constructed_arrays ? a3 : a2;
  __ ld(jmp_reg, FieldMemOperand(a1, JSFunction::kSharedFunctionInfoOffset));
  __ ld(jmp_reg, FieldMemOperand(jmp_reg,
                                 SharedFunctionInfo::kConstructStubOffset));
  __ Addu(at, jmp_reg, Operand(Code::kHeaderSize - kHeapObjectTag));
  __ Jump(at);

  // a0: number of arguments
  // a1: called object
  // a3: object type
  Label do_call;
  __ bind(&slow);
  __ Branch(&non_function_call, ne, a3, Operand(JS_FUNCTION_PROXY_TYPE));
  __ GetBuiltinEntry(a3, Builtins::CALL_FUNCTION_PROXY_AS_CONSTRUCTOR);
  __ jmp(&do_call);

  __ bind(&non_function_call);
  __ GetBuiltinEntry(a3, Builtins::CALL_NON_FUNCTION_AS_CONSTRUCTOR);
  __ bind(&do_call);
  // Set expected number of arguments to zero (not changing r0).
  __ li(a2, Operand(0, RelocInfo::NONE32));
  __ SetCallKind(t1, CALL_AS_METHOD);
  __ Jump(masm->isolate()->builtins()->ArgumentsAdaptorTrampoline(),
          RelocInfo::CODE_TARGET);
}



// StringCharCodeAtGenerator.
void StringCharCodeAtGenerator::GenerateFast(MacroAssembler* masm) {
  Label flat_string;
  Label ascii_string;
  Label got_char_code;
  Label sliced_string;

  ASSERT(!t0.is(index_));
  ASSERT(!t0.is(result_));
  ASSERT(!t0.is(object_));

  // If the receiver is a smi trigger the non-string case.
  __ JumpIfSmi(object_, receiver_not_string_);

  // Fetch the instance type of the receiver into result register.
  __ ld(result_, FieldMemOperand(object_, HeapObject::kMapOffset));
  __ ld1u(result_, FieldMemOperand(result_, Map::kInstanceTypeOffset));
  // If the receiver is not a string trigger the non-string case.
  __ And(t0, result_, Operand(kIsNotStringMask));
  __ Branch(receiver_not_string_, ne, t0, Operand(zero));

  // If the index is non-smi trigger the non-smi case.
  __ JumpIfNotSmi(index_, &index_not_smi_);

  __ bind(&got_smi_index_);

  // Check for index out of range.
  __ ld(t0, FieldMemOperand(object_, String::kLengthOffset));
  __ Branch(index_out_of_range_, ls, t0, Operand(index_));

  __ sra(index_, index_, 32);

  StringCharLoadGenerator::Generate(masm,
                                    object_,
                                    index_,
                                    result_,
                                    &call_runtime_);

  __ sll(result_, result_, 32);
  __ bind(&exit_);
}


void StringCharCodeAtGenerator::GenerateSlow(
    MacroAssembler* masm,
    const RuntimeCallHelper& call_helper) {
  __ Abort("Unexpected fallthrough to CharCodeAt slow case");

  // Index is not a smi.
  __ bind(&index_not_smi_);
  // If index is a heap number, try converting it to an integer.
  __ CheckMap(index_,
              result_,
              Heap::kHeapNumberMapRootIndex,
              index_not_number_,
              DONT_DO_SMI_CHECK);
  call_helper.BeforeCall(masm);
  // Consumed by runtime conversion function:
  __ Push(object_, index_);
  if (index_flags_ == STRING_INDEX_IS_NUMBER) {
    __ CallRuntime(Runtime::kNumberToIntegerMapMinusZero, 1);
  } else {
    ASSERT(index_flags_ == STRING_INDEX_IS_ARRAY_INDEX);
    // NumberToSmi discards numbers that are not exact integers.
    __ CallRuntime(Runtime::kNumberToSmi, 1);
  }

  // Save the conversion result before the pop instructions below
  // have a chance to overwrite it.

  __ Move(index_, v0);
  __ pop(object_);
  // Reload the instance type.
  __ ld(result_, FieldMemOperand(object_, HeapObject::kMapOffset));
  __ ld1u(result_, FieldMemOperand(result_, Map::kInstanceTypeOffset));
  call_helper.AfterCall(masm);
  // If index is still not a smi, it must be out of range.
  __ JumpIfNotSmi(index_, index_out_of_range_);
  // Otherwise, return to the fast path.
  __ Branch(&got_smi_index_);

  // Call runtime. We get here when the receiver is a string and the
  // index is a number, but the code of getting the actual character
  // is too complex (e.g., when the string needs to be flattened).
  __ bind(&call_runtime_);
  call_helper.BeforeCall(masm);
  __ sll(index_, index_, 32);
  __ Push(object_, index_);
  __ CallRuntime(Runtime::kStringCharCodeAt, 2);

  __ Move(result_, v0);

  call_helper.AfterCall(masm);
  __ jmp(&exit_);

  __ Abort("Unexpected fallthrough from CharCodeAt slow case");
}


// -------------------------------------------------------------------------
// StringCharFromCodeGenerator

void StringCharFromCodeGenerator::GenerateFast(MacroAssembler* masm) {
  // Fast case of Heap::LookupSingleCharacterStringFromCode.

  ASSERT(!t0.is(result_));
  ASSERT(!t0.is(code_));

  STATIC_ASSERT(kSmiTag == 0);
  STATIC_ASSERT(kSmiShiftSize == 31);
  ASSERT(IsPowerOf2(String::kMaxOneByteCharCode + 1));
  __ And(t0,
         code_,
         Operand(1L | (static_cast<int64_t>(~String::kMaxOneByteCharCode) << 32)));
  __ Branch(&slow_case_, ne, t0, Operand(zero));

  __ LoadRoot(result_, Heap::kSingleCharacterStringCacheRootIndex);
  // At this point code register contains smi tagged ASCII char code.
  STATIC_ASSERT(kSmiTag == 0);
  __ sra(t0, code_, 32);
  __ sll(t0, t0, kPointerSizeLog2);
  __ Addu(result_, result_, t0);
  __ ld(result_, FieldMemOperand(result_, FixedArray::kHeaderSize));
  __ LoadRoot(t0, Heap::kUndefinedValueRootIndex);
  __ Branch(&slow_case_, eq, result_, Operand(t0));
  __ bind(&exit_);
}


void StringCharFromCodeGenerator::GenerateSlow(
    MacroAssembler* masm,
    const RuntimeCallHelper& call_helper) {
  __ Abort("Unexpected fallthrough to CharFromCode slow case");

  __ bind(&slow_case_);
  call_helper.BeforeCall(masm);
  __ push(code_);
  __ CallRuntime(Runtime::kCharFromCode, 1);
  __ Move(result_, v0);

  call_helper.AfterCall(masm);
  __ Branch(&exit_);

  __ Abort("Unexpected fallthrough from CharFromCode slow case");
}


void StringHelper::GenerateCopyCharacters(MacroAssembler* masm,
                                          Register dest,
                                          Register src,
                                          Register count,
                                          Register scratch,
                                          bool ascii) {
  Label loop;
  Label done;
  // This loop just copies one character at a time, as it is only used for
  // very short strings.
  if (!ascii) {
    __ add(count, count, count);
  }
  __ Branch(&done, eq, count, Operand(zero));
  __ add(count, dest, count);  // Count now points to the last dest byte.

  __ bind(&loop);
  __ ld1u(scratch, MemOperand(src));
  __ addli(src, src, 1);
  __ st1(scratch, MemOperand(dest));
  __ addli(dest, dest, 1);
  __ Branch(&loop, lt, dest, Operand(count));

  __ bind(&done);
}


enum CopyCharactersFlags {
  COPY_ASCII = 1,
  DEST_ALWAYS_ALIGNED = 2
};


void StringHelper::GenerateCopyCharactersLong(MacroAssembler* masm,
                                              Register dest,
                                              Register src,
                                              Register count,
                                              Register scratch1,
                                              Register scratch2,
                                              Register scratch3,
                                              Register scratch4,
                                              Register scratch5,
                                              int flags) {
  bool ascii = (flags & COPY_ASCII) != 0;
  bool dest_always_aligned = (flags & DEST_ALWAYS_ALIGNED) != 0;

  if (dest_always_aligned && FLAG_debug_code) {
    // Check that destination is actually word aligned if the flag says
    // that it is.
    __ And(scratch4, dest, Operand(kPointerAlignmentMask));
    __ Check(eq,
             "Destination of copy not aligned.",
             scratch4,
             Operand(zero));
  }

  const int kReadAlignment = 8;
  const int kReadAlignmentMask = kReadAlignment - 1;
  // Ensure that reading an entire aligned word containing the last character
  // of a string will not read outside the allocated area (because we pad up
  // to kObjectAlignment).
  STATIC_ASSERT(kObjectAlignment >= kReadAlignment);
  // Assumes word reads and writes are little endian.
  // Nothing to do for zero characters.
  Label done;

  if (!ascii) {
    __ add(count, count, count);
  }
  __ Branch(&done, eq, count, Operand(zero));

  Label byte_loop;
  // Must copy at least sixteen bytes, otherwise just do it one byte at a time.
  __ Subu(scratch1, count, Operand(16));
  __ Addu(count, dest, Operand(count));
  Register limit = count;  // Read until src equals this.
  __ Branch(&byte_loop, lt, scratch1, Operand(zero));

  if (!dest_always_aligned) {
    // Align dest by byte copying. Copies between zero and three bytes.
    __ And(scratch4, dest, Operand(kReadAlignmentMask));
    Label dest_aligned;
    __ Branch(&dest_aligned, eq, scratch4, Operand(zero));
    Label aligned_loop;
    __ bind(&aligned_loop);
    __ ld1u(scratch1, MemOperand(src));
    __ addli(src, src, 1);
    __ st1(scratch1, MemOperand(dest));
    __ addli(dest, dest, 1);
    __ addli(scratch4, scratch4, 1);
    __ Branch(&aligned_loop, le, scratch4, Operand(kReadAlignmentMask));
    __ bind(&dest_aligned);
  }

  Label simple_loop;

  __ And(scratch4, src, Operand(kReadAlignmentMask));
  __ Branch(&simple_loop, eq, scratch4, Operand(zero));

#if 0 
  // Loop for src/dst that are not aligned the same way.
  // This loop uses lwl and lwr instructions. These instructions
  // depend on the endianness, and the implementation assumes little-endian.
  {
    Label loop;
    __ bind(&loop);
    __ lwr(scratch1, MemOperand(src));
    __ Addu(src, src, Operand(kReadAlignment));
    __ lwl(scratch1, MemOperand(src, -1));
    __ st(scratch1, MemOperand(dest));
    __ Addu(dest, dest, Operand(kReadAlignment));
    __ Subu(scratch2, limit, dest);
    __ Branch(&loop, ge, scratch2, Operand(kReadAlignment));
  }
#endif

  __ Branch(&byte_loop);

  // Simple loop.
  // Copy words from src to dest, until less than eight bytes left.
  // Both src and dest are word aligned.
  __ bind(&simple_loop);
  {
    Label loop;
    __ bind(&loop);
    __ ld(scratch1, MemOperand(src));
    __ Addu(src, src, Operand(kReadAlignment));
    __ st(scratch1, MemOperand(dest));
    __ Addu(dest, dest, Operand(kReadAlignment));
    __ Subu(scratch2, limit, dest);
    __ Branch(&loop, ge, scratch2, Operand(kReadAlignment));
  }

  // Copy bytes from src to dest until dest hits limit.
  __ bind(&byte_loop);
  // Test if dest has already reached the limit.
  __ Branch(&done, ge, dest, Operand(limit));
  __ ld1u(scratch1, MemOperand(src));
  __ addli(src, src, 1);
  __ st1(scratch1, MemOperand(dest));
  __ addli(dest, dest, 1);
  __ Branch(&byte_loop);

  __ bind(&done);
}


void StringHelper::GenerateTwoCharacterStringTableProbe(MacroAssembler* masm,
                                                        Register c1,
                                                        Register c2,
                                                        Register scratch1,
                                                        Register scratch2,
                                                        Register scratch3,
                                                        Register scratch4,
                                                        Register scratch5,
                                                        Label* not_found) {
  // Register scratch3 is the general scratch register in this function.
  Register scratch = scratch3;

  // Make sure that both characters are not digits as such strings has a
  // different hash algorithm. Don't try to look for these in the string table.
  Label not_array_index;
  __ Subu(scratch, c1, Operand(static_cast<int>('0')));
  __ Branch(&not_array_index,
            Ugreater,
            scratch,
            Operand(static_cast<int>('9' - '0')));
  __ Subu(scratch, c2, Operand(static_cast<int>('0')));

  // If check failed combine both characters into single halfword.
  // This is required by the contract of the method: code at the
  // not_found branch expects this combination in c1 register.
  Label tmp;
  __ sll(scratch1, c2, kBitsPerByte);
  __ Branch(&tmp, Ugreater, scratch, Operand(static_cast<int>('9' - '0')));
  __ Or(c1, c1, scratch1);
  __ bind(&tmp);
  __ Branch(
      not_found, Uless_equal, scratch, Operand(static_cast<int>('9' - '0')));

  __ bind(&not_array_index);
  // Calculate the two character string hash.
  Register hash = scratch1;
  StringHelper::GenerateHashInit(masm, hash, c1);
  StringHelper::GenerateHashAddCharacter(masm, hash, c2);
  StringHelper::GenerateHashGetHash(masm, hash);

  // Collect the two characters in a register.
  Register chars = c1;
  __ sll(scratch, c2, kBitsPerByte);
  __ Or(chars, chars, scratch);

  // chars: two character string, char 1 in byte 0 and char 2 in byte 1.
  // hash:  hash of two character string.

  // Load string table.
  // Load address of first element of the string table.
  Register string_table = c2;
  __ LoadRoot(string_table, Heap::kStringTableRootIndex);

  Register undefined = scratch4;
  __ LoadRoot(undefined, Heap::kUndefinedValueRootIndex);

  // Calculate capacity mask from the string table capacity.
  Register mask = scratch2;
  __ ld(mask, FieldMemOperand(string_table, StringTable::kCapacityOffset));
  __ sra(mask, mask, 32);
  __ Addu(mask, mask, -1);

  // Calculate untagged address of the first element of the string table.
  Register first_string_table_element = string_table;
  __ Addu(first_string_table_element, string_table,
         Operand(StringTable::kElementsStartOffset - kHeapObjectTag));

  // Registers.
  // chars: two character string, char 1 in byte 0 and char 2 in byte 1.
  // hash:  hash of two character string
  // mask:  capacity mask
  // first_string_table_element: address of the first element of
  //                             the string table
  // undefined: the undefined object
  // scratch: -

  // Perform a number of probes in the string table.
  const int kProbes = 4;
  Label found_in_string_table;
  Label next_probe[kProbes];
  Register candidate = scratch5;  // Scratch register contains candidate.
  for (int i = 0; i < kProbes; i++) {
    // Calculate entry in string table.
    if (i > 0) {
      __ Addu(candidate, hash, Operand(StringTable::GetProbeOffset(i)));
    } else {
      __ move(candidate, hash);
    }

    __ And(candidate, candidate, Operand(mask));

    // Load the entry from the symble table.
    STATIC_ASSERT(StringTable::kEntrySize == 1);
    __ sll(scratch, candidate, kPointerSizeLog2);
    __ Addu(scratch, scratch, first_string_table_element);
    __ ld(candidate, MemOperand(scratch));

    // If entry is undefined no string with this hash can be found.
    Label is_string;
    __ GetObjectType(candidate, scratch, scratch);
    __ Branch(&is_string, ne, scratch, Operand(ODDBALL_TYPE));

    __ Branch(not_found, eq, undefined, Operand(candidate));
    // Must be the hole (deleted entry).
    if (FLAG_debug_code) {
      __ LoadRoot(scratch, Heap::kTheHoleValueRootIndex);
      __ Assert(eq, "oddball in string table is not undefined or the hole",
          scratch, Operand(candidate));
    }
    __ jmp(&next_probe[i]);

    __ bind(&is_string);

    // Check that the candidate is a non-external ASCII string.  The instance
    // type is still in the scratch register from the CompareObjectType
    // operation.
    __ JumpIfInstanceTypeIsNotSequentialAscii(scratch, scratch, &next_probe[i]);

    // If length is not 2 the string is not a candidate.
    __ ld(scratch, FieldMemOperand(candidate, String::kLengthOffset));
    __ Branch(&next_probe[i], ne, scratch, Operand(Smi::FromInt(2)));

    // Check if the two characters match.
    // Assumes that word load is little endian.
    __ ld2u(scratch, FieldMemOperand(candidate, SeqOneByteString::kHeaderSize));
    __ Branch(&found_in_string_table, eq, chars, Operand(scratch));
    __ bind(&next_probe[i]);
  }

  // No matching 2 character string found by probing.
  __ jmp(not_found);

  // Scratch register contains result when we fall through to here.
  Register result = candidate;
  __ bind(&found_in_string_table);
  __ move(v0, result);
}


void StringHelper::GenerateHashInit(MacroAssembler* masm,
                                    Register hash,
                                    Register character) {
  // hash = seed + character + ((seed + character) << 10);
  __ LoadRoot(hash, Heap::kHashSeedRootIndex);
  // Untag smi seed and add the character.
  __ SmiUntag(hash);
  __ addx(hash, hash, character);
  __ sllx(at, hash, 10);
  __ addx(hash, hash, at);
  // hash ^= hash >> 6;
  __ srlx(at, hash, 6);
  __ xor_(hash, hash, at);
}


void StringHelper::GenerateHashAddCharacter(MacroAssembler* masm,
                                            Register hash,
                                            Register character) {
  // hash += character;
  __ addx(hash, hash, character);
  // hash += hash << 10;
  __ sllx(at, hash, 10);
  __ addx(hash, hash, at);
  // hash ^= hash >> 6;
  __ srlx(at, hash, 6);
  __ xor_(hash, hash, at);
}


void StringHelper::GenerateHashGetHash(MacroAssembler* masm,
                                       Register hash) {
  // hash += hash << 3;
  __ sllx(at, hash, 3);
  __ add(hash, hash, at);
  // hash ^= hash >> 11;
  __ srlx(at, hash, 11);
  __ xor_(hash, hash, at);
  // hash += hash << 15;
  __ sllx(at, hash, 15);
  __ addx(hash, hash, at);

  __ li(at, Operand(String::kHashBitMask));
  __ and_(hash, hash, at);

  // if (hash == 0) hash = 27;
  __ ori(at, zero, StringHasher::kZeroHash);
  __ movz(hash, at, hash);
}


void SubStringStub::Generate(MacroAssembler* masm) {
  Label runtime;
  // Stack frame on entry.
  //  ra: return address
  //  sp[0]: to
  //  sp[4]: from
  //  sp[8]: string

  // This stub is called from the native-call %_SubString(...), so
  // nothing can be assumed about the arguments. It is tested that:
  //  "string" is a sequential string,
  //  both "from" and "to" are smis, and
  //  0 <= from <= to <= string.length.
  // If any of these assumptions fail, we call the runtime system.

  const int kToOffset = 0 * kPointerSize;
  const int kFromOffset = 1 * kPointerSize;
  const int kStringOffset = 2 * kPointerSize;

  __ ld(a2, MemOperand(sp, kToOffset));
  __ ld(a3, MemOperand(sp, kFromOffset));
  STATIC_ASSERT(kFromOffset == kToOffset + 8);
  STATIC_ASSERT(kSmiTag == 0);
  STATIC_ASSERT(kSmiTagSize + kSmiShiftSize == 32);

  // Utilize delay slots. SmiUntag doesn't emit a jump, everything else is
  // safe in this case.
  __ UntagAndJumpIfNotSmi(a2, a2, &runtime);
  __ UntagAndJumpIfNotSmi(a3, a3, &runtime);
  // Both a2 and a3 are untagged integers.

  __ Branch(&runtime, lt, a3, Operand(zero));  // From < 0.

  __ Branch(&runtime, gt, a3, Operand(a2));  // Fail if from > to.
  __ Subu(a2, a2, a3);

  // Make sure first argument is a string.
  __ ld(v0, MemOperand(sp, kStringOffset));
  __ JumpIfSmi(v0, &runtime);
  __ ld(a1, FieldMemOperand(v0, HeapObject::kMapOffset));
  __ ld1u(a1, FieldMemOperand(a1, Map::kInstanceTypeOffset));
  __ And(t0, a1, Operand(kIsNotStringMask));

  __ Branch(&runtime, ne, t0, Operand(zero));

  Label single_char;
  __ Branch(&single_char, eq, a2, Operand(1));

  // Short-cut for the case of trivial substring.
  Label return_v0;
  // v0: original string
  // a2: result string length
  __ ld(t0, FieldMemOperand(v0, String::kLengthOffset));
  __ sra(t0, t0, 32);
  // Return original string.
  __ Branch(&return_v0, eq, a2, Operand(t0));
  // Longer than original string's length or negative: unsafe arguments.
  __ Branch(&runtime, hi, a2, Operand(t0));
  // Shorter than original string's length: an actual substring.

  // Deal with different string types: update the index if necessary
  // and put the underlying string into t1.
  // v0: original string
  // a1: instance type
  // a2: length
  // a3: from index (untagged)
  Label underlying_unpacked, sliced_string, seq_or_external_string;
  // If the string is not indirect, it can only be sequential or external.
  STATIC_ASSERT(kIsIndirectStringMask == (kSlicedStringTag & kConsStringTag));
  STATIC_ASSERT(kIsIndirectStringMask != 0);
  __ And(at, a1, Operand(kIsIndirectStringMask));
  // t0 is used as a scratch register and can be overwritten in either case.
  __ And(t0, a1, Operand(kSlicedNotConsMask));
  __ Branch(&seq_or_external_string, eq, at, Operand(zero));
  __ Branch(&sliced_string, ne, t0, Operand(zero));
  // Cons string.  Check whether it is flat, then fetch first part.
  __ ld(t1, FieldMemOperand(v0, ConsString::kSecondOffset));
  __ LoadRoot(t0, Heap::kempty_stringRootIndex);
  __ Branch(&runtime, ne, t1, Operand(t0));
  __ ld(t1, FieldMemOperand(v0, ConsString::kFirstOffset));
  // Update instance type.
  __ ld(a1, FieldMemOperand(t1, HeapObject::kMapOffset));
  __ ld1u(a1, FieldMemOperand(a1, Map::kInstanceTypeOffset));
  __ jmp(&underlying_unpacked);

  __ bind(&sliced_string);
  // Sliced string.  Fetch parent and correct start index by offset.
  __ ld(t1, FieldMemOperand(v0, SlicedString::kParentOffset));
  __ ld(t0, FieldMemOperand(v0, SlicedString::kOffsetOffset));
  __ sra(t0, t0, 32);  // Add offset to index.
  __ Addu(a3, a3, t0);
  // Update instance type.
  __ ld(a1, FieldMemOperand(t1, HeapObject::kMapOffset));
  __ ld1u(a1, FieldMemOperand(a1, Map::kInstanceTypeOffset));
  __ jmp(&underlying_unpacked);

  __ bind(&seq_or_external_string);
  // Sequential or external string.  Just move string to the expected register.
  __ move(t1, v0);

  __ bind(&underlying_unpacked);

  if (FLAG_string_slices) {
    Label copy_routine;
    // t1: underlying subject string
    // a1: instance type of underlying subject string
    // a2: length
    // a3: adjusted start index (untagged)
    // Short slice.  Copy instead of slicing.
    __ Branch(&copy_routine, lt, a2, Operand(SlicedString::kMinLength));
    // Allocate new sliced string.  At this point we do not reload the instance
    // type including the string encoding because we simply rely on the info
    // provided by the original string.  It does not matter if the original
    // string's encoding is wrong because we always have to recheck encoding of
    // the newly created string's parent anyways due to externalized strings.
    Label two_byte_slice, set_slice_header;
    STATIC_ASSERT((kStringEncodingMask & kOneByteStringTag) != 0);
    STATIC_ASSERT((kStringEncodingMask & kTwoByteStringTag) == 0);
    __ And(t0, a1, Operand(kStringEncodingMask));
    __ Branch(&two_byte_slice, eq, t0, Operand(zero));
    __ AllocateAsciiSlicedString(v0, a2, t2, t3, &runtime);
    __ jmp(&set_slice_header);
    __ bind(&two_byte_slice);
    __ AllocateTwoByteSlicedString(v0, a2, t2, t3, &runtime);
    __ bind(&set_slice_header);
    __ sll(a3, a3, 32);
    __ st(t1, FieldMemOperand(v0, SlicedString::kParentOffset));
    __ st(a3, FieldMemOperand(v0, SlicedString::kOffsetOffset));
    __ jmp(&return_v0);

    __ bind(&copy_routine);
  }

  // t1: underlying subject string
  // a1: instance type of underlying subject string
  // a2: length
  // a3: adjusted start index (untagged)
  Label two_byte_sequential, sequential_string, allocate_result;
  STATIC_ASSERT(kExternalStringTag != 0);
  STATIC_ASSERT(kSeqStringTag == 0);
  __ And(t0, a1, Operand(kExternalStringTag));
  __ Branch(&sequential_string, eq, t0, Operand(zero));

  // Handle external string.
  // Rule out short external strings.
  STATIC_CHECK(kShortExternalStringTag != 0);
  __ And(t0, a1, Operand(kShortExternalStringTag));
  __ Branch(&runtime, ne, t0, Operand(zero));
  __ ld(t1, FieldMemOperand(t1, ExternalString::kResourceDataOffset));
  // t1 already points to the first character of underlying string.
  __ jmp(&allocate_result);

  __ bind(&sequential_string);
  // Locate first character of underlying subject string.
  STATIC_ASSERT(SeqTwoByteString::kHeaderSize == SeqOneByteString::kHeaderSize);
  __ Addu(t1, t1, Operand(SeqOneByteString::kHeaderSize - kHeapObjectTag));

  __ bind(&allocate_result);
  // Sequential acii string.  Allocate the result.
  STATIC_ASSERT((kOneByteStringTag & kStringEncodingMask) != 0);
  __ And(t0, a1, Operand(kStringEncodingMask));
  __ Branch(&two_byte_sequential, eq, t0, Operand(zero));

  // Allocate and copy the resulting ASCII string.
  __ AllocateAsciiString(v0, a2, t0, t2, t3, &runtime);

  // Locate first character of substring to copy.
  __ Addu(t1, t1, a3);

  // Locate first character of result.
  __ Addu(a1, v0, Operand(SeqOneByteString::kHeaderSize - kHeapObjectTag));

  // v0: result string
  // a1: first character of result string
  // a2: result string length
  // t1: first character of substring to copy
  STATIC_ASSERT((SeqOneByteString::kHeaderSize & kObjectAlignmentMask) == 0);
  StringHelper::GenerateCopyCharactersLong(
      masm, a1, t1, a2, a3, t0, t2, t3, t4, COPY_ASCII | DEST_ALWAYS_ALIGNED);
  __ jmp(&return_v0);

  // Allocate and copy the resulting two-byte string.
  __ bind(&two_byte_sequential);
  __ AllocateTwoByteString(v0, a2, t0, t2, t3, &runtime);

  // Locate first character of substring to copy.
  STATIC_ASSERT(kSmiTagSize == 1 && kSmiTag == 0);
  __ sll(t0, a3, 1);
  __ Addu(t1, t1, t0);
  // Locate first character of result.
  __ Addu(a1, v0, Operand(SeqTwoByteString::kHeaderSize - kHeapObjectTag));

  // v0: result string.
  // a1: first character of result.
  // a2: result length.
  // t1: first character of substring to copy.
  STATIC_ASSERT((SeqTwoByteString::kHeaderSize & kObjectAlignmentMask) == 0);
  StringHelper::GenerateCopyCharactersLong(
      masm, a1, t1, a2, a3, t0, t2, t3, t4, DEST_ALWAYS_ALIGNED);

  __ bind(&return_v0);
  Counters* counters = masm->isolate()->counters();
  __ IncrementCounter(counters->sub_string_native(), 1, a3, t0);
  __ DropAndRet(3);

  // Just jump to runtime to create the sub string.
  __ bind(&runtime);
  __ TailCallRuntime(Runtime::kSubString, 3, 1);

  __ bind(&single_char);
  // v0: original string
  // a1: instance type
  // a2: length
  // a3: from index (untagged)
  __ SmiTag(a3, a3);
  StringCharAtGenerator generator(
      v0, a3, a2, v0, &runtime, &runtime, &runtime, STRING_INDEX_IS_NUMBER);
  generator.GenerateFast(masm);
  __ DropAndRet(3);
  generator.SkipSlow(masm, &runtime);
}


void StringCompareStub::GenerateFlatAsciiStringEquals(MacroAssembler* masm,
                                                      Register left,
                                                      Register right,
                                                      Register scratch1,
                                                      Register scratch2,
                                                      Register scratch3) {
  Register length = scratch1;

  // Compare lengths.
  Label strings_not_equal, check_zero_length;
  __ ld(length, FieldMemOperand(left, String::kLengthOffset));
  __ ld(scratch2, FieldMemOperand(right, String::kLengthOffset));
  __ Branch(&check_zero_length, eq, length, Operand(scratch2));
  __ bind(&strings_not_equal);
  __ li(v0, Operand(Smi::FromInt(NOT_EQUAL)));
  __ Ret();

  // Check if the length is zero.
  Label compare_chars;
  __ bind(&check_zero_length);
  STATIC_ASSERT(kSmiTag == 0);
  __ Branch(&compare_chars, ne, length, Operand(zero));
  __ li(v0, Operand(Smi::FromInt(EQUAL)));
  __ Ret();

  // Compare characters.
  __ bind(&compare_chars);

  GenerateAsciiCharsCompareLoop(masm,
                                left, right, length, scratch2, scratch3, at,
                                &strings_not_equal);

  // Characters are equal.
  __ li(v0, Operand(Smi::FromInt(EQUAL)));
  __ Ret();
}


void StringCompareStub::GenerateCompareFlatAsciiStrings(MacroAssembler* masm,
                                                        Register left,
                                                        Register right,
                                                        Register scratch1,
                                                        Register scratch2,
                                                        Register scratch3,
                                                        Register scratch4) {
  Label result_not_equal, compare_lengths;
  // Find minimum length and length difference.
  __ ld(scratch1, FieldMemOperand(left, String::kLengthOffset));
  __ ld(scratch2, FieldMemOperand(right, String::kLengthOffset));
  __ Subu(scratch3, scratch1, Operand(scratch2));
  Register length_delta = scratch3;
  __ cmplts(scratch4, scratch2, scratch1);
  __ movn(scratch1, scratch2, scratch4);
  Register min_length = scratch1;
  STATIC_ASSERT(kSmiTag == 0);
  __ Branch(&compare_lengths, eq, min_length, Operand(zero));

  // Compare loop.
  GenerateAsciiCharsCompareLoop(masm,
                                left, right, min_length, scratch2, scratch4, at,
                                &result_not_equal);

  // Compare lengths - strings up to min-length are equal.
  __ bind(&compare_lengths);
  ASSERT(Smi::FromInt(EQUAL) == static_cast<Smi*>(0));
  // Use length_delta as result if it's zero.
  __ move(scratch2, length_delta);
  __ move(scratch4, zero);
  __ move(v0, zero);

  __ bind(&result_not_equal);
  // Conditionally update the result based either on length_delta or
  // the last comparion performed in the loop above.
  Label ret;
  __ Branch(&ret, eq, scratch2, Operand(scratch4));
  __ li(v0, Operand(Smi::FromInt(GREATER)));
  __ Branch(&ret, gt, scratch2, Operand(scratch4));
  __ li(v0, Operand(Smi::FromInt(LESS)));
  __ bind(&ret);
  __ Ret();
}


void StringCompareStub::GenerateAsciiCharsCompareLoop(
    MacroAssembler* masm,
    Register left,
    Register right,
    Register length,
    Register scratch1,
    Register scratch2,
    Register scratch3,
    Label* chars_not_equal) {

  ASSERT(scratch3.is(at));

  // Change index to run from -length to -1 by adding length to string
  // start. This means that loop ends when index reaches zero, which
  // doesn't need an additional compare.
  __ SmiUntag(length);
  __ Addu(scratch1, length,
          Operand(SeqOneByteString::kHeaderSize - kHeapObjectTag));
  __ Addu(left, left, Operand(scratch1));
  __ Addu(right, right, Operand(scratch1));
  __ Subu(length, zero, length);
  Register index = length;  // index = -length;


  // Compare loop.
  Label loop;
  __ bind(&loop);
  __ Addu(scratch3, left, index);
  __ ld1u(scratch1, MemOperand(scratch3));
  __ Addu(scratch3, right, index);
  __ ld1u(scratch2, MemOperand(scratch3));
  __ Branch(chars_not_equal, ne, scratch1, Operand(scratch2));
  __ Addu(index, index, 1);
  __ Branch(&loop, ne, index, Operand(zero));
}


void StringCompareStub::Generate(MacroAssembler* masm) {
  Label runtime;

  Counters* counters = masm->isolate()->counters();

  // Stack frame on entry.
  //  sp[0]: right string
  //  sp[4]: left string
  __ ld(a1, MemOperand(sp, 1 * kPointerSize));  // Left.
  __ ld(a0, MemOperand(sp, 0 * kPointerSize));  // Right.

  Label not_same;
  __ Branch(&not_same, ne, a0, Operand(a1));
  STATIC_ASSERT(EQUAL == 0);
  STATIC_ASSERT(kSmiTag == 0);
  __ li(v0, Operand(Smi::FromInt(EQUAL)));
  __ IncrementCounter(counters->string_compare_native(), 1, a1, a2);
  __ DropAndRet(2);

  __ bind(&not_same);

  // Check that both objects are sequential ASCII strings.
  __ JumpIfNotBothSequentialAsciiStrings(a1, a0, a2, a3, &runtime);

  // Compare flat ASCII strings natively. Remove arguments from stack first.
  __ IncrementCounter(counters->string_compare_native(), 1, a2, a3);
  __ Addu(sp, sp, Operand(2 * kPointerSize));
  GenerateCompareFlatAsciiStrings(masm, a1, a0, a2, a3, t0, t1);

  __ bind(&runtime);
  __ TailCallRuntime(Runtime::kStringCompare, 2, 1);
}


void StringAddStub::Generate(MacroAssembler* masm) {
  Label call_runtime, call_builtin;
  Builtins::JavaScript builtin_id = Builtins::ADD;

  Counters* counters = masm->isolate()->counters();

  // Stack on entry:
  // sp[0]: second argument (right).
  // sp[8]: first argument (left).

  // Load the two arguments.
  __ ld(a0, MemOperand(sp, 1 * kPointerSize));  // First argument.
  __ ld(a1, MemOperand(sp, 0 * kPointerSize));  // Second argument.

  // Make sure that both arguments are strings if not known in advance.
  if (flags_ == NO_STRING_ADD_FLAGS) {
    __ JumpIfEitherSmi(a0, a1, &call_runtime);
    // Load instance types.
    __ ld(t0, FieldMemOperand(a0, HeapObject::kMapOffset));
    __ ld(t1, FieldMemOperand(a1, HeapObject::kMapOffset));
    __ ld1u(t0, FieldMemOperand(t0, Map::kInstanceTypeOffset));
    __ ld1u(t1, FieldMemOperand(t1, Map::kInstanceTypeOffset));
    STATIC_ASSERT(kStringTag == 0);
    // If either is not a string, go to runtime.
    __ Or(t4, t0, Operand(t1));
    __ And(t4, t4, Operand(kIsNotStringMask));
    __ Branch(&call_runtime, ne, t4, Operand(zero));
  } else {
    // Here at least one of the arguments is definitely a string.
    // We convert the one that is not known to be a string.
    if ((flags_ & NO_STRING_CHECK_LEFT_IN_STUB) == 0) {
      ASSERT((flags_ & NO_STRING_CHECK_RIGHT_IN_STUB) != 0);
      GenerateConvertArgument(
          masm, 1 * kPointerSize, a0, a2, a3, t0, t1, &call_builtin);
      builtin_id = Builtins::STRING_ADD_RIGHT;
    } else if ((flags_ & NO_STRING_CHECK_RIGHT_IN_STUB) == 0) {
      ASSERT((flags_ & NO_STRING_CHECK_LEFT_IN_STUB) != 0);
      GenerateConvertArgument(
          masm, 0 * kPointerSize, a1, a2, a3, t0, t1, &call_builtin);
      builtin_id = Builtins::STRING_ADD_LEFT;
    }
  }

  // Both arguments are strings.
  // a0: first string
  // a1: second string
  // t0: first string instance type (if flags_ == NO_STRING_ADD_FLAGS)
  // t1: second string instance type (if flags_ == NO_STRING_ADD_FLAGS)
  {
    Label strings_not_empty;
    // Check if either of the strings are empty. In that case return the other.
    // These tests use zero-length check on string-length whch is an Smi.
    // Assert that Smi::FromInt(0) is really 0.
    STATIC_ASSERT(kSmiTag == 0);
    ASSERT(Smi::FromInt(0) == 0);
    __ ld(a2, FieldMemOperand(a0, String::kLengthOffset));
    __ ld(a3, FieldMemOperand(a1, String::kLengthOffset));
    __ move(at2, a0);
    __ move(v0, a0);       // Assume we'll return first string (from a0).
    __ movz(v0, a1, a2);  // If first is empty, return second (from a1).
    __ cmplts(t4, zero, a2);   // if (a2 > 0) t4 = 1.
    __ cmplts(t5, zero, a3);   // if (a3 > 0) t5 = 1.
    __ and_(t4, t4, t5);        // Branch if both strings were non-empty.
    __ Branch(&strings_not_empty, ne, t4, Operand(zero));

    __ IncrementCounter(counters->string_add_native(), 1, a2, a3);
    __ DropAndRet(2);

    __ bind(&strings_not_empty);
    __ move(a0, at2);
  }

  // Untag both string-lengths.
  __ sra(a2, a2, 32);
  __ sra(a3, a3, 32);

  // Both strings are non-empty.
  // a0: first string
  // a1: second string
  // a2: length of first string
  // a3: length of second string
  // t0: first string instance type (if flags_ == NO_STRING_ADD_FLAGS)
  // t1: second string instance type (if flags_ == NO_STRING_ADD_FLAGS)
  // Look at the length of the result of adding the two strings.
  Label string_add_flat_result, longer_than_two;
  // Adding two lengths can't overflow.
  STATIC_ASSERT(String::kMaxLength < String::kMaxLength * 2);
  __ Addu(t2, a2, Operand(a3));
  // Use the string table when adding two one character strings, as it
  // helps later optimizations to return a string here.
  __ Branch(&longer_than_two, ne, t2, Operand(2));

  // Check that both strings are non-external ASCII strings.
  if (flags_ != NO_STRING_ADD_FLAGS) {
    __ ld(t0, FieldMemOperand(a0, HeapObject::kMapOffset));
    __ ld(t1, FieldMemOperand(a1, HeapObject::kMapOffset));
    __ ld1u(t0, FieldMemOperand(t0, Map::kInstanceTypeOffset));
    __ ld1u(t1, FieldMemOperand(t1, Map::kInstanceTypeOffset));
  }
  __ JumpIfBothInstanceTypesAreNotSequentialAscii(t0, t1, t2, t3,
                                                 &call_runtime);

  // Get the two characters forming the sub string.
  __ ld1u(a2, FieldMemOperand(a0, SeqOneByteString::kHeaderSize));
  __ ld1u(a3, FieldMemOperand(a1, SeqOneByteString::kHeaderSize));

  // Try to lookup two character string in string table. If it is not found
  // just allocate a new one.
  Label make_two_character_string;
  StringHelper::GenerateTwoCharacterStringTableProbe(
      masm, a2, a3, t2, t3, t0, t1, t5, &make_two_character_string);
  __ IncrementCounter(counters->string_add_native(), 1, a2, a3);
  __ DropAndRet(2);

  __ bind(&make_two_character_string);
  // Resulting string has length 2 and first chars of two strings
  // are combined into single halfword in a2 register.
  // So we can fill resulting string without two loops by a single
  // halfword store instruction (which assumes that processor is
  // in a little endian mode).
  __ li(t2, Operand(2));
  __ AllocateAsciiString(v0, t2, t0, t1, t5, &call_runtime);
  __ st2(a2, FieldMemOperand(v0, SeqOneByteString::kHeaderSize));
  __ IncrementCounter(counters->string_add_native(), 1, a2, a3);
  __ DropAndRet(2);

  __ bind(&longer_than_two);
  // Check if resulting string will be flat.
  __ Branch(&string_add_flat_result, lt, t2, Operand(ConsString::kMinLength));
  // Handle exceptionally long strings in the runtime system.
  STATIC_ASSERT((String::kMaxLength & 0x80000000) == 0);
  ASSERT(IsPowerOf2(String::kMaxLength + 1));
  // kMaxLength + 1 is representable as shifted literal, kMaxLength is not.
  __ Branch(&call_runtime, hs, t2, Operand(String::kMaxLength + 1));

  // If result is not supposed to be flat, allocate a cons string object.
  // If both strings are ASCII the result is an ASCII cons string.
  if (flags_ != NO_STRING_ADD_FLAGS) {
    __ ld(t0, FieldMemOperand(a0, HeapObject::kMapOffset));
    __ ld(t1, FieldMemOperand(a1, HeapObject::kMapOffset));
    __ ld1u(t0, FieldMemOperand(t0, Map::kInstanceTypeOffset));
    __ ld1u(t1, FieldMemOperand(t1, Map::kInstanceTypeOffset));
  }
  Label non_ascii, allocated, ascii_data;
  STATIC_ASSERT(kTwoByteStringTag == 0);
  // Branch to non_ascii if either string-encoding field is zero (non-ASCII).
  __ And(t4, t0, Operand(t1));
  __ And(t4, t4, Operand(kStringEncodingMask));
  __ Branch(&non_ascii, eq, t4, Operand(zero));

  // Allocate an ASCII cons string.
  __ bind(&ascii_data);
  __ move(t6, a0);
  __ AllocateAsciiConsString(v0, t2, t0, t1, &call_runtime);
  __ bind(&allocated);
  // Fill the fields of the cons string.
  __ st(t6, FieldMemOperand(v0, ConsString::kFirstOffset));
  __ st(a1, FieldMemOperand(v0, ConsString::kSecondOffset));

  __ IncrementCounter(counters->string_add_native(), 1, a2, a3);
  __ DropAndRet(2);

  __ bind(&non_ascii);
  // At least one of the strings is two-byte. Check whether it happens
  // to contain only one byte characters.
  // t0: first instance type.
  // t1: second instance type.
  // Branch to if _both_ instances have kOneByteDataHintMask set.
  __ And(at, t0, Operand(kOneByteDataHintMask));
  __ and_(at, at, t1);
  __ Branch(&ascii_data, ne, at, Operand(zero));
  __ Xor(t0, t0, Operand(t1));
  STATIC_ASSERT(kOneByteStringTag != 0 && kOneByteDataHintTag != 0);
  __ And(t0, t0, Operand(kOneByteStringTag | kOneByteDataHintTag));
  __ Branch(&ascii_data, eq, t0,
      Operand(kOneByteStringTag | kOneByteDataHintTag));

  // Save a0 which is still alive. The following Allocate will clobber it.
  __ move(t6, a0);
  // Allocate a two byte cons string.
  __ AllocateTwoByteConsString(v0, t2, t0, t1, &call_runtime);
  __ Branch(&allocated);

  // We cannot encounter sliced strings or cons strings here since:
  STATIC_ASSERT(SlicedString::kMinLength >= ConsString::kMinLength);
  // Handle creating a flat result from either external or sequential strings.
  // Locate the first characters' locations.
  // a0: first string
  // a1: second string
  // a2: length of first string
  // a3: length of second string
  // t0: first string instance type (if flags_ == NO_STRING_ADD_FLAGS)
  // t1: second string instance type (if flags_ == NO_STRING_ADD_FLAGS)
  // t2: sum of lengths.
  Label first_prepared, second_prepared;
  __ bind(&string_add_flat_result);
  if (flags_ != NO_STRING_ADD_FLAGS) {
    __ ld(t0, FieldMemOperand(a0, HeapObject::kMapOffset));
    __ ld(t1, FieldMemOperand(a1, HeapObject::kMapOffset));
    __ ld1u(t0, FieldMemOperand(t0, Map::kInstanceTypeOffset));
    __ ld1u(t1, FieldMemOperand(t1, Map::kInstanceTypeOffset));
  }
  // Check whether both strings have same encoding
  __ Xor(t3, t0, Operand(t1));
  __ And(t3, t3, Operand(kStringEncodingMask));
  __ Branch(&call_runtime, ne, t3, Operand(zero));

  STATIC_ASSERT(kSeqStringTag == 0);
  __ And(t4, t0, Operand(kStringRepresentationMask));

  STATIC_ASSERT(SeqOneByteString::kHeaderSize == SeqTwoByteString::kHeaderSize);
  Label skip_first_add;
  __ Branch(&skip_first_add, ne, t4, Operand(zero));
  __ addli(t3, a0, SeqOneByteString::kHeaderSize - kHeapObjectTag);
  __ Branch(&first_prepared);
  __ bind(&skip_first_add);
  // External string: rule out short external string and load string resource.
  STATIC_ASSERT(kShortExternalStringTag != 0);
  __ And(t4, t0, Operand(kShortExternalStringMask));
  __ Branch(&call_runtime, ne, t4, Operand(zero));
  __ ld(t3, FieldMemOperand(a0, ExternalString::kResourceDataOffset));
  __ bind(&first_prepared);

  STATIC_ASSERT(kSeqStringTag == 0);
  __ And(t4, t1, Operand(kStringRepresentationMask));
  STATIC_ASSERT(SeqOneByteString::kHeaderSize == SeqTwoByteString::kHeaderSize);
  Label skip_second_add;
  __ Branch(&skip_second_add, ne, t4, Operand(zero));
  __ addli(a1, a1, SeqOneByteString::kHeaderSize - kHeapObjectTag);
  __ Branch(&second_prepared);
  __ bind(&skip_second_add);
  // External string: rule out short external string and load string resource.
  STATIC_ASSERT(kShortExternalStringTag != 0);
  __ And(t4, t1, Operand(kShortExternalStringMask));
  __ Branch(&call_runtime, ne, t4, Operand(zero));
  __ ld(a1, FieldMemOperand(a1, ExternalString::kResourceDataOffset));
  __ bind(&second_prepared);

  Label non_ascii_string_add_flat_result;
  // t3: first character of first string
  // a1: first character of second string
  // a2: length of first string
  // a3: length of second string
  // t2: sum of lengths.
  // Both strings have the same encoding.
  STATIC_ASSERT(kTwoByteStringTag == 0);
  __ And(t4, t1, Operand(kStringEncodingMask));
  __ Branch(&non_ascii_string_add_flat_result, eq, t4, Operand(zero));

  __ AllocateAsciiString(v0, t2, t0, t1, t5, &call_runtime);
  __ Addu(t2, v0, Operand(SeqOneByteString::kHeaderSize - kHeapObjectTag));
  // v0: result string.
  // t3: first character of first string.
  // a1: first character of second string
  // a2: length of first string.
  // a3: length of second string.
  // t2: first character of result.

  StringHelper::GenerateCopyCharacters(masm, t2, t3, a2, t0, true);
  // t2: next character of result.
  StringHelper::GenerateCopyCharacters(masm, t2, a1, a3, t0, true);
  __ IncrementCounter(counters->string_add_native(), 1, a2, a3);
  __ DropAndRet(2);

  __ bind(&non_ascii_string_add_flat_result);
  __ AllocateTwoByteString(v0, t2, t0, t1, t5, &call_runtime);
  __ Addu(t2, v0, Operand(SeqTwoByteString::kHeaderSize - kHeapObjectTag));
  // v0: result string.
  // t3: first character of first string.
  // a1: first character of second string.
  // a2: length of first string.
  // a3: length of second string.
  // t2: first character of result.
  StringHelper::GenerateCopyCharacters(masm, t2, t3, a2, t0, false);
  // t2: next character of result.
  StringHelper::GenerateCopyCharacters(masm, t2, a1, a3, t0, false);

  __ IncrementCounter(counters->string_add_native(), 1, a2, a3);
  __ DropAndRet(2);

  // Just jump to runtime to add the two strings.
  __ bind(&call_runtime);
  __ TailCallRuntime(Runtime::kStringAdd, 2, 1);


  if (call_builtin.is_linked()) {
    __ bind(&call_builtin);
    __ InvokeBuiltin(builtin_id, JUMP_FUNCTION);
  }
}


void StringAddStub::GenerateConvertArgument(MacroAssembler* masm,
                                            int stack_offset,
                                            Register arg,
                                            Register scratch1,
                                            Register scratch2,
                                            Register scratch3,
                                            Register scratch4,
                                            Label* slow) {
  // First check if the argument is already a string.
  Label not_string, done;
  __ JumpIfSmi(arg, &not_string);
  __ GetObjectType(arg, scratch1, scratch1);
  __ Branch(&done, lt, scratch1, Operand(FIRST_NONSTRING_TYPE));

  // Check the number to string cache.
  Label not_cached;
  __ bind(&not_string);
  // Puts the cached result into scratch1.
  NumberToStringStub::GenerateLookupNumberStringCache(masm,
                                                      arg,
                                                      scratch1,
                                                      scratch2,
                                                      scratch3,
                                                      scratch4,
                                                      false,
                                                      &not_cached);
  __ move(arg, scratch1);
  __ st(arg, MemOperand(sp, stack_offset));
  __ jmp(&done);

  // Check if the argument is a safe string wrapper.
  __ bind(&not_cached);
  __ JumpIfSmi(arg, slow);
  __ GetObjectType(arg, scratch1, scratch2);  // map -> scratch1.
  __ Branch(slow, ne, scratch2, Operand(JS_VALUE_TYPE));
  __ ld1u(scratch2, FieldMemOperand(scratch1, Map::kBitField2Offset));
  __ li(scratch4, 1 << Map::kStringWrapperSafeForDefaultValueOf);
  __ And(scratch2, scratch2, scratch4);
  __ Branch(slow, ne, scratch2, Operand(scratch4));
  __ ld(arg, FieldMemOperand(arg, JSValue::kValueOffset));
  __ st(arg, MemOperand(sp, stack_offset));

  __ bind(&done);
}


void ICCompareStub::GenerateSmis(MacroAssembler* masm) {
  ASSERT(state_ == CompareIC::SMI);
  Label miss;
  __ Or(a2, a1, a0);
  __ JumpIfNotSmi(a2, &miss);

  if (GetCondition() == eq) {
    // For equality we do not care about the sign of the result.
    __ Subu(v0, a0, a1);
  } else {
    // Untag before subtracting to avoid handling overflow.
    __ SmiUntag(a1);
    __ SmiUntag(a0);
    __ Subu(v0, a1, a0);
  }
  __ Ret();

  __ bind(&miss);
  GenerateMiss(masm);
}


void ICCompareStub::GenerateNumbers(MacroAssembler* masm) {
  ASSERT(state_ == CompareIC::NUMBER);

  Label generic_stub;
  Label unordered, maybe_undefined1, maybe_undefined2;
  Label miss;

  if (left_ == CompareIC::SMI) {
    __ JumpIfNotSmi(a1, &miss);
  }
  if (right_ == CompareIC::SMI) {
    __ JumpIfNotSmi(a0, &miss);
  }

  __ bind(&unordered);
  __ bind(&generic_stub);
  ICCompareStub stub(op_, CompareIC::GENERIC, CompareIC::GENERIC,
                     CompareIC::GENERIC);
  __ Jump(stub.GetCode(masm->isolate()), RelocInfo::CODE_TARGET);

  __ bind(&maybe_undefined1);
  if (Token::IsOrderedRelationalCompareOp(op_)) {
    __ LoadRoot(at, Heap::kUndefinedValueRootIndex);
    __ Branch(&miss, ne, a0, Operand(at));
    __ JumpIfSmi(a1, &unordered);
    __ GetObjectType(a1, a2, a2);
    __ Branch(&maybe_undefined2, ne, a2, Operand(HEAP_NUMBER_TYPE));
    __ jmp(&unordered);
  }

  __ bind(&maybe_undefined2);
  if (Token::IsOrderedRelationalCompareOp(op_)) {
    __ LoadRoot(at, Heap::kUndefinedValueRootIndex);
    __ Branch(&unordered, eq, a1, Operand(at));
  }

  __ bind(&miss);
  GenerateMiss(masm);
}


void ICCompareStub::GenerateInternalizedStrings(MacroAssembler* masm) {
  ASSERT(state_ == CompareIC::INTERNALIZED_STRING);
  Label miss;

  // Registers containing left and right operands respectively.
  Register left = a1;
  Register right = a0;
  Register tmp1 = a2;
  Register tmp2 = a3;

  // Check that both operands are heap objects.
  __ JumpIfEitherSmi(left, right, &miss);

  // Check that both operands are internalized strings.
  __ ld(tmp1, FieldMemOperand(left, HeapObject::kMapOffset));
  __ ld(tmp2, FieldMemOperand(right, HeapObject::kMapOffset));
  __ ld1u(tmp1, FieldMemOperand(tmp1, Map::kInstanceTypeOffset));
  __ ld1u(tmp2, FieldMemOperand(tmp2, Map::kInstanceTypeOffset));
  STATIC_ASSERT(kInternalizedTag != 0);
  __ And(tmp1, tmp1, Operand(tmp2));
  __ And(tmp1, tmp1, kIsInternalizedMask);
  __ Branch(&miss, eq, tmp1, Operand(zero));
  // Make sure a0 is non-zero. At this point input operands are
  // guaranteed to be non-zero.
  ASSERT(right.is(a0));
  STATIC_ASSERT(EQUAL == 0);
  STATIC_ASSERT(kSmiTag == 0);
  __ move(v0, right);
  // Internalized strings are compared by identity.
  __ Ret(ne, left, Operand(right));
  __ li(v0, Operand(Smi::FromInt(EQUAL)));
  __ Ret();

  __ bind(&miss);
  GenerateMiss(masm);
}

void ICCompareStub::GenerateUniqueNames(MacroAssembler* masm) {
  ASSERT(state_ == CompareIC::UNIQUE_NAME);
  ASSERT(GetCondition() == eq);
  Label miss;

  // Registers containing left and right operands respectively.
  Register left = a1;
  Register right = a0;
  Register tmp1 = a2;
  Register tmp2 = a3;

  // Check that both operands are heap objects.
  __ JumpIfEitherSmi(left, right, &miss);

  // Check that both operands are unique names. This leaves the instance
  // types loaded in tmp1 and tmp2.
  STATIC_ASSERT(kInternalizedTag != 0);
  __ ld(tmp1, FieldMemOperand(left, HeapObject::kMapOffset));
  __ ld(tmp2, FieldMemOperand(right, HeapObject::kMapOffset));
  __ ld1u(tmp1, FieldMemOperand(tmp1, Map::kInstanceTypeOffset));
  __ ld1u(tmp2, FieldMemOperand(tmp2, Map::kInstanceTypeOffset));

  Label succeed1;
  __ And(at, tmp1, Operand(kIsInternalizedMask));
  __ Branch(&succeed1, ne, at, Operand(zero));
  __ Branch(&miss, ne, tmp1, Operand(SYMBOL_TYPE));
  __ bind(&succeed1);

  Label succeed2;
  __ And(at, tmp2, Operand(kIsInternalizedMask));
  __ Branch(&succeed2, ne, at, Operand(zero));
  __ Branch(&miss, ne, tmp2, Operand(SYMBOL_TYPE));
  __ bind(&succeed2);

  // Use a0 as result
  //__ move(v0, a0);

  // Unique names are compared by identity.
  Label done;
  __ Branch(&done, ne, left, Operand(right));
  // Make sure a0 is non-zero. At this point input operands are
  // guaranteed to be non-zero.
  ASSERT(right.is(a0));
  STATIC_ASSERT(EQUAL == 0);
  STATIC_ASSERT(kSmiTag == 0);
  __ li(v0, Operand(Smi::FromInt(EQUAL)));
  __ bind(&done);
  __ Ret();

  __ bind(&miss);
  GenerateMiss(masm);
}


void ICCompareStub::GenerateStrings(MacroAssembler* masm) {
  ASSERT(state_ == CompareIC::STRING);
  Label miss;

  bool equality = Token::IsEqualityOp(op_);

  // Registers containing left and right operands respectively.
  Register left = a1;
  Register right = a0;
  Register tmp1 = a2;
  Register tmp2 = a3;
  Register tmp3 = t0;
  Register tmp4 = t1;
  Register tmp5 = t2;

  // Check that both operands are heap objects.
  __ JumpIfEitherSmi(left, right, &miss);

  // Check that both operands are strings. This leaves the instance
  // types loaded in tmp1 and tmp2.
  __ ld(tmp1, FieldMemOperand(left, HeapObject::kMapOffset));
  __ ld(tmp2, FieldMemOperand(right, HeapObject::kMapOffset));
  __ ld1u(tmp1, FieldMemOperand(tmp1, Map::kInstanceTypeOffset));
  __ ld1u(tmp2, FieldMemOperand(tmp2, Map::kInstanceTypeOffset));
  STATIC_ASSERT(kNotStringTag != 0);
  __ Or(tmp3, tmp1, tmp2);
  __ And(tmp5, tmp3, Operand(kIsNotStringMask));
  __ Branch(&miss, ne, tmp5, Operand(zero));

  // Fast check for identical strings.
  Label left_ne_right;
  STATIC_ASSERT(EQUAL == 0);
  STATIC_ASSERT(kSmiTag == 0);
  __ Branch(&left_ne_right, ne, left, Operand(right));
  __ move(v0, zero);  // In the delay slot.
  __ Ret();
  __ bind(&left_ne_right);

  // Handle not identical strings.

  // Check that both strings are internalized strings. If they are, we're done
  // because we already know they are not identical.
  if (equality) {
    ASSERT(GetCondition() == eq);
    STATIC_ASSERT(kInternalizedTag != 0);
    __ And(tmp3, tmp1, Operand(tmp2));
    __ And(tmp5, tmp3, Operand(kIsInternalizedMask));
    Label is_symbol;
    __ Branch(&is_symbol, eq, tmp5, Operand(zero));
    // Make sure a0 is non-zero. At this point input operands are
    // guaranteed to be non-zero.
    ASSERT(right.is(a0));
    //__ move(v0, a0);  // In the delay slot.
    __ Ret();
    __ bind(&is_symbol);
  }

  // Check that both strings are sequential ASCII.
  Label runtime;
  __ JumpIfBothInstanceTypesAreNotSequentialAscii(
      tmp1, tmp2, tmp3, tmp4, &runtime);

  // Compare flat ASCII strings. Returns when done.
  if (equality) {
    StringCompareStub::GenerateFlatAsciiStringEquals(
        masm, left, right, tmp1, tmp2, tmp3);
  } else {
    StringCompareStub::GenerateCompareFlatAsciiStrings(
        masm, left, right, tmp1, tmp2, tmp3, tmp4);
  }

  // Handle more complex cases in runtime.
  __ bind(&runtime);
  __ Push(left, right);
  if (equality) {
    __ TailCallRuntime(Runtime::kStringEquals, 2, 1);
  } else {
    __ TailCallRuntime(Runtime::kStringCompare, 2, 1);
  }

  __ bind(&miss);
  GenerateMiss(masm);
}


void ICCompareStub::GenerateObjects(MacroAssembler* masm) {
  ASSERT(state_ == CompareIC::OBJECT);
  Label miss;
  __ And(a2, a1, Operand(a0));
  __ JumpIfSmi(a2, &miss);

  __ GetObjectType(a0, a2, a2);
  __ Branch(&miss, ne, a2, Operand(JS_OBJECT_TYPE));
  __ GetObjectType(a1, a2, a2);
  __ Branch(&miss, ne, a2, Operand(JS_OBJECT_TYPE));

  ASSERT(GetCondition() == eq);
  __ sub(v0, a0, a1);
  __ Ret();

  __ bind(&miss);
  GenerateMiss(masm);
}


void ICCompareStub::GenerateKnownObjects(MacroAssembler* masm) {
  Label miss;
  __ And(a2, a1, a0);
  __ JumpIfSmi(a2, &miss);
  __ ld(a2, FieldMemOperand(a0, HeapObject::kMapOffset));
  __ ld(a3, FieldMemOperand(a1, HeapObject::kMapOffset));
  __ Branch(&miss, ne, a2, Operand(known_map_));
  __ Branch(&miss, ne, a3, Operand(known_map_));

  __ sub(r0, r0, r1);
  __ Ret();

  __ bind(&miss);
  GenerateMiss(masm);
}

void ICCompareStub::GenerateMiss(MacroAssembler* masm) {
  {
    // Call the runtime system in a fresh internal frame.
    ExternalReference miss =
        ExternalReference(IC_Utility(IC::kCompareIC_Miss), masm->isolate());
    FrameScope scope(masm, StackFrame::INTERNAL);
    __ Push(a1, a0);
    __ push(ra);
    __ Push(a1, a0);
    __ li(t0, Operand(Smi::FromInt(op_)));
    __ addi(sp, sp, -kPointerSize);
    __ st(t0, MemOperand(sp));
    __ CallExternalReference(miss, 3);
    // Compute the entry point of the rewritten stub.
    __ Addu(a2, v0, Operand(Code::kHeaderSize - kHeapObjectTag));
    // Restore registers.
    __ Pop(a1, a0, ra);
  }
  __ Jump(a2);
}


void DirectCEntryStub::Generate(MacroAssembler* masm) {
  // No need to pop or drop anything, LeaveExitFrame will restore the old
  // stack, thus dropping the allocated space for the return value.
  // The saved ra is after the reserved stack space for the 4 args.
  __ ld(t9, MemOperand(sp, kStackLowReserve));

  if (FLAG_debug_code && FLAG_enable_slow_asserts) {
    // In case of an error the return address may point to a memory area
    // filled with kZapValue by the GC.
    // Dereference the address and check for this.
    __ ld(t0, MemOperand(t9));
    __ Assert(ne, "Received invalid return address.", t0,
        Operand(reinterpret_cast<uint64_t>(kZapValue)));
  }
  __ Jump(t9);
}


void DirectCEntryStub::GenerateCall(MacroAssembler* masm,
                                    ExternalReference function) {
  __ li(t9, Operand(function));
  this->GenerateCall(masm, t9);
}


void DirectCEntryStub::GenerateCall(MacroAssembler* masm,
                                    Register target) {
  __ Move(t9, target);
  __ AssertStackIsAligned();

  // Block the trampoline pool through the whole function to make sure the
  // number of generated instructions is constant.
  Assembler::BlockTrampolinePoolScope block_trampoline_pool(masm);

  // We need to get the current 'pc' value, which is not available on MIPS.
  masm->lnk(lr);  // ra = pc + 8.

  Label find_ra;
  masm->bind(&find_ra);
  const int kNumInstructionsToJump = 7;
  masm->addli(ra, ra, kNumInstructionsToJump * kPointerSize);
  // Push return address (accessible to GC through exit frame pc).
  // This spot for ra was reserved in EnterExitFrame.
  masm->st(ra, MemOperand(sp));
  // Allocate space for TileGX private stack zone.
  __ Subu(sp, sp, kStackLowReserve);
  intptr_t loc =
      reinterpret_cast<intptr_t>(GetCode(masm->isolate()).location());
  masm->li(ra, Operand(loc, RelocInfo::CODE_TARGET), CONSTANT_SIZE);
  // Call the function.
  masm->Jump(t9);
  // Make sure the stored 'ra' points to this position.
  ASSERT_EQ(kNumInstructionsToJump, masm->InstructionsGeneratedSince(&find_ra));
}


void NameDictionaryLookupStub::GenerateNegativeLookup(MacroAssembler* masm,
                                                      Label* miss,
                                                      Label* done,
                                                      Register receiver,
                                                      Register properties,
                                                      Handle<Name> name,
                                                      Register scratch0) {
  ASSERT(name->IsUniqueName());
  // If names of slots in range from 1 to kProbes - 1 for the hash value are
  // not equal to the name and kProbes-th slot is not used (its name is the
  // undefined value), it guarantees the hash table doesn't contain the
  // property. It's true even if some slots represent deleted properties
  // (their names are the hole value).
  for (int i = 0; i < kInlinedProbes; i++) {
    // scratch0 points to properties hash.
    // Compute the masked index: (hash + i + i * i) & mask.
    Register index = scratch0;
    // Capacity is smi 2^n.
    __ ld(index, FieldMemOperand(properties, kCapacityOffset));
    __ SmiUntag(index, index);
    __ Subu(index, index, Operand(1));
    __ And(index, index, Operand(name->Hash() + NameDictionary::GetProbeOffset(i)));

    // Scale the index by multiplying by the entry size.
    ASSERT(NameDictionary::kEntrySize == 3);
    __ sll(at, index, 1);
    __ Addu(index, index, at);

    Register entity_name = scratch0;
    // Having undefined at this place means the name is not contained.
    ASSERT_EQ(kSmiTagSize, 1);
    Register tmp = properties;
    __ sll(scratch0, index, 3);
    __ Addu(tmp, properties, scratch0);
    __ ld(entity_name, FieldMemOperand(tmp, kElementsStartOffset));

    ASSERT(!tmp.is(entity_name));
    __ LoadRoot(tmp, Heap::kUndefinedValueRootIndex);
    __ Branch(done, eq, entity_name, Operand(tmp));

    // Load the hole ready for use below:
    __ LoadRoot(tmp, Heap::kTheHoleValueRootIndex);

    // Stop if found the property.
    __ Branch(miss, eq, entity_name, Operand(Handle<Name>(name)));

    Label good;
    __ Branch(&good, eq, entity_name, Operand(tmp));

    // Check if the entry name is not a unique name.
    __ ld(entity_name, FieldMemOperand(entity_name, HeapObject::kMapOffset));
    __ ld1u(entity_name,
           FieldMemOperand(entity_name, Map::kInstanceTypeOffset));
    __ And(scratch0, entity_name, Operand(kIsInternalizedMask));
    __ Branch(&good, ne, scratch0, Operand(zero));
    __ Branch(miss, ne, entity_name, Operand(SYMBOL_TYPE));

    __ bind(&good);

    // Restore the properties.
    __ ld(properties,
          FieldMemOperand(receiver, JSObject::kPropertiesOffset));
  }

  const long spill_mask =
      (ra.bit() | t2.bit() | t1.bit() | t0.bit() | a3.bit() |
       a2.bit() | a1.bit() | a0.bit() | v0.bit());

  __ MultiPush(spill_mask);
  __ ld(a0, FieldMemOperand(receiver, JSObject::kPropertiesOffset));
  __ li(a1, Operand(Handle<Name>(name)));
  NameDictionaryLookupStub stub(NEGATIVE_LOOKUP);
  __ CallStub(&stub);
  __ move(at2, v0);
  __ MultiPop(spill_mask);

  __ Branch(done, eq, at2, Operand(zero));
  __ Branch(miss, ne, at2, Operand(zero));
}


// Probe the name dictionary in the |elements| register. Jump to the
// |done| label if a property with the given name is found. Jump to
// the |miss| label otherwise.
// If lookup was successful |scratch2| will be equal to elements + 4 * index.
void NameDictionaryLookupStub::GeneratePositiveLookup(MacroAssembler* masm,
                                                      Label* miss,
                                                      Label* done,
                                                      Register elements,
                                                      Register name,
                                                      Register scratch1,
                                                      Register scratch2) {
  ASSERT(!elements.is(scratch1));
  ASSERT(!elements.is(scratch2));
  ASSERT(!name.is(scratch1));
  ASSERT(!name.is(scratch2));

  __ AssertName(name);

  // Compute the capacity mask.
  __ ld(scratch1, FieldMemOperand(elements, kCapacityOffset));
  __ sra(scratch1, scratch1, 32);  // convert smi to int
  __ Subu(scratch1, scratch1, Operand(1));

  // Generate an unrolled loop that performs a few probes before
  // giving up. Measurements done on Gmail indicate that 2 probes
  // cover ~93% of loads from dictionaries.
  for (int i = 0; i < kInlinedProbes; i++) {
    // Compute the masked index: (hash + i + i * i) & mask.
    __ ld4u(scratch2, FieldMemOperand(name, Name::kHashFieldOffset));
    if (i > 0) {
      // Add the probe offset (i + i * i) left shifted to avoid right shifting
      // the hash in a separate instruction. The value hash + i + i * i is right
      // shifted in the following and instruction.
      ASSERT(NameDictionary::GetProbeOffset(i) <
             1 << (32 - Name::kHashFieldOffset));
      __ Addu(scratch2, scratch2, Operand(
          NameDictionary::GetProbeOffset(i) << Name::kHashShift));
    }
    __ srl(scratch2, scratch2, Name::kHashShift);
    __ And(scratch2, scratch1, scratch2);

    // Scale the index by multiplying by the element size.
    ASSERT(NameDictionary::kEntrySize == 3);
    // scratch2 = scratch2 * 3.

    __ sll(at, scratch2, 1);
    __ Addu(scratch2, scratch2, at);

    // Check if the key is identical to the name.
    __ sll(at, scratch2, 3);
    __ Addu(scratch2, elements, at);
    __ ld(at, FieldMemOperand(scratch2, kElementsStartOffset));
    __ Branch(done, eq, name, Operand(at));
  }

  const long spill_mask =
      (ra.bit() | t2.bit() | t1.bit() | t0.bit() |
       a3.bit() | a2.bit() | a1.bit() | a0.bit() | v0.bit()) &
      ~(scratch1.bit() | scratch2.bit());

  __ MultiPush(spill_mask);
  if (name.is(a0)) {
    ASSERT(!elements.is(a1));
    __ Move(a1, name);
    __ Move(a0, elements);
  } else {
    __ Move(a0, elements);
    __ Move(a1, name);
  }
  NameDictionaryLookupStub stub(POSITIVE_LOOKUP);
  __ CallStub(&stub);
  __ move(scratch2, a2);
  __ move(at2, v0);
  __ MultiPop(spill_mask);

  __ Branch(done, ne, at2, Operand(zero));
  __ Branch(miss, eq, at2, Operand(zero));
}


void NameDictionaryLookupStub::Generate(MacroAssembler* masm) {
  // This stub overrides SometimesSetsUpAFrame() to return false.  That means
  // we cannot call anything that could cause a GC from this stub.
  // Registers:
  //  result: NameDictionary to probe
  //  a1: key
  //  dictionary: NameDictionary to probe.
  //  index: will hold an index of entry if lookup is successful.
  //         might alias with result_.
  // Returns:
  //  result_ is zero if lookup failed, non zero otherwise.

  Register result = v0;
  Register dictionary = t3; // Move from a0 to avoid collision with result
  Register key = a1;
  Register index = a2;
  Register mask = a3;
  Register hash = t0;
  Register undefined = t1;
  Register entry_key = t2;

  Label in_dictionary, maybe_in_dictionary, not_in_dictionary;

  __ move(dictionary, a0);
  __ ld(mask, FieldMemOperand(dictionary, kCapacityOffset));
  __ sra(mask, mask, 32);
  __ Subu(mask, mask, Operand(1));

  __ ld4u(hash, FieldMemOperand(key, Name::kHashFieldOffset));

  __ LoadRoot(undefined, Heap::kUndefinedValueRootIndex);

  for (int i = kInlinedProbes; i < kTotalProbes; i++) {
    // Compute the masked index: (hash + i + i * i) & mask.
    // Capacity is smi 2^n.
    if (i > 0) {
      // Add the probe offset (i + i * i) left shifted to avoid right shifting
      // the hash in a separate instruction. The value hash + i + i * i is right
      // shifted in the following and instruction.
      ASSERT(NameDictionary::GetProbeOffset(i) <
             1 << (32 - Name::kHashFieldOffset));
      __ Addu(index, hash, Operand(
          NameDictionary::GetProbeOffset(i) << Name::kHashShift));
    } else {
      __ move(index, hash);
    }
    __ srl(index, index, Name::kHashShift);
    __ And(index, mask, index);

    // Scale the index by multiplying by the entry size.
    ASSERT(NameDictionary::kEntrySize == 3);
    // index *= 3.
    __ move(at, index);
    __ sll(index, index, 1);
    __ Addu(index, index, at);


    ASSERT_EQ(kSmiTagSize, 1);
    __ sll(index, index, 3);
    __ Addu(index, index, dictionary);
    __ ld(entry_key, FieldMemOperand(index, kElementsStartOffset));

    // Having undefined at this place means the name is not contained.
    __ Branch(&not_in_dictionary, eq, entry_key, Operand(undefined));

    // Stop if found the property.
    __ Branch(&in_dictionary, eq, entry_key, Operand(key));

    if (i != kTotalProbes - 1 && mode_ == NEGATIVE_LOOKUP) {
      // Check if the entry name is not a unique name.
      Label cont;
      __ ld(entry_key, FieldMemOperand(entry_key, HeapObject::kMapOffset));
      __ ld1u(entry_key,
             FieldMemOperand(entry_key, Map::kInstanceTypeOffset));
      __ And(result, entry_key, Operand(kIsInternalizedMask));
      __ Branch(&cont, ne, result, Operand(zero));
      __ Branch(&maybe_in_dictionary, ne, entry_key, Operand(SYMBOL_TYPE));
      __ bind(&cont);
    }
  }

  __ bind(&maybe_in_dictionary);
  // If we are doing negative lookup then probing failure should be
  // treated as a lookup success. For positive lookup probing failure
  // should be treated as lookup failure.
  if (mode_ == POSITIVE_LOOKUP) {
    __ move(result, zero);
    __ Ret();
  }

  __ bind(&in_dictionary);
  __ li(result, 1);
  __ Ret();

  __ bind(&not_in_dictionary);
  __ move(result, zero);
  __ Ret();
}


struct AheadOfTimeWriteBarrierStubList {
  Register object, value, address;
  RememberedSetAction action;
};

#define REG(Name) { kRegister_ ## Name ## _Code }

static const AheadOfTimeWriteBarrierStubList kAheadOfTime[] = {
  // Used in RegExpExecStub.
  { REG(s2), REG(s0), REG(t3), EMIT_REMEMBERED_SET },
  // Used in CompileArrayPushCall.
  // Also used in StoreIC::GenerateNormal via GenerateDictionaryStore.
  // Also used in KeyedStoreIC::GenerateGeneric.
  { REG(a3), REG(t0), REG(t1), EMIT_REMEMBERED_SET },
  // Used in CompileStoreGlobal.
  { REG(t0), REG(a1), REG(a2), OMIT_REMEMBERED_SET },
  // Used in StoreStubCompiler::CompileStoreField via GenerateStoreField.
  { REG(a1), REG(a2), REG(a3), EMIT_REMEMBERED_SET },
  { REG(a3), REG(a2), REG(a1), EMIT_REMEMBERED_SET },
  // Used in KeyedStoreStubCompiler::CompileStoreField via GenerateStoreField.
  { REG(a2), REG(a1), REG(a3), EMIT_REMEMBERED_SET },
  { REG(a3), REG(a1), REG(a2), EMIT_REMEMBERED_SET },
  // KeyedStoreStubCompiler::GenerateStoreFastElement.
  { REG(a3), REG(a2), REG(t0), EMIT_REMEMBERED_SET },
  { REG(a2), REG(a3), REG(t0), EMIT_REMEMBERED_SET },
  // ElementsTransitionGenerator::GenerateMapChangeElementTransition
  // and ElementsTransitionGenerator::GenerateSmiToDouble
  // and ElementsTransitionGenerator::GenerateDoubleToObject
  { REG(a2), REG(a3), REG(t5), EMIT_REMEMBERED_SET },
  { REG(a2), REG(a3), REG(t5), OMIT_REMEMBERED_SET },
  // ElementsTransitionGenerator::GenerateDoubleToObject
  { REG(t2), REG(a2), REG(a0), EMIT_REMEMBERED_SET },
  { REG(a2), REG(t2), REG(t5), EMIT_REMEMBERED_SET },
  // StoreArrayLiteralElementStub::Generate
  { REG(t1), REG(a0), REG(t2), EMIT_REMEMBERED_SET },
  // FastNewClosureStub::Generate
  { REG(a2), REG(t0), REG(a1), EMIT_REMEMBERED_SET },
  // StringAddStub::Generate
  { REG(t3), REG(t6), REG(t0), EMIT_REMEMBERED_SET },
  { REG(t3), REG(a1), REG(t0), EMIT_REMEMBERED_SET },
  { REG(t3), REG(a0), REG(t0), EMIT_REMEMBERED_SET },
  // Null termination.
  { REG(no_reg), REG(no_reg), REG(no_reg), EMIT_REMEMBERED_SET}
};

#undef REG


bool RecordWriteStub::IsPregenerated() {
  for (const AheadOfTimeWriteBarrierStubList* entry = kAheadOfTime;
       !entry->object.is(no_reg);
       entry++) {
    if (object_.is(entry->object) &&
        value_.is(entry->value) &&
        address_.is(entry->address) &&
        remembered_set_action_ == entry->action &&
        save_fp_regs_mode_ == kDontSaveFPRegs) {
      return true;
    }
  }
  return false;
}


void StoreBufferOverflowStub::GenerateFixedRegStubsAheadOfTime(
    Isolate* isolate) {
  StoreBufferOverflowStub stub1(kDontSaveFPRegs);
  stub1.GetCode(isolate)->set_is_pregenerated(true);
}


void RecordWriteStub::GenerateFixedRegStubsAheadOfTime(Isolate* isolate) {
  for (const AheadOfTimeWriteBarrierStubList* entry = kAheadOfTime;
       !entry->object.is(no_reg);
       entry++) {
    RecordWriteStub stub(entry->object,
                         entry->value,
                         entry->address,
                         entry->action,
                         kDontSaveFPRegs);
    stub.GetCode(isolate)->set_is_pregenerated(true);
  }
}


bool CodeStub::CanUseFPRegisters() {
  return false;  // FPU is a base requirement for V8.
}


// Takes the input in 3 registers: address_ value_ and object_.  A pointer to
// the value has just been written into the object, now this stub makes sure
// we keep the GC informed.  The word in the object where the value has been
// written is in the address register.
void RecordWriteStub::Generate(MacroAssembler* masm) {
  Label skip_to_incremental_noncompacting;
  Label skip_to_incremental_compacting;

  // The first two branch+nop instructions are generated with labels so as to
  // get the offset fixed up correctly by the bind(Label*) call.  We patch it
  // back and forth between a "bne zero, zero, ..." (a nop in this
  // position) and the "beq zero, zero, ..." when we start and stop
  // incremental heap marking.
  // See RecordWriteStub::Patch for details.
  __ beqz(zero, &skip_to_incremental_noncompacting);
  __ beqz(zero, &skip_to_incremental_compacting);

  if (remembered_set_action_ == EMIT_REMEMBERED_SET) {
    __ RememberedSetHelper(object_,
                           address_,
                           value_,
                           save_fp_regs_mode_,
                           MacroAssembler::kReturnAtEnd);
  }
  __ Ret();

  __ bind(&skip_to_incremental_noncompacting);
  GenerateIncremental(masm, INCREMENTAL);

  __ bind(&skip_to_incremental_compacting);
  GenerateIncremental(masm, INCREMENTAL_COMPACTION);

  // Initial mode of the stub is expected to be STORE_BUFFER_ONLY.
  // Will be checked in IncrementalMarking::ActivateGeneratedStub.

  PatchBranchIntoNop(masm, 0);
  PatchBranchIntoNop(masm, 1 * Assembler::kInstrSize);
}


void RecordWriteStub::GenerateIncremental(MacroAssembler* masm, Mode mode) {
  regs_.Save(masm);

  if (remembered_set_action_ == EMIT_REMEMBERED_SET) {
    Label dont_need_remembered_set;

    __ ld(regs_.scratch0(), MemOperand(regs_.address(), 0));
    __ JumpIfNotInNewSpace(regs_.scratch0(),  // Value.
                           regs_.scratch0(),
                           &dont_need_remembered_set);

    __ CheckPageFlag(regs_.object(),
                     regs_.scratch0(),
                     1 << MemoryChunk::SCAN_ON_SCAVENGE,
                     ne,
                     &dont_need_remembered_set);

    // First notify the incremental marker if necessary, then update the
    // remembered set.
    CheckNeedsToInformIncrementalMarker(
        masm, kUpdateRememberedSetOnNoNeedToInformIncrementalMarker, mode);
    InformIncrementalMarker(masm, mode);
    regs_.Restore(masm);
    __ RememberedSetHelper(object_,
                           address_,
                           value_,
                           save_fp_regs_mode_,
                           MacroAssembler::kReturnAtEnd);

    __ bind(&dont_need_remembered_set);
  }

  CheckNeedsToInformIncrementalMarker(
      masm, kReturnOnNoNeedToInformIncrementalMarker, mode);
  InformIncrementalMarker(masm, mode);
  regs_.Restore(masm);
  __ Ret();
}


void RecordWriteStub::InformIncrementalMarker(MacroAssembler* masm, Mode mode) {

  regs_.SaveCallerSaveRegisters(masm, save_fp_regs_mode_);
  int argument_count = 3;
  __ PrepareCallCFunction(argument_count, regs_.scratch0());
  Register address =
      a0.is(regs_.address()) ? regs_.scratch0() : regs_.address();
  ASSERT(!address.is(regs_.object()));
  ASSERT(!address.is(a0));
  __ Move(address, regs_.address());
  __ Move(a0, regs_.object());
  __ Move(a1, address);
  __ li(a2, Operand(ExternalReference::isolate_address(masm->isolate())));

  AllowExternalCallThatCantCauseGC scope(masm);
  if (mode == INCREMENTAL_COMPACTION) {
    __ CallCFunction(
        ExternalReference::incremental_evacuation_record_write_function(
            masm->isolate()),
        argument_count);
  } else {
    ASSERT(mode == INCREMENTAL);
    __ CallCFunction(
        ExternalReference::incremental_marking_record_write_function(
            masm->isolate()),
        argument_count);
  }
  regs_.RestoreCallerSaveRegisters(masm, save_fp_regs_mode_);
}


void RecordWriteStub::CheckNeedsToInformIncrementalMarker(
    MacroAssembler* masm,
    OnNoNeedToInformIncrementalMarker on_no_need,
    Mode mode) {
  Label on_black;
  Label need_incremental;
  Label need_incremental_pop_scratch;

  __ And(regs_.scratch0(), regs_.object(), Operand(~Page::kPageAlignmentMask));
  __ ld(regs_.scratch1(),
        MemOperand(regs_.scratch0(),
                   MemoryChunk::kWriteBarrierCounterOffset));
  __ Subu(regs_.scratch1(), regs_.scratch1(), Operand(1));
  __ st(regs_.scratch1(),
         MemOperand(regs_.scratch0(),
                    MemoryChunk::kWriteBarrierCounterOffset));
  __ Branch(&need_incremental, lt, regs_.scratch1(), Operand(zero));

  // Let's look at the color of the object:  If it is not black we don't have
  // to inform the incremental marker.
  __ JumpIfBlack(regs_.object(), regs_.scratch0(), regs_.scratch1(), &on_black);

  regs_.Restore(masm);
  if (on_no_need == kUpdateRememberedSetOnNoNeedToInformIncrementalMarker) {
    __ RememberedSetHelper(object_,
                           address_,
                           value_,
                           save_fp_regs_mode_,
                           MacroAssembler::kReturnAtEnd);
  } else {
    __ Ret();
  }

  __ bind(&on_black);

  // Get the value from the slot.
  __ ld(regs_.scratch0(), MemOperand(regs_.address(), 0));

  if (mode == INCREMENTAL_COMPACTION) {
    Label ensure_not_white;

    __ CheckPageFlag(regs_.scratch0(),  // Contains value.
                     regs_.scratch1(),  // Scratch.
                     MemoryChunk::kEvacuationCandidateMask,
                     eq,
                     &ensure_not_white);

    __ CheckPageFlag(regs_.object(),
                     regs_.scratch1(),  // Scratch.
                     MemoryChunk::kSkipEvacuationSlotsRecordingMask,
                     eq,
                     &need_incremental);

    __ bind(&ensure_not_white);
  }

  // We need extra registers for this, so we push the object and the address
  // register temporarily.
  __ Push(regs_.object(), regs_.address());
  __ EnsureNotWhite(regs_.scratch0(),  // The value.
                    regs_.scratch1(),  // Scratch.
                    regs_.object(),  // Scratch.
                    regs_.address(),  // Scratch.
                    &need_incremental_pop_scratch);
  __ Pop(regs_.object(), regs_.address());

  regs_.Restore(masm);
  if (on_no_need == kUpdateRememberedSetOnNoNeedToInformIncrementalMarker) {
    __ RememberedSetHelper(object_,
                           address_,
                           value_,
                           save_fp_regs_mode_,
                           MacroAssembler::kReturnAtEnd);
  } else {
    __ Ret();
  }

  __ bind(&need_incremental_pop_scratch);
  __ Pop(regs_.object(), regs_.address());

  __ bind(&need_incremental);

  // Fall through when we need to inform the incremental marker.
}


void StoreArrayLiteralElementStub::Generate(MacroAssembler* masm) {
  // ----------- S t a t e -------------
  //  -- a0    : element value to store
  //  -- a1    : array literal
  //  -- a2    : map of array literal
  //  -- a3    : element index as smi
  //  -- t0    : array literal index in function as smi
  // -----------------------------------

  Label element_done;
  Label double_elements;
  Label smi_element;
  Label slow_elements;
  Label fast_elements;

  __ CheckFastElements(a2, t1, &double_elements);
  // Check for FAST_*_SMI_ELEMENTS or FAST_*_ELEMENTS elements
  __ JumpIfSmi(a0, &smi_element);
  __ CheckFastSmiElements(a2, t1, &fast_elements);

  // Store into the array literal requires a elements transition. Call into
  // the runtime.
  __ bind(&slow_elements);
  // call.
  __ Push(a1, a3, a0);
  __ ld(t1, MemOperand(fp, JavaScriptFrameConstants::kFunctionOffset));
  __ ld(t1, FieldMemOperand(t1, JSFunction::kLiteralsOffset));
  __ Push(t1, t0);
  __ TailCallRuntime(Runtime::kStoreArrayLiteralElement, 5, 1);

  // Array literal has ElementsKind of FAST_*_ELEMENTS and value is an object.
  __ bind(&fast_elements);
  __ ld(t1, FieldMemOperand(a1, JSObject::kElementsOffset));
  __ sra(t2, a3, 32);
  __ sll(t2, t2, kPointerSizeLog2);
  __ Addu(t2, t1, t2);
  __ Addu(t2, t2, Operand(FixedArray::kHeaderSize - kHeapObjectTag));
  __ st(a0, MemOperand(t2, 0));
  // Update the write barrier for the array store.
  __ RecordWrite(t1, t2, a0, kRAHasNotBeenSaved, kDontSaveFPRegs,
                 EMIT_REMEMBERED_SET, OMIT_SMI_CHECK);
  //__ move(v0, a0);
  __ Ret();

  // Array literal has ElementsKind of FAST_*_SMI_ELEMENTS or FAST_*_ELEMENTS,
  // and value is Smi.
  __ bind(&smi_element);
  __ ld(t1, FieldMemOperand(a1, JSObject::kElementsOffset));
  __ sra(t2, a3, 32);
  __ sll(t2, t2, kPointerSizeLog2);
  __ Addu(t2, t1, t2);
  __ st(a0, FieldMemOperand(t2, FixedArray::kHeaderSize));
  //__ move(v0, a0);
  __ Ret();

  // Array literal has ElementsKind of FAST_*_DOUBLE_ELEMENTS.
  __ bind(&double_elements);
  __ ld(t1, FieldMemOperand(a1, JSObject::kElementsOffset));
  __ StoreNumberToDoubleElements(a0, a3,
                                 // Overwrites all regs after this.
                                 t1, t2, t3, t5, a2,
                                 &slow_elements);
  //__ move(v0, a0);
  __ Ret();
}


void StubFailureTrampolineStub::Generate(MacroAssembler* masm) {
  CEntryStub ces(1, fp_registers_ ? kSaveFPRegs : kDontSaveFPRegs);
  __ Call(ces.GetCode(masm->isolate()), RelocInfo::CODE_TARGET);
  int parameter_count_offset =
      StubFailureTrampolineFrame::kCallerStackParameterCountFrameOffset;
  __ ld(r1, MemOperand(fp, parameter_count_offset));
  if (function_mode_ == JS_FUNCTION_STUB_MODE) {
    __ Addu(r1, r1, Operand(1));
  }
  masm->LeaveFrame(StackFrame::STUB_FAILURE_TRAMPOLINE);
  __ sll(r1, r1, kPointerSizeLog2);
  __ Addu(sp, sp, r1);
  __ Ret();
}


void ProfileEntryHookStub::MaybeCallEntryHook(MacroAssembler* masm) {
  if (entry_hook_ != NULL) {
    ProfileEntryHookStub stub;
    __ push(ra);
    __ CallStub(&stub);
    __ pop(ra);
  }
}


void ProfileEntryHookStub::Generate(MacroAssembler* masm) {
  // The entry hook is a "push ra" instruction, followed by a call.
  // Note: on MIPS "push" is 2 instruction
  const int32_t kReturnAddressDistanceFromFunctionStart =
      Assembler::kCallTargetAddressOffset + (2 * Assembler::kInstrSize);

  // Save live volatile registers.
  __ Push(ra, t1, a1);
  const int32_t kNumSavedRegs = 3;

  // Compute the function's address for the first argument.
  __ Subu(a0, ra, Operand(kReturnAddressDistanceFromFunctionStart));

  // The caller's return address is above the saved temporaries.
  // Grab that for the second argument to the hook.
  __ Addu(a1, sp, Operand(kNumSavedRegs * kPointerSize));

  // Align the stack if necessary.
  int frame_alignment = masm->ActivationFrameAlignment();
  if (frame_alignment > kPointerSize) {
    __ move(t1, sp);
    ASSERT(IsPowerOf2(frame_alignment));
    __ And(sp, sp, Operand(-frame_alignment));
  }

  __ Subu(sp, sp, Operand(16));
  __ li(at, Operand(reinterpret_cast<int64_t>(&entry_hook_)));
  __ ld(at, MemOperand(at));
  __ Call(at);
  __ Addu(sp, sp, Operand(16));

  // Restore the stack pointer if needed.
  if (frame_alignment > kPointerSize) {
    __ move(sp, t1);
  }

  __ Pop(ra, t1, a1);
  __ Ret();
}


template<class T>
static void CreateArrayDispatch(MacroAssembler* masm) {
  int last_index = GetSequenceIndexFromFastElementsKind(
      TERMINAL_FAST_ELEMENTS_KIND);
  for (int i = 0; i <= last_index; ++i) {
    Label next;
    ElementsKind kind = GetFastElementsKindFromSequenceIndex(i);
    __ Branch(&next, ne, a3, Operand(kind));
    T stub(kind);
    __ TailCallStub(&stub);
    __ bind(&next);
  }

  // If we reached this point there is a problem.
  __ Abort("Unexpected ElementsKind in array constructor");
}


static void CreateArrayDispatchOneArgument(MacroAssembler* masm) {
  // a2 - type info cell
  // a3 - kind
  // a0 - number of arguments
  // a1 - constructor?
  // sp[0] - last argument
  ASSERT(FAST_SMI_ELEMENTS == 0);
  ASSERT(FAST_HOLEY_SMI_ELEMENTS == 1);
  ASSERT(FAST_ELEMENTS == 2);
  ASSERT(FAST_HOLEY_ELEMENTS == 3);
  ASSERT(FAST_DOUBLE_ELEMENTS == 4);
  ASSERT(FAST_HOLEY_DOUBLE_ELEMENTS == 5);

  Handle<Object> undefined_sentinel(
      masm->isolate()->heap()->undefined_value(),
      masm->isolate());

  // is the low bit set? If so, we are holey and that is good.
  Label normal_sequence;
  __ And(at, a3, Operand(1));
  __ Branch(&normal_sequence, ne, at, Operand(zero));

  // look at the first argument
  __ ld(t1, MemOperand(sp, 0));
  __ Branch(&normal_sequence, eq, t1, Operand(zero));

  // We are going to create a holey array, but our kind is non-holey.
  // Fix kind and retry
  __ Addu(a3, a3, Operand(1));
  __ Branch(&normal_sequence, eq, a2, Operand(undefined_sentinel));

  // Save the resulting elements kind in type info
  __ SmiTag(a3);
  __ st(a3, FieldMemOperand(a2, kPointerSize));
  __ SmiUntag(a3);

  __ bind(&normal_sequence);
  int last_index = GetSequenceIndexFromFastElementsKind(
      TERMINAL_FAST_ELEMENTS_KIND);
  for (int i = 0; i <= last_index; ++i) {
    Label next;
    ElementsKind kind = GetFastElementsKindFromSequenceIndex(i);
    __ Branch(&next, ne, a3, Operand(kind));
    ArraySingleArgumentConstructorStub stub(kind);
    __ TailCallStub(&stub);
    __ bind(&next);
  }

  // If we reached this point there is a problem.
  __ Abort("Unexpected ElementsKind in array constructor");
}

template<class T>
static void ArrayConstructorStubAheadOfTimeHelper(Isolate* isolate) {
  int to_index = GetSequenceIndexFromFastElementsKind(
      TERMINAL_FAST_ELEMENTS_KIND);
  for (int i = 0; i <= to_index; ++i) {
    ElementsKind kind = GetFastElementsKindFromSequenceIndex(i);
    T stub(kind);
    stub.GetCode(isolate)->set_is_pregenerated(true);
  }
}

void ArrayConstructorStubBase::GenerateStubsAheadOfTime(Isolate* isolate) {
  ArrayConstructorStubAheadOfTimeHelper<ArrayNoArgumentConstructorStub>(
      isolate);
  ArrayConstructorStubAheadOfTimeHelper<ArraySingleArgumentConstructorStub>(
      isolate);
  ArrayConstructorStubAheadOfTimeHelper<ArrayNArgumentsConstructorStub>(
      isolate);
}


void ArrayConstructorStub::Generate(MacroAssembler* masm) {
  // ----------- S t a t e -------------
  //  -- a0 : argc (only if argument_count_ == ANY)
  //  -- a1 : constructor
  //  -- a2 : type info cell
  //  -- sp[0] : return address
  //  -- sp[4] : last argument
  // -----------------------------------
  Handle<Object> undefined_sentinel(
      masm->isolate()->heap()->undefined_value(),
      masm->isolate());

  if (FLAG_debug_code) {
    // The array construct code is only set for the global and natives
    // builtin Array functions which always have maps.

    // Initial map for the builtin Array function should be a map.
    __ ld(a3, FieldMemOperand(a1, JSFunction::kPrototypeOrInitialMapOffset));
    // Will both indicate a NULL and a Smi.
    __ And(at, a3, Operand(kSmiTagMask));
    __ Assert(ne, "Unexpected initial map for Array function",
        at, Operand(zero));
    __ GetObjectType(a3, a3, t0);
    __ Assert(eq, "Unexpected initial map for Array function",
        t0, Operand(MAP_TYPE));

    // We should either have undefined in ebx or a valid jsglobalpropertycell
    Label okay_here;
    Handle<Map> global_property_cell_map(
        masm->isolate()->heap()->global_property_cell_map());
    __ Branch(&okay_here, eq, a2, Operand(undefined_sentinel));
    __ ld(a3, FieldMemOperand(a2, 0));
    __ Assert(eq, "Expected property cell in register ebx",
        a3, Operand(global_property_cell_map));
    __ bind(&okay_here);
  }

  if (FLAG_optimize_constructed_arrays) {
    Label no_info, switch_ready;
    // Get the elements kind and case on that.
    __ Branch(&no_info, eq, a2, Operand(undefined_sentinel));
    __ ld(a3, FieldMemOperand(a2, kPointerSize));
    __ JumpIfNotSmi(a3, &no_info);

    // There is no info if the call site went megamorphic either
    // TODO(mvstanton): Really? I thought if it was the array function that
    // the cell wouldn't get stamped as megamorphic.
    __ Branch(&no_info, eq, a3,
	      Operand(TypeFeedbackCells::MegamorphicSentinel(masm->isolate())));
    __ SmiUntag(a3);
    __ jmp(&switch_ready);
    __ bind(&no_info);
    __ li(a3, Operand(GetInitialFastElementsKind()));
    __ bind(&switch_ready);

    if (argument_count_ == ANY) {
      Label not_zero_case, not_one_case;
      __ And(at, a0, a0);
      __ Branch(&not_zero_case, ne, at, Operand(zero));
      CreateArrayDispatch<ArrayNoArgumentConstructorStub>(masm);

      __ bind(&not_zero_case);
      __ Branch(&not_one_case, gt, a0, Operand(1));
      CreateArrayDispatchOneArgument(masm);

      __ bind(&not_one_case);
      CreateArrayDispatch<ArrayNArgumentsConstructorStub>(masm);
    } else if (argument_count_ == NONE) {
      CreateArrayDispatch<ArrayNoArgumentConstructorStub>(masm);
    } else if (argument_count_ == ONE) {
      CreateArrayDispatchOneArgument(masm);
    } else if (argument_count_ == MORE_THAN_ONE) {
      CreateArrayDispatch<ArrayNArgumentsConstructorStub>(masm);
    } else {
     UNREACHABLE();
    }
  } else {
     Label generic_constructor;
     // Run the native code for the Array function called as a constructor.
     ArrayNativeCode(masm, &generic_constructor);

     // Jump to the generic construct code in case the specialized code cannot
     // handle the construction.
     __ bind(&generic_constructor);
     Handle<Code> generic_construct_stub =
         masm->isolate()->builtins()->JSConstructStubGeneric();
     __ Jump(generic_construct_stub, RelocInfo::CODE_TARGET);
  }
}

#undef __

} }  // namespace v8::internal

#endif  // V8_TARGET_ARCH_TILEGX
