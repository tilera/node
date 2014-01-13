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

#include "tilegx/lithium-codegen-tilegx.h"
#include "tilegx/lithium-gap-resolver-tilegx.h"
#include "code-stubs.h"
#include "stub-cache.h"
#include "hydrogen-osr.h"

namespace v8 {
namespace internal {


class SafepointGenerator V8_FINAL: public CallWrapper {
 public:
  SafepointGenerator(LCodeGen* codegen,
                     LPointerMap* pointers,
                     Safepoint::DeoptMode mode)
      : codegen_(codegen),
        pointers_(pointers),
        deopt_mode_(mode) { }
  virtual ~SafepointGenerator() { }

  virtual void BeforeCall(int call_size) const V8_OVERRIDE { }

  virtual void AfterCall() const V8_OVERRIDE {
    codegen_->RecordSafepoint(pointers_, deopt_mode_);
  }

 private:
  LCodeGen* codegen_;
  LPointerMap* pointers_;
  Safepoint::DeoptMode deopt_mode_;
};


#define __ masm()->

bool LCodeGen::GenerateCode() {
  LPhase phase("Z_Code generation", chunk());
  ASSERT(is_unused());
  status_ = GENERATING;

  // Open a frame scope to indicate that there is a frame on the stack.  The
  // NONE indicates that the scope shouldn't actually generate code to set up
  // the frame (that is done in GeneratePrologue).
  FrameScope frame_scope(masm_, StackFrame::NONE);

  return GeneratePrologue() &&
      GenerateBody() &&
      GenerateDeferredCode() &&
      GenerateDeoptJumpTable() &&
      GenerateSafepointTable();
}


void LCodeGen::FinishCode(Handle<Code> code) {
  ASSERT(is_done());
  code->set_stack_slots(GetStackSlotCount());
  code->set_safepoint_table_offset(safepoints_.GetCodeOffset());
  if (FLAG_weak_embedded_maps_in_optimized_code) {
    RegisterDependentCodeForEmbeddedMaps(code);
  }
  PopulateDeoptimizationData(code);
  info()->CommitDependencies(code);
}

void LChunkBuilder::Abort(BailoutReason reason) {
  info()->set_bailout_reason(reason);
  status_ = ABORTED;
}

bool LCodeGen::GeneratePrologue() {
  ASSERT(is_generating());

  if (info()->IsOptimizing()) {
    ProfileEntryHookStub::MaybeCallEntryHook(masm_);

#ifdef DEBUG
    if (strlen(FLAG_stop_at) > 0 &&
        info_->function()->name()->IsUtf8EqualTo(CStrVector(FLAG_stop_at))) {
      __ stop("stop_at");
    }
#endif

    // a1: Callee's JS function.
    // cp: Callee's context.
    // fp: Caller's frame pointer.
    // lr: Caller's pc.

    // Strict mode functions and builtins need to replace the receiver
    // with undefined when called as functions (without an explicit
    // receiver object). r5 is zero for method calls and non-zero for
    // function calls.
    if (!info_->is_classic_mode() || info_->is_native()) {
      Label ok;
      __ Branch(&ok, eq, t1, Operand(zero));

      int receiver_offset = scope()->num_parameters() * kPointerSize;
      __ LoadRoot(a2, Heap::kUndefinedValueRootIndex);
      __ st(a2, MemOperand(sp, receiver_offset));
      __ bind(&ok);
    }
  }

  info()->set_prologue_offset(masm_->pc_offset());
  if (NeedsEagerFrame()) {
    __ Prologue(info()->IsStub() ? BUILD_STUB_FRAME : BUILD_FUNCTION_FRAME);
    frame_is_built_ = true;
    info_->AddNoFrameRange(0, masm_->pc_offset());
  }

  // Reserve space for the stack slots needed by the code.
  int slots = GetStackSlotCount();
  if (slots > 0) {
    if (FLAG_debug_code) {
      __ Subu(sp,  sp, Operand(slots * kPointerSize));
      __ push(a0);
      __ push(a1);
      __ Addu(a0, sp, Operand(slots *  kPointerSize));
      __ li(a1, Operand(kSlotsZapValue));
      Label loop;
      __ bind(&loop);
      __ Subu(a0, a0, Operand(kPointerSize));
      __ st(a1, MemOperand(a0, 2 * kPointerSize));
      __ Branch(&loop, ne, a0, Operand(sp));
      __ pop(a1);
      __ pop(a0);
    } else {
      __ Subu(sp, sp, Operand(slots * kPointerSize));
    }
  }

#if 0
  if (info()->saves_caller_doubles()) {
    Comment(";;; Save clobbered callee double registers");
    int count = 0;
    BitVector* doubles = chunk()->allocated_double_registers();
    BitVector::Iterator save_iterator(doubles);
    while (!save_iterator.Done()) {
      __ sdc1(DoubleRegister::FromAllocationIndex(save_iterator.Current()),
              MemOperand(sp, count * kDoubleSize));
      save_iterator.Advance();
      count++;
    }
  }
#endif

  // Possibly allocate a local context.
  int heap_slots = info()->num_heap_slots() - Context::MIN_CONTEXT_SLOTS;
  if (heap_slots > 0) {
    Comment(";;; Allocate local context");
    // Argument to NewContext is the function, which is in a1.
    __ push(a1);
    if (heap_slots <= FastNewContextStub::kMaximumSlots) {
      FastNewContextStub stub(heap_slots);
      __ CallStub(&stub);
    } else {
      __ CallRuntime(Runtime::kNewFunctionContext, 1);
    }
    RecordSafepoint(Safepoint::kNoLazyDeopt);
    // Context is returned in both v0 and cp.  It replaces the context
    // passed to us.  It's saved in the stack and kept live in cp.
    __ st(cp, MemOperand(fp, StandardFrameConstants::kContextOffset));
    // Copy any necessary parameters into the context.
    int num_parameters = scope()->num_parameters();
    for (int i = 0; i < num_parameters; i++) {
      Variable* var = scope()->parameter(i);
      if (var->IsContextSlot()) {
        int parameter_offset = StandardFrameConstants::kCallerSPOffset +
            (num_parameters - 1 - i) * kPointerSize;
        // Load parameter from stack.
        __ ld(a0, MemOperand(fp, parameter_offset));
        // Store it in the context.
        MemOperand target = ContextOperand(cp, var->index());
        __ st(a0, target);
        // Update the write barrier. This clobbers a3 and a0.
        __ RecordWriteContextSlot(
            cp, target.offset(), a0, a3, GetRAState(), kDontSaveFPRegs);
      }
    }
    Comment(";;; End allocate local context");
  }

  // Trace the call.
  if (FLAG_trace && info()->IsOptimizing()) {
    // We have not executed any compiled code yet, so cp still holds the
    // incoming context.
    __ CallRuntime(Runtime::kTraceEnter, 0);
  }
  return !is_aborted();
}

void LCodeGen::GenerateOsrPrologue() {
  // Generate the OSR entry prologue at the first unknown OSR value, or if there
  // are none, at the OSR entrypoint instruction.
  if (osr_pc_offset_ >= 0) return;

  osr_pc_offset_ = masm()->pc_offset();

  // Adjust the frame size, subsuming the unoptimized frame into the
  // optimized frame.
  int slots = GetStackSlotCount() - graph()->osr()->UnoptimizedFrameSlots();
  ASSERT(slots >= 0);
  __ Subu(sp, sp, Operand(slots * kPointerSize));
}

bool LCodeGen::GenerateDeferredCode() {
  ASSERT(is_generating());
  if (deferred_.length() > 0) {
    for (int i = 0; !is_aborted() && i < deferred_.length(); i++) {
      LDeferredCode* code = deferred_[i];

      HValue* value =
          instructions_->at(code->instruction_index())->hydrogen_value();
      RecordAndWritePosition(value->position());

      Comment(";;; <@%d,#%d> "
              "-------------------- Deferred %s --------------------",
              code->instruction_index(),
              code->instr()->hydrogen_value()->id(),
              code->instr()->Mnemonic());
      __ bind(code->entry());
      if (NeedsDeferredFrame()) {
        Comment(";;; Build frame");
        ASSERT(!frame_is_built_);
        ASSERT(info()->IsStub());
        frame_is_built_ = true;
        __ MultiPush(cp.bit() | fp.bit() | ra.bit());
        __ li(scratch0(), Operand(Smi::FromInt(StackFrame::STUB)));
        __ push(scratch0());
        __ Addu(fp, sp, Operand(2 * kPointerSize));
        Comment(";;; Deferred code");
      }
      code->Generate();
      if (NeedsDeferredFrame()) {
        Comment(";;; Destroy frame");
        ASSERT(frame_is_built_);
        __ pop(at);
        __ MultiPop(cp.bit() | fp.bit() | ra.bit());
        frame_is_built_ = false;
      }
      __ jmp(code->exit());
    }
  }
  // Deferred code is the last part of the instruction sequence. Mark
  // the generated code as done unless we bailed out.
  if (!is_aborted()) status_ = DONE;
  return !is_aborted();
}


bool LCodeGen::GenerateDeoptJumpTable() {
  if (deopt_jump_table_.length() > 0) {
    Comment(";;; -------------------- Jump table --------------------");
  }
  Assembler::BlockTrampolinePoolScope block_trampoline_pool(masm_);
  Label table_start;
  __ bind(&table_start);
  Label needs_frame;
  for (int i = 0; i < deopt_jump_table_.length(); i++) {
    __ bind(&deopt_jump_table_[i].label);
    Address entry = deopt_jump_table_[i].address;
    Deoptimizer::BailoutType type = deopt_jump_table_[i].bailout_type;
    int id = Deoptimizer::GetDeoptimizationId(isolate(), entry, type);
    if (id == Deoptimizer::kNotDeoptimizationEntry) {
      Comment(";;; jump table entry %d.", i);
    } else {
      Comment(";;; jump table entry %d: deoptimization bailout %d.", i, id);
    }
    __ li(t9, Operand(ExternalReference::ForDeoptEntry(entry)));
    if (deopt_jump_table_[i].needs_frame) {
      if (needs_frame.is_bound()) {
        __ Branch(&needs_frame);
      } else {
        __ bind(&needs_frame);
        __ MultiPush(cp.bit() | fp.bit() | ra.bit());
        // This variant of deopt can only be used with stubs. Since we don't
        // have a function pointer to install in the stack frame that we're
        // building, install a special marker there instead.
        ASSERT(info()->IsStub());
        __ li(scratch0(), Operand(Smi::FromInt(StackFrame::STUB)));
        __ push(scratch0());
        __ Addu(fp, sp, Operand(2 * kPointerSize));
        __ Call(t9);
      }
    } else {
      __ Call(t9);
    }
  }
  __ RecordComment("]");

  // The deoptimization jump table is the last part of the instruction
  // sequence. Mark the generated code as done unless we bailed out.
  if (!is_aborted()) status_ = DONE;
  return !is_aborted();
}


bool LCodeGen::GenerateSafepointTable() {
  ASSERT(is_done());
  safepoints_.Emit(masm(), GetStackSlotCount());
  return !is_aborted();
}


Register LCodeGen::ToRegister(int index) const {
  return Register::FromAllocationIndex(index);
}


DoubleRegister LCodeGen::ToDoubleRegister(int index) const {
  return DoubleRegister::FromAllocationIndex(index);
}


Register LCodeGen::ToRegister(LOperand* op) const {
  ASSERT(op->IsRegister());
  return ToRegister(op->index());
}


Register LCodeGen::EmitLoadRegister(LOperand* op, Register scratch) {
  if (op->IsRegister()) {
    return ToRegister(op->index());
  } else if (op->IsConstantOperand()) {
    LConstantOperand* const_op = LConstantOperand::cast(op);
    HConstant* constant = chunk_->LookupConstant(const_op);
    Handle<Object> literal = constant->handle(isolate());
    Representation r = chunk_->LookupLiteralRepresentation(const_op);
    if (r.IsInteger32()) {
      ASSERT(literal->IsNumber());
      __ li(scratch, Operand(static_cast<int32_t>(literal->Number())));
    } else if (r.IsSmi()) {
      ASSERT(constant->HasSmiValue());
      __ li(scratch, Operand(Smi::FromInt(constant->Integer32Value())));
    } else if (r.IsDouble()) {
      Abort(kEmitLoadRegisterUnsupportedDoubleImmediate);
    } else {
      ASSERT(r.IsSmiOrTagged());
      __ LoadObject(scratch, literal);
    }
    return scratch;
  } else if (op->IsStackSlot() || op->IsArgument()) {
    __ ld(scratch, ToMemOperand(op));
    return scratch;
  }
  UNREACHABLE();
  return scratch;
}


DoubleRegister LCodeGen::ToDoubleRegister(LOperand* op) const {
  ASSERT(op->IsDoubleRegister());
  return ToDoubleRegister(op->index());
}

Handle<Object> LCodeGen::ToHandle(LConstantOperand* op) const {
  HConstant* constant = chunk_->LookupConstant(op);
  ASSERT(chunk_->LookupLiteralRepresentation(op).IsSmiOrTagged());
  return constant->handle(isolate());
}


bool LCodeGen::IsInteger32(LConstantOperand* op) const {
  return chunk_->LookupLiteralRepresentation(op).IsSmiOrInteger32();
}

bool LCodeGen::IsSmi(LConstantOperand* op) const {
  return chunk_->LookupLiteralRepresentation(op).IsSmi();
}


int32_t LCodeGen::ToInteger32(LConstantOperand* op) const {
  HConstant* constant = chunk_->LookupConstant(op);
  return constant->Integer32Value();
}


Smi* LCodeGen::ToSmi(LConstantOperand* op) const {
  HConstant* constant = chunk_->LookupConstant(op);
  return Smi::FromInt(constant->Integer32Value());
}


double LCodeGen::ToDouble(LConstantOperand* op) const {  UNREACHABLE();  return 0.0;}


Operand LCodeGen::ToOperand(LOperand* op) {
  if (op->IsConstantOperand()) {
    LConstantOperand* const_op = LConstantOperand::cast(op);
    HConstant* constant = chunk()->LookupConstant(const_op);
    Representation r = chunk_->LookupLiteralRepresentation(const_op);
    if (r.IsSmi()) {
      ASSERT(constant->HasSmiValue());
      return Operand(Smi::FromInt(constant->Integer32Value()));
    } else if (r.IsInteger32()) {
      ASSERT(constant->HasInteger32Value());
      return Operand(constant->Integer32Value());
    } else if (r.IsDouble()) {
      Abort(kToOperandUnsupportedDoubleImmediate);
    }
    ASSERT(r.IsTagged());
    return Operand(constant->handle(isolate()));
  } else if (op->IsRegister()) {
    return Operand(ToRegister(op));
  } else if (op->IsDoubleRegister()) {
    Abort(kToOperandIsDoubleRegisterUnimplemented);
    return Operand((int64_t)0);
  }
  // Stack slots not implemented, use ToMemOperand instead.
  UNREACHABLE();
  return Operand((int64_t)0);
}


MemOperand LCodeGen::ToMemOperand(LOperand* op) const {
  ASSERT(!op->IsRegister());
  ASSERT(!op->IsDoubleRegister());
  ASSERT(op->IsStackSlot() || op->IsDoubleStackSlot());
  return MemOperand(fp, StackSlotOffset(op->index()));
}

MemOperand LCodeGen::ToHighMemOperand(LOperand* op) const {
  ASSERT(op->IsDoubleStackSlot());
  return MemOperand(fp, StackSlotOffset(op->index()) + kPointerSize);
}

void LCodeGen::WriteTranslation(LEnvironment* environment,
                                Translation* translation) {
  if (environment == NULL) return;

  // The translation includes one command per value in the environment.
  int translation_size = environment->translation_size();
  // The output frame height does not include the parameters.
  int height = translation_size - environment->parameter_count();

  WriteTranslation(environment->outer(), translation);
  bool has_closure_id = !info()->closure().is_null() &&
      !info()->closure().is_identical_to(environment->closure());
  int closure_id = has_closure_id
      ? DefineDeoptimizationLiteral(environment->closure())
      : Translation::kSelfLiteralId;

  switch (environment->frame_type()) {
    case JS_FUNCTION:
      translation->BeginJSFrame(environment->ast_id(), closure_id, height);
      break;
    case JS_CONSTRUCT:
      translation->BeginConstructStubFrame(closure_id, translation_size);
      break;
    case JS_GETTER:
      ASSERT(translation_size == 1);
      ASSERT(height == 0);
      translation->BeginGetterStubFrame(closure_id);
      break;
    case JS_SETTER:
      ASSERT(translation_size == 2);
      ASSERT(height == 0);
      translation->BeginSetterStubFrame(closure_id);
      break;
    case STUB:
      translation->BeginCompiledStubFrame();
      break;
    case ARGUMENTS_ADAPTOR:
      translation->BeginArgumentsAdaptorFrame(closure_id, translation_size);
      break;
  }

  int object_index = 0;
  int dematerialized_index = 0;
  for (int i = 0; i < translation_size; ++i) {
    LOperand* value = environment->values()->at(i);
    AddToTranslation(environment,
                     translation,
                     value,
                     environment->HasTaggedValueAt(i),
                     environment->HasUint32ValueAt(i),
                     &object_index,
                     &dematerialized_index);
  }
}

void LCodeGen::AddToTranslation(LEnvironment* environment,
                                Translation* translation,
                                LOperand* op,
                                bool is_tagged,
                                bool is_uint32,
                                int* object_index_pointer,
                                int* dematerialized_index_pointer) {
  if (op == LEnvironment::materialization_marker()) {
    int object_index = (*object_index_pointer)++;
    if (environment->ObjectIsDuplicateAt(object_index)) {
      int dupe_of = environment->ObjectDuplicateOfAt(object_index);
      translation->DuplicateObject(dupe_of);
      return;
    }
    int object_length = environment->ObjectLengthAt(object_index);
    if (environment->ObjectIsArgumentsAt(object_index)) {
      translation->BeginArgumentsObject(object_length);
    } else {
      translation->BeginCapturedObject(object_length);
    }
    int dematerialized_index = *dematerialized_index_pointer;
    int env_offset = environment->translation_size() + dematerialized_index;
    *dematerialized_index_pointer += object_length;
    for (int i = 0; i < object_length; ++i) {
      LOperand* value = environment->values()->at(env_offset + i);
      AddToTranslation(environment,
                       translation,
                       value,
                       environment->HasTaggedValueAt(env_offset + i),
                       environment->HasUint32ValueAt(env_offset + i),
                       object_index_pointer,
                       dematerialized_index_pointer);
    }
    return;
  }

  if (op->IsStackSlot()) {
    if (is_tagged) {
      translation->StoreStackSlot(op->index());
    } else if (is_uint32) {
      translation->StoreUint32StackSlot(op->index());
    } else {
      translation->StoreInt32StackSlot(op->index());
    }
  } else if (op->IsDoubleStackSlot()) {
    translation->StoreDoubleStackSlot(op->index());
  } else if (op->IsArgument()) {
    ASSERT(is_tagged);
    int src_index = GetStackSlotCount() + op->index();
    translation->StoreStackSlot(src_index);
  } else if (op->IsRegister()) {
    Register reg = ToRegister(op);
    if (is_tagged) {
      translation->StoreRegister(reg);
    } else if (is_uint32) {
      translation->StoreUint32Register(reg);
    } else {
      translation->StoreInt32Register(reg);
    }
  } else if (op->IsDoubleRegister()) {
    DoubleRegister reg = ToDoubleRegister(op);
    translation->StoreDoubleRegister(reg);
  } else if (op->IsConstantOperand()) {
    HConstant* constant = chunk()->LookupConstant(LConstantOperand::cast(op));
    int src_index = DefineDeoptimizationLiteral(constant->handle(isolate()));
    translation->StoreLiteral(src_index);
  } else {
    UNREACHABLE();
  }
}

void LCodeGen::CallCode(Handle<Code> code,
                        RelocInfo::Mode mode,
                        LInstruction* instr) {

  CallCodeGeneric(code, mode, instr, RECORD_SIMPLE_SAFEPOINT);
}

void LCodeGen::CallCodeGeneric(Handle<Code> code,
                               RelocInfo::Mode mode,
                               LInstruction* instr,
                               SafepointMode safepoint_mode) {
  EnsureSpaceForLazyDeopt(Deoptimizer::patch_size());
  ASSERT(instr != NULL);
  __ Call(code, mode);
  RecordSafepointWithLazyDeopt(instr, safepoint_mode);
}

void LCodeGen::CallRuntime(const Runtime::Function* function,
                           int num_arguments,
                           LInstruction* instr,
                           SaveFPRegsMode save_doubles) {
  ASSERT(instr != NULL);

  __ CallRuntime(function, num_arguments);

  RecordSafepointWithLazyDeopt(instr, RECORD_SIMPLE_SAFEPOINT);
}

void LCodeGen::LoadContextFromDeferred(LOperand* context) {
  if (context->IsRegister()) {
    __ Move(cp, ToRegister(context));
  } else if (context->IsStackSlot()) {
    __ ld(cp, ToMemOperand(context));
  } else if (context->IsConstantOperand()) {
    HConstant* constant =
        chunk_->LookupConstant(LConstantOperand::cast(context));
    __ LoadObject(cp, Handle<Object>::cast(constant->handle(isolate())));
  } else {
    UNREACHABLE();
  }
}

void LCodeGen::CallRuntimeFromDeferred(Runtime::FunctionId id,
                                       int argc,
                                       LInstruction* instr,
                                       LOperand* context) {
  if (context != NULL)
    LoadContextFromDeferred(context);
  __ CallRuntimeSaveDoubles(id);
  RecordSafepointWithRegisters(
      instr->pointer_map(), argc, Safepoint::kNoLazyDeopt);
}


void LCodeGen::RegisterEnvironmentForDeoptimization(LEnvironment* environment, Safepoint::DeoptMode mode) {
  if (!environment->HasBeenRegistered()) {
    // Physical stack frame layout:
    // -x ............. -4  0 ..................................... y
    // [incoming arguments] [spill slots] [pushed outgoing arguments]

    // Layout of the environment:
    // 0 ..................................................... size-1
    // [parameters] [locals] [expression stack including arguments]

    // Layout of the translation:
    // 0 ........................................................ size - 1 + 4
    // [expression stack including arguments] [locals] [4 words] [parameters]
    // |>------------  translation_size ------------<|

    int frame_count = 0;
    int jsframe_count = 0;
    for (LEnvironment* e = environment; e != NULL; e = e->outer()) {
      ++frame_count;
      if (e->frame_type() == JS_FUNCTION) {
        ++jsframe_count;
      }
    }
    Translation translation(&translations_, frame_count, jsframe_count, zone());
    WriteTranslation(environment, &translation);
    int deoptimization_index = deoptimizations_.length();
    int pc_offset = masm()->pc_offset();
    environment->Register(deoptimization_index,
                          translation.index(),
                          (mode == Safepoint::kLazyDeopt) ? pc_offset : -1);
    deoptimizations_.Add(environment, zone());
  }
}

void LCodeGen::DeoptimizeIf(Condition condition,
                            LEnvironment* environment,
                            Deoptimizer::BailoutType bailout_type,
                            Register src1,
                            const Operand& src2) {
  RegisterEnvironmentForDeoptimization(environment, Safepoint::kNoLazyDeopt);
  ASSERT(environment->HasBeenRegistered());
  int id = environment->deoptimization_index();
  ASSERT(info()->IsOptimizing() || info()->IsStub());
  Address entry =
      Deoptimizer::GetDeoptimizationEntry(isolate(), id, bailout_type);
  if (entry == NULL) {
    Abort(kBailoutWasNotPrepared);
    return;
  }

  ASSERT(FLAG_deopt_every_n_times < 2);  // Other values not supported on MIPS.
  if (FLAG_deopt_every_n_times == 1 &&
      !info()->IsStub() &&
      info()->opt_count() == id) {
    ASSERT(frame_is_built_);
    __ Call(entry, RelocInfo::RUNTIME_ENTRY);
    return;
  }

  if (info()->ShouldTrapOnDeopt()) {
    Label skip;
    if (condition != al) {
      __ Branch(&skip, NegateCondition(condition), src1, src2);
    }
    __ stop("trap_on_deopt");
    __ bind(&skip);
  }

  ASSERT(info()->IsStub() || frame_is_built_);
  if (condition == al && frame_is_built_) {
    __ Call(entry, RelocInfo::RUNTIME_ENTRY, condition, src1, src2);
  } else {
    // We often have several deopts to the same entry, reuse the last
    // jump entry if this is the case.
    if (deopt_jump_table_.is_empty() ||
        (deopt_jump_table_.last().address != entry) ||
        (deopt_jump_table_.last().bailout_type != bailout_type) ||
        (deopt_jump_table_.last().needs_frame != !frame_is_built_)) {
      Deoptimizer::JumpTableEntry table_entry(entry,
                                              bailout_type,
                                              !frame_is_built_);
      deopt_jump_table_.Add(table_entry, zone());
    }
    __ Branch(&deopt_jump_table_.last().label, condition, src1, src2);
  }
}

void LCodeGen::DeoptimizeIf(Condition condition,
                            LEnvironment* environment,
                            Register src1,
                            const Operand& src2) {
  Deoptimizer::BailoutType bailout_type = info()->IsStub()
      ? Deoptimizer::LAZY
      : Deoptimizer::EAGER;
  DeoptimizeIf(condition, environment, bailout_type, src1, src2);
}

void LCodeGen::RegisterDependentCodeForEmbeddedMaps(Handle<Code> code) {
  ZoneList<Handle<Map> > maps(1, zone());
  int mode_mask = RelocInfo::ModeMask(RelocInfo::EMBEDDED_OBJECT);
  for (RelocIterator it(*code, mode_mask); !it.done(); it.next()) {
    RelocInfo::Mode mode = it.rinfo()->rmode();
    if (mode == RelocInfo::EMBEDDED_OBJECT &&
        it.rinfo()->target_object()->IsMap()) {
      Handle<Map> map(Map::cast(it.rinfo()->target_object()));
      if (map->CanTransition()) {
        maps.Add(map, zone());
      }
    }
  }
#ifdef VERIFY_HEAP
  // This disables verification of weak embedded maps after full GC.
  // AddDependentCode can cause a GC, which would observe the state where
  // this code is not yet in the depended code lists of the embedded maps.
  NoWeakEmbeddedMapsVerificationScope disable_verification_of_embedded_maps;
#endif
  for (int i = 0; i < maps.length(); i++) {
    maps.at(i)->AddDependentCode(DependentCode::kWeaklyEmbeddedGroup, code);
  }
}

void LCodeGen::PopulateDeoptimizationData(Handle<Code> code) {
  int length = deoptimizations_.length();
  if (length == 0) return;
  Handle<DeoptimizationInputData> data =
      factory()->NewDeoptimizationInputData(length, TENURED);

  Handle<ByteArray> translations =
      translations_.CreateByteArray(isolate()->factory());
  data->SetTranslationByteArray(*translations);
  data->SetInlinedFunctionCount(Smi::FromInt(inlined_function_count_));

  Handle<FixedArray> literals =
      factory()->NewFixedArray(deoptimization_literals_.length(), TENURED);
  { AllowDeferredHandleDereference copy_handles;
    for (int i = 0; i < deoptimization_literals_.length(); i++) {
      literals->set(i, *deoptimization_literals_[i]);
    }
    data->SetLiteralArray(*literals);
  }

  data->SetOsrAstId(Smi::FromInt(info_->osr_ast_id().ToInt()));
  data->SetOsrPcOffset(Smi::FromInt(osr_pc_offset_));

  // Populate the deoptimization entries.
  for (int i = 0; i < length; i++) {
    LEnvironment* env = deoptimizations_[i];
    data->SetAstId(i, env->ast_id());
    data->SetTranslationIndex(i, Smi::FromInt(env->translation_index()));
    data->SetArgumentsStackHeight(i,
                                  Smi::FromInt(env->arguments_stack_height()));
    data->SetPc(i, Smi::FromInt(env->pc_offset()));
  }
  code->set_deoptimization_data(*data);
}

int LCodeGen::DefineDeoptimizationLiteral(Handle<Object> literal) {
  int result = deoptimization_literals_.length();
  for (int i = 0; i < deoptimization_literals_.length(); ++i) {
    if (deoptimization_literals_[i].is_identical_to(literal)) return i;
  }
  deoptimization_literals_.Add(literal, zone());
  return result;
}

void LCodeGen::PopulateDeoptimizationLiteralsWithInlinedFunctions() {
  ASSERT(deoptimization_literals_.length() == 0);

  const ZoneList<Handle<JSFunction> >* inlined_closures =
      chunk()->inlined_closures();

  for (int i = 0, length = inlined_closures->length();
       i < length;
       i++) {
    DefineDeoptimizationLiteral(inlined_closures->at(i));
  }

  inlined_function_count_ = deoptimization_literals_.length();
}


void LCodeGen::RecordSafepointWithLazyDeopt(
    LInstruction* instr, SafepointMode safepoint_mode) {
  if (safepoint_mode == RECORD_SIMPLE_SAFEPOINT) {
    RecordSafepoint(instr->pointer_map(), Safepoint::kLazyDeopt);
  } else {
    ASSERT(safepoint_mode == RECORD_SAFEPOINT_WITH_REGISTERS_AND_NO_ARGUMENTS);
    RecordSafepointWithRegisters(
        instr->pointer_map(), 0, Safepoint::kLazyDeopt);
  }
}

void LCodeGen::RecordSafepoint(
    LPointerMap* pointers,
    Safepoint::Kind kind,
    int arguments,
    Safepoint::DeoptMode deopt_mode) {
  ASSERT(expected_safepoint_kind_ == kind);

  const ZoneList<LOperand*>* operands = pointers->GetNormalizedOperands();
  Safepoint safepoint = safepoints_.DefineSafepoint(masm(),
      kind, arguments, deopt_mode);
  for (int i = 0; i < operands->length(); i++) {
    LOperand* pointer = operands->at(i);
    if (pointer->IsStackSlot()) {
      safepoint.DefinePointerSlot(pointer->index(), zone());
    } else if (pointer->IsRegister() && (kind & Safepoint::kWithRegisters)) {
      safepoint.DefinePointerRegister(ToRegister(pointer), zone());
    }
  }
  if (kind & Safepoint::kWithRegisters) {
    // Register cp always contains a pointer to the context.
    safepoint.DefinePointerRegister(cp, zone());
  }
}

void LCodeGen::RecordSafepoint(LPointerMap* pointers,
                               Safepoint::DeoptMode deopt_mode) {
  RecordSafepoint(pointers, Safepoint::kSimple, 0, deopt_mode);
}

void LCodeGen::RecordSafepoint(Safepoint::DeoptMode deopt_mode) {
  LPointerMap empty_pointers(zone());
  RecordSafepoint(&empty_pointers, deopt_mode);
}

void LCodeGen::RecordSafepointWithRegisters(LPointerMap* pointers,
                                            int arguments,
                                            Safepoint::DeoptMode deopt_mode) {
  RecordSafepoint(
      pointers, Safepoint::kWithRegisters, arguments, deopt_mode);
}

void LCodeGen::RecordSafepointWithRegistersAndDoubles(
    LPointerMap* pointers,
    int arguments,
    Safepoint::DeoptMode deopt_mode) {  UNREACHABLE();  }

void LCodeGen::RecordAndWritePosition(int position) {
  if (position == RelocInfo::kNoPosition) return;
  masm()->positions_recorder()->RecordPosition(position);
  masm()->positions_recorder()->WriteRecordedPositions();
}

static const char* LabelType(LLabel* label) {
  if (label->is_loop_header()) return " (loop header)";
  if (label->is_osr_entry()) return " (OSR entry)";
  return "";
}

void LCodeGen::DoLabel(LLabel* label) {
  Comment(";;; <@%d,#%d> -------------------- B%d%s --------------------",
          current_instruction_,
          label->hydrogen_value()->id(),
          label->block_id(),
          LabelType(label));
  __ bind(label->label());
  current_block_ = label->block_id();
  DoGap(label);
}

void LCodeGen::DoParallelMove(LParallelMove* move) {
  resolver_.Resolve(move);
}

void LCodeGen::DoGap(LGap* gap) {
  for (int i = LGap::FIRST_INNER_POSITION;
       i <= LGap::LAST_INNER_POSITION;
       i++) {
    LGap::InnerPosition inner_pos = static_cast<LGap::InnerPosition>(i);
    LParallelMove* move = gap->GetParallelMove(inner_pos);
    if (move != NULL) DoParallelMove(move);
  }
}

void LCodeGen::DoInstructionGap(LInstructionGap* instr) {
  DoGap(instr);
}

void LCodeGen::DoParameter(LParameter* instr) {
}

void LCodeGen::DoCallStub(LCallStub* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  ASSERT(ToRegister(instr->result()).is(v0));
  switch (instr->hydrogen()->major_key()) {
    case CodeStub::RegExpConstructResult: {
      RegExpConstructResultStub stub;
      CallCode(stub.GetCode(isolate()), RelocInfo::CODE_TARGET, instr);
      break;
    }
    case CodeStub::RegExpExec: {
      RegExpExecStub stub;
      CallCode(stub.GetCode(isolate()), RelocInfo::CODE_TARGET, instr);
      break;
    }
    case CodeStub::SubString: {
      SubStringStub stub;
      CallCode(stub.GetCode(isolate()), RelocInfo::CODE_TARGET, instr);
      break;
    }
    case CodeStub::StringCompare: {
      StringCompareStub stub;
      CallCode(stub.GetCode(isolate()), RelocInfo::CODE_TARGET, instr);
      break;
    }
    case CodeStub::TranscendentalCache: {
      __ ld(a0, MemOperand(sp, 0));
      TranscendentalCacheStub stub(instr->transcendental_type(),
                                   TranscendentalCacheStub::TAGGED);
      CallCode(stub.GetCode(isolate()), RelocInfo::CODE_TARGET, instr);
      break;
    }
    default:
      UNREACHABLE();
  }
}

void LCodeGen::DoUnknownOSRValue(LUnknownOSRValue* instr) {
}

void LCodeGen::DoModI(LModI* instr) {  UNREACHABLE();  }


void LCodeGen::DoDivI(LDivI* instr) {  UNREACHABLE();  }


void LCodeGen::DoMultiplyAddD(LMultiplyAddD* instr) {  UNREACHABLE();  }


void LCodeGen::DoMulI(LMulI* instr) {
  Register scratch = scratch0();
  Register result = ToRegister(instr->result());
  // Note that result may alias left.
  Register left = ToRegister(instr->left());
  LOperand* right_op = instr->right();

  bool can_overflow = instr->hydrogen()->CheckFlag(HValue::kCanOverflow);
  bool bailout_on_minus_zero =
    instr->hydrogen()->CheckFlag(HValue::kBailoutOnMinusZero);

  if (right_op->IsConstantOperand() && !can_overflow) {
    // Use optimized code for specific constants.
    int32_t constant = ToInteger32(LConstantOperand::cast(right_op));

    if (bailout_on_minus_zero && (constant < 0)) {
      // The case of a null constant will be handled separately.
      // If constant is negative and left is null, the result should be -0.
      DeoptimizeIf(eq, instr->environment(), left, Operand(zero));
    }

    switch (constant) {
      case -1:
        __ Subu(result, zero, left);
        break;
      case 0:
        if (bailout_on_minus_zero) {
          // If left is strictly negative and the constant is null, the
          // result is -0. Deoptimize if required, otherwise return 0.
          DeoptimizeIf(lt, instr->environment(), left, Operand(zero));
        }
        __ move(result, zero);
        break;
      case 1:
        // Nothing to do.
        __ move(result, left);
        break;
      default:
        // Multiplying by powers of two and powers of two plus or minus
        // one can be done faster with shifted operands.
        // For other constants we emit standard code.
        int32_t mask = constant >> 31;
        uint32_t constant_abs = (constant + mask) ^ mask;

        if (IsPowerOf2(constant_abs) ||
            IsPowerOf2(constant_abs - 1) ||
            IsPowerOf2(constant_abs + 1)) {
          if (IsPowerOf2(constant_abs)) {
            int32_t shift = WhichPowerOf2(constant_abs);
            __ sll(result, left, shift);
          } else if (IsPowerOf2(constant_abs - 1)) {
            int32_t shift = WhichPowerOf2(constant_abs - 1);
            __ sll(scratch, left, shift);
            __ Addu(result, scratch, left);
          } else if (IsPowerOf2(constant_abs + 1)) {
            int32_t shift = WhichPowerOf2(constant_abs + 1);
            __ sll(scratch, left, shift);
            __ Subu(result, scratch, left);
          }

          // Correct the sign of the result is the constant is negative.
          if (constant < 0)  {
            __ Subu(result, zero, result);
          }

        } else {
          // Generate standard code.
          __ li(at, constant);
          __ Mul(result, left, at);
        }
    }

  } else {
    Register right = EmitLoadRegister(right_op, scratch);
    if (bailout_on_minus_zero) {
      __ Or(ToRegister(instr->temp()), left, right);
    }

    if (can_overflow) {
      // hi:lo = left * right.
      __ mul_ls_ls(result, left, right);
      __ sra(scratch, result, 32);
      __ sra(at, result, 31);
      DeoptimizeIf(ne, instr->environment(), scratch, Operand(at));
    } else {
      __ Mul(result, left, right);
    }

    if (bailout_on_minus_zero) {
      // Bail out if the result is supposed to be negative zero.
      Label done;
      __ Branch(&done, ne, result, Operand(zero));
      DeoptimizeIf(lt,
                   instr->environment(),
                   ToRegister(instr->temp()),
                   Operand(zero));
      __ bind(&done);
    }
  }
}


void LCodeGen::DoBitI(LBitI* instr) {
  LOperand* left_op = instr->left();
  LOperand* right_op = instr->right();
  ASSERT(left_op->IsRegister());
  Register left = ToRegister(left_op);
  Register result = ToRegister(instr->result());
  Operand right(no_reg);

  if (right_op->IsStackSlot() || right_op->IsArgument()) {
    right = Operand(EmitLoadRegister(right_op, at));
  } else {
    ASSERT(right_op->IsRegister() || right_op->IsConstantOperand());
    right = ToOperand(right_op);
  }

  switch (instr->op()) {
    case Token::BIT_AND:
      __ And(result, left, right);
      break;
    case Token::BIT_OR:
      __ Or(result, left, right);
      break;
    case Token::BIT_XOR:
      __ Xor(result, left, right);
      break;
    default:
      UNREACHABLE();
      break;
  }
}


void LCodeGen::DoShiftI(LShiftI* instr) {
  // Both 'left' and 'right' are "used at start" (see LCodeGen::DoShift), so
  // result may alias either of them.
  LOperand* right_op = instr->right();
  Register left = ToRegister(instr->left());
  Register result = ToRegister(instr->result());

  if (right_op->IsRegister()) {
    // No need to mask the right operand on MIPS, it is built into the variable
    // shift instructions.
    switch (instr->op()) {
      case Token::ROR:
        __ Ror(result, left, Operand(ToRegister(right_op)));
        break;
      case Token::SAR:
        __ sra(result, left, ToRegister(right_op));
        break;
      case Token::SHR:
        __ srl(result, left, ToRegister(right_op));
        if (instr->can_deopt()) {
          DeoptimizeIf(lt, instr->environment(), result, Operand(zero));
        }
        break;
      case Token::SHL:
        __ sll(result, left, ToRegister(right_op));
        break;
      default:
        UNREACHABLE();
        break;
    }
  } else {
    // Mask the right_op operand.
    int value = ToInteger32(LConstantOperand::cast(right_op));
    uint8_t shift_count = static_cast<uint8_t>(value & 0x1F);
    switch (instr->op()) {
      case Token::ROR:
        if (shift_count != 0) {
          __ Ror(result, left, Operand(shift_count));
        } else {
          __ Move(result, left);
        }
        break;
      case Token::SAR:
        if (shift_count != 0) {
          __ sra(result, left, shift_count);
        } else {
          __ Move(result, left);
        }
        break;
      case Token::SHR:
        if (shift_count != 0) {
          __ srl(result, left, shift_count);
        } else {
          if (instr->can_deopt()) {
            __ And(at, left, Operand(0x80000000));
            DeoptimizeIf(ne, instr->environment(), at, Operand(zero));
          }
          __ Move(result, left);
        }
        break;
      case Token::SHL:
        if (shift_count != 0) {
          __ sll(result, left, shift_count);
        } else {
          __ Move(result, left);
        }
        break;
      default:
        UNREACHABLE();
        break;
    }
  }
}


void LCodeGen::DoSubI(LSubI* instr) {
  LOperand* left = instr->left();
  LOperand* right = instr->right();
  LOperand* result = instr->result();
  bool can_overflow = instr->hydrogen()->CheckFlag(HValue::kCanOverflow);

  if (!can_overflow) {
    if (right->IsStackSlot() || right->IsArgument()) {
      Register right_reg = EmitLoadRegister(right, at);
      __ Subu(ToRegister(result), ToRegister(left), Operand(right_reg));
    } else {
      ASSERT(right->IsRegister() || right->IsConstantOperand());
      __ Subu(ToRegister(result), ToRegister(left), ToOperand(right));
    }
  } else {  // can_overflow.
    Register overflow = scratch0();
    Register scratch = scratch1();
    if (right->IsStackSlot() ||
        right->IsArgument() ||
        right->IsConstantOperand()) {
      Register right_reg = EmitLoadRegister(right, scratch);
      __ SubuAndCheckForOverflow(ToRegister(result),
                                 ToRegister(left),
                                 right_reg,
                                 overflow);  // Reg at also used as scratch.
    } else {
      ASSERT(right->IsRegister());
      // Due to overflow check macros not supporting constant operands,
      // handling the IsConstantOperand case was moved to prev if clause.
      __ SubuAndCheckForOverflow(ToRegister(result),
                                 ToRegister(left),
                                 ToRegister(right),
                                 overflow);  // Reg at also used as scratch.
    }
    DeoptimizeIf(lt, instr->environment(), overflow, Operand(zero));
  }
}


void LCodeGen::DoConstantI(LConstantI* instr) {
  __ li(ToRegister(instr->result()), Operand(instr->value()));
}

void LCodeGen::DoConstantS(LConstantS* instr) {
  __ li(ToRegister(instr->result()), Operand(instr->value()));
}

void LCodeGen::DoConstantD(LConstantD* instr) {
  ASSERT(instr->result()->IsDoubleRegister());
  Register result = Register::from_code(ToDoubleRegister(instr->result()).code());
  double v = instr->value();
  int64_t vi = *(int64_t *)&v;
  __ li(result, Operand(vi));
}

void LCodeGen::DoConstantE(LConstantE* instr) {
  __ li(ToRegister(instr->result()), Operand(instr->value()));
}

void LCodeGen::DoConstantT(LConstantT* instr) {
  Handle<Object> value = instr->value(isolate());
  AllowDeferredHandleDereference smi_check;
  __ LoadObject(ToRegister(instr->result()), value);
}

void LCodeGen::DoMapEnumLength(LMapEnumLength* instr) {
  Register result = ToRegister(instr->result());
  Register map = ToRegister(instr->value());
  __ EnumLength(result, map);
}

void LCodeGen::DoElementsKind(LElementsKind* instr) {  UNREACHABLE();  }


void LCodeGen::DoValueOf(LValueOf* instr) {  UNREACHABLE();  }


void LCodeGen::DoDateField(LDateField* instr) {  UNREACHABLE();  }


void LCodeGen::DoSeqStringSetChar(LSeqStringSetChar* instr) {  UNREACHABLE();  }


void LCodeGen::DoThrow(LThrow* instr) {  UNREACHABLE();  }


void LCodeGen::DoAddI(LAddI* instr) {
  LOperand* left = instr->left();
  LOperand* right = instr->right();
  LOperand* result = instr->result();
  bool can_overflow = instr->hydrogen()->CheckFlag(HValue::kCanOverflow);

  if (!can_overflow) {
    if (right->IsStackSlot() || right->IsArgument()) {
      Register right_reg = EmitLoadRegister(right, at);
      __ Addu(ToRegister(result), ToRegister(left), Operand(right_reg));
    } else {
      ASSERT(right->IsRegister() || right->IsConstantOperand());
      __ Addu(ToRegister(result), ToRegister(left), ToOperand(right));
    }
  } else {  // can_overflow.
    Register overflow = scratch0();
    Register scratch = scratch1();
    if (right->IsStackSlot() ||
        right->IsArgument() ||
        right->IsConstantOperand()) {
      Register right_reg = EmitLoadRegister(right, scratch);
      __ AdduAndCheckForOverflow(ToRegister(result),
                                 ToRegister(left),
                                 right_reg,
                                 overflow);  // Reg at also used as scratch.
    } else {
      ASSERT(right->IsRegister());
      // Due to overflow check macros not supporting constant operands,
      // handling the IsConstantOperand case was moved to prev if clause.
      __ AdduAndCheckForOverflow(ToRegister(result),
                                 ToRegister(left),
                                 ToRegister(right),
                                 overflow);  // Reg at also used as scratch.
    }
    DeoptimizeIf(lt, instr->environment(), overflow, Operand(zero));
  }
}



void LCodeGen::DoMathMinMax(LMathMinMax* instr) {  UNREACHABLE();  }


void LCodeGen::DoArithmeticD(LArithmeticD* instr) {  UNREACHABLE();  }


void LCodeGen::DoArithmeticT(LArithmeticT* instr) {
  ASSERT(ToRegister(instr->left()).is(a1));
  ASSERT(ToRegister(instr->right()).is(a0));
  ASSERT(ToRegister(instr->result()).is(v0));

  BinaryOpStub stub(instr->op(), NO_OVERWRITE);
  CallCode(stub.GetCode(isolate()), RelocInfo::CODE_TARGET, instr);
  // Other arch use a nop here, to signal that there is no inlined
  // patchable code. Mips does not need the nop, since our marker
  // instruction (andi zero) will never be used in normal code.
}

template<class InstrType>
void LCodeGen::EmitBranch(InstrType instr,
                          Condition condition,
                          Register src1,
                          const Operand& src2) {
  int left_block = instr->TrueDestination(chunk_);
  int right_block = instr->FalseDestination(chunk_);

  int next_block = GetNextEmittedBlock();
  if (right_block == left_block || condition == al) {
    EmitGoto(left_block);
  } else if (left_block == next_block) {
    __ Branch(chunk_->GetAssemblyLabel(right_block),
              NegateCondition(condition), src1, src2);
  } else if (right_block == next_block) {
    __ Branch(chunk_->GetAssemblyLabel(left_block), condition, src1, src2);
  } else {
    __ Branch(chunk_->GetAssemblyLabel(left_block), condition, src1, src2);
    __ Branch(chunk_->GetAssemblyLabel(right_block));
  }
}

void LCodeGen::DoDebugBreak(LDebugBreak* instr) {
  __ stop("LDebugBreak");
}

void LCodeGen::DoBranch(LBranch* instr) {
  Representation r = instr->hydrogen()->value()->representation();
  if (r.IsInteger32() || r.IsSmi()) {
    ASSERT(!info()->IsStub());
    Register reg = ToRegister(instr->value());
    EmitBranch(instr, ne, reg, Operand(zero));
  } else if (r.IsDouble()) {
#if 0
    ASSERT(!info()->IsStub());
    DoubleRegister reg = ToDoubleRegister(instr->value());
    // Test the double value. Zero and NaN are false.
    EmitBranchF(instr, nue, reg, kDoubleRegZero);
#else
    UNREACHABLE();
#endif
  } else {
    ASSERT(r.IsTagged());
    Register reg = ToRegister(instr->value());
    HType type = instr->hydrogen()->value()->type();
    if (type.IsBoolean()) {
      ASSERT(!info()->IsStub());
      __ LoadRoot(at, Heap::kTrueValueRootIndex);
      EmitBranch(instr, eq, reg, Operand(at));
    } else if (type.IsSmi()) {
      ASSERT(!info()->IsStub());
      EmitBranch(instr, ne, reg, Operand(zero));
    } else if (type.IsJSArray()) {
      ASSERT(!info()->IsStub());
      EmitBranch(instr, al, zero, Operand(zero));
    } else if (type.IsHeapNumber()) {
#if 0
      ASSERT(!info()->IsStub());
      DoubleRegister dbl_scratch = double_scratch0();
      __ ldc1(dbl_scratch, FieldMemOperand(reg, HeapNumber::kValueOffset));
      // Test the double value. Zero and NaN are false.
      EmitBranchF(instr, nue, dbl_scratch, kDoubleRegZero);
#else
      UNREACHABLE();
#endif
    } else if (type.IsString()) {
      ASSERT(!info()->IsStub());
      __ ld(at, FieldMemOperand(reg, String::kLengthOffset));
      EmitBranch(instr, ne, at, Operand(zero));
    } else {
      ToBooleanStub::Types expected = instr->hydrogen()->expected_input_types();
      // Avoid deopts in the case where we've never executed this path before.
      if (expected.IsEmpty()) expected = ToBooleanStub::Types::Generic();

      if (expected.Contains(ToBooleanStub::UNDEFINED)) {
        // undefined -> false.
        __ LoadRoot(at, Heap::kUndefinedValueRootIndex);
        __ Branch(instr->FalseLabel(chunk_), eq, reg, Operand(at));
      }
      if (expected.Contains(ToBooleanStub::BOOLEAN)) {
        // Boolean -> its value.
        __ LoadRoot(at, Heap::kTrueValueRootIndex);
        __ Branch(instr->TrueLabel(chunk_), eq, reg, Operand(at));
        __ LoadRoot(at, Heap::kFalseValueRootIndex);
        __ Branch(instr->FalseLabel(chunk_), eq, reg, Operand(at));
      }
      if (expected.Contains(ToBooleanStub::NULL_TYPE)) {
        // 'null' -> false.
        __ LoadRoot(at, Heap::kNullValueRootIndex);
        __ Branch(instr->FalseLabel(chunk_), eq, reg, Operand(at));
      }

      if (expected.Contains(ToBooleanStub::SMI)) {
        // Smis: 0 -> false, all other -> true.
        __ Branch(instr->FalseLabel(chunk_), eq, reg, Operand(zero));
        __ JumpIfSmi(reg, instr->TrueLabel(chunk_));
      } else if (expected.NeedsMap()) {
        // If we need a map later and have a Smi -> deopt.
        __ And(at, reg, Operand(kSmiTagMask));
        DeoptimizeIf(eq, instr->environment(), at, Operand(zero));
      }

      const Register map = scratch0();
      if (expected.NeedsMap()) {
        __ ld(map, FieldMemOperand(reg, HeapObject::kMapOffset));
        if (expected.CanBeUndetectable()) {
          // Undetectable -> false.
          __ ld1u(at, FieldMemOperand(map, Map::kBitFieldOffset));
          __ And(at, at, Operand(1 << Map::kIsUndetectable));
          __ Branch(instr->FalseLabel(chunk_), ne, at, Operand(zero));
        }
      }

      if (expected.Contains(ToBooleanStub::SPEC_OBJECT)) {
        // spec object -> true.
        __ ld1u(at, FieldMemOperand(map, Map::kInstanceTypeOffset));
        __ Branch(instr->TrueLabel(chunk_),
                  ge, at, Operand(FIRST_SPEC_OBJECT_TYPE));
      }

      if (expected.Contains(ToBooleanStub::STRING)) {
        // String value -> false iff empty.
        Label not_string;
        __ ld1u(at, FieldMemOperand(map, Map::kInstanceTypeOffset));
        __ Branch(&not_string, ge , at, Operand(FIRST_NONSTRING_TYPE));
        __ ld(at, FieldMemOperand(reg, String::kLengthOffset));
        __ Branch(instr->TrueLabel(chunk_), ne, at, Operand(zero));
        __ Branch(instr->FalseLabel(chunk_));
        __ bind(&not_string);
      }

      if (expected.Contains(ToBooleanStub::SYMBOL)) {
        // Symbol value -> true.
        const Register scratch = scratch1();
        __ ld1u(scratch, FieldMemOperand(map, Map::kInstanceTypeOffset));
        __ Branch(instr->TrueLabel(chunk_), eq, scratch, Operand(SYMBOL_TYPE));
      }

      if (expected.Contains(ToBooleanStub::HEAP_NUMBER)) {
#if 0
        // heap number -> false iff +0, -0, or NaN.
        DoubleRegister dbl_scratch = double_scratch0();
        Label not_heap_number;
        __ LoadRoot(at, Heap::kHeapNumberMapRootIndex);
        __ Branch(&not_heap_number, ne, map, Operand(at));
        __ ldc1(dbl_scratch, FieldMemOperand(reg, HeapNumber::kValueOffset));
        __ BranchF(instr->TrueLabel(chunk_), instr->FalseLabel(chunk_),
                   ne, dbl_scratch, kDoubleRegZero);
        // Falls through if dbl_scratch == 0.
        __ Branch(instr->FalseLabel(chunk_));
        __ bind(&not_heap_number);
#else
	UNREACHABLE();
#endif
      }

      if (!expected.IsGeneric()) {
        // We've seen something for the first time -> deopt.
        // This can only happen if we are not generic already.
        DeoptimizeIf(al, instr->environment(), zero, Operand(zero));
      }
    }
  }
}

void LCodeGen::EmitGoto(int block) {
  if (!IsNextEmittedBlock(block)) {
    __ jmp(chunk_->GetAssemblyLabel(chunk_->LookupDestination(block)));
  }
}

void LCodeGen::DoGoto(LGoto* instr) {
  EmitGoto(instr->block_id());
}

Condition LCodeGen::TokenToCondition(Token::Value op, bool is_unsigned) {
  Condition cond = kNoCondition;
  switch (op) {
    case Token::EQ:
    case Token::EQ_STRICT:
      cond = eq;
      break;
    case Token::NE:
    case Token::NE_STRICT:
      cond = ne;
      break;
    case Token::LT:
      cond = is_unsigned ? lo : lt;
      break;
    case Token::GT:
      cond = is_unsigned ? hi : gt;
      break;
    case Token::LTE:
      cond = is_unsigned ? ls : le;
      break;
    case Token::GTE:
      cond = is_unsigned ? hs : ge;
      break;
    case Token::IN:
    case Token::INSTANCEOF:
    default:
      UNREACHABLE();
  }
  return cond;
}

void LCodeGen::DoCompareNumericAndBranch(LCompareNumericAndBranch* instr) {
  LOperand* left = instr->left();
  LOperand* right = instr->right();
  Condition cond = TokenToCondition(instr->op(), false);

  if (left->IsConstantOperand() && right->IsConstantOperand()) {
    // We can statically evaluate the comparison.
    double left_val = ToDouble(LConstantOperand::cast(left));
    double right_val = ToDouble(LConstantOperand::cast(right));
    int next_block = EvalComparison(instr->op(), left_val, right_val) ?
        instr->TrueDestination(chunk_) : instr->FalseDestination(chunk_);
    EmitGoto(next_block);
  } else {
    if (instr->is_double()) {
      UNREACHABLE();
#if 0
      // Compare left and right as doubles and load the
      // resulting flags into the normal status register.
      FPURegister left_reg = ToDoubleRegister(left);
      FPURegister right_reg = ToDoubleRegister(right);

      // If a NaN is involved, i.e. the result is unordered,
      // jump to false block label.
      __ BranchF(NULL, chunk_->GetAssemblyLabel(false_block), eq,
                 left_reg, right_reg);

      EmitBranchF(true_block, false_block, cond, left_reg, right_reg);
#endif
    } else {
      Register cmp_left;
      Operand cmp_right = Operand((int64_t)0);

      if (right->IsConstantOperand()) {
        int32_t value = ToInteger32(LConstantOperand::cast(right));
        if (instr->hydrogen_value()->representation().IsSmi()) {
          cmp_left = ToRegister(left);
          cmp_right = Operand(Smi::FromInt(value));
        } else {
          cmp_left = ToRegister(left);
          cmp_right = Operand(value);
        }
      } else if (left->IsConstantOperand()) {
        int32_t value = ToInteger32(LConstantOperand::cast(left));
        if (instr->hydrogen_value()->representation().IsSmi()) {
           cmp_left = ToRegister(right);
           cmp_right = Operand(Smi::FromInt(value));
        } else {
          cmp_left = ToRegister(right);
          cmp_right = Operand(value);
        }
        // We transposed the operands. Reverse the condition.
        cond = ReverseCondition(cond);
      } else {
        cmp_left = ToRegister(left);
        cmp_right = Operand(ToRegister(right));
      }

      EmitBranch(instr, cond, cmp_left, cmp_right);
    }
  }
}

void LCodeGen::DoCmpObjectEqAndBranch(LCmpObjectEqAndBranch* instr) {
  Register left = ToRegister(instr->left());
  Register right = ToRegister(instr->right());

  EmitBranch(instr, eq, left, Operand(right));
}

void LCodeGen::DoCmpHoleAndBranch(LCmpHoleAndBranch* instr) { UNREACHABLE(); }


Condition LCodeGen::EmitIsObject(Register input,
                                 Register temp1,
                                 Register temp2,
                                 Label* is_not_object,
                                 Label* is_object) {  UNREACHABLE();  return al;}


void LCodeGen::DoIsObjectAndBranch(LIsObjectAndBranch* instr) {
  Register reg = ToRegister(instr->value());
  Register temp1 = ToRegister(instr->temp());
  Register temp2 = scratch0();

  Condition true_cond =
      EmitIsObject(reg, temp1, temp2,
          instr->FalseLabel(chunk_), instr->TrueLabel(chunk_));

  EmitBranch(instr, true_cond, temp2,
             Operand(LAST_NONCALLABLE_SPEC_OBJECT_TYPE));
}

Condition LCodeGen::EmitIsString(Register input,
                                 Register temp1,
                                 Label* is_not_string,
                                 SmiCheck check_needed = INLINE_SMI_CHECK) {
  if (check_needed == INLINE_SMI_CHECK) {
    __ JumpIfSmi(input, is_not_string);
  }
  __ GetObjectType(input, temp1, temp1);

  return lt;
}

void LCodeGen::DoIsStringAndBranch(LIsStringAndBranch* instr) {  UNREACHABLE();  }


void LCodeGen::DoIsSmiAndBranch(LIsSmiAndBranch* instr) {
  Register input_reg = EmitLoadRegister(instr->value(), at);
  __ And(at, input_reg, kSmiTagMask);
  EmitBranch(instr, eq, at, Operand(zero));
}


void LCodeGen::DoIsUndetectableAndBranch(LIsUndetectableAndBranch* instr) {
  Register input = ToRegister(instr->value());
  Register temp = ToRegister(instr->temp());

  if (!instr->hydrogen()->value()->IsHeapObject()) {
    __ JumpIfSmi(input, instr->FalseLabel(chunk_));
  }
  __ ld(temp, FieldMemOperand(input, HeapObject::kMapOffset));
  __ ld1u(temp, FieldMemOperand(temp, Map::kBitFieldOffset));
  __ And(at, temp, Operand(1 << Map::kIsUndetectable));
  EmitBranch(instr, ne, at, Operand(zero));

}

static Condition ComputeCompareCondition(Token::Value op) {
  switch (op) {
    case Token::EQ_STRICT:
    case Token::EQ:
      return eq;
    case Token::LT:
      return lt;
    case Token::GT:
      return gt;
    case Token::LTE:
      return le;
    case Token::GTE:
      return ge;
    default:
      UNREACHABLE();
      return kNoCondition;
  }
}

void LCodeGen::DoStringCompareAndBranch(LStringCompareAndBranch* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  Token::Value op = instr->op();

  Handle<Code> ic = CompareIC::GetUninitialized(isolate(), op);
  CallCode(ic, RelocInfo::CODE_TARGET, instr);

  Condition condition = ComputeCompareCondition(op);

  EmitBranch(instr, condition, v0, Operand(zero));
}

static InstanceType TestType(HHasInstanceTypeAndBranch* instr) {
  InstanceType from = instr->from();
  InstanceType to = instr->to();
  if (from == FIRST_TYPE) return to;
  ASSERT(from == to || to == LAST_TYPE);
  return from;
}

static Condition BranchCondition(HHasInstanceTypeAndBranch* instr) {
  InstanceType from = instr->from();
  InstanceType to = instr->to();
  if (from == to) return eq;
  if (to == LAST_TYPE) return hs;
  if (from == FIRST_TYPE) return ls;
  UNREACHABLE();
  return eq;
}

void LCodeGen::DoHasInstanceTypeAndBranch(LHasInstanceTypeAndBranch* instr) {
  Register scratch = scratch0();
  Register input = ToRegister(instr->value());

  if (!instr->hydrogen()->value()->IsHeapObject()) {
    __ JumpIfSmi(input, instr->FalseLabel(chunk_));
  }

  __ GetObjectType(input, scratch, scratch);
  EmitBranch(instr,
             BranchCondition(instr->hydrogen()),
             scratch,
             Operand(TestType(instr->hydrogen())));
}

void LCodeGen::DoGetCachedArrayIndex(LGetCachedArrayIndex* instr) {
  Register input = ToRegister(instr->value());
  Register result = ToRegister(instr->result());

  __ AssertString(input);

  __ ld4u(result, FieldMemOperand(input, String::kHashFieldOffset));
  __ IndexFromHash(result, result);
}

void LCodeGen::DoHasCachedArrayIndexAndBranch(
    LHasCachedArrayIndexAndBranch* instr) {
  Register input = ToRegister(instr->value());
  Register scratch = scratch0();

  __ ld(scratch,
         FieldMemOperand(input, String::kHashFieldOffset));
  __ And(at, scratch, Operand(String::kContainsCachedArrayIndexMask));
  EmitBranch(instr, eq, at, Operand(zero));
}

// Branches to a label or falls through with the answer in flags.  Trashes
// the temp registers, but not the input.
void LCodeGen::EmitClassOfTest(Label* is_true,
                               Label* is_false,
                               Handle<String>class_name,
                               Register input,
                               Register temp,
                               Register temp2) {  UNREACHABLE();  }


void LCodeGen::DoClassOfTestAndBranch(LClassOfTestAndBranch* instr) {
  Register input = ToRegister(instr->value());
  Register temp = scratch0();
  Register temp2 = ToRegister(instr->temp());
  Handle<String> class_name = instr->hydrogen()->class_name();

  EmitClassOfTest(instr->TrueLabel(chunk_), instr->FalseLabel(chunk_),
                  class_name, input, temp, temp2);

  EmitBranch(instr, eq, temp, Operand(class_name));
}

void LCodeGen::DoCmpMapAndBranch(LCmpMapAndBranch* instr) {
  Register reg = ToRegister(instr->value());
  Register temp = ToRegister(instr->temp());

  __ ld(temp, FieldMemOperand(reg, HeapObject::kMapOffset));
  EmitBranch(instr, eq, temp, Operand(instr->map()));
}

void LCodeGen::DoInstanceOf(LInstanceOf* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  Label true_label, done;
  ASSERT(ToRegister(instr->left()).is(a0));  // Object is in a0.
  ASSERT(ToRegister(instr->right()).is(a1));  // Function is in a1.
  Register result = ToRegister(instr->result());
  ASSERT(result.is(v0));

  InstanceofStub stub(InstanceofStub::kArgsInRegisters);
  CallCode(stub.GetCode(isolate()), RelocInfo::CODE_TARGET, instr);

  __ Branch(&true_label, eq, result, Operand(zero));
  __ li(result, Operand(factory()->false_value()));
  __ Branch(&done);
  __ bind(&true_label);
  __ li(result, Operand(factory()->true_value()));
  __ bind(&done);
}

void LCodeGen::DoInstanceOfKnownGlobal(LInstanceOfKnownGlobal* instr) {
  class DeferredInstanceOfKnownGlobal V8_FINAL: public LDeferredCode {
   public:
    DeferredInstanceOfKnownGlobal(LCodeGen* codegen,
                                  LInstanceOfKnownGlobal* instr)
        : LDeferredCode(codegen), instr_(instr) { }
    virtual void Generate() V8_OVERRIDE {
      codegen()->DoDeferredInstanceOfKnownGlobal(instr_, &map_check_);
    }
    virtual LInstruction* instr() V8_OVERRIDE { return instr_; }
    Label* map_check() { return &map_check_; }

   private:
    LInstanceOfKnownGlobal* instr_;
    Label map_check_;
  };

  DeferredInstanceOfKnownGlobal* deferred;
  deferred = new(zone()) DeferredInstanceOfKnownGlobal(this, instr);

  Label done, false_result;
  Register object = ToRegister(instr->value());
  Register temp = ToRegister(instr->temp());
  Register result = ToRegister(instr->result());

  ASSERT(object.is(a0));
  ASSERT(result.is(v0));

  // A Smi is not instance of anything.
  __ JumpIfSmi(object, &false_result);

  // This is the inlined call site instanceof cache. The two occurences of the
  // hole value will be patched to the last map/result pair generated by the
  // instanceof stub.
  Label cache_miss;
  Register map = temp;
  __ ld(map, FieldMemOperand(object, HeapObject::kMapOffset));

  Assembler::BlockTrampolinePoolScope block_trampoline_pool(masm_);
  __ bind(deferred->map_check());  // Label for calculating code patching.
  // We use Factory::the_hole_value() on purpose instead of loading from the
  // root array to force relocation to be able to later patch with
  // the cached map.
  Handle<Cell> cell = factory()->NewCell(factory()->the_hole_value());
  __ li(at, Operand(Handle<Object>(cell)));
  __ ld(at, FieldMemOperand(at, PropertyCell::kValueOffset));
  __ Branch(&cache_miss, ne, map, Operand(at));
  // We use Factory::the_hole_value() on purpose instead of loading from the
  // root array to force relocation to be able to later patch
  // with true or false.
  __ li(result, Operand(factory()->the_hole_value()), CONSTANT_SIZE);
  __ Branch(&done);

  // The inlined call site cache did not match. Check null and string before
  // calling the deferred code.
  __ bind(&cache_miss);
  // Null is not instance of anything.
  __ LoadRoot(temp, Heap::kNullValueRootIndex);
  __ Branch(&false_result, eq, object, Operand(temp));

  // String values is not instance of anything.
  Condition cc = __ IsObjectStringType(object, temp, temp);
  __ Branch(&false_result, cc, temp, Operand(zero));

  // Go to the deferred code.
  __ Branch(deferred->entry());

  __ bind(&false_result);
  __ LoadRoot(result, Heap::kFalseValueRootIndex);

  // Here result has either true or false. Deferred code also produces true or
  // false object.
  __ bind(deferred->exit());
  __ bind(&done);
}

void LCodeGen::DoDeferredInstanceOfKnownGlobal(LInstanceOfKnownGlobal* instr,
                                               Label* map_check) {
  Register result = ToRegister(instr->result());
  ASSERT(result.is(v0));

  InstanceofStub::Flags flags = InstanceofStub::kNoFlags;
  flags = static_cast<InstanceofStub::Flags>(
      flags | InstanceofStub::kArgsInRegisters);
  flags = static_cast<InstanceofStub::Flags>(
      flags | InstanceofStub::kCallSiteInlineCheck);
  flags = static_cast<InstanceofStub::Flags>(
      flags | InstanceofStub::kReturnTrueFalseObject);
  InstanceofStub stub(flags);

  PushSafepointRegistersScope scope(this, Safepoint::kWithRegisters);
  LoadContextFromDeferred(instr->context());

  // Get the temp register reserved by the instruction. This needs to be t0 as
  // its slot of the pushing of safepoint registers is used to communicate the
  // offset to the location of the map check.
  Register temp = ToRegister(instr->temp());
  ASSERT(temp.is(t0));
  __ LoadHeapObject(InstanceofStub::right(), instr->function());
  static const int kAdditionalDelta = 7;
  int delta = masm_->InstructionsGeneratedSince(map_check) + kAdditionalDelta;
  Label before_push_delta;
  __ bind(&before_push_delta);
  {
    Assembler::BlockTrampolinePoolScope block_trampoline_pool(masm_);
    __ li(temp, Operand(delta * kPointerSize), CONSTANT_SIZE);
    __ StoreToSafepointRegisterSlot(temp, temp);
  }
  CallCodeGeneric(stub.GetCode(isolate()),
                  RelocInfo::CODE_TARGET,
                  instr,
                  RECORD_SAFEPOINT_WITH_REGISTERS_AND_NO_ARGUMENTS);
  LEnvironment* env = instr->GetDeferredLazyDeoptimizationEnvironment();
  safepoints_.RecordLazyDeoptimizationIndex(env->deoptimization_index());
  // Put the result value into the result register slot and
  // restore all registers.
  __ StoreToSafepointRegisterSlot(result, result);
}

void LCodeGen::DoCmpT(LCmpT* instr) {  UNREACHABLE();  }


void LCodeGen::DoReturn(LReturn* instr) {
  if (FLAG_trace && info()->IsOptimizing()) {
    // Push the return value on the stack as the parameter.
    // Runtime::TraceExit returns its parameter in v0.
    __ push(v0);
    __ CallRuntime(Runtime::kTraceExit, 1);
  }

  //FIXME
#if 0 
  if (info()->saves_caller_doubles()) {
    ASSERT(NeedsEagerFrame());
    BitVector* doubles = chunk()->allocated_double_registers();
    BitVector::Iterator save_iterator(doubles);
    int count = 0;
    while (!save_iterator.Done()) {
      __ ldc1(DoubleRegister::FromAllocationIndex(save_iterator.Current()),
              MemOperand(sp, count * kDoubleSize));
      save_iterator.Advance();
      count++;
    }
  }
#endif

  int no_frame_start = -1;
  if (NeedsEagerFrame()) {
    __ move(sp, fp);
    __ Pop(ra, fp);
    no_frame_start = masm_->pc_offset();
  }
  if (instr->has_constant_parameter_count()) {
    int parameter_count = ToInteger32(instr->constant_parameter_count());
    int32_t sp_delta = (parameter_count + 1) * kPointerSize;
    if (sp_delta != 0) {
      __ Addu(sp, sp, Operand(sp_delta));
    }
  } else {
    Register reg = ToRegister(instr->parameter_count());
    // The argument count parameter is a smi
    __ SmiUntag(reg);
    __ sll(at, reg, kPointerSizeLog2);
    __ Addu(sp, sp, at);
  }

  __ Jump(ra);

  if (no_frame_start != -1) {
    info_->AddNoFrameRange(no_frame_start, masm_->pc_offset());
  }
}


void LCodeGen::DoLoadGlobalCell(LLoadGlobalCell* instr) {
  Register result = ToRegister(instr->result());
  __ li(at, Operand(Handle<Object>(instr->hydrogen()->cell().handle())));
  __ ld(result, FieldMemOperand(at, Cell::kValueOffset));
  if (instr->hydrogen()->RequiresHoleCheck()) {
    __ LoadRoot(at, Heap::kTheHoleValueRootIndex);
    DeoptimizeIf(eq, instr->environment(), result, Operand(at));
  }
}

void LCodeGen::DoLoadGlobalGeneric(LLoadGlobalGeneric* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  ASSERT(ToRegister(instr->global_object()).is(a0));
  ASSERT(ToRegister(instr->result()).is(v0));

  __ li(a2, Operand(instr->name()));
  RelocInfo::Mode mode = instr->for_typeof() ? RelocInfo::CODE_TARGET
                                             : RelocInfo::CODE_TARGET_CONTEXT;
  Handle<Code> ic = isolate()->builtins()->LoadIC_Initialize();
  CallCode(ic, mode, instr);
}

void LCodeGen::DoStoreGlobalCell(LStoreGlobalCell* instr) {
  Register value = ToRegister(instr->value());
  Register cell = scratch0();

  // Load the cell.
  __ li(cell, Operand(instr->hydrogen()->cell().handle()));

  // If the cell we are storing to contains the hole it could have
  // been deleted from the property dictionary. In that case, we need
  // to update the property details in the property dictionary to mark
  // it as no longer deleted.
  if (instr->hydrogen()->RequiresHoleCheck()) {
    // We use a temp to check the payload.
    Register payload = ToRegister(instr->temp());
    __ ld(payload, FieldMemOperand(cell, Cell::kValueOffset));
    __ LoadRoot(at, Heap::kTheHoleValueRootIndex);
    DeoptimizeIf(eq, instr->environment(), payload, Operand(at));
  }

  // Store the value.
  __ st(value, FieldMemOperand(cell, Cell::kValueOffset));
  // Cells are always rescanned, so no write barrier here.
}


void LCodeGen::DoStoreGlobalGeneric(LStoreGlobalGeneric* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  ASSERT(ToRegister(instr->global_object()).is(a1));
  ASSERT(ToRegister(instr->value()).is(a0));

  __ li(a2, Operand(instr->name()));
  Handle<Code> ic = (instr->strict_mode_flag() == kStrictMode)
      ? isolate()->builtins()->StoreIC_Initialize_Strict()
      : isolate()->builtins()->StoreIC_Initialize();
  CallCode(ic, RelocInfo::CODE_TARGET_CONTEXT, instr);
}

void LCodeGen::DoLoadContextSlot(LLoadContextSlot* instr) {
  Register context = ToRegister(instr->context());
  Register result = ToRegister(instr->result());

  __ ld(result, ContextOperand(context, instr->slot_index()));
  if (instr->hydrogen()->RequiresHoleCheck()) {
    __ LoadRoot(at, Heap::kTheHoleValueRootIndex);

    if (instr->hydrogen()->DeoptimizesOnHole()) {
      DeoptimizeIf(eq, instr->environment(), result, Operand(at));
    } else {
      Label is_not_hole;
      __ Branch(&is_not_hole, ne, result, Operand(at));
      __ LoadRoot(result, Heap::kUndefinedValueRootIndex);
      __ bind(&is_not_hole);
    }
  }
}

void LCodeGen::DoStoreContextSlot(LStoreContextSlot* instr) {
  Register context = ToRegister(instr->context());
  Register value = ToRegister(instr->value());
  Register scratch = scratch0();
  MemOperand target = ContextOperand(context, instr->slot_index());

  Label skip_assignment;

  if (instr->hydrogen()->RequiresHoleCheck()) {
    __ ld(scratch, target);
    __ LoadRoot(at, Heap::kTheHoleValueRootIndex);

    if (instr->hydrogen()->DeoptimizesOnHole()) {
      DeoptimizeIf(eq, instr->environment(), scratch, Operand(at));
    } else {
      __ Branch(&skip_assignment, ne, scratch, Operand(at));
    }
  }

  __ st(value, target);
  if (instr->hydrogen()->NeedsWriteBarrier()) {
    SmiCheck check_needed =
        instr->hydrogen()->value()->IsHeapObject()
            ? OMIT_SMI_CHECK : INLINE_SMI_CHECK;
    __ RecordWriteContextSlot(context,
                              target.offset(),
                              value,
                              scratch0(),
                              GetRAState(),
                              kSaveFPRegs,
                              EMIT_REMEMBERED_SET,
                              check_needed);
  }

  __ bind(&skip_assignment);
}

void LCodeGen::DoLoadNamedField(LLoadNamedField* instr) {
  HObjectAccess access = instr->hydrogen()->access();
  int offset = access.offset();
  Register object = ToRegister(instr->object());

  if (access.IsExternalMemory()) {
    Register result = ToRegister(instr->result());
    MemOperand operand = MemOperand(object, offset);
    if (access.representation().IsByte()) {
      __ ld1u(result, operand);
    } else {
      __ ld(result, operand);
    }
    return;
  }

  if (instr->hydrogen()->representation().IsDouble()) {
    DoubleRegister result = ToDoubleRegister(instr->result());
    __ ld(Register::from_code(result.code()), FieldMemOperand(object, offset));
    return;
  }

  Register result = ToRegister(instr->result());
  if (!access.IsInobject()) {
    __ ld(result, FieldMemOperand(object, JSObject::kPropertiesOffset));
    object = result;
  }
  MemOperand operand = FieldMemOperand(object, offset);
  if (access.representation().IsByte()) {
    __ ld1u(result, operand);
  } else {
    __ ld(result, operand);
  }
}

void LCodeGen::DoLoadRoot(LLoadRoot* instr) {
  Register result = ToRegister(instr->result());
  __ LoadRoot(result, instr->index());
}

void LCodeGen::DoLoadNamedGeneric(LLoadNamedGeneric* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  ASSERT(ToRegister(instr->object()).is(a0));
  ASSERT(ToRegister(instr->result()).is(v0));

  // Name is always in a2.
  __ li(a2, Operand(instr->name()));
  Handle<Code> ic = isolate()->builtins()->LoadIC_Initialize();
  CallCode(ic, RelocInfo::CODE_TARGET, instr);
}

void LCodeGen::DoLoadFunctionPrototype(LLoadFunctionPrototype* instr) {
  Register scratch = scratch0();
  Register function = ToRegister(instr->function());
  Register result = ToRegister(instr->result());

  // Check that the function really is a function. Load map into the
  // result register.
  __ GetObjectType(function, result, scratch);
  DeoptimizeIf(ne, instr->environment(), scratch, Operand(JS_FUNCTION_TYPE));

  // Make sure that the function has an instance prototype.
  Label non_instance;
  __ ld1u(scratch, FieldMemOperand(result, Map::kBitFieldOffset));
  __ And(scratch, scratch, Operand(1 << Map::kHasNonInstancePrototype));
  __ Branch(&non_instance, ne, scratch, Operand(zero));

  // Get the prototype or initial map from the function.
  __ ld(result,
         FieldMemOperand(function, JSFunction::kPrototypeOrInitialMapOffset));

  // Check that the function has a prototype or an initial map.
  __ LoadRoot(at, Heap::kTheHoleValueRootIndex);
  DeoptimizeIf(eq, instr->environment(), result, Operand(at));

  // If the function does not have an initial map, we're done.
  Label done;
  __ GetObjectType(result, scratch, scratch);
  __ Branch(&done, ne, scratch, Operand(MAP_TYPE));

  // Get the prototype from the initial map.
  __ ld(result, FieldMemOperand(result, Map::kPrototypeOffset));
  __ Branch(&done);

  // Non-instance prototype: Fetch prototype from constructor field
  // in initial map.
  __ bind(&non_instance);
  __ ld(result, FieldMemOperand(result, Map::kConstructorOffset));

  // All done.
  __ bind(&done);
}


void LCodeGen::DoLoadExternalArrayPointer(
    LLoadExternalArrayPointer* instr) {
  Register to_reg = ToRegister(instr->result());
  Register from_reg  = ToRegister(instr->object());
  __ ld(to_reg, FieldMemOperand(from_reg,
                                ExternalArray::kExternalPointerOffset));
}

void LCodeGen::DoAccessArgumentsAt(LAccessArgumentsAt* instr) {
  Register arguments = ToRegister(instr->arguments());
  Register result = ToRegister(instr->result());
  if (instr->length()->IsConstantOperand() &&
      instr->index()->IsConstantOperand()) {
    int const_index = ToInteger32(LConstantOperand::cast(instr->index()));
    int const_length = ToInteger32(LConstantOperand::cast(instr->length()));
    int index = (const_length - const_index) + 1;
    __ ld(result, MemOperand(arguments, index * kPointerSize));
  } else {
    Register length = ToRegister(instr->length());
    Register index = ToRegister(instr->index());
    // There are two words between the frame pointer and the last argument.
    // Subtracting from length accounts for one of them, add one more.
    __ sub(length, length, index);
    __ Addu(length, length, Operand(1));
    __ sll(length, length, kPointerSizeLog2);
    __ Addu(at, arguments, Operand(length));
    __ ld(result, MemOperand(at, 0));
  }
}

void LCodeGen::DoLoadKeyedExternalArray(LLoadKeyed* instr) {
  Register external_pointer = ToRegister(instr->elements());
  Register key = no_reg;
  ElementsKind elements_kind = instr->elements_kind();
  bool key_is_constant = instr->key()->IsConstantOperand();
  int constant_key = 0;
  if (key_is_constant) {
    constant_key = ToInteger32(LConstantOperand::cast(instr->key()));
    if (constant_key & 0xF0000000) {
      Abort(kArrayIndexConstantValueTooBig);
    }
  } else {
    key = ToRegister(instr->key());
  }
  int element_size_shift = ElementsKindToShiftSize(elements_kind);
  int is_smi = instr->hydrogen()->key()->representation().IsSmi();
  int additional_offset = instr->additional_index() << element_size_shift;

  if (elements_kind == EXTERNAL_FLOAT_ELEMENTS ||
      elements_kind == EXTERNAL_DOUBLE_ELEMENTS) {
    DoubleRegister result = ToDoubleRegister(instr->result());
    if (key_is_constant) {
      __ Addu(scratch0(), external_pointer, constant_key << element_size_shift);
    } else {
      __ sra(scratch0(), key, 32);
      __ sll(scratch0(), scratch0(), element_size_shift);
      __ Addu(scratch0(), scratch0(), external_pointer);
    }
    if (elements_kind == EXTERNAL_FLOAT_ELEMENTS) {
      __ ld4s(Register::from_code(result.code()), MemOperand(scratch0(), additional_offset));
      //RegList saved_regs = a0.bit() | a1.bit() | a2.bit() | a3.bit() | r4.bit() | lr.bit();
      RegList saved_regs = a0.bit() | a1.bit() | a2.bit() | a3.bit() | r4.bit() | r5.bit() | r6.bit()
	                   | r27.bit() | r28.bit() | r29.bit() | lr.bit();
      __ MultiPush(saved_regs);
      __ PrepareCallCFunction(1, scratch1());
      __ move(a0, Register::from_code(result.code()));
      __ CallCFunction(
          ExternalReference::cvt_float_to_double(isolate()), 1);
      __ move(Register::from_code(result.code()), a0);
      __ MultiPop(saved_regs);
    } else  {  // i.e. elements_kind == EXTERNAL_DOUBLE_ELEMENTS
      __ ld(result, MemOperand(scratch0(), additional_offset));
    }
  } else {
    Register result = ToRegister(instr->result());
    MemOperand mem_operand = PrepareKeyedOperand(
        key, external_pointer, key_is_constant, constant_key,
        element_size_shift, is_smi,
        instr->additional_index(), additional_offset);
    switch (elements_kind) {
      case EXTERNAL_BYTE_ELEMENTS:
        __ ld1s(result, mem_operand);
        break;
      case EXTERNAL_PIXEL_ELEMENTS:
      case EXTERNAL_UNSIGNED_BYTE_ELEMENTS:
        __ ld1u(result, mem_operand);
        break;
      case EXTERNAL_SHORT_ELEMENTS:
        __ ld2s(result, mem_operand);
        break;
      case EXTERNAL_UNSIGNED_SHORT_ELEMENTS:
        __ ld2u(result, mem_operand);
        break;
      case EXTERNAL_INT_ELEMENTS:
        __ ld4s(result, mem_operand);
        break;
      case EXTERNAL_UNSIGNED_INT_ELEMENTS:
        __ ld4u(result, mem_operand);
        if (!instr->hydrogen()->CheckFlag(HInstruction::kUint32)) {
          DeoptimizeIf(Ugreater_equal, instr->environment(),
              result, Operand(0x80000000));
        }
        break;
      case EXTERNAL_FLOAT_ELEMENTS:
      case EXTERNAL_DOUBLE_ELEMENTS:
      case FAST_DOUBLE_ELEMENTS:
      case FAST_ELEMENTS:
      case FAST_SMI_ELEMENTS:
      case FAST_HOLEY_DOUBLE_ELEMENTS:
      case FAST_HOLEY_ELEMENTS:
      case FAST_HOLEY_SMI_ELEMENTS:
      case DICTIONARY_ELEMENTS:
      case NON_STRICT_ARGUMENTS_ELEMENTS:
        UNREACHABLE();
        break;
    }
  }
}


void LCodeGen::DoLoadKeyedFixedDoubleArray(LLoadKeyed* instr) {
  Register elements = ToRegister(instr->elements());
  bool key_is_constant = instr->key()->IsConstantOperand();
  Register key = no_reg;
  DoubleRegister result = ToDoubleRegister(instr->result());
  Register scratch = scratch0();

  int element_size_shift = ElementsKindToShiftSize(FAST_DOUBLE_ELEMENTS);
  int constant_key = 0;
  if (key_is_constant) {
    constant_key = ToInteger32(LConstantOperand::cast(instr->key()));
    if (constant_key & 0xF0000000) {
      Abort(kArrayIndexConstantValueTooBig);
    }
  } else {
    key = ToRegister(instr->key());
  }

  int base_offset = (FixedDoubleArray::kHeaderSize - kHeapObjectTag) +
      ((constant_key + instr->additional_index()) << element_size_shift);
  if (!key_is_constant) {
    __ sra(scratch, key, 32);
    __ sll(scratch, scratch, element_size_shift);
    __ Addu(elements, elements, scratch);
  }
  __ Addu(elements, elements, Operand(base_offset));
  __ ld(result, MemOperand(elements));
  if (instr->hydrogen()->RequiresHoleCheck()) {
    __ ld4u(scratch, MemOperand(elements, sizeof(kHoleNanLower32)));
    DeoptimizeIf(eq, instr->environment(), scratch, Operand(kHoleNanUpper32));
  }
}

void LCodeGen::DoLoadKeyedFixedArray(LLoadKeyed* instr) {
  Register elements = ToRegister(instr->elements());
  Register result = ToRegister(instr->result());
  Register scratch = scratch0();
  Register store_base = scratch;
  int offset = 0;

  if (instr->key()->IsConstantOperand()) {
    LConstantOperand* const_operand = LConstantOperand::cast(instr->key());
    offset = FixedArray::OffsetOfElementAt(ToInteger32(const_operand) +
                                           instr->additional_index());
    store_base = elements;
  } else {
    Register key = ToRegister(instr->key());
    // Even though the HLoadKeyed instruction forces the input
    // representation for the key to be an integer, the input gets replaced
    // during bound check elimination with the index argument to the bounds
    // check, which can be tagged, so that case must be handled here, too.
    if (instr->hydrogen()->key()->representation().IsSmi()) {
      __ sra(scratch, key, kSmiTagSize + kSmiShiftSize);
      __ sll(scratch, scratch, kPointerSizeLog2);
      __ add(scratch, elements, scratch);
    } else {
      __ sll(scratch, key, kPointerSizeLog2);
      __ add(scratch, elements, scratch);
    }
    offset = FixedArray::OffsetOfElementAt(instr->additional_index());
  }
  __ ld(result, FieldMemOperand(store_base, offset));

  // Check for the hole value.
  if (instr->hydrogen()->RequiresHoleCheck()) {
    if (IsFastSmiElementsKind(instr->hydrogen()->elements_kind())) {
      __ And(scratch, result, Operand(kSmiTagMask));
      DeoptimizeIf(ne, instr->environment(), scratch, Operand(zero));
    } else {
      __ LoadRoot(scratch, Heap::kTheHoleValueRootIndex);
      DeoptimizeIf(eq, instr->environment(), result, Operand(scratch));
    }
  }
}


void LCodeGen::DoLoadKeyed(LLoadKeyed* instr) {
  if (instr->is_external()) {
    DoLoadKeyedExternalArray(instr);
  } else if (instr->hydrogen()->representation().IsDouble()) {
    DoLoadKeyedFixedDoubleArray(instr);
  } else {
    DoLoadKeyedFixedArray(instr);
  }
}

MemOperand LCodeGen::PrepareKeyedOperand(Register key,
                                         Register base,
                                         bool key_is_constant,
                                         int constant_key,
                                         int element_size,
                                         int is_smi,
                                         int additional_index,
                                         int additional_offset) {
  uint64_t tmp64 = additional_index;

  if (additional_index != 0 && !key_is_constant) {
    if (is_smi)
      tmp64 = tmp64 << 32;
    __ Addu(scratch0(), key, Operand(tmp64));
  }

  if (key_is_constant) {
    return MemOperand(base,
                      (constant_key << element_size) + additional_offset);
  }

  if (additional_index == 0) {
    if (is_smi) {
      __ sra(scratch0(), key, 32);
      __ sll(scratch0(), scratch0(), element_size);
      __ Addu(scratch0(), base, scratch0());
      return MemOperand(scratch0());
    } else {
      __ sll(scratch0(), key, element_size);
      __ Addu(scratch0(), base, scratch0());
      return MemOperand(scratch0());
    }
  }

  if (is_smi) {
    __ sra(scratch0(), scratch0(), 32);
    __ sll(scratch0(), scratch0(), element_size);
    __ Addu(scratch0(), base, scratch0());
    return MemOperand(scratch0());
  } else {
    __ sll(scratch0(), scratch0(), element_size);
    __ Addu(scratch0(), base, scratch0());
    return MemOperand(scratch0());
  }
}

void LCodeGen::DoLoadKeyedGeneric(LLoadKeyedGeneric* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  ASSERT(ToRegister(instr->object()).is(a1));
  ASSERT(ToRegister(instr->key()).is(a0));

  Handle<Code> ic = isolate()->builtins()->KeyedLoadIC_Initialize();
  CallCode(ic, RelocInfo::CODE_TARGET, instr);
}

void LCodeGen::DoArgumentsElements(LArgumentsElements* instr) {  UNREACHABLE();  }


void LCodeGen::DoArgumentsLength(LArgumentsLength* instr) {  UNREACHABLE();  }


void LCodeGen::DoWrapReceiver(LWrapReceiver* instr) {  UNREACHABLE();  }

void LCodeGen::DoApplyArguments(LApplyArguments* instr) {  UNREACHABLE();  }


void LCodeGen::DoPushArgument(LPushArgument* instr) {  UNREACHABLE();  }


void LCodeGen::DoDrop(LDrop* instr) {
  __ Drop(instr->count());
}

void LCodeGen::DoThisFunction(LThisFunction* instr) {
  Register result = ToRegister(instr->result());
  __ ld(result, MemOperand(fp, JavaScriptFrameConstants::kFunctionOffset));
}

void LCodeGen::DoContext(LContext* instr) {
  // If there is a non-return use, the context must be moved to a register.
  Register result = ToRegister(instr->result());
  if (info()->IsOptimizing()) {
    __ ld(result, MemOperand(fp, StandardFrameConstants::kContextOffset));
  } else {
    // If there is no frame, the context must be in cp.
    ASSERT(result.is(cp));
  }
}

void LCodeGen::DoOuterContext(LOuterContext* instr) {
  Register context = ToRegister(instr->context());
  Register result = ToRegister(instr->result());
  __ ld(result,
        MemOperand(context, Context::SlotOffset(Context::PREVIOUS_INDEX)));
}

void LCodeGen::DoDeclareGlobals(LDeclareGlobals* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  __ LoadHeapObject(scratch0(), instr->hydrogen()->pairs());
  __ li(scratch1(), Operand(Smi::FromInt(instr->hydrogen()->flags())));
  // The context is the first argument.
  __ Push(cp, scratch0(), scratch1());
  CallRuntime(Runtime::kDeclareGlobals, 3, instr);
}

void LCodeGen::DoGlobalObject(LGlobalObject* instr) {
  Register context = ToRegister(instr->context());
  Register result = ToRegister(instr->result());
  __ ld(result, ContextOperand(context, Context::GLOBAL_OBJECT_INDEX));
}

void LCodeGen::DoGlobalReceiver(LGlobalReceiver* instr) {
  Register global = ToRegister(instr->global_object());
  Register result = ToRegister(instr->result());
  __ ld(result, FieldMemOperand(global, GlobalObject::kGlobalReceiverOffset));
}


void LCodeGen::CallKnownFunction(Handle<JSFunction> function,
                                 int formal_parameter_count,
                                 int arity,
                                 LInstruction* instr,
                                 CallKind call_kind,
                                 A1State a1_state) {  UNREACHABLE();  }


void LCodeGen::DoCallConstantFunction(LCallConstantFunction* instr) {  UNREACHABLE();  }


void LCodeGen::DoDeferredMathAbsTaggedHeapNumber(LMathAbs* instr) {  UNREACHABLE();  }


void LCodeGen::EmitIntegerMathAbs(LMathAbs* instr) {  UNREACHABLE();  }


void LCodeGen::DoMathAbs(LMathAbs* instr) {  UNREACHABLE();  }


void LCodeGen::DoMathFloor(LMathFloor* instr) {  UNREACHABLE();  }


void LCodeGen::DoMathRound(LMathRound* instr) {  UNREACHABLE();  }


void LCodeGen::DoMathSqrt(LMathSqrt* instr) {  UNREACHABLE();  }


void LCodeGen::DoMathPowHalf(LMathPowHalf* instr) {  UNREACHABLE();  }


void LCodeGen::DoPower(LPower* instr) {  UNREACHABLE();  }


void LCodeGen::DoRandom(LRandom* instr) {  UNREACHABLE();  }


void LCodeGen::DoMathExp(LMathExp* instr) {  UNREACHABLE();  }


void LCodeGen::DoMathLog(LMathLog* instr) {  UNREACHABLE();  }


void LCodeGen::DoMathTan(LMathTan* instr) {  UNREACHABLE();  }


void LCodeGen::DoMathCos(LMathCos* instr) {  UNREACHABLE();  }


void LCodeGen::DoMathSin(LMathSin* instr) {  UNREACHABLE();  }


void LCodeGen::DoInvokeFunction(LInvokeFunction* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  ASSERT(ToRegister(instr->function()).is(a1));
  ASSERT(instr->HasPointerMap());

  Handle<JSFunction> known_function = instr->hydrogen()->known_function();
  if (known_function.is_null()) {
    LPointerMap* pointers = instr->pointer_map();
    SafepointGenerator generator(this, pointers, Safepoint::kLazyDeopt);
    ParameterCount count(instr->arity());
    __ InvokeFunction(a1, count, CALL_FUNCTION, generator, CALL_AS_METHOD);
  } else {
    CallKnownFunction(known_function,
                      instr->hydrogen()->formal_parameter_count(),
                      instr->arity(),
                      instr,
                      CALL_AS_METHOD,
                      A1_CONTAINS_TARGET);
  }
}

void LCodeGen::DoCallKeyed(LCallKeyed* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  ASSERT(ToRegister(instr->result()).is(v0));

  int arity = instr->arity();
  Handle<Code> ic =
      isolate()->stub_cache()->ComputeKeyedCallInitialize(arity);
  CallCode(ic, RelocInfo::CODE_TARGET, instr);
}

void LCodeGen::DoCallNamed(LCallNamed* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  ASSERT(ToRegister(instr->result()).is(v0));

  int arity = instr->arity();
  RelocInfo::Mode mode = RelocInfo::CODE_TARGET;
  Handle<Code> ic =
      isolate()->stub_cache()->ComputeCallInitialize(arity, mode);
  __ li(a2, Operand(instr->name()));
  CallCode(ic, mode, instr);
}

void LCodeGen::DoCallFunction(LCallFunction* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  ASSERT(ToRegister(instr->function()).is(a1));
  ASSERT(ToRegister(instr->result()).is(v0));

  int arity = instr->arity();
  CallFunctionStub stub(arity, NO_CALL_FUNCTION_FLAGS);
  CallCode(stub.GetCode(isolate()), RelocInfo::CODE_TARGET, instr);
}

void LCodeGen::DoCallGlobal(LCallGlobal* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  ASSERT(ToRegister(instr->result()).is(v0));

  int arity = instr->arity();
  RelocInfo::Mode mode = RelocInfo::CODE_TARGET_CONTEXT;
  Handle<Code> ic =
      isolate()->stub_cache()->ComputeCallInitialize(arity, mode);
  __ li(a2, Operand(instr->name()));
  CallCode(ic, mode, instr);
}

void LCodeGen::DoCallKnownGlobal(LCallKnownGlobal* instr) {
  ASSERT(ToRegister(instr->result()).is(v0));
  CallKnownFunction(instr->hydrogen()->target(),
                    instr->hydrogen()->formal_parameter_count(),
                    instr->arity(),
                    instr,
                    CALL_AS_FUNCTION,
                    A1_UNINITIALIZED);
}

void LCodeGen::DoCallNew(LCallNew* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  ASSERT(ToRegister(instr->constructor()).is(a1));
  ASSERT(ToRegister(instr->result()).is(v0));

  __ li(a0, Operand(instr->arity()));
  // No cell in a2 for construct type feedback in optimized code
  Handle<Object> undefined_value(isolate()->factory()->undefined_value());
  __ li(a2, Operand(undefined_value));
  CallConstructStub stub(NO_CALL_FUNCTION_FLAGS);
  CallCode(stub.GetCode(isolate()), RelocInfo::CONSTRUCT_CALL, instr);
}

void LCodeGen::DoCallNewArray(LCallNewArray* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  ASSERT(ToRegister(instr->constructor()).is(a1));
  ASSERT(ToRegister(instr->result()).is(v0));

  __ li(a0, Operand(instr->arity()));
  __ li(a2, Operand(instr->hydrogen()->property_cell()));
  ElementsKind kind = instr->hydrogen()->elements_kind();
  AllocationSiteOverrideMode override_mode =
      (AllocationSite::GetMode(kind) == TRACK_ALLOCATION_SITE)
          ? DISABLE_ALLOCATION_SITES
          : DONT_OVERRIDE;
  ContextCheckMode context_mode = CONTEXT_CHECK_NOT_REQUIRED;

  if (instr->arity() == 0) {
    ArrayNoArgumentConstructorStub stub(kind, context_mode, override_mode);
    CallCode(stub.GetCode(isolate()), RelocInfo::CONSTRUCT_CALL, instr);
  } else if (instr->arity() == 1) {
    Label done;
    if (IsFastPackedElementsKind(kind)) {
      Label packed_case;
      // We might need a change here,
      // look at the first argument.
      __ ld(t1, MemOperand(sp, 0));
      __ Branch(&packed_case, eq, t1, Operand(zero));

      ElementsKind holey_kind = GetHoleyElementsKind(kind);
      ArraySingleArgumentConstructorStub stub(holey_kind, context_mode,
                                              override_mode);
      CallCode(stub.GetCode(isolate()), RelocInfo::CONSTRUCT_CALL, instr);
      __ jmp(&done);
      __ bind(&packed_case);
    }

    ArraySingleArgumentConstructorStub stub(kind, context_mode, override_mode);
    CallCode(stub.GetCode(isolate()), RelocInfo::CONSTRUCT_CALL, instr);
    __ bind(&done);
  } else {
    ArrayNArgumentsConstructorStub stub(kind, context_mode, override_mode);
    CallCode(stub.GetCode(isolate()), RelocInfo::CONSTRUCT_CALL, instr);
  }
}

void LCodeGen::DoStoreCodeEntry(LStoreCodeEntry* instr) {
  Register function = ToRegister(instr->function());
  Register code_object = ToRegister(instr->code_object());
  __ Addu(code_object, code_object,
          Operand(Code::kHeaderSize - kHeapObjectTag));
  __ st(code_object,
        FieldMemOperand(function, JSFunction::kCodeEntryOffset));
}

void LCodeGen::DoCallRuntime(LCallRuntime* instr) {
  CallRuntime(instr->function(), instr->arity(), instr);
}

void LCodeGen::DoInnerAllocatedObject(LInnerAllocatedObject* instr) {
  Register result = ToRegister(instr->result());
  Register base = ToRegister(instr->base_object());
  __ Addu(result, base, Operand(instr->offset()));
}

void LCodeGen::DoStoreNamedField(LStoreNamedField* instr) {
  Representation representation = instr->representation();

  Register object = ToRegister(instr->object());
  Register scratch = scratch0();
  HObjectAccess access = instr->hydrogen()->access();
  int offset = access.offset();

  if (access.IsExternalMemory()) {
    Register value = ToRegister(instr->value());
    MemOperand operand = MemOperand(object, offset);
    if (representation.IsByte()) {
      __ st1(value, operand);
    } else {
      __ st(value, operand);
    }
    return;
  }

  Handle<Map> transition = instr->transition();

  if (FLAG_track_heap_object_fields && representation.IsHeapObject()) {
    Register value = ToRegister(instr->value());
    if (!instr->hydrogen()->value()->type().IsHeapObject()) {
      __ And(scratch, value, Operand(kSmiTagMask));
      DeoptimizeIf(eq, instr->environment(), scratch, Operand(zero));
    }
  } else if (FLAG_track_double_fields && representation.IsDouble()) {
    ASSERT(transition.is_null());
    ASSERT(access.IsInobject());
    ASSERT(!instr->hydrogen()->NeedsWriteBarrier());
    DoubleRegister value = ToDoubleRegister(instr->value());
    __ st(value, FieldMemOperand(object, offset));
    return;
  }

  if (!transition.is_null()) {
    __ li(scratch, Operand(transition));
    __ st(scratch, FieldMemOperand(object, HeapObject::kMapOffset));
    if (instr->hydrogen()->NeedsWriteBarrierForMap()) {
      Register temp = ToRegister(instr->temp());
      // Update the write barrier for the map field.
      __ RecordWriteField(object,
                          HeapObject::kMapOffset,
                          scratch,
                          temp,
                          GetRAState(),
                          kSaveFPRegs,
                          OMIT_REMEMBERED_SET,
                          OMIT_SMI_CHECK);
    }
  }

  // Do the store.
  Register value = ToRegister(instr->value());
  ASSERT(!object.is(value));
  SmiCheck check_needed =
      instr->hydrogen()->value()->IsHeapObject()
          ? OMIT_SMI_CHECK : INLINE_SMI_CHECK;
  if (access.IsInobject()) {
    MemOperand operand = FieldMemOperand(object, offset);
    if (representation.IsByte()) {
      __ st1(value, operand);
    } else {
      __ st(value, operand);
    }
    if (instr->hydrogen()->NeedsWriteBarrier()) {
      // Update the write barrier for the object for in-object properties.
      __ RecordWriteField(object,
                          offset,
                          value,
                          scratch,
                          GetRAState(),
                          kSaveFPRegs,
                          EMIT_REMEMBERED_SET,
                          check_needed);
    }
  } else {
    __ ld(scratch, FieldMemOperand(object, JSObject::kPropertiesOffset));
    MemOperand operand = FieldMemOperand(scratch, offset);
    if (representation.IsByte()) {
      __ st1(value, operand);
    } else {
      __ st(value, operand);
    }
    if (instr->hydrogen()->NeedsWriteBarrier()) {
      // Update the write barrier for the properties array.
      // object is used as a scratch register.
      __ RecordWriteField(scratch,
                          offset,
                          value,
                          object,
                          GetRAState(),
                          kSaveFPRegs,
                          EMIT_REMEMBERED_SET,
                          check_needed);
    }
  }
}

void LCodeGen::DoStoreNamedGeneric(LStoreNamedGeneric* instr) {
  ASSERT(ToRegister(instr->context()).is(cp));
  ASSERT(ToRegister(instr->object()).is(a1));
  ASSERT(ToRegister(instr->value()).is(a0));

  // Name is always in a2.
  __ li(a2, Operand(instr->name()));
  Handle<Code> ic = (instr->strict_mode_flag() == kStrictMode)
      ? isolate()->builtins()->StoreIC_Initialize_Strict()
      : isolate()->builtins()->StoreIC_Initialize();
  CallCode(ic, RelocInfo::CODE_TARGET, instr);
}

void LCodeGen::ApplyCheckIf(Condition condition,
                            LBoundsCheck* check,
                            Register src1,
                            const Operand& src2) {
  if (FLAG_debug_code && check->hydrogen()->skip_check()) {
    Label done;
    __ Branch(&done, NegateCondition(condition), src1, src2);
    __ stop("eliminated bounds check failed");
    __ bind(&done);
  } else {
    DeoptimizeIf(condition, check->environment(), src1, src2);
  }
}

void LCodeGen::DoBoundsCheck(LBoundsCheck* instr) {
  if (instr->hydrogen()->skip_check()) return;

  Condition condition = instr->hydrogen()->allow_equality() ? hi : hs;
  if (instr->index()->IsConstantOperand()) {
    int constant_index =
        ToInteger32(LConstantOperand::cast(instr->index()));
    if (instr->hydrogen()->length()->representation().IsSmi()) {
      __ li(at, Operand(Smi::FromInt(constant_index)));
    } else {
      __ li(at, Operand(constant_index));
    }
    ApplyCheckIf(condition,
                 instr,
                 at,
                 Operand(ToRegister(instr->length())));
  } else {
    ApplyCheckIf(condition,
                 instr,
                 ToRegister(instr->index()),
                 Operand(ToRegister(instr->length())));
  }
}

void LCodeGen::DoStoreKeyedExternalArray(LStoreKeyed* instr) {
  Register external_pointer = ToRegister(instr->elements());
  Register key = no_reg;
  ElementsKind elements_kind = instr->elements_kind();
  bool key_is_constant = instr->key()->IsConstantOperand();
  int constant_key = 0;
  if (key_is_constant) {
    constant_key = ToInteger32(LConstantOperand::cast(instr->key()));
    if (constant_key & 0xF0000000) {
      Abort(kArrayIndexConstantValueTooBig);
    }
  } else {
    key = ToRegister(instr->key());
  }
  int element_size_shift = ElementsKindToShiftSize(elements_kind);
  int is_smi = instr->hydrogen()->key()->representation().IsSmi();
  int additional_offset = instr->additional_index() << element_size_shift;

  if (elements_kind == EXTERNAL_FLOAT_ELEMENTS ||
      elements_kind == EXTERNAL_DOUBLE_ELEMENTS) {
    DoubleRegister value(ToDoubleRegister(instr->value()));
    if (key_is_constant) {
      __ Addu(scratch0(), external_pointer, constant_key <<
          element_size_shift);
    } else {
      __ sra(scratch0(), key, 32);
      __ sll(scratch0(), scratch0(), element_size_shift);
      __ Addu(scratch0(), scratch0(), external_pointer);
    }

    if (elements_kind == EXTERNAL_FLOAT_ELEMENTS) {
      //__ cvt_s_d(double_scratch0(), value);
      RegList saved_regs = a0.bit() | a1.bit() | a2.bit() | a3.bit() | r4.bit() | r5.bit() | r6.bit()
	                   | r27.bit() | r28.bit() | r29.bit() | lr.bit();
      __ MultiPush(saved_regs);
      __ PrepareCallCFunction(1, scratch1());
      __ move(a0, Register::from_code(value.code()));
      __ CallCFunction(
          ExternalReference::cvt_double_to_float(isolate()), 1);
      __ move(scratch1(), a0);
      __ MultiPop(saved_regs);
      __ st4(scratch1(), MemOperand(scratch0(), additional_offset));
    } else {  // i.e. elements_kind == EXTERNAL_DOUBLE_ELEMENTS
      __ st(value, MemOperand(scratch0(), additional_offset));
    }
  } else {
    Register value(ToRegister(instr->value()));
    MemOperand mem_operand = PrepareKeyedOperand(
        key, external_pointer, key_is_constant, constant_key,
        element_size_shift, is_smi,
        instr->additional_index(), additional_offset);
    switch (elements_kind) {
      case EXTERNAL_PIXEL_ELEMENTS:
      case EXTERNAL_BYTE_ELEMENTS:
      case EXTERNAL_UNSIGNED_BYTE_ELEMENTS:
        __ st1(value, mem_operand);
        break;
      case EXTERNAL_SHORT_ELEMENTS:
      case EXTERNAL_UNSIGNED_SHORT_ELEMENTS:
        __ st2(value, mem_operand);
        break;
      case EXTERNAL_INT_ELEMENTS:
      case EXTERNAL_UNSIGNED_INT_ELEMENTS:
        __ st4(value, mem_operand);
        break;
      case EXTERNAL_FLOAT_ELEMENTS:
      case EXTERNAL_DOUBLE_ELEMENTS:
      case FAST_DOUBLE_ELEMENTS:
      case FAST_ELEMENTS:
      case FAST_SMI_ELEMENTS:
      case FAST_HOLEY_DOUBLE_ELEMENTS:
      case FAST_HOLEY_ELEMENTS:
      case FAST_HOLEY_SMI_ELEMENTS:
      case DICTIONARY_ELEMENTS:
      case NON_STRICT_ARGUMENTS_ELEMENTS:
        UNREACHABLE();
        break;
    }
  }
}


void LCodeGen::DoStoreKeyedFixedDoubleArray(LStoreKeyed* instr) {
  DoubleRegister value = ToDoubleRegister(instr->value());
  Register elements = ToRegister(instr->elements());
  Register key = no_reg;
  Register scratch = scratch0();
  bool key_is_constant = instr->key()->IsConstantOperand();
  int constant_key = 0;

  // Calculate the effective address of the slot in the array to store the
  // double value.
  if (key_is_constant) {
    constant_key = ToInteger32(LConstantOperand::cast(instr->key()));
    if (constant_key & 0xF0000000) {
      Abort(kArrayIndexConstantValueTooBig);
    }
  } else {
    key = ToRegister(instr->key());
  }
  int element_size_shift = ElementsKindToShiftSize(FAST_DOUBLE_ELEMENTS);
  if (key_is_constant) {
    __ Addu(scratch, elements, Operand((constant_key << element_size_shift) +
            FixedDoubleArray::kHeaderSize - kHeapObjectTag));
  } else {
    __ sra(scratch, key, 32);
    __ sll(scratch, scratch, element_size_shift);
    __ Addu(scratch, elements, Operand(scratch));
    __ Addu(scratch, scratch,
            Operand(FixedDoubleArray::kHeaderSize - kHeapObjectTag));
  }

#if 0 // FIXME, we should handle NaN case although it rarely happened.
  Label not_nan;
  if (instr->NeedsCanonicalization()) {
    Label is_nan;
    // Check for NaN. All NaNs must be canonicalized.
    __ BranchF(NULL, &is_nan, eq, value, value);
    __ Branch(&not_nan);

    // Only load canonical NaN if the comparison above set the overflow.
    __ bind(&is_nan);
    __ Move(value, FixedDoubleArray::canonical_not_the_hole_nan_as_double());
  }
  __ bind(&not_nan);
#endif

  __ st(value, MemOperand(scratch, instr->additional_index() <<
      element_size_shift));
}


void LCodeGen::DoStoreKeyedFixedArray(LStoreKeyed* instr) {
  Register value = ToRegister(instr->value());
  Register elements = ToRegister(instr->elements());
  Register key = instr->key()->IsRegister() ? ToRegister(instr->key())
      : no_reg;
  Register scratch = scratch0();
  Register store_base = scratch;
  int offset = 0;

  // Do the store.
  if (instr->key()->IsConstantOperand()) {
    ASSERT(!instr->hydrogen()->NeedsWriteBarrier());
    LConstantOperand* const_operand = LConstantOperand::cast(instr->key());
    offset = FixedArray::OffsetOfElementAt(ToInteger32(const_operand) +
                                           instr->additional_index());
    store_base = elements;
  } else {
    // Even though the HLoadKeyed instruction forces the input
    // representation for the key to be an integer, the input gets replaced
    // during bound check elimination with the index argument to the bounds
    // check, which can be tagged, so that case must be handled here, too.
    if (instr->hydrogen()->key()->representation().IsSmi()) {
      __ sra(scratch, key, kSmiTagSize + kSmiShiftSize);
      __ sll(scratch, scratch, kPointerSizeLog2);
      __ add(scratch, elements, scratch);
    } else {
      __ sll(scratch, key, kPointerSizeLog2);
      __ add(scratch, elements, scratch);
    }
    offset = FixedArray::OffsetOfElementAt(instr->additional_index());
  }
  __ st(value, FieldMemOperand(store_base, offset));

  if (instr->hydrogen()->NeedsWriteBarrier()) {
    SmiCheck check_needed =
        instr->hydrogen()->value()->IsHeapObject()
            ? OMIT_SMI_CHECK : INLINE_SMI_CHECK;
    // Compute address of modified element and store it into key register.
    __ Addu(key, store_base, Operand(offset - kHeapObjectTag));
    __ RecordWrite(elements,
                   key,
                   value,
                   GetRAState(),
                   kSaveFPRegs,
                   EMIT_REMEMBERED_SET,
                   check_needed);
  }
}

void LCodeGen::DoStoreKeyed(LStoreKeyed* instr) {
  // By cases: external, fast double
  if (instr->is_external()) {
    DoStoreKeyedExternalArray(instr);
  } else if (instr->hydrogen()->value()->representation().IsDouble()) {
    DoStoreKeyedFixedDoubleArray(instr);
  } else {
    DoStoreKeyedFixedArray(instr);
  }
}

void LCodeGen::DoStoreKeyedGeneric(LStoreKeyedGeneric* instr) {  UNREACHABLE();  }


void LCodeGen::DoTransitionElementsKind(LTransitionElementsKind* instr) {  UNREACHABLE();  }


void LCodeGen::DoTrapAllocationMemento(LTrapAllocationMemento* instr) {  UNREACHABLE();  }


void LCodeGen::DoStringAdd(LStringAdd* instr) {  UNREACHABLE();  }


void LCodeGen::DoStringCharCodeAt(LStringCharCodeAt* instr) {  UNREACHABLE();  }


void LCodeGen::DoDeferredStringCharCodeAt(LStringCharCodeAt* instr) {  UNREACHABLE();  }


void LCodeGen::DoStringCharFromCode(LStringCharFromCode* instr) {  UNREACHABLE();  }


void LCodeGen::DoDeferredStringCharFromCode(LStringCharFromCode* instr) {  UNREACHABLE();  }


void LCodeGen::DoInteger32ToDouble(LInteger32ToDouble* instr) {  UNREACHABLE();  }


void LCodeGen::DoInteger32ToSmi(LInteger32ToSmi* instr) {
  LOperand* input = instr->value();
  LOperand* output = instr->result();
  Register scratch = scratch0();

  __ SmiTagCheckOverflow(ToRegister(output), ToRegister(input), scratch);
  if (!instr->hydrogen()->value()->HasRange() ||
      !instr->hydrogen()->value()->range()->IsInSmiRange()) {
    DeoptimizeIf(lt, instr->environment(), scratch, Operand(zero));
  }
}

void LCodeGen::DoUint32ToSmi(LUint32ToSmi* instr) {
  LOperand* input = instr->value();
  LOperand* output = instr->result();
  if (!instr->hydrogen()->value()->HasRange() ||
      !instr->hydrogen()->value()->range()->IsInSmiRange()) {
    Register scratch = scratch0();
    __ And(scratch, ToRegister(input), Operand(0xc0000000));
    DeoptimizeIf(ne, instr->environment(), scratch, Operand(zero));
  }
  __ SmiTag(ToRegister(output), ToRegister(input));
}

void LCodeGen::DoUint32ToDouble(LUint32ToDouble* instr) {
  LOperand* input = instr->value();
  LOperand* output = instr->result();

  FloatingPointHelper::ConvertUIntToDouble(masm(), ToRegister(input),
    FloatingPointHelper::kCoreRegisters, Register::from_code(ToDoubleRegister(output).code()), scratch0());
}

void LCodeGen::DoNumberTagI(LNumberTagI* instr) {
  Register src = ToRegister(instr->value());
  Register dst = ToRegister(instr->result());
  //Register overflow = scratch0();

  //DeferredNumberTagI* deferred = new(zone()) DeferredNumberTagI(this, instr);
  //__ SmiTagCheckOverflow(dst, src, overflow);
  //__ BranchOnOverflow(deferred->entry(), overflow);
  //__ bind(deferred->exit());
  __ SmiTag(dst, src);
}

void LCodeGen::DoNumberTagU(LNumberTagU* instr) {
  class DeferredNumberTagU V8_FINAL : public LDeferredCode {
   public:
    DeferredNumberTagU(LCodeGen* codegen, LNumberTagU* instr)
        : LDeferredCode(codegen), instr_(instr) { }
    virtual void Generate() V8_OVERRIDE {
      codegen()->DoDeferredNumberTagU(instr_, instr_->value());
    }
    virtual LInstruction* instr() V8_OVERRIDE { return instr_; }
   private:
    LNumberTagU* instr_;
  };

  LOperand* input = instr->value();
  ASSERT(input->IsRegister() && input->Equals(instr->result()));
  Register reg = ToRegister(input);

  DeferredNumberTagU* deferred = new(zone()) DeferredNumberTagU(this, instr);
  __ Branch(deferred->entry(), hi, reg, Operand(Smi::kMaxValue));
  __ SmiTag(reg, reg);
  __ bind(deferred->exit());
}

void LCodeGen::DoDeferredNumberTagU(LInstruction* instr,
                                    LOperand* value) {
  Label slow;
  Register src = ToRegister(value);
  Register dst = ToRegister(instr->result());
  Register scratch0_ = scratch0();
  Register scratch1_ = scratch1();

  // Preserve the value of all registers.
  PushSafepointRegistersScope scope(this, Safepoint::kWithRegisters);

  Label done;
  FloatingPointHelper::ConvertUIntToDouble(masm(), src,
					   FloatingPointHelper::kCoreRegisters, scratch0_, scratch1_);

  if (FLAG_inline_new) {
    __ LoadRoot(scratch1_, Heap::kHeapNumberMapRootIndex);
    __ AllocateHeapNumber(t1, a3, t0, scratch1_, &slow, DONT_TAG_RESULT);
    __ Move(dst, t1);
    __ Branch(&done);
  }

  // Slow case: Call the runtime system to do the number allocation.
  __ bind(&slow);

  // TODO(3095996): Put a valid pointer value in the stack slot where the result
  // register is stored, as this register is in the pointer map, but contains an
  // integer value.
  __ StoreToSafepointRegisterSlot(zero, dst);
  CallRuntimeFromDeferred(Runtime::kAllocateHeapNumber, 0, instr, NULL);
  __ Move(dst, v0);
  __ Subu(dst, dst, kHeapObjectTag);

  // Done. Put the value in dbl_scratch into the value of the allocated heap
  // number.
  __ bind(&done);
  __ st(scratch0_, MemOperand(dst, HeapNumber::kValueOffset));
  __ Addu(dst, dst, kHeapObjectTag);
  __ StoreToSafepointRegisterSlot(dst, dst);
}

void LCodeGen::DoNumberTagD(LNumberTagD* instr) {
  class DeferredNumberTagD: public LDeferredCode {
   public:
    DeferredNumberTagD(LCodeGen* codegen, LNumberTagD* instr)
        : LDeferredCode(codegen), instr_(instr) { }
    virtual void Generate() { codegen()->DoDeferredNumberTagD(instr_); }
    virtual LInstruction* instr() { return instr_; }
   private:
    LNumberTagD* instr_;
  };

  DoubleRegister input_reg = ToDoubleRegister(instr->value());
  Register scratch = scratch0();
  Register reg = ToRegister(instr->result());
  Register temp1 = ToRegister(instr->temp());
  Register temp2 = ToRegister(instr->temp2());

  bool convert_hole = false;
  HValue* change_input = instr->hydrogen()->value();
  if (change_input->IsLoadKeyed()) {
    HLoadKeyed* load = HLoadKeyed::cast(change_input);
    convert_hole = load->UsesMustHandleHole();
  }

  Label done;
#if 0 // FIXME, we will complete softfloat NaN check later, as it's rarely happend.
  Label no_special_nan_handling;
  if (convert_hole) {
    DoubleRegister input_reg = ToDoubleRegister(instr->value());
    __ BranchF(&no_special_nan_handling, NULL, eq, input_reg, input_reg);
    __ Move(reg, scratch0(), input_reg);
    Label canonicalize;
    __ Branch(&canonicalize, ne, scratch0(), Operand(kHoleNanUpper32));
    __ li(reg, factory()->the_hole_value());
    __ Branch(&done);
    __ bind(&canonicalize);
    __ Move(input_reg,
            FixedDoubleArray::canonical_not_the_hole_nan_as_double());
  }
  __ bind(&no_special_nan_handling);
#endif

  DeferredNumberTagD* deferred = new(zone()) DeferredNumberTagD(this, instr);
  if (FLAG_inline_new) {
    __ LoadRoot(scratch, Heap::kHeapNumberMapRootIndex);
    // We want the untagged address first for performance
    __ AllocateHeapNumber(reg, temp1, temp2, scratch, deferred->entry(),
                          DONT_TAG_RESULT);
  } else {
    __ Branch(deferred->entry());
  }
  __ bind(deferred->exit());
  __ st(input_reg, MemOperand(reg, HeapNumber::kValueOffset));
  // Now that we have finished with the object's real address tag it
  __ Addu(reg, reg, kHeapObjectTag);
  __ bind(&done);
}


void LCodeGen::DoDeferredNumberTagD(LNumberTagD* instr) {
  // TODO(3095996): Get rid of this. For now, we need to make the
  // result register contain a valid pointer because it is already
  // contained in the register pointer map.
  Register reg = ToRegister(instr->result());
  __ move(reg, zero);

  PushSafepointRegistersScope scope(this, Safepoint::kWithRegisters);
  // NumberTagI and NumberTagD use the context from the frame, rather than
  // the environment's HContext or HInlinedContext value.
  // They only call Runtime::kAllocateHeapNumber.
  // The corresponding HChange instructions are added in a phase that does
  // not have easy access to the local context.
  __ ld(cp, MemOperand(fp, StandardFrameConstants::kContextOffset));
  __ CallRuntimeSaveDoubles(Runtime::kAllocateHeapNumber);
  RecordSafepointWithRegisters(
      instr->pointer_map(), 0, Safepoint::kNoLazyDeopt);
  __ Subu(v0, v0, kHeapObjectTag);
  __ StoreToSafepointRegisterSlot(v0, reg);

}


void LCodeGen::DoSmiTag(LSmiTag* instr) {
  ASSERT(!instr->hydrogen_value()->CheckFlag(HValue::kCanOverflow));
  __ SmiTag(ToRegister(instr->result()), ToRegister(instr->value()));
}

void LCodeGen::DoSmiUntag(LSmiUntag* instr) {
  Register scratch = scratch0();
  Register input = ToRegister(instr->value());
  Register result = ToRegister(instr->result());
  if (instr->needs_check()) {
    STATIC_ASSERT(kHeapObjectTag == 1);
    // If the input is a HeapObject, value of scratch won't be zero.
    __ And(scratch, input, Operand(kHeapObjectTag));
    __ SmiUntag(result, input);
    DeoptimizeIf(ne, instr->environment(), scratch, Operand(zero));
  } else {
    __ SmiUntag(result, input);
  }
}

#if 1
void LCodeGen::EmitNumberUntagD(Register input_reg,
                                DoubleRegister result_reg,
                                bool can_convert_undefined_to_nan,
                                bool deoptimize_on_minus_zero,
                                LEnvironment* env,
                                NumberUntagDMode mode) {
  Register scratch = scratch0();
  Label convert, load_smi, done;
  if (mode == NUMBER_CANDIDATE_IS_ANY_TAGGED) {
    // Smi check.
    __ UntagAndJumpIfSmi(scratch, input_reg, &load_smi);
    // Heap number map check.
    __ ld(scratch, FieldMemOperand(input_reg, HeapObject::kMapOffset));
    __ LoadRoot(at, Heap::kHeapNumberMapRootIndex);
    if (can_convert_undefined_to_nan) {
      __ Branch(&convert, ne, scratch, Operand(at));
    } else {
      DeoptimizeIf(ne, env, scratch, Operand(at));
    }
    // Load heap number.
    __ ld(result_reg, FieldMemOperand(input_reg, HeapNumber::kValueOffset));
    if (deoptimize_on_minus_zero) {
      DeoptimizeIf(eq, env, Register::from_code(result_reg.code()), Operand(0x8000000000000000L));
    }
    __ Branch(&done);
    if (can_convert_undefined_to_nan) {
      __ bind(&convert);
      // Convert undefined (and hole) to NaN.
      __ LoadRoot(at, Heap::kUndefinedValueRootIndex);
      DeoptimizeIf(ne, env, input_reg, Operand(at));
      __ LoadRoot(scratch, Heap::kNanValueRootIndex);
      __ ld(result_reg, FieldMemOperand(scratch, HeapNumber::kValueOffset));
      __ Branch(&done);
    }
  } else {
    __ SmiUntag(scratch, input_reg);
    ASSERT(mode == NUMBER_CANDIDATE_IS_SMI);
  }
  // Smi to double register conversion
  __ bind(&load_smi);
  FloatingPointHelper::ConvertIntToDouble(masm(),
					  scratch, FloatingPointHelper::kCoreRegisters,
					  Register::from_code(result_reg.code()), at, scratch1());
  __ bind(&done);
}
#else

void LCodeGen::EmitNumberUntagD(Register input_reg,
                                DoubleRegister result_reg,
                                bool deoptimize_on_undefined,
                                bool deoptimize_on_minus_zero,
                                LEnvironment* env,
                                NumberUntagDMode mode) {
  Register scratch = scratch0();

  Label load_smi, heap_number, done;

  if (mode >= NUMBER_CANDIDATE_IS_ANY_TAGGED) {
    // Smi check.
    __ UntagAndJumpIfSmi(scratch, input_reg, &load_smi);

    // Heap number map check.
    __ ld(scratch, FieldMemOperand(input_reg, HeapObject::kMapOffset));
    __ LoadRoot(at, Heap::kHeapNumberMapRootIndex);
    if (deoptimize_on_undefined) {
      DeoptimizeIf(ne, env, scratch, Operand(at));
    } else {
      Label heap_number, convert;
      __ Branch(&heap_number, eq, scratch, Operand(at));

      // Convert undefined (and hole) to NaN.
      __ LoadRoot(at, Heap::kUndefinedValueRootIndex);
      if (mode == NUMBER_CANDIDATE_IS_ANY_TAGGED_CONVERT_HOLE) {
        __ Branch(&convert, eq, input_reg, Operand(at));
        __ LoadRoot(at, Heap::kTheHoleValueRootIndex);
      }
      DeoptimizeIf(ne, env, input_reg, Operand(at));

      __ bind(&convert);
      __ LoadRoot(at, Heap::kNanValueRootIndex);
      __ ld(Register::from_code(result_reg.code()), FieldMemOperand(at, HeapNumber::kValueOffset));
      __ Branch(&done);

      __ bind(&heap_number);
    }
    // Heap number to double register conversion.
    __ ld(Register::from_code(result_reg.code()), FieldMemOperand(input_reg, HeapNumber::kValueOffset));
    if (deoptimize_on_minus_zero) {
      DeoptimizeIf(eq, env, Register::from_code(result_reg.code()), Operand(0x8000000000000000L));
    }
    __ Branch(&done);
  } else {
    __ SmiUntag(scratch, input_reg);
    ASSERT(mode == NUMBER_CANDIDATE_IS_SMI);
  }

  // Smi to double register conversion
  __ bind(&load_smi);
  // scratch: untagged value of input_reg
  FloatingPointHelper::ConvertIntToDouble(masm(),
					  scratch, FloatingPointHelper::kCoreRegisters,
					  Register::from_code(result_reg.code()), at, scratch1());
  __ bind(&done);
}
#endif

void LCodeGen::DoDeferredTaggedToI(LTaggedToI* instr) {
  Register input_reg = ToRegister(instr->value());
  Register scratch1_ = scratch0();
  Register scratch2 = scratch1();
  Register scratch3 = ToRegister(instr->temp());
  Register scratch4 = ToRegister(instr->temp2());
  Register scratch5 = ToRegister(instr->temp3());

  ASSERT(!scratch1_.is(input_reg) && !scratch1_.is(scratch2));
  ASSERT(!scratch2.is(input_reg) && !scratch2.is(scratch1_));

  Label done;

  // The input is a tagged HeapObject.
  // Heap number map check.
  __ ld(scratch1_, FieldMemOperand(input_reg, HeapObject::kMapOffset));
  __ LoadRoot(at, Heap::kHeapNumberMapRootIndex);
  // This 'at' value and scratch1_ map value are used for tests in both clauses
  // of the if.

  if (instr->truncating()) {
    Register scratch3 = ToRegister(instr->temp2());
    ASSERT(!scratch3.is(input_reg) &&
           !scratch3.is(scratch1_) &&
           !scratch3.is(scratch2));
    // Performs a truncating conversion of a floating point number as used by
    // the JS bitwise operations.
    Label heap_number;
    Label not_in_int32_range;
    __ Branch(&heap_number, eq, scratch1_, Operand(at));  // HeapNumber map?
    // Check for undefined. Undefined is converted to zero for truncating
    // conversions.
    __ LoadRoot(at, Heap::kUndefinedValueRootIndex);
    DeoptimizeIf(ne, instr->environment(), input_reg, Operand(at));
    ASSERT(ToRegister(instr->result()).is(input_reg));
    __ move(input_reg, zero);
    __ Branch(&done);

    __ bind(&heap_number);
#if 0
    __ ld(double_scratch2,
          FieldMemOperand(input_reg, HeapNumber::kValueOffset));
    __ EmitECMATruncate(input_reg,
                        double_scratch2,
                        single_scratch,
                        scratch1_,
                        scratch2,
                        scratch3);
#else
  __ move(scratch5, input_reg);
  __ ConvertToInt32(input_reg,
                    input_reg,
                    scratch1_,
                    scratch2,
                    scratch3,
                    scratch4,
		    &not_in_int32_range);

  __ jmp(&done);

  __ bind(&not_in_int32_range);
  __ ld(scratch1_, FieldMemOperand(scratch5, HeapNumber::kValueOffset));

  __ EmitOutOfInt32RangeTruncate(input_reg,
                                 scratch1_,
                                 scratch2);
#endif
  } else {
    // Deoptimize if we don't have a heap number.
    DeoptimizeIf(ne, instr->environment(), scratch1_, Operand(at));

    // Load the double value.
    __ ld(at2,
          FieldMemOperand(input_reg, HeapNumber::kValueOffset));
#if 0
    Register except_flag = scratch2;
    __ EmitFPUTruncate(kRoundToZero,
                       input_reg,
                       double_scratch,
                       scratch1_,
                       double_scratch2,
                       except_flag,
                       kCheckForInexactConversion);

    // Deopt if the operation did not succeed.
    DeoptimizeIf(ne, instr->environment(), except_flag, Operand(zero));
#else
    __ ConvertToInt32(input_reg, input_reg, scratch1_, scratch2, scratch3, scratch4, NULL, true);
#endif

    if (instr->hydrogen()->CheckFlag(HValue::kBailoutOnMinusZero)) {
      __ Branch(&done, ne, input_reg, Operand(zero));

      __ And(at2, at2, Operand(0x8000000000000000L));
      DeoptimizeIf(ne, instr->environment(), at2, Operand(zero));
    }
  }
  __ bind(&done);
}

void LCodeGen::DoTaggedToI(LTaggedToI* instr) {
  class DeferredTaggedToI: public LDeferredCode {
   public:
    DeferredTaggedToI(LCodeGen* codegen, LTaggedToI* instr)
        : LDeferredCode(codegen), instr_(instr) { }
    virtual void Generate() { codegen()->DoDeferredTaggedToI(instr_); }
    virtual LInstruction* instr() { return instr_; }
   private:
    LTaggedToI* instr_;
  };

  LOperand* input = instr->value();
  ASSERT(input->IsRegister());
  ASSERT(input->Equals(instr->result()));

  Register input_reg = ToRegister(input);

  DeferredTaggedToI* deferred = new(zone()) DeferredTaggedToI(this, instr);

  // Let the deferred code handle the HeapObject case.
  __ JumpIfNotSmi(input_reg, deferred->entry());

  // Smi to int32 conversion.
  __ SmiUntag(input_reg);
  __ bind(deferred->exit());
}


void LCodeGen::DoNumberUntagD(LNumberUntagD* instr) {
  LOperand* input = instr->value();
  ASSERT(input->IsRegister());
  LOperand* result = instr->result();
  ASSERT(result->IsDoubleRegister());

  Register input_reg = ToRegister(input);
  DoubleRegister result_reg = ToDoubleRegister(result);

  HValue* value = instr->hydrogen()->value();
  NumberUntagDMode mode = value->representation().IsSmi()
      ? NUMBER_CANDIDATE_IS_SMI : NUMBER_CANDIDATE_IS_ANY_TAGGED;

  EmitNumberUntagD(input_reg, result_reg,
                   instr->hydrogen()->can_convert_undefined_to_nan(),
                   instr->hydrogen()->deoptimize_on_minus_zero(),
                   instr->environment(),
                   mode);
}

void LCodeGen::DoDoubleToI(LDoubleToI* instr) {  UNREACHABLE();  }


void LCodeGen::DoDoubleToSmi(LDoubleToSmi* instr) {  UNREACHABLE();  }


void LCodeGen::DoCheckSmi(LCheckSmi* instr) {
  LOperand* input = instr->value();
  __ And(at, ToRegister(input), Operand(kSmiTagMask));
  DeoptimizeIf(ne, instr->environment(), at, Operand(zero));
}


void LCodeGen::DoCheckNonSmi(LCheckNonSmi* instr) {
  LOperand* input = instr->value();
  __ And(at, ToRegister(input), Operand(kSmiTagMask));
  DeoptimizeIf(eq, instr->environment(), at, Operand(zero));
}


void LCodeGen::DoCheckInstanceType(LCheckInstanceType* instr) {
  Register input = ToRegister(instr->value());
  Register scratch = scratch0();

  __ GetObjectType(input, scratch, scratch);

  if (instr->hydrogen()->is_interval_check()) {
    InstanceType first;
    InstanceType last;
    instr->hydrogen()->GetCheckInterval(&first, &last);

    // If there is only one type in the interval check for equality.
    if (first == last) {
      DeoptimizeIf(ne, instr->environment(), scratch, Operand(first));
    } else {
      DeoptimizeIf(lo, instr->environment(), scratch, Operand(first));
      // Omit check for the last type.
      if (last != LAST_TYPE) {
        DeoptimizeIf(hi, instr->environment(), scratch, Operand(last));
      }
    }
  } else {
    uint8_t mask;
    uint8_t tag;
    instr->hydrogen()->GetCheckMaskAndTag(&mask, &tag);

    if (IsPowerOf2(mask)) {
      ASSERT(tag == 0 || IsPowerOf2(tag));
      __ And(at, scratch, mask);
      DeoptimizeIf(tag == 0 ? ne : eq, instr->environment(),
          at, Operand(zero));
    } else {
      __ And(scratch, scratch, Operand(mask));
      DeoptimizeIf(ne, instr->environment(), scratch, Operand(tag));
    }
  }
}

void LCodeGen::DoDeferredInstanceMigration(LCheckMaps* instr, Register object) {
  {
    PushSafepointRegistersScope scope(this, Safepoint::kWithRegisters);
    __ push(object);
    __ move(cp, zero);
    __ CallRuntimeSaveDoubles(Runtime::kMigrateInstance);
    RecordSafepointWithRegisters(
        instr->pointer_map(), 1, Safepoint::kNoLazyDeopt);
    __ StoreToSafepointRegisterSlot(v0, scratch0());
  }
  __ And(at, scratch0(), Operand(kSmiTagMask));
  DeoptimizeIf(eq, instr->environment(), at, Operand(zero));
}

void LCodeGen::DoCheckMaps(LCheckMaps* instr) {
  class DeferredCheckMaps V8_FINAL : public LDeferredCode {
   public:
    DeferredCheckMaps(LCodeGen* codegen, LCheckMaps* instr, Register object)
        : LDeferredCode(codegen), instr_(instr), object_(object) {
      SetExit(check_maps());
    }
    virtual void Generate() V8_OVERRIDE {
      codegen()->DoDeferredInstanceMigration(instr_, object_);
    }
    Label* check_maps() { return &check_maps_; }
    virtual LInstruction* instr() V8_OVERRIDE { return instr_; }
   private:
    LCheckMaps* instr_;
    Label check_maps_;
    Register object_;
  };

  if (instr->hydrogen()->CanOmitMapChecks()) return;
  Register map_reg = scratch0();
  LOperand* input = instr->value();
  ASSERT(input->IsRegister());
  Register reg = ToRegister(input);
  __ ld(map_reg, FieldMemOperand(reg, HeapObject::kMapOffset));

  DeferredCheckMaps* deferred = NULL;
  if (instr->hydrogen()->has_migration_target()) {
    deferred = new(zone()) DeferredCheckMaps(this, instr, reg);
    __ bind(deferred->check_maps());
  }

  UniqueSet<Map> map_set = instr->hydrogen()->map_set();
  Label success;
  for (int i = 0; i < map_set.size() - 1; i++) {
    Handle<Map> map = map_set.at(i).handle();
    __ CompareMapAndBranch(map_reg, map, &success, eq, &success);
  }
  Handle<Map> map = map_set.at(map_set.size() - 1).handle();
  // Do the CompareMap() directly within the Branch() and DeoptimizeIf().
  if (instr->hydrogen()->has_migration_target()) {
    __ Branch(deferred->entry(), ne, map_reg, Operand(map));
  } else {
    DeoptimizeIf(ne, instr->environment(), map_reg, Operand(map));
  }

  __ bind(&success);
}

void LCodeGen::DoClampDToUint8(LClampDToUint8* instr) {
  DoubleRegister value_reg = ToDoubleRegister(instr->unclamped());
  Register result_reg = ToRegister(instr->result());
  Register temp_reg = ToRegister(instr->temp());
  Register temp_reg1 = ToRegister(instr->temp1());
  Register temp_reg2 = ToRegister(instr->temp2());
  __ ClampDoubleToUint8(result_reg, Register::from_code(value_reg.code()), temp_reg, temp_reg1 ,temp_reg2);
}



void LCodeGen::DoClampIToUint8(LClampIToUint8* instr) {
  Register unclamped_reg = ToRegister(instr->unclamped());
  Register result_reg = ToRegister(instr->result());
  __ ClampUint8(result_reg, unclamped_reg);
}


void LCodeGen::DoClampTToUint8(LClampTToUint8* instr) {
  Register scratch = scratch0();
  Register input_reg = ToRegister(instr->unclamped());
  Register result_reg = ToRegister(instr->result());
  Register temp_reg = ToRegister(instr->temp());
  Register temp_reg1 = ToRegister(instr->temp1());
  Register temp_reg2 = ToRegister(instr->temp2());
  Label is_smi, done, heap_number;

  // Both smi and heap number cases are handled.
  __ UntagAndJumpIfSmi(scratch, input_reg, &is_smi);

  // Check for heap number
  __ ld(scratch, FieldMemOperand(input_reg, HeapObject::kMapOffset));
  __ Branch(&heap_number, eq, scratch, Operand(factory()->heap_number_map()));

  // Check for undefined. Undefined is converted to zero for clamping
  // conversions.
  DeoptimizeIf(ne, instr->environment(), input_reg,
               Operand(factory()->undefined_value()));
  __ move(result_reg, zero);
  __ jmp(&done);

  // Heap number
  __ bind(&heap_number);
  __ ld(scratch1(), FieldMemOperand(input_reg,
                                             HeapNumber::kValueOffset));
  __ ClampDoubleToUint8(result_reg, scratch1(), temp_reg, temp_reg1, temp_reg2);
  __ jmp(&done);

  __ bind(&is_smi);
  __ ClampUint8(result_reg, scratch);

  __ bind(&done);
}

void LCodeGen::DoAllocate(LAllocate* instr) {
  class DeferredAllocate V8_FINAL : public LDeferredCode {
   public:
    DeferredAllocate(LCodeGen* codegen, LAllocate* instr)
        : LDeferredCode(codegen), instr_(instr) { }
    virtual void Generate() V8_OVERRIDE {
      codegen()->DoDeferredAllocate(instr_);
    }
    virtual LInstruction* instr() V8_OVERRIDE { return instr_; }
   private:
    LAllocate* instr_;
  };

  DeferredAllocate* deferred =
      new(zone()) DeferredAllocate(this, instr);

  Register result = ToRegister(instr->result());
  Register scratch = ToRegister(instr->temp1());
  Register scratch2 = ToRegister(instr->temp2());

  // Allocate memory for the object.
  AllocationFlags flags = TAG_OBJECT;
  if (instr->hydrogen()->MustAllocateDoubleAligned()) {
    flags = static_cast<AllocationFlags>(flags | DOUBLE_ALIGNMENT);
  }
  if (instr->hydrogen()->IsOldPointerSpaceAllocation()) {
    ASSERT(!instr->hydrogen()->IsOldDataSpaceAllocation());
    ASSERT(!instr->hydrogen()->IsNewSpaceAllocation());
    flags = static_cast<AllocationFlags>(flags | PRETENURE_OLD_POINTER_SPACE);
  } else if (instr->hydrogen()->IsOldDataSpaceAllocation()) {
    ASSERT(!instr->hydrogen()->IsNewSpaceAllocation());
    flags = static_cast<AllocationFlags>(flags | PRETENURE_OLD_DATA_SPACE);
  }
  if (instr->size()->IsConstantOperand()) {
    int32_t size = ToInteger32(LConstantOperand::cast(instr->size()));
    __ Allocate(size, result, scratch, scratch2, deferred->entry(), flags);
  } else {
    Register size = ToRegister(instr->size());
    __ Allocate(size,
                result,
                scratch,
                scratch2,
                deferred->entry(),
                flags);
  }

  __ bind(deferred->exit());

  if (instr->hydrogen()->MustPrefillWithFiller()) {
    if (instr->size()->IsConstantOperand()) {
      int32_t size = ToInteger32(LConstantOperand::cast(instr->size()));
      __ li(scratch, Operand(size));
    } else {
      scratch = ToRegister(instr->size());
    }
    __ Subu(scratch, scratch, Operand(kPointerSize));
    __ Subu(result, result, Operand(kHeapObjectTag));
    Label loop;
    __ bind(&loop);
    __ li(scratch2, Operand(isolate()->factory()->one_pointer_filler_map()));
    __ Addu(at, result, Operand(scratch));
    __ st(scratch2, MemOperand(at));
    __ Subu(scratch, scratch, Operand(kPointerSize));
    __ Branch(&loop, ge, scratch, Operand(zero));
    __ Addu(result, result, Operand(kHeapObjectTag));
  }
}

void LCodeGen::DoDeferredAllocate(LAllocate* instr) {
  Register result = ToRegister(instr->result());

  // TODO(3095996): Get rid of this. For now, we need to make the
  // result register contain a valid pointer because it is already
  // contained in the register pointer map.
  __ move(result, zero);

  PushSafepointRegistersScope scope(this, Safepoint::kWithRegisters);
  if (instr->size()->IsRegister()) {
    Register size = ToRegister(instr->size());
    ASSERT(!size.is(result));
    __ SmiTag(size);
    __ push(size);
  } else {
    int32_t size = ToInteger32(LConstantOperand::cast(instr->size()));
    __ Push(Smi::FromInt(size));
  }

  if (instr->hydrogen()->IsOldPointerSpaceAllocation()) {
    ASSERT(!instr->hydrogen()->IsOldDataSpaceAllocation());
    ASSERT(!instr->hydrogen()->IsNewSpaceAllocation());
    CallRuntimeFromDeferred(Runtime::kAllocateInOldPointerSpace, 1, instr,
                            instr->context());
  } else if (instr->hydrogen()->IsOldDataSpaceAllocation()) {
    ASSERT(!instr->hydrogen()->IsNewSpaceAllocation());
    CallRuntimeFromDeferred(Runtime::kAllocateInOldDataSpace, 1, instr,
                            instr->context());
  } else {
    CallRuntimeFromDeferred(Runtime::kAllocateInNewSpace, 1, instr,
                            instr->context());
  }
  __ StoreToSafepointRegisterSlot(v0, result);
}

void LCodeGen::DoToFastProperties(LToFastProperties* instr) {
  ASSERT(ToRegister(instr->value()).is(a0));
  ASSERT(ToRegister(instr->result()).is(v0));
  __ push(a0);
  CallRuntime(Runtime::kToFastProperties, 1, instr);
}

void LCodeGen::DoRegExpLiteral(LRegExpLiteral* instr) {
  Label materialized;
  // Registers will be used as follows:
  // t3 = literals array.
  // a1 = regexp literal.
  // a0 = regexp literal clone.
  // a2 and t0-t2 are used as temporaries.
  int literal_offset =
      FixedArray::OffsetOfElementAt(instr->hydrogen()->literal_index());
  __ LoadHeapObject(t3, instr->hydrogen()->literals());
  __ ld(a1, FieldMemOperand(t3, literal_offset));
  __ LoadRoot(at, Heap::kUndefinedValueRootIndex);
  __ Branch(&materialized, ne, a1, Operand(at));

  // Create regexp literal using runtime function
  // Result will be in v0.
  __ li(t2, Operand(Smi::FromInt(instr->hydrogen()->literal_index())));
  __ li(t1, Operand(instr->hydrogen()->pattern()));
  __ li(t0, Operand(instr->hydrogen()->flags()));
  __ Push(t3, t2, t1, t0);
  CallRuntime(Runtime::kMaterializeRegExpLiteral, 4, instr);
  __ move(a1, v0);

  __ bind(&materialized);
  int size = JSRegExp::kSize + JSRegExp::kInObjectFieldCount * kPointerSize;
  Label allocated, runtime_allocate;

  __ Allocate(size, v0, a2, a3, &runtime_allocate, TAG_OBJECT);
  __ jmp(&allocated);

  __ bind(&runtime_allocate);
  __ li(a0, Operand(Smi::FromInt(size)));
  __ Push(a1, a0);
  CallRuntime(Runtime::kAllocateInNewSpace, 1, instr);
  __ pop(a1);

  __ bind(&allocated);
  // Copy the content into the newly allocated memory.
  // (Unroll copy loop once for better throughput).
  for (int i = 0; i < size - kPointerSize; i += 2 * kPointerSize) {
    __ ld(a3, FieldMemOperand(a1, i));
    __ ld(a2, FieldMemOperand(a1, i + kPointerSize));
    __ st(a3, FieldMemOperand(v0, i));
    __ st(a2, FieldMemOperand(v0, i + kPointerSize));
  }
  if ((size % (2 * kPointerSize)) != 0) {
    __ ld(a3, FieldMemOperand(a1, size - kPointerSize));
    __ st(a3, FieldMemOperand(v0, size - kPointerSize));
  }
}

void LCodeGen::DoFunctionLiteral(LFunctionLiteral* instr) {
  // Use the fast case closure allocation code that allocates in new
  // space for nested functions that don't need literals cloning.
  bool pretenure = instr->hydrogen()->pretenure();
  if (!pretenure && instr->hydrogen()->has_no_literals()) {
    FastNewClosureStub stub(instr->hydrogen()->language_mode(),
                            instr->hydrogen()->is_generator());
    __ li(a1, Operand(instr->hydrogen()->shared_info()));
    __ push(a1);
    CallCode(stub.GetCode(isolate()), RelocInfo::CODE_TARGET, instr);
  } else {
    __ li(a2, Operand(instr->hydrogen()->shared_info()));
    __ li(a1, Operand(pretenure ? factory()->true_value()
                                : factory()->false_value()));
    __ Push(cp, a2, a1);
    CallRuntime(Runtime::kNewClosure, 3, instr);
  }
}


void LCodeGen::DoTypeof(LTypeof* instr) {
  ASSERT(ToRegister(instr->result()).is(v0));
  Register input = ToRegister(instr->value());
  __ push(input);
  CallRuntime(Runtime::kTypeof, 1, instr);
}

void LCodeGen::DoTypeofIsAndBranch(LTypeofIsAndBranch* instr) {
  Register input = ToRegister(instr->value());

  Register cmp1 = no_reg;
  Operand cmp2 = Operand(no_reg);

  Condition final_branch_condition = EmitTypeofIs(instr->TrueLabel(chunk_),
                                                  instr->FalseLabel(chunk_),
                                                  input,
                                                  instr->type_literal(),
                                                  cmp1,
                                                  cmp2);

  ASSERT(cmp1.is_valid());
  ASSERT(!cmp2.is_reg() || cmp2.rm().is_valid());

  if (final_branch_condition != kNoCondition) {
    EmitBranch(instr, final_branch_condition, cmp1, cmp2);
  }
}

Condition LCodeGen::EmitTypeofIs(Label* true_label,
                                 Label* false_label,
                                 Register input,
                                 Handle<String> type_name,
                                 Register& cmp1,
                                 Operand& cmp2) {
  // This function utilizes the delay slot heavily. This is used to load
  // values that are always usable without depending on the type of the input
  // register.
  Condition final_branch_condition = kNoCondition;
  Register scratch = scratch0();
  if (type_name->Equals(heap()->number_string())) {
    __ JumpIfSmi(input, true_label);
    __ ld(input, FieldMemOperand(input, HeapObject::kMapOffset));
    __ LoadRoot(at, Heap::kHeapNumberMapRootIndex);
    cmp1 = input;
    cmp2 = Operand(at);
    final_branch_condition = eq;

  } else if (type_name->Equals(heap()->string_string())) {
    __ JumpIfSmi(input, false_label);
    __ GetObjectType(input, input, scratch);
    // input is an object so we can load the BitFieldOffset even if we take the
    // other branch.
    __ Branch(false_label, ge, scratch, Operand(FIRST_NONSTRING_TYPE));
    __ ld1u(at2, FieldMemOperand(input, Map::kBitFieldOffset));
    __ And(at, at2, 1 << Map::kIsUndetectable);
    cmp1 = at;
    cmp2 = Operand(zero);
    final_branch_condition = eq;

  } else if (type_name->Equals(heap()->symbol_string())) {
    __ JumpIfSmi(input, false_label);
    __ GetObjectType(input, input, scratch);
    cmp1 = scratch;
    cmp2 = Operand(SYMBOL_TYPE);
    final_branch_condition = eq;

  } else if (type_name->Equals(heap()->boolean_string())) {
    __ LoadRoot(at2, Heap::kTrueValueRootIndex);
    __ LoadRoot(at, Heap::kFalseValueRootIndex);
    __ Branch(true_label, eq, at2, Operand(input));
    cmp1 = at;
    cmp2 = Operand(input);
    final_branch_condition = eq;

  } else if (FLAG_harmony_typeof && type_name->Equals(heap()->null_string())) {
    __ LoadRoot(at, Heap::kNullValueRootIndex);
    cmp1 = at;
    cmp2 = Operand(input);
    final_branch_condition = eq;

  } else if (type_name->Equals(heap()->undefined_string())) {
    __ LoadRoot(at, Heap::kUndefinedValueRootIndex);
    __ Branch(true_label, eq, at, Operand(input));
    // The first instruction of JumpIfSmi is an And - it is safe in the delay
    // slot.
    __ JumpIfSmi(input, false_label);
    // Check for undetectable objects => true.
    __ ld(input, FieldMemOperand(input, HeapObject::kMapOffset));
    __ ld1u(at2, FieldMemOperand(input, Map::kBitFieldOffset));
    __ And(at, at2, 1 << Map::kIsUndetectable);
    cmp1 = at;
    cmp2 = Operand(zero);
    final_branch_condition = ne;

  } else if (type_name->Equals(heap()->function_string())) {
    STATIC_ASSERT(NUM_OF_CALLABLE_SPEC_OBJECT_TYPES == 2);
    __ JumpIfSmi(input, false_label);
    __ GetObjectType(input, scratch, input);
    __ Branch(true_label, eq, input, Operand(JS_FUNCTION_TYPE));
    cmp1 = input;
    cmp2 = Operand(JS_FUNCTION_PROXY_TYPE);
    final_branch_condition = eq;

  } else if (type_name->Equals(heap()->object_string())) {
    __ JumpIfSmi(input, false_label);
    if (!FLAG_harmony_typeof) {
      __ LoadRoot(at, Heap::kNullValueRootIndex);
      __ Branch(true_label, eq, at, Operand(input));
    }
    Register map = input;
    __ GetObjectType(input, map, scratch);
    __ Branch(false_label,
              lt, scratch, Operand(FIRST_NONCALLABLE_SPEC_OBJECT_TYPE));
    // map is still valid, so the BitField can be loaded in delay slot.
    // Check for undetectable objects => false.

    __ Branch(false_label,
              gt, scratch, Operand(LAST_NONCALLABLE_SPEC_OBJECT_TYPE));
    __ ld1u(at2, FieldMemOperand(map, Map::kBitFieldOffset));
    __ And(at, at2, 1 << Map::kIsUndetectable);
    cmp1 = at;
    cmp2 = Operand(zero);
    final_branch_condition = eq;

  } else {
    cmp1 = at;
    cmp2 = Operand(zero);  // Set to valid regs, to avoid caller assertion.
    __ Branch(false_label);
  }

  return final_branch_condition;
}

void LCodeGen::DoIsConstructCallAndBranch(LIsConstructCallAndBranch* instr) {
  Register temp1 = ToRegister(instr->temp());

  EmitIsConstructCall(temp1, scratch0());

  EmitBranch(instr, eq, temp1,
             Operand(Smi::FromInt(StackFrame::CONSTRUCT)));
}

void LCodeGen::EmitIsConstructCall(Register temp1, Register temp2) {
  ASSERT(!temp1.is(temp2));
  // Get the frame pointer for the calling frame.
  __ ld(temp1, MemOperand(fp, StandardFrameConstants::kCallerFPOffset));

  // Skip the arguments adaptor frame if it exists.
  Label check_frame_marker;
  __ ld(temp2, MemOperand(temp1, StandardFrameConstants::kContextOffset));
  __ Branch(&check_frame_marker, ne, temp2,
            Operand(Smi::FromInt(StackFrame::ARGUMENTS_ADAPTOR)));
  __ ld(temp1, MemOperand(temp1, StandardFrameConstants::kCallerFPOffset));

  // Check the marker in the calling frame.
  __ bind(&check_frame_marker);
  __ ld(temp1, MemOperand(temp1, StandardFrameConstants::kMarkerOffset));
}


void LCodeGen::EnsureSpaceForLazyDeopt(int space_needed) {
  if (info()->IsStub()) return;
  // Ensure that we have enough space after the previous lazy-bailout
  // instruction for patching the code here.
  int current_pc = masm()->pc_offset();
  if (current_pc < last_lazy_deopt_pc_ + space_needed) {
    int padding_size = last_lazy_deopt_pc_ + space_needed - current_pc;
    ASSERT_EQ(0, padding_size % Assembler::kInstrSize);
    while (padding_size > 0) {
      __ nop();
      padding_size -= Assembler::kInstrSize;
    }
  }
}

void LCodeGen::DoLazyBailout(LLazyBailout* instr) {
  EnsureSpaceForLazyDeopt(Deoptimizer::patch_size());
  ASSERT(instr->HasEnvironment());
  LEnvironment* env = instr->environment();
  RegisterEnvironmentForDeoptimization(env, Safepoint::kLazyDeopt);
  safepoints_.RecordLazyDeoptimizationIndex(env->deoptimization_index());
}

void LCodeGen::DoDeoptimize(LDeoptimize* instr) {
  Deoptimizer::BailoutType type = instr->hydrogen()->type();
  // TODO(danno): Stubs expect all deopts to be lazy for historical reasons (the
  // needed return address), even though the implementation of LAZY and EAGER is
  // now identical. When LAZY is eventually completely folded into EAGER, remove
  // the special case below.
  if (info()->IsStub() && type == Deoptimizer::EAGER) {
    type = Deoptimizer::LAZY;
  }

  Comment(";;; deoptimize: %s", instr->hydrogen()->reason());
  DeoptimizeIf(al, instr->environment(), type, zero, Operand(zero));
}

void LCodeGen::DoDummyUse(LDummyUse* instr) {
  // Nothing to see here, move on!
}

void LCodeGen::DoCheckValue(LCheckValue* instr) {
  Register reg = ToRegister(instr->value());
  Handle<HeapObject> object = instr->hydrogen()->object().handle();
  AllowDeferredHandleDereference smi_check;
  if (isolate()->heap()->InNewSpace(*object)) {
    Register reg = ToRegister(instr->value());
    Handle<Cell> cell = isolate()->factory()->NewCell(object);
    __ li(at, Operand(Handle<Object>(cell)));
    __ ld(at, FieldMemOperand(at, Cell::kValueOffset));
    DeoptimizeIf(ne, instr->environment(), reg,
                 Operand(at));
  } else {
    DeoptimizeIf(ne, instr->environment(), reg,
                 Operand(object));
  }
}

void LCodeGen::DoDummy(LDummy* instr) {}

void LCodeGen::DoMathFloorOfDiv(LMathFloorOfDiv* instr) { UNREACHABLE(); }

void LCodeGen::DoDeferredStackCheck(LStackCheck* instr) {  UNREACHABLE();  }


void LCodeGen::DoStackCheck(LStackCheck* instr) {  UNREACHABLE();  }


void LCodeGen::DoOsrEntry(LOsrEntry* instr) {  UNREACHABLE();  }


void LCodeGen::DoForInPrepareMap(LForInPrepareMap* instr) {  UNREACHABLE();  }


void LCodeGen::DoForInCacheArray(LForInCacheArray* instr) {  UNREACHABLE();  }


void LCodeGen::DoCheckMapValue(LCheckMapValue* instr) {  UNREACHABLE();  }


void LCodeGen::DoLoadFieldByIndex(LLoadFieldByIndex* instr) {
  Register object = ToRegister(instr->object());
  Register index = ToRegister(instr->index());
  Register result = ToRegister(instr->result());
  Register scratch = scratch0();

  Label out_of_object, done;
  __ sra(scratch, index, kSmiTagSize + kSmiShiftSize);  // In delay slot.
  __ sll(scratch, scratch, kPointerSizeLog2);  // In delay slot.
  __ Branch(&out_of_object, lt, index, Operand(zero));

  STATIC_ASSERT(kPointerSizeLog2 > kSmiTagSize);
  __ Addu(scratch, object, scratch);
  __ ld(result, FieldMemOperand(scratch, JSObject::kHeaderSize));

  __ Branch(&done);

  __ bind(&out_of_object);
  __ ld(result, FieldMemOperand(object, JSObject::kPropertiesOffset));
  // Index is equal to negated out of object property index plus 1.
  __ Subu(scratch, result, scratch);
  __ ld(result, FieldMemOperand(scratch,
                                FixedArray::kHeaderSize - kPointerSize));
  __ bind(&done);
}


#undef __

} }  // namespace v8::internal
