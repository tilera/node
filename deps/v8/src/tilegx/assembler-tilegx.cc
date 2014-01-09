// Copyright (c) 1994-2006 Sun Microsystems Inc.
// All Rights Reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// - Redistributions of source code must retain the above copyright notice,
// this list of conditions and the following disclaimer.
//
// - Redistribution in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// - Neither the name of Sun Microsystems or the names of contributors may
// be used to endorse or promote products derived from this software without
// specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
// IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
// THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
// PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
// CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
// EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
// PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
// LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
// NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

// The original source code covered by the above license above has been
// modified significantly by Google Inc.
// Copyright 2012 the V8 project authors. All rights reserved.


#include "v8.h"

#if V8_TARGET_ARCH_TILEGX

#include "tilegx/assembler-tilegx-inl.h"
#include "serialize.h"

namespace v8 {
namespace internal {

#ifdef DEBUG
bool CpuFeatures::initialized_ = false;
#endif
unsigned CpuFeatures::supported_ = 0;
unsigned CpuFeatures::found_by_runtime_probing_only_ = 0;
unsigned CpuFeatures::cross_compile_ = 0;


ExternalReference ExternalReference::cpu_features() {
  ASSERT(CpuFeatures::initialized_);
  return ExternalReference(&CpuFeatures::supported_);
}

void CpuFeatures::Probe() {
  uint64_t standard_features = OS::CpuFeaturesImpliedByPlatform();

  ASSERT(supported_ == 0 || supported_ == standard_features);

#ifdef DEBUG
  initialized_ = true;
#endif

  supported_ |= standard_features;

  if (Serializer::enabled()) {
    // No probing for features if we might serialize (generate snapshot).
    return;
  }

  // No further probing currently, may be extended in future.
}

// Determines the end of the Jump chain (a subset of the label link chain).
const int kEndOfJumpChain = 0;

bool Assembler::IsBranch(Instr instr) {
  uint32_t mode   = get_Mode(instr);
  int32_t X1_OPC = -1;

  if (mode != 0)
    return false;

  X1_OPC = get_Opcode_X1(instr);

  // Checks if the instruction is a branch.
  return X1_OPC == BRANCH_OPCODE_X1;
}

bool Assembler::IsJ(Instr instr) {
  uint32_t mode   = get_Mode(instr);
  int32_t X1_OPC = -1, X1_SUB_OPC = -1;

  if (mode != 0)
    return false;

  X1_OPC = get_Opcode_X1(instr);
  X1_SUB_OPC = get_JumpOpcodeExtension_X1(instr);

  // Checks if the instruction is a jump.
  return X1_OPC == JUMP_OPCODE_X1 && X1_SUB_OPC == J_JUMP_OPCODE_X1;
}

bool Assembler::IsJAL(Instr instr) {
  uint32_t mode   = get_Mode(instr);
  int32_t X1_OPC = -1, X1_SUB_OPC = -1;

  if (mode != 0)
    return false;

  X1_OPC = get_Opcode_X1(instr);
  X1_SUB_OPC = get_JumpOpcodeExtension_X1(instr);

  // Checks if the instruction is a jal.
  return X1_OPC == JUMP_OPCODE_X1 && X1_SUB_OPC == JAL_JUMP_OPCODE_X1;
}

bool Assembler::IsJALR(Instr instr) {
  uint32_t mode   = get_Mode(instr);
  int32_t X1_OPC = -1, X1_SUB_OPC = -1, X1_SSUB_OPC = -1;

  if (mode != 0)
    return false;

  X1_OPC = get_Opcode_X1(instr);
  X1_SUB_OPC = get_RRROpcodeExtension_X1(instr);
  X1_SSUB_OPC = get_UnaryOpcodeExtension_X1(instr);

  // Checks if the instruction is a jal.
  return X1_OPC == RRR_0_OPCODE_X1
    && X1_SUB_OPC == UNARY_RRR_0_OPCODE_X1 && X1_SSUB_OPC == JALR_UNARY_OPCODE_X1;
}

bool Assembler::IsJR(Instr instr) {
  uint32_t mode   = get_Mode(instr);
  int32_t X1_OPC = -1, X1_SUB1_OPC = -1, X1_SUB2_OPC = -1;
  int32_t Y1_OPC = -1, Y1_SUB1_OPC = -1, Y1_SUB2_OPC = -1;

  if (mode != 0) {
    Y1_OPC = get_Opcode_Y1(instr);
    Y1_SUB1_OPC = get_RRROpcodeExtension_Y1(instr);
    Y1_SUB2_OPC = get_UnaryOpcodeExtension_Y1(instr);
  } else {
    X1_OPC = get_Opcode_X1(instr);
    X1_SUB1_OPC = get_RRROpcodeExtension_X1(instr);
    X1_SUB2_OPC = get_UnaryOpcodeExtension_X1(instr);
  }

  // Checks if the instruction is a jr.
  return (X1_OPC == RRR_0_OPCODE_X1 && X1_SUB1_OPC == UNARY_RRR_0_OPCODE_X1
          && X1_SUB2_OPC == JR_UNARY_OPCODE_X1)
         || (Y1_OPC == RRR_1_OPCODE_Y1 && Y1_SUB1_OPC == UNARY_RRR_1_OPCODE_Y1
             && Y1_SUB2_OPC == JR_UNARY_OPCODE_Y1);
}

bool Assembler::IsSHL16INSLI(Instr instr) {
  uint32_t mode   = get_Mode(instr);
  int32_t X0_OPC = -1, X1_OPC = -1;

  if (mode != 0)
    return false;

  X0_OPC = get_Opcode_X0(instr);
  X1_OPC = get_Opcode_X1(instr);

  // Checks if the instruction is a shl16insli which
  // is used for constant loading.
  return X0_OPC == SHL16INSLI_OPCODE_X0 || X1_OPC == SHL16INSLI_OPCODE_X1;
}

bool Assembler::IsMOVELI(Instr instr) {
  uint32_t mode   = get_Mode(instr);
  int32_t X0_OPC = -1, X1_OPC = -1;

  if (mode != 0)
    return false;

  X0_OPC = get_Opcode_X0(instr);
  X1_OPC = get_Opcode_X1(instr);

  // Checks if the instruction is a moveli which is
  // used for constant loading and is actually alias
  // of addli.
  return X0_OPC == ADDLI_OPCODE_X0 || X1_OPC == ADDLI_OPCODE_X1;
}

bool Assembler::IsSHL(Instr instr) {
  uint32_t mode   = get_Mode(instr);
  int32_t X0_OPC = -1, X1_OPC = -1;
  int32_t X0_SUB_OPC = -1, X1_SUB_OPC = -1;

  if (mode != 0)
    return false;

  X0_OPC = get_Opcode_X0(instr);
  X1_OPC = get_Opcode_X1(instr);
  X0_SUB_OPC = get_RRROpcodeExtension_X0(instr);
  X1_SUB_OPC = get_RRROpcodeExtension_X1(instr);

  return (X0_OPC == RRR_0_OPCODE_X0
          && X0_SUB_OPC == SHL_RRR_0_OPCODE_X0)
         || (X1_OPC == RRR_0_OPCODE_X1
             && X1_SUB_OPC == SHL_RRR_0_OPCODE_X1);
}

bool Assembler::IsANDI(Instr instr) {
  uint32_t mode   = get_Mode(instr);
  int32_t X0_OPC = -1, X1_OPC = -1;
  int32_t X0_SUB_OPC = -1, X1_SUB_OPC = -1;

  if (mode != 0)
    return false;

  X0_OPC = get_Opcode_X0(instr);
  X1_OPC = get_Opcode_X1(instr);
  X0_SUB_OPC = get_Imm8OpcodeExtension_X0(instr);
  X1_SUB_OPC = get_Imm8OpcodeExtension_X1(instr);

  // Checks if the instruction is a moveli which is
  // used for constant loading and is actually alias
  // of addli.
  return (X0_OPC == IMM8_OPCODE_X0 && X0_SUB_OPC == ANDI_IMM8_OPCODE_X0)
          || (X1_OPC == IMM8_OPCODE_X1 && X1_SUB_OPC == ANDI_IMM8_OPCODE_X1);
}

bool Assembler::IsBeqz(Instr instr) {
  uint32_t mode   = get_Mode(instr);
  int32_t X1_OPC = -1, BrType = -1;

  if (mode != 0)
    return false;

  X1_OPC = get_Opcode_X1(instr);
  BrType = get_BrType_X1(instr);

  // Checks if the instruction is a moveli which is
  // used for constant loading and is actually alias
  // of addli.
  return X1_OPC == BRANCH_OPCODE_X1 && BrType == BEQZ_BRANCH_OPCODE_X1;
}

bool Assembler::IsBnez(Instr instr) {
  uint32_t mode   = get_Mode(instr);
  int32_t X1_OPC = -1, BrType = -1;

  if (mode != 0)
    return false;

  X1_OPC = get_Opcode_X1(instr);
  BrType = get_BrType_X1(instr);

  // Checks if the instruction is a moveli which is
  // used for constant loading and is actually alias
  // of addli.
  return X1_OPC == BRANCH_OPCODE_X1 && BrType == BNEZ_BRANCH_OPCODE_X1;
}

Assembler::Assembler(Isolate* isolate, void* buffer, int buffer_size)
    : AssemblerBase(isolate, buffer, buffer_size),
      recorded_ast_id_(TypeFeedbackId::None()),
      positions_recorder_(this) {
  reloc_info_writer.Reposition(buffer_ + buffer_size_, pc_);

  last_trampoline_pool_end_ = 0;
  no_trampoline_pool_before_ = 0;
  trampoline_pool_blocked_nesting_ = 0;
  // We leave space (16 * kTrampolineSlotsSize)
  // for BlockTrampolinePoolScope buffer.
  next_buffer_check_ = kMaxBranchOffset - kTrampolineSlotsSize * 16;
  internal_trampoline_exception_ = false;
  last_bound_pos_ = 0;

  trampoline_emitted_ = false;
  unbound_labels_count_ = 0;

  ClearRecordedAstId();
}

void Assembler::lnk(const Register& rd, int line) {
  ASSERT(rd.is_valid());
  Instr instr = LNK_X1 | DEST_X1(rd.code());
  emit(instr, line);
}

void Assembler::st(const Register& rd, const MemOperand& rs, int line) {
  ASSERT(rd.is_valid() && rs.rm().is_valid());
  if (rs.offset_ != 0) {
    if (is_int16(rs.offset_)) {
      Instr instr = ADDLI_X1 | DEST_X1(at.code())
                             | SRCA_X1(rs.rm().code()) | IMM16_X1(rs.offset_);
      emit(instr, line);
      instr = ST_X1 | SRCA_X1(at.code()) | SRCB_X1(rd.code());
      emit(instr, line);
    } else {
      moveli(at, (rs.offset_ >> 48) & 0xFFFF, line);
      shl16insli(at, at, (rs.offset_ >> 32) & 0xFFFF, line);
      shl16insli(at, at, (rs.offset_ >> 16) & 0xFFFF, line);
      shl16insli(at, at, rs.offset_ & 0xFFFF, line);
      add(at, rs.rm(), at, line);
      st(rd, at, line);
    }
  } else
    st(rd, rs.rm(), line);
}

void Assembler::st(const Register& rd, const Register& rs, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = ST_X1 | SRCA_X1(rs.code()) | SRCB_X1(rd.code());
  emit(instr, line);
}

void Assembler::st(const DoubleRegister& rd, const MemOperand& rs, int line) {
  ASSERT(rd.is_valid() && rs.rm().is_valid());
  if (rs.offset_ != 0) {
    if (is_int16(rs.offset_)) {
      Instr instr = ADDLI_X1 | DEST_X1(at.code())
                             | SRCA_X1(rs.rm().code()) | IMM16_X1(rs.offset_);
      emit(instr, line);
      instr = ST_X1 | SRCA_X1(at.code()) | SRCB_X1(rd.code());
      emit(instr, line);
    } else {
      moveli(at, (rs.offset_ >> 48) & 0xFFFF, line);
      shl16insli(at, at, (rs.offset_ >> 32) & 0xFFFF, line);
      shl16insli(at, at, (rs.offset_ >> 16) & 0xFFFF, line);
      shl16insli(at, at, rs.offset_ & 0xFFFF, line);
      add(at, rs.rm(), at, line);
      st(rd, at, line);
    }
  } else
    st(rd, rs.rm(), line);
}

void Assembler::st(const DoubleRegister& rd, const Register& rs, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = ST_X1 | SRCA_X1(rs.code()) | SRCB_X1(rd.code());
  emit(instr, line);
}

void Assembler::st1(const Register& rd, const MemOperand& rs, int line) {
  ASSERT(rd.is_valid() && rs.rm().is_valid() && is_int16(rs.offset_));
  if (rs.offset_ != 0) {
    if (is_int16(rs.offset_)) {
    Instr instr = ADDLI_X1 | DEST_X1(at.code())
                           | SRCA_X1(rs.rm().code()) | IMM16_X1(rs.offset_);
    emit(instr, line);
    instr = ST1_X1 | SRCA_X1(at.code()) | SRCB_X1(rd.code());
    emit(instr, line);
    } else
      UNREACHABLE();
  } else
    st1(rd, rs.rm(), line);
}

void Assembler::st1(const Register& rd, const Register& rs, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = ST1_X1 | SRCA_X1(rs.code()) | SRCB_X1(rd.code());
  emit(instr, line);
}

void Assembler::st2(const Register& rd, const MemOperand& rs, int line) {
  ASSERT(rd.is_valid() && rs.rm().is_valid() && is_int16(rs.offset_));
  if (rs.offset_ != 0) {
    if (is_int16(rs.offset_)) {
    Instr instr = ADDLI_X1 | DEST_X1(at.code())
                           | SRCA_X1(rs.rm().code()) | IMM16_X1(rs.offset_);
    emit(instr, line);
    instr = ST2_X1 | SRCA_X1(at.code()) | SRCB_X1(rd.code());
    emit(instr, line);
    } else
      UNREACHABLE();
  } else
    st2(rd, rs.rm(), line);
}

void Assembler::st2(const Register& rd, const Register& rs, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = ST2_X1 | SRCA_X1(rs.code()) | SRCB_X1(rd.code());
  emit(instr, line);
}

void Assembler::st4(const Register& rd, const MemOperand& rs, int line) {
  ASSERT(rd.is_valid() && rs.rm().is_valid() && is_int16(rs.offset_));
  if (rs.offset_ != 0) {
    if (is_int16(rs.offset_)) {
    Instr instr = ADDLI_X1 | DEST_X1(at.code())
                           | SRCA_X1(rs.rm().code()) | IMM16_X1(rs.offset_);
    emit(instr, line);
    instr = ST4_X1 | SRCA_X1(at.code()) | SRCB_X1(rd.code());
    emit(instr, line);
    } else
      UNREACHABLE();
  } else
    st4(rd, rs.rm(), line);
}

void Assembler::st4(const Register& rd, const Register& rs, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = ST4_X1 | SRCA_X1(rs.code()) | SRCB_X1(rd.code());
  emit(instr, line);
}

void Assembler::ld(const Register& rd, const MemOperand& rs, int line) {
  ASSERT(rd.is_valid() && rs.rm().is_valid());
  if (rs.offset_ != 0) {
    if (is_int16(rs.offset_)) {
    Instr instr = ADDLI_X1 | DEST_X1(at.code())
                           | SRCA_X1(rs.rm().code()) | IMM16_X1(rs.offset_);
    emit(instr, line);
    instr = LD_X1 | DEST_X1(rd.code()) | SRCA_X1(at.code());
    emit(instr, line);
    } else {
      moveli(at, (rs.offset_ >> 48) & 0xFFFF, line);
      shl16insli(at, at, (rs.offset_ >> 32) & 0xFFFF, line);
      shl16insli(at, at, (rs.offset_ >> 16) & 0xFFFF, line);
      shl16insli(at, at, rs.offset_ & 0xFFFF, line);
      add(at, rs.rm(), at, line);
      ld(rd, at, line);
    }
  } else
    ld(rd, rs.rm(), line);
}

void Assembler::ld(const Register& rd, const Register& rs, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = LD_X1 | DEST_X1(rd.code()) | SRCA_X1(rs.code());
  emit(instr, line);
}

void Assembler::ld(const DoubleRegister& rd, const MemOperand& rs, int line) {
  ASSERT(rd.is_valid() && rs.rm().is_valid());
  if (rs.offset_ != 0) {
    if (is_int16(rs.offset_)) {
    Instr instr = ADDLI_X1 | DEST_X1(at.code())
                           | SRCA_X1(rs.rm().code()) | IMM16_X1(rs.offset_);
    emit(instr, line);
    instr = LD_X1 | DEST_X1(rd.code()) | SRCA_X1(at.code());
    emit(instr, line);
    } else {
      moveli(at, (rs.offset_ >> 48) & 0xFFFF, line);
      shl16insli(at, at, (rs.offset_ >> 32) & 0xFFFF, line);
      shl16insli(at, at, (rs.offset_ >> 16) & 0xFFFF, line);
      shl16insli(at, at, rs.offset_ & 0xFFFF, line);
      add(at, rs.rm(), at, line);
      ld(rd, at, line);
    }
  } else
    ld(rd, rs.rm(), line);
}

void Assembler::ld(const DoubleRegister& rd, const Register& rs, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = LD_X1 | DEST_X1(rd.code()) | SRCA_X1(rs.code());
  emit(instr, line);
}

void Assembler::ld1s(const Register& rd, const MemOperand& rs, int line) {
  ASSERT(rd.is_valid() && rs.rm().is_valid() && is_int16(rs.offset_));
  if (rs.offset_ != 0) {
    if (is_int16(rs.offset_)) {
    Instr instr = ADDLI_X1 | DEST_X1(at.code())
                           | SRCA_X1(rs.rm().code()) | IMM16_X1(rs.offset_);
    emit(instr, line);
    instr = LD1S_X1 | DEST_X1(rd.code()) | SRCA_X1(at.code());
    emit(instr, line);
    } else
      UNREACHABLE();
  } else
    ld1s(rd, rs.rm(), line);
}

void Assembler::ld1s(const Register& rd, const Register& rs, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = LD1S_X1 | DEST_X1(rd.code()) | SRCA_X1(rs.code());
  emit(instr, line);
}

void Assembler::ld1u(const Register& rd, const MemOperand& rs, int line) {
  ASSERT(rd.is_valid() && rs.rm().is_valid() && is_int16(rs.offset_));
  if (rs.offset_ != 0) {
    if (is_int16(rs.offset_)) {
    Instr instr = ADDLI_X1 | DEST_X1(at.code())
                           | SRCA_X1(rs.rm().code()) | IMM16_X1(rs.offset_);
    emit(instr, line);
    instr = LD1U_X1 | DEST_X1(rd.code()) | SRCA_X1(at.code());
    emit(instr, line);
    } else
      UNREACHABLE();
  } else
    ld1u(rd, rs.rm(), line);
}

void Assembler::ld1u(const Register& rd, const Register& rs, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = LD1U_X1 | DEST_X1(rd.code()) | SRCA_X1(rs.code());
  emit(instr, line);
}

void Assembler::ld2s(const Register& rd, const MemOperand& rs, int line) {
  ASSERT(rd.is_valid() && rs.rm().is_valid() && is_int16(rs.offset_));
  if (rs.offset_ != 0) {
    if (is_int16(rs.offset_)) {
    Instr instr = ADDLI_X1 | DEST_X1(at.code())
                           | SRCA_X1(rs.rm().code()) | IMM16_X1(rs.offset_);
    emit(instr, line);
    instr = LD2S_X1 | DEST_X1(rd.code()) | SRCA_X1(at.code());
    emit(instr, line);
    } else
      UNREACHABLE();
  } else
    ld2s(rd, rs.rm(), line);
}

void Assembler::ld2s(const Register& rd, const Register& rs, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = LD2S_X1 | DEST_X1(rd.code()) | SRCA_X1(rs.code());
  emit(instr, line);
}

void Assembler::ld2u(const Register& rd, const MemOperand& rs, int line) {
  ASSERT(rd.is_valid() && rs.rm().is_valid() && is_int16(rs.offset_));
  if (rs.offset_ != 0) {
    if (is_int16(rs.offset_)) {
    Instr instr = ADDLI_X1 | DEST_X1(at.code())
                           | SRCA_X1(rs.rm().code()) | IMM16_X1(rs.offset_);
    emit(instr, line);
    instr = LD2U_X1 | DEST_X1(rd.code()) | SRCA_X1(at.code());
    emit(instr, line);
    } else
      UNREACHABLE();
  } else
    ld2u(rd, rs.rm(), line);
}

void Assembler::ld2u(const Register& rd, const Register& rs, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = LD2U_X1 | DEST_X1(rd.code()) | SRCA_X1(rs.code());
  emit(instr, line);
}

void Assembler::ld4u(const Register& rd, const MemOperand& rs, int line) {
  ASSERT(rd.is_valid() && rs.rm().is_valid() && is_int16(rs.offset_));
  if (rs.offset_ != 0) {
    if (is_int16(rs.offset_)) {
    Instr instr = ADDLI_X1 | DEST_X1(at.code())
                           | SRCA_X1(rs.rm().code()) | IMM16_X1(rs.offset_);
    emit(instr, line);
    instr = LD4U_X1 | DEST_X1(rd.code()) | SRCA_X1(at.code());
    emit(instr, line);
    } else
      UNREACHABLE();
  } else
    ld4u(rd, rs.rm(), line);
}

void Assembler::ld4u(const Register& rd, const Register& rs, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = LD4U_X1 | DEST_X1(rd.code()) | SRCA_X1(rs.code());
  emit(instr, line);
}

void Assembler::ld4s(const Register& rd, const MemOperand& rs, int line) {
  ASSERT(rd.is_valid() && rs.rm().is_valid() && is_int16(rs.offset_));
  if (rs.offset_ != 0) {
    if (is_int16(rs.offset_)) {
    Instr instr = ADDLI_X1 | DEST_X1(at.code())
                           | SRCA_X1(rs.rm().code()) | IMM16_X1(rs.offset_);
    emit(instr, line);
    instr = LD4S_X1 | DEST_X1(rd.code()) | SRCA_X1(at.code());
    emit(instr, line);
    } else
      UNREACHABLE();
  } else
    ld4s(rd, rs.rm(), line);
}

void Assembler::ld4s(const Register& rd, const Register& rs, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = LD4S_X1 | DEST_X1(rd.code()) | SRCA_X1(rs.code());
  emit(instr, line);
}

void Assembler::fsingle_pack1(const Register& rd, const Register& rsa, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid());
  Instr instr = FSINGLE_PACK1_X0 | DEST_X0(rd.code()) | SRCA_X0(rsa.code());
  emit(instr, line);
}

void Assembler::fsingle_pack2(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = FSINGLE_PACK2_X0 | DEST_X0(rd.code())
	               | SRCA_X0(rsa.code()) | SRCB_X0(rsb.code());
  emit(instr, line);
}

void Assembler::fdouble_pack1(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = FDOUBLE_PACK1_X0 | DEST_X0(rd.code())
	               | SRCA_X0(rsa.code()) | SRCB_X0(rsb.code());
  emit(instr, line);
}

void Assembler::fdouble_pack2(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = FDOUBLE_PACK2_X0 | DEST_X0(rd.code())
	               | SRCA_X0(rsa.code()) | SRCB_X0(rsb.code());
  emit(instr, line);
}

void Assembler::fdouble_add_flags(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = FDOUBLE_ADD_FLAGS_X0 | DEST_X0(rd.code())
	               | SRCA_X0(rsa.code()) | SRCB_X0(rsb.code());
  emit(instr, line);
}

void Assembler::add(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = ADD_X1 | DEST_X1(rd.code())
	               | SRCA_X1(rsa.code()) | SRCB_X1(rsb.code());
  emit(instr, line);
}

void Assembler::sub(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = SUB_X1 | DEST_X1(rd.code())
	               | SRCA_X1(rsa.code()) | SRCB_X1(rsb.code());
  emit(instr, line);
}

void Assembler::subx(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = SUBX_X1 | DEST_X1(rd.code())
	               | SRCA_X1(rsa.code()) | SRCB_X1(rsb.code());
  emit(instr, line);
}

void Assembler::nor(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = NOR_X1 | DEST_X1(rd.code())
	               | SRCA_X1(rsa.code()) | SRCB_X1(rsb.code());
  emit(instr, line);
}

void Assembler::mulx(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = MULX_X0 | DEST_X0(rd.code())
	                | SRCA_X0(rsa.code()) | SRCB_X0(rsb.code());
  emit(instr, line);
}

void Assembler::addi(const Register& rd, const Register& rs, int8_t imm, int line) {
  ASSERT(rd.is_valid() && rs.is_valid() && is_int8(imm));
  Instr instr = ADDI_X1 | DEST_X1(rd.code())
	                | SRCA_X1(rs.code()) | IMM8_X1(imm);
  emit(instr, line);
}

void Assembler::addxi(const Register& rd, const Register& rs, int8_t imm, int line) {
  ASSERT(rd.is_valid() && rs.is_valid() && is_int8(imm));
  Instr instr = ADDXI_X1 | DEST_X1(rd.code())
	                 | SRCA_X1(rs.code()) | IMM8_X1(imm);
  emit(instr, line);
}

void Assembler::and_(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = AND_X1 | DEST_X1(rd.code())
	               | SRCA_X1(rsa.code()) | SRCB_X1(rsb.code());
  emit(instr, line);
}

void Assembler::or_(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = OR_X1 | DEST_X1(rd.code())
	              | SRCA_X1(rsa.code()) | SRCB_X1(rsb.code());
  emit(instr, line);
}

void Assembler::xor_(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = XOR_X1 | DEST_X1(rd.code())
	               | SRCA_X1(rsa.code()) | SRCB_X1(rsb.code());
  emit(instr, line);
}

void Assembler::andi(const Register& rd, const Register& rs, int8_t imm, int line) {
  ASSERT(rd.is_valid() && rs.is_valid() && is_int8(imm));
  Instr instr = ANDI_X1 | DEST_X1(rd.code())
	                | SRCA_X1(rs.code()) | IMM8_X1(imm);
  emit(instr, line);
}

void Assembler::ori(const Register& rd, const Register& rs, int8_t imm, int line) {
  ASSERT(rd.is_valid() && rs.is_valid() && is_int8(imm));
  Instr instr = ORI_X1  | DEST_X1(rd.code())
	                | SRCA_X1(rs.code()) | IMM8_X1(imm);
  emit(instr, line);
}

void Assembler::xori(const Register& rd, const Register& rs, int8_t imm, int line) {
  ASSERT(rd.is_valid() && rs.is_valid() && is_int8(imm));
  Instr instr = XORI_X1 | DEST_X1(rd.code())
	                | SRCA_X1(rs.code()) | IMM8_X1(imm);
  emit(instr, line);
}

void Assembler::addli(const Register& rd, const Register& rs, int16_t imm, int line) {
  ASSERT(rd.is_valid() && rs.is_valid() && is_int16(imm));
  Instr instr = ADDLI_X1 | DEST_X1(rd.code())
	                 | SRCA_X1(rs.code()) | IMM16_X1(imm);
  emit(instr, line);
}

void Assembler::bpt(int line) {
  Instr instr = BPT_X1;
  emit(instr, line);
}

void Assembler::info(const int16_t imm16, int line) {
  ASSERT(is_int16(imm16));
  Instr instr = INFOL_X1 | IMM16_X1(imm16);
  emit(instr, line);
}

void Assembler::shl16insli(const Register& rd, const Register& rs, int16_t imm, int line) {
  ASSERT(rd.is_valid() && rs.is_valid() && is_int16(imm));
  Instr instr = SHL16INSLI_X1 | DEST_X1(rd.code())
	                      | SRCA_X1(rs.code()) | IMM16_X1(imm);
  emit(instr, line);
}

void Assembler::moveli(const Register& rd, int16_t imm, int line) {
  ASSERT(rd.is_valid() && is_int16(imm));
  Instr instr = MOVELI_X1 | DEST_X1(rd.code()) | IMM16_X1(imm);
  emit(instr, line);
}

void Assembler::move(const Register& rd, const Register& rs, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = ADD_X1 | DEST_X1(rd.code())
	               | SRCA_X1(zero.code()) | SRCB_X1(rs.code());
  emit(instr, line);
}

void Assembler::movn(const Register& rd, const Register& rs, const Register& rt, int line) {
  ASSERT(rd.is_valid() && rs.is_valid() && rt.is_valid());
  Instr instr = CMOVNEZ_X0 | DEST_X0(rd.code())
	                   | SRCA_X0(rt.code()) | SRCB_X0(rs.code());
  emit(instr, line);
}

void Assembler::clz(const Register& rd, const Register& rs, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = CLZ_X0 | DEST_X0(rd.code()) | SRCA_X0(rs.code());
  emit(instr, line);
}

void Assembler::v4int_l(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = V4INT_L_X1 | DEST_X1(rd.code())
	              | SRCA_X1(rsa.code()) | SRCB_X1(rsb.code());
  emit(instr, line);
}

void Assembler::movz(const Register& rd, const Register& rs, const Register& rt, int line) {
  ASSERT(rd.is_valid() && rs.is_valid() && rt.is_valid());
  Instr instr = CMOVEQZ_X0 | DEST_X0(rd.code())
	                   | SRCA_X0(rt.code()) | SRCB_X0(rs.code());
  emit(instr, line);
}

void Assembler::srl(const Register& rd, const Register& rs, int16_t imm, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = SHRUI_X1 | DEST_X1(rd.code())
	                 | SRCA_X1(rs.code()) | SHIFTIMM_X1(imm);
  emit(instr, line);
}

void Assembler::srl(const Register& rd, const Register& rs, const Register& rt, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = SHRU_X1 | DEST_X1(rd.code())
	                | SRCA_X1(rs.code()) | SRCB_X1(rt.code());
  emit(instr, line);
}

void Assembler::srlx(const Register& rd, const Register& rs, int16_t imm, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = SHRUXI_X1 | DEST_X1(rd.code())
	                  | SRCA_X1(rs.code()) | SHIFTIMM_X1(imm);
  emit(instr, line);
}

void Assembler::srlx(const Register& rd, const Register& rs, const Register& rt, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = SHRUX_X1 | DEST_X1(rd.code())
	                 | SRCA_X1(rs.code()) | SRCB_X1(rt.code());
  emit(instr, line);
}

void Assembler::sra(const Register& rd, const Register& rs, int16_t imm, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = SHRSI_X1 | DEST_X1(rd.code())
	                 | SRCA_X1(rs.code()) | SHIFTIMM_X1(imm);
  emit(instr, line);
}

void Assembler::sra(const Register& rd, const Register& rs, const Register& rt, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = SHRS_X1 | DEST_X1(rd.code())
	                | SRCA_X1(rs.code()) | SRCB_X1(rt.code());
  emit(instr, line);
}

void Assembler::sll(const Register& rd, const Register& rs, int16_t imm, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = SHLI_X1 | DEST_X1(rd.code())
	                | SRCA_X1(rs.code()) | SHIFTIMM_X1(imm);
  emit(instr, line);
}

void Assembler::sll(const Register& rd, const Register& rs, const Register& rt, int line) {
  ASSERT(rd.is_valid() && rs.is_valid() && rt.is_valid());
  Instr instr = SHL_X1 | DEST_X1(rd.code())
	                | SRCA_X1(rs.code()) | SRCB_X1(rt.code());
  emit(instr, line);
}

void Assembler::sllx(const Register& rd, const Register& rs, int16_t imm, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = SHLXI_X1 | DEST_X1(rd.code())
	                 | SRCA_X1(rs.code()) | SHIFTIMM_X1(imm);
  emit(instr, line);
}

void Assembler::sllx(const Register& rd, const Register& rs, const Register& rt, int line) {
  ASSERT(rd.is_valid() && rs.is_valid() && rt.is_valid());
  Instr instr = SHLX_X1 | DEST_X1(rd.code())
	                | SRCA_X1(rs.code()) | SRCB_X1(rt.code());
  emit(instr, line);
}

void Assembler::mul_hs_hs(const Register& rd, const Register& rs, const Register& rt, int line) {
  ASSERT(rd.is_valid() && rs.is_valid() && rt.is_valid());
  Instr instr = MUL_HS_HS_X0 | DEST_X0(rd.code())
	                | SRCA_X0(rs.code()) | SRCB_X0(rt.code());
  emit(instr, line);
}

void Assembler::mul_ls_ls(const Register& rd, const Register& rs, const Register& rt, int line) {
  ASSERT(rd.is_valid() && rs.is_valid() && rt.is_valid());
  Instr instr = MUL_LS_LS_X0 | DEST_X0(rd.code())
	                | SRCA_X0(rs.code()) | SRCB_X0(rt.code());
  emit(instr, line);
}

void Assembler::mul_lu_lu(const Register& rd, const Register& rs, const Register& rt, int line) {
  ASSERT(rd.is_valid() && rs.is_valid() && rt.is_valid());
  Instr instr = MUL_LU_LU_X0 | DEST_X0(rd.code())
	                | SRCA_X0(rs.code()) | SRCB_X0(rt.code());
  emit(instr, line);
}

void Assembler::mul_hs_ls(const Register& rd, const Register& rs, const Register& rt, int line) {
  ASSERT(rd.is_valid() && rs.is_valid() && rt.is_valid());
  Instr instr = MUL_HS_LS_X0 | DEST_X0(rd.code())
	                | SRCA_X0(rs.code()) | SRCB_X0(rt.code());
  emit(instr, line);
}

void Assembler::GetCode(CodeDesc* desc) {
  ASSERT(pc_ <= reloc_info_writer.pos());  // No overlap.
  // Set up code descriptor.
  desc->buffer = buffer_;
  desc->buffer_size = buffer_size_;
  desc->instr_size = pc_offset();
  desc->reloc_size = (buffer_ + buffer_size_) - reloc_info_writer.pos();
}

void Assembler::print(Label* L) {
  if (L->is_unused()) {
    PrintF("unused label\n");
  } else if (L->is_bound()) {
    PrintF("bound label to %d\n", L->pos());
  } else if (L->is_linked()) {
    Label l = *L;
    PrintF("unbound label");
    while (l.is_linked()) {
      PrintF("@ %d ", l.pos());
      Instr instr = instr_at(l.pos());
      if ((instr & ~kImm16Mask) == 0) {
        PrintF("value\n");
      } else {
        PrintF("0x%08lx\n", (long)instr);
      }
      next(&l);
    }
  } else {
    PrintF("label in inconsistent state (pos = %d)\n", L->pos_);
  }
}

const int kEndOfChain = 0;

int Assembler::target_at(int32_t pos) {
  Instr instr = instr_at(pos);
  if ((instr & ~kImm16Mask) == 0) {
    // Emitted label constant, not part of a branch.
    if (instr == 0) {
       return kEndOfChain;
     } else {
       int32_t imm18 =((instr & static_cast<int32_t>(kImm16Mask)) << 16) >> 14;
       return (imm18 + pos);
     }
  }
#ifdef TILEGX_DEBUG
  // Check we have a branch or jump instruction.
  printf("==> ");
  print_insn_tilegx((unsigned char *)&instr);
#endif
  ASSERT(IsBranch(instr) || IsJ(instr) || IsJAL(instr) || IsMOVELI(instr));
  // Do NOT change this to << 3. We rely on arithmetic shifts here, assuming
  // the compiler uses arithmectic shifts for signed integers.
  if (IsBranch(instr)) {
    int32_t imm20 = (((int)get_BrOff_X1(instr)) << 15) >> 12;

    if (imm20 == kEndOfChain) {
      // EndOfChain sentinel is returned directly, not relative to pc or pos.
      return kEndOfChain;
    } else {
      return pos + imm20;
    }
  } else if (IsMOVELI(instr)) {
    Instr instr_moveli = instr_at(pos + 0 * Assembler::kInstrSize);
    Instr instr_shl16insli_0 = instr_at(pos + 1 * Assembler::kInstrSize);
    Instr instr_shl16insli_1 = instr_at(pos + 2 * Assembler::kInstrSize);
    ASSERT(IsMOVELI(instr_moveli));
    ASSERT(IsSHL16INSLI(instr_shl16insli_0));
    ASSERT(IsSHL16INSLI(instr_shl16insli_1));
    int64_t imm = ((int64_t)get_Imm16_X1(instr_moveli)) << 32; 
    imm |= get_Imm16_X1(instr_shl16insli_0) << 16;
    imm |= get_Imm16_X1(instr_shl16insli_1);

    if (imm == kEndOfJumpChain) {
      // EndOfChain sentinel is returned directly, not relative to pc or pos.
      return kEndOfChain;
    } else {
      uint64_t instr_address = reinterpret_cast<int64_t>(buffer_ + pos);
      int64_t delta = instr_address - imm;
      ASSERT(pos > delta);
      return pos - delta;
    }
  } else {
    int64_t imm30 = get_JumpOff_X1(instr) << 3;
    if (imm30 == kEndOfJumpChain) {
      // EndOfChain sentinel is returned directly, not relative to pc or pos.
      return kEndOfChain;
    } else {
      return pos + imm30;
    }
  }
}

void Assembler::target_at_put(int32_t pos, int32_t target_pos) {
  Instr instr = instr_at(pos);
  if ((instr & ~kImm16Mask) == 0) {
    ASSERT(target_pos == kEndOfChain || target_pos >= 0);
    // Emitted label constant, not part of a branch.
    // Make label relative to Code* of generated Code object.
    instr_at_put(pos, target_pos + (Code::kHeaderSize - kHeapObjectTag));
    return;
  }

  ASSERT(IsBranch(instr) || IsJ(instr) || IsJAL(instr) || IsMOVELI(instr));
  if (IsBranch(instr)) {
    int32_t imm20 = target_pos - pos;
    ASSERT((imm20 & 7) == 0);

    int32_t imm17 = imm20 >> 3;
    ASSERT(is_intn(imm17, 17));

    instr_at_put(pos, (instr & (~create_BrOff_X1(-1))) | create_BrOff_X1(imm17));
  } else if (IsMOVELI(instr)) {
    // TileGX userspace address space is less than 48bit, although
    // we support 64bit in theory.
    Instr instr_moveli = instr_at(pos + 0 * Assembler::kInstrSize);
    Instr instr_shl16insli_0 = instr_at(pos + 1 * Assembler::kInstrSize);
    Instr instr_shl16insli_1 = instr_at(pos + 2 * Assembler::kInstrSize);
    ASSERT(IsSHL16INSLI(instr_shl16insli_0));
    ASSERT(IsSHL16INSLI(instr_shl16insli_1));
    uint64_t imm = reinterpret_cast<uint64_t>(buffer_) + target_pos;
    ASSERT((imm & 7) == 0);

    instr_moveli &= ~create_Imm16_X1(-1);
    instr_shl16insli_0 &= ~create_Imm16_X1(-1);
    instr_shl16insli_1 &= ~create_Imm16_X1(-1);

    instr_at_put(pos + 0 * Assembler::kInstrSize,
                 instr_moveli | create_Imm16_X1(imm >> 32));
    instr_at_put(pos + 1 * Assembler::kInstrSize,
                 instr_shl16insli_0 | create_Imm16_X1(imm >> 16));
    instr_at_put(pos + 2 * Assembler::kInstrSize,
                 instr_shl16insli_1 | create_Imm16_X1(imm));
  } else {
    int32_t imm30 = target_pos - pos;
    ASSERT((imm30 & 7) == 0);

    int32_t imm27 = imm30 >> 3;
    ASSERT(is_intn(imm27, 27));

    instr_at_put(pos, (instr & (~create_JumpOff_X1(-1))) | create_JumpOff_X1(imm27));
  }
}

// Returns the next free trampoline entry.
void Assembler::bind_to(Label* L, int pos) {
  ASSERT(0 <= pos && pos <= pc_offset());  // Must have valid binding position.
  int32_t trampoline_pos = kInvalidSlotPos;
  if (L->is_linked() && !trampoline_emitted_) {
    unbound_labels_count_--;
    next_buffer_check_ += kTrampolineSlotsSize;
  }

  while (L->is_linked()) {
    int32_t fixup_pos = L->pos();
    int32_t dist = pos - fixup_pos;
    next(L);  // Call next before overwriting link with target at fixup_pos.
    Instr instr = instr_at(fixup_pos);
    if (IsBranch(instr)) {
      if (dist > kMaxBranchOffset) {
        if (trampoline_pos == kInvalidSlotPos) {
          trampoline_pos = get_trampoline_entry(fixup_pos);
          CHECK(trampoline_pos != kInvalidSlotPos);
        }
        ASSERT((trampoline_pos - fixup_pos) <= kMaxBranchOffset);
        target_at_put(fixup_pos, trampoline_pos);
        fixup_pos = trampoline_pos;
        dist = pos - fixup_pos;
      }
      target_at_put(fixup_pos, pos);
    } else {
      ASSERT(IsJ(instr) || IsJAL(instr) || IsMOVELI(instr) || IsEmittedConstant(instr));
      target_at_put(fixup_pos, pos);
    }
  }
  L->bind_to(pos);

  // Keep track of the last bound label so we don't eliminate any instructions
  // before a bound label.
  if (pos > last_bound_pos_)
    last_bound_pos_ = pos;
}

void Assembler::next(Label* L) {
  ASSERT(L->is_linked());
  int link = target_at(L->pos());
  if (link == kEndOfChain) {
    L->Unuse();
  } else {
    ASSERT(link >= 0);
    L->link_to(link);
  }
}

void Assembler::bind(Label* L) {
  ASSERT(!L->is_bound());
  bind_to(L, pc_offset());
}

Address Assembler::target_address_at(Address pc) {
  Instr instr1 = instr_at(pc);
  Instr instr2 = instr_at(pc + kInstrSize);
  Instr instr3 = instr_at(pc + 2 * kInstrSize);

  // Interpret 2 instructions generated by li: lui/ori
  if (IsMOVELI(instr1) && IsSHL16INSLI(instr2) && IsSHL16INSLI(instr3)) {
    // Assemble the 48 bit value.
    // FIXME: currently, we always assume they are encoded in X1 slot.
    return reinterpret_cast<Address>(
        ((long)((short)get_Imm16_X1(instr1)) << 32) | (get_Imm16_X1(instr2) << 16) | get_Imm16_X1(instr3));
  }

  // We should never get here, force a bad address if we do.
  UNREACHABLE();
  return (Address)0x0;
}

// On TileGX, a target address is stored in a moveli/shl16insli/shl16insli instruction pair,
// each of which load 16 bits of the 48-bit address to a register.
// Patching the address must replace both instr, and flush the i-cache.
// (TileGX support 64bit address space in theory, but currently, we only use
//  less than 48bit)
//
// There is an optimization below, which emits a nop when the address
// fits in just 16 bits. This is unlikely to help, and should be benchmarked,
// and possibly removed.
void Assembler::set_target_address_at(Address pc, Address target) {
  Instr instr2 = instr_at(pc + kInstrSize);
  uint32_t rt_code = get_SrcA_X1(instr2);
  uint64_t* p = reinterpret_cast<uint64_t*>(pc);
  uint64_t itarget = reinterpret_cast<uint64_t>(target);

#ifdef DEBUG
  // Check we have the result from a li macro-instruction, using instr pair.
  Instr instr1 = instr_at(pc);
  Instr instr3 = instr_at(pc + 2 * kInstrSize);
  CHECK(IsMOVELI(instr1) && IsSHL16INSLI(instr2) && IsSHL16INSLI(instr3));
#endif

  *p = MOVELI_X1 | DEST_X1(rt_code) | IMM16_X1(itarget >> 32);
  *(p+1) = SHL16INSLI_X1 | DEST_X1(rt_code) | SRCA_X1(rt_code) | IMM16_X1(itarget >> 16);
  *(p+2) = SHL16INSLI_X1 | DEST_X1(rt_code) | SRCA_X1(rt_code) | IMM16_X1(itarget);

  // The following code is an optimization for the common case of Call()
  // or Jump() which is load to register, and jump through register:
  //     li(t9, address); jalr(t9)    (or jr(t9)).
  // If the destination address is in the same 256 MB page as the call, it
  // is faster to do a direct jal, or j, rather than jump thru register, since
  // that lets the cpu pipeline prefetch the target address. However each
  // time the address above is patched, we have to patch the direct jal/j
  // instruction, as well as possibly revert to jalr/jr if we now cross a
  // 256 MB page. Note that with the jal/j instructions, we do not need to
  // load the register, but that code is left, since it makes it easy to
  // revert this process. A further optimization could try replacing the
  // li sequence with nops.
  // This optimization can only be applied if the rt-code from instr2 is the
  // register used for the jalr/jr. Finally, we have to skip 'jr ra', which is
  // mips return. Occasionally this lands after an li().

#if 0
  Instr instr3 = instr_at(pc + 2 * kInstrSize);
  uint32_t ipc = reinterpret_cast<uint32_t>(pc + 3 * kInstrSize);
  bool in_range = (ipc ^ static_cast<uint32_t>(itarget) >>
                  (kImm26Bits + kImmFieldShift)) == 0;
  uint32_t target_field =
      static_cast<uint32_t>(itarget & kJumpAddrMask) >>kImmFieldShift;
  bool patched_jump = false;

  if (IsJalr(instr3)) {
    // Try to convert JALR to JAL.
    if (in_range && GetRt(instr2) == GetRs(instr3)) {
      *(p+2) = JAL | target_field;
      patched_jump = true;
    }
  } else if (IsJr(instr3)) {
    // Try to convert JR to J, skip returns (jr ra).
    bool is_ret = static_cast<int>(GetRs(instr3)) == ra.code();
    if (in_range && !is_ret && GetRt(instr2) == GetRs(instr3)) {
      *(p+2) = J | target_field;
      patched_jump = true;
    }
  } else if (IsJal(instr3)) {
    if (in_range) {
      // We are patching an already converted JAL.
      *(p+2) = JAL | target_field;
    } else {
      // Patch JAL, but out of range, revert to JALR.
      // JALR rs reg is the rt reg specified in the ORI instruction.
      uint32_t rs_field = GetRt(instr2) << kRsShift;
      uint32_t rd_field = ra.code() << kRdShift;  // Return-address (ra) reg.
      *(p+2) = SPECIAL | rs_field | rd_field | JALR;
    }
    patched_jump = true;
  } else if (IsJ(instr3)) {
    if (in_range) {
      // We are patching an already converted J (jump).
      *(p+2) = J | target_field;
    } else {
      // Trying patch J, but out of range, just go back to JR.
      // JR 'rs' reg is the 'rt' reg specified in the ORI instruction (instr2).
      uint32_t rs_field = GetRt(instr2) << kRsShift;
      *(p+2) = SPECIAL | rs_field | JR;
    }
    patched_jump = true;
  }
#endif

  CPU::FlushICache(pc, 3 * sizeof(int64_t));
}

void Assembler::Align(int m) {
  ASSERT(m >= 4 && IsPowerOf2(m));
  while ((pc_offset() & (m - 1)) != 0) {
    nop();
  }
}

void Assembler::db(uint8_t data) {
  CheckBuffer();
  *reinterpret_cast<uint8_t*>(pc_) = data;
  pc_ += sizeof(uint8_t);
}


void Assembler::dd(uint32_t data) {
  CheckBuffer();
  *reinterpret_cast<uint32_t*>(pc_) = data;
  pc_ += sizeof(uint32_t);
}

void Assembler::dq(uint64_t data) {
  CheckBuffer();
  *reinterpret_cast<uint64_t*>(pc_) = data;
  pc_ += sizeof(uint64_t);
}

bool Assembler::IsNop(Instr instr, unsigned int type) {
  // See Assembler::nop(type).
  ASSERT(type < 32);

  uint32_t mode = get_Mode(instr);
  int32_t X0_OPC = -1, X1_OPC = -1;
  int32_t X0_SUB_OPC = -1, X1_SUB_OPC = -1;

  if (mode != 0)
    return false;

  X0_OPC = get_Opcode_X0(instr);
  X1_OPC = get_Opcode_X1(instr);
  X0_SUB_OPC = get_ShiftOpcodeExtension_X0(instr);
  X1_SUB_OPC = get_ShiftOpcodeExtension_X1(instr);

  Register nop_rt_reg = (type == 0) ? zero : at;
  bool ret = ((X0_OPC == SHIFT_OPCODE_X0
              && X0_SUB_OPC == SHLI_SHIFT_OPCODE_X0
              && get_SrcA_X0(instr) == static_cast<uint32_t>(ToNumber(nop_rt_reg))
              && get_ShAmt_X0(instr) == type)
             || (X1_OPC == SHIFT_OPCODE_X1
                 && X1_SUB_OPC == SHLI_SHIFT_OPCODE_X1
                 && get_SrcA_X1(instr) == static_cast<uint32_t>(ToNumber(nop_rt_reg))
                 && get_ShAmt_X1(instr) == type));

  return ret;
}

const int RelocInfo::kApplyMask = RelocInfo::kCodeTargetMask |
                                  1 << RelocInfo::INTERNAL_REFERENCE;

int Assembler::RelocateInternalReference(byte* pc, intptr_t pc_delta) {
  Instr instr = instr_at(pc);
  ASSERT(IsJ(instr) || IsMOVELI(instr));
  if (IsMOVELI(instr)) {
    Instr instr_moveli = instr_at(pc + 0 * Assembler::kInstrSize);
    Instr instr_shl16insli0 = instr_at(pc + 1 * Assembler::kInstrSize);
    Instr instr_shl16insli1 = instr_at(pc + 2 * Assembler::kInstrSize);
    Instr instr_shl16insli2 = instr_at(pc + 3 * Assembler::kInstrSize);
    ASSERT(IsSHL16INSLI(instr_shl16insli0));
    ASSERT(IsSHL16INSLI(instr_shl16insli1));
    ASSERT(!IsSHL16INSLI(instr_shl16insli2));
    int64_t imm = ((long)get_Imm16_X1(instr_moveli) << 32 )
                   | (get_Imm16_X1(instr_shl16insli0) << 16) | get_Imm16_X1(instr_shl16insli1);

    if (imm == kEndOfJumpChain) {
      return 0;  // Number of instructions patched.
    }

    imm += pc_delta;
    ASSERT((imm & 7) == 0);

    instr_moveli &= ~get_Imm16_X1(-1);
    instr_shl16insli0 &= ~get_Imm16_X1(-1);
    instr_shl16insli1 &= ~get_Imm16_X1(-1);

    instr_at_put(pc + 0 * Assembler::kInstrSize,
                 instr_moveli | get_Imm16_X1(imm >> 32));
    instr_at_put(pc + 1 * Assembler::kInstrSize,
                 instr_shl16insli0 | get_Imm16_X1(imm >> 16));
    instr_at_put(pc + 2 * Assembler::kInstrSize,
                 instr_shl16insli1 | get_Imm16_X1(imm));
    return 3;  // Number of instructions patched.
  } else {
    uint64_t imm30 = get_JumpOff_X1(instr) << 3;
    if (static_cast<int32_t>(imm30) == kEndOfJumpChain) {
      return 0;  // Number of instructions patched.
    }
    imm30 += pc_delta;
    ASSERT((imm30 & 7) == 0);

    instr &= ~get_JumpOff_X1(-1);
    uint32_t imm27 = imm30 >> 3;
    ASSERT(is_uintn(imm27, 27));

    instr_at_put(pc, instr | get_JumpOff_X1(imm27));
    return 1;  // Number of instructions patched.
  }
}

void Assembler::RecordJSReturn() {
  positions_recorder()->WriteRecordedPositions();
  CheckBuffer();
  RecordRelocInfo(RelocInfo::JS_RETURN);
}

void Assembler::RecordDebugBreakSlot() {
  positions_recorder()->WriteRecordedPositions();
  CheckBuffer();
  RecordRelocInfo(RelocInfo::DEBUG_BREAK_SLOT);
}

void Assembler::RecordComment(const char* msg) {
  if (FLAG_code_comments) {
    CheckBuffer();
    RecordRelocInfo(RelocInfo::COMMENT, reinterpret_cast<intptr_t>(msg));
  }
}

MemOperand::MemOperand(Register rm, int64_t offset) : Operand(rm) {
  offset_ = offset;
}

Operand::Operand(Handle<Object> handle) {
  AllowDeferredHandleDereference using_raw_address;
  rm_ = no_reg;
  // Verify all Objects referred by code are NOT in new space.
  Object* obj = *handle;
  if (obj->IsHeapObject()) {
    ASSERT(!HeapObject::cast(obj)->GetHeap()->InNewSpace(obj));
    imm64_ = reinterpret_cast<intptr_t>(handle.location());
    rmode_ = RelocInfo::EMBEDDED_OBJECT;
  } else {
    // No relocation needed.
    imm64_ = reinterpret_cast<intptr_t>(obj);
    rmode_ = RelocInfo::NONE32;
  }
}

bool RelocInfo::IsCodedSpecially() {
  // The deserializer needs to know whether a pointer is specially coded.  Being
  // specially coded on MIPS means that it is a lui/ori instruction, and that is
  // always the case inside code objects.
  return true;
}

// Patch the code at the current address with the supplied instructions.
void RelocInfo::PatchCode(byte* instructions, int instruction_count) {
  Instr* pc = reinterpret_cast<Instr*>(pc_);
  Instr* instr = reinterpret_cast<Instr*>(instructions);
  for (int i = 0; i < instruction_count; i++) {
    *(pc + i) = *(instr + i);
  }

  // Indicate that code has changed.
  CPU::FlushICache(pc_, instruction_count * Assembler::kInstrSize);
}

// Patch the code at the current PC with a call to the target address.
// Additional guard instructions can be added if required.
void RelocInfo::PatchCodeWithCall(Address target, int guard_bytes) {
  // Patch the code at the current address with a call to the target.
  UNIMPLEMENTED_TILEGX();
}

void Assembler::RecordRelocInfo(RelocInfo::Mode rmode, intptr_t data) {
  // We do not try to reuse pool constants.
  RelocInfo rinfo(pc_, rmode, data, NULL);
  if (!RelocInfo::IsNone(rinfo.rmode())) {
    // Don't record external references unless the heap will be serialized.
    if (rmode == RelocInfo::EXTERNAL_REFERENCE) {
#ifdef DEBUG
      if (!Serializer::enabled()) {
        Serializer::TooLateToEnableNow();
      }
#endif
      if (!Serializer::enabled() && !emit_debug_code()) {
        return;
      }
    }
    ASSERT(buffer_space() >= kMaxRelocSize);  // Too late to grow buffer here.
    if (rmode == RelocInfo::CODE_TARGET_WITH_ID) {
      RelocInfo reloc_info_with_ast_id(pc_,
                                       rmode,
                                       RecordedAstId().ToInt(),
                                       NULL);
      ClearRecordedAstId();
      reloc_info_writer.Write(&reloc_info_with_ast_id);

    } else {
      reloc_info_writer.Write(&rinfo);
    }
  }

}


void Assembler::b(int32_t offset, int line) {
  beqz(zero, offset, line);
}

void Assembler::beqz(const Register& rs, int32_t offset, int line) {
  ASSERT(rs.is_valid());
  Instr instr = BEQZ_X1 | SRCA_X1(rs.code()) | BOFF_X1(offset);
  emit(instr, line);
}

void Assembler::bnez(const Register& rs, int32_t offset, int line) {
  ASSERT(rs.is_valid());
  Instr instr = BNEZ_X1 | SRCA_X1(rs.code()) | BOFF_X1(offset);
  emit(instr, line);
}

void Assembler::bgez(const Register& rs, int32_t offset, int line) {
  ASSERT(rs.is_valid());
  Instr instr = BGEZ_X1 | SRCA_X1(rs.code()) | BOFF_X1(offset);
  emit(instr, line);
}

void Assembler::bgtz(const Register& rs, int32_t offset, int line) {
  ASSERT(rs.is_valid());
  Instr instr = BGTZ_X1 | SRCA_X1(rs.code()) | BOFF_X1(offset);
  emit(instr, line);
}

void Assembler::blez(const Register& rs, int32_t offset, int line) {
  ASSERT(rs.is_valid());
  Instr instr = BLEZ_X1 | SRCA_X1(rs.code()) | BOFF_X1(offset);
  emit(instr, line);
}

void Assembler::bltz(const Register& rs, int32_t offset, int line) {
  ASSERT(rs.is_valid());
  Instr instr = BLTZ_X1 | SRCA_X1(rs.code()) | BOFF_X1(offset);
  emit(instr, line);
}

void Assembler::bfins(const Register& rd, const Register& rs, int32_t offset1, int32_t offset2, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = BFINS_X0 | DEST_X0(rd.code()) | SRCA_X0(rs.code()) | BFSTART_X0(offset1) | BFEND_X0(offset2);
  emit(instr, line);
}

void Assembler::bfextu(const Register& rd, const Register& rs, int32_t offset1, int32_t offset2, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = BFEXTU_X0 | DEST_X0(rd.code()) | SRCA_X0(rs.code()) | BFSTART_X0(offset1) | BFEND_X0(offset2);
  emit(instr, line);
}

void Assembler::bfexts(const Register& rd, const Register& rs, int32_t offset1, int32_t offset2, int line) {
  ASSERT(rd.is_valid() && rs.is_valid());
  Instr instr = BFEXTS_X0 | DEST_X0(rd.code()) | SRCA_X0(rs.code()) | BFSTART_X0(offset1) | BFEND_X0(offset2);
  emit(instr, line);
}

void Assembler::cmpeq(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = CMPEQ_X1 | DEST_X1(rd.code()) | SRCA_X1(rsa.code()) | SRCB_X1(rsb.code());
  emit(instr, line);
}

void Assembler::cmpne(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = CMPNE_X1 | DEST_X1(rd.code()) | SRCA_X1(rsa.code()) | SRCB_X1(rsb.code());
  emit(instr, line);
}

void Assembler::cmplts(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = CMPLTS_X1 | DEST_X1(rd.code()) | SRCA_X1(rsa.code()) | SRCB_X1(rsb.code());
  emit(instr, line);
}

void Assembler::cmpltsi(const Register& rd, const Register& rsa, int8_t imm, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && is_int8(imm));
  Instr instr = CMPLTSI_X1 | DEST_X1(rd.code()) | SRCA_X1(rsa.code()) | IMM8_X1(imm);
  emit(instr, line);
}

Instr Assembler::cmpltsi_b(const Register& rd, const Register& rsa, int8_t imm, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && is_int8(imm));
  Instr instr = CMPLTSI_X1 | DEST_X1(rd.code()) | SRCA_X1(rsa.code()) | IMM8_X1(imm);
  return instr;
}

void Assembler::cmples(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = CMPLES_X1 | DEST_X1(rd.code()) | SRCA_X1(rsa.code()) | SRCB_X1(rsb.code());
  emit(instr, line);
}

void Assembler::cmpltu(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = CMPLTU_X1 | DEST_X1(rd.code()) | SRCA_X1(rsa.code()) | SRCB_X1(rsb.code());
  emit(instr, line);
}

void Assembler::cmpltui(const Register& rd, const Register& rsa, int8_t imm, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && is_int8(imm));
  Instr instr = CMPLTUI_X1 | DEST_X1(rd.code()) | SRCA_X1(rsa.code()) | IMM8_X1(imm);
  emit(instr, line);
}

void Assembler::cmpleu(const Register& rd, const Register& rsa, const Register& rsb, int line) {
  ASSERT(rd.is_valid() && rsa.is_valid() && rsb.is_valid());
  Instr instr = CMPLEU_X1 | DEST_X1(rd.code()) | SRCA_X1(rsa.code()) | SRCB_X1(rsb.code());
  emit(instr, line);
}

int32_t Assembler::branch_offset(Label* L, bool is_long) {
  int32_t target_pos;

  if (L->is_bound()) {
    target_pos = L->pos();
  } else {
    if (L->is_linked()) {
      target_pos = L->pos();
      L->link_to(pc_offset());
    } else {
      L->link_to(pc_offset());
      return kEndOfChain;
    }
  }

  int32_t offset = target_pos - pc_offset();
  ASSERT((offset & 7) == 0);
  ASSERT(is_intn(offset >> 3, is_long ? 27 : 17));

  return offset;
}

void Assembler::GrowBuffer() {
  if (!own_buffer_) FATAL("external code buffer is too small");

  // Compute new buffer size.
  CodeDesc desc;  // The new buffer.
  if (buffer_size_ < 4*KB) {
    desc.buffer_size = 4*KB;
  } else if (buffer_size_ < 1*MB) {
    desc.buffer_size = 2*buffer_size_;
  } else {
    desc.buffer_size = buffer_size_ + 1*MB;
  }
  CHECK_GT(desc.buffer_size, 0);  // No overflow.

  // Set up new buffer.
  desc.buffer = NewArray<byte>(desc.buffer_size);

  desc.instr_size = pc_offset();
  desc.reloc_size = (buffer_ + buffer_size_) - reloc_info_writer.pos();

  // Copy the data.
  intptr_t pc_delta = desc.buffer - buffer_;
  intptr_t rc_delta = (desc.buffer + desc.buffer_size) - (buffer_ + buffer_size_);
  OS::MemMove(desc.buffer, buffer_, desc.instr_size);
  OS::MemMove(reloc_info_writer.pos() + rc_delta,
              reloc_info_writer.pos(), desc.reloc_size);

  // Switch buffers.
  DeleteArray(buffer_);
  buffer_ = desc.buffer;
  buffer_size_ = desc.buffer_size;
  pc_ += pc_delta;
  reloc_info_writer.Reposition(reloc_info_writer.pos() + rc_delta,
                               reloc_info_writer.last_pc() + pc_delta);

  // Relocate runtime entries.
  for (RelocIterator it(desc); !it.done(); it.next()) {
    RelocInfo::Mode rmode = it.rinfo()->rmode();
    if (rmode == RelocInfo::INTERNAL_REFERENCE) {
      byte* p = reinterpret_cast<byte*>(it.rinfo()->pc());
      RelocateInternalReference(p, pc_delta);
    }
  }

  ASSERT(!overflow());
}

bool Assembler::is_near(Label* L) {
  if (L->is_bound()) {
    return (pc_offset() - L->pos()) < ((1 << 30) - 1);
  }
  return false;
}

uint64_t Assembler::jump_address(Label* L) {
  int64_t target_pos;

  if (L->is_bound()) {
    target_pos = L->pos();
  } else {
    if (L->is_linked()) {
      target_pos = L->pos();  // L's link.
      L->link_to(pc_offset());
    } else {
      L->link_to(pc_offset());
      return kEndOfJumpChain;
    }
  }

  uint64_t imm = reinterpret_cast<uint64_t>(buffer_) + target_pos;
  ASSERT((imm & 7) == 0);

  return imm;
}

void Assembler::jr(Register rs, int line) {
  if (rs.is(lr)) {
    positions_recorder()->WriteRecordedPositions();
  }

  Instr instr = JR_X1 | SRCA_X1(rs.code());
  emit(instr, line);
}

void Assembler::jalr(Register rs, int line) {
  positions_recorder()->WriteRecordedPositions();
  Instr instr = JALR_X1 | SRCA_X1(rs.code());
  emit(instr, line);
}

void Assembler::j(int64_t target, int line) {
  Instr instr = J_X1 | JOFF_X1(target);
  emit(instr, line);
}

void Assembler::jal(int32_t offset, int line) {
  Instr instr = JAL_X1 | JOFF_X1(offset);
  emit(instr, line);
}

// We have to use a temporary register for things that can be relocated even
// if they can be encoded in the MIPS's 16 bits of immediate-offset instruction
// space.  There is no guarantee that the relocated location can be similarly
// encoded.
bool Assembler::MustUseReg(RelocInfo::Mode rmode) {
  return !RelocInfo::IsNone(rmode);
}

int ToNumber(Register reg) {
  ASSERT(reg.is_valid());
  const int kNumbers[] = {
    0,
    1,
    2,
    3,
    4,
    5,
    6,
    7,
    8,
    9,
    10,
    11,
    12,
    13,
    14,
    15,
    16,
    17,
    18,
    19,
    20,
    21,
    22,
    23,
    24,
    25,
    26,
    27,
    28,
    29,
    30,
    31,
    32,
    33,
    34,
    35,
    36,
    37,
    38,
    39,
    40,
    41,
    42,
    43,
    44,
    45,
    46,
    47,
    48,
    49,
    50,
    51,
    52,
    53,
    54,
    55,
    56,
    57,
    58,
    59,
    60,
    61,
    62,
    63,
  };
  return kNumbers[reg.code()];
}

Register ToRegister(int num) {
  ASSERT(num >= 0 && num < kNumRegisters);
  const Register kRegisters[] = {
    r0, r1, r2, r3, r4, r5, r6, r7,
    r8, r9, r10, r11, r12, r13, r14, r15,
    r16, r17, r18, r19, r20, r21, r22, r23,
    r24, r25, r26, r27, r28, r29, r30, r31,
    r32, r33, r34, r35, r36, r37, r38, r39,
    r40, r41, r42, r43, r44, r45, r46, r47,
    r48, r49, r50, r51, r52, r53, r54, r55,
    r56, r57, r58, r59, r60, r61, r62, r63
  };
  return kRegisters[num];
}

// Returns the next free trampoline entry.
int32_t Assembler::get_trampoline_entry(int32_t pos) {
  int32_t trampoline_entry = kInvalidSlotPos;

  if (!internal_trampoline_exception_) {
    if (trampoline_.start() > pos) {
     trampoline_entry = trampoline_.take_slot();
    }

    if (kInvalidSlotPos == trampoline_entry) {
      internal_trampoline_exception_ = true;
    }
  }
  return trampoline_entry;
}

uint32_t Assembler::GetLabelConst(Instr instr) {
  return instr & ~kImm16Mask;
}

bool Assembler::IsEmittedConstant(Instr instr) {
  uint32_t label_constant = GetLabelConst(instr);
  return label_constant == 0;  // Emitted label const in reg-exp engine.
}

void Assembler::break_(uint32_t code, bool break_as_stop) {
  ASSERT((code & ~0xfffff) == 0);
  // We need to invalidate breaks that could be stops as well because the
  // simulator expects a char pointer after the stop instruction.
  // See constants-mips.h for explanation.
  ASSERT((break_as_stop &&
          code <= kMaxStopCode &&
          code > kMaxWatchpointCode) ||
         (!break_as_stop &&
          (code > kMaxStopCode ||
           code <= kMaxWatchpointCode)));
  Instr break_instr = BPT_X1;
  emit(break_instr);
}

void Assembler::stop(const char* msg, uint32_t code) {
  ASSERT(code > kMaxWatchpointCode);
  ASSERT(code <= kMaxStopCode);
#if V8_HOST_ARCH_TILEGX
  break_(0x54321);
#else  // V8_HOST_ARCH_TILEGX
#if 0 // No Simulator Support for TileGX
  BlockTrampolinePoolFor(2);
  // The Simulator will handle the stop instruction and get the message address.
  // On MIPS stop() is just a special kind of break_().
  break_(code, true);
  emit(reinterpret_cast<Instr>(msg));
#else
  UNREACHABLE();
#endif
#endif
}

void Assembler::JumpLabelToJumpRegister(Address pc) {
  UNREACHABLE();
}

} }  // namespace v8::internal

#endif  // V8_TARGET_ARCH_TILEGX
