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


#ifndef V8_TILEGX_ASSEMBLER_TILEGX_H_
#define V8_TILEGX_ASSEMBLER_TILEGX_H_

#include <stdio.h>
#include <arch/opcode.h>
#include "assembler.h"
#include "cpu.h"
#include "constants-tilegx.h"
#include "serialize.h"

namespace v8 {
namespace internal {

int print_insn_tilegx (unsigned char * memaddr);
int print_insn_tilegx_buf (unsigned char * memaddr, char *buf);

/* Opcode Helper Macros */
#define TILEGX_X_MODE 0

#define ANOP_X0                                                                \
  create_Opcode_X0(RRR_0_OPCODE_X0) |                                          \
      create_RRROpcodeExtension_X0(UNARY_RRR_0_OPCODE_X0) |                    \
      create_UnaryOpcodeExtension_X0(NOP_UNARY_OPCODE_X0)

#define FNOP_X0                                                                \
  create_Opcode_X0(RRR_0_OPCODE_X0) |                                          \
      create_RRROpcodeExtension_X0(UNARY_RRR_0_OPCODE_X0) |                    \
      create_UnaryOpcodeExtension_X0(FNOP_UNARY_OPCODE_X0)

#define FNOP_X1                                                                \
  create_Opcode_X1(RRR_0_OPCODE_X1) |                                          \
      create_RRROpcodeExtension_X1(UNARY_RRR_0_OPCODE_X1) |                    \
      create_UnaryOpcodeExtension_X1(FNOP_UNARY_OPCODE_X1)

#define NOP create_Mode(TILEGX_X_MODE) | FNOP_X0 | FNOP_X1

#define MUL_LU_LU_X0                                                           \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
      create_RRROpcodeExtension_X0(MUL_LU_LU_RRR_0_OPCODE_X0) | FNOP_X1

#define MUL_LS_LS_X0                                                           \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
      create_RRROpcodeExtension_X0(MUL_LS_LS_RRR_0_OPCODE_X0) | FNOP_X1

#define MUL_HS_LS_X0                                                           \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
      create_RRROpcodeExtension_X0(MUL_HS_LS_RRR_0_OPCODE_X0) | FNOP_X1

#define MUL_HS_HS_X0                                                           \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
      create_RRROpcodeExtension_X0(MUL_HS_HS_RRR_0_OPCODE_X0) | FNOP_X1

#define MUL_HU_HU_X0                                                           \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
    create_RRROpcodeExtension_X0(MUL_HU_HU_RRR_0_OPCODE_X0) | FNOP_X1

#define MUL_HU_LU_X0                                                           \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
    create_RRROpcodeExtension_X0(MUL_HU_LU_RRR_0_OPCODE_X0) | FNOP_X1

#define MULA_HU_LU_X0                                                           \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
    create_RRROpcodeExtension_X0(MULA_HU_LU_RRR_0_OPCODE_X0) | FNOP_X1

#define FSINGLE_PACK1_X0                                                       \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
      create_RRROpcodeExtension_X0(UNARY_RRR_0_OPCODE_X0) |                    \
      create_UnaryOpcodeExtension_X0(FSINGLE_PACK1_UNARY_OPCODE_X0) | FNOP_X1

#define FSINGLE_PACK2_X0                                                       \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
      create_RRROpcodeExtension_X0(FSINGLE_PACK2_RRR_0_OPCODE_X0) | FNOP_X1

#define FDOUBLE_PACK1_X0                                                       \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
      create_RRROpcodeExtension_X0(FDOUBLE_PACK1_RRR_0_OPCODE_X0) | FNOP_X1

#define FDOUBLE_PACK2_X0                                                       \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
      create_RRROpcodeExtension_X0(FDOUBLE_PACK2_RRR_0_OPCODE_X0) | FNOP_X1

#define FDOUBLE_ADD_FLAGS_X0                                                   \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
      create_RRROpcodeExtension_X0(FDOUBLE_ADD_FLAGS_RRR_0_OPCODE_X0) | FNOP_X1

#define FDOUBLE_ADDSUB_X0                                                      \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
    create_RRROpcodeExtension_X0(FDOUBLE_ADDSUB_RRR_0_OPCODE_X0) | FNOP_X1

#define FDOUBLE_MUL_FLAGS_X0                                                   \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
    create_RRROpcodeExtension_X0(FDOUBLE_MUL_FLAGS_RRR_0_OPCODE_X0) | FNOP_X1

#define FDOUBLE_SUB_FLAGS_X0                                                   \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
    create_RRROpcodeExtension_X0(FDOUBLE_SUB_FLAGS_RRR_0_OPCODE_X0) | FNOP_X1

#define FDOUBLE_UNPACK_MAX_X0                                                  \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
    create_RRROpcodeExtension_X0(FDOUBLE_UNPACK_MAX_RRR_0_OPCODE_X0) | FNOP_X1

#define FDOUBLE_UNPACK_MIN_X0                                                  \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
    create_RRROpcodeExtension_X0(FDOUBLE_UNPACK_MIN_RRR_0_OPCODE_X0) | FNOP_X1

#define ADD_X1                                                                 \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(ADD_RRR_0_OPCODE_X1) | FNOP_X0

#define ADDX_X1							               \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |	       \
    create_RRROpcodeExtension_X1(ADDX_RRR_0_OPCODE_X1) | FNOP_X0

#define SUB_X1                                                                 \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(SUB_RRR_0_OPCODE_X1) | FNOP_X0

#define SUBX_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(SUBX_RRR_0_OPCODE_X1) | FNOP_X0

#define MULX_X0                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
      create_RRROpcodeExtension_X0(MULX_RRR_0_OPCODE_X0) | FNOP_X1

#define NOR_X1                                                                 \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(NOR_RRR_0_OPCODE_X1) | FNOP_X0

#define OR_X1                                                                  \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(OR_RRR_0_OPCODE_X1) | FNOP_X0

#define AND_X1                                                                 \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(AND_RRR_0_OPCODE_X1) | FNOP_X0

#define XOR_X1                                                                 \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(XOR_RRR_0_OPCODE_X1) | FNOP_X0

#define CMOVNEZ_X0                                                             \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
      create_RRROpcodeExtension_X0(CMOVNEZ_RRR_0_OPCODE_X0) | FNOP_X1

#define CMOVEQZ_X0                                                             \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
      create_RRROpcodeExtension_X0(CMOVEQZ_RRR_0_OPCODE_X0) | FNOP_X1

#define CMPEXCH_X1                                                             \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
    create_RRROpcodeExtension_X1(CMPEXCH_RRR_0_OPCODE_X1) | FNOP_X0

#define MTSPR_X1                                                               \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(IMM8_OPCODE_X1) |              \
    create_Imm8OpcodeExtension_X1(MTSPR_IMM8_OPCODE_X1) | FNOP_X0

#define ADDLI_X1                                                               \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(ADDLI_OPCODE_X1) | FNOP_X0

#define MOVELI_X1                                                              \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(ADDLI_OPCODE_X1) |             \
	create_SrcA_X1(0x3F) | FNOP_X0

#define ADDXLI_X1                                                              \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(ADDXLI_OPCODE_X1) | FNOP_X0

#define ADDI_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(IMM8_OPCODE_X1) |              \
      create_Imm8OpcodeExtension_X1(ADDI_IMM8_OPCODE_X1) | FNOP_X0

#define ADDXI_X1                                                               \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(IMM8_OPCODE_X1) |              \
      create_Imm8OpcodeExtension_X1(ADDXI_IMM8_OPCODE_X1) | FNOP_X0

#define V4INT_L_X1                                                             \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(V4INT_L_RRR_0_OPCODE_X1) | FNOP_X0

#define BFINS_X0                                                               \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(BF_OPCODE_X0) |                \
      create_BFOpcodeExtension_X0(BFINS_BF_OPCODE_X0) | FNOP_X1

#define BFEXTU_X0                                                              \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(BF_OPCODE_X0) |                \
      create_BFOpcodeExtension_X0(BFEXTU_BF_OPCODE_X0) | FNOP_X1

#define BFEXTS_X0                                                              \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(BF_OPCODE_X0) |                \
      create_BFOpcodeExtension_X0(BFEXTS_BF_OPCODE_X0) | FNOP_X1

#define SHL1ADD_X1                                                             \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
    create_RRROpcodeExtension_X1(SHL1ADD_RRR_0_OPCODE_X1) | FNOP_X0

#define SHL3ADD_X1                                                             \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
    create_RRROpcodeExtension_X1(SHL3ADD_RRR_0_OPCODE_X1) | FNOP_X0

#define SHL16INSLI_X1                                                          \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(SHL16INSLI_OPCODE_X1) | FNOP_X0

#define INFOL_X1                                                               \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(SHL16INSLI_OPCODE_X1) |        \
      SRCA_X1(0x3F) | DEST_X1(0x3F) | FNOP_X0

#define LNK_X1                                                                 \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(UNARY_RRR_0_OPCODE_X1) |                    \
      create_UnaryOpcodeExtension_X1(LNK_UNARY_OPCODE_X1) | FNOP_X0

#define ST_X1                                                                  \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(ST_RRR_0_OPCODE_X1) | create_Dest_X1(0x0) | \
      FNOP_X0

#define ST1_X1                                                                 \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(ST1_RRR_0_OPCODE_X1) | create_Dest_X1(0x0) | \
      FNOP_X0

#define ST2_X1                                                                 \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(ST2_RRR_0_OPCODE_X1) | create_Dest_X1(0x0) | \
      FNOP_X0

#define ST4_X1                                                                 \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(ST4_RRR_0_OPCODE_X1) | create_Dest_X1(0x0) | \
      FNOP_X0

#define LD_X1                                                                  \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(UNARY_RRR_0_OPCODE_X1) |                    \
      create_UnaryOpcodeExtension_X1(LD_UNARY_OPCODE_X1) | FNOP_X0

#define LD1S_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(UNARY_RRR_0_OPCODE_X1) |                    \
      create_UnaryOpcodeExtension_X1(LD1S_UNARY_OPCODE_X1) | FNOP_X0

#define LD1U_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(UNARY_RRR_0_OPCODE_X1) |                    \
      create_UnaryOpcodeExtension_X1(LD1U_UNARY_OPCODE_X1) | FNOP_X0

#define LD2S_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(UNARY_RRR_0_OPCODE_X1) |                    \
      create_UnaryOpcodeExtension_X1(LD2S_UNARY_OPCODE_X1) | FNOP_X0


#define LD2U_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(UNARY_RRR_0_OPCODE_X1) |                    \
      create_UnaryOpcodeExtension_X1(LD2U_UNARY_OPCODE_X1) | FNOP_X0

#define LD4S_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(UNARY_RRR_0_OPCODE_X1) |                    \
      create_UnaryOpcodeExtension_X1(LD4S_UNARY_OPCODE_X1) | FNOP_X0

#define LD4U_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(UNARY_RRR_0_OPCODE_X1) |                    \
      create_UnaryOpcodeExtension_X1(LD4U_UNARY_OPCODE_X1) | FNOP_X0

#define JR_X1                                                                  \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(UNARY_RRR_0_OPCODE_X1) |                    \
      create_UnaryOpcodeExtension_X1(JR_UNARY_OPCODE_X1) | FNOP_X0

#define JALR_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(UNARY_RRR_0_OPCODE_X1) |                    \
      create_UnaryOpcodeExtension_X1(JALR_UNARY_OPCODE_X1) | FNOP_X0

#define CLZ_X0                                                                 \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X0(RRR_0_OPCODE_X0) |             \
      create_RRROpcodeExtension_X0(UNARY_RRR_0_OPCODE_X0) |                    \
      create_UnaryOpcodeExtension_X0(CNTLZ_UNARY_OPCODE_X0) | FNOP_X1

#define CMPEQ_X1                                                               \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(CMPEQ_RRR_0_OPCODE_X1) |                    \
      FNOP_X0

#define CMPNE_X1                                                               \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(CMPNE_RRR_0_OPCODE_X1) |                    \
      FNOP_X0

#define CMPLTS_X1                                                              \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(CMPLTS_RRR_0_OPCODE_X1) |                   \
      FNOP_X0

#define CMPLES_X1                                                              \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(CMPLES_RRR_0_OPCODE_X1) |                   \
      FNOP_X0

#define CMPLTU_X1                                                              \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(CMPLTU_RRR_0_OPCODE_X1) |                   \
      FNOP_X0

#define CMPLEU_X1                                                              \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(CMPLEU_RRR_0_OPCODE_X1) |                   \
      FNOP_X0

#define CMPLTSI_X1                                                             \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(IMM8_OPCODE_X1) |              \
      create_Imm8OpcodeExtension_X1(CMPLTSI_IMM8_OPCODE_X1) |                  \
      FNOP_X0

#define CMPLTUI_X1                                                             \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(IMM8_OPCODE_X1) |              \
      create_Imm8OpcodeExtension_X1(CMPLTUI_IMM8_OPCODE_X1) |                  \
      FNOP_X0

#define XORI_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(IMM8_OPCODE_X1) |              \
      create_Imm8OpcodeExtension_X1(XORI_IMM8_OPCODE_X1) |                     \
      FNOP_X0

#define ORI_X1                                                                 \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(IMM8_OPCODE_X1) |              \
      create_Imm8OpcodeExtension_X1(ORI_IMM8_OPCODE_X1) |                      \
      FNOP_X0

#define ANDI_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(IMM8_OPCODE_X1) |              \
      create_Imm8OpcodeExtension_X1(ANDI_IMM8_OPCODE_X1) |                     \
      FNOP_X0

#define SHLI_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(SHIFT_OPCODE_X1) |             \
      create_ShiftOpcodeExtension_X1(SHLI_SHIFT_OPCODE_X1) | FNOP_X0

#define SHL_X1                                                                 \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(SHL_RRR_0_OPCODE_X1) | FNOP_X0

#define SHLXI_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(SHIFT_OPCODE_X1) |             \
      create_ShiftOpcodeExtension_X1(SHLXI_SHIFT_OPCODE_X1) | FNOP_X0

#define SHLX_X1                                                                 \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(SHLX_RRR_0_OPCODE_X1) | FNOP_X0

#define SHRSI_X1                                                               \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(SHIFT_OPCODE_X1) |             \
      create_ShiftOpcodeExtension_X1(SHRSI_SHIFT_OPCODE_X1) | FNOP_X0

#define SHRS_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(SHRS_RRR_0_OPCODE_X1) | FNOP_X0

#define SHRUI_X1                                                               \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(SHIFT_OPCODE_X1) |             \
      create_ShiftOpcodeExtension_X1(SHRUI_SHIFT_OPCODE_X1) | FNOP_X0

#define SHRU_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(SHRU_RRR_0_OPCODE_X1) | FNOP_X0

#define SHRUXI_X1                                                               \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(SHIFT_OPCODE_X1) |             \
      create_ShiftOpcodeExtension_X1(SHRUXI_SHIFT_OPCODE_X1) | FNOP_X0

#define SHRUX_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(SHRUX_RRR_0_OPCODE_X1) | FNOP_X0

#define ROTL_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
    create_RRROpcodeExtension_X1(ROTL_RRR_0_OPCODE_X1) | FNOP_X0

#define BEQZ_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(BRANCH_OPCODE_X1) |            \
      create_BrType_X1(BEQZ_BRANCH_OPCODE_X1) | FNOP_X0

#define BNEZ_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(BRANCH_OPCODE_X1) |            \
      create_BrType_X1(BNEZ_BRANCH_OPCODE_X1) | FNOP_X0

#define BGTZ_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(BRANCH_OPCODE_X1) |            \
      create_BrType_X1(BGTZ_BRANCH_OPCODE_X1) | FNOP_X0

#define BGEZ_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(BRANCH_OPCODE_X1) |            \
      create_BrType_X1(BGEZ_BRANCH_OPCODE_X1) | FNOP_X0

#define BLTZ_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(BRANCH_OPCODE_X1) |            \
      create_BrType_X1(BLTZ_BRANCH_OPCODE_X1) | FNOP_X0

#define BLEZ_X1                                                                \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(BRANCH_OPCODE_X1) |            \
      create_BrType_X1(BLEZ_BRANCH_OPCODE_X1) | FNOP_X0

#define J_X1                                                                   \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(JUMP_OPCODE_X1) |              \
      create_JumpOpcodeExtension_X1(J_JUMP_OPCODE_X1) | FNOP_X0

#define JAL_X1                                                                 \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(JUMP_OPCODE_X1) |              \
      create_JumpOpcodeExtension_X1(JAL_JUMP_OPCODE_X1) | FNOP_X0

#define BPT_X1                                                                 \
  create_Mode(TILEGX_X_MODE) | create_Opcode_X1(RRR_0_OPCODE_X1) |             \
      create_RRROpcodeExtension_X1(UNARY_RRR_0_OPCODE_X1) |                    \
      create_UnaryOpcodeExtension_X1(ILL_UNARY_OPCODE_X1) |                    \
      create_Dest_X1(0x1C) | create_SrcA_X1(0x25) | ANOP_X0

#define DEST_X0(x) create_Dest_X0(x)
#define SRCA_X0(x) create_SrcA_X0(x)
#define SRCB_X0(x) create_SrcB_X0(x)
#define DEST_X1(x) create_Dest_X1(x)
#define SRCA_X1(x) create_SrcA_X1(x)
#define SRCB_X1(x) create_SrcB_X1(x)
#define MT_IMM14_X1(x) create_MT_Imm14_X1(x)
#define IMM16_X1(x) create_Imm16_X1(x)
#define IMM8_X1(x) create_Imm8_X1(x)
#define BFSTART_X0(x) create_BFStart_X0(x)
#define BFEND_X0(x) create_BFEnd_X0(x)
#define SHIFTIMM_X1(x) create_ShAmt_X1(x)
#define JOFF_X1(x) create_JumpOff_X1(x)
#define BOFF_X1(x) create_BrOff_X1(x)

// TileGX has 64 64bit registers.
struct Register {
  static const int kNumRegisters = 64;
  // For Float Register
  static const int kMaxNumRegisters = 64;
  static const int kMaxNumAllocatableRegisters = 17;
  static const int kSizeInBytes = 8;

  inline static int NumAllocatableRegisters();

  static int ToAllocationIndex(Register reg) {
    ASSERT(kMaxNumAllocatableRegisters == 17); // If not, fix the table below!    
    const int unused = -1;
    const int alloc_top = 11;
    const int code_to_index[] = {
      alloc_top + 5,    // 0       (a0/v0)
      alloc_top + 4,    // 1       (a1)
      alloc_top + 3,    // 2       (a2)
      alloc_top + 2,    // 3       (a3)
      alloc_top + 1,    // 4       (a4) 
      alloc_top + 6,    // 5       (t0) 
      alloc_top + 7,    // 6       (t1) 
      alloc_top + 8,    // 7       (t2) 
      alloc_top + 9,    // 8       (t3) 
      alloc_top + 10,   // 9       (t4) 
      0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,     // 10 - 21 (the allocatable set)
      unused, unused, unused,                   // 22 - 24
      unused, unused, unused, unused, unused,   // 25 - 29
      unused, unused, unused, unused, unused,   // 30 - 34
      unused, unused, unused, unused, unused,   // 35 - 39                        
      alloc_top + 11,   // 40      (s1)                   
      alloc_top + 12,   // 41      (s2)                   
      alloc_top + 13,   // 42      (s3)                   
      alloc_top + 14,   // 43      (s4)                   
      alloc_top + 15,   // 44      (s5)                   
      unused, unused, unused, unused, unused,   // 45 - 49                        
      unused, unused, unused, unused, unused,   // 50 - 54                        
      unused, unused, unused, unused, unused,   // 55 - 59                        
      unused, unused, unused, unused};          // 60 - 63                        
    ASSERT(reg.code() < kNumRegisters);
    ASSERT(code_to_index[reg.code()] != -1);
    return code_to_index[reg.code()];
  }

  static Register FromAllocationIndex(int index) {
    ASSERT(kMaxNumAllocatableRegisters == 17); // If not, fix the table below!    
    const int index_to_code[] = {
      10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,  // the allocatable set
      4, 3, 2, 1, 0,            // a0, a1, a2, a3, a4
      5, 6, 7, 8, 9,            // t0, t1, t2, t3, t4
      40, 41, 42, 43, 44};      // 40, 41, 42, 43, 44 (temps)

    ASSERT((uint)index < (sizeof(index_to_code)/sizeof(int)));
    return from_code(index_to_code[index]);
  }

  static const char* AllocationIndexToString(int index) {
    const char* const names[] = {
      "r10", "r11", "r12", "r13", "r14",
      "r15", "r16", "r17", "r18", "r19", "r20", "r21",          // the allocatable set
      "r4", "r3", "r2", "r1", "r0",               // a4, a3, a2, a1, a0
      "r5", "r6", "r7", "r8", "r9",               // t0, t1, t2, t3, t4  
      "r40", "r41", "r42", "r43", "r44)"};        // 40, 41, 42, 43, 44  (s* temps)
    ASSERT((uint)index < (sizeof(names)/sizeof(char*)));
    return names[index];
  }

  static Register from_code(int code) {
    Register r = { code };
    return r;
  }

  bool is_valid() const { return 0 <= code_ && code_ < kNumRegisters; }
  bool is(Register reg) const { return code_ == reg.code_; }

  int code() const {
    ASSERT(is_valid());
    return code_;
  }

  uint64_t bit() const {
    ASSERT(is_valid());
    return 1L << code_;
  }

  void set_code(int code) {
    code_ = code;
    ASSERT(is_valid());
  }

  // Unfortunately we can't make this private in a struct.
  int code_;
};

#define REGISTER(N, C) \
  const int kRegister_ ## N ## _Code = C; \
  const Register N = { C }

REGISTER(r0, 0);
REGISTER(r1, 1);
REGISTER(r2, 2);
REGISTER(r3, 3);
REGISTER(r4, 4);
REGISTER(r5, 5);
REGISTER(r6, 6);
REGISTER(r7, 7);
REGISTER(r8, 8);
REGISTER(r9, 9);
REGISTER(r10, 10);
REGISTER(r11, 11);
REGISTER(r12, 12);
REGISTER(r13, 13);
REGISTER(r14, 14);
REGISTER(r15, 15);
REGISTER(r16, 16);
REGISTER(r17, 17);
REGISTER(r18, 18);
REGISTER(r19, 19);
REGISTER(r20, 20);
REGISTER(r21, 21);
REGISTER(r22, 22);
REGISTER(r23, 23);
REGISTER(r24, 24);
REGISTER(r25, 25);
REGISTER(r26, 26);
REGISTER(r27, 27);
REGISTER(r28, 28);
REGISTER(r29, 29);
REGISTER(r30, 30);
REGISTER(r31, 31);
REGISTER(r32, 32);
REGISTER(r33, 33);
REGISTER(r34, 34);
REGISTER(r35, 35);
REGISTER(r36, 36);
REGISTER(r37, 37);
REGISTER(r38, 38);
REGISTER(r39, 39);
REGISTER(r40, 40);
REGISTER(r41, 41);
REGISTER(r42, 42);
REGISTER(r43, 43);
REGISTER(r44, 44);
REGISTER(r45, 45);
REGISTER(r46, 46);
REGISTER(r47, 47);
REGISTER(r48, 48);
REGISTER(r49, 49);
REGISTER(r50, 50);
REGISTER(r51, 51);
REGISTER(r52, 52);
REGISTER(r53, 53);
REGISTER(r54, 54);
REGISTER(r55, 55);
REGISTER(r56, 56);
REGISTER(r57, 57);
REGISTER(r58, 58);
REGISTER(r59, 59);
REGISTER(r60, 60);
REGISTER(r61, 61);
REGISTER(r62, 62);
REGISTER(r63, 63);

#undef REGISTER

struct DoubleRegister {
  static const int kNumRegisters = 64;
  // For Float Register                                                                              
  static const int kMaxNumRegisters = 64;
  static const int kMaxNumAllocatableRegisters = 17;
  static const int kSizeInBytes = 8;
  
  inline static int NumAllocatableRegisters();

  static int ToAllocationIndex(DoubleRegister reg) {
    ASSERT(kMaxNumAllocatableRegisters == 17); // If not, fix the table below!                       
    const int unused = -1;
    const int alloc_top = 11;
    const int code_to_index[] = {
      alloc_top + 5,    // 0       (a0/v0)
      alloc_top + 4,    // 1       (a1)
      alloc_top + 3,    // 2       (a2)
      alloc_top + 2,    // 3       (a3)
      alloc_top + 1,    // 4       (a4)
      alloc_top + 6,    // 5       (t0)
      alloc_top + 7,    // 6       (t1)
      alloc_top + 8,    // 7       (t2)
      alloc_top + 9,    // 8       (t3)
      alloc_top + 10,   // 9       (t4)
      unused, unused, unused, unused, unused,   // 10 - 14
      unused, unused, unused, unused,           // 15 - 18
      unused, unused, unused, unused, unused,   // 19 - 23
      unused, unused, unused, unused,           // 24 - 27
      unused, unused,                           // 28 - 29
      0, 1, 2, 3, 4, 5, 6, 7, 8,                // 30 - 37 (the allocatable set)    
      unused, unused,   // 38 - 39
      alloc_top + 11,   // 40      (s1)
      alloc_top + 12,   // 41      (s2)
      alloc_top + 13,   // 42      (s3)
      alloc_top + 14,   // 43      (s4)
      alloc_top + 15,   // 44      (s5)
      unused, unused,                           // 45 - 46
      9, 10, 11,                                // 47 - 49 (allocatable)
      unused, unused, unused, unused, unused,   // 50 - 54
      unused, unused, unused, unused, unused,   // 55 - 59
      unused, unused, unused, unused};          // 60 - 63
    ASSERT(reg.code() < kNumRegisters);
    ASSERT(code_to_index[reg.code()] != -1);
    return code_to_index[reg.code()];
  }

  static DoubleRegister FromAllocationIndex(int index) {
    ASSERT(kMaxNumAllocatableRegisters == 17); // If not, fix the table below!
    const int index_to_code[] = {
      30, 31, 32, 33, 34, 35, 36, 37, 38, 47, 48, 49,   // the allocatable set
      4, 3, 2, 1, 0,            // a0, a1, a2, a3, a4
      5, 6, 7, 8, 9,            // t0, t1, t2, t3, t4
      40, 41, 42, 43, 44};      // 40, 41, 42, 43, 44 (temps)

    ASSERT((uint)index < (sizeof(index_to_code)/sizeof(int)));
    return from_code(index_to_code[index]);
  }

  static const char* AllocationIndexToString(int index) {
    const char* const names[] = {
      "r30", "r31", "r32", "r33", "r34", "r35", "r36", "r37", "r38", "r47", "r48", "r49",
      "r4", "r3", "r2", "r1", "r0",               // a0, a1, a2, a3, a4
      "r5", "r6", "r7", "r8", "r9",               // t0, t1, t2, t3, t4
      "r40", "r41", "r42", "r43", "r44)"};        // 40, 41, 42, 43, 44  (s* temps)
    ASSERT((uint)index < (sizeof(names)/sizeof(char*)));
    return names[index];
  }

  
  static DoubleRegister from_code(int code) {
    DoubleRegister r = { code };
    return r;
  }
  
  bool is_valid() const { return 0 <= code_ && code_ < kNumRegisters; }
  bool is(DoubleRegister reg) const { return code_ == reg.code_; }
  
  int code() const {
    ASSERT(is_valid());
    return code_;
  }
  
  uint64_t bit() const {
    ASSERT(is_valid());
    return 1L << code_;
  }
  
  void set_code(int code) {
    code_ = code;
    ASSERT(is_valid());
  }
  
  // Unfortunately we can't make this private in a struct.
  int code_;
};


const int kRegister_a0_Code = 0;
const int kRegister_a1_Code = 1;
const int kRegister_a2_Code = 2;
const int kRegister_a3_Code = 3;
const int kRegister_a4_Code = 4;

const int kRegister_t0_Code = 5 /*5*/;
const int kRegister_t1_Code = 6 /*6*/;
const int kRegister_t2_Code = 7 /*7*/;
const int kRegister_t3_Code = 8 /*8*/;
const int kRegister_t4_Code = 9 /*9*/;
const int kRegister_t5_Code = 23 /*23*/;
const int kRegister_t6_Code = 24 /*24*/;
const int kRegister_t7_Code = 25 /*25*/;

const int kRegister_t8_Code = 26 /*26*/;
const int kRegister_t9_Code = 27 /*27*/;

const int kRegister_s0_Code = 39;
const int kRegister_s1_Code = 40;
const int kRegister_s2_Code = 41;
const int kRegister_s3_Code = 42;
const int kRegister_s4_Code = 43;
const int kRegister_s5_Code = 44;
const int kRegister_s6_Code = 45;
const int kRegister_s7_Code = 46;

const int kRegister_at_Code = 28;
const int kRegister_at2_Code = 29;

const int kRegister_pc_Code = 50;
const int kRegister_gp_Code = 51;
const int kRegister_fp_Code = 52;
const int kRegister_tp_Code = 53;
const int kRegister_sp_Code = 54;
const int kRegister_lr_Code = 55;
const int kRegister_zero_Code = 63;
const int kRegister_no_reg_Code = -1;

const Register v0  = { kRegister_a0_Code };
const Register a0  = { kRegister_a0_Code };
const Register v1  = { kRegister_a1_Code };
const Register a1  = { kRegister_a1_Code };
const Register a2  = { kRegister_a2_Code };
const Register a3  = { kRegister_a3_Code };
const Register a4  = { kRegister_a4_Code };
const DoubleRegister v0_as_double  = { kRegister_a0_Code };
const DoubleRegister a0_as_double  = { kRegister_a0_Code };
const DoubleRegister a1_as_double  = { kRegister_a1_Code };
const DoubleRegister a2_as_double  = { kRegister_a2_Code };
const DoubleRegister a3_as_double  = { kRegister_a3_Code };
const DoubleRegister a4_as_double  = { kRegister_a4_Code };

const Register t0  = { kRegister_t0_Code };
const Register t1  = { kRegister_t1_Code };
const Register t2  = { kRegister_t2_Code };
const Register t3  = { kRegister_t3_Code };
const Register t4  = { kRegister_t4_Code };
const Register t5  = { kRegister_t5_Code };
const Register t6  = { kRegister_t6_Code };
const Register t7  = { kRegister_t7_Code };
const Register t8  = { kRegister_t8_Code };
const Register t9  = { kRegister_t9_Code };
// 'tt' is treated as TileGX temp register,
// like 'at' in MIPS.
const Register s0  = { kRegister_s0_Code };
const Register s1  = { kRegister_s1_Code };
const Register s2  = { kRegister_s2_Code };
const Register s3  = { kRegister_s3_Code };
const Register s4  = { kRegister_s4_Code };
const Register s5  = { kRegister_s5_Code };
const Register s6  = { kRegister_s6_Code };
const Register s7  = { kRegister_s7_Code };
const DoubleRegister s2_as_double  = { kRegister_s2_Code };
const DoubleRegister s3_as_double  = { kRegister_s3_Code };
const DoubleRegister s4_as_double  = { kRegister_s4_Code };
const DoubleRegister s5_as_double  = { kRegister_s5_Code };

const Register at  = { kRegister_at_Code };
const Register at2  = { kRegister_at2_Code };
const Register pc  = { kRegister_pc_Code };
const Register gp  = { kRegister_gp_Code };
const Register fp  = { kRegister_fp_Code };
const Register tp  = { kRegister_tp_Code };
const Register sp  = { kRegister_sp_Code };
const Register ra  = { kRegister_lr_Code };
const Register lr  = { kRegister_lr_Code };
const Register zero = { kRegister_zero_Code };
const DoubleRegister zero_as_double = { kRegister_zero_Code };
const Register no_reg = { kRegister_no_reg_Code };

// Register aliases.
// cp is assumed to be a callee saved register.
// Defined using #define instead of "static const Register&" because Clang
// complains otherwise when a compilation unit that includes this header
// doesn't use the variables.
#define kRootRegister s6
#define cp s7
#define kLithiumScratchReg s3
#define kLithiumScratchReg2 s4
#define kLithiumScratchReg3 s5
#define kLithiumScratchReg4 s2
#define kLithiumScratchRegD s3_as_double
#define kLithiumScratchRegD2 s4_as_double
#define kLithiumScratchRegD3 s5_as_double
#define kLithiumScratchRegD4 s2_as_double

int ToNumber(Register reg);

Register ToRegister(int num);

// Class Operand represents a shifter operand in data processing instructions.
class Operand BASE_EMBEDDED {
 public:

  // Immediate.
  INLINE(explicit Operand(int64_t immediate,
         RelocInfo::Mode rmode = RelocInfo::NONE64));
  INLINE(explicit Operand(const ExternalReference& f));
  INLINE(explicit Operand(const char* s));
  INLINE(explicit Operand(Object** opp));
  INLINE(explicit Operand(Context** cpp));
  explicit Operand(Handle<Object> handle);
  INLINE(explicit Operand(Smi* value));

  // Register.
  INLINE(explicit Operand(Register rm));

  // Return true if this is a register operand.
  INLINE(bool is_reg() const);

  Register rm() const { return rm_; }

 private:
  Register rm_;
  int64_t imm64_;  // Valid if rm_ == no_reg.
  RelocInfo::Mode rmode_;

  friend class Assembler;
  friend class MacroAssembler;
};


class MemOperand : public Operand {
 public:
  explicit MemOperand(Register rn, int64_t offset = 0);
  int32_t offset() const { return offset_; }

 private:
  int64_t offset_;

  friend class Assembler;
};

class Assembler : public AssemblerBase {
 public:
  // Create an assembler. Instructions and relocation information are emitted
  // into a buffer, with the instructions starting from the beginning and the
  // relocation information starting from the end of the buffer. See CodeDesc
  // for a detailed comment on the layout (globals.h).
  //
  // If the provided buffer is NULL, the assembler allocates and grows its own
  // buffer, and buffer_size determines the initial buffer size. The buffer is
  // owned by the assembler and deallocated upon destruction of the assembler.
  //
  // If the provided buffer is not NULL, the assembler uses the provided buffer
  // for code generation and assumes its size to be buffer_size. If the buffer
  // is too small, a fatal error occurs. No deallocation of the buffer is done
  // upon destruction of the assembler.
  Assembler(Isolate* isolate, void* buffer, int buffer_size);
  virtual ~Assembler() { }

  // Different nop operations are used by the code generator to detect certain
  // states of the generated code.
  enum NopMarkerTypes {
    NON_MARKING_NOP = 0,
    DEBUG_BREAK_NOP,
    // IC markers.
    PROPERTY_ACCESS_INLINED,
    PROPERTY_ACCESS_INLINED_CONTEXT,
    PROPERTY_ACCESS_INLINED_CONTEXT_DONT_DELETE,
    // Helper values.
    LAST_CODE_MARKER,
    FIRST_IC_MARKER = PROPERTY_ACCESS_INLINED,
    // Code aging
    CODE_AGE_MARKER_NOP = 6,
    INTERRUPT_PATCH_NOP = 7
  };

  // Insert the smallest number of nop instructions
  // possible to align the pc offset to a multiple
  // of m. m must be a power of 2 (>= 8).
  void Align(int m);

  // Record the AST id of the CallIC being compiled, so that it can be placed
  // in the relocation information.
  void SetRecordedAstId(TypeFeedbackId ast_id) {
    ASSERT(recorded_ast_id_.IsNone());
    recorded_ast_id_ = ast_id;
  }

  TypeFeedbackId RecordedAstId() {
    ASSERT(!recorded_ast_id_.IsNone());
    return recorded_ast_id_;
  }

  void ClearRecordedAstId() { recorded_ast_id_ = TypeFeedbackId::None(); }

  void RecordJSReturn();
  void RecordDebugBreakSlot();
  // Record a comment relocation entry that can be used by a disassembler.
  // Use --code-comments to enable.
  void RecordComment(const char* msg);
  static int RelocateInternalReference(byte* pc, intptr_t pc_delta);

  // Writes a single byte or word of data in the code stream.  Used for
  // inline tables, e.g., jump-tables.
  void db(uint8_t data);
  void dd(uint32_t data);
  void dq(uint64_t data);

  // GetCode emits any pending (non-emitted) code and fills the descriptor
  // desc. GetCode() is idempotent; it returns the same result if no other
  // Assembler functions are invoked in between GetCode() calls.
  void GetCode(CodeDesc* desc);

  void bind(Label* L);  // Binds an unbound label L to current code position.
  void bind_to(Label* L, int pos);
  void next(Label* L);
  void print(Label* L);

  // Returns the branch offset to the given label from the current code
  // position. Links the label to the current position if it is still unbound.
  // Manages the jump elimination optimization if the second parameter is true.
  int32_t branch_offset(Label* L, bool is_long = false);
  int32_t shifted_branch_offset(Label* L, bool is_long = false) {
    int32_t o = branch_offset(L, is_long);
    ASSERT((o & 7) == 0);   // Assert the offset is aligned.
    return o >> 3;
  }

  uint64_t jump_address(Label* L);

  static const int kInstrSize = sizeof(Instr);

  static Instr instr_at(byte* pc) { return *reinterpret_cast<Instr*>(pc); }
  static void instr_at_put(byte* pc, Instr instr) {
    *reinterpret_cast<Instr*>(pc) = instr;
  }
  Instr instr_at(int pos) { return *reinterpret_cast<Instr*>(buffer_ + pos); }
  void instr_at_put(int pos, Instr instr, bool flush = true) {
    Instr* pc= reinterpret_cast<Instr*>(buffer_ + pos);
    *pc = instr;
  }

  static bool IsBranch(Instr instr);
  static bool IsJ(Instr instr);
  static bool IsJR(Instr instr);
  static bool IsJAL(Instr instr);
  static bool IsJALR(Instr instr);
  static bool IsMOVELI(Instr instr);
  static bool IsANDI(Instr instr);
  static bool IsSHL(Instr instr);
  static bool IsSHL16INSLI(Instr instr);
  static bool IsBeqz(Instr instr);
  static bool IsBnez(Instr instr);

  static uint32_t GetLabelConst(Instr instr);
  static bool IsEmittedConstant(Instr instr);

  // Return the code target address at a call site from the return address
  // of that call in the instruction stream.
  inline static Address target_address_from_return_address(Address pc);

  // Read/Modify the code target address in the branch/call instruction at pc.
  static Address target_address_at(Address pc);
  static void set_target_address_at(Address pc, Address target);

  static void JumpLabelToJumpRegister(Address pc);

  // Here we are patching the address in the LUI/ORI instruction pair.
  // These values are used in the serialization process and must be zero for
  // MIPS platform, as Code, Embedded Object or External-reference pointers
  // are split across two consecutive instructions and don't exist separately
  // in the code, so the serializer should not step forwards in memory after
  // a target is resolved and written.
  static const int kSpecialTargetSize = 0;

  // Number of consecutive instructions used to store 32bit constant.
  // Before jump-optimizations, this constant was used in
  // RelocInfo::target_address_address() function to tell serializer address of
  // the instruction that follows LUI/ORI instruction pair. Now, with new jump
  // optimization, where jump-through-register instruction that usually
  // follows LUI/ORI pair is substituted with J/JAL, this constant equals
  // to 3 instructions (LUI+ORI+J/JAL/JR/JALR).
  static const int kInstructionsFor32BitConstant = 3;

  // Distance between the instruction referring to the address of the call
  // target and the return address.
  static const int kCallTargetAddressOffset = 4 * kInstrSize;

  // This sets the branch destination (which gets loaded at the call address).
  // This is for calls and branches within generated code.  The serializer
  // has already deserialized the lui/ori instructions etc.
  inline static void deserialization_set_special_target_at(
      Address instruction_payload, Address target) {
    set_target_address_at(
        instruction_payload - kInstructionsFor32BitConstant * kInstrSize,
        target);
  }

  PositionsRecorder* positions_recorder() { return &positions_recorder_; }

  inline bool overflow() const { return pc_ >= reloc_info_writer.pos() - kGap; }

  static const int kMaxRelocSize = RelocInfoWriter::kMaxSize;
  RelocInfoWriter reloc_info_writer;

  static const int kPatchReturnSequenceAddressOffset = 0;

  // Distance between start of patched debug break slot and the emitted address
  // to jump to.
  static const int kPatchDebugBreakSlotAddressOffset =  0 * kInstrSize;

  // Difference between address of current opcode and value read from pc
  // register.
  static const int kPcLoadDelta = 4;

  static const int kPatchDebugBreakSlotReturnOffset = 4 * kInstrSize;

  // Number of instructions used for the JS return sequence. The constant is
  // used by the debugger to patch the JS return sequence.
  static const int kJSReturnSequenceInstructions = 7;
  static const int kDebugBreakSlotInstructions = 4;
  static const int kDebugBreakSlotLength =
      kDebugBreakSlotInstructions * kInstrSize;

  // ---------------------------------------------------------------------------
  // Instruction Encoding
  
  void nop(unsigned int type = 0, int line = 0) {
    ASSERT(type < 32);
    Register nop_rt_reg = (type == 0) ? zero : at;
    sll(zero, nop_rt_reg, type, line);
  }

  void j(int64_t target, int line = 0);
  void jal(int32_t offset, int line = 0);
  void jr(Register target, int line = 0);
  void jalr(Register target, int line = 0);

  void b(int32_t offset, int line = 0);
  void b(Label* L, int line = 0) { b(shifted_branch_offset(L), line); }
  void beqz(const Register& rs, int32_t offset, int line = 0);
  void beqz(const Register& rs, Label* L, int line = 0) {
    beqz(rs, shifted_branch_offset(L), line);
  }
  void bnez(const Register& rs, int32_t offset, int line = 0);
  void bnez(const Register& rs, Label* L, int line = 0) {
    bnez(rs, shifted_branch_offset(L), line);
  }
  void bgez(const Register& rs, int32_t offset, int line = 0);
  void bgtz(const Register& rs, int32_t offset, int line = 0);
  void blez(const Register& rs, int32_t offset, int line = 0);
  void bltz(const Register& rs, int32_t offset, int line = 0);

  void bfextu(const Register& rd, const Register& rs, int32_t offset1, int32_t offset2, int line = 0);
  void bfextu(const DoubleRegister& rd, const DoubleRegister& rs, 
	      int32_t offset1, int32_t offset2, int line = 0);
  void bfexts(const Register& rd, const Register& rs, int32_t offset1, int32_t offset2, int line = 0);
  void bfins(const Register& rd, const Register& rs, int32_t offset1, int32_t offset2, int line = 0);
  void bfins(const DoubleRegister& rd, const DoubleRegister& rs, int32_t offset1, 
	     int32_t offset2, int line = 0);

  void cmpeq(const Register& rd, const Register& rsa, const Register& rsb, int line = 0);
  void cmpne(const Register& rd, const Register& rsa, const Register& rsb, int line = 0);
  void cmplts(const Register& rd, const Register& rsa, const Register& rsb, int line = 0);
  void cmpltsi(const Register& rd, const Register& rsa, int8_t imm, int line = 0);
  Instr cmpltsi_b(const Register& rd, const Register& rsa, int8_t imm, int line = 0);
  void cmples(const Register& rd, const Register& rsa, const Register& rsb, int line = 0);
  void cmpltu(const Register& rd, const Register& rsa, const Register& rsb, int line = 0);
  void cmpltu(const DoubleRegister& rd, const DoubleRegister& rsa,
	      const DoubleRegister& rsb, int line = 0);
  void cmpltui(const Register& rd, const Register& rsa, int8_t imm, int line = 0);
  void cmpleu(const Register& rd, const Register& rsa, const Register& rsb, int line = 0);

  void cmpexch(const Register& rd, const Register& rsa, const Register& rsb, int line = 0);
  void mtspr(int16_t imm, const Register& rs, int line = 0);

  void bpt(int line = 0);
  void info(const int16_t imm16, int line = 0);
  void lnk(const Register& rd, int line = 0);
  void st(const Register& rd, const MemOperand& rs, int line = 0);
  void st(const Register& rd, const Register& rs, int line = 0);
  void st(const DoubleRegister& rd, const MemOperand& rs, int line = 0);
  void st(const DoubleRegister& rd, const Register& rs, int line = 0);
  void st1(const Register& rd, const MemOperand& rs, int line = 0);
  void st1(const Register& rd, const Register& rs, int line = 0);
  void st2(const Register& rd, const MemOperand& rs, int line = 0);
  void st2(const Register& rd, const Register& rs, int line = 0);
  void st4(const Register& rd, const MemOperand& rs, int line = 0);
  void st4(const Register& rd, const Register& rs, int line = 0);
  void ld(const Register& rd, const Register& rs, int line = 0);
  void ld(const Register& rd, const MemOperand& rs, int line = 0);
  void ld(const DoubleRegister& rd, const Register& rs, int line = 0);
  void ld(const DoubleRegister& rd, const MemOperand& rs, int line = 0);
  void ld1s(const Register& rd, const MemOperand& rs, int line = 0);
  void ld1s(const Register& rd, const Register& rs, int line = 0);
  void ld1u(const Register& rd, const MemOperand& rs, int line = 0);
  void ld1u(const Register& rd, const Register& rs, int line = 0);
  void ld2u(const Register& rd, const MemOperand& rs, int line = 0);
  void ld2u(const Register& rd, const Register& rs, int line = 0);
  void ld2s(const Register& rd, const MemOperand& rs, int line = 0);
  void ld2s(const Register& rd, const Register& rs, int line = 0);
  void ld4u(const Register& rd, const MemOperand& rs, int line = 0);
  void ld4u(const Register& rd, const Register& rs, int line = 0);
  void ld4s(const Register& rd, const MemOperand& rs, int line = 0);
  void ld4s(const DoubleRegister& rd, const MemOperand& rs, int line = 0);
  void ld4s(const Register& rd, const Register& rs, int line = 0);
  void ld4s(const DoubleRegister& rd, const Register& rs, int line = 0);
  void add(const Register& rd, const Register& rsa, const Register& rsb, int line = 0);
  void add(const DoubleRegister& rd, const DoubleRegister& rsa,
	   const DoubleRegister& rsb, int line = 0);
  void addx(const Register& rd, const Register& rsa, const Register& rsb, int line = 0);
  void sub(const Register& rd, const Register& rsa, const Register& rsb, int line = 0);
  void subx(const Register& rd, const Register& rsa, const Register& rsb, int line = 0);
  void mulx(const Register& rd, const Register& rsa, const Register& rsb, int line = 0);
  void addi(const Register& rd, const Register& rs, int8_t imm, int line = 0);
  void addi(const DoubleRegister& rd, const DoubleRegister& rs, int8_t imm, int line = 0);
  void addxi(const Register& rd, const Register& rs, int8_t imm, int line = 0);
  void addli(const Register& rd, const Register& rs, int16_t imm, int line = 0);
  void addxli(const Register& rd, const Register& rs, int16_t imm, int line = 0);
  void srl(const Register& rd, const Register& rs, int16_t imm, int line = 0);
  void srl(const DoubleRegister& rd, const DoubleRegister& rs, int16_t imm, int line = 0);
  void srl(const Register& rd, const Register& rs, const Register& rt, int line = 0);
  void sra(const Register& rd, const Register& rs, int16_t imm, int line = 0);
  void sra(const Register& rd, const Register& rs, const Register& rt, int line = 0);
  void sll(const Register& rd, const Register& rs, int16_t imm, int line = 0);
  void sll(const DoubleRegister& rd, const DoubleRegister& rs, int16_t imm, int line = 0);
  void sll(const Register& rd, const Register& rs, const Register& rt, int line = 0);

  void srlx(const Register& rd, const Register& rs, int16_t imm, int line = 0);
  void srlx(const Register& rd, const Register& rs, const Register& rt, int line = 0);
  void sllx(const Register& rd, const Register& rs, int16_t imm, int line = 0);
  void sllx(const Register& rd, const Register& rs, const Register& rt, int line = 0);

  void rotl(const Register& rd, const Register& rs, const Register& rt, int line = 0);

  void moveli(const Register& rd, int16_t imm, int line = 0);
  void shl1add(const Register& rd, const Register& rs, const Register& rt, int line = 0);
  void shl3add(const Register& rd, const Register& rs, const Register& rt, int line = 0);
  void shl16insli(const Register& rd, const Register& rs, int16_t imm, int line = 0);
  void move(const Register& rt, const Register& rs, int line = 0);
  void move(const DoubleRegister& rt, const DoubleRegister& rs, int line = 0);
  void moved2r(const Register& rt, const DoubleRegister& rs, int line = 0);
  void mover2d(const DoubleRegister& rt, const Register& rs, int line = 0);
  void and_(const Register& rd, const Register& rs, const Register& rt, int line = 0);
  void or_(const Register& rd, const Register& rs, const Register& rt, int line = 0);
  void nor(const Register& rd, const Register& rs, const Register& rt, int line = 0);
  void xor_(const Register& rd, const Register& rs, const Register& rt, int line = 0);
  void ori(const Register& rd, const Register& rs, int8_t imm8, int line = 0);
  void xori(const Register& rd, const Register& rs, int8_t imm8, int line = 0);
  void andi(const Register& rd, const Register& rs, int8_t imm8, int line = 0);
  void movn(const Register& rd, const Register& rs, const Register& rt, int line = 0);
  void movz(const Register& rd, const Register& rs, const Register& rt, int line = 0);
  void clz(const Register& rd, const Register& rs, int line = 0);
  void v4int_l(const Register& rd, const Register& rs, const Register& rt, int line = 0);

  void mul_hu_hu(const DoubleRegister& rd, const DoubleRegister& rs,
		 const DoubleRegister& rt, int line = 0);
  void mul_hu_lu(const DoubleRegister& rd, const DoubleRegister& rs,
		 const DoubleRegister& rt, int line = 0);
  void mula_hu_lu(const DoubleRegister& rd, const DoubleRegister& rs,
		  const DoubleRegister& rt, int line = 0);
  void mul_lu_lu(const DoubleRegister& rd, const DoubleRegister& rs,
		 const DoubleRegister& rt, int line = 0);
  void mul_ls_ls(const Register& rd, const Register& rs, const Register& rt, int line = 0);
  void mul_hs_ls(const Register& rd, const Register& rs, const Register& rt, int line = 0);
  void mul_hs_hs(const Register& rd, const Register& rs, const Register& rt, int line = 0);

  void fsingle_pack1(const Register& rd, const Register& rsa, int line = 0);
  void fsingle_pack2(const Register& rd, const Register& rsa, const Register& rsb, int line = 0);
  void fdouble_pack1(const DoubleRegister& rd, const DoubleRegister& rsa,
		     const DoubleRegister& rsb, int line = 0);
  void fdouble_pack2(const DoubleRegister& rd, const DoubleRegister& rsa, 
		     const DoubleRegister& rsb, int line = 0);
  void fdouble_add_flags(const DoubleRegister& rd, const DoubleRegister& rsa, 
			 const DoubleRegister& rsb, int line = 0);
  void fdouble_addsub(const DoubleRegister& rd, const DoubleRegister& rsa, 
		      const DoubleRegister& rsb, int line = 0);
  void fdouble_mul_flags(const DoubleRegister& rd, const DoubleRegister& rsa, 
			 const DoubleRegister& rsb, int line = 0);
  void fdouble_sub_flags(const DoubleRegister& rd, const DoubleRegister& rsa, 
			 const DoubleRegister& rsb, int line = 0);
  void fdouble_unpack_max(const DoubleRegister& rd, const DoubleRegister& rsa, 
			  const DoubleRegister& rsb, int line = 0);
  void fdouble_unpack_min(const DoubleRegister& rd, const DoubleRegister& rsa, 
			  const DoubleRegister& rsb, int line = 0);
  void fdouble_pack1(const Register& rd, const Register& rsa,
                     const Register& rsb, int line = 0);
  void fdouble_pack2(const Register& rd, const Register& rsa,
                     const Register& rsb, int line = 0);
  void fdouble_add_flags(const Register& rd, const Register& rsa,
                         const Register& rsb, int line = 0);
  void fdouble_add_flags(const Register& rd, const DoubleRegister& rsa,
                         const Register& rsb, int line = 0);
  void fdouble_addsub(const Register& rd, const Register& rsa,
                      const Register& rsb, int line = 0);
  void fdouble_mul_flags(const Register& rd, const Register& rsa,
                         const Register& rsb, int line = 0);
  void fdouble_sub_flags(const Register& rd, const Register& rsa,
                         const Register& rsb, int line = 0);
  void fdouble_unpack_max(const Register& rd, const Register& rsa,
                          const Register& rsb, int line = 0);
  void fdouble_unpack_min(const Register& rd, const Register& rsa,
                          const Register& rsb, int line = 0);
  void fdouble_unpack_max(const Register& rd, const DoubleRegister& rsa,
                          const Register& rsb, int line = 0);
  void fdouble_unpack_min(const Register& rd, const DoubleRegister& rsa,
                          const Register& rsb, int line = 0);
 
  void break_(uint32_t code, bool break_as_stop = false);
  void stop(const char* msg, uint32_t code = kMaxStopCode);

  // Check if an instruction is a branch of some kind.
  static bool IsNop(Instr instr, unsigned int type);

  bool is_near(Label* L);

  // Check the code size generated from label to here.
  int SizeOfCodeGeneratedSince(Label* label) {
    return pc_offset() - label->pos();
  }

  // Check the number of instructions generated from label to here.
  int InstructionsGeneratedSince(Label* label) {
    return SizeOfCodeGeneratedSince(label) / kInstrSize;
  }

  // Class for scoping postponing the trampoline pool generation.
  class BlockTrampolinePoolScope {
   public:
    explicit BlockTrampolinePoolScope(Assembler* assem) : assem_(assem) {
      assem_->StartBlockTrampolinePool();
    }
    ~BlockTrampolinePoolScope() {
      assem_->EndBlockTrampolinePool();
    }

   private:
    Assembler* assem_;

    DISALLOW_IMPLICIT_CONSTRUCTORS(BlockTrampolinePoolScope);
  };

  // Class for postponing the assembly buffer growth. Typically used for
  // sequences of instructions that must be emitted as a unit, before
  // buffer growth (and relocation) can occur.
  // This blocking scope is not nestable.
  class BlockGrowBufferScope {
   public:
    explicit BlockGrowBufferScope(Assembler* assem) : assem_(assem) {
      assem_->StartBlockGrowBuffer();
    }
    ~BlockGrowBufferScope() {
      assem_->EndBlockGrowBuffer();
    }

    private:
     Assembler* assem_;

     DISALLOW_IMPLICIT_CONSTRUCTORS(BlockGrowBufferScope);
  };

 protected:
  TypeFeedbackId recorded_ast_id_;

  void StartBlockTrampolinePool() {
    trampoline_pool_blocked_nesting_++;
  }

  void EndBlockTrampolinePool() {
    trampoline_pool_blocked_nesting_--;
  }

  bool is_trampoline_pool_blocked() const {
    return trampoline_pool_blocked_nesting_ > 0;
  }

  bool is_trampoline_emitted() const {
    return trampoline_emitted_;
  }

  // Temporarily block automatic assembly buffer growth.
  void StartBlockGrowBuffer() {
    ASSERT(!block_buffer_growth_);
    block_buffer_growth_ = true;
  }

  void EndBlockGrowBuffer() {
    ASSERT(block_buffer_growth_);
    block_buffer_growth_ = false;
  }

  // Record reloc info for current pc_.
  void RecordRelocInfo(RelocInfo::Mode rmode, intptr_t data = 0);

  int64_t buffer_space() const { return reloc_info_writer.pos() - pc_; }

  // Decode branch instruction at pos and return branch target pos.
  int target_at(int32_t pos);

  // Patch branch instruction at pos to branch to given branch target pos.
  void target_at_put(int32_t pos, int32_t target_pos);

  // Say if we need to relocate with this mode.
  bool MustUseReg(RelocInfo::Mode rmode);

 private:
  // Code generation
  // The relocation writer's position is at least kGap bytes below the end of
  // the generated instructions. This is so that multi-instruction sequences do
  // not have to check for overflow. The same is true for writes of large
  // relocation info entries.
  static const int kGap = 32;

  inline void CheckBuffer();
  void GrowBuffer();
  inline void emit(Instr x, int line = 0);

  PositionsRecorder positions_recorder_;

  int next_buffer_check_;  // pc offset of next buffer check.

  // Emission of the trampoline pool may be blocked in some code sequences.
  int trampoline_pool_blocked_nesting_;  // Block emission if this is not zero.
  int no_trampoline_pool_before_;  // Block emission before this pc offset.

  // Keep track of the last emitted pool to guarantee a maximal distance.
  int last_trampoline_pool_end_;  // pc offset of the end of the last pool.

  // Automatic growth of the assembly buffer may be blocked for some sequences.
  bool block_buffer_growth_;  // Block growth when true.

  // The bound position, before this we cannot do instruction elimination.
  int last_bound_pos_;

  // One trampoline consists of:
  // - space for trampoline slots,
  // - space for labels.
  //
  // Space for trampoline slots is equal to slot_count * 2 * kInstrSize.
  // Space for trampoline slots preceeds space for labels. Each label is of one
  // instruction size, so total amount for labels is equal to
  // label_count *  kInstrSize.
  class Trampoline {
   public:
    Trampoline() {
      start_ = 0;
      next_slot_ = 0;
      free_slot_count_ = 0;
      end_ = 0;
    }
    Trampoline(int start, int slot_count) {
      start_ = start;
      next_slot_ = start;
      free_slot_count_ = slot_count;
      end_ = start + slot_count * kTrampolineSlotsSize;
    }
    int start() {
      return start_;
    }
    int end() {
      return end_;
    }
    int take_slot() {
      int trampoline_slot = kInvalidSlotPos;
      if (free_slot_count_ <= 0) {
        // We have run out of space on trampolines.
        // Make sure we fail in debug mode, so we become aware of each case
        // when this happens.
        ASSERT(0);
        // Internal exception will be caught.
      } else {
        trampoline_slot = next_slot_;
        free_slot_count_--;
        next_slot_ += kTrampolineSlotsSize;
      }
      return trampoline_slot;
    }

   private:
    int start_;
    int end_;
    int next_slot_;
    int free_slot_count_;
  };

  int32_t get_trampoline_entry(int32_t pos);
  int unbound_labels_count_;
  // If trampoline is emitted, generated code is becoming large. As this is
  // already a slow case which can possibly break our code generation for the
  // extreme case, we use this information to trigger different mode of
  // branch instruction generation, where we use jump instructions rather
  // than regular branch instructions.
  bool trampoline_emitted_;
  static const int kTrampolineSlotsSize = 4 * kInstrSize;
  static const int kMaxBranchOffset = (1 << 18) - 1;
  static const int kInvalidSlotPos = -1;

  Trampoline trampoline_;
  bool internal_trampoline_exception_;


  friend class EnsureSpace;
  friend class CodePatcher;
  friend class PositionsRecorder;
};

class EnsureSpace BASE_EMBEDDED {
 public:
  explicit EnsureSpace(Assembler* assembler) {
    assembler->CheckBuffer();
  }
};

// CpuFeatures keeps track of which features are supported by the target CPU.
// Supported features must be enabled by a CpuFeatureScope before use.
class CpuFeatures : public AllStatic {
 public:
  // Detect features of the target CPU. Set safe defaults if the serializer
  // is enabled (snapshots must be portable).
  static void Probe();

  // Check whether a feature is supported by the target CPU.
  static bool IsSupported(CpuFeature f) {
    ASSERT(initialized_);
    return (supported_ & (1u << f)) != 0;
  }

  static bool IsFoundByRuntimeProbingOnly(CpuFeature f) {
    ASSERT(initialized_);
    return (found_by_runtime_probing_only_ &
            (static_cast<uint64_t>(1) << f)) != 0;
  }

  static bool IsSafeForSnapshot(CpuFeature f) {
    return (IsSupported(f) &&
            (!Serializer::enabled() || !IsFoundByRuntimeProbingOnly(f)));
  }

 private:
#ifdef DEBUG
  static bool initialized_;
#endif
  static unsigned supported_;
  static unsigned found_by_runtime_probing_only_;

  friend class ExternalReference;
  DISALLOW_COPY_AND_ASSIGN(CpuFeatures);
};


} }  // namespace v8::internal

#endif  // V8_TILEGX_ASSEMBLER_TILEGX_H_
