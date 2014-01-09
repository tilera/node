// Copyright 2011 the V8 project authors. All rights reserved.
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

#include "constants-tilegx.h"

namespace v8 {
namespace internal {


// -----------------------------------------------------------------------------
// Registers.


// These register names are defined in a way to match the native disassembler
// formatting. See for example the command "objdump -d <binary file>".
const char* Registers::names_[kNumRegisters] = {
  "r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7",
  "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
  "r16", "r17", "r18", "r19", "r20", "r21", "r22", "r23",
  "r24", "r25", "r26", "r27", "r28", "r29", "r30", "r31",
  "r32", "r33", "r34", "r35", "r36", "r37", "r38", "r39",
  "r40", "r41", "r42", "r43", "r44", "r45", "r46", "r47",
  "r48", "r49", "r50", "r51", "fp", "tp", "sp", "lr",
  "r56", "r57", "r58", "r59", "r60", "r61", "r62", "zero",
};

// List of alias names which can be used when referring to MIPS registers.
const Registers::RegisterAlias Registers::aliases_[] = {
  {52, "r52"},
  {53, "r53"},
  {54, "r54"},
  {55, "r55"},
  {56, "sn"},
  {57, "idn0"},
  {58, "idn1"},
  {59, "udn0"},
  {60, "udn1"},
  {61, "udn2"},
  {62, "udn3"},
  {63, "r63"},
  {kInvalidRegister, NULL}
};

const char* Registers::Name(int reg) {
  const char* result;
  if ((0 <= reg) && (reg < kNumRegisters)) {
    result = names_[reg];
  } else {
    result = "noreg";
  }
  return result;
}


int Registers::Number(const char* name) {
  // Look through the canonical names.
  for (int i = 0; i < kNumRegisters; i++) {
    if (strcmp(names_[i], name) == 0) {
      return i;
    }
  }

  // Look through the alias names.
  int i = 0;
  while (aliases_[i].reg != kInvalidRegister) {
    if (strcmp(aliases_[i].name, name) == 0) {
      return aliases_[i].reg;
    }
    i++;
  }

  // No register with the reguested name found.
  return kInvalidRegister;
}


// -----------------------------------------------------------------------------
// Instructions.


} }   // namespace v8::internal

#endif  // V8_TARGET_ARCH_TILEGX
