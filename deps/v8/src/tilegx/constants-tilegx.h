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

#ifndef  V8_TILEGX_CONSTANTS_H_
#define  V8_TILEGX_CONSTANTS_H_

#define UNIMPLEMENTED_TILEGX()                                                \
  v8::internal::PrintF("%s, \tline %d: \tfunction %s not implemented. \n",    \
                       __FILE__, __LINE__, __func__)

namespace v8 {
namespace internal {

const int kImm8Shift = 0;
const int kImm8Bits  = 8;
const int kImm16Shift = 0;
const int kImm16Bits  = 16;
const int kImm30Shift = 0;
const int kImm30Bits  = 30;
const int kImm8Mask   = ((1 << kImm8Bits) - 1) << kImm8Shift;
const int kImm16Mask  = ((1 << kImm16Bits) - 1) << kImm16Shift;
const int kImm30Mask  = ((1 << kImm30Bits) - 1) << kImm30Shift;

const uint32_t kMaxWatchpointCode = 31;
const uint32_t kMaxStopCode = 127;
STATIC_ASSERT(kMaxWatchpointCode < kMaxStopCode);

enum Condition {
  // Any value < 0 is considered no_condition.
  kNoCondition  = -1,

  overflow      =  0,
  no_overflow   =  1,
  Uless         =  2,
  Ugreater_equal=  3,
  equal         =  4,
  not_equal     =  5,
  Uless_equal   =  6,
  Ugreater      =  7,
  negative      =  8,
  positive      =  9,
  parity_even   = 10,
  parity_odd    = 11,
  less          = 12,
  greater_equal = 13,
  less_equal    = 14,
  greater       = 15,
  ueq           = 16,  // Unordered or Equal.
  nue           = 17,  // Not (Unordered or Equal).

  cc_always     = 18,

  // Aliases.
  carry         = Uless,
  not_carry     = Ugreater_equal,
  zero_cond     = equal,
  eq            = equal,
  not_zero      = not_equal,
  ne            = not_equal,
  nz            = not_equal,
  sign          = negative,
  not_sign      = positive,
  mi            = negative,
  pl            = positive,
  hi            = Ugreater,
  ls            = Uless_equal,
  ge            = greater_equal,
  lt            = less,
  gt            = greater,
  le            = less_equal,
  hs            = Ugreater_equal,
  lo            = Uless,
  al            = cc_always,

  cc_default    = kNoCondition
};

// Returns the equivalent of !cc.
// Negation of the default kNoCondition (-1) results in a non-default
// no_condition value (-2). As long as tests for no_condition check
// for condition < 0, this will work as expected.
inline Condition NegateCondition(Condition cc) {
  ASSERT(cc != cc_always);
  return static_cast<Condition>(cc ^ 1);
}

inline Condition ReverseCondition(Condition cc) {
  switch (cc) {
    case Uless:
      return Ugreater;
    case Ugreater:
      return Uless;
    case Ugreater_equal:
      return Uless_equal;
    case Uless_equal:
      return Ugreater_equal;
    case less:
      return greater;
    case greater:
      return less;
    case greater_equal:
      return less_equal;
    case less_equal:
      return greater_equal;
    default:
      return cc;
  };
}

// TileGX has 64bit width instruction encoding.
typedef int64_t Instr;

const int kArgByRegNum = 10;
const int kStackLowReserve = 2 * kPointerSize;
const int kNumRegisters = 64;
const int kInvalidRegister = -1;

// Helper functions for converting between register numbers and names.
class Registers {
 public:
  // Return the name of the register.
  static const char* Name(int reg);

  // Lookup the register number for the name provided.
  static int Number(const char* name);

  struct RegisterAlias {
    int reg;
    const char* name;
  };

 private:
  static const char* names_[kNumRegisters];
  static const RegisterAlias aliases_[];
};

class Instruction {
 public:
  enum {
    kInstrSize = 8,
    kInstrSizeLog2 = 3
  };

  // Get the raw instruction bits.
  inline Instr InstructionBits() const {
    return *reinterpret_cast<const Instr*>(this);
  }

  // Set the raw instruction bits to value.
  inline void SetInstructionBits(Instr value) {
    *reinterpret_cast<Instr*>(this) = value;
  }

  // Read one particular bit out of the instruction bits.
  inline int Bit(int nr) const {
    return (InstructionBits() >> nr) & 1;
  }

  // Read a bit field out of the instruction bits.
  inline int Bits(int hi, int lo) const {
    return (InstructionBits() >> lo) & ((2 << (hi - lo)) - 1);
  }

  // Instructions are read of out a code stream. The only way to get a
  // reference to an instruction is to convert a pointer. There is no way
  // to allocate or create instances of class Instruction.
  // Use the At(pc) function to create references to Instruction.
  static Instruction* At(byte* pc) {
    return reinterpret_cast<Instruction*>(pc);
  }

 private:
  // We need to prevent the creation of instances of class Instruction.
  DISALLOW_IMPLICIT_CONSTRUCTORS(Instruction);
};


} } // namespace v8::internal

#endif    // #ifndef V8_TILEGX_CONSTANTS_H_
