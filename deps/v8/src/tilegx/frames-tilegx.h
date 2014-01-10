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



#ifndef V8_TILEGX_FRAMES_TILEGX_H_
#define V8_TILEGX_FRAMES_TILEGX_H_

namespace v8 {
namespace internal {

// Register lists.
// Note that the bit values must match those used in actual instruction
// encoding.
const int kNumRegs = 64;

const RegList kJSCallerSaved =
  1L << 0  |  // r0
  1L << 1  |  // r1
  1L << 2  |  // r2
  1L << 3  |  // r3
  1L << 4  |  // r4
  1L << 5  |  // r5
  1L << 6  |  // r6
  1L << 7  |  // r7
  1L << 8  |  // r8
  1L << 9  |  // r9
  1L << 10 |  // r10
  1L << 11 |  // r11
  1L << 12 |  // r12
  1L << 13 |  // r13
  1L << 14 |  // r14
  1L << 15 |  // r15
  1L << 16 |  // r16
  1L << 17 |  // r17
  1L << 18 |  // r18
  1L << 19 |  // r19
  1L << 20 |  // r20
  1L << 21 |  // r21
  1L << 22 |  // r22
  1L << 23 |  // r23
  1L << 24 |  // r24
  1L << 25 |  // r25
  1L << 26 |  // r26
  1L << 27 ;  // r27

const int kNumJSCallerSaved = 28;

int JSCallerSavedCode(int n);

// Callee-saved registers preserved when switching from C to JavaScript.
const RegList kCalleeSaved =
  1L << 30 |  // r30
  1L << 31 |  // r31
  1L << 32 |  // r32
  1L << 33 |  // r33
  1L << 34 |  // r34
  1L << 35 |  // r35
  1L << 36 |  // r36
  1L << 37 |  // r37
  1L << 38 |  // r38
  1L << 39 |  // r39
  1L << 40 |  // r40
  1L << 41 |  // r41
  1L << 42 |  // r42
  1L << 43 |  // r43
  1L << 44 |  // r44
  1L << 45 |  // r45
  1L << 46 |  // r46
  1L << 47 |  // r47
  1L << 48 |  // r48
  1L << 49;   // r49

const int kNumCalleeSaved = 20;

const int kUndefIndex = -1;

const int kSafepointRegisterStackIndexMap[kNumRegs] = {
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
  kUndefIndex, // at
  kUndefIndex, // at2
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
  kUndefIndex,
  kUndefIndex,
  kUndefIndex,
  kUndefIndex,
  kUndefIndex,
  kUndefIndex,
  kUndefIndex,// sn
  kUndefIndex,// idn0
  kUndefIndex,// idn1
  kUndefIndex,// udn0
  kUndefIndex,// udn1
  kUndefIndex,// udn2
  kUndefIndex,// udn3
  kUndefIndex // zero
};

typedef Object* JSCallerSavedBuffer[kNumJSCallerSaved];

class JavaScriptFrameConstants : public AllStatic {
 public:
  // FP-relative.
  static const int kLocal0Offset = StandardFrameConstants::kExpressionsOffset;
  static const int kLastParameterOffset = +2 * kPointerSize;
  static const int kFunctionOffset = StandardFrameConstants::kMarkerOffset;

  // Caller SP-relative.
  static const int kParam0Offset   = -2 * kPointerSize;
  static const int kReceiverOffset = -1 * kPointerSize;
};

inline Object* JavaScriptFrame::function_slot_object() const {
  const int offset = JavaScriptFrameConstants::kFunctionOffset;
  return Memory::Object_at(fp() + offset);
}

class ExitFrameConstants : public AllStatic {
 public:
  // See some explanation in MacroAssembler::EnterExitFrame.
  // This marks the top of the extra allocated stack space.
  static const int kStackSpaceOffset = -3 * kPointerSize;

  static const int kCodeOffset = -2 * kPointerSize;

  static const int kSPOffset = -1 * kPointerSize;

  // The caller fields are below the frame pointer on the stack.
  static const int kCallerFPOffset = +0 * kPointerSize;
  // The calling JS function is between FP and PC.
  static const int kCallerPCOffset = +1 * kPointerSize;

  // MIPS-specific: a pointer to the old sp to avoid unnecessary calculations.
  static const int kCallerSPOffset = +2 * kPointerSize;

  // FP-relative displacement of the caller's SP.
  static const int kCallerSPDisplacement = +2 * kPointerSize;
};

class InternalFrameConstants : public AllStatic {
 public:
  // FP-relative.
  static const int kCodeOffset = StandardFrameConstants::kExpressionsOffset;
};

class ArgumentsAdaptorFrameConstants : public AllStatic {
 public:
  // FP-relative.
  static const int kLengthOffset = StandardFrameConstants::kExpressionsOffset;

  static const int kFrameSize =
      StandardFrameConstants::kFixedFrameSize + kPointerSize;
};

class ConstructFrameConstants : public AllStatic {
 public:
  // FP-relative.
  static const int kImplicitReceiverOffset = -6 * kPointerSize;
  static const int kConstructorOffset      = -5 * kPointerSize;
  static const int kLengthOffset           = -4 * kPointerSize;
  static const int kCodeOffset = StandardFrameConstants::kExpressionsOffset;

  static const int kFrameSize =
      StandardFrameConstants::kFixedFrameSize + 4 * kPointerSize;
};

class EntryFrameConstants : public AllStatic {
 public:
  static const int kCallerFPOffset      = -3 * kPointerSize;
};

// Number of registers for which space is reserved in safepoints. Must be a
// multiple of 8.
const int kNumSafepointRegisters = 56;

// Define the list of registers actually saved at safepoints.
// Note that the number of saved registers may be smaller than the reserved
// space, i.e. kNumSafepointSavedRegisters <= kNumSafepointRegisters.
const RegList kSafepointSavedRegisters = kJSCallerSaved | kCalleeSaved;
const int kNumSafepointSavedRegisters =
    kNumJSCallerSaved + kNumCalleeSaved;

typedef Object* JSCallerSavedBuffer[kNumJSCallerSaved];

inline void StackHandler::SetFp(Address slot, Address fp) {
  Memory::Address_at(slot) = fp;
}

} }  // namespace v8::internal

#endif
