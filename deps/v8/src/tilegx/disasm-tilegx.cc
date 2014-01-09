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

// A Disassembler object is used to disassemble a block of code instruction by
// instruction. The default implementation of the NameConverter object can be
// overriden to modify register names or to do symbol lookup on addresses.
//
// The example below will disassemble a block of code and print it to stdout.
//
//   NameConverter converter;
//   Disassembler d(converter);
//   for (byte* pc = begin; pc < end;) {
//     v8::internal::EmbeddedVector<char, 256> buffer;
//     byte* prev_pc = pc;
//     pc += d.InstructionDecode(buffer, pc);
//     printf("%p    %08x      %s\n",
//            prev_pc, *reinterpret_cast<int32_t*>(prev_pc), buffer);
//   }
//
// The Disassembler class also has a convenience method to disassemble a block
// of code into a FILE*, meaning that the above functionality could also be
// achieved by just calling Disassembler::Disassemble(stdout, begin, end);


#include <assert.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#ifndef WIN32
#include <stdint.h>
#endif

#include "v8.h"

#if defined(V8_TARGET_ARCH_TILEGX)

#include "tilegx/constants-tilegx.h"
#include "disasm.h"
#include "macro-assembler.h"
#include "platform.h"

namespace v8 {
namespace internal {

//------------------------------------------------------------------------------

// Decoder decodes and disassembles instructions into an output buffer.
// It uses the converter to convert register names and call destinations into
// more informative description.
class Decoder {
 public:
  Decoder(const disasm::NameConverter& converter,
          v8::internal::Vector<char> out_buffer)
    : converter_(converter),
      out_buffer_(out_buffer),
      out_buffer_pos_(0) {
    out_buffer_[out_buffer_pos_] = '\0';
  }

  ~Decoder() {}

  // Writes one disassembled instruction into 'buffer' (0-terminated).
  // Returns the length of the disassembled machine instruction in bytes.
  int InstructionDecode(byte* instruction);

 private:
  void Format(char* format);
  void DecodeTypeJump(Instruction* instr);

  const disasm::NameConverter& converter_;
  v8::internal::Vector<char> out_buffer_;
  int out_buffer_pos_;

  DISALLOW_COPY_AND_ASSIGN(Decoder);
};

// Format takes a formatting string for a whole instruction and prints it into
// the output buffer. All escaped options are handed to FormatOption to be
// parsed further.
void Decoder::Format(char* format) {
  char cur = *format++;
  while ((cur != 0) && (out_buffer_pos_ < (out_buffer_.length() - 1))) {
    out_buffer_[out_buffer_pos_++] = cur;
    cur = *format++;
  }
  out_buffer_[out_buffer_pos_]  = '\0';
}

// Disassemble the instruction at *instr_ptr into the output buffer.
int Decoder::InstructionDecode(byte* instr_ptr) {
  Instruction* instr = Instruction::At(instr_ptr);
  Instr bits = instr->InstructionBits();
  char dout[128];

  // Print raw instruction bytes.
  out_buffer_pos_ += OS::SNPrintF(out_buffer_ + out_buffer_pos_,
                                       "%016lx  ",
                                       bits);
  print_insn_tilegx_buf((unsigned char *)&bits, dout);
  Format(dout);
  return Instruction::kInstrSize;
}


} }  // namespace v8::internal



//------------------------------------------------------------------------------

namespace disasm {

const char* NameConverter::NameOfAddress(byte* addr) const {
  v8::internal::OS::SNPrintF(tmp_buffer_, "%p", addr);
  return tmp_buffer_.start();
}


const char* NameConverter::NameOfConstant(byte* addr) const {
  return NameOfAddress(addr);
}


const char* NameConverter::NameOfCPURegister(int reg) const {
  return v8::internal::Registers::Name(reg);
}


const char* NameConverter::NameOfXMMRegister(int reg) const {
  UNREACHABLE();
  return "nofpreg";
}


const char* NameConverter::NameOfByteCPURegister(int reg) const {
  UNREACHABLE();
  return "nobytereg";
}


const char* NameConverter::NameInCode(byte* addr) const {
  // The default name converter is called for unknown code. So we will not try
  // to access any memory.
  return "";
}


//------------------------------------------------------------------------------

Disassembler::Disassembler(const NameConverter& converter)
    : converter_(converter) {}


Disassembler::~Disassembler() {}


int Disassembler::InstructionDecode(v8::internal::Vector<char> buffer,
                                    byte* instruction) {
  v8::internal::Decoder d(converter_, buffer);
  return d.InstructionDecode(instruction);
}


// The MIPS assembler does not currently use constant pools.
int Disassembler::ConstantPoolSizeAt(byte* instruction) {
  return -1;
}


void Disassembler::Disassemble(FILE* f, byte* begin, byte* end) {
  NameConverter converter;
  Disassembler d(converter);
  for (byte* pc = begin; pc < end;) {
    v8::internal::EmbeddedVector<char, 128> buffer;
    buffer[0] = '\0';
    byte* prev_pc = pc;
    pc += d.InstructionDecode(buffer, pc);
    v8::internal::PrintF(f, "%p    %08x      %s\n",
        prev_pc, *reinterpret_cast<int32_t*>(prev_pc), buffer.start());
  }
}


#undef UNSUPPORTED

}  // namespace disasm

#endif  // V8_TARGET_ARCH_TILEGX
