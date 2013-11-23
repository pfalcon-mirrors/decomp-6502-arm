# insn_arm.py
# Copyright (C) 2013 Ulrich Hecht

# This file is part of 6502 Decompiler.

# 6502 Decompiler is free software: you can redistribute it and/or modify it
# under the terms of the GNU General Public License version 3 as published
# by the Free Software Foundation.

# 6502 Decompiler is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
# for more details.

# You should have received a copy of the GNU General Public License along
# with 6502 Decompiler.  If not, see <http://www.gnu.org/licenses/>.

from debug import *
from insn import Symbol
import struct
from copy import copy

def trace(self, code, org, addr, ins):
    opcode = struct.unpack('<I', code[addr-org : addr-org+4])[0]
    #print(opcode)
    ins.bytes = [opcode]

    ins.cond = opcode >> 28
    ins.op = (opcode >> 20) & 0xff
    
    link_ins = ins
    if ins.cond != 0xe and ins.op >> 4 != 0xa:
      # conditional instruction that is not a branch
      # insert a fake branch with inverted condition to the nearest insn with a different
      # condition code
      debug(TRACE, 4, 'conditional non-branch at', hex(addr))

      ins2 = copy(ins)
      ins2.comefrom = [ins]
      # make this insn unconditional
      ins2.cond = 0xe

      cond_end = addr + 4
      while struct.unpack('<I', code[cond_end-org : cond_end-org+4])[0] >> 28 == ins.cond and cond_end - org < len(code) - 4:
        # modify machine code to make subsequent insns with the same condition
        # unconditional
        # XXX: yuck; find a way to do this without changing the source text
        debug(TRACE, 4, 'unconding', hex(cond_end), hex(len(code)),hex(org))
        code[cond_end-org+3] = (code[cond_end-org+3] & 0xf) | 0xe0
        cond_end += 4

      ins.artificial_branch = cond_end
      ins.cond = ins.cond ^ 1
      ins.op = 0xa0 # Bcc
      ins.next = [ins2, self.trace(code, org, cond_end, ins)]

      ins = ins2
    
    debug(TRACE, 4, "continuing", hex(addr))
    ins.set_flags = (opcode >> 20) & 1
    ins.rn = (opcode >> 16) & 0xf
    ins.rd = (opcode >> 12) & 0xf
    ins.rs = (opcode >> 8) & 0xf
    ins.shift_bits = (opcode >> 7) & 0x1f
    ins.shift = (opcode >> 5) & 0x3
    ins.shift_rot = (opcode >> 4) & 0x1
    ins.rm = opcode & 0xf
    ins.imm8 = opcode & 0xff
    ins.imm12 = opcode & 0xfff
    ins.off24 = opcode & 0xffffff
    if ins.off24 >= 0x800000:
      ins.off24 -= 0x1000000
    ins.reglist = opcode & 0xffff
    
    debug(TRACE, 4, 'opcode '+hex(opcode), 'op', hex(ins.op), 'cond', hex(ins.cond))

    if ins.op >> 4 == 0xa:
      daddr = addr + ins.off24 * 4 + 8
      debug(TRACE, 4, 'B', hex(ins.off24), hex(ins.cond))
      if ins.cond == 0xe:
        ins.next = [self.trace(code, org, daddr, ins)]
      else:
        ins.next = [self.trace(code, org, addr + 4, ins), self.trace(code, org, daddr, ins)]
    elif ins.op >> 4 == 0xb:
      daddr = addr + ins.off24 * 4 + 8
      debug(TRACE, 4, 'BL', hex(ins.off24))
      ins.next = [self.trace(code, org, addr + 4, ins), self.trace(code, org, daddr, ins, Symbol(daddr, 'fun'))]
    elif opcode & 0x0ffffff0 == 0x012fff10 and ins.cond == 0xe:
      debug(TRACE, 4, 'EOT (BX r' + str(ins.rm) + ')')
      ins.next = None
    elif ins.op & 0xe5 == 0x81 and ins.cond == 0xe and (ins.reglist & 0x8000) == 0x8000:
      debug(TRACE, 4, 'EOT (LDM {...pc}')
      ins.next = None
    elif ins.op & 0xe5 == 0x41 and ins.rd == 15:
      # LDR pc,[...]
      if ins.rn != 15:
        debug(TRACE, 4, 'EOT (LDR pc,[...])')
        if ins.cond != 0xe:
          ins.next = [self.trace(code, org, addr + 4, ins)]
        else:
          ins.next = None
      else:
        debug(TRACE, 4, 'LDR pc,[pc...])')
        if ins.op & 0x08:
          daddr_loc = ins.imm12 + addr + 8
        else:
          daddr_loc = -ins.imm12 + addr + 8
        daddr = struct.unpack('<I', code[daddr_loc:daddr_loc + 4])[0]
        if ins.cond != 0xe:
          ins.next = [self.trace(code, org, addr + 4, ins), self.trace(code, org, daddr, ins)]
        else:
          ins.next = [self.trace(code, org, daddr, ins)]
    elif ins.op & 0xfe == 0x1a and ins.rd == 15:
      debug(TRACE, 4, 'EOT (MOV pc,...)')
      ins.next = None
    else:
      ins.next = [self.trace(code, org, addr + 4, ins)]

    return link_ins

def guess_entry_points(text, org, manual_entries):
  # find all "MOV R12, SP" and "PUSH {..., lr}"
  mov_r12_sp = []
  push_lr = []
  for i in range(0, len(text) >> 2):
    insn = struct.unpack('<I', text[i:i+4])[0]
    if insn == 0xe1a0c00d:
      mov_r12_sp += [i]
    elif insn & 0xffffc000 == 0xe92d4000:
      push_lr += [i]
  debug(TRACE, 3, 'found', len(mov_r12_sp), 'times MOV R12, SP;', len(push_lr), 'times PUSH {...lr}')

  # if there are a lot of "MOV R12, SP"'s, we assume the code has been
  # compiled with frame pointer and functions start at the MOV; otherwise,
  # functions start at the PUSH
  if len(mov_r12_sp) > len(push_lr) / 2:
    entry_points = mov_r12_sp
  else:
    entry_points = push_lr

  new_entry_points = []
  for i in entry_points:
    i += org
    if not i in manual_entries:
      new_entry_points.append(i)

  return new_entry_points
