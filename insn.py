# insn.py
# Copyright (C) 2012, 2013 Ulrich Hecht

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

from __future__ import print_function

from util import *
from debug import *
import config

OPC_OUTOFRANGE = 0x1000

class Arch:
  def __init__(self):
    self.name = None
    self.register_base = False
    self.max_array_idx = 0x100
    self.register_type = 'uint8_t'
    self.register_size = 8
    self.flags = ['C', 'Z', 'N', 'V']
    self.numbered_registers = False
    self.stacked_return_address = False
  def set_arch(self, arch):
    self.name = arch
    if arch == 'arm':
      self.register_base = True
      self.max_array_idx = 0x10000000
      self.register_type = 'uint32_t'
      self.register_size = 32
      # XXX: should this contain R13-R15?
      self.registers = ['R0', 'R1', 'R2', 'R3', 'R4', 'R5', 'R6', 'R7', 'R8', 'R9', 'R10', 'R11', 'R12', 'R13', 'R14', 'R15']
      self.return_locs = self.registers[0:2]
      self.non_return_locs = self.registers[2:] + self.flags
      self.arg_locs = self.registers[0:4]
      self.non_arg_locs = self.registers[4:] + self.flags
      self.numbered_registers = True
    elif arch == '6502':
      self.registers = ['A', 'X', 'Y']
      # no calling conventions, any register or flag can be used to pass data
      self.return_locs = self.registers + self.flags
      self.non_return_locs = []
      self.arg_locs = self.return_locs
      self.non_arg_locs = []
      self.stacked_return_address = True
    else:
      raise UserError('unknown architecture ' + arm)

arch = Arch()
config.arch = arch

class Insn:
  def __init__(self, addr):
    self.addr = addr
    self.bytes = []
    self.disas = '(unknown)'
    self.next = []
    self.comefrom = []
    self.sym = None
    # if analysis determines that this two-way instruction is actually
    # one-way, fake_branch can be set to the index into .next that is
    # actually taken; currently used by conditional branches
    self.fake_branch = -1
    self.fixed_mem = -1
    self.artificial_branch = -1
  def __str__(self):
    s = hex(self.addr) + ': ' + self.disas
    if self.next:
      s += ' -> ['
      for i in self.next:
        s += hex(i.addr) + ' '
      s += ']'
    if self.comefrom:
      s += ' <- ['
      for i in self.comefrom:
        s += hex(i.addr) + ' '
      s += ']'
    return s

class Symbol:
  def __init__(self, address, name = None):
    self.address = address
    if name == None:
      name = 'sym'
    self.name = name + '_' + zhex(address)
    self.insn = None

import insn_6502
import insn_arm

class MCodeGraph:
  def __init__(self):
    self.symbols = dict()
    self.traced = dict()
    if arch.name == '6502':
      self.trace_arch = insn_6502.trace
    elif arch.name == 'arm':
      self.trace_arch = insn_arm.trace
    else:
      raise InternalError('unknown arch ' + arch.name)
  
  def traceall(self, code, org, entries):
    MCodeGraph._text = code
    MCodeGraph._org = org
    for i in entries:
      self.trace(code, org, i, None, Symbol(i, 'start'))
  
  def trace(self, code, org, addr, comefrom = None, sym = None):
    def outside():
      debug(TRACE, 2, 'tracing outside available code')
      ins.bytes = [OPC_OUTOFRANGE]
      ins.next = []

    debug(TRACE, 4, 'tracing', hex(addr))
    try:
      debug(TRACE, 4, hex(code[addr - org]))
    except IndexError:
      debug(TRACE, 4, 'out of range')
    if addr in self.traced:
      # no need to trace, but we may have to add a symbol
      if sym != None and self.traced[addr].sym == None:
        sym.insn = self.traced[addr]
        self.symbols[addr] = sym
        self.traced[addr].sym = sym
      if comefrom and not comefrom in self.traced[addr].comefrom:
        self.traced[addr].comefrom += [comefrom]
      return self.traced[addr]
    ins = Insn(addr)
    if sym:
      sym.insn = ins
      self.symbols[addr] = sym
      ins.sym = sym
    self.traced[addr] = ins
    if comefrom and not comefrom in ins.comefrom:
      ins.comefrom += [comefrom]
    if addr - org >= len(code) or addr < org:
      outside()
      return ins

    return self.trace_arch(self, code, org, addr, ins)
