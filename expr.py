# expr.py
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
from copy import copy

from debug import *

import ssa
import struct
from insn import MCodeGraph
from config import arch
from util import *

CONST = 0
VAR = 1
COMPARE_EQ = 2
COMPARE_GE = 3
SUB = 5
ADD = 6
ADD_PTR = 7
AND = 8
BITFLAGS_N = 9
BITFLAGS_V = 10
OR = 11
ORFLAGS_N = 12
ORFLAGS_Z = 13
ANDFLAGS_N = 14
ANDFLAGS_Z = 15
PHI = 16
ARGS = 17
SHFLAGS_N = 18
SHLFLAGS_C = 19
SHL = 21
SHRFLAGS_C = 23
SHR = 25
ADCFLAGS_N = 26
ADCFLAGS_C = 27
ADCFLAGS_Z = 28
ROL = 29
EOR = 33
EORFLAGS_N = 34
EORFLAGS_Z = 35
SBBFLAGS_N = 36
SBBFLAGS_C = 37
SBBFLAGS_Z = 38
ROR = 39
NOP = 43
NOT = 44
COMPARE_NE = 45
COMPARE_LT = 46
EXPLICIT_PHI = 47
LOAD = 48
STORE = 49
ANDFLAGS_NOTZ = 50
INTRINSIC = 51
IOIN = 52
IOOUT = 53
FLAGS = 54
DEFLAGS_C = 55
DEFLAGS_Z = 56
DEFLAGS_N = 57
DEFLAGS_V = 58
ADCFLAGS_V = 59
SBBFLAGS_V = 60
EORFLAGS_NOTN = 61
LOAD32 = 62
ORFLAGS_C = 63
EORFLAGS_C = 64
MOVFLAGS_C = 65
MOVFLAGS_Z = 66
MOVFLAGS_N = 67
ANDFLAGS_C = 68
SUBFLAGS_C = 69
SUBFLAGS_Z = 70
SUBFLAGS_N = 71
STORE16 = 72
STORE32 = 73
ASR = 74
ADDFLAGS_C = 75
ADDFLAGS_Z = 76
ADDFLAGS_N = 77
ADDFLAGS_V = 78
SUBFLAGS_V = 79
LOAD16 = 80
INV = 81
COMPARE_GES = 82
COMPARE_GTS = 83
COMPARE_LTS = 84
COMPARE_LES = 85
IOIN16 = 86
IOIN32 = 87
IOOUT16 = 88
IOOUT32 = 89

def access_size(op):
  if op == LOAD32:
    return 32
  elif op == LOAD16:
    return 16
  elif op == LOAD:
    return 8
  else:
    raise InternalError("unknown access size for op")

class Expr:
  def __init__(self, type, ops):
    assert(isinstance(ops, list))
    self.type = type
    self.ops = ops
    self.dont_propagate = False
    self.dont_eliminate = False

  def equals(self, other):
    if self.type != other.type:
      return False
    if len(self.ops) != len(other.ops):
      return False
    for i in range(0, len(self.ops)):
      if isinstance(self.ops[i], Expr):
        if not isinstance(other.ops[i], Expr):
          return False
        if not self.ops[i].equals(other.ops[i]):
          return False
      elif self.ops[i] != other.ops[i]:
        return False
    return True

  def __str__(self):
    t = {
      CONST: '',
      VAR: '',
      COMPARE_EQ: ' ==',
      COMPARE_GE: ' >=',
      COMPARE_NE: ' !=',
      COMPARE_LT: ' <',
      SUB: ' -',
      ADD: ' +',
      ADD_PTR: ' +p',
      AND: ' &',
      BITFLAGS_N: ' bitN',
      BITFLAGS_V: ' bitV',
      OR: ' |',
      ORFLAGS_N: ' orN',
      ORFLAGS_Z: ' orZ',
      ANDFLAGS_N: ' andN',
      ANDFLAGS_Z: ' andZ',
      ANDFLAGS_NOTZ: ' and!Z',
      PHI: 'phi',
      EXPLICIT_PHI: 'exphi',
      ARGS: ' args',
      SHFLAGS_N: ' shN',
      SHLFLAGS_C: ' shlC',
      SHL: ' <<',
      SHRFLAGS_C: ' shrC',
      SHR: ' >>',
      ADCFLAGS_N: ' +cN',
      ADCFLAGS_C: ' +cC',
      ADCFLAGS_Z: ' +cZ',
      ADCFLAGS_V: ' +cV',
      ROL: ' rol',
      ROR: ' ror',
      EOR: ' ^',
      EORFLAGS_N: ' eorN',
      EORFLAGS_NOTN: ' eor!N',
      EORFLAGS_Z: ' eorZ',
      SBBFLAGS_N: ' -cN',
      SBBFLAGS_C: ' -cC',
      SBBFLAGS_Z: ' -cZ',
      SBBFLAGS_V: ' -cV',
      NOP: 'nop',
      NOT: '!',
      LOAD: ' load',
      LOAD16: ' load16',
      STORE: ' store',
      INTRINSIC: 'intr',
      IOIN: 'inb',
      IOIN16: 'inw',
      IOIN32: 'inl',
      IOOUT: ' outb',
      IOOUT16: ' outw',
      IOOUT32: ' outl',
      FLAGS: ' flags',
      DEFLAGS_C: 'defc',
      DEFLAGS_Z: 'defz',
      DEFLAGS_N: 'defn',
      DEFLAGS_V: 'defv',
      LOAD32: ' load32',
      ORFLAGS_C: ' orC',
      EORFLAGS_C: ' eorC',
      MOVFLAGS_C: ' movC',
      MOVFLAGS_Z: ' movZ',
      MOVFLAGS_N: ' movN',
      ANDFLAGS_C: ' andC',
      SUBFLAGS_C: ' -C',
      SUBFLAGS_Z: ' -Z',
      SUBFLAGS_N: ' -N',
      SUBFLAGS_V: ' -V',
      STORE16: ' store16',
      STORE32: ' store32',
      ASR: ' >>s',
      ADDFLAGS_C: ' +C',
      ADDFLAGS_Z: ' +Z',
      ADDFLAGS_N: ' +N',
      ADDFLAGS_V: ' +V',
      INV: '~',
      COMPARE_GES: ' >=s',
      COMPARE_GTS: ' >s',
      COMPARE_LTS: ' <s',
      COMPARE_LES: ' <=s',
    }
    s = '('
    if (len(self.ops) == 1 and t[self.type] != '') or self.type == PHI:
      s += t[self.type] + '('
      for i in self.ops:
        s += str(i) + ', '
      s = s.rstrip(', ') + ')'
    elif len(self.ops) == 1:
      s += str(self.ops[0])
    else:
      s += str(self.ops[0]) + t[self.type]
      for i in self.ops[1:]:
        s += ' ' + str(i)
    return s + ')'

  def getallops(self):
    ops = []
    for i in self.ops:
      if isinstance(i, Expr):
        assert(not (i is self))
        ops += i.getallops()
      else:
        ops += [i]
    return ops

  def getallsubexprs(self):
    exp = []
    for i in self.ops:
      if isinstance(i, Expr):
        assert(not (i is self))
        exp += [i] + i.getallsubexprs()
    return exp

  def copy(self):
    new_ops = []
    for i in self.ops:
      if isinstance(i, Expr):
        new_ops += [i.copy()]
      else:
        new_ops += [i]
    new_expr = Expr(self.type, new_ops)
    new_expr.dont_propagate = self.dont_propagate
    new_expr.dont_eliminate = self.dont_eliminate
    return new_expr

  def substitute(self, old, new, dup = False):
    assert(not (self is new))
    if dup:
      # don't copy definitions, prevents matching using ==
      self = self.copy()
    for i in range(0, len(self.ops)):
      if isinstance(self.ops[i], Expr) and not (self.ops[i] is new):
        self.ops[i] = self.ops[i].substitute(old, new, dup)
      elif self.ops[i] == old:
        self.ops[i] = new
    return self

  def substitute_expr(self, old, new):
    for i in range(0, len(self.ops)):
      if isinstance(self.ops[i], Expr):
        if self.ops[i].equals(old):
          debug(EXPR, 4, 'subexing', self.ops[i], 'in', self, 'to', new)
          self.ops[i] = new
        else:
          self.ops[i].substitute_expr(old, new)

  def remove(self, op):
    newops = []
    for i in self.ops:
      if i != op:
        newops += [i]
    self.ops = newops

  def simplify(self):
    for i in self.ops:
      if isinstance(i, Expr):
        debug(EXPR, 4, 'recusimp', i)
        i.simplify()
    nowop = str(self)
    simplifications = ''

    for i in range(0, len(self.ops)):
      if isinstance(self.ops[i], ssa.SSADef) and self.ops[i].type[0] == 'M' and isinstance(self.ops[i].addr, int):
        # XXX: is text writable?
        if self.ops[i].addr >= MCodeGraph._org and self.ops[i].addr < MCodeGraph._org + len(MCodeGraph._text):
          self.ops[i] = struct.unpack('<I', MCodeGraph._text[self.ops[i].addr - MCodeGraph._org:self.ops[i].addr - MCodeGraph._org+4])[0]
          simplifications += 'constmem'

    if self.type == VAR and isinstance(self.ops[0], Expr):
      self.type = self.ops[0].type
      self.ops = self.ops[0].ops
      simplifications += 'unbracket'
    for i in range(0, len(self.ops)):
      if isinstance(self.ops[i], Expr) and (self.ops[i].type == CONST or self.ops[i].type == VAR):
        simplifications += 'const/var '
        self.ops[i] = self.ops[i].ops[0]
    if self.type == NOT:
      if isinstance(self.ops[0], Expr) and self.ops[0].type == NOT:
        simplifications += 'not '
        self.type = VAR
        self.ops[0] = self.ops[0].ops[0]
    if self.type in [ADD, SUB]:
      newops = []
      for i in self.ops:
        if isinstance(i, Expr) and i.type == self.type:
          simplifications += 'add/sub '
          newops += i.ops
        else:
          newops += [i]
      self.ops = newops
    if self.type in [ADD, ADCFLAGS_N, ADCFLAGS_C, ADCFLAGS_Z, ADCFLAGS_V]:
      total_const = 0
      newops = []
      nonconst = False
      for i in self.ops:
        if isinstance(i, int):
          total_const += i
          simplifications += 'addconst '
        else:
          newops += [i]
          nonconst = True
      self.ops = newops
      if total_const != 0 or len(self.ops) == 0:
        self.ops += [total_const]
      if self.type == ADD:
        if not nonconst:
          self.type = CONST
        elif len(self.ops) == 1:
          self.type = VAR

    if self.type in [SUB, SBBFLAGS_C, SBBFLAGS_N, SBBFLAGS_Z, SBBFLAGS_V]:
      total_const = 0
      first_const = False
      if isinstance(self.ops[0], int):
        first_const = True
      newops = [self.ops[0]]
      nonconst = not first_const
      for i in self.ops[1:]:
        if isinstance(i, int):
          if first_const:
            newops[0] -= i
          else:
            total_const += i
          simplifications += 'subconst '
        else:
          newops += [i]
          nonconst = True
      self.ops = newops
      if total_const != 0:
        self.ops += [total_const]
      if not nonconst:
        self.type = CONST
      elif len(self.ops) == 1:
        self.type = VAR

    if self.type in [SHL, SHR] and isinstance(self.ops[0], Expr) and self.ops[0].type == self.type:
      inside = self.ops[0]
      self.ops[0] = inside.ops[0]
      self.ops[1] = Expr(ADD, [inside.ops[1], self.ops[1]])
      simplifications += 'shl/r '
    if self.type in [SHL, SHR] and isinstance(self.ops[0], int) and isinstance(self.ops[1], int):
      self.type = CONST
      if self.type == SHL:
        self.ops = [(self.ops[0] << self.ops[1]) & ~(1 << arch.register_size)]
      else:
        self.ops = [(self.ops[0] >> self.ops[1]) & ~(1 << arch.register_size)]
      simplifications += 'shl/rconst '
    elif self.type in [SHL, SHR] and isinstance(self.ops[1], int) and self.ops[1] == 0:
      self.type = VAR
      self.ops = [self.ops[0]]
      simplifications += 'shl/r#0 '
    if self.type == NOT and isinstance(self.ops[0], Expr) and self.ops[0].type in [COMPARE_EQ, COMPARE_GE, COMPARE_NE, COMPARE_LT, ANDFLAGS_Z, ANDFLAGS_NOTZ, EORFLAGS_N, EORFLAGS_NOTN, COMPARE_GES]:
      inside = self.ops[0]
      self.ops = inside.ops
      if inside.type == COMPARE_EQ:
        self.type = COMPARE_NE
      elif inside.type == COMPARE_GE:
        self.type = COMPARE_LT
      elif inside.type == COMPARE_NE:
        self.type = COMPARE_EQ
      elif inside.type == COMPARE_LT:
        self.type = COMPARE_GE
      elif inside.type == ANDFLAGS_Z:
        self.type = ANDFLAGS_NOTZ
      elif inside.type == ANDFLAGS_NOTZ:
        self.type = ANDFLAGS_Z
      elif inside.type == EORFLAGS_N:
        self.type = EORFLAGS_NOTN
      elif inside.type == EORFLAGS_NOTN:
        self.type = EORFLAGS_N
      elif inside.type == COMPARE_GES:
        self.type = COMPARE_LTS
      simplifications += 'notcond '
    if self.type in [COMPARE_EQ, COMPARE_NE, ANDFLAGS_N, ANDFLAGS_Z] and isinstance(self.ops[0], int) and isinstance(self.ops[1], int):
      if self.type == COMPARE_EQ:
        res = self.ops[0] == self.ops[1]
        simplifications += 'cmpeq'
      elif self.type == COMPARE_NE:
        res = self.ops[0] != self.ops[1]
        simplifications += 'cmpne'
      elif self.type == ANDFLAGS_N:
        res = (self.ops[0] & self.ops[1]) >= 128
        simplifications += 'andn'
      elif self.type == ANDFLAGS_Z:
        res = (self.ops[0] & self.ops[1]) == 0
        simplifications += 'andz'
      self.type = CONST
      self.ops = [1 if res else 0]
      simplifications += 'const '
    if self.type == NOT and isinstance(self.ops[0], int):
      self.type = CONST
      if self.ops[0] != 0:
        self.ops[0] = 0
      else:
        self.ops[0] = 1
      simplifications += 'notconst '
    if self.type == OR and 0 in self.ops:
      self.type = CONST
      if self.ops[0] == 0:
        self.ops = [self.ops[1]]
      else:
        self.ops = [self.ops[0]]
      simplifications += 'orzero '
    if self.type in [DEFLAGS_C, DEFLAGS_Z, DEFLAGS_N, DEFLAGS_V] and \
       isinstance(self.ops[0], Expr) and self.ops[0].type == FLAGS:
      if self.type == DEFLAGS_C:
        self.ops = [self.ops[0].ops[0]]
      elif self.type == DEFLAGS_Z:
        self.ops = [self.ops[0].ops[1]]
      elif self.type == DEFLAGS_N:
        self.ops = [self.ops[0].ops[2]]
      elif self.type == DEFLAGS_V:
        self.ops = [self.ops[0].ops[3]]
      self.type = VAR
      simplifications += 'deflagflags '
    if self.type == VAR and isinstance(self.ops[0], int):
      self.type = CONST
      simplifications += 'varconst '
    if self.type in [STORE, STORE16, STORE32]:
      if isinstance(self.ops[1], int) and isinstance(self.ops[2], Expr):
        inside = self.ops[2]
        if inside.type == ADD and len(inside.ops) == 2 and isinstance(inside.ops[1], int):
          self.ops[1] += inside.ops[1]
          inside.type = VAR
          inside.ops = [inside.ops[0]]
          simplifications += 'ptrsum '
    if self.type == COMPARE_EQ and isinstance(self.ops[0], Expr) and isinstance(self.ops[1], Expr) and self.ops[0].ops == self.ops[1].ops:
      if self.ops[0].type == COMPARE_LT and self.ops[1].type == SUBFLAGS_V:
        self.type = COMPARE_GES
        self.ops = self.ops[0].ops
        simplifications += 'signedge '
    if self.type == AND and isinstance(self.ops[0], Expr) and isinstance(self.ops[1], Expr) and self.ops[0].ops == self.ops[1].ops:
      if self.ops[0].type == COMPARE_NE and self.ops[1].type == COMPARE_GES:
        self.type = COMPARE_GTS
        self.ops = self.ops[0].ops
        simplifications += 'signedgt '
    if self.type == COMPARE_NE and isinstance(self.ops[0], Expr) and isinstance(self.ops[1], Expr) and self.ops[0].ops == self.ops[1].ops:
      if self.ops[0].type == COMPARE_LT and self.ops[1].type == SUBFLAGS_V:
        self.type = COMPARE_LTS
        self.ops = self.ops[0].ops
        simplifications += 'signedlt '
    if self.type == OR and isinstance(self.ops[0], Expr) and isinstance(self.ops[1], Expr) and self.ops[0].ops == self.ops[1].ops:
      if self.ops[0].type == COMPARE_EQ and self.ops[1].type == COMPARE_LTS:
        self.type = COMPARE_LES
        self.ops = self.ops[0].ops
        simplifications += 'signedle '
    if self.type == MOVFLAGS_Z:
      self.type = NOT
      self.ops = [self.ops[0]]
      simplifications += 'movz '
    if nowop != str(self):
      debug(EXPR, 4, 'simplified', nowop, 'to', self, 'using', simplifications)
      self.simplify()
