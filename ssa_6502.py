# ssa_6502.py
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

from debug import *
from ssa import SSAStatement, SSADef, IMPURE, ASGN, BRANCH_COND, RETURN, CALL, ENDLESS_LOOP
from insn import OPC_OUTOFRANGE
from expr import *

def translate(self, ctx, insn, sp, end_bp, bp):
  debug(SSA, 2, 'translating', insn, hex(insn.bytes[0]))

  def chain_flags_ldimm(st, imm):
    st1 = SSAStatement(SSADef(ctx, 'N'), ASGN)
    st.chain(ctx, st1)
    st = st1
    if imm > 0x80:
      st.expr = Expr(CONST, [1])
    else:
      st.expr = Expr(CONST, [0])
    st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN)
    st.chain(ctx, st2)
    st = st2
    if imm:
      st.expr = Expr(CONST, [0])
    else:
      st.expr = Expr(CONST, [1])
    return st

  def chain_flags_ld(st, reg):
    op = SSADef.cur(ctx, 'A')
    st1 = SSAStatement(SSADef(ctx, 'N'), ASGN)
    st.chain(ctx, st1)
    st = st1
    st.expr = Expr(COMPARE_GE, [Expr(VAR, [op]), 0x80])
    st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN)
    st.chain(ctx, st2)
    st = st2
    st.expr = Expr(NOT, [op])
    return st

  def chain_flags_incdec(st, reg):
    st1 = SSAStatement(SSADef(ctx, 'Z'), ASGN)
    st.chain(ctx, st1)
    st = st1
    st.expr = Expr(NOT, [reg])
    st2 = SSAStatement(SSADef(ctx, 'N'), ASGN)
    st.chain(ctx, st2)
    st = st2
    st.expr = Expr(COMPARE_GE, [reg, 0x80])
    return st

  def chain_flags_bit(st, mem):
    st1 = SSAStatement(SSADef(ctx, 'N'), ASGN)
    st.chain(ctx, st1)
    st = st1
    st.expr = Expr(BITFLAGS_N, [SSADef.cur(ctx, 'M', mem)])
    st2 = SSAStatement(SSADef(ctx, 'V'), ASGN)
    st.chain(ctx, st2)
    st = st2
    st.expr = Expr(BITFLAGS_V, [SSADef.cur(ctx, 'M', mem)])
    return st

  def chain_flags_or(st, reg, op):
    st1 = SSAStatement(SSADef(ctx, 'N'), ASGN)
    st.chain(ctx, st1)
    st = st1
    st.expr = Expr(ORFLAGS_N, [reg, op])
    st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN)
    st.chain(ctx, st2)
    st = st2
    st.expr = Expr(ORFLAGS_Z, [reg, op])
    return st

  def chain_flags_shl(st, reg, res):
    st1 = SSAStatement(SSADef(ctx, 'N'), ASGN)
    st.chain(ctx, st1)
    st1.expr = Expr(SHFLAGS_N, [res])
    st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN)
    st1.chain(ctx, st2)
    st2.expr = Expr(NOT, [res])
    st3 = SSAStatement(SSADef(ctx, 'C'), ASGN)
    st2.chain(ctx, st3)
    st3.expr = Expr(SHLFLAGS_C, [reg])
    return st3

  def chain_flags_shr(st, reg, res):
    st1 = SSAStatement(SSADef(ctx, 'N'), ASGN)
    st.chain(ctx, st1)
    st1.expr = Expr(SHFLAGS_N, [res])
    st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN)
    st1.chain(ctx, st2)
    st2.expr = Expr(NOT, [res])
    st3 = SSAStatement(SSADef(ctx, 'C'), ASGN)
    st2.chain(ctx, st3)
    st3.expr = Expr(AND, [reg, 1])
    return st3

  def chain_flags_and(st, reg, op):
    st1 = SSAStatement(SSADef(ctx, 'N'), ASGN, Expr(ANDFLAGS_N, [reg, op]))
    st.chain(ctx, st1)
    st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN, Expr(ANDFLAGS_Z, [reg, op]))
    st1.chain(ctx, st2)
    return st2

  def chain_flags_eor(st, reg, op):
    st1 = SSAStatement(SSADef(ctx, 'N'), ASGN, Expr(EORFLAGS_N, [reg, op]))
    st.chain(ctx, st1)
    st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN, Expr(EORFLAGS_Z, [reg, op]))
    st1.chain(ctx, st2)
    return st2

  def chain_flags_adc(st, reg1, reg2, reg3):
    st1 = SSAStatement(SSADef(ctx, 'N'), ASGN, Expr(ADCFLAGS_N, [reg1, reg2, reg3]))
    st.chain(ctx, st1)
    st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN, Expr(ADCFLAGS_Z, [reg1, reg2, reg3]))
    st1.chain(ctx, st2)
    st3 = SSAStatement(SSADef(ctx, 'C'), ASGN, Expr(ADCFLAGS_C, [reg1, reg2, reg3]))
    st2.chain(ctx, st3)
    st4 = SSAStatement(SSADef(ctx, 'V'), ASGN, Expr(ADCFLAGS_V, [reg1, reg2, reg3]))
    st3.chain(ctx, st4)
    return st4

  def chain_flags_sbb(st, reg1, reg2, reg3):
    st1 = SSAStatement(SSADef(ctx, 'N'), ASGN, Expr(SBBFLAGS_N, [reg1, reg2, reg3]))
    st.chain(ctx, st1)
    st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN, Expr(SBBFLAGS_Z, [reg1, reg2, reg3]))
    st1.chain(ctx, st2)
    st3 = SSAStatement(SSADef(ctx, 'C'), ASGN, Expr(SBBFLAGS_C, [reg1, reg2, reg3]))
    st2.chain(ctx, st3)
    st4 = SSAStatement(SSADef(ctx, 'V'), ASGN, Expr(SBBFLAGS_V, [reg1, reg2, reg3]))
    st3.chain(ctx, st4)
    return st4

  def chain_flags_rol(st, reg1, res):
    st1 = SSAStatement(SSADef(ctx, 'N'), ASGN, Expr(SHFLAGS_N, [res]))
    st.chain(ctx, st1)
    st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN, Expr(NOT, [res]))
    st1.chain(ctx, st2)
    st3 = SSAStatement(SSADef(ctx, 'C'), ASGN, Expr(SHR, [reg1, 7]))
    st2.chain(ctx, st3)
    return st3

  def chain_flags_ror(st, reg1, res):
    st1 = SSAStatement(SSADef(ctx, 'N'), ASGN, Expr(SHFLAGS_N, [res]))
    st.chain(ctx, st1)
    st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN, Expr(NOT, [res]))
    st1.chain(ctx, st2)
    st3 = SSAStatement(SSADef(ctx, 'C'), ASGN, Expr(AND, [reg1, 1]))
    st2.chain(ctx, st3)
    return st3

  def emit_flags_subimm(st, reg, imm):
    st.dest = [SSADef(ctx, 'C')]
    st.op = ASGN
    st.expr = Expr(COMPARE_GE, [SSADef.cur(ctx, reg), imm])
    st1 = SSAStatement(SSADef(ctx, 'N'), ASGN, Expr(COMPARE_LT, [SSADef.cur(ctx, reg), imm]))
    st.chain(ctx, st1)
    st2 = SSAStatement(SSADef(ctx, 'Z'), ASGN, Expr(COMPARE_EQ, [SSADef.cur(ctx, reg), imm]))
    st1.chain(ctx, st2)
    return st2

  # normally, add() will follow the flow of the machine code instructions;
  # if we know better (such as with branches with constant conditions), we
  # can put a list of successor instructions here
  next = None

  st = SSAStatement()

  debug(SSA, 2, 'translating', insn, hex(insn.bytes[0]), 'to', st.num)

  opc = insn.bytes[0]

  if insn == None:
    return None
  
  st_start = st
  self.ssa_for_insn[insn] = st
  st.insn = insn

  if len(insn.comefrom) > 1:
    debug(SSA, 3, 'phiing')
    for g in ctx.local_indices.values():
      st.dest = [SSADef(ctx, g.type, g.addr)]
      st.op = ASGN
      st.expr = Expr(PHI, [g])
      for h in insn.comefrom:
        if h in self.last_ssa_for_insn:
          #print('reaching from', self.last_ssa_for_insn[h], [str(x) + '(' + repr(x) + ')' for x in self.last_ssa_for_insn[h].reaching])
          for i in self.last_ssa_for_insn[h].reaching:
            if i.type == g.type and i.addr == g.addr and not i in st.expr.ops:
              st.expr.ops += [i]
      st1 = SSAStatement()
      st.chain(ctx, st1)
      st = st1
  
  def abs():
    return insn.bytes[1] + (insn.bytes[2] << 8)
  def zp():
    return insn.bytes[1]
  def imm():
    return insn.bytes[1]

  def do_st_abs(reg):
    if self.is_io(abs()):
      st.op = IMPURE
      st.dest = []
      st.expr = Expr(IOOUT, [abs(), SSADef.cur(ctx, reg)])
      st.expr.dont_propagate = True
      st.expr.dont_eliminate = True
    else:
      st.dest = [SSADef(ctx, 'M', abs())]
      st.op = ASGN
      st.expr = Expr(VAR, [SSADef.cur(ctx, reg)])

  def do_ld_abs(reg):
    nonlocal st
    st.dest = [SSADef(ctx, reg)]
    st.op = ASGN
    if self.is_io(abs()):
      st.expr = Expr(IOIN, [abs()])
      st.expr.dont_propagate = True
      st.expr.dont_eliminate = True
    else:
      st.expr = Expr(VAR, [SSADef.cur(ctx, 'M', abs())])
    st = chain_flags_ld(st, reg)

  def do_st_xy(src, addr, reg):
    st.dest = []
    st.op = IMPURE
    if self.is_io(addr):
      st.expr = Expr(IOOUT, [Expr(ADD, [addr, SSADef.cur(ctx, reg)]), SSADef.cur(ctx, src)])
      st.expr.dont_propagate = True
      st.expr.dont_eliminate = True
    else:
      st.expr = Expr(STORE, [SSADef.cur(ctx, src), addr, SSADef.cur(ctx, reg)])

  def do_ld_xy(dst, addr, reg):
    nonlocal st
    st.dest = [SSADef(ctx, dst)]
    st.op = ASGN
    if self.is_io(addr):
      st.expr = Expr(IOIN, [Expr(ADD, [addr, SSADef.cur(ctx, reg)])])
      st.expr.dont_propagate = True
      st.expr.dont_eliminate = True
    else:
      st.expr = Expr(LOAD, [addr, SSADef.cur(ctx, reg)])
    st = chain_flags_ld(st, dst)

  def do_branch(flag, positive):
    nonlocal next, st
    if insn.fake_branch >= 0:
      next = [insn.next[insn.fake_branch]]
      st.op = ASGN
      st.expr = Expr(NOP, [0])
    else:
      st.op = BRANCH_COND
      st.expr = Expr(VAR if positive else NOT, [SSADef.cur(ctx, flag)])
    st.dest = []
  
  if opc == 0x00:	# BRK
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(INTRINSIC, ['brk', imm()])
  elif opc == 0x01:	# ORA (zp,X)
    addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    current_mem = Expr(LOAD, [addr, 0])
    current_a = SSADef.cur(ctx, 'A')
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(OR, [current_a, current_mem])
    st = chain_flags_or(st, current_a, current_mem)
  elif opc == 0x05:	# ORA zp
    current_a = SSADef.cur(ctx, 'A')
    st.op = ASGN
    st.expr = Expr(OR, [current_a, SSADef.cur(ctx, 'M', zp())])
    st.dest = [SSADef(ctx, 'A')]
    st = chain_flags_or(st, current_a, SSADef.cur(ctx, 'M', zp()))
  elif opc == 0x06:	# ASL zp
    current_mem = SSADef.cur(ctx, 'M', zp())
    st.op = ASGN
    st.expr = Expr(SHL, [current_mem, 1])
    st.dest = [SSADef(ctx, 'M', zp())]
    st = chain_flags_shl(st, current_mem, st.expr)
  elif opc == 0x08:	# PHP
    st.dest = [SSADef(ctx, 's', sp)]
    sp -= 1
    st.op = ASGN
    st.expr = Expr(FLAGS, [SSADef.cur(ctx, 'C'),SSADef.cur(ctx, 'Z'),SSADef.cur(ctx, 'N'),SSADef.cur(ctx, 'V')])
  elif opc == 0x09:	# ORA imm
    current_a = SSADef.cur(ctx, 'A')
    st.op = ASGN
    st.expr = Expr(OR, [current_a, imm()])
    st.dest = [SSADef(ctx, 'A')]
    st = chain_flags_or(st, current_a, imm())
  elif opc == 0x0a:	# ASL A
    current_a = SSADef.cur(ctx, 'A')
    st.op = ASGN
    st.expr = Expr(SHL, [current_a, 1])
    st.dest = [SSADef(ctx, 'A')]
    st = chain_flags_shl(st, current_a, st.expr)
  elif opc == 0x0d:	# ORA abs
    current_a = SSADef.cur(ctx, 'A')
    st.op = ASGN
    st.expr = Expr(OR, [current_a, SSADef.cur(ctx, 'M', abs())])
    st.dest = [SSADef(ctx, 'A')]
    st = chain_flags_or(st, current_a, SSADef.cur(ctx, 'M', abs()))
  elif opc == 0x0e:	# ASL abs
    current_mem = SSADef.cur(ctx, 'M', abs())
    st.op = ASGN
    st.expr = Expr(SHL, [current_mem, 1])
    st.dest = [SSADef(ctx, 'M', abs())]
    st = chain_flags_shl(st, current_mem, st.expr)
  elif opc == 0x10:	# BPL dd
    do_branch('N', False)
  elif opc == 0x11:	# ORA (zp),Y
    current_a = SSADef.cur(ctx, 'A')
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    operand = Expr(LOAD, [SSADef.cur(ctx, 'M', zp()), SSADef.cur(ctx, 'Y')])
    st.expr = Expr(OR, [current_a, operand])
    st = chain_flags_or(st, current_a, operand)
  elif opc == 0x15:	# ORA zp,X
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    st.expr = Expr(OR, [current_a, current_mem])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st = chain_flags_or(st, current_a, current_mem)
  elif opc == 0x16:	# ASL zp,X
    current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    shlex = Expr(SHL, [current_mem, 1])
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(STORE, [shlex, zp(), SSADef.cur(ctx, 'X')])
    st = chain_flags_shl(st, current_mem, shlex)
  elif opc == 0x18:	# CLC
    st.dest = [SSADef(ctx, 'C')]
    st.expr = Expr(CONST, [0])
    st.op = ASGN
  elif opc == 0x19:	# ORA abs,Y
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'Y')])
    st.expr = Expr(OR, [current_a, current_mem])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st = chain_flags_or(st, current_a, current_mem)
  elif opc == 0x1d:	# ORA abs,X
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
    st.expr = Expr(OR, [current_a, current_mem])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st = chain_flags_or(st, current_a, current_mem)
  elif opc == 0x1e:	# ASL abs,X
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
    shlex = Expr(SHL, [current_mem, 1])
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(STORE, [shlex, abs(), SSADef.cur(ctx, 'X')])
    st = chain_flags_shl(st, current_mem, shlex)
  elif opc == 0x20:	# JSR abs
    st.expr = Expr(ARGS, [abs()] + self.fun_args(ctx, insn.next[1], st, sp))
    st.dest = self.fun_returns(ctx, insn.next[1], st)
    st.op = CALL
  elif opc == 0x21:	# AND (zp,X)
    addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    current_mem = Expr(LOAD, [addr, 0])
    current_a = SSADef.cur(ctx, 'A')
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(AND, [current_a, current_mem])
    st = chain_flags_and(st, current_a, current_mem)
  elif opc == 0x24:	# BIT zp
    st.expr = Expr(COMPARE_EQ, [Expr(AND, [SSADef.cur(ctx, 'A'), SSADef.cur(ctx, 'M', zp())]), 0])
    st.dest = [SSADef(ctx, 'Z')]
    st.op = ASGN
    st = chain_flags_bit(st, zp())
  elif opc == 0x25:	# AND zp
    current_a = SSADef.cur(ctx, 'A')
    current_mem = SSADef.cur(ctx, 'M', zp())
    st.expr = Expr(AND, [current_a, current_mem])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st = chain_flags_and(st, current_a, current_mem)
  elif opc == 0x26:	# ROL zp
    current_mem = SSADef.cur(ctx, 'M', zp())
    current_c = SSADef.cur(ctx, 'C')
    st.op = ASGN
    st.expr = Expr(OR, [Expr(SHL, [current_mem, 1]), current_c])
    st.expr.dont_propagate = True
    st.dest = [SSADef(ctx, 'M', zp())]
    st = chain_flags_rol(st, current_mem, st.expr)
  elif opc == 0x28:	# PLP
    sp += 1
    flags = SSADef.cur(ctx, 's', sp)
    for i in [('C', DEFLAGS_C), ('Z', DEFLAGS_Z), ('N', DEFLAGS_N), ('V', DEFLAGS_V)]:
      st.op = ASGN
      st.dest = [SSADef(ctx, i[0])]
      st.expr = Expr(i[1], [flags])
      if i[0] != 'V':
        st1 = SSAStatement()
        st.chain(ctx, st1)
        st = st1
  elif opc == 0x29:	# AND imm
    current_a = SSADef.cur(ctx, 'A')
    st.op = ASGN
    st.expr = Expr(AND, [current_a, imm()])
    st.dest = [SSADef(ctx, 'A')]
    st = chain_flags_and(st, current_a, imm())
  elif opc == 0x2a:	# ROL A
    current_a = SSADef.cur(ctx, 'A')
    current_c = SSADef.cur(ctx, 'C')
    st.op = ASGN
    st.expr = Expr(OR, [Expr(SHL, [current_a, 1]), current_c])
    st.expr.dont_propagate = True
    st.dest = [SSADef(ctx, 'A')]
    st = chain_flags_rol(st, current_a, st.expr)
  elif opc == 0x2c:	# BIT abs
    st.expr = Expr(COMPARE_EQ, [Expr(AND, [SSADef.cur(ctx, 'A'), SSADef.cur(ctx, 'M', abs())]), 0])
    st.dest = [SSADef(ctx, 'Z')]
    st.op = ASGN
    st = chain_flags_bit(st, abs())
  elif opc == 0x2d:	# AND abs
    current_a = SSADef.cur(ctx, 'A')
    current_mem = SSADef.cur(ctx, 'M', abs())
    st.expr = Expr(AND, [current_a, current_mem])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st = chain_flags_and(st, current_a, current_mem)
  elif opc == 0x2e:	# ROL abs
    current_mem = SSADef.cur(ctx, 'M', abs())
    current_c = SSADef.cur(ctx, 'C')
    st.op = ASGN
    st.expr = Expr(OR, [Expr(SHL, [current_mem, 1]), current_c])
    st.expr.dont_propagate = True
    st.dest = [SSADef(ctx, 'M', abs())]
    st = chain_flags_rol(st, current_mem, st.expr)
  elif opc == 0x30:	# BMI dd
    do_branch('N', True)
  elif opc == 0x31:	# AND (zp),Y
    current_mem = Expr(LOAD, [SSADef.cur(ctx, 'M', zp()), SSADef.cur(ctx, 'Y')])
    current_a = SSADef.cur(ctx, 'A')
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(AND, [current_a, current_mem])
    st = chain_flags_and(st, current_a, current_mem)
  elif opc == 0x35:	# AND zp,X
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    st.expr = Expr(AND, [current_a, current_mem])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st = chain_flags_and(st, current_a, current_mem)
  elif opc == 0x36:	# ROL zp,X
    current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    current_c = SSADef.cur(ctx, 'C')
    st.op = IMPURE
    rolex = Expr(OR, [Expr(SHL, [current_mem, 1]), current_c])
    rolex.dont_propagate = True
    st.dest = []
    st.expr = Expr(STORE, [rolex, zp(), SSADef.cur(ctx, 'X')])
    st = chain_flags_rol(st, current_mem, rolex)
  elif opc == 0x38:	# SEC
    st.dest = [SSADef(ctx, 'C')]
    st.op = ASGN
    st.expr = Expr(CONST, [1])
  elif opc == 0x39:	# AND abs,Y
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'Y')])
    st.expr = Expr(AND, [current_a, current_mem])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st = chain_flags_and(st, current_a, current_mem)
  elif opc == 0x3d:	# AND abs,X
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
    st.expr = Expr(AND, [current_a, current_mem])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st = chain_flags_and(st, current_a, current_mem)
  elif opc == 0x3e:	# ROL abs,X
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
    current_c = SSADef.cur(ctx, 'C')
    st.op = IMPURE
    rolex = Expr(OR, [Expr(SHL, [current_mem, 1]), current_c])
    rolex.dont_propagate = True
    st.dest = []
    st.expr = Expr(STORE, [rolex, abs(), SSADef.cur(ctx, 'X')])
    st = chain_flags_rol(st, current_mem, rolex)
  elif opc == 0x40:	# RTI
    st.dest = []
    st.op = RETURN
    st.expr = None
    st.add_comment('RTI')
  elif opc == 0x41:	# EOR (zp,X)
    addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    current_mem = Expr(LOAD, [addr, 0])
    current_a = SSADef.cur(ctx, 'A')
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(EOR, [current_a, current_mem])
    st = chain_flags_eor(st, current_a, current_mem)
  elif opc == 0x45:	# EOR zp
    current_a = SSADef.cur(ctx, 'A')
    current_mem = SSADef.cur(ctx, 'M', zp())
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(EOR, [current_a, current_mem])
    st = chain_flags_eor(st, current_a, current_mem)
  elif opc == 0x46:	# LSR zp
    current_mem = SSADef.cur(ctx, 'M', zp())
    st.op = ASGN
    st.expr = Expr(SHR, [current_mem, 1])
    st.dest = [SSADef(ctx, 'M', zp())]
    st = chain_flags_shr(st, current_mem, st.expr)
  elif opc == 0x48:	# PHA
    st.dest = [SSADef(ctx, 's', sp)]
    sp -= 1
    st.op = ASGN
    st.expr = Expr(VAR, [SSADef.cur(ctx, 'A')])
  elif opc == 0x49:	# EOR imm
    current_a = SSADef.cur(ctx, 'A')
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(EOR, [current_a, imm()])
    st = chain_flags_eor(st, current_a, imm())
  elif opc == 0x4a:	# LSR A
    current_a = SSADef.cur(ctx, 'A')
    st.op = ASGN
    st.expr = Expr(SHR, [current_a, 1])
    st.dest = [SSADef(ctx, 'A')]
    st = chain_flags_shr(st, current_a, st.expr)
  elif opc == 0x4c:	# JMP
    if insn.next[0] == insn:
      st.op = ENDLESS_LOOP
      st.expr = None
      st.dest = []
    elif insn.next[0].sym != None:
      # tail call
      if insn.next[0] == ctx.graph.first_insn:
        debug(SSA, 2, 'tail recursion at', insn)
        # recursion causes us grief with args/rets, so we avoid it if
        # possible; here, we can just let the jmp run its course
        st.op = ASGN
        st.dest = []
        st.expr = Expr(NOP, [0])
      else:
        debug(SSA, 2, 'tail call at', insn)
        st.expr = Expr(ARGS, [abs()] + self.fun_args(ctx, insn.next[0], st, sp))
        st.dest = self.fun_returns(ctx, insn.next[0], st)
        st.op = CALL
        st1 = SSAStatement()
        st.chain(ctx, st1)
        st = st1
        st.dest = []
        st.op = RETURN
        st.expr = None
        next = []
    else:
      st.op = ASGN
      st.dest = []
      st.expr = Expr(NOP, [0])
  elif opc == 0x4d:	# EOR abs
    current_a = SSADef.cur(ctx, 'A')
    current_mem = SSADef.cur(ctx, 'M', abs())
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(EOR, [current_a, current_mem])
    st = chain_flags_eor(st, current_a, current_mem)
  elif opc == 0x4e:	# LSR abs
    current_mem = SSADef.cur(ctx, 'M', abs())
    st.op = ASGN
    st.expr = Expr(SHR, [current_mem, 1])
    st.dest = [SSADef(ctx, 'M', abs())]
    st = chain_flags_shr(st, current_mem, st.expr)
  elif opc == 0x50:	# BVC
    do_branch('V', False)
  elif opc == 0x51:	# EOR (zp),Y
    current_a = SSADef.cur(ctx, 'A')
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    operand = Expr(LOAD, [SSADef.cur(ctx, 'M', zp()), SSADef.cur(ctx, 'Y')])
    st.expr = Expr(EOR, [current_a, operand])
    st = chain_flags_eor(st, current_a, operand)
  elif opc == 0x55:	# EOR zp,X
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    st.expr = Expr(EOR, [current_a, current_mem])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st = chain_flags_eor(st, current_a, current_mem)
  elif opc == 0x56:	# LSR zp,X
    current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    shrex = Expr(SHR, [current_mem, 1])
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(STORE, [shrex, zp(), SSADef.cur(ctx, 'X')])
    st = chain_flags_shr(st, current_mem, shrex)
  elif opc == 0x58:	# CLI
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(INTRINSIC, ['cli'])
  elif opc == 0x59:	# EOR abs,Y
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'Y')])
    st.expr = Expr(EOR, [current_a, current_mem])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st = chain_flags_eor(st, current_a, current_mem)
  elif opc == 0x5d:	# EOR abs,X
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
    st.expr = Expr(EOR, [current_a, current_mem])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st = chain_flags_eor(st, current_a, current_mem)
  elif opc == 0x5e:	# LSR abs,X
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
    shrex = Expr(SHR, [current_mem, 1])
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(STORE, [shrex, abs(), SSADef.cur(ctx, 'X')])
    st = chain_flags_shr(st, current_mem, shrex)
  elif opc == 0x60:	# RTS
    st.dest = []
    st.op = RETURN
    st.expr = None
  elif opc == 0x61:	# ADC (zp,X)
    addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [addr, 0])
    current_c = SSADef.cur(ctx, 'C')
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(ADD, [current_a, current_mem, current_c])
    st = chain_flags_adc(st, current_a, current_mem, current_c)
  elif opc == 0x65:	# ADC zp
    current_a = SSADef.cur(ctx, 'A')
    current_mem = SSADef.cur(ctx, 'M', zp())
    current_c = SSADef.cur(ctx, 'C')
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(ADD, [current_a, current_mem, current_c])
    st = chain_flags_adc(st, current_a, current_mem, current_c)
  elif opc == 0x66:	# ROR zp
    current_mem = SSADef.cur(ctx, 'M', zp())
    current_c = SSADef.cur(ctx, 'C')
    st.op = ASGN
    st.expr = Expr(OR, [Expr(SHR, [current_mem, 1]), Expr(SHL, [current_c, 7])])
    st.expr.dont_propagate = True
    st.dest = [SSADef(ctx, 'M', zp())]
    st = chain_flags_ror(st, current_mem, st.expr)
  elif opc == 0x68:	# PLA
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    sp += 1
    st.expr = Expr(VAR, [SSADef.cur(ctx, 's', sp)])
    st = chain_flags_ld(st, 'A')
  elif opc == 0x69:	# ADC imm
    current_a = SSADef.cur(ctx, 'A')
    current_c = SSADef.cur(ctx, 'C')
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(ADD, [current_a, imm(), current_c])
    st = chain_flags_adc(st, current_a, imm(), current_c)
  elif opc == 0x6a:	# ROR A
    current_a = SSADef.cur(ctx, 'A')
    current_c = SSADef.cur(ctx, 'C')
    st.op = ASGN
    st.expr = Expr(OR, [Expr(SHR, [current_a, 1]), Expr(SHL, [current_c, 7])])
    st.expr.dont_propagate = True
    st.dest = [SSADef(ctx, 'A')]
    st = chain_flags_ror(st, current_a, st.expr)
  elif opc == 0x6c:	# JMP ind
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(INTRINSIC, ['jmp', SSADef.cur(ctx, 'M', abs())])
    st.add_comment('XXX: indirect jump not implemented yet')
  elif opc == 0x6d:	# ADC abs
    current_a = SSADef.cur(ctx, 'A')
    current_mem = SSADef.cur(ctx, 'M', abs())
    current_c = SSADef.cur(ctx, 'C')
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(ADD, [current_a, current_mem, current_c])
    st = chain_flags_adc(st, current_a, current_mem, current_c)
  elif opc == 0x6e:	# ROR abs
    current_mem = SSADef.cur(ctx, 'M', abs())
    current_c = SSADef.cur(ctx, 'C')
    st.op = ASGN
    st.expr = Expr(OR, [Expr(SHR, [current_mem, 1]), Expr(SHL, [current_c, 7])])
    st.expr.dont_propagate = True
    st.dest = [SSADef(ctx, 'M', abs())]
    st = chain_flags_ror(st, current_mem, st.expr)
  elif opc == 0x70:	# BVS dd
    do_branch('V', True)
  elif opc == 0x71:	# ADC (zp),Y
    current_a = SSADef.cur(ctx, 'A')
    current_c = SSADef.cur(ctx, 'C')
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    operand = Expr(LOAD, [SSADef.cur(ctx, 'M', zp()), SSADef.cur(ctx, 'Y')])
    st.expr = Expr(ADD, [current_a, operand, current_c])
    st = chain_flags_adc(st, current_a, operand, current_c)
  elif opc == 0x75:	# ADC zp,X
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    current_c = SSADef.cur(ctx, 'C')
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(ADD, [current_a, current_mem, current_c])
    st = chain_flags_adc(st, current_a, current_mem, current_c)
  elif opc == 0x76:	# ROR zp,X
    current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    current_c = SSADef.cur(ctx, 'C')
    st.op = IMPURE
    rorex = Expr(OR, [Expr(SHR, [current_mem, 1]), Expr(SHL, [current_c, 7])])
    rorex.dont_propagate = True
    st.dest = []
    st.expr = Expr(STORE, [rorex, zp(), SSADef.cur(ctx, 'X')])
    st = chain_flags_ror(st, current_mem, rorex)
  elif opc == 0x78: 	# SEI
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(INTRINSIC, ['sei'])
  elif opc == 0x79:	# ADC abs,Y
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'Y')])
    current_c = SSADef.cur(ctx, 'C')
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(ADD, [current_a, current_mem, current_c])
    st = chain_flags_adc(st, current_a, current_mem, current_c)
  elif opc == 0x7d:	# ADC abs,X
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
    current_c = SSADef.cur(ctx, 'C')
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(ADD, [current_a, current_mem, current_c])
    st = chain_flags_adc(st, current_a, current_mem, current_c)
  elif opc == 0x7e:	# ROR abs,X
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
    current_c = SSADef.cur(ctx, 'C')
    st.op = IMPURE
    rorex = Expr(OR, [Expr(SHR, [current_mem, 1]), Expr(SHL, [current_c, 7])])
    rorex.dont_propagate = True
    st.dest = []
    st.expr = Expr(STORE, [rorex, abs(), SSADef.cur(ctx, 'X')])
    st = chain_flags_ror(st, current_mem, rorex)
  elif opc == 0x81:	# STA (zp,X)
    addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    st.op = IMPURE
    st.dest = []
    st.expr = Expr(STORE, [SSADef.cur(ctx, 'A'), addr, 0])
  elif opc == 0x84:	# STY zp
    st.dest = [SSADef(ctx, 'M', zp())]
    st.op = ASGN
    st.expr = Expr(VAR, [SSADef.cur(ctx, 'Y')])
  elif opc == 0x85:	# STA zp
    st.dest = [SSADef(ctx, 'M', zp())]
    st.op = ASGN
    st.expr = Expr(VAR, [SSADef.cur(ctx, 'A')])
  elif opc == 0x86:	# STX zp
    st.dest = [SSADef(ctx, 'M', zp())]
    st.op = ASGN
    st.expr = Expr(VAR, [SSADef.cur(ctx, 'X')])
  elif opc == 0x88:	# DEY
    st.expr = Expr(SUB, [SSADef.cur(ctx, 'Y'), 1])
    st.dest = [SSADef(ctx, 'Y')]
    st.op = ASGN
    st = chain_flags_incdec(st, SSADef.cur(ctx, 'Y'))
  elif opc == 0x8a:	# TXA
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(VAR, [SSADef.cur(ctx, 'X')])
    st = chain_flags_ld(st, 'A')
  elif opc == 0x8c:	# STY abs
    do_st_abs('Y')
  elif opc == 0x8d:	# STA abs
    do_st_abs('A')
  elif opc == 0x8e:	# STX abs
    do_st_abs('X')
  elif opc == 0x90:	# BCC dd
    do_branch('C', False)
  elif opc == 0x91:	# STA (zp),Y
    current_ind = SSADef.cur(ctx, 'M', zp())
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(STORE, [SSADef.cur(ctx, 'A'), current_ind, SSADef.cur(ctx, 'Y')])
  elif opc == 0x94:	# STY zp,X
    do_st_xy('Y', zp(), 'X')
  elif opc == 0x95:	# STA zp,X
    do_st_xy('A', zp(), 'X')
  elif opc == 0x96:	# STX zp,Y
    do_st_xy('X', zp(), 'Y')
  elif opc == 0x98:	# TYA
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(VAR, [SSADef.cur(ctx, 'Y')])
    st = chain_flags_ld(st, 'A')
  elif opc == 0x99:	# STA abs,Y
    do_st_xy('A', abs(), 'Y')
  elif opc == 0x9a:	# TXS
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(INTRINSIC, ['setsp', SSADef.cur(ctx, 'X')])
  elif opc == 0x9d:	# STA abs,X
    do_st_xy('A', abs(), 'X')
  elif opc == 0xa0:	# LDY imm
    st.dest = [SSADef(ctx, 'Y')]
    st.op = ASGN
    st.expr = Expr(CONST, [imm()])
    st = chain_flags_ldimm(st, imm())
  elif opc == 0xa1:	# LDA (zp,X)
    addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(VAR, [Expr(LOAD, [addr, 0])])
    st = chain_flags_ld(st, 'A')
  elif opc == 0xa2:	# LDX imm
    st.dest = [SSADef(ctx, 'X')]
    st.op = ASGN
    st.expr = Expr(CONST, [imm()])
    st = chain_flags_ldimm(st, imm())
  elif opc == 0xa4:	# LDY zp
    st.dest = [SSADef(ctx, 'Y')]
    st.op = ASGN
    st.expr = Expr(VAR, [SSADef.cur(ctx, 'M', zp())])
    st = chain_flags_ld(st, 'Y')
  elif opc == 0xa5:	# LDA zp
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(VAR, [SSADef.cur(ctx, 'M', zp())])
    st = chain_flags_ld(st, 'A')
  elif opc == 0xa6:	# LDX zp
    st.dest = [SSADef(ctx, 'X')]
    st.op = ASGN
    st.expr = Expr(VAR, [SSADef.cur(ctx, 'M', zp())])
    st = chain_flags_ld(st, 'X')
  elif opc == 0xa8:	# TAY
    st.dest = [SSADef(ctx, 'Y')]
    st.op = ASGN
    st.expr = Expr(VAR, [SSADef.cur(ctx, 'A')])
    st = chain_flags_ld(st, 'Y')
  elif opc == 0xa9:	# LDA imm
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(CONST, [imm()])
    st = chain_flags_ldimm(st, imm())
  elif opc == 0xaa:	# TAX
    st.dest = [SSADef(ctx, 'X')]
    st.op = ASGN
    st.expr = Expr(VAR, [SSADef.cur(ctx, 'A')])
    st = chain_flags_ld(st, 'X')
  elif opc == 0xac:	# LDY abs
    do_ld_abs('Y')
  elif opc == 0xad:	# LDA abs
    do_ld_abs('A')
  elif opc == 0xae:	# LDX abs
    do_ld_abs('X')
  elif opc == 0xb0:	# BCS dd
    do_branch('C', True)
  elif opc == 0xb1:	# LDA (zp),Y
    current_ind = SSADef.cur(ctx, 'M', zp())
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(LOAD, [current_ind, SSADef.cur(ctx, 'Y')])
    st = chain_flags_ld(st, 'A')
  elif opc == 0xb4:	# LDY zp,X
    do_ld_xy('Y', zp(), 'X')
  elif opc == 0xb5:	# LDA zp,X
    do_ld_xy('A', zp(), 'X')
  elif opc == 0xb6:	# LDX zp,Y
    do_ld_xy('X', zp(), 'Y')
  elif opc == 0xb8:	# CLV
    st.op = ASGN
    st.dest = [SSADef(ctx, 'V')]
    st.expr = Expr(CONST, [0])
  elif opc == 0xb9:	# LDA abs,Y
    do_ld_xy('A', abs(), 'Y')
  elif opc == 0xba:	# TSX
    st.dest = [SSADef(ctx, 'X')]
    st.op = ASGN
    st.expr = Expr(INTRINSIC, ['getsp'])
  elif opc == 0xbc:	# LDY abs,X
    do_ld_xy('Y', abs(), 'X')
  elif opc == 0xbd:	# LDA abs,X
    do_ld_xy('A', abs(), 'X')
  elif opc == 0xbe:	# LDX abs,Y
    do_ld_xy('X', abs(), 'Y')
  elif opc == 0xc0:	# CPY imm
    st = emit_flags_subimm(st, 'Y', imm())
  elif opc == 0xc1:	# CMP (zp,X)
    addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    st = emit_flags_subimm(st, 'A', Expr(LOAD, [addr, 0]))
  elif opc == 0xc4:	# CPY zp
    st = emit_flags_subimm(st, 'Y', SSADef.cur(ctx, 'M', zp()))
  elif opc == 0xc5:	# CMP zp
    st = emit_flags_subimm(st, 'A', SSADef.cur(ctx, 'M', zp()))
  elif opc == 0xc6:	# DEC zp
    current_mem = SSADef.cur(ctx, 'M', zp())
    st.expr = Expr(SUB, [current_mem, 1])
    st.dest = [SSADef(ctx, 'M', zp())]
    st.op = ASGN
    st = chain_flags_incdec(st, SSADef.cur(ctx, 'M', zp()))
  elif opc == 0xc8:	# INY
    st.expr = Expr(ADD, [SSADef.cur(ctx, 'Y'), 1])
    st.dest = [SSADef(ctx, 'Y')]
    st.op = ASGN
    st = chain_flags_incdec(st, SSADef.cur(ctx, 'Y'))
  elif opc == 0xc9:	# CMP imm
    st = emit_flags_subimm(st, 'A', imm())
  elif opc == 0xca:	# DEX
    current_x = SSADef.cur(ctx, 'X')
    st.expr = Expr(SUB, [current_x, 1])
    st.dest = [SSADef(ctx, 'X')]
    st.op = ASGN
    st = chain_flags_incdec(st, SSADef.cur(ctx, 'X'))
  elif opc == 0xcc:	# CPY abs
    st = emit_flags_subimm(st, 'Y', SSADef.cur(ctx, 'M', abs()))
  elif opc == 0xcd:	# CMP abs
    st = emit_flags_subimm(st, 'A', SSADef.cur(ctx, 'M', abs()))
  elif opc == 0xce:	# DEC abs
    current_mem = SSADef.cur(ctx, 'M', abs())
    st.expr = Expr(SUB, [current_mem, 1])
    st.dest = [SSADef(ctx, 'M', abs())]
    st.op = ASGN
    st = chain_flags_incdec(st, SSADef.cur(ctx, 'M', abs()))
  elif opc == 0xd0:	# BNE dd
    do_branch('Z', False)
  elif opc == 0xd1:	# CMP (zp),Y
    operand = Expr(LOAD, [SSADef.cur(ctx, 'M', zp()), SSADef.cur(ctx, 'Y')])
    st = emit_flags_subimm(st, 'A', operand)
  elif opc == 0xd5:	# CMP zp,X
    st = emit_flags_subimm(st, 'A', Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')]))
  elif opc == 0xd6:	# DEC zp,X
    current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    subex = Expr(SUB, [current_mem, 1])
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(STORE, [subex, zp(), SSADef.cur(ctx, 'X')])
    st = chain_flags_incdec(st, subex)
  elif opc == 0xd8:	# CLD
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(INTRINSIC, ['cld'])
    st.add_comment('XXX: CLD unimplemented')
  elif opc == 0xd9:	# CMP abs,Y
    st = emit_flags_subimm(st, 'A', Expr(LOAD, [abs(), SSADef.cur(ctx, 'Y')]))
  elif opc == 0xdd:	# CMP abs,X
    st = emit_flags_subimm(st, 'A', Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')]))
  elif opc == 0xde:	# DEC abs,X
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
    subex = Expr(SUB, [current_mem, 1])
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(STORE, [subex, abs(), SSADef.cur(ctx, 'X')])
    st = chain_flags_incdec(st, subex)
  elif opc == 0xe0:	# CPX imm
    st = emit_flags_subimm(st, 'X', imm())
  elif opc == 0xe1:	# SBC (zp,X)
    addr = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [addr, 0])
    current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(SUB, [current_a, current_mem, current_borrow])
    st = chain_flags_sbb(st, current_a, current_mem, current_borrow)
  elif opc == 0xe4:	# CPX zp
    st = emit_flags_subimm(st, 'X', SSADef.cur(ctx, 'M', zp()))
  elif opc == 0xe5:	# SBC zp
    current_a = SSADef.cur(ctx, 'A')
    current_mem = SSADef.cur(ctx, 'M', zp())
    current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(SUB, [current_a, current_mem, current_borrow])
    st = chain_flags_sbb(st, current_a, current_mem, current_borrow)
  elif opc == 0xe6:	# INC zp
    current_mem = SSADef.cur(ctx, 'M', zp())
    st.expr = Expr(ADD, [current_mem, 1])
    st.dest = [SSADef(ctx, 'M', zp())]
    st.op = ASGN
    st = chain_flags_incdec(st, SSADef.cur(ctx, 'M', zp()))
  elif opc == 0xe8:	# INX
    current_x = SSADef.cur(ctx, 'X')
    st.expr = Expr(ADD, [current_x, 1])
    st.dest = [SSADef(ctx, 'X')]
    st.op = ASGN
    st = chain_flags_incdec(st, SSADef.cur(ctx, 'X'))
  elif opc == 0xe9:	# SBC imm
    current_a = SSADef.cur(ctx, 'A')
    current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(SUB, [current_a, imm(), current_borrow])
    st = chain_flags_sbb(st, current_a, imm(), current_borrow)
  elif opc == 0xea:	# NOP
    st.op = ASGN
    st.dest = []
    st.expr = Expr(NOP, [0])
  elif opc == 0xec:	# CPX abs
    st = emit_flags_subimm(st, 'X', SSADef.cur(ctx, 'M', abs()))
  elif opc == 0xed:	# SBC abs
    current_a = SSADef.cur(ctx, 'A')
    current_mem = SSADef.cur(ctx, 'M', abs())
    current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(SUB, [current_a, current_mem, current_borrow])
    st = chain_flags_sbb(st, current_a, current_mem, current_borrow)
  elif opc == 0xee:	# INC abs
    current_mem = SSADef.cur(ctx, 'M', abs())
    st.expr = Expr(ADD, [current_mem, 1])
    st.dest = [SSADef(ctx, 'M', abs())]
    st.op = ASGN
    st = chain_flags_incdec(st, SSADef.cur(ctx, 'M', abs()))
  elif opc == 0xf0:	# BEQ dd
    do_branch('Z', True)
  elif opc == 0xf1:	# SBC (zp),Y
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [SSADef.cur(ctx, 'M', zp()), SSADef.cur(ctx, 'Y')])
    current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(SUB, [current_a, current_mem, current_borrow])
    st = chain_flags_sbb(st, current_a, current_mem, current_borrow)
  elif opc == 0xf5:	# SBC zp,X
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(SUB, [current_a, current_mem, current_borrow])
    st = chain_flags_sbb(st, current_a, current_mem, current_borrow)
  elif opc == 0xf6:	# INC zp,X
    current_mem = Expr(LOAD, [zp(), SSADef.cur(ctx, 'X')])
    result = Expr(ADD, [current_mem, 1])
    st.expr = Expr(STORE, [result, zp(), SSADef.cur(ctx, 'X')])
    st.dest = []
    st.op = IMPURE
    st = chain_flags_incdec(st, result)
  elif opc == 0xf8:	# SED
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(INTRINSIC, ['sed'])
    st.add_comment('XXX: SED unimplemented')
  elif opc == 0xf9:	# SBC abs,Y
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'Y')])
    current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(SUB, [current_a, current_mem, current_borrow])
    st = chain_flags_sbb(st, current_a, current_mem, current_borrow)
  elif opc == 0xfd:	# SBC abs,X
    current_a = SSADef.cur(ctx, 'A')
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
    current_borrow = Expr(SUB, [1, SSADef.cur(ctx, 'C')])
    st.dest = [SSADef(ctx, 'A')]
    st.op = ASGN
    st.expr = Expr(SUB, [current_a, current_mem, current_borrow])
    st = chain_flags_sbb(st, current_a, current_mem, current_borrow)
  elif opc == 0xfe:	# INC abs,X
    current_mem = Expr(LOAD, [abs(), SSADef.cur(ctx, 'X')])
    result = Expr(ADD, [current_mem, 1])
    st.expr = Expr(STORE, [result, abs(), SSADef.cur(ctx, 'X')])
    st.dest = []
    st.op = IMPURE
    st = chain_flags_incdec(st, result)
  elif opc == OPC_OUTOFRANGE:
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(INTRINSIC, ['thunk', insn.addr])
  elif opc in [      0x02, 0x03, 0x04, 0x07,             0x0b, 0x0c,       0x0f,
                     0x12, 0x13, 0x14, 0x17,       0x1a, 0x1b, 0x1c,       0x1f,
                     0x22, 0x23,       0x27,             0x2b,             0x2f,
                     0x32, 0x33, 0x34, 0x37,       0x3a, 0x3b, 0x3c,       0x3f,
                     0x42, 0x43, 0x44, 0x47,             0x4b,             0x4f,
                     0x52, 0x53, 0x54, 0x57,       0x5a, 0x5b, 0x5c,       0x5f,
                     0x62, 0x63, 0x64, 0x67,             0x6b,             0x6f,
                     0x72, 0x73, 0x74, 0x77,       0x7a, 0x7b, 0x7c,       0x7f,
               0x80, 0x82, 0x83,       0x87, 0x89,       0x8b,             0x8f,
                     0x92, 0x93,       0x97,             0x9b, 0x9c, 0x9e, 0x9f,
                           0xa3,       0xa7,             0xab,             0xaf,
                     0xb2, 0xb3,       0xb7,             0xbb,             0xbf,
                     0xc2, 0xc3,       0xc7,             0xcb,             0xcf,
                     0xd2, 0xd3, 0xd4, 0xd7,       0xda, 0xdb, 0xdc,       0xdf,
                     0xe2, 0xe3,       0xe7,             0xeb,             0xef,
                     0xf2, 0xf3, 0xf4, 0xf7,       0xfa, 0xfb, 0xfc,       0xff]:
    # illegal opcode
    # XXX: add switch to allow 'useful' illegal opcodes
    st.op = IMPURE
    st.expr = Expr(INTRINSIC, ['illegal', opc])
    st.dest = []
    st.add_comment('XXX: unimplemented illegal opcode')
  else:
    raise InternalError('unknown opcode ' + hex(opc))

  # all current indices are reaching, with the exception of anything
  # below the stack pointer
  st.reaching = []
  for i in ctx.local_indices.values():
    if i.type != 's':# or i.addr > sp:
      st.reaching += [i]

  self.last_ssa_for_insn[insn] = st
  return (st_start, st, sp, bp, end_bp, next)
