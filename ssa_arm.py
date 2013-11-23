# ssa_arm.py
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
from ssa import SSAStatement, SSADef, IMPURE, ASGN, BRANCH_COND, RETURN, CALL
from expr import *
from insn import OPC_OUTOFRANGE
from util import *

def translate(self, ctx, insn, sp, end_bp, bp):

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
  

  def rot_imm(imm8, rs):
    return ((imm8 >> rs * 2) | (imm8 << (32 - rs * 2))) & 0xffffffff

  def do_ld_abs(reg, addr, size):
    nonlocal st
    st.op = ASGN
    if self.is_io(addr):
      if size == 1:
        op = IOIN
      elif size == 2:
        op = IOIN16
      else:
        op = IOIN32
      st.expr = Expr(op, [addr])
      st.expr.dont_propagate = True
      st.expr.dont_eliminate = True
    else:
      if size == 4:
        st.expr = Expr(VAR, [SSADef.cur(ctx, 'Mw', addr)])
      elif size == 2:
        st.expr = Expr(VAR, [SSADef.cur(ctx, 'Mh', addr)])
      elif size == 1:
        st.expr = Expr(VAR, [SSADef.cur(ctx, 'M', addr)])
      else:
        raise InternalError('unhandled size ' + str(size))
    st.dest = [SSADef(ctx, reg)]

  
  def do_ld_reg(dst, off, reg, size):
    nonlocal st
    st.op = ASGN
    # XXX: convert to IOIN after constant prop
    if size == 1:
      st.expr = Expr(LOAD, [off, SSADef.cur(ctx, reg)])
    elif size == 2:
      st.expr = Expr(LOAD16, [off, SSADef.cur(ctx, reg)])
    elif size == 4:
      st.expr = Expr(LOAD32, [off, SSADef.cur(ctx, reg)])
    else:
      raise InternalError('unhandled size ' + str(size))
    st.dest = [SSADef(ctx, dst)]

  def do_st_abs(reg, addr, size):
    if self.is_io(addr):
      st.op = IMPURE
      if size == 4:
        op = IOOUT32
      elif size == 2:
        op = IOOUT16
      else:
        op = IOOUT
      st.expr = Expr(op, [SSADef.cur(ctx, reg), addr])
      st.expr.dont_propagate = True
      st.expr.dont_eliminate = True
      st.dest = []
    else:
      st.op = ASGN
      st.expr = Expr(VAR, [SSADef.cur(ctx, reg)])
      if size == 4:
        pref = 'Mw'
      elif size == 2:
        pref = 'Mh'
      elif size == 1:
        pref = 'M'
      else:
        raise InternalError('unhandled size ' + str(size))
      st.dest = [SSADef(ctx, pref, addr)]

  def do_st_reg(src, off, reg, size):
    st.dest = []
    st.op = IMPURE
    # XXX: convert to IOOUT after constant prop
    if size == 4:
      op = STORE32
    elif size == 2:
      op = STORE16
    elif size == 1:
      op = STORE
    else:
      raise InternalError('unhandled size ' + str(size))
    st.expr = Expr(op, [SSADef.cur(ctx, src), off, SSADef.cur(ctx, reg)])

  def do_ld_stack(dst, off, size):
    nonlocal sp, st
    st.op = ASGN
    st.expr = Expr(VAR, [SSADef.cur(ctx, 's', off+sp)])
    st.dest = [SSADef(ctx, dst)]
  
  def do_st_stack(src, off, size):
    nonlocal sp, st
    st.op = ASGN
    st.expr = Expr(VAR, [SSADef.cur(ctx, src)])
    st.dest = [SSADef(ctx, 's', off+sp)]

  def creg(num):
    nonlocal sp
    if num == 13:
      return Expr(AUTO, [sp, -1])
    elif num == 15:
      return insn.addr + 8
    else:
      return SSADef.cur(ctx, 'R'+str(num))

  def get_rm():
    if insn.shift == 0:
      op = SHL
    elif insn.shift == 1:
      op = SHR
    elif insn.shift == 2:
      op = ASR
    else:
      op = ROR
    if insn.shift_rot == 1:
      # rs
      return Expr(op, [creg(insn.rm), creg(insn.rs)])
    else:
      # imm
      return Expr(op, [creg(insn.rm), insn.shift_bits])

  if insn.bytes[0] != OPC_OUTOFRANGE and insn.cond < 0xe or insn.artificial_branch != -1:
    debug(SSA, 5, "conditional", insn, hex(insn.artificial_branch))
    # conditional
    st.op = BRANCH_COND

    if insn.cond == 0:
      st.expr = Expr(VAR, [SSADef.cur(ctx, 'Z')])
    elif insn.cond == 1:
      st.expr = Expr(NOT, [SSADef.cur(ctx, 'Z')])
    elif insn.cond == 2:
      st.expr = Expr(VAR, [SSADef.cur(ctx, 'C')])
    elif insn.cond == 3:
      st.expr = Expr(NOT, [SSADef.cur(ctx, 'C')])
    elif insn.cond == 4:
      st.expr = Expr(VAR, [SSADef.cur(ctx, 'N')])
    elif insn.cond == 5:
      st.expr = Expr(NOT, [SSADef.cur(ctx, 'N')])
    elif insn.cond == 8:
      st.expr = Expr(AND, [SSADef.cur(ctx, 'C'), Expr(NOT, [SSADef.cur(ctx, 'Z')])])
    elif insn.cond == 9:
      st.expr = Expr(OR, [Expr(NOT, [SSADef.cur(ctx, 'C')]), SSADef.cur(ctx, 'Z')])
    elif insn.cond == 0xa:
      st.expr = Expr(COMPARE_EQ, [SSADef.cur(ctx, 'N'), SSADef.cur(ctx, 'V')])
    elif insn.cond == 0xb:
      st.expr = Expr(COMPARE_NE, [SSADef.cur(ctx, 'N'), SSADef.cur(ctx, 'V')])
    elif insn.cond == 0xc:
      st.expr = Expr(AND, [
        Expr(NOT, [SSADef.cur(ctx, 'Z')]),
        Expr(COMPARE_EQ, [SSADef.cur(ctx, 'N'), SSADef.cur(ctx, 'V')])
      ])
    elif insn.cond == 0xd:
      st.expr = Expr(OR, [
        SSADef.cur(ctx, 'Z'),
        Expr(COMPARE_NE, [SSADef.cur(ctx, 'N'), SSADef.cur(ctx, 'V')])
      ])
    else:
      raise InternalError('unsupported condition')

    assert(insn.op & 0xf0 == 0xa0 or insn.artificial_branch != -1)

  if insn.bytes[0] == OPC_OUTOFRANGE:
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(INTRINSIC, ['thunk', insn.addr])
  elif insn.cond == 0xf:	# NV predicate
      debug(SSA, 5, "NV predicate")
      st.dest = []
      st.op = ASGN
      st.expr = Expr(NOP, [0])
  elif insn.op & 0xf0 == 0xa0:	# B
      debug(SSA, 5, "branch")
      if insn.cond == 0xe:
        debug(SSA, 5, "unconditional branch")
        st.op = ASGN
        st.dest = []
        st.expr = Expr(NOP, [0])
  elif insn.op & 0xf1 == 0xe0:	# MCR
      debug(SSA, 5, "mcr")
      st.op = IMPURE
      st.dest = []
      st.expr = Expr(INTRINSIC, ['mcr'])
  elif insn.op & 0xf1 == 0xe1:	# MRC
      debug(SSA, 5, "mrc")
      st.op = ASGN
      st.dest = [SSADef(ctx, 'R'+str(insn.rd))]
      st.expr = Expr(INTRINSIC, ['mrc'])
  elif insn.op & 0xc0 == 0x40:	# LDR/STR rd,[rn,+-#imm12 / rm <> shift] pre/post
      if insn.op & 0x20:
        # register offset
        if insn.op & 0x08 == 0x08:
          off = get_rm()
        else:
          off = Expr(SUB, [0, get_rm()])
      else:
        # immediate offset
        if insn.op & 0x08 == 0x08:
          off = insn.imm12
        else:
          off = -insn.imm12
      if insn.op & 0x04 == 0x04:
        size = 1
      else:
        size = 4
      if insn.fixed_mem != -1:
        assert(insn.rn != 13)
        debug(SSA, 6, 'transing fixed mem insn', insn)
        if insn.op & 1:
          do_ld_abs('R'+str(insn.rd), insn.fixed_mem, size)
        else:
          do_st_abs('R'+str(insn.rd), insn.fixed_mem, size)
      else:
        if insn.op & 1 == 1 and insn.rd == 15:
          # PC load
          if insn.rn == 15:
            # decoded already in insn.py
            st.dest = []
            st.op = ASGN
            st.expr = Expr(NOP, [0])
          else:
            st.dest = []
            st.op = IMPURE
            st.expr = Expr(INTRINSIC, ['set_pc', insn.rn, off])
        else:
          if insn.op & 0x10:	# pre indexing
            noff = off
          else:
            noff = 0
          if insn.rn == 15:
            if insn.op & 1:
              do_ld_abs('R'+str(insn.rd), insn.addr + 8 + noff, size)
            else:
              do_st_abs('R'+str(insn.rd), insn.addr + 8 + noff, size)
          elif insn.rn == 13:
            if insn.op & 1:
              do_ld_stack('R'+str(insn.rd), noff, size)
            else:
              do_st_stack('R'+str(insn.rd), noff, size)
          else:
            if insn.op & 1:
              do_ld_reg('R'+str(insn.rd), noff, 'R'+str(insn.rn), size)
            else:
              do_st_reg('R'+str(insn.rd), noff, 'R'+str(insn.rn), size)
      if insn.op & 2 == 2 or insn.op & 0x10 == 0:	# write back or post indexing
        if insn.rn == 13:
          sp += off
        else:
          st1 = SSAStatement()
          st.chain(ctx, st1)
          st = st1
          st.op = ASGN
          st.expr = Expr(ADD, [creg(insn.rn), off])
          st.dest = [SSADef(ctx, 'R'+str(insn.rn))]
  elif insn.op & 0xe4 == 4 and insn.imm8 & 0x90 == 0x90:	# LDRH/STRH rd, [rn, +-immWEIRD]
      imm = insn.rm | (insn.rs >> 4)
      if insn.op & 0x08 == 0:
        imm = -imm
      if insn.fixed_mem != -1:
        assert(insn.rn != 13)
        debug(SSA, 6, 'transing fixed mem insn', insn)
        if insn.op & 1:
          do_ld_abs('R'+str(insn.rd), insn.fixed_mem, 2)
        else:
          do_st_abs('R'+str(insn.rd), insn.fixed_mem, 2)
      else:
        if insn.op & 0x10:	# pre indexing
          noff = imm
        else:
          noff = 0
        if insn.rn == 13:
          if insn.op & 1:
            do_ld_stack('R'+str(insn.rd), noff, 2)
          else:
            do_st_stack('R'+str(insn.rd), noff, 2)
        else:
          if insn.op & 1:
            do_ld_reg('R'+str(insn.rd), noff, 'R'+str(insn.rn), 2)
          else:
            do_st_reg('R'+str(insn.rd), noff, 'R'+str(insn.rn), 2)
      if insn.op & 2:	# write back
        st1 = SSAStatement()
        st.chain(ctx, st1)
        st = st1
        st.op = ASGN
        st.expr = Expr(ADD, [creg(insn.rn), imm])
        st.dest = [SSADef(ctx, 'R'+str(insn.rn))]
  elif insn.op == 0x32:	# MSR CPSR_f, rm
      debug(SSA, 5, "MSR CPSR_f, rm")
      st.op = IMPURE
      st.dest = []
      st.expr = Expr(INTRINSIC, ['msr_cpsr_f', creg(insn.rm)])
  elif insn.bytes[0] & 0x0fbf0fff == 0x010f0000:	# MRS
      st.op = ASGN
      st.expr = Expr(INTRINSIC, ['mrs', insn.op & 4])
      st.dest = [SSADef(ctx, 'R'+str(insn.rd))]
  elif insn.bytes[0] & 0x0fbffff0 == 0x0129f000:	# MSR
      st.op = IMPURE
      st.expr = Expr(INTRINSIC, ['msr', insn.op & 4, creg(insn.rm)])
      st.dest = []
  elif insn.op & 0xf0 == 0xb0:	# BL off24
    st.expr = Expr(ARGS, [insn.addr + 8 + insn.off24 * 4] + self.fun_args(ctx, insn.next[1], st, sp))
    st.dest = self.fun_returns(ctx, insn.next[1], st)
    st.op = CALL
  elif insn.op & 0xe0 == 0x80:	# LDM/STM
    # XXX: PSR/force user?
    off = 0
    if insn.op & 0x08 == 0x08:
      inc = 4
      regs = range(0, 16)
    else:
      inc = -4
      regs = range(15, -1, -1)
    st.op = None
    do_return = False
    for i in regs:
      if insn.reglist & (1 << i):
        if insn.op & 0x10 == 0x10:	# pre indexing
          off += inc
        if st.op != None:
          st1 = SSAStatement()
          st.chain(ctx, st1)
          st = st1
        if insn.op & 1:	# LDM
          if i == 15:
            # XXX: only if [rn,off] is r14
            do_return = True
          elif insn.rn == 13:
            do_ld_stack('R'+str(i), off, 4)
          else:
            do_ld_reg('R'+str(i), off, 'R'+str(insn.rn), 4)
        else:
          if insn.rn == 13:
            do_st_stack('R'+str(i), off, 4)
          else:
            do_st_reg('R'+str(i), off, 'R'+str(insn.rn), 4)
        if insn.op & 0x10 != 0x10:	# post indexing
          off += inc
    if insn.op & 2 == 2:	# write back
        if insn.rn == 13:
          sp += off
          if end_bp == 0:
            end_bp = sp
        else:
          if st.op != None:
            st1 = SSAStatement()
            st.chain(ctx, st1)
            st = st1
          st.op = ASGN
          st.expr = Expr(ADD, [creg(insn.rn), off])
          st.dest = [SSADef(ctx, 'R'+str(insn.rn))]
    if do_return:
      if st.op != None:
        st1 = SSAStatement()
        st.chain(ctx, st1)
        st = st1
      st.op = RETURN
      st.expr = None
      st.dest = []
  elif insn.bytes[0] & 0x0ffffff0 == 0x012fff10:	# BX rm
    if insn.rm == 14:
      # XXX: only if R14 is unassigned
      st.dest = []
      st.op = RETURN
      st.expr = None
    else:
      st.dest = []
      st.op = IMPURE
      st.expr = Expr(INTRINSIC, ['bx', creg(insn.rm)])
      st.add_comment('XXX: indirect jump not implemented yet')
  elif insn.bytes[0] & 0xffffff0 == 0x012fff30:	# BLX rm
    st.dest = []
    st.op = IMPURE
    st.expr = Expr(INTRINSIC, ['blx', creg(insn.rm)])
    st.add_comment('XXX: indirect call not implemented yet')
  elif insn.op & 0xc0 == 0x00:	# ALU rd, rn, #imm8 <> rs / rm <> shift
      alu_op = (insn.op >> 1) & 0xf
      debug(SSA, 5, "alu op", alu_op)
      if insn.rd == 13 and alu_op in [2, 4]:
        assert(insn.op & 0x20 == 0x20)	# immediate
        if alu_op == 4:
          # XXX: hack: assume conditional adds to SP only occur in epilogs and ignore them
          # otherwise our stack pointer tracking gets mangled
          if insn.cond == 0xe:
            sp += rot_imm(insn.imm8, insn.rs)
        else:
          sp -= rot_imm(insn.imm8, insn.rs)
        st.op = ASGN
        st.dest = []
        st.expr = Expr(NOP, [sp])
      else:
        st.op = None
        if insn.op & 0x20 == 0:
          imm = get_rm()
        else:
          imm = rot_imm(insn.imm8, insn.rs)

        if alu_op in [2, 3, 6, 7, 0xa]:
          op = SUB
          op_c = COMPARE_GE
          op_z = COMPARE_EQ
          op_n = COMPARE_LT
          op_v = SUBFLAGS_V
        elif alu_op == 0 or alu_op == 8 or alu_op == 0xe:
          op = AND
          op_c = ANDFLAGS_C
          op_z = ANDFLAGS_Z
          op_n = ANDFLAGS_N
          op_v = None
        elif alu_op == 1 or alu_op == 9:
          op = EOR
          op_c = EORFLAGS_C
          op_z = EORFLAGS_Z
          op_n = EORFLAGS_N
          op_v = None
        elif alu_op == 4 or alu_op == 5 or alu_op == 0xb:
          op = ADD
          op_c = ADDFLAGS_C
          op_z = ADDFLAGS_Z
          op_n = ADDFLAGS_N
          op_v = ADDFLAGS_V
        elif alu_op == 0xc:
          op = OR
          op_c = ORFLAGS_C
          op_z = ORFLAGS_Z
          op_n = ORFLAGS_N
          op_v = None
        else:	# MOV, MVN
          op = CONST
          op_c = MOVFLAGS_C
          op_z = MOVFLAGS_Z
          op_n = MOVFLAGS_N
          op_v = None

        reverse = False
        if alu_op == 3 or alu_op == 7:	# RSB, RSC
          reverse = True

        if alu_op == 0xf or alu_op == 0xe:	# BIC, MVN
          imm = Expr(INV, [imm])

        if op == CONST:
          if insn.op & 0x20 == 0:
            st.expr = imm
          else:
            st.expr = Expr(CONST, [imm])
        else:
          if insn.rn == 13 and insn.op & 0x20 == 0x20 and alu_op == 4:
            st.expr = Expr(AUTO, [sp + imm, -1])
            # XXX: may be better to do this on CALL
            if sp + imm < bp:
              bp = sp + imm
          elif insn.rn == 13 and insn.op & 0x20 == 0x20 and alu_op == 2:
            st.expr = Expr(AUTO, [sp - imm, -1])
            if sp - imm < bp:
              bp = sp - imm
          else:
            op1 = creg(insn.rn)
            if reverse:
              op2 = op1
              op1 = imm
            else:
              op2 = imm

            if alu_op == 5:	# ADC
              st.expr = Expr(op, [op1, op2, SSADef.cur(ctx, 'C')])
            elif alu_op == 6 or alu_op == 7:	# SBC, RSC
              st.expr = Expr(ADD, [Expr(op, [op1, op2, 1]), SSADef.cur(ctx, 'C')])
            else:
              st.expr = Expr(op, [op1, op2])

        if alu_op in [0, 1, 2, 3, 4, 5, 6, 7, 0xc, 0xd, 0xe, 0xf] and insn.rd != 15:
          st.op = ASGN
          st.dest = [SSADef(ctx, 'R'+str(insn.rd))]
        if insn.rd == 15:
          st.op = IMPURE
          st.expr = Expr(INTRINSIC, ['set_pc', st.expr])
          st.dest = []

        if insn.op & 1:	# set flags
          alu_expr = st.expr
          if st.op == ASGN:
            st1 = SSAStatement()
            st.chain(ctx, st1)
            st = st1
          st.op = ASGN
          st.expr = Expr(op_c, copy(alu_expr.ops))
          st.dest = [SSADef(ctx, 'C')]
          st1 = SSAStatement()
          st.chain(ctx, st1)
          st = st1
          st.op = ASGN
          st.expr = Expr(op_z, copy(alu_expr.ops))
          st.dest = [SSADef(ctx, 'Z')]
          st1 = SSAStatement()
          st.chain(ctx, st1)
          st = st1
          st.op = ASGN
          st.expr = Expr(op_n, copy(alu_expr.ops))
          st.dest = [SSADef(ctx, 'N')]
          if op_v:
            st1 = SSAStatement()
            st.chain(ctx, st1)
            st = st1
            st.op = ASGN
            st.expr = Expr(op_v, copy(alu_expr.ops))
            st.dest = [SSADef(ctx, 'V')]
          
        
  else:
    raise InternalError('unknown op ' + hex(insn.op))

  # all current indices are reaching, with the exception of anything
  # below the stack pointer
  st.reaching = []
  for i in ctx.local_indices.values():
    if not (i.type == 's' and i.addr < 0): #True: #i.type != 's':# or i.addr > sp:
      st.reaching += [i]

  self.last_ssa_for_insn[insn] = st
  debug(SSA, 6, "st_end in translate", st)
  return (st_start, st, sp, bp, end_bp, next)
