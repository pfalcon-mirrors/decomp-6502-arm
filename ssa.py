# ssa.py
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

from operator import attrgetter

from debug import *
from expr import *
from insn import OPC_OUTOFRANGE, MCodeGraph
from util import *
import struct
from config import *


ASGN = 0
BRANCH_COND = 1
CALL = 2
RETURN = 3
ENDLESS_LOOP = 4
IMPURE = 5	# operation with side-effects, leave it alone

ssacache = dict()
ssa_in_progress = set()

class SSAStatement:
  statement_count = 0
  def __init__(self, dest = None, op = None, expr = None):
    self.next = []
    self.comefrom = []
    self.op = op
    if dest == None:
      dest = []
    elif not isinstance(dest, list):
      dest = [dest]
    self.dest = dest
    self.expr = expr
    self.num = SSAStatement.statement_count
    self.insn = None
    self.reaching = []
    self.call_uses = None
    SSAStatement.statement_count += 1
    self.comment = []
    self.comment_once = []
    
  def desthasmem(self, saved_regs_off):
    for i in self.dest:
      if i.type == 's' and i.addr < saved_regs_off:
        # XXX: eventually, all stack locations should be considered non-memory
        return True
      if i.type[0] == 'M':
        return True
    return False
    
  def __str__(self):
    a = { ASGN: ':=',
          BRANCH_COND: 'bcc',
          CALL: 'call',
          RETURN: 'ret',
          ENDLESS_LOOP: 'eloop',
          IMPURE: 'impure',
        }
    s = str(self.num) + ' '
    if len(self.dest) == 1:
      s += str(self.dest[0]) + ' '
    elif len(self.dest) > 1:
      s += '[ '
      for i in self.dest:
        s += str(i) + ' '
      s += '] '
    if self.call_uses != None:
      s += '[ USED '
      for i in self.call_uses:
        s += str(i) + ' '
      s += '] '
    s += a[self.op] + ' '
    s += str(self.expr) + ' -> '
    for i in self.next:
      s += str(i.num) + ' '
    s += '<- '
    for i in self.comefrom:
      s += str(i.num) + ' '
    if self.insn:
      s += '{' + str(self.insn) + '}'
    if self.reaching and len(self.reaching) > 0 and self.op == RETURN:
      s += ' [ reaching '
      for i in self.reaching:
        s += str(i) + ' '
      s += ']'
    return s
  def chain(self, ctx, st1):
    self.next.append(st1)
    self.reaching = list(ctx.local_indices.values())
    st1.comefrom.append(self)
    if st1.insn == None:
      st1.insn = self.insn

  def add_comment(self, text, once = False):
    debug(SSA, 5, 'adding comment', text, once, 'to', self.num)
    if not once:
      if text not in self.comment:
        self.comment += [text]
    else:
      if text not in self.comment_once:
        self.comment_once += [text]

class SSADef:
  def __init__(self, ctx, dtype, addr=None, idx=None, dessa_tmp=False):
    self.type = dtype
    assert(isinstance(dtype, str))
    self.addr = addr
    key = (dtype, addr)

    if idx == None:
      try:
        self.idx = ctx.graph.indices[key].idx + 1
      except KeyError:
        self.idx = 1
    else:
      self.idx = idx
      if idx == 0 and ctx != None:
        ctx.graph.zeros[key] = self

    if ctx != None:
      ctx.local_indices[key] = self
    if ctx != None and ctx.graph != None:
      ctx.graph.indices[key] = self
    #print('adding', key, 'to index, now', len(graph.indices.values()), 'values,', len(set(graph.indices.values())), 'unique')
    self.define_statement = None
    self.dessa_name = None
    self.is_dessa_tmp = dessa_tmp
    self.data_type = SSAType()
    self.parent_def = None
    if dtype.startswith('ap'):
      debug(SSA, 6, "adding new def to stack objs")
      ctx.graph.stack_obj_defs.add(self)
      ctx.graph.stack_obj_ptrs.add(self.addr)
      self.data_type.type = SSAType.COMPOUND

  @staticmethod
  def cur(ctx, dtype, addr = None):
    key = (dtype, addr)
    try:
      ret = ctx.local_indices[key]
    except KeyError:
      # Only create a new zero-index def if there isn't one already.
      # If we don't check this, we get duplicate arguments.
      if key in ctx.graph.zeros:
        ret = ctx.graph.zeros[key]
      else:
        ret = SSADef(ctx, dtype, addr, 0)
      ctx.local_indices[key] = ret
    return ret
  
  def is_text(self):
    return self.type[0] == 'M' and \
           isinstance(self.addr, int) and \
           self.addr >= MCodeGraph._org and \
           self.addr < MCodeGraph._org + len(MCodeGraph._text)

  def __str__(self):
    s = self.type
    if self.addr != None:
      assert(isinstance(self.addr, int))
      s += hex(self.addr)
    s += '(' + str(self.idx) + ')'
    return s

class SSAType:
  UNKNOWN = 1
  SCALAR = 2
  DPOINTER = 3
  FPOINTER = 4
  COMPOUND = 5
  SIGNED = 6
  UNSIGNED = 7
  def __init__(self):
    self.type = SSAType.UNKNOWN
    self.size = 0
    self.signedness = SSAType.UNKNOWN
    self.members = None

import ssa_6502
import ssa_arm

fun_returns_d = dict()
fun_returns_tentative = set()
fun_args_d = dict()
fun_args_tentative = set()

class SSAGraph:
  class SSAifyContext:
    def __init__(self, graph, local_indices=None):
      self.graph = graph
      self._pass = graph._pass
      if local_indices == None:
        self.local_indices = dict()
        # XXX: This is a partial workaround for missing phi functions at
        # function entry points.  Actually, we'd have to define every single
        # memory location as well...
        for i in arch.registers:
          SSADef(self, i, idx = 0)
        for i in arch.flags:
          SSADef(self, i, idx = 0)
      else:
        self.local_indices = local_indices
    def copy(self):
      return SSAGraph.SSAifyContext(self.graph, self.local_indices.copy())

  def __init__(self, iomap, _pass):
    self.start = None
    self.insns = dict()
    self.ssa_for_insn = dict()
    self.last_ssa_for_insn = dict()
    self.ssa_counter = 0
    self.definitions = []
    self.first_insn = None
    self.indices = {}
    self.callers_graphs = []
    self.callers_st = []
    self.callee_graphs = []
    self.actual_returns = None
    self.blocks = None
    self.iomap = iomap
    self.origin = None
    self.base_ptr = 0
    self.end_base_ptr = 0
    self.stack_obj_ptrs = set()
    self.stack_obj_defs = set()
    if arch.name == '6502':
      self.translate = ssa_6502.translate
    elif arch.name == 'arm':
      self.translate = ssa_arm.translate
    else:
      raise InternalError('unknown arch ' + arch.name)
    # Definitions with index zero are implicitly created when used.
    # To make sure there is only one such definition per graph, we save
    # the first one created in a graph-wide dictionary and always
    # return this instance.
    self.zeros = dict()
    self._pass = _pass

  def dump(self, level, st = None, dumped = None):
    if not debug_enabled(level):
      return
    if st == None:
      st = self.start
      dumped = dict()

    debug(SSA, level, st)
    dumped[st] = True

    while st.next and len(st.next) == 1 and not st.next[0] in dumped:
      st = st.next[0]
      debug(SSA, level, st)
      dumped[st] = True

    if st.next:
      for i in st.next:
        if not i in dumped:
          self.dump(level, i, dumped)

  def add(self, insn, sp = 0, bp = 0, end_bp = 0, ctx = None):
    if ctx == None:
      ctx = SSAGraph.SSAifyContext(self)
    if self.first_insn == None:
      self.first_insn = insn
    if insn in self.ssa_for_insn:
      return self.ssa_for_insn[insn]
    (st_start, st_end, sp, bp, end_bp, next) = self.translate(self, ctx, insn, sp, end_bp, bp)
    if next == None:
      # default control flow, use the successors of the insn
      next = insn.next
    if bp < self.base_ptr:
      self.base_ptr = bp
    if end_bp < 0:
      self.end_base_ptr = end_bp
    if self.start == None:
      self.start = st_start
    if st_end != None and next:
      for i in next:
        if i in self.ssa_for_insn:
          self.update_phis(ctx, self.ssa_for_insn[i])
      
      for i in next:
        new_ctx = ctx.copy()
        next_statement = self.add(i, sp, bp, end_bp, new_ctx)
        st_end.chain(ctx, next_statement)
        if st_end.op == CALL:
          break

    return st_start

  def update_phis(self, ctx, st):
    debug(SSA, 3, 'updating phis for', st)
    while st.expr and st.expr.type == PHI:
      debug(SSA, 4, 'phi expr', st.expr)
      for d in st.dest:
        curd = SSADef.cur(ctx, d.type, d.addr)
        if curd.idx != d.idx and not curd in st.expr.ops:
          st.expr.ops += [curd]
          debug(SSA, 4, 'added phi', curd, 'to', st)
      st = st.next[0]
  
  def fun_returns(self, ctx, insn, st):
    if not insn in fun_returns_d:
      if insn in ssa_in_progress:
        debug(ARGRET, 1, 'function', hex(insn.addr), 'in progress, cannot get returns')
        fun_returns_tentative.add(insn.addr)
        return []
      ssacache[insn.addr] = ssaify(insn)
      debug(ARGRET, 4, 'ssaified', insn, 'to', ssacache[insn.addr])
    if ctx._pass == 2:
      debug(ARGRET, 4, 'adding', self, 'to callers_graph of', insn, repr(insn))
      ssacache[insn.addr].callers_graphs += [self]
      ssacache[insn.addr].callers_st += [st]
    if not ssacache[insn.addr] in self.callee_graphs:
      self.callee_graphs += [ssacache[insn.addr]]
    rets = fun_returns_d[insn]
    myrets = []
    for i in rets:
      if i.idx != 0:	# saveds are not returns
        myrets += [SSADef(ctx, i.type, i.addr)]
    return myrets
  
  def fun_args(self, ctx, insn, st, sp):
    if not insn in fun_args_d:
      if insn in ssa_in_progress:
        debug(ARGRET, 1, 'function', hex(insn.addr), 'in progress at', hex(st.insn.addr), ', cannot get arguments')
        fun_args_tentative.add(insn.addr)
        return []
      ssacache[insn.addr] = ssaify(insn, None, self.iomap)
    myargs = []
    for i in fun_args_d[insn]:
      if i.type == 's':
        myargs += [SSADef.cur(ctx, i.type, i.addr + sp)]
      else:
        myargs += [SSADef.cur(ctx, i.type, i.addr)]
    return myargs
  
  def getall(self, st = None, got = None, all = None):
    if st == None:
      st = self.start
      got = dict()
      all = []

    all += [st]
    got[st] = True
    
    while st.next and len(st.next) == 1 and not st.next[0] in got:
      st = st.next[0]
      all += [st]
      got[st] = True
      
    if st.next:
      for i in st.next:
        if not i in got:
          self.getall(i, got, all)
    return all

  def get_all_defs(self):
    defs = set()
    for i in self.getall():
      for j in i.dest:
        defs.add(j)
    return defs

  def dce(self):
    eliminated = True
    while eliminated:
      if self.actual_returns != None:
        definitions = self.actual_returns
      else:
        definitions = self.definitions
      
      alluses = []
      use_statements = dict()
      all = self.getall()
      for i in all:
        if i.expr:
          uses = i.expr.getallops()
          for j in uses:
            if isinstance(j, SSADef):
              alluses += [j]
              if j in use_statements:
                use_statements[j] += [i]
              else:
                use_statements[j] = [i]

      alluses += definitions
      
      debug(SSA, 3, 'alluses', len(alluses))
      alluses = set(alluses)
      debug(SSA, 3, 'alluses set', len(alluses))
      debug(SSA, 5, 'start', self.start)
      
      #print('DCE uses', [str(x) for x in alluses])
      eliminated = False
      for i in all:
        if i.op == ASGN and \
           ((not i.desthasmem(self.end_base_ptr)) or i.expr.type == PHI) and \
           len(set(i.dest) & alluses) == 0 and \
           len(set(i.dest) & set(definitions)) == 0 and \
           not i in i.next and not i.expr.dont_eliminate:
          debug(SSA, 4, 'eliminate', i.num)
          eliminated = True
          assert(len(i.next) == 1)
          if len(i.comefrom) > 0:
            # replace us with our successor in predecessors' next
            for j in i.comefrom:
              j.next = [i.next[0] if x == i else x for x in j.next]
          # remove ourselves from successor's comefrom
          if i in i.next[0].comefrom:
            i.next[0].comefrom.remove(i)
          # add our predecessors to successor's comefrom
          for j in i.comefrom:
            if not j in i.next[0].comefrom:
              i.next[0].comefrom += [j]
          if self.start == i:
            self.start = i.next[0]
        elif i.op == ASGN and i.expr.type == PHI and i.dest[0] in use_statements and len(set(i.dest) & set(definitions)) == 0:
          # eliminate phi loops
          # this function checks if a phi definition is used in any non-phi expression
          def has_non_phi_uses(df, done = None):
            if done == None:
              done = dict()
            if df in done:
              #print('already checked', df)
              return done[df]
            done[df] = False
            if not df in use_statements:
              #print('no uses found for', df)
              done[df] = False
              return False
            for j in use_statements[df]:
              #print('phicheck', j)
              if j.op != ASGN or (j.expr and j.expr.type != PHI):
                done[df] = True
                return True
              elif has_non_phi_uses(j.dest[0], done):
                  done[df] = True
                  return True
            done[df] = False
            return False

          if not has_non_phi_uses(i.dest[0]):
            debug(SSA, 4, 'eliminate phi-only', i.num)

            for j in use_statements[i.dest[0]]:
              # Remove the definition from all phi expressions it is used in.
              debug(SSA, 6, 'removing it from', j)
              j.expr.ops.remove(i.dest[0])
              # Doing this frequently produces empty phi functions without
              # any operands. These expressions make no sense, but are
              # expected to be eliminated in this or subsequent DCE runs.
              # It is, however, possible that propagation is performed
              # before that happens, and it would consider all such
              # definitions equivalent, messing the program up completely.
              if len(j.expr.ops) == 0:
                j.expr.dont_propagate = True

            eliminated = True
            i.dest = []
            i.expr.type = NOP
            i.expr.ops = [0]

        elif i.op == CALL:
          i.call_uses = []
          for j in i.dest:
            if j in alluses:
              i.call_uses += [j]
        
      #self.dump()
  
  def find_definitions(self, st = None, done = None):
    # definitions that may be returns
    self.definitions = []
    # all reaching definitions
    self.definitions_all = []
    for i in self.getall():
      if i.op == RETURN:
        for j in i.reaching:
          if not j in self.definitions and not j.type in arch.non_return_locs:
            self.definitions += [j]
          if not j in self.definitions_all:
            self.definitions_all += [j]

  def find_args(self):
    args = []
    for i in self.getall():
      if i.expr:
        for j in i.expr.getallops():
          if isinstance(j, SSADef) and j.idx == 0 and not j in args and not j.type in arch.non_arg_locs and not j.type == 'ap':
            args += [j]
    args.sort(key = attrgetter('type'))
    debug(ARGRET, 1, 'args:', [str(x) for x in args])
    fun_args_d[self.first_insn] = args
  
  def find_rets(self):
    if self.actual_returns != None:
      definitions = self.actual_returns
    else:
      definitions = self.definitions
    debug(ARGRET, 1, 'rets:', [str(x) for x in definitions])
    debug(ARGRET, 4, 'adding', self.first_insn, 'for', self, 'to fun_returns_d')
    fun_returns_d[self.first_insn] = definitions
  
  def dereach(self):
    for i in self.getall():
      if i.reaching and i.op != RETURN:
        i.reaching = None
  
  #@profile
  def propagate(self, _pass):
    uses = dict()
    uses_defs = dict()
    for k in self.getall():
      # get all expression operands
      if isinstance(k.expr, Expr):
        for l in k.expr.getallops():
          if isinstance(l, SSADef):
            #print('deeping', m, 'in', k)
            if l in uses:
              uses[l] += [k]
            else:
              uses[l] = [k]
      # get all dests
      for l in k.dest:
        if isinstance(l, SSADef):
          #print('deeping', m, 'in', k)
          if l in uses:
            uses[l] += [k]
          else:
            uses[l] = [k]
      # get all reachings
      if k.reaching != None:
        for l in k.reaching:
          if isinstance(l, SSADef):
            if l in uses_defs:
              uses_defs[l] += [k]
            else:
              uses_defs[l] = [k]

    for i in self.getall():
      # link to defining statement
      for j in i.dest:
        j.define_statement = i
      
      # remove duplicate args in phi functions
      if isinstance(i.expr, Expr) and i.expr.type == PHI and len(set(i.expr.ops)) != len(i.expr.ops):
        nops = []
        for j in i.expr.ops:
          if not j in nops:
            nops += [j]
        i.expr.ops = nops
      
      # eliminate phi functions with only one operand
      if isinstance(i.expr, Expr) and i.expr.type == PHI and len(i.expr.ops) == 1:
        debug(SSA, 3, 'dephiing', i)
        i.expr.type = NOP
        # rename uses of i.dest
        if i.dest[0] in uses:
          for k in uses[i.dest[0]]:
            # operands
            if isinstance(k.expr, Expr):
              if k.expr.type == PHI and k.dest[0] == i.expr.ops[0]:
                debug(SSA, 6, 'remove', i.dest[0], 'from phi', k)
                k.expr.remove(i.dest[0])
              else:
                k.expr.substitute(i.dest[0], i.expr.ops[0])
                debug(SSA, 6, 'subbing', i.dest[0], 'for', i.expr.ops[0], 'in', k)
                # Make sure to add the new definition to uses so it
                # can itself be replaced if necessary.
                if i.expr.ops[0] in uses:
                  uses[i.expr.ops[0]].append(k)
                else:
                  uses[i.expr.ops[0]] = [k]
        if i.dest[0] in uses_defs:
          for k in uses_defs[i.dest[0]]:
            # reachings
            if k.reaching and k.reaching != []:
              debug(SSA, 4, 'rereaching', i.dest[0], 'to', i.expr.ops[0], 'in', k)
              k.reaching = [x if x != i.dest[0] else i.expr.ops[0] for x in k.reaching]

              # Make sure to add the new definition to uses_defs so it
              # can itself be rereached if necessary.
              if i.expr.ops[0] in uses_defs:
                uses_defs[i.expr.ops[0]].append(k)
              else:
                uses_defs[i.expr.ops[0]] = [k]
              # XXX: It would feel right to remove k from uses_defs of
              # i.dest[0] here, but that leads to problems with missing
              # dessa names, so we don't do it. In the worst case, that
              # should cause a few redundant rereachings.

              #print('reaching now', [str(x) for x in k.reaching])
          # rereach definitions
          if i.dest[0] in self.definitions:
            self.definitions = [x if x != i.dest[0] else i.expr.ops[0] for x in self.definitions]
          if self.actual_returns != None:
            self.actual_returns = [x if x != i.dest[0] else i.expr.ops[0] for x in self.actual_returns]
        
        i.dest = []
        i.expr.ops = [0]
        
    propped = True
    while propped:
      propped = False
      for i in self.getall():
        # prop to expressions, but leave phi functions as they are
        if isinstance(i.expr, Expr) and not i.expr.type == PHI:
          for j in i.expr.getallops():
            # the operand must be an SSADef and have a link to its definition, which must only define
            # this single operand
            if isinstance(j, SSADef) and j.define_statement != None and len(j.define_statement.dest) == 1 and j.define_statement.op == ASGN:
              # propagate everything except phi functions
              if (not isinstance(j.define_statement.expr, Expr) or j.define_statement.expr.type != PHI) and \
                 not j.define_statement.expr.dont_propagate and \
                 not (_pass == 1 and j.define_statement.expr.type in [LOAD, LOAD16, LOAD32]):	# we don't know yet if it's I/O
                if len(j.define_statement.expr.getallops()) > 10:
                  debug(SSA, 4, 'not propping', i.expr, 'to complex expression', j.define_statement.expr)
                elif i.expr.getallops().count(j) > 1:
                  debug(SSA, 4, 'not propping', j, 'in', i.expr, 'multiple times to', j.define_statement.expr)
                else:
                  debug(SSA, 4, 'propping', j, 'in', i.expr, 'to expr of ', j.define_statement)
                  i.expr.substitute(j, j.define_statement.expr)
                  propped = True

  def depropagate(self):
    for i in self.getall():
      if isinstance(i.expr, Expr) and i.expr.type != CONST:
        # search predecessors for definitions that can be used instead of
        # i.expr
        cf = i
        # we give up when encountering a fork; not optimal, but easy to
        # implement
        visited = set()
        while len(cf.comefrom) == 1 and cf.comefrom[0] not in visited:
          cf = cf.comefrom[0]
          visited.add(cf)
          # Expressions that have dont_propagate set are supposed to be left
          # in place, making it illegal to depropagate them as well.
          if cf.op == ASGN and len(cf.dest) == 1 and not cf.expr.dont_propagate:
            if cf.expr.equals(i.expr) and cf.expr is not i.expr:
              debug(SSA, 4, 'depropping', i, 'to', cf)
              i.expr = Expr(VAR, [cf.dest[0]])
            else:
              i.expr.substitute_expr(cf.expr, cf.dest[0])

  def simplify(self, _pass = 1):
    for i in self.getall():
      if isinstance(i.expr, Expr):
        i.expr.simplify()
      if _pass == 1 and i.op == BRANCH_COND and i.expr.type == CONST:
        if i.expr.type == CONST:
          debug(SSA, 3, 'pruning', i)
          if i.expr.ops[0] == 0:
            # never branch
            i.insn.fake_branch = 0
          else:
            # always branch
            i.insn.fake_branch = 1
      if _pass == 1 and i.op == IMPURE and i.expr.type in [STORE, STORE16, STORE32] and \
        (isinstance(i.expr.ops[2], int) or (isinstance(i.expr.ops[2], SSADef) and i.expr.ops[2].is_text())) and \
        isinstance(i.expr.ops[1], int):
          if isinstance(i.expr.ops[2], SSADef):
            i.insn.fixed_mem = struct.unpack('<I', MCodeGraph._text[i.expr.ops[2].addr - MCodeGraph._org:i.expr.ops[2].addr - MCodeGraph._org+4])[0]
          else:
            i.insn.fixed_mem = i.expr.ops[2]
          i.insn.fixed_mem += i.expr.ops[1]
          debug(SSA, 5, 'found constant store to', hex(i.insn.fixed_mem), 'in', i)
      if _pass == 1 and i.op == ASGN and i.expr.type in [LOAD, LOAD16, LOAD32] and \
        (isinstance(i.expr.ops[1], int) or (isinstance(i.expr.ops[1], SSADef) and i.expr.ops[1].is_text())) and \
        isinstance(i.expr.ops[0], int):
          if isinstance(i.expr.ops[1], SSADef):
            i.insn.fixed_mem = struct.unpack('<I', MCodeGraph._text[i.expr.ops[1].addr - MCodeGraph._org:i.expr.ops[1].addr - MCodeGraph._org+4])[0]
          else:
            i.insn.fixed_mem = i.expr.ops[1]
          i.insn.fixed_mem += i.expr.ops[0]
          debug(SSA, 5, 'found constant load from', hex(i.insn.fixed_mem), 'in', i)
      # simplify cases in which a loop counter is incremented/decremented and
      # the old value is checked afterwards; this is a typical result of the
      # ARM idiom "SUBS Rx, Rx,... ; BNE ..."
      if _pass == 2 and i.op == ASGN and i.expr.type in [ADD, SUB] and len(i.next) == 1 and len(i.next[0].comefrom) == 1 and len(i.expr.ops) == 2 and isinstance(i.expr.ops[1], int) and \
        isinstance(i.expr.ops[0], SSADef) and len(i.dest) == 1 and i.dest[0].type == i.expr.ops[0].type:
          debug(SSA, 6, 'found inc/dec by int in', i)
          if i.expr.type == ADD:
            compl = SUB
          else:
            compl = ADD
          n = i.next[0]
          for j in n.expr.getallops():
            if i.expr.ops[0] == j:
              debug(SSA, 6, 'bingo!', j, n)
              n.expr = n.expr.substitute(j, Expr(compl, [i.dest[0], i.expr.ops[1]]), dup = True)
              debug(SSA, 6, 'new statement', n)
              debug(SSA, 6, 'pre statement', i)

  def is_io(self, addr):
    for i in self.iomap:
      if isinstance(i, tuple):
        if addr >= i[0] and addr < i[1]:
          return True
      elif addr == i:
        return True
    return False

  # de-SSA works by dumping the indices of definitions if their live ranges
  # do not overlap; if they do, it will rename the definition if it is not
  # used outside this block or create a temporary copy if it is
  def dessa(self):
    done = set()
    tmp_index = 0
    temps = dict()
    def do_dessa(st, defs = None):
      if defs == None:
        defs = dict()
      nonlocal tmp_index
      done.add(st)
      debug(DESSA, 3, 'starting dessa at', st)
      if isinstance(st.expr, Expr):
        # check all uses if they are the latest definition
        # if not, we have to keep a copy of the use before
        # it is overwritten
        for i in st.expr.getallops():
          if isinstance(i, SSADef):
            # implicit definitions with 0 as index are not named in the loop
            # below, so we do it here instead
            if i.dessa_name == None and i.idx == 0:
              i.dessa_name = type2dessaname(i.type)
              debug(DESSA, 4, 'bnamed', i, object.__str__(i), 'to', i.dessa_name)

            key = (i.type, i.addr)
            # check if this is the current (most recent) definition
            # we ignore the following cases:
            # - temps: no need to copy what already is a copy
            # - phi functions: designed from the outset to only use current
            #   definitions
            if key in defs and defs[key] != i and not i.is_dessa_tmp and st.expr.type not in [PHI, EXPLICIT_PHI]:
              # use of a non-current definition
              debug(DESSA, 4, 'old definition', i, 'used, current', defs[key])
              def_st = i.define_statement
              if i in temps:
                st.expr = st.expr.substitute(i, temps[i], dup = True)
              elif def_st == None:
                # no defining statement; this is a function argument
                debug(DESSA, 4, 'need to copy argument', i)
                assert(i.idx == 0)
                # we need to make a copy at the start of the function
                old_start = self.start
                nst = SSAStatement()
                nst.op = ASGN
                nst.dest = [SSADef(None, 'TMP', idx=tmp_index, dessa_tmp=True)]
                nst.dest[0].dessa_name = 'old_' + i.dessa_name #'tmp' + str(tmp_index)
                nst.dest[0].addr = i.addr
                tmp_index += 1
                nst.expr = Expr(VAR, [i])
                nst.next = [old_start]
                nst.insn = old_start.insn
                old_start.comefrom += [nst]
                self.start = nst
                st.expr = st.expr.substitute(i, nst.dest[0], dup = True)
                temps[i] = nst.dest[0]
                debug(DESSA, 4, 'argtmp', i, nst.dest[0], st)
              else:
                if def_st.expr.type == PHI:
                  # the definition used is defined as a phi function
                  # making it explicit is sufficient to create a copy
                  def_st.dest[0].dessa_name = type2dessaname(def_st.dest[0].type)
                  if arch.numbered_registers:
                    def_st.dest[0].dessa_name += '_'
                  def_st.dest[0].dessa_name += str(def_st.dest[0].idx)
                  def_st.expr.type = EXPLICIT_PHI
                  temps[i] = def_st.dest[0]
                  def_st.dest[0].is_dessa_tmp = True
                else:
                  # create an additional copy when at the point of definition
                  new_def = SSADef(None, 'TMP', idx=tmp_index, dessa_tmp=True)
                  new_def.dessa_name = 'tmp' + str(tmp_index)
                  tmp_index += 1
                  if def_st.op == ASGN:
                    def_st.dest += [new_def]
                    debug(DESSA, 4, 'copytmp', def_st)
                  elif def_st.op == CALL:
                    new_st = SSAStatement()
                    new_st.dest = [new_def]
                    new_st.op = ASGN
                    new_st.expr = Expr(VAR, [i])
                    new_st.insn = def_st.insn
                    new_st.next = def_st.next
                    for j in def_st.next:
                      j.comefrom.remove(def_st)
                      j.comefrom.append(new_st)
                    def_st.next = [new_st]
                    new_st.comefrom = [def_st]
                    debug(DESSA, 4, 'duptmp', new_st)
                  temps[i] = new_def
                  st.expr = st.expr.substitute(i, new_def, dup = True)
                  debug(DESSA, 4, 'duped', st.expr)
      # collect all definitions and give them a default name
      for d in st.dest:
        key = (d.type, d.addr)
        defs[key] = d
        if d.dessa_name == None:
          d.dessa_name = type2dessaname(d.type)
          debug(DESSA, 4, 'named', d, object.__str__(d), 'to', d.dessa_name)
      for i in st.next:
        if not i in done:
          do_dessa(i, defs.copy())
    do_dessa(self.start)

  def recover_types(self):
    high = self.end_base_ptr
    for i in sorted(self.stack_obj_ptrs):	# top down
      for j in self.stack_obj_defs:
        if j in self.definitions_all and j.addr == i:
          # found a reaching stack object for this address
          j.data_type.size = high - i
          debug(SSA, 6, 'recovered size of', j, 'to be', high - i)
          # find stack scalars that are part of this object
          for k in self.get_all_defs():	# XXX: self.definitions_all?
            if k.type == 's' and (k.addr >= j.addr and k.addr < j.addr + j.data_type.size):
              debug(SSA, 6, 'declaring', k, 'to be member of', j)
              k.parent_def = j
      high = i

def ssaify(insn, symbol, iomap):
  if insn.addr in ssacache:
    debug(SSA, 2, 'serving', insn, 'from SSA cache')
    ret = ssacache[insn.addr]
    ret.symbol = symbol
    return ret

  debug(SSA, 1, '--- START', insn)
  for _pass in [1, 2]:
    debug(SSA, 1, '--- PASS', _pass)
    ssag = SSAGraph(iomap, _pass)
    ssag.origin = insn.addr
    ssag.symbol = symbol
    ssa_in_progress.add(insn)
    debug(SSA, 5, 'progress in', hex(insn.addr), [hex(x.addr) for x in ssa_in_progress])
    ssag.add(insn)
    debug(SSA, 5, 'progress out', hex(insn.addr), [hex(x.addr) for x in ssa_in_progress])
    ssa_in_progress.remove(insn)
    ssag.dump(2)
    ssag.find_definitions()
    ssag.dce()
    ssag.dump(4)
    ssag.dereach()
    ssag.propagate(_pass)
    ssag.dump(4)
    ssag.dce()
    #ssag.dump()
    ssag.simplify(_pass)
  debug(SSA, 1, '--- FINAL', insn)
  ssag.dump(2)
  # propagation may have redefined reachings
  ssag.find_definitions()
  ssag.find_args()
  ssag.find_rets()
  ssag.recover_types()
  debug(SSA, 1, '--- DONE', insn)
  debug(ARGRET, 4, 'adding', ssag, 'for insn', insn, 'to ssacache')
  ssacache[insn.addr] = ssag
  return ssag

def identifyreturns(graphs):
  done = []
  for g in graphs:
    debug(ARGRET, 2, '-- IDENTIRET', hex(g.origin))
    uses = []
    for call in g.callers_st:
      debug(ARGRET, 5, 'uses from', call)
      for j in call.call_uses:
        if not j in uses:
          uses += [j]
    debug(ARGRET, 2, 'definitions', [str(x) for x in g.definitions])
    debug(ARGRET, 2, 'actual uses', [str(x) for x in uses])
    callee_context_uses = []
    for u in uses:
      for d in g.definitions:
        if u.type == d.type and u.addr == d.addr and not d in callee_context_uses:
          callee_context_uses += [d]
    debug(ARGRET, 2, 'callee uses', [str(x) for x in callee_context_uses])
    g.actual_returns = callee_context_uses
    g.find_rets()
    g.dce()
    g.dump(4)
    for h in g.callee_graphs:
      if h in done:
        debug(ARGRET, 2, 'redoing', h)
        identifyreturns([h])
    done += [g]

def type2dessaname(type):
  if type == 'M':
    return 'byte'
  elif type == 'Mw':
    return 'dword'
  elif type == 'Mh':
    return 'word'
  else:
    return type.lower()
