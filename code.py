# code.py
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

import block
from ssa import SSADef, CALL, RETURN, LOAD, STORE, ASGN, BRANCH_COND, IMPURE, ENDLESS_LOOP, type2dessaname
import ssa
from expr import *
from util import *
from debug import *
from insn import arch

def ind(num):
  return ' ' * num

def mem_access_style(ops, type):
  do_array = False
  base_op = 0
  idx_op = 1
  if isinstance(ops[0], int) and ops[0] > arch.max_array_idx:
    do_array = True
  elif isinstance(ops[1], int) and ops[1] > arch.max_array_idx:
    do_array = True
    base_op = 1
    idx_op = 0
  elif isinstance(ops[0], int):
    base_op = 1
    idx_op = 0
  if type == LOAD or type == STORE:
    type_str = 'uint8_t'
  elif type == LOAD16 or type == STORE16: 
    type_str = 'uint16_t'
  else:
    type_str = 'uint32_t'
  return type_str, base_op, idx_op, do_array

def block_comment(indent, comment):
  s = ind(indent) + '/* '
  s += ('\n' + ind(indent)).join(comment.split('\n'))
  s += ' */\n'
  return s

class Code:
  def __init__(self):
    self.graph = None
    self.sym_dict = dict()
    self.graph_dict = dict()

    # hack to allow adding comments from expression processing
    self.current_statement = None

    self.ret_struct_count = 0

    self.declare_locals = dict()
    self.declare_globals = dict()
    self.declare_arrays = dict()


  def label(self, blk):
    if blk.start_st.op == RETURN or (blk.end_st and blk.end_st.op == RETURN):
      l = 'ret_'
    else:
      l = 'label_'
    return l + zhex(blk.start_st.insn.addr)

  def any2c(self, any, prio = 19, preferhex=False, implicit_global=False):
    if isinstance(any, int):
      if preferhex or hex(any)[2:].count('0') > str(any).count('0'):
        return hex(any)
      else:
        return str(any)
    elif isinstance(any, Expr):
      return self.expr2c(any, prio, preferhex)
    elif isinstance(any, SSADef):
      return self.def2c(any, prio, implicit_global)
    raise InternalError('unknown operand ' + str(any) + ' of type ' + str(type(any)))

  def def2c(self, ssad, prio = 19, implicit_global=False):
    if isinstance(ssad.addr, int):
      if ssad.dessa_name == None:
        raise InternalError('no dessa_name in ' + str(ssad) + '(' + repr(ssad) + '), defined in ' + str(ssad.define_statement))
      s = ssad.dessa_name + '_' + zhex(ssad.addr)
    else:
      assert(ssad.addr == None)
      assert(ssad.dessa_name != None)
      s = ssad.dessa_name
    if not implicit_global and ssad.type[0] == 'M' and not ssad.is_dessa_tmp and s not in declare_globals:
      declare_globals[s] = 'unknown_t'
    elif (ssad.type[0] != 'M' or ssad.is_dessa_tmp) and s not in declare_locals:
      if ssad.type == 's':
        self.declare_locals[s] = ('unknown_t', '__sp[' + str(ssad.addr) + ']')
      else:
        declare_locals[s] = ('unknown_t', None)
    if ssad.type == 's' and ssad.addr in [1,2]:
      current_statement.add_comment('XXX: stacked return address accessed')
    return s

  def expr2c(self, ex, prio = 19, preferhex=False):
    myprio = 18

    def unop(operator):
      assert(len(ex.ops) == 1)
      return operator + self.any2c(ex.ops[0], myprio, preferhex)
    def binop(operator):
      assert(len(ex.ops) == 2)
      return self.any2c(ex.ops[0], myprio, preferhex) + ' ' + operator + ' ' + self.any2c(ex.ops[1], myprio, preferhex)
    def nadicop(operator):
      assert(len(ex.ops) >= 2)
      return (' ' + operator + ' ').join([self.any2c(x, myprio, preferhex) for x in ex.ops])

    if ex.type == EXPLICIT_PHI:
      debug(CODE, 4, 'coding exphi', ex)
      dessa_name = ex.ops[0].dessa_name
      for i in ex.getallops()[1:]:
        debug(CODE, 4, 'is', i.dessa_name, '==', dessa_name, '?')
        #assert(i.dessa_name == dessa_name and i.addr == ex.ops[0].addr)
        assert(i.dessa_name[0] == dessa_name[0] and i.addr == ex.ops[0].addr)
      ret = self.def2c(ex.ops[0])
    elif ex.type == VAR:
      assert(len(ex.ops) == 1)
      ret = self.any2c(ex.ops[0])
    elif ex.type == CONST:
      assert(len(ex.ops) == 1)
      ret = self.any2c(ex.ops[0])
    elif ex.type == ARGS:
      #print(ex.ops[0], type(ex.ops[0]))
      sym = self.sym_dict[ex.ops[0]]
      graph = self.graph_dict[ex.ops[0]]
      ret = sym.name + '('
      reg_args = []
      mem_args = []
      # number of arguments should equal number of callee parameters
      assert(graph.origin in ssa.fun_args_tentative or len(ex.ops) - 1 == len(ssa.fun_args_d[graph.first_insn]))
      if graph.origin in ssa.fun_args_tentative:
        current_statement.add_comment('args/rets may be incorrect')
      for i in range(0, len(ex.ops) - 1):
        # distinguish between memory parameters (implicit) and register
        # parameters (explicit)
        if ssa.fun_args_d[graph.first_insn][i].type[0] != 'M' and not (ssa.fun_args_d[graph.first_insn][i].type == 's' and ssa.fun_args_d[graph.first_insn][i].addr < 0):
          # for registers, we want 'our' (the caller's) name
          reg_args += [ex.ops[1 + i]]
        elif ssa.fun_args_d[graph.first_insn][i].type[0] == 'M':
          # for memory parameters, we want both names; this is because
          # in our scope, we may just have a constant or a register, which
          # is not very meaningful outside our context
          mem_args += [(ssa.fun_args_d[graph.first_insn][i], ex.ops[1 + i])]
        # ignore stack arguments
      ret += ', '.join([self.any2c(i) for i in reg_args]) + ')'
      if debug_level >= 2 and len(mem_args) > 0:
        # emit memory arguments as a comment
        comment = 'uses '
        count = 0
        for i in mem_args:
          # workaround: because no argument pruning is done after return
          # identification, we may see arguments that are not actually
          # used by the callee and thus don't have a dessa_name;
          # we ignore those for now
          if i[0].dessa_name != None:
            def0 = self.def2c(i[0], implicit_global=True)
            def1 = self.any2c(i[1], implicit_global=True)
            comment += def0
            if def0 != def1:
              comment += ' (' + def1 + ')'
            comment += ', '
            count += 1
            if count >= 3:
              comment += '...'
              break
        comment = comment.rstrip(', ')
        current_statement.add_comment(comment)
    elif ex.type in [LOAD, LOAD16, LOAD32]:
      assert(len(ex.ops) == 2)
      myprio = 2
      if debug_enabled(3):
        current_statement.add_comment('load ' + str(ex))
      if arch.register_base:
        type, base_op, idx_op, do_array = mem_access_style(ex.ops, ex.type)
        if do_array:
          ret = 'arr_' + zhex(ex.ops[base_op])
          self.declare_arrays[ret] = type
        else:   
          ret = '((' + type + ' *)' + self.any2c(ex.ops[base_op]) + ')'
        ret += '[' + self.any2c(ex.ops[idx_op]) + ']'
      else:
        if isinstance(ex.ops[0], int):
          ret = 'arr_' + zhex(ex.ops[0])
          if ex.type == LOAD:
            self.declare_arrays[ret] = 'uint8_t'
          elif ex.type == LOAD16:
            self.declare_arrays[ret] = 'uint16_t'
          else:
            self.declare_arrays[ret] = 'uint32_t'
        else:
          if ex.type == LOAD:
            ret = '((uint8_t *)'
          elif ex.type == LOAD16:
            ret = '((uint16_t *)'
          else:
            ret = '((uint32_t *)'
          ret += self.any2c(ex.ops[0]) + ')'
        ret += '[' + self.any2c(ex.ops[1]) + ']'
    elif ex.type in [STORE, STORE16, STORE32]:
      assert(len(ex.ops) == 3)
      myprio = 2
      if debug_enabled(3):
        current_statement.add_comment('store ' + str(ex))
      if arch.register_base:  
        type, base_op, idx_op, do_array = mem_access_style(ex.ops[1:], ex.type)
        if do_array:
          ret = 'arr_' + zhex(ex.ops[base_op+1])
          self.declare_arrays[ret] = type
        else:   
          ret = '((' + type + ' *)' + self.any2c(ex.ops[base_op+1]) + ')'
        ret += '[' + self.any2c(ex.ops[idx_op+1]) + '] = ' + self.any2c(ex.ops[0])
      else:
        if isinstance(ex.ops[1], int):
          ret = 'arr_' + zhex(ex.ops[1])
          if ex.type == STORE:
            self.declare_arrays[ret] = 'uint8_t'
          elif ex.type == STORE16:
            self.declare_arrays[ret] = 'uint16_t'
          else:
            self.declare_arrays[ret] = 'uint32_t'
        else:
          if ex.type == STORE:
            ret = '((uint8_t *)'
          elif ex.type == STORE16:
            ret = '((uint16_t *)'
          else:
            ret = '((uint32_t *)'
          ret += self.any2c(ex.ops[1]) + ')'
        ret += '[' + self.any2c(ex.ops[2]) + '] = ' + self.any2c(ex.ops[0])
    elif ex.type in [IOIN, IOIN16, IOIN32]:
      assert(len(ex.ops) == 1)
      if ex.type == IOIN:
        mod = 'b'
      elif ex.type == IOIN16:
        mod = 'w'
      else:
        mod = 'l'
      ret = 'in' + mod + '(' + self.any2c(ex.ops[0], preferhex=True) + ')'
      myprio = 1
    elif ex.type in [IOOUT, IOOUT16, IOOUT32]:
      assert(len(ex.ops) == 2)
      if ex.type == IOOUT32:
        mod = 'l'
      elif ex.type == IOOUT16:
        mod = 'w'
      else:
        mod = 'b'
      ret = 'out' + mod + '(' + self.any2c(ex.ops[0], preferhex = True) + ', ' + self.any2c(ex.ops[1], preferhex = True) + ')'
      myprio = 1
    elif ex.type == SHR:
      myprio = 7
      ret = binop('>>')
    elif ex.type == SHL:
      myprio = 7
      ret = binop('<<')
    elif ex.type == COMPARE_EQ:
      assert(len(ex.ops) == 2)
      myprio = 7
      ret = binop('==')
    elif ex.type == COMPARE_NE:
      assert(len(ex.ops) == 2)
      myprio = 9
      ret = binop('!=')
    elif ex.type == COMPARE_LT:
      myprio = 8
      ret = binop('<')
    elif ex.type == COMPARE_GE:
      myprio = 8
      ret = binop('>=')
    elif ex.type == COMPARE_GES:
      # XXX: write as '>=', declare operands signed instead
      myprio = 8
      ret = binop('>=s')
    elif ex.type == COMPARE_GTS:
      # XXX: write as '>', declare operands signed instead
      myprio = 8
      ret = binop('>s')
    elif ex.type == COMPARE_LTS:
      # XXX: write as '<', declare operands signed instead
      myprio = 8
      ret = binop('<s')
    elif ex.type == COMPARE_LES:
      # XXX: write as '<=', declare operands signed instead
      myprio = 8
      ret = binop('<=s')
    elif ex.type == ADD:
      myprio = 6
      ret = nadicop('+')
    elif ex.type == SUB:
      myprio = 6
      ret = nadicop('-')
    elif ex.type == NOT:
      myprio = 3
      ret = unop('!')
    elif ex.type == INV:
      myprio = 3 # sure?
      ret = unop('~')
    elif ex.type == AND:
      myprio = 10
      ret = binop('&')
    elif ex.type == OR:
      myprio = 12
      ret = binop('|')
    elif ex.type == EOR:
      myprio = 11
      ret = binop('^')
    elif ex.type == ANDFLAGS_Z:
      myprio = 10 # & operator
      ret = '!(' + binop('&') + ')'
      myprio = 3 # ! operator
    elif ex.type == ANDFLAGS_NOTZ:
      myprio = 10 # & operator
      ret = '(' + binop('&') + ') != 0'
      myprio = 9 # == operator
    elif ex.type == ANDFLAGS_N:
      myprio = 10 # & operator
      ret = '(' + binop('&') + ') >= 128'
      myprio = 8 # >= operator
    elif ex.type == SHLFLAGS_C:
      myprio = 10 # & operator
      ret = '(' + self.any2c(ex.ops[0]) + ' & 0x80) == 0'
      myprio = 9 # == operator
    elif ex.type == SHFLAGS_N:
      myprio = 8
      ret = self.any2c(ex.ops[0], 8) + ' >= 128'
    elif ex.type == INTRINSIC:
      ret = '__' + ex.ops[0] + '(' + ', '.join([self.any2c(x, preferhex=True) for x in ex.ops[1:]]) + ')'
    elif ex.type == ADCFLAGS_C:
      myprio = 6 # + operator
      ret = ' + '.join([self.any2c(x, myprio) for x in ex.ops])
      ret += ' >= 256'
      myprio = 8 # >= operator
    elif ex.type == ADCFLAGS_N:
      myprio = 6 # + operator
      ret = ' + '.join([self.any2c(x, myprio) for x in ex.ops])
      ret += ' >= 128'
      myprio = 8 # < operator
    elif ex.type == ADCFLAGS_Z:
      myprio = 6 # + operator
      ret = ' + '.join([self.any2c(x, myprio) for x in ex.ops])
      ret += ' == 0'
      myprio = 9 # == operator
    elif ex.type == ADCFLAGS_V:
      myprio = 6 # + operator
      sum = '(int8_t)' + ' + (int8_t)'.join([self.any2c(x, myprio) for x in ex.ops])
      ret = '(' + sum + ' >= 128) || (' + sum + ' < -128)'
      myprio = 14 # || operator
    elif ex.type == SBBFLAGS_C:
      # While we internally use a borrow flag, the result of this must be a carry,
      # i.e. the condition is inverted (>= instead of <).
      assert(len(ex.ops) >= 2)
      ret = self.any2c(ex.ops[0], 8) + ' >= ' + ' + '.join([self.any2c(x, 6) for x in ex.ops[1:]])
      myprio = 8 # >= operator
    elif ex.type == SBBFLAGS_N:
      ret = ' - '.join([self.any2c(x, 6) for x in ex.ops]) + ' >= 128'
      myprio = 8	# >= operator
    elif ex.type == SBBFLAGS_Z:
      ret = ' - '.join([self.any2c(x, 6) for x in ex.ops]) + ' == 0'
      myprio = 9	# == operator
    elif ex.type == SBBFLAGS_V:
      myprio = 6 # + operator
      diff = '(int8_t)' + ' - (int8_t)'.join([self.any2c(x, myprio) for x in ex.ops])
      ret = '(' + diff + ' >= 128) || (' + diff + ' < -128)'
      myprio = 14 # || operator
    elif ex.type == ORFLAGS_N:
      myprio = 12 # | operator
      ret = '(' + binop('|') + ') >= 128'
      myprio = 8 # >= operator
    elif ex.type == ORFLAGS_Z:
      myprio = 12 # | operator
      ret = '(' + binop('|') + ') == 0'
      myprio = 9 # == operator
    elif ex.type == EORFLAGS_Z:
      myprio = 11 # ^ operator
      ret = '(' + binop('^') + ') == 0'
      myprio = 9 # == operator
    elif ex.type == EORFLAGS_N:
      myprio = 11 # ^ operator
      ret = '(' + binop('^') + ') >= 128'
      myprio = 8 # < operator
    elif ex.type == EORFLAGS_NOTN:
      myprio = 11 # ^ operator
      ret = '(' + binop('^') + ') < 128'
      myprio = 8 # < operator
    elif ex.type in [DEFLAGS_V, BITFLAGS_V]:
      # The parens are not necessary, but it feels weird without them.
      ret = '(' + self.any2c(ex.ops[0], 7) + ' >> 6) & 1'
      myprio = 10 # & operator
    elif ex.type in [DEFLAGS_N, BITFLAGS_N]:
      myprio = 7	# >> operator
      ret = self.any2c(ex.ops[0], myprio) + ' >> 7'
    elif ex.type == DEFLAGS_C:
      myprio = 10 # & operator
      ret = self.any2c(ex.ops[0], myprio) + ' & 1'
    elif ex.type == DEFLAGS_Z:
      # The parens are not necessary, but it feels weird without them.
      ret = '(' + self.any2c(ex.ops[0], 7) + ' >> 1) & 1'
      myprio = 10 # & operator
    elif ex.type == FLAGS:
      ret = '__flags(' + ', '.join([self.any2c(x, 18) for x in ex.ops]) + ')'
      myprio = 2	# function call
    else:
      ret = 'RAW ' + str(ex)
    if myprio >= prio:
      ret = '(' + ret + ')'
    #ret = '( /* ' + str(myprio) + '/' + str(prio) + ' */ ' + ret + ')'
    return ret

  def get_returns(self, actual_returns):
    # XXX: We should really use a function like ssa.fun_returns().
    rets = []
    rets_d = []
    mrets = []
    mrets_d = []
    for i in sorted(actual_returns, key = attrgetter('type')):
      if i.idx == 0:
        continue
      cdef = self.any2c(i, implicit_global=True)
      if i.type[0] != 'M' and not (i.type == 's' and i.addr < 0) and not cdef in rets:
        assert(isinstance(cdef, str))
        rets += [cdef]
        rets_d += [i]
      elif i.type[0] == 'M' and not cdef in mrets:
        mrets += [cdef]
        mrets_d += [i]
    return rets_d, mrets_d

  def rets2struct(self, rets):
    return 'struct ret_' + ''.join([type2dessaname(x.type) for x in rets])


  def statement2c(self, st, indent, graph, bare = False):
    global current_statement
    current_statement = st
    if isinstance(st.expr, Expr) and st.expr.type == PHI:
      return ''
    semi = '' if bare else ';'
    line = ind(indent)
    if st.op == ASGN:
      if len(st.dest) >= 1:
        line += ' = '.join([self.def2c(x) for x in st.dest]) + ' = ' + self.expr2c(st.expr) + semi
      elif len(st.dest) == 0:
        if (st.expr.type == NOP):
          line += '/* do nothing */'
        else:
          line += self.expr2c(st.expr) + semi
      else:
        line += str(st)
    elif st.op == CALL:
      # code assignment of return value(s)
      callee_rets, callee_mrets = self.get_returns(self.graph_dict[st.expr.ops[0]].actual_returns)
      rets = []
      mrets = []
      if len(st.call_uses) > 0:
        # distinguish between explicit (register) returns and implicit (memory)
        # returns
        for i in st.call_uses:
          r = self.def2c(i, implicit_global=True)
          if i.type[0] != 'M' and not (i.type[0] == 's' and i.addr < 0) and not i.is_dessa_tmp:
            rets += [r]
          elif i.type[0] == 'M':
            mrets += [r]
          # ignore stack returns
        # sorting is required to get a canonical return struct name
        # (for memory parameters it's just beautification)
        rets.sort()
        mrets.sort()
        if len(callee_rets) > 1 and len(rets) > 0:
          # we need a return structure
          rname = 'ret' + str(self.ret_struct_count)
          self.ret_struct_count += 1
          line += self.rets2struct(callee_rets) + ' ' + rname + ' = '
        elif len(callee_rets) == 1 and len(rets) == 1:
          # direct assignment to register variable
          line += rets[0] + ' = '
      line += self.expr2c(st.expr) + semi
      if debug_level >= 2 and len(mrets) > 0:	# XXX: or callee_mrets?
        # emit memory parameters as a comment
        comment = 'modifies ' + ', '.join(mrets[:3])
        if len(mrets) > 3:
          comment += ', ...'
        st.add_comment(comment)
      assert(len(callee_rets) >= len(rets))
      if len(rets) >= 1 and len(callee_rets) > 1:
        # if we have used a return struct, we have to assign its members to
        # the corresponding register variables
        for i in rets:
          line += '\n' + ind(indent) + i + ' = ' + rname + '.' + i + ';'
    elif st.op == RETURN:
      if graph.actual_returns and len(graph.actual_returns) > 0:
        rets, mrets = self.get_returns(graph.actual_returns)
        if len(rets) > 1:
          # return a struct
          line += self.rets2struct(rets) + ' ret = { ' + ', '.join([self.any2c(x, implicit_global=True) for x in rets]) + ' }; '
          line += 'return ret' + semi
        elif len(rets) == 1:
          line += 'return ' + self.any2c(rets[0], implicit_global=True) + semi
        else:
          line += 'return' + semi
        if debug_level >= 2 and len(mrets) > 0:
          line += ' /* modified ' + ', '.join([self.any2c(x, implicit_global=True) for x in mrets[:3]])
          if len(mrets) > 3:
            line += ', ...'
          line += ' */'
      else:
        line += 'return' + semi
    elif st.op == IMPURE:
      line += self.any2c(st.expr) + semi
    elif st.op == ENDLESS_LOOP:
      line += 'for (;;);'
    else:
      line += str(st)

    # comments that should always be printed
    my_comments = list(st.comment)
    # comments that should be only printed once per program
    for i in st.comment_once:
      if pull_oneshot_comment(i):
        my_comments += [i]
    if my_comments:
      max_len = 0
      for i in my_comments:
        if len(i) > max_len: max_len = len(i)
      if len(line) + max_len > 80 and not bare:
        line = ind(indent) + '/* ' + (' */\n/* ').join(my_comments).replace('\n', '\n' + ind(indent)) + ' */\n' + line
      else:
        line += ' /* ' + '; '.join(my_comments) + ' */'

    return line + ('' if bare else '\n')

  def code(self, blk, symbol, symbols, graphs, graph):
    self.graph = graph

    if symbols != None:
      self.sym_dict = symbols
    if graphs != None:
      for i in graphs:
        self.graph_dict[i.first_insn.addr] = i

    c_header = ''

    if self.graph.origin in ssa.fun_returns_tentative or \
       graph.origin in ssa.fun_args_tentative:
      c_header += block_comment(0, 'XXX: recursion, inaccurate args/returns')

    # code function header
    rets, mrets = self.get_returns(graph.actual_returns)
    if len(rets) > 1:
      c_header += self.rets2struct(rets)
    elif len(rets) == 1:
      c_header += 'unknown_t'
    else:
      c_header += 'void'
    c_header += ' ' + symbol + '('
    # code (explicit, i.e. register) function parameters
    # XXX: code implicit (memory) parameters as a comment
    declare_arguments = []
    for i in ssa.fun_args_d[graph.first_insn]:
      # workaround for dead arguments that have not been pruned after return
      # identification
      if i.dessa_name != None and i.type[0] != 'M' and not (i.type == 's' and i.addr < 0) and not i.is_dessa_tmp:
        c_header += 'unknown_t '
        if i.type == 's':
          c_header += i.dessa_name + '_' + zhex(i.addr)
        else:
          c_header += i.dessa_name
        c_header += ', '
        declare_arguments += [i.dessa_name]
    c_header = c_header.rstrip(', ') + ')\n'
    if debug_enabled(2):
      c_header += '/* bp ' + hex(graph.base_ptr) + ' ebp ' + hex(graph.end_base_ptr) + ' */\n'
    c_header += '{\n'
    indent = 4
    done = dict()
    gotos = []
    labels = []

    self.ret_struct_count = 0
    self.declare_locals = dict()
    self.declare_globals = dict()
    self.declare_arrays = dict()

    def do_code(blk, norecurse = False):
      global current_statement
      nonlocal labels, indent, gotos
      c_code = ''

      # We cannot emit labels for clipped basic blocks or mark them as done
      # unless we're coding them as part of an advanced block (norecurse ==
      # True)
      if not (not norecurse and blk.clipped):
        l = self.label(blk)
        if not l in labels:
          c_code += l + ':\n'
          labels += [l]
        done[blk] = True

      current_statement = blk.start_st

      if isinstance(blk, block.AdvancedBlock):
        if debug_enabled(2):
          c_code += ind(indent) + '/* ablock ' + str(blk) + ' */\n'
        if blk.type in [block.IF_THEN_ELSE, block.IF_THEN]:
          c_code += ind(indent) + 'if (' + self.any2c(blk.condition) + ') {\n'
          indent += 4
          if debug_enabled(3):
            c_code += ind(indent) + '/* in IT(E) ablock ' + str(blk) + ' */\n'
          if not blk.blocks[0] in done:
            c_code += do_code(blk.blocks[0], norecurse = True)
          else:
            c_code += ind(indent) + 'goto ' + self.label(blk.blocks[0]) + ';'
            if debug_enabled(3):
              c_code += ' /* IT(E) ablock item already coded */\n'
            c_code += '\n'
            gotos += [self.label(blk.blocks[0])]
          indent -=4
          c_code += ind(indent) + '}\n'
          if blk.type == block.IF_THEN_ELSE:
            c_code += ind(indent) + 'else {\n'
            indent += 4
            if not blk.blocks[1] in done:
              c_code += do_code(blk.blocks[1], norecurse = True)
            else:
              c_code += ind(indent) + 'goto ' + self.label(blk.blocks[1]) + ';'
              if debug_enabled(3):
                c_code += ' /* ITE ablock item already coded */'
              c_code += '\n'
              gotos += [self.label(blk.blocks[1])]
            indent -= 4
            c_code += ind(indent) + '}\n'
        elif blk.type in [block.POST_LOOP, block.EMPTY_LOOP]:
          c_code += ind(indent) + 'do {\n'
          if blk.type == block.POST_LOOP:
            indent += 4
            if not blk.blocks[0] in done:
              for i in blk.blocks:
                assert(i not in done)
                if debug_enabled(2):
                  c_code += ind(indent) + '/* post loop block */\n'
                c_code += do_code(i, norecurse = True)
            else:
              c_code += ind(indent) + 'goto ' + self.label(blk.blocks[0]) + ';'
              if debug_enabled(3):
                c_code += ' /* post loop ablock item already coded */'
              c_code += '\n'
              gotos += [self.label(blk.blocks[0])]
            indent -=4
          c_code += ind(indent) + '} while (' + self.expr2c(blk.condition) + ');\n'
        elif blk.type == block.PRE_LOOP:
          c_code += ind(indent) + 'while ('
          if blk.prolog:
            # statements that are executed before every loop iteration _and_
            # before the test; an alternative would be to code this prolog and
            # repeat it in the iteration step of a for() loop
            # this would also make it easier to declare lvalues properly
            for i in blk.prolog:
              st_code = self.statement2c(i, 0, graph, bare=True)
              if st_code != '': c_code += st_code + ', '
          c_code += self.any2c(blk.condition) + ') {\n'

          indent += 4
          if not blk.blocks[0] in done:
            c_code += do_code(blk.blocks[0], norecurse = True)
          else:
            c_code += ind(indent) + 'goto ' + self.label(blk.blocks[0]) + ';'
            if debug_enabled(3):
              c_code += ' /* pre loop ablock item already coded */'
            c_code += '\n'
            gotos += [self.label(blk.blocks[0])]
          indent -=4

          c_code += ind(indent) + '}\n'
        else:
          for b in blk.blocks:
            if debug_enabled(3):
              c_code += ind(indent) + '/* in ablock ' + str(blk) + ' */\n'
            if not b in done:
              c_code += do_code(b, norecurse = True)
            else:
              c_code += ind(indent) + 'goto ' + self.label(b) + ';'
              if debug_enabled(3):
                c_code += ' /* ablock item already coded */'
              c_code += '\n'
              gotos += [self.label(b)]
              if blk.type == block.IF_THEN:
                indent -=4
                c_code += ind(indent) + '}\n'
              return c_code

        if not norecurse:
          if len(blk.next) > 0:
            if not blk.next[0] in done:
              if debug_enabled(3):
                c_code += ind(indent) + '/* from ablock ' + str(blk) + ' */\n'
              c_code += do_code(blk.next[0])
            else:
              c_code += ind(indent) + 'goto ' + self.label(blk.next[0]) + ';'
              if debug_enabled(3):
                c_code += ' /* from ablock ' + str(blk) + ' */'
              c_code += '\n'
              gotos += [self.label(blk.next[0])]
      else:
        st = blk.start_st
        if debug_enabled(2):
          c_code += ind(indent) + '/* bblock' + str(blk) + ' */\n'

        def emit_goto(_blk, _comment=None):
          nonlocal c_code, gotos
          c_code += ind(indent) + 'goto ' + self.label(_blk) + ';'
          if _comment != None and debug_enabled(3):
            c_code += ' /* ' + _comment + ' */'
          c_code += '\n'
          gotos += [self.label(_blk)]

        def emit_code(_blk, _comment=None):
          nonlocal c_code
          if _comment != None and debug_enabled(3):
            c_code += ind(indent) + '/* ' + _comment+ ' */\n'
          c_code += do_code(_blk)

        if not norecurse and blk.clipped:
          # We cannot code a clipped basic block because it's missing its
          # conditional branch at the end; since such a block is always
          # a part of an advanced block, however, we can just emit a
          # goto and rely on the block being coded as part of its
          # container.
          emit_goto(blk, 'clipped')
        else:
          # don't emit conditional branch statements at the end of blocks,
          # we deal with them later
          if st != blk.end_st or st.op != BRANCH_COND:
            c_code += self.statement2c(st, indent, graph)
          while st != blk.end_st:
            st = list(st.next)[0]
            if st != blk.end_st or st.op != BRANCH_COND:
              c_code += self.statement2c(st, indent, graph)

          if not norecurse:
            if len(blk.next) == 1:
              if blk.next[0] in done:
                emit_goto(blk.next[0], 'from bblock ' + str(blk))
              else:
                emit_code(blk.next[0], 'from bblock ' + str(blk))
            elif len(blk.next) == 2:
              assert(st.op == BRANCH_COND)
              do_done = blk.next[0] in done
              skip_done = blk.next[1] in done
              use_skip = skip_done and not do_done
              if use_skip:
                # use skip in conditional statement
                cond_expr = st.expr
              else:
                # use do in conditional statement
                cond_expr = Expr(NOT, [st.expr])
                cond_expr.simplify()
              c_code += ind(indent) + 'if (' + self.any2c(cond_expr) + ') {\n'
              indent += 4
              if use_skip:
                assert(skip_done)
                emit_goto(blk.next[1], 'branch taken')
              elif do_done:
                emit_goto(blk.next[0], 'branch not taken')
              else:
                assert(not do_done)
                emit_code(blk.next[0], 'from bblock ' + str(blk) + ', branch not taken')
              indent -= 4
              c_code += ind(indent) + '}\n'
              if use_skip:
                assert(not do_done)
                emit_code(blk.next[0], 'from bblock ' + str(blk) + ', branch not taken')
              else:
                if not skip_done:
                  emit_code(blk.next[1], 'from bblock ' + str(blk) + ', branch taken')
                else:
                  emit_goto(blk.next[1], 'branch taken')
            elif len(blk.next) == 0:
              pass	# nothing to do
            else:
              c_code += '#warning unimplemented multi-target branch\n'
              for c, i in enumerate(blk.next):
                emit_goto(i, 'from bblock ' + str(blk))
              for i in blk.next:
                if not i in done:
                  emit_code(i, 'from bblock ' + str(blk))

      return c_code

    c_body = do_code(blk) + '}\n'
    for i in labels:
      if not i in gotos:
        c_body = c_body.replace(i + ':\n', '')
        #c_body = c_body.replace(i + ':\n', '/* ' + i + ': */\n')

    c_decl = ''
    c_extern = ''
    declare_stack = False
    for i, t in self.declare_locals.items():
      if i not in declare_arguments:
        c_decl += ind(indent) + t[0] + ' ' + i
        if t[1] != None:
          c_decl += ' = ' + t[1]
          if '__sp' in t[1] and not declare_stack:
            c_extern += 'extern ' + arch.register_type + ' *__sp;\n'
            declare_stack = True
        c_decl += ';\n'

    for i, t in self.declare_globals.items():
      c_extern += 'extern ' + t + ' ' + i + ';\n'

    for i, t in self.declare_arrays.items():
      c_extern += 'extern ' + t + ' ' + i + '[];\n'

    return c_extern + c_header + c_decl + c_body
