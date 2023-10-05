#!/usr/bin/env python3

import argparse
import random
import time
from dataclasses import dataclass
from functools import reduce

import numpy as np
import z3
from matplotlib import animation
from matplotlib import pyplot as plt


@dataclass
class RandVar:
    min : int
    max : int
    set : bool
    value : int

@dataclass
class Partition:
    assertions: list[z3.ExprRef]
    vars: list[z3.ArithRef]

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('-f', '--file', type=argparse.FileType('r', encoding='UTF-8'), required=True)
    parser.add_argument('-v', '--verbose', action='store_true')
    args = parser.parse_args()

    verbose = args.verbose
    print(f'{verbose=}')

    # Load smt2 file into z3
    s = z3.Optimize()
    s.from_string(args.file.read())
    print(s)

    # Check satisfiability
    ret = s.check()
    if ret != z3.sat:
        print(ret)
        exit(-1)

    # Build up vars used
    var_map = {}
    assert_map = {}
    s_vars = set()
    for assertion in s.assertions():
        assert_map[assertion] = []
        for s_var in z3.z3util.get_vars(assertion):
            s_vars.add(s_var)
            assert_map[assertion].append(s_var)
            if s_var not in var_map:
                var_map[s_var] = []
            var_map[s_var].append(assertion)

    # Treat as list for easier indexing
    s_vars = list(s_vars)
    range_map = init_range_map_z3(s, s_vars, verbose)
    print(range_map)

    partitions = partition_assertions(var_map, assert_map, s_vars)
    # TODO Explore ranges without using z3
    # for p in partitions:
    #     range_map = init_var_ranges(assert_map, p)
    #     explore_ranges(assert_map, p, range_map)

    for p in partitions:
        random.shuffle(p.vars)
        for var in p.vars:
            v = range_map[var] 
            v.value = random.randrange(v.min, v.max+1)
            v.set = False

            # Update remaining variable ranges
            # TODO
            # for a in p.assertions:
            #     update_range_map(a, range_map, var)

            print(v)

    exit(0)


def update_range_map(node, range_map : dict[z3.ArithRef, RandVar], var : z3.ArithRef):
    # Find lhs max by recursively looking at nodes
    cl = node.children()
    if len(cl) == 2:
        lhs = cl[0]
        rhs = cl[1]
    
    # Identify functions and recurse
    if z3.is_le(node):
        return update_range_map(lhs, range_map, var) + eval_max_range(rhs, range_map, var)
    elif z3.is_add(node):
        return update_range_map(lhs, range_map, var) + eval_max_range(rhs, range_map, var)
    elif type(node) == z3.IntNumRef:
        return node.as_long()
    elif type(node) == z3.ArithRef:
        node : z3.ArithRef
        if node.num_args() == 0:
            return range_map[node].max

    print(f'Unknown type: {type(node)}')
    exit(-1)


def init_var_ranges(assert_map, p : Partition, debug=False):
    range_map : dict[z3.ArithRef, RandVar] = {}
    for var in p.vars:
        range = []
        print(var, type(var), var.sort(), var.sort_kind())
        if var.is_int():
             range = [-2**31, 2**31-1]

        if debug: print(f'  {range}')

            # Find min/max of this variable by looking at simple assertions for just this variable
        for assertion in p.assertions:
            vars_involved = assert_map[assertion]
            children = assertion.children()
            print(f'  {assertion} {children}')
            if len(vars_involved) == 1 and vars_involved[0] == var and len(children) == 2:
                if children[0] == var and type(children[1]) is z3.IntNumRef:
                    if z3.is_le(assertion):
                        range[1] = min(range[1], assertion.children()[1].as_long())
                    elif z3.is_lt(assertion):
                        range[1] = min(range[1], assertion.children()[1].as_long()-1)
                    elif z3.is_ge(assertion):
                        range[0] = max(range[0], assertion.children()[1].as_long())
                    elif z3.is_gt(assertion):
                        range[0] = max(range[0], assertion.children()[1].as_long()+1)
                if children[1] == var and type(children[0]) is z3.IntNumRef:
                    if z3.is_le(assertion):
                        range[0] = min(range[1], assertion.children()[0].as_long())
                    elif z3.is_lt(assertion):
                        range[0] = min(range[1], assertion.children()[0].as_long()-1)
                    elif z3.is_ge(assertion):
                        range[1] = max(range[0], assertion.children()[0].as_long())
                    elif z3.is_gt(assertion):
                        range[1] = max(range[0], assertion.children()[0].as_long()+1)

        if debug: print(f'  {range}')
        range_map[var] = RandVar(range[0], range[1], True, 0)
    return range_map

def explore_ranges(assert_map, p : Partition, range_map : dict[z3.ArithRef, RandVar], debug=False):
    for assertion in p.assertions:
        vars_involved = assert_map[assertion]
        children = assertion.children()
        if len(vars_involved) > 1:
            lhs = children[0]
            rhs = children[1]
            print(f'  {assertion} {lhs=} {rhs=}')
            if z3.is_le(assertion):
                # Compare max of lhs to max of rhs

                # Find lhs max by recursively looking at assertions
                lhs_max = eval_max_range(lhs, range_map, debug)
                print(f'  {lhs_max=}')
                
                rhs_max = eval_max_range(rhs, range_map, debug)
                print(f'  {rhs_max=}')

def eval_max_range(node, range_map : dict[z3.ArithRef, RandVar], debug=False):
    # Find lhs max by recursively looking at nodes
    cl = node.children()
    if len(cl) == 2:
        lhs = cl[0]
        rhs = cl[1]
    
    # Identify functions and recurse
    if z3.is_add(node):
        return eval_max_range(lhs, range_map) + eval_max_range(rhs, range_map)
    elif type(node) == z3.IntNumRef:
        return node.as_long()
    elif type(node) == z3.ArithRef:
        node : z3.ArithRef
        if node.num_args() == 0:
            return range_map[node].max if range_map[node].enabled else range_map[node].value

    print(f'Unknown type: {type(node)}')
    exit(-1)

def partition_assertions(var_map, assert_map, s_vars) -> list[Partition]:
    partitions : list[Partition] = []
    for var in s_vars:
        new_partition = True
        for partition in partitions:
            # Check if variable is already part of a partition
            if var in partition.vars:
                new_partition = False
                p = partition
                break
            # Check if any variables directly related to this variable are part of a partition
            for assertion in var_map[var]:
                for s_var in assert_map[assertion]:
                    if s_var in partition.vars:
                        new_partition = False
                        p = partition
                        break

        if new_partition:
            p = Partition([], [var])
            partitions.append(p)

        # Add assertions and variables to partition, existing or new
        for assertion in var_map[var]:
            if assertion not in p.assertions:
                p.assertions.append(assertion)
            for svar in assert_map[assertion]:
                if svar not in p.vars:
                    p.vars.append(svar)

    return partitions

def init_range_map_z3(s, s_vars, verbose=False):
    range_map : dict[z3.ArithRef, RandVar] = {}
    if verbose: print('init_range_map_z3: ', s)

    for s_var in s_vars:
        s.push()
        if type(s_var) is z3.z3.BoolRef:
            s.add(s_var == False)
            ret = s.check()
            if ret == z3.sat:
                # TODO
                range_map[s_var] = RandVar(False, True, True, None)
            elif ret == z3.unsat:
                # TODO
                range_map[s_var] = RandVar(None, None, False, True)
            else:
                print(ret)
                exit(-1)
        else:
            s.minimize(s_var)
            ret = s.check()
            if ret != z3.sat:
                print(ret)
                exit(-1)

            m = s.model()
            # print(f'{s_var} max: {m[s_var]}')
            range_map[s_var] = RandVar(m[s_var].as_long(), 2**32-1, True, None)

        s.pop()

        s.push()
        if type(s_var) is z3.z3.BoolRef:
            s.add(s_var == True)
            ret = s.check()
            if ret == z3.sat:
                # TODO
                range_map[s_var].max(True)
            elif ret == z3.unsat:
                # TODO
                range_map[s_var].max(False)
            else:
                print(ret)
                exit(-1)
        else:
            s.maximize(s_var)
            ret = s.check()
            if ret != z3.sat:
                print(ret)
                exit(-1)

            m = s.model()
            # print(f'{s_var} min: {m[s_var]}')
            range_map[s_var].max = m[s_var].as_long()

        s.pop()
    return range_map


# Evaluate assertion
# TODO Use this to build up python functions to compile down
def eval_a(a : z3.ExprRef, s_vars, s_vals):
    if not hasattr(a, 'parent'):
        a.parent = None
    # print(f'eval: {a} {type(a):} {a.sort():}')
    cl = a.children()
    for c in cl:
        print(c, type(c))
        c.parent = a
        eval_a(c, s_vars, s_vals)

    return True

    # Identify functions and recurse
    if z3.is_gt(a):
        return f'({eval_a(cl[0])} > {eval_a(cl[1])})'
    elif z3.is_ge(a):
        return f'({eval_a(cl[0])} >= {eval_a(cl[1])})'
    elif z3.is_lt(a):
        return f'({eval_a(cl[0])} < {eval_a(cl[1])})'
    elif z3.is_le(a):
        return f'({eval_a(cl[0])} <= {eval_a(cl[1])})'
    elif z3.is_eq(a):
        return f'({eval_a(cl[0])} == {eval_a(cl[1])})'
    elif z3.is_add(a):
        return f'({eval_a(cl[0])} + {eval_a(cl[1])})'
    elif z3.is_mul(a):
        return f'({eval_a(cl[0])} * {eval_a(cl[1])})'
    elif z3.is_div(a):
        return f'({eval_a(cl[0])} / {eval_a(cl[1])})'
    elif z3.is_idiv(a):
        return f'({eval_a(cl[0])} // {eval_a(cl[1])})'
    elif z3.is_mod(a):
        return f'({eval_a(cl[0])} % {eval_a(cl[1])})'
    elif z3.is_implies(a):
        return f'({eval_a(cl[1])} if {eval_a(cl[0])} else True)'
    elif z3.is_app_of(a, z3.Z3_OP_ITE):
        print(cl)
        return f'({eval_a(cl[1])} if {eval_a(cl[0])} else {eval_a(cl[2])})'
    elif z3.is_or(a):
        if len(cl) > 1:
            return '(' + ' or '.join([eval_a(c) for c in cl]) +')'
        else:
            return eval_a(cl[0])
    elif z3.is_and(a):
        if len(cl) > 1:
            return '(' + ' and '.join([eval_a(c) for c in cl]) + ')'
        else:
            return eval_a(cl[0])
    elif z3.is_not(a):
        return f'not {eval_a(cl[0])}'

    # Print out variable names?
    if type(a) == z3.BoolRef:
        return str(a)

    if type(a) == z3.IntNumRef:
        return str(a.as_long())

    if type(a) == z3.ArithRef:
        a : z3.ArithRef
        if a.num_args() == 0:
            return str(a)

    if type(a) == z3.BitVecRef:
        return str(a)

    print(f'Unknown type: {type(a)}')
    exit(-1)


def assertions_to_string(s_vars, assertions):
    py_assertions = []
    for assertion in assertions:
        py_assertion = eval_a(assertion)
        print(f'{assertion}\n{py_assertion}\n')
        py_assertions.append(py_assertion)
    return ' and '.join([f'({a})' for a in py_assertions])


def string_to_function(s_vars, expression: str):
    # Produce arg list of all input variables
    var_list = [str(v) for v in s_vars]
    var_str = ','.join(var_list)

    srcCode = f'def smt_expr({var_str}):  return {expression}'
    print(srcCode)
    execCode = compile(srcCode, 'test', 'exec')
    glob, loc = {}, {}
    exec(execCode, glob, loc)

    return glob, loc


if __name__ == "__main__":
    main()
