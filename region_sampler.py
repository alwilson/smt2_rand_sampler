#!/usr/bin/env python3

import argparse
import random
import time
from xmlrpc.client import Boolean

import numpy as np
import z3
from matplotlib import animation
from matplotlib import pyplot as plt

from functools import reduce

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('-f', '--file', type=argparse.FileType('r', encoding='UTF-8'), required=True)
    parser.add_argument('-s', '--splits', type=int, default=1)
    parser.add_argument('-v', '--verbose', action='store_true')
    args = parser.parse_args()

    start_time = time.time()

    splits = args.splits
    verbose = args.verbose
    print(f'{verbose=}')

    # Load smt2 file into z3
    s = z3.Optimize()
    s.from_string(args.file.read())
    print(s)

    nx = 500
    ny = 500

    # Build up vars used
    s_vars = set()
    for assertion in s.assertions():
        for s_var in z3.z3util.get_vars(assertion):
            s_vars.add(s_var)

    # Treat as list for easier indexing
    s_vars = list(s_vars)

    # Check satisfiability
    ret = s.check()
    if ret != z3.sat:
        print(ret)
        exit(-1)

    print('Solution:')
    print(s.model())
    print()

    # Search for min/maxs of each variable
    region = search_region(s, s_vars, verbose)
    region['hits'] = 0
    region['total'] = 0
    print(region)

    # Convert z3 assertions into compiled python function
    py_assertion_str = assertions_to_string(s_vars, s.assertions())
    print(py_assertion_str)
    glob, loc = string_to_function(s_vars, py_assertion_str)
    
    elapsed_time = time.time() - start_time
    print(f'--- initial setup: {elapsed_time:.3f} seconds ---\n')

    # print(loc['smt_expr'](0, 0))
    # exit(0)

    # fig = plt.figure()
    # data = np.zeros((nx, ny))
    rands = 100000
    hits = 0
    start_time = time.time()

    # Split regions
    regions = []
    if splits > 0:
        # print('--------------------------------------')
        split_regions(s, s_vars, 0, region, regions, verbose)
        # print('--------------------------------------')

        # KEEP SPLITTING!?!?!
        for _ in range(splits-1):
            new_regions = []
            for r in regions:
                split_regions(s, s_vars, 0, r, new_regions, verbose)
            # print('--------------------------------------')
            regions = new_regions
    else:
        regions.append(region)

    elapsed_time = time.time() - start_time
    print(f'--- regions split: {elapsed_time:.3f} seconds ---\n')
    start_time = time.time()

    # print('--------------------------------------')
    # # print(region)
    # print(regions)
    # print(len(regions))

    # NOTE The dictionary lookups here are very, very slow!
    # Cache regions into quick lookup table
    qregs = []
    qregsizes = []
    qregtotal = 0
    for r in regions:
        qregs.append([(r[s_var][0], r[s_var][1]) for s_var in s_vars])
        size = reduce(lambda x, y: x*y, [(r[s_var][1] - r[s_var][0] + 1) for s_var in s_vars])
        qregsizes.append(size)
        qregtotal += size
    print(qregs)
    print(qregsizes)
    print(qregtotal)
    for i in range(rands):

        # reg_i = random.randrange(0, len(regions))
        rand_size = random.randrange(0, qregtotal)
        reg_i = 0
        while True:
            rand_size -= qregsizes[reg_i]
            if rand_size > 0:
                reg_i += 1
            else:
                break

        vals = []
        for r in qregs[reg_i]:
            if r[0] != r[1]:
                if type(r[0]) is Boolean:
                    vals.append(bool(random.getrandbits(1)))
                else:
                    vals.append(random.randrange(r[0], r[1]+1))
            else:
                vals.append(r[0])

        # print(vals)
        if loc['smt_expr'](*vals):
            hits += 1
            regions[reg_i]['hits'] += 1
            # data[vals[0]][vals[1]] += 1
        regions[reg_i]['total'] += 1

    elapsed_time = time.time() - start_time
    rands_per_s = rands / elapsed_time
    hits_per_s = hits / elapsed_time
    print(f'--- {rands} randomizations ---')
    print(f'--- done randomizing: {elapsed_time:.3f} seconds ---')
    print(f'--- {rands_per_s:.2f} rands per second ---')
    print(f'--- {hits} hits ---')
    print(f'--- {100*hits/rands:.2f}% hit rate ---')
    print(f'--- {hits_per_s:.2f} hits per second ---')
    print(f'{len(regions)=}')

    # plt.imshow(data, cmap='hot', interpolation='nearest')
    # plt.show()

    exit(0)

def split_regions(s, s_vars, var_i, region, regions, verbose=False):
    # print(f'split_regions({s}, {var_i}, {s_vars})')

    single_value = True
    for s_var in s_vars:
        if region[s_var][0] != region[s_var][1]:
            single_value = False
            break

    if single_value:
        regions.append(region)

    s_var = s_vars[var_i]

    if region[s_var][0] == region[s_var][1]:
        s.push()
        s.add(s_var == region[s_var][0])

        # if verbose: print(s_var, region[s_var], region[s_var][0], (region[s_var][0] + region[s_var][1]) // 2)
        
        if var_i+1 < len(s_vars):
            split_regions(s, s_vars, var_i+1, region, regions, verbose)
        else:
            ret = s.check()
            if ret != z3.sat:
                if verbose: print(f'Empty region')
                # print(s)
            else:
                new_region = search_region(s, s_vars, verbose)
                new_region['hits'] = 0
                new_region['total'] = 0
                if verbose: print(new_region)
                regions.append(new_region)
        
        s.pop()
    else:
        s.push()
        s.add(s_var >= region[s_var][0])
        s.add(s_var <= (region[s_var][0] + region[s_var][1]) // 2)

        # if verbose: print(s_var, region[s_var], region[s_var][0], (region[s_var][0] + region[s_var][1]) // 2)

        if var_i+1 < len(s_vars):
            split_regions(s, s_vars, var_i+1, region, regions, verbose)
        else:
            ret = s.check()
            if ret != z3.sat:
                if verbose: print(f'Empty region')
                # print(s)
            else:
                new_region = search_region(s, s_vars, verbose)
                new_region['hits'] = 0
                new_region['total'] = 0
                if verbose: print(new_region)
                regions.append(new_region)
        s.pop()


        s.push()
        s.add(s_var > (region[s_var][0] + region[s_var][1]) // 2)
        s.add(s_var <= region[s_var][1])
    
        if verbose: print(s_var, region[s_var], (region[s_var][0] + region[s_var][1]) // 2, region[s_var][1])

        if var_i+1 < len(s_vars):
            split_regions(s, s_vars, var_i+1, region, regions, verbose)
        else:
            ret = s.check()
            if ret != z3.sat:
                if verbose: print(f'Empty region')
                # print(s)
            else:
                new_region = search_region(s, s_vars, verbose)
                new_region['hits'] = 0
                new_region['total'] = 0
                if verbose: print(new_region)
                regions.append(new_region)
        s.pop()

def search_region(s, s_vars, verbose=False):
    if verbose: print('search_region: ', s)

    region = {}
    for s_var in s_vars:
        s.push()
        if type(s_var) is z3.z3.BoolRef:
            s.add(s_var == False)
            ret = s.check()
            if ret == z3.sat:
                region[s_var] = [False]
            elif ret == z3.unsat:
                region[s_var] = [True]
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
            region[s_var] = [m[s_var].as_long()]

        s.pop()

        s.push()
        if type(s_var) is z3.z3.BoolRef:
            s.add(s_var == True)
            ret = s.check()
            if ret == z3.sat:
                region[s_var].append(True)
            elif ret == z3.unsat:
                region[s_var].append(False)
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
            region[s_var].append(m[s_var].as_long())

        s.pop()
    return region


# Evaluate assertion
# TODO Use this to build up python functions to compile down
def eval_a(a : z3.ExprRef):
    # print(f'eval: {a} {type(a):} {a.sort():}')
    cl = a.children()

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
