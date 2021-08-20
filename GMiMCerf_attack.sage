#!/usr/bin/env python
# coding: utf-8


"""
GB Attack on GMiMCerf,t=4, prime field=307
AUTHOR: Gizem Kara <kara.gizem@metu.edu.tr>

NOTE: This code is based on the sage implementations of the
attacks on Jarvis and Friday by Albrecht et al. 
at https://github.com/IAIK/marvellous-attacks
"""

from sage.rings.polynomial.multi_polynomial_ideal import MPolynomialIdeal
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildIrred_list

import sage.libs.singular.function_factory
eliminate = sage.libs.singular.function_factory.ff.eliminate
import copy
import time

def define_constants():
    array=[]
    for i in range(0,num_rounds):
        array.append(K.random_element())
    return array

def F_func(x,k,c):
    return (x+k+c)**3

def define_plaintext():
    array=[0,0,0,0]
    for i in range(4):
        array[i]= K.random_element()
    return array

def encr_gmimc_erf(plaintext,key,num_rounds,constants):
    cipher=[0,0,0,0]
    plaintext_copy=copy.deepcopy(plaintext)
    for i in range(num_rounds):
        F_i =F_func(plaintext_copy[0],key,constants[i])
        cipher[0]=F_i+plaintext_copy[1]
        cipher[1]=F_i+plaintext_copy[2]
        cipher[2]=F_i+plaintext_copy[3]
        cipher[3]=plaintext_copy[0]
        for j in range(4):
            plaintext_copy[j]=cipher[j]
    return cipher

def decr_gmimc_erf(ciphertext,key,num_rounds,constants):
    plain=[0,0,0,0]
    ciphertext_copy=copy.deepcopy(ciphertext)
    constants=constants[::-1]
    for i in range(num_rounds):
        plain[0]=ciphertext_copy[3]
        plain[1]=ciphertext_copy[0]
        plain[2]=ciphertext_copy[1]
        plain[3]=ciphertext_copy[2]
        F_i =F_func(plain[0],key,constants[i])
        plain[1]-=F_i
        plain[2]-=F_i
        plain[3]-=F_i
        for j in range(4):
            ciphertext_copy[j]=plain[j]
    return plain


def get_elimination_ideal(F, variables, deg_bound=None, algorithm="singular:slimgb", *args, **kwds): 
   
    P = PolynomialRing(K, variables, order="degrevlex") 
    F = Sequence([P(f) for f in F])
    print( "n_v: {n_v:3d}, n_e: {n_e:3d}, max_deg: {d:3d}".format(n_v=F.nvariables(), n_e=len(F),
                                                                  d=F.maximal_degree()))

    gb = None
    if deg_bound:
        ideal = Ideal(F)
        print(ideal)
        print( "1 Dimension of R/I as vector space:", len(ideal.normal_basis()))
        H = ideal.change_ring(P.change_ring(order="degrevlex")).gens()
        print("n: {n:3d}, m: {m:3d}, max(deg(f)): {d:3d},".format(n=F.nvariables(), m=len(F),
                                                                  d=H.maximal_degree()))
        if deg_bound is True:
            deg_bound = 1 + sum(f.degree() - 1 for f in H)
        if deg_bound < H.maximal_degree():
            raise ValueError("Degree bound %d is smaller than input degrees %d."%(deg_bound,
                                                                                  H.maximal_degree()))
        t = walltime()
        gb = H.groebner_basis(deg_bound=deg_bound, algorithm=algorithm, *args, **kwds)
        print( "GB time: {t:5.1f}s". format(t=walltime(t)))
        print( "deg_bound: {deg_bound:3d}, is GB: {is_gb}".format(deg_bound=deg_bound, 
                                                                  is_gb=gb.is_groebner()))
        if not gb.is_groebner():
            raise ValueError("Degree bound %d too low, output is not a Grobner basis."%deg_bound)

    if gb == None:
        ideal = Ideal(F)
        print( "2 Dimension of R/I as vector space:", len(ideal.normal_basis()))
        t = walltime()
        gb = F.groebner_basis(algorithm=algorithm, *args, **kwds)
        print( "GB time: {t:5.1f}s".format(t=walltime(t)))

    t = walltime()
    gb_lex = Ideal(gb).transformed_basis('fglm')
    print( "FGLM time: {t:5.1f}s".format(t=walltime(t)))
    univariate = Sequence([f for f in gb_lex if f.is_univariate()])
    return univariate

t = walltime()
print( "FACT time: {t:5.1f}s".format(t=walltime(t)))

def solve(eqns, vars, rem_var, deg_bound, *args, **kwds):
    P = PolynomialRing(K, vars)
    if debug:
        for eq in eqns:
            print( "Degree:", P(eq).degree())
    #print("eqns",eqns)
    elGB = get_elimination_ideal(eqns, vars, deg_bound=deg_bound, *args, **kwds)
    if debug:
        print( "Length of elimination ideal:", len(elGB))
    Q = PolynomialRing(K, rem_var)
    print("elGB",elGB)
    #print("elGB0",elGB[0])
    #print("elGB-1",elGB[-1])

    #print( "elGB elements",[elt for elt in elGB])
    elim = Q(elGB[-1])
    sols = [el[0] for el in set(elim.roots(ring=K))]
    print( "Degree of univariate equation:", elim.degree())
    print("roots",elim.roots(ring=K))
    return sols

def gmimc_attack(plaintext,key,num_rounds, constants, deg_bound=None, *args, **kwds):
    ciphertext=encr_gmimc_erf(plaintext,key,num_rounds,constants)
    print( "Ciphertext ", ciphertext)
    variables = []
    for i in range(0, num_rounds):
        variables.append("x_"+str(4*i))
        variables.append("x_"+str(4*i+1))
        variables.append("x_"+str(4*i+2))
        variables.append("x_"+str(4*i+3))
    variables.append("k_0")
    print(variables)
    P = PolynomialRing(K, variables, order="degrevlex")
    P.inject_variables()
    variables = [P(v) for v in variables]
    equations = []
    elGB = None
    for i in range(0,num_rounds+1):
        if i==0:
            equations.append(variables[4*i+1]-F_func(plaintext[0],k_0,constants[i])-plaintext[1])
            equations.append(variables[4*i+2]-F_func(plaintext[0],k_0,constants[i])-plaintext[2])
            equations.append(variables[4*i+3]-F_func(plaintext[0],k_0,constants[i])-plaintext[3])
            equations.append(variables[4*i]-plaintext[0])

        elif i<num_rounds:
            equations.append(variables[4*i]-variables[4*(i-1)+1])
            equations.append(variables[4*i+1]-(variables[4*(i-1)+2])-F_func(variables[4*(i-1)+1],k_0,
                                                                            constants[i]))
            equations.append(variables[4*i+2]-(variables[4*(i-1)+3])-F_func(variables[4*(i-1)+1],k_0,
                                                                            constants[i]))
            equations.append(variables[4*i+3]-(variables[4*(i-1)])-F_func(variables[4*(i-1)+1],k_0,
                                                                          constants[i]))
        else:
            equations.append(variables[4*(i-1)]-ciphertext[3])
            equations.append(variables[4*(i-1)+1]-ciphertext[0])
            equations.append(variables[4*(i-1)+2]-ciphertext[1])
            equations.append(variables[4*(i-1)+3]-ciphertext[2])

    remaining_variable = "k_0"

    
    print( "Solutions:")
    for s in solve(equations, variables, remaining_variable, deg_bound, *args, **kwds):
        print( "K: ",s)

def run_gmimc_attack(r, deg_bound=None, *args, **kwds):
    K= GF(307)
    k= K.random_element()
    constants = define_constants()
    print("key", k)
    print("constants", constants)
    p=define_plaintext()
    print( "Plaintext: ", p)
    #ciphertext=encr_gmimc_erf(p,k,r,constants)
    #print( "Ciphertext:", ciphertext)
    gmimc_attack(p,k,r,constants,deg_bound=deg_bound, *args, **kwds)

num_rounds=10
K= GF(307)
run_gmimc_attack(r=10, deg_bound=None)






