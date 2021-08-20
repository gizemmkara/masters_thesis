#!/usr/bin/env python
# coding: utf-8


"""
Implementing Gröbner basis elements as polynomial equations
until 12 rounds for GMiMCerf,t=4, field= GF(307)"

AUTHOR: Gizem Kara <kara.gizem@metu.edu.tr>

"""

from sage.rings.polynomial.multi_polynomial_ideal import MPolynomialIdeal
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildIrred_list

import sage.libs.singular.function_factory
eliminate = sage.libs.singular.function_factory.ff.eliminate
import copy
import time

def define_constants():
    array=[]
    a=K.random_element()
    for i in range(0,num_rounds):
        array.append(a)
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
        print( "1 Dimension of R/I as vector space:", len(ideal.normal_basis()))
        H = ideal.change_ring(P.change_ring(order="lex")).gens()
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
        gb = ideal
        print( "GB time: {t:5.1f}s".format(t=walltime(t)))

    t = walltime()
    gb_lex = Ideal(gb).transformed_basis('gwalk')
    print( "gwalk time: {t:5.1f}s".format(t=walltime(t)))
    #print( "gröbner basis: ",gb)
    univariate = Sequence([f for f in gb_lex if f.is_univariate()])
    return univariate

t = walltime()
print( "FACT time: {t:5.1f}s".format(t=walltime(t)))

def solve(eqns, vars, rem_var, deg_bound, *args, **kwds):
    P = PolynomialRing(K, vars)
    if debug:
        for eq in eqns:
            print( "Degree:", P(eq).degree())
    print("eqns",eqns)
    elGB = get_elimination_ideal(eqns, vars, deg_bound=deg_bound, *args, **kwds)
    if debug:
        print( "Length of elimination ideal:", len(elGB))
    Q = PolynomialRing(K, rem_var)
    print("elGB",elGB)
    print( "elGB elements",[elt for elt in elGB])
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
    print("variables:",variables)
    P = PolynomialRing(K, variables, order="degrevlex")
    P.inject_variables()
    variables = [P(v) for v in variables]
    equations = []
    #comment
    elGB = None
   
    if num_rounds==5:
        equations.append(F_func(plaintext[0],k_0,constants[0])-variables[4]+plaintext[1])
        equations.append(F_func(variables[4],k_0,constants[0])-variables[8]+variables[4]
                         +plaintext[2]-plaintext[1])
        equations.append(F_func(variables[8],k_0,constants[0])-variables[12]+variables[8]
                         +plaintext[3]-plaintext[2])
        equations.append(F_func(variables[12],k_0,constants[0])-variables[16]+
                         variables[12]-variables[4]-plaintext[3]+plaintext[1]+plaintext[0])
        equations.append(F_func(variables[16],k_0,constants[0])-variables[17]+variables[16]
                         -variables[8]+2*variables[4]+plaintext[2]-plaintext[1]-plaintext[0])
        equations.append(variables[19]-variables[17]+variables[16]-variables[12]-variables[8]
                         +2*variables[4]+plaintext[2]-plaintext[1]-plaintext[0])
        equations.append(variables[18]-variables[17]+variables[12]-2*variables[8]
                         +variables[4]-plaintext[3]+plaintext[2])
        equations.append(variables[16]-ciphertext[3])
        equations.append(variables[17]-ciphertext[0])
        equations.append(variables[18]-ciphertext[1])
        equations.append(variables[19]-ciphertext[2])
        
    if num_rounds==6:
        equations.append(variables[0]-plaintext[0])
        equations.append(variables[1]-plaintext[1])
        equations.append(variables[2]-plaintext[2])
        equations.append(variables[3]-plaintext[3])
        equations.append(F_func(variables[0],k_0,constants[0])-variables[4]+variables[1])
        equations.append(F_func(variables[4],k_0,constants[0])-variables[8]+variables[4]
                         +variables[2]-variables[1])
        equations.append(F_func(variables[8],k_0,constants[0])-variables[12]+variables[8]
                         +variables[3]-variables[2])
        equations.append(F_func(variables[12],k_0,constants[0])-variables[16]+variables[12]
                         -variables[4]-variables[3]+variables[1]+variables[0])
        equations.append(F_func(variables[16],k_0,constants[0])-variables[20]+variables[16]
                         -variables[8]+2*variables[4]+variables[2]-variables[1]-variables[0])
        equations.append(F_func(variables[20],k_0,constants[0])-variables[21]+variables[20]
                         -variables[12]+2*variables[8]-variables[4]+variables[3]-variables[2])
        equations.append(variables[23]-variables[21]+variables[20]-variables[16]-variables[12]
                         +2*variables[8]-variables[4]+variables[3]-variables[2])
        equations.append(variables[22]-variables[21]+variables[16]-2*variables[12]
                        +variables[8]+variables[4]+variables[3]-variables[1]-variables[0])
        equations.append(variables[20]-ciphertext[3])
        equations.append(variables[21]-ciphertext[0])
        equations.append(variables[22]-ciphertext[1])
        equations.append(variables[23]-ciphertext[2])
        
    if num_rounds==7:
        equations.append(F_func(plaintext[0],k_0,constants[0])-variables[4]+plaintext[1])
        equations.append(F_func(variables[4],k_0,constants[0])-variables[8]+variables[4]
                         +plaintext[2]-plaintext[1])
        equations.append(F_func(variables[8],k_0,constants[0])-variables[12]+variables[8]
                         +plaintext[3]-plaintext[2])
        equations.append(F_func(variables[12],k_0,constants[0])-variables[16]+variables[12]
                         -variables[4]-plaintext[3]+plaintext[1]+plaintext[0])
        equations.append(F_func(variables[16],k_0,constants[0])-variables[20]+variables[16]
                         -variables[8]+2*variables[4]+plaintext[2]-plaintext[1]-plaintext[0])
        equations.append(F_func(variables[20],k_0,constants[0])-variables[24]+variables[20]
                         -variables[12]+2*variables[8]-variables[4]+plaintext[3]-plaintext[2])
        equations.append(F_func(variables[24],k_0,constants[0])-variables[25]+variables[24]
                         -variables[16]+2*variables[12]-variables[8]-variables[4]-plaintext[3]
                         +plaintext[1]+plaintext[0])
        equations.append(variables[27]-variables[25]+variables[24]-variables[20]-variables[16]
                         +2*variables[12]-variables[8]-variables[4]-plaintext[3]+plaintext[1]
                         +plaintext[0])
        equations.append(variables[26]-variables[25]+variables[20]-2*variables[16]+variables[12]
                         +variables[8]-2*variables[4]-plaintext[2]+plaintext[1]+plaintext[0])
        equations.append(variables[24]-ciphertext[3])
        equations.append(variables[25]-ciphertext[0])
        equations.append(variables[26]-ciphertext[1])
        equations.append(variables[27]-ciphertext[2])
        
    if num_rounds==8:
        equations.append(F_func(plaintext[0],k_0,constants[0])-variables[4]+plaintext[1])
        equations.append(F_func(variables[4],k_0,constants[0])-variables[8]+variables[4]
                         +plaintext[2]-plaintext[1])
        equations.append(F_func(variables[8],k_0,constants[0])-variables[12]+variables[8]
                         +plaintext[3]-plaintext[2])
        equations.append(F_func(variables[12],k_0,constants[0])-variables[16]+variables[12]
                         -variables[4]-plaintext[3]+plaintext[1]+plaintext[0])
        equations.append(F_func(variables[16],k_0,constants[0])-variables[20]+variables[16]
                         -variables[8]+2*variables[4]+plaintext[2]-plaintext[1]-plaintext[0])
        equations.append(F_func(variables[20],k_0,constants[0])-variables[24]+variables[20]
                         -variables[12]+2*variables[8]-variables[4]+plaintext[3]-plaintext[2])
        equations.append(F_func(variables[24],k_0,constants[0])-variables[28]+variables[24]
                         -variables[16]+2*variables[12]-variables[8]-variables[4]-plaintext[3]
                         +plaintext[1]+plaintext[0])
        equations.append(F_func(variables[28],k_0,constants[0])-variables[29]+variables[28]
                         -variables[20]+2*variables[16]-variables[12]-variables[8]
                         +2*variables[4]+plaintext[2]-plaintext[1]-plaintext[0])
        equations.append(variables[31]-variables[29]+variables[28]-variables[24]
                         -variables[20]+2*variables[16]-variables[12]-variables[8]
                         +2*variables[4]+plaintext[2]-plaintext[1]-plaintext[0])
        equations.append(variables[30]-variables[29]+variables[24]-2*variables[20]+
                         variables[16]+variables[12]-2*variables[8]+variables[4]
                         -plaintext[3]+plaintext[2])
        equations.append(variables[28]-ciphertext[3])
        equations.append(variables[29]-ciphertext[0])
        equations.append(variables[30]-ciphertext[1])
        equations.append(variables[31]-ciphertext[2])
      
    if num_rounds==9:
        equations.append(F_func(plaintext[0],k_0,constants[0])-variables[4]+plaintext[1])
        equations.append(F_func(variables[4],k_0,constants[0])-variables[8]+variables[4]
                         +plaintext[2]-plaintext[1])
        equations.append(F_func(variables[8],k_0,constants[0])-variables[12]+variables[8]
                         +plaintext[3]-plaintext[2])
        equations.append(F_func(variables[12],k_0,constants[0])-variables[16]+variables[12]
                         -variables[4]-plaintext[3]+plaintext[1]+plaintext[0])
        equations.append(F_func(variables[16],k_0,constants[0])-variables[20]+variables[16]
                         -variables[8]+2*variables[4]+plaintext[2]-plaintext[1]-plaintext[0])
        equations.append(F_func(variables[20],k_0,constants[0])-variables[24]+variables[20]
                         -variables[12]+2*variables[8]-variables[4]+plaintext[3]-plaintext[2])
        equations.append(F_func(variables[24],k_0,constants[0])-variables[28]+variables[24]
                         -variables[16]+2*variables[12]-variables[8]-variables[4]
                         -plaintext[3]+plaintext[1]+plaintext[0])
        equations.append(F_func(variables[28],k_0,constants[0])-variables[32]+variables[28]
                         -variables[20]+2*variables[16]-variables[12]-variables[8]
                         +2*variables[4]+plaintext[2]-plaintext[1]-plaintext[0])
        equations.append(F_func(variables[32],k_0,constants[0])-variables[33]+variables[32]
                         -variables[24]+2*variables[20]-variables[16]-variables[12]
                         +2*variables[8]-variables[4]+plaintext[3]-plaintext[2])
        equations.append(variables[35]-variables[33]+variables[32]-variables[28]-variables[24]
                         +2*variables[20]-variables[16]-variables[12]+2*variables[8]
                         -variables[4]+plaintext[3]-plaintext[2])
        equations.append(variables[34]-variables[33]+variables[28]-2*variables[24]+variables[20]
                         +variables[16]-2*variables[12]+variables[8]+variables[4]+plaintext[3]
                         -plaintext[1]-plaintext[0])
        equations.append(variables[32]-ciphertext[3])
        equations.append(variables[33]-ciphertext[0])
        equations.append(variables[34]-ciphertext[1])
        equations.append(variables[35]-ciphertext[2])
        
    if num_rounds==10:
        equations.append(F_func(plaintext[0],k_0,constants[0])-variables[4]+plaintext[1])
        equations.append(F_func(variables[4],k_0,constants[0])-variables[8]+variables[4]
                         +plaintext[2]-plaintext[1])
        equations.append(F_func(variables[8],k_0,constants[0])-variables[12]+variables[8]
                         +plaintext[3]-plaintext[2])
        equations.append(F_func(variables[12],k_0,constants[0])-variables[16]+variables[12]
                         -variables[4]-plaintext[3]+plaintext[1]+plaintext[0])
        equations.append(F_func(variables[16],k_0,constants[0])-variables[20]+variables[16]
                         -variables[8]+2*variables[4]+plaintext[2]-plaintext[1]-plaintext[0])
        equations.append(F_func(variables[20],k_0,constants[0])-variables[24]+variables[20]
                         -variables[12]+2*variables[8]-variables[4]+plaintext[3]-plaintext[2])
        equations.append(F_func(variables[24],k_0,constants[0])-variables[28]+variables[24]
                         -variables[16]+2*variables[12]-variables[8]-variables[4]
                         -plaintext[3]+plaintext[1]+plaintext[0])
        equations.append(F_func(variables[28],k_0,constants[0])-variables[32]+variables[28]
                         -variables[20]+2*variables[16]-variables[12]-variables[8]
                         +2*variables[4]+plaintext[2]-plaintext[1]-plaintext[0])
        equations.append(F_func(variables[32],k_0,constants[0])-variables[36]+variables[32]
                         -variables[24]+2*variables[20]-variables[16]-variables[12]
                         +2*variables[8]-variables[4]+plaintext[3]-plaintext[2])
        equations.append(F_func(variables[36],k_0,constants[0])-variables[37]+variables[36]
                         -variables[28]+2*variables[24]-variables[20]-variables[16]
                         +2*variables[12]-variables[8]-variables[4]-plaintext[3]+plaintext[1]
                         +plaintext[0])        
        equations.append(variables[39]-variables[37]+variables[36]-variables[32]-variables[28]
                         +2*variables[24]-variables[20]-variables[16]+2*variables[12]
                         -variables[8]-variables[4]-plaintext[3]+plaintext[1]+plaintext[0])
        equations.append(variables[38]-variables[37]+variables[32]-2*variables[28]+variables[24]
                         +variables[20]-2*variables[16]+variables[12]+variables[8]
                         -2*variables[4]-plaintext[2]+plaintext[1]+plaintext[0])
        equations.append(variables[36]-ciphertext[3])
        equations.append(variables[37]-ciphertext[0])
        equations.append(variables[38]-ciphertext[1])
        equations.append(variables[39]-ciphertext[2])
        
    if num_rounds==11:
        equations.append(F_func(plaintext[0],k_0,constants[0])-variables[4]+plaintext[1])
        equations.append(F_func(variables[4],k_0,constants[0])-variables[8]+variables[4]
                         +plaintext[2]-plaintext[1])
        equations.append(F_func(variables[8],k_0,constants[0])-variables[12]+variables[8]
                         +plaintext[3]-plaintext[2])
        equations.append(F_func(variables[12],k_0,constants[0])-variables[16]+variables[12]
                         -variables[4]-plaintext[3]+plaintext[1]+plaintext[0])
        equations.append(F_func(variables[16],k_0,constants[0])-variables[20]+variables[16]
                         -variables[8]+2*variables[4]+plaintext[2]-plaintext[1]-plaintext[0])
        equations.append(F_func(variables[20],k_0,constants[0])-variables[24]+variables[20]
                         -variables[12]+2*variables[8]-variables[4]+plaintext[3]-plaintext[2])
        equations.append(F_func(variables[24],k_0,constants[0])-variables[28]+variables[24]
                         -variables[16]+2*variables[12]-variables[8]-variables[4]-plaintext[3]
                         +plaintext[1]+plaintext[0])
        equations.append(F_func(variables[28],k_0,constants[0])-variables[32]+variables[28]
                         -variables[20]+2*variables[16]-variables[12]-variables[8]+2*variables[4]
                         +plaintext[2]-plaintext[1]-plaintext[0])
        equations.append(F_func(variables[32],k_0,constants[0])-variables[36]+variables[32]
                         -variables[24]+2*variables[20]-variables[16]-variables[12]
                         +2*variables[8]-variables[4]+plaintext[3]-plaintext[2])
        equations.append(F_func(variables[36],k_0,constants[0])-variables[40]+variables[36]
                         -variables[28]+2*variables[24]-variables[20]-variables[16]+2*variables[12]
                         -variables[8]-variables[4]-plaintext[3]+
                         plaintext[1]+plaintext[0])  
        equations.append(F_func(variables[40],k_0,constants[0])-variables[41]+variables[40]-
                         variables[32]+2*variables[28]-variables[24]-variables[20]+2*variables[16]
                         -variables[12]-variables[8]+2*variables[4]+
                         plaintext[2]-plaintext[1]-plaintext[0])  
        equations.append(variables[43]-variables[41]+variables[40]-variables[36]-variables[32]
                         +2*variables[28]-variables[24]-variables[20]+2*variables[16]-
                         variables[12]-variables[8]+2*variables[4]+plaintext[2]-plaintext[1]-
                         plaintext[0])
        equations.append(variables[42]-variables[41]+variables[36]-2*variables[32]+variables[28]
                         +variables[24]-2*variables[20]+variables[16]+variables[12]
                         -2*variables[8]+variables[4]-plaintext[3]+plaintext[2])
        equations.append(variables[40]-ciphertext[3])
        equations.append(variables[41]-ciphertext[0])
        equations.append(variables[42]-ciphertext[1])
        equations.append(variables[43]-ciphertext[2])
        
    if num_rounds==12:
        equations.append(F_func(plaintext[0],k_0,constants[0])-variables[4]+plaintext[1])
        equations.append(F_func(variables[4],k_0,constants[0])-variables[8]+variables[4]
                         +plaintext[2]-plaintext[1])
        equations.append(F_func(variables[8],k_0,constants[0])-variables[12]+variables[8]
                         +plaintext[3]-plaintext[2])
        equations.append(F_func(variables[12],k_0,constants[0])-variables[16]+variables[12]
                         -variables[4]-plaintext[3]+plaintext[1]+plaintext[0])
        equations.append(F_func(variables[16],k_0,constants[0])-variables[20]+variables[16]
                         -variables[8]+2*variables[4]+plaintext[2]-plaintext[1]-plaintext[0])
        equations.append(F_func(variables[20],k_0,constants[0])-variables[24]+variables[20]
                         -variables[12]+2*variables[8]-variables[4]+plaintext[3]-plaintext[2])
        equations.append(F_func(variables[24],k_0,constants[0])-variables[28]+variables[24]
                         -variables[16]+2*variables[12]-variables[8]-variables[4]
                         -plaintext[3]+plaintext[1]+plaintext[0])
        equations.append(F_func(variables[28],k_0,constants[0])-variables[32]+variables[28]
                         -variables[20]+2*variables[16]-variables[12]-variables[8]
                         +2*variables[4]+plaintext[2]-plaintext[1]-plaintext[0])
        equations.append(F_func(variables[32],k_0,constants[0])-variables[36]+variables[32]
                         -variables[24]+2*variables[20]-variables[16]-variables[12]
                         +2*variables[8]-variables[4]+plaintext[3]-plaintext[2])
        equations.append(F_func(variables[36],k_0,constants[0])-variables[40]+variables[36]
                         -variables[28]+2*variables[24]-variables[20]-variables[16]
                         +2*variables[12]-variables[8]-variables[4]-plaintext[3]+
                         plaintext[1]+plaintext[0])  
        equations.append(F_func(variables[40],k_0,constants[0])-variables[44]+variables[40]
                         -variables[32]+2*variables[28]-variables[24]-variables[20]
                         +2*variables[16]-variables[12]-variables[8]+2*variables[4]+
                         plaintext[2]-plaintext[1]-plaintext[0])  
        
        equations.append(F_func(variables[44],k_0,constants[0])-variables[45]+variables[44]
                         -variables[36]+2*variables[32]-variables[28]-variables[24]
                         +2*variables[20]-variables[16]-variables[12]+2*variables[8]
                         -variables[4]+plaintext[3]-plaintext[2])
        equations.append(variables[47]-variables[45]+variables[44]-variables[40]-variables[36]
                         +2*variables[32]-variables[28]-variables[24]+2*variables[20]
                         -variables[16]-variables[12]+2*variables[8]-variables[4]
                         +plaintext[3]-plaintext[2])
        equations.append(variables[46]-variables[45]+variables[40]-2*variables[36]+variables[32]
                         +variables[28]-2*variables[24]+variables[20]+variables[16]
                         -2*variables[12]+variables[8]+variables[4]+plaintext[3]-plaintext[1]
                         -plaintext[0])
        equations.append(variables[44]-ciphertext[3])
        equations.append(variables[45]-ciphertext[0])
        equations.append(variables[46]-ciphertext[1])
        equations.append(variables[47]-ciphertext[2])
            
    
    remaining_variable = "k_0"

    #print( "equations: ")
    #[show(eq) for eq in equations]
    print( "Solutions:")
    for s in solve(equations, variables, remaining_variable, deg_bound, *args, **kwds):
        print( "K: ",s)

def run_gmimc_attack(r, deg_bound=None, *args, **kwds):
    K= GF(307,modulus="primitive")
    k=K.random_element()
    constants = define_constants()
    print("key", k)
    print("constants", constants)
    p= define_plaintext()
    print( "Plaintext: ", p)
    ciphertext=encr_gmimc_erf(p,k,r,constants)
    #print( "Ciphertext:", ciphertext)
    #print( "key is :", key)
    gmimc_attack(p,k,r,constants,deg_bound=deg_bound, *args, **kwds)


num_rounds=9
K= GF(307,modulus="primitive")
run_gmimc_attack(r=9, deg_bound=None)




