#!/usr/bin/env python
# coding: utf-8


"""
GB Attack on reduced rounds of MiMC
AUTHOR: Gizem Kara <kara.gizem@metu.edu.tr>

NOTE: This code is based on the sage implementations of the
attacks on Jarvis and Friday by Albrecht et al. 
at https://github.com/IAIK/marvellous-attacks
"""


from sage.rings.polynomial.multi_polynomial_ideal import MPolynomialIdeal
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildIrred_list

import sage.libs.singular.function_factory


def define_constants():
    array=[]
    for i in range(0,num_rounds-1):
        array.append(K.random_element())
    return array
    

def mimc_encryption(plaintext,key,num_rounds,constants):
    cipher=(plaintext+key)^3
    for i in range(0,num_rounds-1):
        cipher=(cipher+key+constants[i])^3
    ciphertext=(cipher+key)
    return ciphertext

def mimc_decryption(ciphertext,key,num_rounds,constants):
    alpha_inverse = (2**(n+1)-1)/3
    plain=(ciphertext-key)
    for i in range(0,num_rounds-1):
        y=num_rounds-2-i
        plain = (plain^alpha_inverse - key - constants[y])
    plaintext=(plain^alpha_inverse-key)
    return plaintext
      

#decrypted_plaintext= mimc_decryption(ciphertext,key,num_rounds,constants)
#print "plaintext: ",decrypted_plaintext

def get_elimination_ideal(F, variables, deg_bound=None, algorithm="singular:slimgb", *args, **kwds): 
    P = PolynomialRing(K, variables, order="degrevlex") 
    F = Sequence([P(f) for f in F])
    print("n_v: {n_v:3d}, n_e: {n_e:3d}, max_deg: {d:3d}".format(n_v=F.nvariables(), n_e=len(F), 
                                                                 d=F.maximal_degree()))

    gb = None
    if deg_bound:
       ideal = Ideal(F)
       print ("Dimension of R/I as vector space:", len(ideal.normal_basis()))
       H = ideal.change_ring(P.change_ring(order="degrevlex")).gens()
       print ("n: {n:3d}, m: {m:3d}, max(deg(f)): {d:3d},".format(n=F.nvariables(), m=len(F),
                                                                  d=H.maximal_degree()))
       if deg_bound is True:
          deg_bound = 1 + sum(f.degree() - 1 for f in H)
       if deg_bound < H.maximal_degree():
          raise ValueError("Degree bound %d is smaller than input degrees %d."%(deg_bound,
                                                                                H.maximal_degree()))
       t = walltime()
       gb = H.groebner_basis(deg_bound=deg_bound, algorithm=algorithm, *args, **kwds)
       print ("GB time: {t:5.1f}s".format(t=walltime(t)))
       print ("deg_bound: {deg_bound:3d}, is GB: {is_gb}".format(deg_bound=deg_bound,
                                                                 is_gb=gb.is_groebner()))
       if not gb.is_groebner():
          raise ValueError("Degree bound %d too low, output is not a Gröbner basis."%deg_bound)

    if gb == None:
       ideal = Ideal(F)
       print ("Dimension of R/I as vector space:", len(ideal.normal_basis()))
       t = walltime()
       gb = F.groebner_basis(algorithm=algorithm, *args, **kwds)
       print ("GB time: {t:5.1f}s".format(t=walltime(t)))

    t = walltime()
    gb_lex = Ideal(gb).transformed_basis('fglm')
    print ("FGLM time: {t:5.1f}s".format(t=walltime(t)))

    univariate = Sequence([f for f in gb_lex if f.is_univariate()])
    return univariate

def solve(eqns, vars, rem_var, deg_bound, *args, **kwds):

    P = PolynomialRing(K, vars)
  
  # Print degrees
    if debug:
        for eq in eqns:
            print ("Degree:", P(eq).degree())

  # Get elimination ideal
    elGB = get_elimination_ideal(eqns, vars, deg_bound=deg_bound, *args, **kwds)
    if debug:
        print("Length of elimination ideal:", len(elGB))

  # Solve univariate equation    
    Q = PolynomialRing(K, rem_var)
    elim = Q(elGB[elGB.nvariables()-1])
    t = walltime()
    sols = [el[0] for el in set(elim.roots(ring=K))]    
    print ("FACT time: {t:5.1f}s".format(t=walltime(t)))
    print ("Degree of univariate equation:", elim.degree())
  
    return sols    


def mimc_attack(plaintext,key,num_rounds, constants, deg_bound=None, *args, **kwds):
    
    ciphertext = mimc_encryption(plaintext,key,num_rounds,constants)
    
    variables = []
    for i in range(0,num_rounds+1):
        variables.append("x_"+str(i))
    variables.append("k_0")
    P = PolynomialRing(K, variables, order="degrevlex")
    P.inject_variables()
    
    variables = [P(v) for v in variables]
    equations = []
     
    for i in range(0,num_rounds+1):
        if i==0:
            equations.append(variables[i]-k_0-plaintext)       
        elif i<num_rounds:
             equations.append(variables[i]-k_0-constants[i-1]-(variables[i-1])^3)
        else:
            equations.append(variables[i]-k_0-(variables[i-1])^3)
            equations.append(ciphertext-variables[i])   
             
    
    remaining_variable = "k_0"
    print ("Solutions:")
    for s in solve(equations, variables, remaining_variable, deg_bound, *args, **kwds):
        print ("K: ",s)

def run_mimc_attack(r=3, deg_bound=None, optimized=True, *args, **kwds):
    k = K.random_element()
    p = K.random_element()
    constants = define_constants()
    print ("key is :", k)
    mimc_attack(p,k,r,constants,deg_bound=deg_bound, *args, **kwds)


n = 129
num_rounds=3
testing_polys = False
debug = False

K = GF(2**n,"a")
K.inject_variables()

run_mimc_attack(3,deg_bound=None)

      





