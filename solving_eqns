#!/usr/bin/env python
# coding: utf-8


"""
Solving the multivariate polynomial system satisfying the equation

A^-1_AES (C)= B^-1 using GB method.

AUTHOR: Gizem Kara <kara.gizem@metu.edu.tr>

"""


from sage.rings.polynomial.multi_polynomial_ideal import MPolynomialIdeal
from sage.rings.polynomial.polynomial_gf2x import GF2X_BuildIrred_list

import sage.libs.singular.function_factory
eliminate = sage.libs.singular.function_factory.ff.eliminate


K.<a>= GF(2**8)

L.<c8,c4,c2>=PolynomialRing(K,order='lex')

"""
Coefficients of degree 128 polynomial representation of
inverse affine function of AES
"""
s128=K._cache.fetch_int(Integer(0x6E))
s64=K._cache.fetch_int(Integer(0xDB))
s32=K._cache.fetch_int(Integer(0x59))
s16=K._cache.fetch_int(Integer(0x78))
s8=K._cache.fetch_int(Integer(0x5A))
s4=K._cache.fetch_int(Integer(0x7F))
s2=K._cache.fetch_int(Integer(0xFE))
s=K._cache.fetch_int(Integer(0x5))

"""The variables c1,c2,c4,c8 are coefficients of C where
c1 is free"""


c1=K.random_element()

         
eqn1=s4*(c8^4)+s8*(c4)^8+s16*(c2^16)+s32*(c1^32)      
eqn2=s8*(c8^8)+s16*(c4)^16+s32*(c2^32)+s64*(c1^64)
eqn3=s16*(c8^16)+s32*(c4)^32+s64*(c2^64)+s128*(c1^128)  


Id= ideal(eqn1,eqn2,eqn3) # ideal is zero-dimensional
Gb=Id.groebner_basis()


#print("C= degree 8, B= degree 16, dimension:", Id.dimension())

print(Id.variety(),"c1:", c1)



