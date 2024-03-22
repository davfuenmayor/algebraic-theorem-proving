#!/usr/bin/env sage
import sys
from sage.all import *

# Returns the list of 'splitting' polynomials: "x^q - x" for each variable x
def splitting_polynomials(ring):
    order = ring.base_ring().order()    
    if not order in [+Infinity,-Infinity]:
        return list(map(lambda x: x**order - x, ring.gens()))        
    return []

# Sanitizes and parses config strings of the form '<ring_type>(<field>, {<vars>})', e.g. 'PolynomialRing(GF(4), {x,y,z})'
def parse_params(s):
    params = s.strip().replace("''", "'") # escaping Isabelle encoded strings
    if params.startswith("["): # in case params is a list of strings: [template, placeholder1, placeholder2, ...]        
        params = eval(params)
        return params[0].format(*params[1:]).replace("{", "\"").replace("}", "\"")
    return params.replace("\'", "").replace("{", "\"").replace("}", "\"")

# Parses a polynomial (equation) expression of the form: '<prefix> <lhs_poly> (<separator> <rhs_poly>)', e.g. '\forall X. poly1 = poly2'
def parse_polyeq(poly_str):
    prefix = ""
    separator = ""
    poly_str = poly_str.replace("\n","").replace("@", "") # remove undesired characters
    dot_index = poly_str.find('.')    
    if dot_index > 0: # a variable binder (e.g. quantifier) introduces a dot on the left-hand side of the equation
        prefix = poly_str[:dot_index+1] # saves as prefix       
        poly_str = poly_str[dot_index+1:] # removes variable binding prefix by deleting leading chars up to the first dot        
    equals_index = poly_str.find('=')
    if equals_index > 0: # an equals symbol found
        separator = "="         
        return poly_str[:equals_index].strip(), poly_str[equals_index+1:].strip(), prefix, separator
    leq_index = poly_str.find('<')
    geq_index = poly_str.find('>')
    if leq_index > 0 and geq_index > 0: # a markup symbol (i.e. having the form '\\<...>') found in the expression
        separator = poly_str[leq_index-2:geq_index+1]
        return poly_str[:leq_index-2].strip(), poly_str[geq_index+1:].strip(), prefix, separator
    if leq_index > 0 and geq_index < 0: # only a '<' symbol found
        separator = "<"
        return poly_str[:leq_index].strip(), poly_str[leq_index+1:].strip(), prefix, separator
    if leq_index < 0 and geq_index > 0: # only a '>' symbol found
        separator = ">"
        return poly_str[:geq_index].strip(), poly_str[geq_index+1:].strip(), prefix, separator 
    return poly_str.strip(), "", prefix, ""

# Reduces (and factorizes) a given polynomial modulo the field's 'splitting' polynomials
def polysimp(expr_str, params_str, factorize):      
    R = eval(parse_params(params_str))
    lhs,rhs,prefix,separator = parse_polyeq(expr_str)
    result = prefix + " " + simplify(lhs,R,factorize) + " " + separator + " " + simplify(rhs,R,factorize)
    return result.strip()

def simplify(poly_str, R, factorize):
    if poly_str == "":
        return ""
    poly = R(poly_str)    
    reduced_poly = poly.reduce(splitting_polynomials(R)) # reduce wrt. the 'splitting' polynomials
    if factorize and poly != R.zero(): 
        return str(reduced_poly.factor())
    else:        
        return str(reduced_poly)

with open(os.getcwd()+"/python/debug-poly_simp.txt", 'w') as file:
    file.write("Command: " + str(sys.argv))

if len(sys.argv) < 4:
    print("Usage: %s <factorize?> <params> <expression>" % sys.argv[0])
    print("Simplifies (and factorizes) a polynomial (equation) <expression> over a given ring <params[0]> wrt. the specified variables <params[1]>")
    sys.exit(1)

factorize = False
if sys.argv[1].lower() in ['true', '1', 't', 'yes', 'y']:
   factorize = True

params = sys.argv[2]
poly = sys.argv[3]

print(polysimp(poly, params, factorize))