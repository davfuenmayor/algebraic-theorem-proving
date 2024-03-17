#!/usr/bin/env sage

import sys
from sage.all import *

def polysimp(poly_str, params_str, factorize):      
    R = eval(parse_params(params_str))
    lhs,rhs,prefix,sep = parse_polyeq(poly_str)
    result = prefix + " " + simplify(lhs,R,factorize) + " " + sep + " " + simplify(rhs,R,factorize)
    return result.strip()

def simplify(poly_str, R, factorize):
    if poly_str == "":
        return ""
    poly = R(poly_str)
    simp_poly = simplify_exponents(R, poly)
    if factorize and poly != R.zero(): 
        return str(simp_poly.factor())
    else:        
        return str(simp_poly)
    
def parse_polyeq(poly_str):
    prefix = ""
    sep = ""
    poly_str = poly_str.replace("\n","").replace("@", "") # remove undesired characters
    dot_index = poly_str.find('.')    
    if dot_index > 0: # a variable binder (e.g. quantifier) introduces a dot on the left-hand side of the equation
        prefix = poly_str[:dot_index+1] # saves as prefix       
        poly_str = poly_str[dot_index+1:] # removes variable binding prefix by deleting leading chars up to the first dot        
    equals_index = poly_str.find('=')
    if equals_index > 0: # an equals symbol found
        sep = "="         
        return poly_str[:equals_index].strip(), poly_str[equals_index+1:].strip(), prefix, sep
    leq_index = poly_str.find('<')
    geq_index = poly_str.find('>')
    if leq_index > 0 and geq_index > 0: # a markup symbol (i.e. having the form '\\<...>') found in the expression
        sep = poly_str[leq_index-2:geq_index+1]
        return poly_str[:leq_index-2].strip(), poly_str[geq_index+1:].strip(), prefix, sep
    if leq_index > 0 and geq_index < 0: # only a '<' symbol found
        sep = "<"
        return poly_str[:leq_index].strip(), poly_str[leq_index+1:].strip(), prefix, sep
    if leq_index < 0 and geq_index > 0: # only a '>' symbol found
        sep = ">"
        return poly_str[:geq_index].strip(), poly_str[geq_index+1:].strip(), prefix, sep 
    return poly_str.strip(), "", prefix, ""  
    
def parse_params(s):
    params = s.strip().replace("''", "'") # escaping Isabelle encoded strings
    if params.startswith("["): # in case params is a list of strings: [template, placeholder1, placeholder2, ...]        
        params = eval(params)
        return params[0].format(*params[1:]).replace("{", "\"").replace("}", "\"")
    return params.replace("\'", "").replace("{", "\"").replace("}", "\"")

def simplify_exponents(ring, poly):
    order = ring.base_ring().order()
    vars = ring.gens()
    if hasattr(poly,'mod') and not order in [+Infinity,-Infinity]:
        for var in vars:            
            m = var**order - var            
            poly = poly.mod(m)
    return poly    

with open(os.getcwd()+"/python/debug.txt", 'w') as file:
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