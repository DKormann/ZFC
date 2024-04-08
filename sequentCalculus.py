#%%
from syntax import *
from typing import Union
#%%
alpha = FormulaVar('α')
beta = FormulaVar('β')

rules=[
  [alpha, OR(alpha, beta)],
  [OR(alpha, alpha), alpha],
  [alpha, NOT(NOT(alpha))],
  [NOT(NOT(alpha)), alpha],
  [OR(alpha,beta),OR(beta,alpha)],
  [NOT(OR(NOT(OR(alpha, beta)),(alpha))), beta],
  [OR(alpha, NOT(alpha))],
  [alpha, beta, NOT(OR(NOT(alpha), NOT(beta)))]
]

rules

#%%

def replaceAll(tree:Composition, old, new):
  newargs = tuple(new if arg == old else arg if isinstance(arg, Var) else replaceAll(arg, old, new) for arg in tree.args)
  assert type(tree.args) == type(newargs)
  if newargs != tree.args: return tree.__class__(tree.rel, *newargs)
  return tree


def comp(c:Composition,r:Composition,map:dict):
  print('comp:',c,r)
  if c.rel != r.rel or len(c.args) != len(r.args): return False
  for ca, ra in zip(c.args, r.args):
    print("argcomp:",ca,ra)
    if ca == ra: continue
    if isinstance(ra, FormulaVar) and isinstance(ca, Formula):
      if not ra in map:
        map[ra] = ca
      else:
        if map[ra] != ca: return False
    else: 
      if isinstance(ca, Var) or not comp (ca,ra,map): return False
  return True

def comp(c,r, map:dict):
  if isinstance(r,FormulaVar):
    if r in map: return map[r] == c
    map[r] = c
    return True
  if c.rel != r.rel or len(c.args) != len(r.args): return False
  for ca, ra in zip(c.args, r.args):
    print("argcomp:",ca,ra)
    if ca == ra: continue
    if isinstance(ca, Var) or not comp(ca,ra,map): return False
  return True
    


a = AND((A,IN,A),FORALL(B,(B, IN, B)))
b = AND((A,IN,A),FORALL(B, alpha))

comp(a,b, {})


def check(claim,rule):
  map = {}
  for c,r in zip(claim, rule):
    if not comp(c,r,map): return False
  return True


a = IN(A,B)
b = IN(B,A)

check([a,OR(a,b)], rules[0])

#%%



#%%

def test():

  A, B = Var('A'), Var('B')
  a = IN(A,B)
  assert id(a) == id(replaceAll(a,A,A))
  assert a != replaceAll(a,A,B)
  
  b = IN(B,A)
  assert not comp(a,b,{})
  assert comp(a,a,{})
  assert comp(AND(a,b), AND(a,beta),{})
  assert not comp(AND(a,b), AND(alpha, alpha),{})
  assert not comp(AND(a,b), OR(a,b),{})
  
test()


# %%
