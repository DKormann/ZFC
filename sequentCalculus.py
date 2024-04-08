#%%
from syntax import *
#%%
alpha = FormulaVar('α')
beta = FormulaVar('β')

# basically sequent calculus rules
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

def comp(c,r, r2c):
  if isinstance(r,FormulaVar): r2c[r] = r2c.get(r,c)
  if r in r2c: return r2c[r] == c
  return not any(ca != ra and not(isinstance(ca, Formula) and comp(ca,ra,r2c)) for ca, ra in zip(*map(lambda x:[x.rel,len(x.args),*x.args],[c,r])))

def check(claim,rule):
  map = {}
  return all(comp(c,r,map) for c,r in zip(claim, rule))

#%%

def test():
  A, B = Var('A'), Var('B')
  a = IN(A,B)
  b = IN(B,A)
  assert id(a) == id(replaceAll(a,A,A))
  assert a != replaceAll(a,A,B)
  
  assert not comp(a,b,{})
  assert comp(a,a,{})
  assert comp(AND(a,b), AND(a,beta),{})
  assert not comp(AND(a,b), AND(alpha, alpha),{})
  assert not comp(AND(a,b), OR(a,b),{})
  assert not (comp (AND(a,AND(a,b)), AND(a,OR(a,b)),{}))

  assert check([a,OR(a,b)], rules[0])
  assert not check([a,OR(a,b)], rules[1])
  assert not check([a,OR(b,a)], rules[0])
  assert check([a,OR(a,a)], rules[0])
  assert check([OR(a,NOT(a))],rules[6])
  assert check([a,OR(b,b),NOT(OR(NOT(a), NOT(OR(b,b))))],rules[7])
  
test()

# %%

