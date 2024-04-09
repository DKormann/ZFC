#%%
from dataclasses import dataclass
from syntax import *

alpha = FormulaVar('α')
beta = FormulaVar('β')

def replaceAll(tree:Composition, old, new):
  newargs = tuple(new if arg == old else arg if isinstance(arg, Var) else replaceAll(arg, old, new) for arg in tree.args)
  assert type(tree.args) == type(newargs)
  if newargs != tree.args: return tree.__class__(tree.rel, *newargs)
  return tree

def comp(c,r, r2c, verbose=False):
  if verbose:print("compare",c,r)
  if isinstance(r,Var): r2c[r] = r2c.get(r,c)
  if r in r2c: return r2c[r] == c
  if isinstance(c,Var):return False
  return not any(ca != ra and not(isinstance(ca, (Composition,Var)) and comp(ca,ra,r2c)) for ca, ra in zip(*map(lambda x:[x.rel,len(x.args),*x.args],[c,r])))

def check(claim,rule):
  map = {}
  return all(comp(c,r,map) for c,r in zip(claim, rule))

comp(OR(alpha,beta), OR(alpha,beta), {})

# AND(alpha, beta) 

#%%
# basically sequent calculus rules

(rules := sum([

  conrules:=[
    [alpha, OR(alpha, beta)],
    [OR(alpha, alpha), alpha],
    [alpha, NOT(NOT(alpha))],
    [NOT(NOT(alpha)), alpha],
    [OR(alpha,beta),OR(beta,alpha)],
    [NOT(OR(NOT(OR(alpha, beta)),(alpha))), beta],
    [OR(alpha, NOT(alpha))],
    [alpha, beta, NOT(OR(NOT(alpha), NOT(beta)))],
  ],

  setrules := [
    [EQUAL(B,B)],
    [EQUAL(A,B),EQUAL(B,A)],
    [EQUAL(A,B), EQUAL(B,C), EQUAL(A,C)],
    [IN(A,B), EQUAL(A,C), IN(C,B)],
    [IN(A,B), EQUAL(B,C), IN(A,C)],
  ],

  quantrules := [
    [P(A), EXISTS(A,P(A))],
    [FORALL(A,P(A)), P(X)],
    [NOT(FORALL(X,P(X))), EXISTS(X,NOT(P(X)))],
    [NOT(EXISTS(X,P(X))), FORALL(X,NOT(P(X)))],
  ],

  defs := [
    [IMPLIES(alpha,beta), OR(NOT(alpha), beta)],
    [AND(alpha,beta), NOT(OR(NOT(alpha),NOT(beta)))],
    [SUBSET(A,B),FORALL(X,((X,IN,A),IMPLIES,(X,IN,B)))],
    [EQUAL(C,UNITY(A,B)),FORALL(X, IFF((X,IN,C),OR((X,IN,B),(X,IN,A))))],
    [EQUAL(C,INTER(A,B)),FORALL(X, IFF((X,IN,C),AND((X,IN,B),(X,IN,A))))],
    [EQUAL(C,SET(A)),FORALL(X, IFF((X, IN, C),(X, EQUAL, A)))],
    [EQUAL(SET(A,B), UNITY(SET(A), SET(B)))],
  ],
  [list(reversed(d)) for d in defs]

],[]))

#%%

@dataclass(frozen=True)
class ProofStep:
  conditions: list[Formula]
  conclusion: Formula
  rule:list [Formula]

@dataclass
class Proof:
  axioms: list
  steps: list[ProofStep]
  def check(self):
    hist = []
    for step in self.steps:
      if not all(cond in hist or cond in self.axioms for cond in step.conditions): return False
      check(step.conditions+[step.conclusion], step.rule)
      hist.append(step.conclusion)
    return True
  
  def build(self,goals):
    hist = []
    def fill_rule(rule_conds:list, binding:dict, axioms:list)->tuple[bool,dict,list]:
      if rule_conds == []: return True, binding, axioms
      rule_cond = rule_conds[0]
      for ax in self.axioms+hist:
        b = binding.copy()
        if (comp(ax,rule_cond,b)):
          succ, newb, axioms = fill_rule(rule_conds[1:], b, axioms+[ax])
          if succ: return True, newb, axioms
      return False, {}, []
    for goal in goals:
      goal_proven = False
      for rule in rules:
        binding = {}
        if comp(goal, rule[-1],binding):
          conditions = rule[:-1]
          succ,_,axioms = fill_rule(conditions, binding,[])
          if succ: 
            self.steps.append(ProofStep(axioms, goal,rule))
            hist.append(goal)
            goal_proven = True
            break
      if not goal_proven: return False
    assert self.check()
    return True
          
gamma = FormulaVar('γ')
delta = FormulaVar('δ')

#%%

proof = Proof([],[])


#%%

proof = Proof([gamma], [])
assert proof.build([
  OR(gamma,delta),
  OR(delta, gamma)
])

proof.steps
# todo: prove demorgan
claim = [IFF(NOT(AND(alpha, beta)), OR(NOT(alpha),NOT(beta)))]
print(claim)


proof = Proof([],[])




assert proof.build([
  OR(alpha, NOT(alpha)),
  OR(beta, NOT(beta)),
  OR(NOT(alpha),alpha),
  IMPLIES(alpha, alpha),
  
  
  # OR(NOT(AND(alpha, beta)), NOT(NOT(AND(alpha,beta)))),
  # OR(NOT(NOT(AND(alpha, beta))), NOT((AND(alpha,beta)))),
  OR((AND(alpha, beta)), NOT((AND(alpha,beta)))),
  OR(NOT(AND(alpha, beta)), (AND(alpha,beta))),
  OR(NOT(AND(alpha, beta)), (OR(NOT(alpha),NOT(beta)))),
  
  
  
  # OR(NOT(AND(alpha,beta)), NOT(OR(NOT(alpha),NOT(beta)))),
  # IMPLIES((AND(alpha,beta)), NOT(OR(NOT(alpha),NOT(beta)))),
  
])

proof.steps[-1].conclusion

#%%

def test():
  A, B = Var('A'), Var('B')
  a = IN(A,B)
  b = IN(B,A)
  assert id(a) == id(replaceAll(a,A,A))
  assert a != replaceAll(a,A,B)
  
  assert comp(a,b,{})
  assert comp(a,a,{})
  assert comp(AND(a,b), AND(a,beta),{})
  assert not comp(AND(a,b), AND(alpha, alpha),{})
  assert not comp(AND(a,b), OR(a,b),{})
  assert not (comp (AND(a,AND(a,b)), AND(a,OR(a,b)),{}))

  assert check([a,OR(a,b)], conrules[0])
  assert not check([a,OR(a,b)], conrules[1])
  assert not check([a,OR(b,a)], conrules[0])
  assert check([a,OR(a,a)], conrules[0])
  assert check([OR(a,NOT(a))],conrules[6])
  assert check([a,OR(b,b),NOT(OR(NOT(a), NOT(OR(b,b))))],conrules[7])

  proof = Proof([gamma], steps = [
    ProofStep([gamma], OR(gamma,delta), rules[0]),
    ProofStep([OR(gamma,delta)], OR(gamma,delta), rules[0]),
  ])
  assert proof.check()

  #TODO: quantrules!!! 
  
test()

