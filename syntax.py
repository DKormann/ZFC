
#%% Logic
from collections.abc import Iterable

def dedup(*args): return list(set(*args))


class Var:
  def __init__(self, name = None):
    self.name = name
    self.atoms = [self]
  def __repr__(self): return self.name if self.name is not None else '<Var>'
  def __hash__(self): return hash(id(self))

EMPTY = Var('ø')
A,B,C,X,Y,Z = [Var(n) for n in "ABCXYZ"]

class Composition:
  
  def __init__(self, rel, *args):
    self.rel = rel
    self.args = args
    self.atoms = dedup([rel, *sum([a.atoms for a in args],[])])
    self.names = set()
    self.namectr = 0
    self.namemap = {}
    for atom in self.atoms:
      name = atom.name
      if name is None or name in self.names: name = self.createname()
      self.names.add(name)
      self.namemap[atom] = name
    self.hash = hash((id(self.rel), *map(hash, self.args)))
  
  def repr(self, namemap):
    argnames = [self.namemap[a] if isinstance(a,Var) else a.repr(namemap) for a in self.args]
    if self.rel.inplace: return f'({argnames[0]} {self.namemap[self.rel]} {argnames[1]})'
    if isinstance(self.rel, Quantifier): return f'{self.namemap[self.rel]}{argnames[0]}({argnames[1]})'
    return f'{self.namemap[self.rel]} ({", ".join(argnames)})'
  
  def __repr__(self):  return self.repr(self.namemap)

  def __eq__ (self, other):
    return isinstance(other, Composition) and self.hash == other.hash
  
  def polnish(self): return f'{self.namemap[self.rel]} {" ".join([a.polnish() if hasattr(a, "polnish") else str(a) for a in self.args])}'
  
  def createname(self):
    while True:
      newname = chr(ord('A') + (self.namectr%26))
      nummr = self.namectr // 26
      if nummr > 0: newname = newname + str(nummr)
      self.namectr += 1
      if newname not in self.names:
        self.names.add(newname)
        return newname
  
  def __hash__(self):return self.hash


class Composer:
  arg_type = Var
  res_type = Composition
  def __init__(self, name, arity = -1, inplace = False):
    self.name = name
    self.arity = arity
    self.inplace = inplace
  def __call__(self, *args):
    args = [ps(arg) if isinstance(arg, (Iterable)) else arg for arg in args]
    if not all(isinstance(arg, self.arg_type) for arg in args): args = [ps(args)]
    if self.arity >= 0 and len(args) != self.arity: raise ValueError(f'{self.name} takes {self.arity} arguments, got {len(args)}')
    assert all(isinstance(arg, (self.arg_type)) for arg in args), f'{self.name} takes {self.arg_type} arguments, got {args}'
    return self.res_type(self, *args)
  def __repr__(self): return self.name

class Term(Composition): pass
class Function(Composer):
  arg_type = (Var, Term)
  res_type = Term

class SetTerm(Term):
  def repr(self, namemap): return f'{{{", ".join([self.namemap[a] if isinstance(a,Var) else a.repr(namemap) for a in self.args])}}}'

SET = Function('set', -1)
SET.res_type = SetTerm

f = Function('f', 1)
UNITY = Function('∪', 2, True)
INTER = Function('∩', 2, True)
DIFF = Function('-', 2, True)

class Formula(Composition): pass
class Predicate(Composer):
  arg_type = (Var, Term)
  res_type = Formula

IN = Predicate('∈', 2, True)
SUBSET = Predicate('⊆', 2, True)
EQUAL = Predicate('=', 2, True)

class Quantifier(Composer):
  res_type = Formula
  def __call__ (self, var, form):
    assert isinstance(var, Var) or all(isinstance(v,Var) for v in var), f'{self.name} takes a variable(s) as the first argument, got {var.__class__.__name__}'
    assert isinstance(form, (Formula,FormulaVar)) or isinstance(form:=ps(*form),Formula), f'{self.name} takes a predicate as the second argument, got {form}'
    return self.res_type(self, var, form)

FORALL = Quantifier('∀', 2)
EXISTS = Quantifier('∃', 2)

class FormulaVar(Var): pass

alpha = FormulaVar('φ')
beta = FormulaVar('ψ')

class Connective(Composer):
  arg_type = Formula, FormulaVar
  res_type = Formula

NOT = Connective('¬', 1)
AND = Connective('∧', 2, True)
OR = Connective('∨', 2, True)
IMPLIES = Connective('→', 2, True)
IFF = Connective('↔', 2, True)

P = Predicate('P', 1)
Q = Predicate('Q', 1)
N = Var('ℕ')

# parse
def ps(*args):
  assert 0<len(args)<4, f'invalid arguments: {args}'
  if len(args) == 1: return args[0] if isinstance(args[0], (Var, Composition)) else SET(*args[0]) if isinstance(args[0], set) else ps(*args[0])
  elif len(args) == 2: rel,args = args[0], args[1:]
  elif isinstance(args[0], Quantifier): rel, args = args[0], args[1:]
  else:  rel, args = args[1], args[:1] + args[2:]
  args = [a if isinstance(a, (Composition, Var)) else ps(a) for a in args]
  return rel(*args)

import re
def strps(s:str):  return eval("ps({})".format(re.sub(r'\s+', ', ', s)))

#%% testing

def test():
  V1 = Var('V1')
  V2 = Var('V2')
  V3 = Var('V3')
  S1 = SET(V1)
  S2 = ps({V1})
  assert S1 == S2
  assert isinstance(S1, SetTerm)
  assert isinstance(S2, SetTerm)
  assert isinstance(ps({V1,V2,V3}), SetTerm)
  f1 = Function('f', 1)
  assert f1(V1) == ps(f1, V1)
  assert FORALL(V1, IN(V1, V2)) == ps(FORALL(V1, (V1, IN, V2)))
  assert all(i == NOT(V1, IN, EMPTY) for i in [NOT(IN(V1, EMPTY)), ps(NOT, (V1, IN, EMPTY))])
  ps({V1,V2,V3}, IN, V1)
  assert type(AND(alpha, beta)) == Formula
  assert hash(A) != hash(Var('A'))
  assert hash(SET(A)) == hash(SET(A))
  FORALL(A, FormulaVar())

test()

# %% ZFC

Origin = {IN}

# def empty: ∀X. ¬(X ∈ ø)
def_empty = FORALL(X, NOT(IN(X, EMPTY))) 
# def subset: ∀X.∀Y. (X ⊆ Y) ↔ ∀Z. (Z ∈ X → Z ∈ Y)
def_subset = FORALL(X, FORALL(Y, IFF(SUBSET(X,Y), FORALL(Z, IMPLIES(IN(Z,X), IN(Z,Y)))))) 
# def union: ∀X.∀Y. (X ∪ Y) = {Z | Z ∈ X ∨ Z ∈ Y}
def_union = FORALL(X, FORALL(Y, FORALL(Z, IFF(IN(Z, UNITY(X,Y)), OR(IN(Z,X), IN(Z,Y))))))
# def intersection: ∀X.∀Y. (X ∩ Y) = {Z | Z ∈ X ∧ Z ∈ Y}
def_intersection = FORALL(X, FORALL(Y, FORALL(Z, IFF(IN(Z, INTER(X,Y)), AND(IN(Z,X), IN(Z,Y))))))
# def difference: ∀X.∀Y. (X - Y) = {Z | Z ∈ X ∧ Z ∉ Y}
def_difference = FORALL(X, FORALL(Y, FORALL(Z, IFF(IN(Z, DIFF(X,Y)), AND(IN(Z,X), NOT(IN(Z,Y)))))))
#def N: ∀X. (X ∈ ℕ ↔ X = ø ∨ ∃Y. (X = 


assert def_empty == strps("FORALL(X NOT((X IN EMPTY)))")

#%% Axioms

F = Function('f', arity=1)
ZF = [
  # 0. Extensionality: ∀X.∀Y. (X = Y) ↔ ∀Z. (Z ∈ X ↔ Z ∈ Y)
  FORALL(X, (FORALL, Y, ((X, EQUAL, Y), IFF, (FORALL, A, ((A, IN, X), IFF, (A, IN, Y)))))),
  # 1. Empty set: ∃X. ∀A. ¬(A ∈ X)
  EXISTS(X, FORALL(A, NOT((A, IN, X)))),
  # 2. Pairing: ∀A.∀B. ∃X. ∀Y. (Y ∈ X ↔ Y = A ∨ Y = B)
  FORALL(A, FORALL(B, EXISTS(X, FORALL(Y, ((Y, IN, X), IFF, ((Y, EQUAL, A), OR, (Y, EQUAL, B))))))),
  # 3. Union: ∀A.∀B. ∃X. ∀Y. (Y ∈ X ↔ Y ∈ A ∨ Y ∈ B)
  FORALL(A, FORALL(B, EXISTS(X, FORALL(Y, ((Y, IN, X), IFF, ((Y, IN, A), OR, (Y, IN, B))))))),
  # 4. Infinity: ∃X. (∅ ∈ X ∧ ∀A. (A ∈ X → A ∪ {A} ∈ X))
  EXISTS(X, ((EMPTY, IN, X), AND, FORALL(A, IMPLIES((A, IN, X), (UNITY(A, SET(A)), IN, X))))),
  # 5. Separation: ∀A. ∃X. ∀Y. (Y ∈ X ↔ Y ∈ A ∧ P(Y))
  FORALL(A, EXISTS(X, FORALL(Y, ((Y, IN, X), IFF, ((Y, IN, A), AND, (P(Y))))))),
  # 6. Replacement: ∀A. ∃B. ∀X. (X ∈ B ↔ ∃Y. (Y ∈ A ∧ F(Y) = X))
  FORALL(A, EXISTS(B, FORALL(X, ((X, IN, B), IFF, EXISTS(Y, AND((Y, IN, A), (F(Y), EQUAL, X))))))),
  # 7. Power Set: ∀A. ∃B. ∀X. (X ∈ B ↔ X ⊆ A)
  FORALL(A, EXISTS(B, FORALL(X, ((X, IN, B), IFF, (X, SUBSET, A))))),
  # 8. Regularity: ∀A. (A ≠ ∅ → ∃B. (B ∈ A ∧ B ∩ A = ∅))
  FORALL(A, IMPLIES(NOT((A, EQUAL, EMPTY)), EXISTS(B, AND((B, IN, A), ((B, INTER, A), EQUAL, EMPTY)))))
]
if __name__ == '__main__':
  print("ZF axioms:")
  for axiom in ZF: print(axiom)

EXONE = Quantifier('∃!', 2)
def_exone = IFF(EXONE(X, P(X)), AND(EXISTS(X, P(X)), FORALL(X, FORALL(Y, IMPLIES(AND(P(X), P(Y)), EQUAL(X, Y))))))

A_contains_distinct_elements = FORALL(X, FORALL(Y, IMPLIES(AND(IN(X, A), IN(Y, A)), OR(EQUAL(X, Y), EQUAL(INTER(A, A), EMPTY)))))
axiom_of_choice = FORALL(A, IMPLIES(A_contains_distinct_elements, FORALL(X, IMPLIES(IN(X, A), EXISTS(Y ,EXONE(Z, (AND(IN(Z, Y), IN(Z, X)))))))))

ZFC = [
  *ZF,
  def_exone,
  axiom_of_choice]

#%% Construction of logic in ZFC

ISPAIROF = Predicate('is_tuple_of', 3)
def_pairof = FORALL(X, FORALL(A, FORALL(B, EQUAL(X, SET(SET(A), SET(A,B))))))

ISPAIR = Predicate('is_tuple', 1)
def_pair = FORALL(X, (ISPAIR(X), IMPLIES, EXISTS(A, EXISTS(B, ISPAIROF(X, A, B)))))

getpair = Function('tuple', 2)
def_getpair = FORALL(A, FORALL(B, ISPAIROF(getpair(A,B), A, B)))

ISFUNCTION = Predicate('is_function', 1)
def_function = FORALL(A, (ISFUNCTION(A), IMPLIES, FORALL(X, FORALL(Y, FORALL(Z, (((getpair(X,Y), IN, A), AND, (getpair(X,Z), IN, A)), IMPLIES, (Y, EQUAL, Z)))))))
#%%

ZERO = Var('0')
SUCC = Function('σ',1)

PEANO = [
    IN(ZERO, N),
    FORALL(X, ((X, IN, N), IMPLIES, (SUCC(X), IN, N))),
    FORALL(B, (((ZERO, IN, B), AND, FORALL(X, ((X, IN, B), IMPLIES, (SUCC(X), IN, B)))), IMPLIES, FORALL(X, ((X, IN, B), IMPLIES, (X, IN, N))))),
]

PEANO

# %%
# s = Function('s',1)
# FORALL (P, (P(ZERO), AND, FORALL(Y, (P(Y), IMPLIES, P(s(Y))))))

# %%
