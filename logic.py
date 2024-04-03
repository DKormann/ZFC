
#%%
from functools import cached_property
from typing import Any
def dedup(*args): return list(set(*args))

class Var:
  def __init__(self, name = None):
    self.name = name
    self.atoms = [self]
  def __repr__(self): return self.name if self.name is not None else '<Var>'

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
  
  def repr(self, namemap):
    argnames = [self.namemap[a] if isinstance(a,Var) else a.repr(namemap) for a in self.args]
    if self.rel.inplace: return f'({argnames[0]} {self.namemap[self.rel]} {argnames[1]})'
    if isinstance(self.rel, Quantifier): return f'{self.namemap[self.rel]}{argnames[0]}({argnames[1]})'
    return f'{self.namemap[self.rel]} ({", ".join(argnames)})'
  
  def __repr__(self):  return self.repr(self.namemap)

  def __eq__ (self, other):
    return isinstance(other, Composition) and \
      self.rel == other.rel and \
      self.args == other.args
  
  def createname(self):
    while True:
      newname = chr(ord('A') + (self.namectr%26))
      nummr = self.namectr // 26
      if nummr > 0: newname = newname + str(nummr)
      self.namectr += 1
      if newname not in self.names:
        self.names.add(newname)
        return newname

class Composer:
  arg_type = Var
  res_type = Composition
  def __init__(self, name, arity = -1, inplace = False):
    self.name = name
    self.arity = arity
    self.inplace = inplace
  def __call__(self, *args):
    if self.arity >= 0 and len(args) != self.arity: raise ValueError(f'{self.name} takes {self.arity} arguments, got {len(args)}')
    assert all(isinstance(arg, self.arg_type) for arg in args), f'{self.name} takes {self.arg_type} arguments, got {args}'
    return self.res_type(self, *args)

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
    assert isinstance(form, Formula), f'{self.name} takes a predicate as the second argument, got {form}'
    return self.res_type(self, var, form)

FORALL = Quantifier('∀', 2)
EXISTS = Quantifier('∃', 2)

class Connective(Composer):
  arg_type = Formula
  res_type = Formula

NOT = Connective('¬', 1)
AND = Connective('∧', 2, True)
OR = Connective('∨', 2, True)
IMPLIES = Connective('→', 2, True)
IFF = Connective('↔', 2, True)

P = Predicate('P', 1)
Q = Predicate('Q', 1)

#%%

F = Function('f', arity=1)
ZF = [
  FORALL(X, FORALL(Y, IFF(EQUAL(X, Y), FORALL(A, IFF(IN(A, X), IN(A, Y)))))), # 0. Extensionality
  EXISTS(X, FORALL(A, NOT(IN(A, X)))), # 1. ∅ ∈ N|
  FORALL(A, FORALL(B, EXISTS(X, FORALL(Y, IFF(IN(Y, X), OR(EQUAL(Y, A), IN(Y, B))))))), # 2. Pairing
  FORALL(A, EXISTS(X, FORALL(Y, IFF(IN(Y, X), EXISTS(Z, AND(IN(Y, Z), IN(Z, A))))))), # 3. Union
  EXISTS(X, AND(IN(EMPTY, X), FORALL(A, IFF(IN(A, X), IN(UNITY(A, SET(A)), X))))), # 4. Infinity
  FORALL(X, EXISTS(Y, (FORALL(A, IFF (IN(A, X), AND (IN(A, Y), P(A))))))), # 5. Separation
  FORALL(A, EXISTS(B, FORALL(X, IFF(IN(X, A), IN(F(X), B))))), # 6. Replacement
  FORALL(A, EXISTS(B, FORALL(X, IFF(IN(X, B), SUBSET(X,A))))), # 7. Power Set
  FORALL(A, IMPLIES(NOT(EQUAL(A, EMPTY)), EXISTS(B, AND(IN(B,A),EQUAL(UNITY(A, B), EMPTY))))) # 8. Regularity
]

print("ZF axioms:")
for axiom in ZF: print(axiom)

EXONE = Quantifier('∃!', 2)
def_exone = IFF(EXONE(X, P(X)), AND(EXISTS(X, P(X)), FORALL(X, FORALL(Y, IMPLIES(AND(P(X), P(Y)), EQUAL(X, Y))))))

A_contains_distinct_elements = FORALL(X, FORALL(Y, IMPLIES(AND(IN(X, A), IN(Y, A)), OR(EQUAL(X, Y), EQUAL(INTER(A, A), EMPTY)))))
axiom_of_choice = FORALL(A, IMPLIES(A_contains_distinct_elements, FORALL(X, IMPLIES(IN(X, A), EXISTS(Y ,EXONE(Z, (AND(IN(Z, Y), IN(Z, X)))))))))

ZFC = [
  *ZF,
  def_exone,
  axiom_of_choice
]
# %%
def _(arg1, rel ,arg2): return rel(arg1, arg2)

ISTUPLE = Predicate('is_tuple', 1)
def_tuple = FORALL(X, _(ISTUPLE(X), IMPLIES, EXISTS(A, EXISTS(B, _(X, EQUAL, SET(SET(A), SET(A,B)))))))
ISTUPLEOF = Predicate('is_tuple_of', 3)
def_tupleof = FORALL(X, FORALL(A, FORALL(B, _(ISTUPLEOF(X,A,B), IMPLIES, _(ISTUPLE(X), AND, _(IN(SET(A), X), AND , IN(SET(A,B), X)))))))
def_tupleof

make_tuple = Function('tuple', 2)
def_make_tuple = FORALL(A, FORALL(B, _(make_tuple(A,B), EQUAL, SET(SET(A), SET(A,B)))))

ISFUNCTION = Predicate('is_function', 1)
def_function = FORALL(X, _(ISFUNCTION(X), IMPLIES, FORALL(A, FORALL(B, _(_(make_tuple(A,B), IN, X), IMPLIES, FORALL(C, _(IN(make_tuple(A,C), X), IMPLIES, _(B, EQUAL, C))))))))

