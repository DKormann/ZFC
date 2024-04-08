#%%
class S:
  def __init__(self, *elements):
    assert all(isinstance(e, S) for e in elements), f'only sets allowed'
    self.data = set(elements)
  def __repr__(self):
    if self.data == set(): return '∅'
    return f'{self.data}'
  def __hash__(self):
    if self.data == set(): return 0
    return hash(tuple(sorted([hash(e) for e in self.data])))
  def __eq__(self, other): return isinstance(other, S) and self.data == other.data
  def u(self,other): return S(*self.data.union(other.data))
  def d(self,other): return S(*self.data.difference(other.data))
  def elemof(self,other): return self in other.data
  def sub(self,other): return all(e in other.data for e in self.data)

def Num(n):
  if n == 0: return S()
  prev = Num(n-1)
  return prev.u(S(prev))

def Pair(a,b):
  return S(S(a),(S(a,b)))

def Tuple(*args):
  res = Pair(args[0],args[1])
  for a in args[2:]: res = Pair(res,a)
  return res

n0 = Num(0)
n1 = Num(1)
n2 = Num(2)
n3 = Num(3)

t123 = Tuple(n1,n2,n3)
t321 = Tuple(n3,n2,n1)

Tuple(n1,n2,n3) == Tuple(Tuple(n1,n2),n3)
Tuple(Tuple(n1,n2), Tuple(n1,n2)) == S(S(Tuple(n1,n2)))
Tuple(n1,n1)

#%%
def P(x:S):
  def fn(ls):
    if ls == []: return [S()]
    head = ls[0]
    tail = ls[1:]
    tail = fn(tail)
    res = []
    for t in tail:
      res.append(t.u(S(head)))
      res.append(t)
    return res
  return S(*fn(list(x.data)))
    

P(n2)