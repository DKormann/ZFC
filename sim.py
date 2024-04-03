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
    hashes = [hash(e) for e in self.data]
    return hash(tuple(sorted(hashes)))
  def __eq__(self, other):
    return isinstance(other, S) and self.data == other.data
  
  def u(self,other):
    res = S()
    res.data = self.data.union(other.data)
    return res

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