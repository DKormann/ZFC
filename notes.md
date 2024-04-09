
Set (ø) : Set => bool
Term (A ∈ Y) : Set[] => Set
Function (f) : Set[] => Set
Formula (A = B) : Set[] => bool
Predicate (R) : Set[] => bool
Quantifier (∀) : (Var, Formula) => Formula
Connective (∧) : Formula[] => Formula


+ 1 2 

and and A B C


∀B((0 ∈ B ∧ ∀X(X ∈ B → σX ∈ B)) → ∀Y (Y ∈ B))

∀P((P(0) ∧ ∀X(P(X()) → P(σX))) → ∀Y (P(Y)))


# sequent calculus


[A, B] -> [A and B]
[A] -> [A or B]
[] -> [A or not A]
[A->C, B->C] -> [(A or B) -> C]
[¬AvC ^ ¬BvC] -> [(¬A^¬B) v C]
[¬AvC ^ ¬BvC] -> [¬(AvB) v C]


