import Mathlib.Data.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Data.Set.Basic


namespace AbsSCplx

class AbstractSimplicialCplx {V: Type _} (X : Set (Finset V)) where
  singletonInclusion : ∀ (p:V), {p} ∈ X
  noEmpty : ∅ ∉ X
  FaceInclusion : ∀ K ∈  X, ∀ (K' : Finset V),((¬ (K'=∅)) ∧ (K'⊆ K)) → K' ∈ X

def N2 : Set (Finset ℕ ) := {{n,n+1}| n : ℕ}
instance realline : AbstractSimplicialCplx N2 where
  singletonInclusion := by

  noEmpty :=
  FaceInclusion := 






end