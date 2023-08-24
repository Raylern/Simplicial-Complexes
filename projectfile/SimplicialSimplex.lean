-- import Mathlib.Data.Finite.Basic  
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
  -- Finset.card (Finset): the number of elements in a finite set
import Mathlib.Data.Set.Card
  -- Set.ncard : with set.Finite, returns natural number as cardinality
import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
  -- for subset operations


/- to be done for the library inclusion :
 - * binomial coefficients
 - * full graph
-/

namespace AbsSCplx

-- def(abstract simplex) : a finite set
class Simplex (V : Type _) where 
  elems : Finset V
  -- non_empty : Finset.empty ≠ elems
/-
class Simplex where 
  elems : Finset ℕ 
-/

-- def Simplex (V : Type _) : Type _ := Finset V

-- def(dimension of a AS) : cardinality 
def dimension {V : Type _} (K : Simplex V) : ℕ := Finset.card K.elems - 1
/- def dimension (K : Simplex) : ℕ := Finset.card K.elems - 1 -/

-- example_1 (simplexes)
instance edge12 : Simplex ℕ where
  elems : Finset ℕ := {1,2}
  -- non_empty := by simp

#check edge12.elems
  -- #print edge12.elems

instance point1 : Simplex ℕ where
  elems := {1}   
  -- non_empty := by simp
instance point2 : Simplex ℕ where
  elems := {2} 
  -- non_empty := by simp

example : dimension point1 = 0 := by
  simp
-- end of example_1

-- def(face) : face is a sub-simplex, which is just a subset
def face {V : Type _} (K : Simplex V) (f : Simplex V) := f.elems ⊆ K.elems ∧ f.elems ≠ K.elems

-- example_2 (face)
example : face ⟨{1,2},(by simp)⟩ ⟨{1},(by simp)⟩ := by
-- example [edge12 :  Simplex ℕ] [point1 : Simplex ℕ]: face edge12 point1 := by
  unfold face
  constructor
  · intro x 
    simp
    intro xe1
    left; exact xe1
  · intro h
    simp at h
-- end of example_2


lemma num_faces_of_simplex {V : Type _} (K : Simplex V) : Set.ncard {f : Simplex V | face K f} = 2^(n+1)-2 := by
  sorry
  
lemma num_faces_of_simplex_dim_i {V : Type _} (K : Simplex V) (i : ℕ) : 
  Set.ncard {f : Simplex V | (face K f)∧(dimension f = i) } = sorry /- dimension K + 1 choose i+1 -/ := by
  sorry

-- def(AbsSC) : a collection of simplexes
class AbstractSimplicialCplx (V: Type _) where
  X : Set (Simplex V)
  singletonInclusion : ∀ (p : V), (Simplex.mk {p}) ∈ X
  noEmpty : ∀ K ∈ X, Finset.empty ≠ elems
  FaceInclusion : ∀ K ∈  X, ∀ (K' : Simplex V),((K'.elems ≠ ∅) ∧ (face K K')) → K' ∈ X

-- example_3 (AbstractSimplicalCplx) real line
def N2 : Set (Simplex ℕ) := {⟨{n,n+1}⟩ | n : ℕ}∪{ ⟨{n}⟩ | n: ℕ}
instance realline : AbstractSimplicialCplx ℕ where
  X := N2
  singletonInclusion := sorry
  noEmpty := sorry
  FaceInclusion := sorry 
-- end of example_3

-- def(skeleton) : a collection of simplexes
def nskeleton {V : Type _} (X : AbstractSimplicialCplx V) (n : ℕ) : Set (Simplex V)
  := {K | (K∈ X.X)∧(dimension K ≤ n)}

-- lemma(n-skeleton is a simplicial complex)
instance n_skeleton {V : Type _} (X : AbstractSimplicialCplx V) (n : ℕ) :  AbstractSimplicialCplx V where
  X := nskeleton X n 
  singletonInclusion := sorry
  noEmpty := sorry
  FaceInclusion := sorry

-- lemma(1-skeleton is a full graph)
lemma clique_1_skeleton {V : Type _} (X : AbstractSimplicialCplx V) : Prop := by sorry
  -- to be continue
  -- maybe an instance of a full graph

-- def(maximum element)
def max_elem {V : Type _} (X : AbstractSimplicialCplx V) (K : Simplex V) : Prop 
  := (K∈X.X) ∧ (∀ K'∈ X.X, (face K K') → false)

-- def(free face)
def free_face {V : Type _} (X : AbstractSimplicialCplx V) (K : Simplex V) : Prop
  -- := (∃ K' ∈ X.X, face K K')∧(∃ K'∈ X.X, ∀ K'' ∈ X.X, (face K K')∧(face K K'') → (K'=K'')) 
  := (K∈X.X) ∧ (∃ K'∈ X.X, ∀ K'' ∈ X.X, (face K K')∧(face K K'') → (K'=K'')) 

lemma unique_simplex_is_maximal {V : Type _} (X : AbstractSimplicialCplx V) (K : Simplex V)
  : (free_face X K) → (∀ K'∈ X.X, face K K' → max_elem X K') := by
  sorry

lemma free_face_codim_1 {V : Type _} (X : AbstractSimplicialCplx V) (K : Simplex V)
  : (free_face X K) → (∀ K'∈ X.X, dimension K + 1 = dimension K') := by
  sorry

