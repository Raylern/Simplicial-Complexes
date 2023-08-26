
/- imports -/
-- import Mathlib.Data.Finite.Basic  
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
  -- Finset.card (Finset): the number of elements in a finite set
import Mathlib.Data.Set.Card
  -- Set.ncard (Set) : with set.Finite, returns natural number as cardinality
import Mathlib.Tactic
  -- For tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
  -- for subset operations
import Mathlib.Data.Finset.Slice
  -- for slice
import Mathlib.Data.Finset.Powerset
  -- powerset to define set of all faces


/- to be done for the library inclusion :
 - * binomial coefficients
 - * full graph
-/

theorem subset_of_singleton {α : Type _} (x : α) (s : Finset α): s ⊆ {x} ↔ (s=∅) ∨ (s={x}) := by
  simp

theorem subset_of_pair {α : Type _} (x : α)(y : α){h : x≠y}(s : Finset α) : s ⊆ ⟨{x,y},(by simp [h])⟩ ↔((s=⟨ {x,y},(by simp [h])⟩ )∨(s={x})∨(s={y})∨(s=∅)) := by
  sorry


/- main library -/

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
#check Simplex ℕ 

-- def(dimension of a AS) : cardinality 
@[simp]
def dimension {V : Type _} (K : Simplex V) : ℕ := Finset.card K.elems - 1
/- def dimension (K : Simplex) : ℕ := Finset.card K.elems -/

-- example_1 (simplexes)
instance edge12 : Simplex ℤ where
  elems : Finset ℤ := {1,2}
  -- non_empty := by simp

#print edge12
#eval edge12.elems

instance point1 : Simplex ℤ where
  elems := {1}   
  -- non_empty := by simp
instance point2 : Simplex ℤ where
  elems := {2} 
  -- non_empty := by simp

example : dimension edge12 = 1 := by
  simp

#eval dimension point1
#eval dimension edge12
-- end of example_1

-- def(face) : face is a sub-simplex, which is just a subset
-- @[simp]
def face {V : Type _} (K : Simplex V) (f : Simplex V) := f.elems ⊂ K.elems

-- @[simp]
def all_faces {V : Type _} (K : Simplex V) : Set (Simplex V) := Simplex.mk '' (Finset.powerset K.elems \ {K.elems})

lemma is_face {V : Type _} (K : Simplex V) (f : Simplex V) : face K f ↔ f ∈ (all_faces K) := by
  simp
  constructor
  · rintro ⟨sub,not_sub⟩ 
    use f.elems
    simp
    constructor
    · exact sub
    · intro eq
      apply not_sub
      simp [eq]
  · intro hx
    rcases hx with ⟨x,ssub,eq⟩
    have h : x = f.elems
    · rw [← eq]
      simp
    rw [h] at ssub
    rw [face]
    rw [ssubset_iff_subset_ne]
    simp at ssub
    exact ssub

-- example_2 (face)
example : face ⟨{1,2}⟩ ⟨{1}⟩ := by
-- example [edge12 :  Simplex ℕ] [point1 : Simplex ℕ]: face edge12 point1 := by
  unfold face
  constructor
  · intro x xe1
    simp at *
    left; exact xe1
  · intro h
    simp at h

def set12 : Finset ℤ := {1,2}
#eval ((Finset.powerset set12) \ {set12})
-- end of example_2

lemma num_faces_of_simplex {V : Type _} (K : Simplex V) : Set.ncard {f : Simplex V | face K f} = 2^(dimension K + 1) - 2 := by
  sorry
  
lemma num_faces_of_simplex_dim_i {V : Type _} (K : Simplex V) (i : ℕ) : 
  Set.ncard {f : Simplex V | (face K f)∧(dimension f = i) } = sorry /- dimension K + 1 choose i+1 -/ := by
  sorry

-- def(AbsSC) : a collection of simplexes
class AbstractSimplicialCplx (V: Type _) where
  X : Set (Simplex V)
  singletonInclusion : ∀ (p : V), (Simplex.mk {p}) ∈ X
  -- noEmpty : ∀ K ∈ X, K.elems ≠ ∅
  FaceInclusion : ∀ K ∈  X, ∀ (K' : Simplex V),(face K K') → K' ∈ X

-- example_3 (AbstractSimplicalCplx) real line
def N2 : Set (Simplex ℤ) := {⟨{n,n+1}⟩ | n : ℤ}∪{ ⟨{n}⟩ | n: ℤ}∪{⟨∅⟩}
#check N2


instance realline : AbstractSimplicialCplx ℤ where
  X := N2
  singletonInclusion := 
    (by
      intro p
      unfold N2
      left;
      right;
      use p
    )
  /-
  noEmpty := 
    (by
      intro K hK
      unfold N2 at hK
      rcases hK with (h1 | h2)
      · simp at h1
        rcases h1 with ⟨p, np⟩ 
        rw [← np]
        simp
      · simp at h2
        rcases h2 with ⟨p, np⟩ 
        rw [← np]
        simp
    )
    -/
  FaceInclusion := 
    (by
      intro K hK
      intro K' fK
      unfold N2 at *
      by_cases emp : K'=⟨∅⟩
      · right; simp; exact emp
      · left; right;
        simp
        rcases hK with ((h1 | h2) | h3)
        · simp at h1
          rcases h1 with ⟨p, np⟩
          rw [← np, is_face,all_faces] at fK
          simp at fK
          rcases fK with ⟨x,⟨yp,hk'⟩⟩
          rcases yp with ⟨c1,c2⟩
          rw [subset_of_pair p (p+1) () x] at c1
          rcases c1 with (x1|x2|x3|x4)
          · exfalso
            apply c2
            exact x1
          · use p
          sorry
        · simp at h2
          rcases h2 with ⟨p, np⟩
          rw [← np, is_face, all_faces] at fK
          simp at fK
          rcases fK with ⟨x,⟨yp,hk'⟩⟩
          exfalso
          have : x = ∅ 
          · rcases yp with ⟨yp1,yp2⟩
            have : x ⊆ {p}
            · intro y hy
              simp
              exact yp1 y hy
            simp at this
            rcases this with (h1|h2)
            · exact h1
            · exfalso
              exact (yp2 h2)
          rw [this] at hk'
          rw [←hk'] at emp
          simp at emp
        · simp at h3
          exfalso
          exact (emp h3)
          sorry
    )
-- end of example_3

-- def(skeleton) : a collection of simplexes
def nskeleton {V : Type _} (X : AbstractSimplicialCplx V) (n : ℕ) : Set (Simplex V)
  := {K | (K∈ X.X)∧(dimension K ≤ n)}

-- lemma(n-skeleton is a simplicial complex)
instance n_skeleton {V : Type _} (X : AbstractSimplicialCplx V) (n : ℕ) :  AbstractSimplicialCplx V where
  X := nskeleton X n 
  singletonInclusion := 
    (by
      intro p
      unfold nskeleton
      simp
      exact X.singletonInclusion p
    )
  /-
  noEmpty := 
    (by
      intro K nskeK
    )
  -/
  FaceInclusion :=
    (by
      sorry
    )

-- lemma(n_skeleton)



-- lemma(1-skeleton is a full graph)
lemma clique_1_skeleton {V : Type _} (X : Simplex V) : Prop := by sorry
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

end 