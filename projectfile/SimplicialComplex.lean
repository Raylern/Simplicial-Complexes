
/- imports -/
import Mathlib.Tactic
  -- For tactics
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
  -- Finset.card (Finset): the number of elements in a finite set
-- import Mathlib.Data.Set.Card
  -- Set.ncard (Set) : with set.Finite, returns natural number as cardinality
-- import Mathlib.Data.Nat.Pow
  -- For Nat power
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
  -- for subset operations
-- import Mathlib.Data.Finset.Slice
  -- Finset.slice (Nat) : r-subsets in A
import Mathlib.Data.Finset.Powerset
  -- Finset.powerset : to define set of all faces
  -- Finset.powerset_len : n-subsets in A
import Mathlib.Data.Nat.Choose.Basic
  -- Nat.choose (n) (k) : n choose k
import Mathlib.Combinatorics.SimpleGraph.Basic
  -- for simple_graph
import Mathlib.Combinatorics.SimpleGraph.Clique
  -- for clique


/- to be done for the library inclusion :
 - * binomial coefficients
 - * full graph
-/

/- Auxiliary theorems -/
theorem subset_of_singleton {α : Type _} (x : α) (s : Finset α) : s ⊆ {x} ↔ (s=∅) ∨ (s={x}) := by
  simp

/-
theorem subset_of_pair {α : Type _} (x y : α){h : x≠y}(s : Finset α)(subs : s ⊆ ⟨{x,y},(by simp [h])⟩) : ((s=⟨ {x,y},(by simp [h])⟩ )∨(s={x})∨(s={y})∨(s=∅)) := by
  -- we compute the powerset of {x,y} in explicit terms
  rw [← Finset.mem_powerset] at subs
  have p_explicit: Finset.powerset (⟨{x,y},(by simp [h])⟩ : Finset α) = ⟨ {∅, {x} , {y}, ⟨{x,y},(by simp [h])⟩},(by simp [h])⟩  := by
     calc p = Finset.powerset (insert n {m}) := by rfl
         _ = Finset.powerset {m} ∪ Finset.image (insert n) (Finset.powerset {m}) := by  exact Finset.powerset_insert {m} n
         _ = {∅, {m}} ∪ Finset.image (insert n) {∅, {m}} := by congr
         _ = {∅, {m}} ∪ {{n}, {n,m}} := by simp
         _ = {∅, {m}, {n}, {n,m} } := by rfl

  -- ... and then conclude
  have t_in_p : t ∈ p := by exact Finset.mem_powerset.mpr t_sub_nm

  rw[p_explicit] at t_in_p
  simp[t_non_empty] at t_in_p
  assumption
-/

lemma subsets_of_edge (n m : ℤ) (t : Finset ℤ) (t_non_empty : t ≠ ∅) (t_sub_nm : t ⊆ {n,m})
  : t = {m} ∨ t = {n} ∨ t = {n,m} := by

  -- we compute the powerset of {x,y} in explicit terms
  let p := Finset.powerset ({n,m} : Finset ℤ)
  have p_explicit: p = {∅, {m}, {n}, {n,m}} := by
     calc p = Finset.powerset (insert n {m}) := by rfl
         _ = Finset.powerset {m} ∪ Finset.image (insert n) (Finset.powerset {m}) := by  exact Finset.powerset_insert {m} n
         _ = {∅, {m}} ∪ Finset.image (insert n) {∅, {m}} := by congr
         _ = {∅, {m}} ∪ {{n}, {n,m}} := by simp
         _ = {∅, {m}, {n}, {n,m} } := by rfl

  -- ... and then conclude
  have t_in_p : t ∈ p := by exact Finset.mem_powerset.mpr t_sub_nm

  rw[p_explicit] at t_in_p
  simp[t_non_empty] at t_in_p
  assumption

theorem le_imp_pred_le (x y:ℕ) : x ≤ y → x.pred ≤ y.pred := by 
  rw [Nat.pred_le_iff] 
  by_cases z: y=0
  · rw [z]
    simp
    intro xz
    rw [xz]
    simp
  · rw [Nat.succ_pred]
    simp
    exact z

/- main library -/

namespace AbsSCplx

-- def(abstract simplex) : a finite set
def Simplex (V : Type _) : Type _ := Finset V

-- type coersion between simplex and finset
instance toFinset : Coe (Simplex V) (Finset V) where
  coe x := x

instance toSimplex : Coe (Finset V) (Simplex V) where
  coe x := x

instance toSetofSet : Coe (Set (Finset V)) (Set (Set V)) where
  coe x := x

#check Simplex ℕ

-- def(dimension of a AS) : cardinality 
-- @[simp]
-- def dimension {V : Type _} (K : Simplex V) : ℤ  := Finset.card K - 1
-- def dimension (K : Simplex) : ℕ := Finset.card K.elems
def dimension {V : Type _} (K : Simplex V) : ℕ := (Finset.card K).pred
  -- problem when -1 in defining dimension

-- example_1 (simplexes)
def edge12 : Simplex ℤ := ⟨{1,2}, (by simp)⟩ 

#print edge12

def point1 : Simplex ℤ := ⟨{1}, (by simp)⟩    
def point2 : Simplex ℤ := ⟨{2}, (by simp)⟩  

example : dimension edge12 = 1 := by
  simp

#check ↑point1
#check toFinset.coe point1

#eval dimension point1
#eval dimension edge12

def emp : Simplex ℤ := ⟨∅,(by simp)⟩
#eval dimension emp

#eval (Finset.powerset {1,2}) \ {{1,2}}
-- end of example_1

-- def(face) : face is a sub-simplex, which is just a subset
@[simp]
def face {V : Type _} (K : Finset V) (f : Finset V) := f ⊆ K
-- def face {V : Type _} (K : Finset V) (f : Finset V) := f ⊂ K

@[simp]
def all_faces {V : Type _} (K : Finset V) : Finset (Finset V) := (Finset.powerset K)
-- def all_faces {V : Type _} (K : Finset V) : Finset (Finset V) := (Finset.powerset K) \ {K} 

@[simp]
def all_faces_of_dim_i {V : Type _} (K : Finset V) (i:ℕ) : Finset (Finset V) := (Finset.powersetLen (i+1) K)

lemma is_face {V : Type _} (K : Simplex V) (f : Simplex V) : face K f ↔ ↑f ∈ (all_faces K) := by
  -- simp?
  -- unfold face
  -- unfold all_faces
  -- constructor
  simp only [face, all_faces, Finset.mem_powerset]

-- example_2 (face)
example : face {1,2} {1} := by
-- example [edge12 :  Simplex ℕ] [point1 : Simplex ℕ]: face edge12 point1 := by
  simp
  -- unfold face
  -- constructor
  -- · intro x xe1
  --   simp at *
  --   left; exact xe1
  -- · intro h
  --   simp at h

def set12 : Finset ℤ := {1,2}

#eval ((Finset.powerset set12) \ {set12})
-- end of example_2

-- dimension of a face is less than the dim of simplex
lemma face_dim_le {V : Type _} (K : Simplex V) (f : Simplex V) (h: face K f): dimension f ≤ dimension K := by
  -- simp
  -- unfold face at h
  unfold dimension at *
  unfold face at h
  have le: Finset.card f ≤ Finset.card K
  · exact Finset.card_le_of_subset h
  exact le_imp_pred_le _ _ le

lemma num_faces_of_simplex {V : Type _} (K : Simplex V) {h : toFinset.coe K ≠ ∅} :
  Finset.card (all_faces K) = 2^(dimension K + 1) := by
  simp [dimension]
  rw [← Nat.succ_eq_add_one, Nat.succ_pred]
  simp
  exact h

lemma num_faces_of_simplex_dim_i {V : Type _} (K : Simplex V) {h : toFinset.coe K ≠ ∅} (i : ℕ) : 
  Finset.card (all_faces_of_dim_i K i) = Nat.choose (dimension K + 1) (i+1) :=  by
  simp?
  simp [dimension]
  rw [← Nat.succ_eq_add_one (Nat.pred (Finset.card K)), Nat.succ_pred]
  simp
  exact h

-- def(AbsSC) : a collection of simplexes
class AbstractSimplicialCplx (V: Type _) where
  X : Set (Finset V)
  singletonInclusion : ∀ (p:V), (p ∈ (⋃ K∈X, K)) → ({p} ∈ X)  -- (⋃ K∈X, K) is the set of vertices
  noEmpty : ∅ ∉ X
  FaceInclusion : ∀ K ∈ X, ∀ (K' : Finset V),(K'≠ ∅)∧(face K K') → K' ∈ X

-- example_3 (AbstractSimplicalCplx) real line
def Lℤ : Set (Finset ℤ) := {{n,n+1} | n : ℤ}∪{{n}| n: ℤ}-- ∪{⟨∅⟩}
#check Lℤ 

instance realline : AbstractSimplicialCplx ℤ where
  X := Lℤ 
  singletonInclusion := 
    (by
      intro p
      unfold Lℤ
      simp?
    )
  noEmpty := 
    (by
      unfold Lℤ
      simp?
    )
  
  FaceInclusion := 
    (by
      intro K hK K' fK
      rcases fK with ⟨non_empty,sub_K⟩
      unfold Lℤ at *
      rw [is_face] at sub_K
      unfold all_faces at sub_K
      simp
      rcases hK with (⟨p1,hp1⟩|⟨p2,hp2⟩)
      · rw [← hp1] at sub_K
        simp at sub_K
        have k : K' = {p1+1} ∨ K' = {p1} ∨ K' = {p1,p1+1}
        · apply subsets_of_edge
          assumption
          assumption
        rcases k with (h1|h2|h3)
        · right; use p1 + 1; rw [h1]
        · right; use p1    ; rw [h2]
        · left;  use p1    ; rw [h3]
      · rw [← hp2] at sub_K
        simp at sub_K
        rcases sub_K with (emp | h2)
        · exfalso; exact non_empty emp
        · right; use p2; rw [h2]
    )
-- end of example_3

-- lemma(simplex as simplicial complex)
instance simplex {V : Type _} (K : Simplex V) : AbstractSimplicialCplx V where
  X := (all_faces K)\{∅}
  singletonInclusion := 
    (by
      intro p
      unfold all_faces
      simp
      intro x xK x_non_empty px
      apply xK
      exact px
    )
  noEmpty := 
    (by
      simp
    )
  FaceInclusion :=
    (by
      simp
      intro K1 fK1 K1_non_empty
      intro K' K'_nonempty fK'
      constructor
      · exact trans fK' fK1
      · exact K'_nonempty
    )


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
      rintro x ⟨xas,dim⟩ px
      constructor
      · exact X.singletonInclusion p (by simp; use x)
      · simp [dimension]
    )
  noEmpty := 
    (by
      unfold nskeleton
      rintro ⟨sc,dim⟩
      exact X.noEmpty sc
    )
  FaceInclusion :=
    (by
      intro K ske_K
      unfold nskeleton at *
      rcases ske_K with ⟨asc,dim⟩
      simp at *
      intro K' no_empty fK
      constructor
      · exact (X.FaceInclusion K asc K' ⟨no_empty,fK⟩)
      · linarith [face_dim_le K K' fK, dim]
    )

-- lemma(n_skeleton)

-- def corresponding simple graph for 1-skeleton
instance one_skeleton_of_complex {V:Type _} [DecidableEq V] (X: AbstractSimplicialCplx V) : SimpleGraph V where
  Adj := fun (x:V) (y:V) ↦ if h : x ≠ y then {x,y} ∈ (n_skeleton X 1).X else false
  symm := 
    (by
      simp
      rintro x y ⟨neq,hxy⟩
      constructor
      · intro eq
        apply neq
        rw [eq]
      · have ha : ({x,y}:Finset V) = ({y,x}:Finset V) := by
          ext z
          simp
          constructor
          · intro h
            rcases h with (zx|zy)
            · right; exact zx
            · left; exact zy
          · intro h
            rcases h with (zx|zy)
            · right; exact zx
            · left; exact zy
        rw [← ha]
        exact hxy
    )
  loopless := 
    (by
      aesop_graph
    )

-- lemma(1-skeleton of a simplex is a full graph)
lemma one_skeleton_of_simplex_is_clique {V : Type _} [DecidableEq V] (K : Simplex V)(h X = simplex K) : (one_skeleton_of_complex K).is_clique K := by
  simp
  

-- def(maximum element)
def max_elem {V : Type _} (X : AbstractSimplicialCplx V) (K : Simplex V) : Prop 
  := (K∈X.X) ∧ (∀ K'∈ X.X, (face K K') → false)

-- def(free face)
def free_face {V : Type _} (X : AbstractSimplicialCplx V) (K : Simplex V) : Prop
  -- := (∃ K' ∈ X.X, face K K')∧(∃ K'∈ X.X, ∀ K'' ∈ X.X, (face K K')∧(face K K'') → (K'=K'')) 
  := (K∈X.X) ∧ (∃ K'∈ X.X, ∀ K'' ∈ X.X, (face K K')∧(face K K'') → (K'=K'')) 

lemma unique_simplex_is_maximal {V : Type _} (X : AbstractSimplicialCplx V) (K : Simplex V)
  : (free_face X K) → (∀ K'∈ X.X, face K K' → max_elem X K') := by
  intro fXK K' hK' fKK'

lemma free_face_codim_one {V : Type _} (X : AbstractSimplicialCplx V) (K : Simplex V)
  : (free_face X K) → (∀ K'∈ X.X, dimension K + 1 = dimension K') := by
  sorry

end 