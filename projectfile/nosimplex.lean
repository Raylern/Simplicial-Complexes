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
import Mathlib.Data.Nat.Choose.Basic -- For choose
import Mathlib.Data.Nat.Choose.Sum -- For binomial coefficients
import Mathlib.Data.Int.Basic


/- to be done for the library inclusion :
 - * full graph
-/

open Classical

namespace AbsSCplx

class AbstractSimplicialCplx {V: Type _} (X: Set (Finset V)) where
  singletonInclusion : ∀ (p : V), ({p} ∈ X)
  FaceInclusion : ∀ K ∈  X, ∀ (K' : Finset V), (K' ≠ ∅ ) ∧ (K' ⊆ K) → K' ∈ X
  NoEmpty :  ∅ ∉ X 

variable (V: Type _) (X: Set (Finset V))
#check AbstractSimplicialCplx 
#check AbstractSimplicialCplx X


def Simplex (V : Type _) := Finset V

variable (V : Type _)
#check Simplex


-- def(dimension of a AS) : cardinality 
def dimensionsmplx {V : Type _} (K : Simplex V) : ℤ := Finset.card K - 1
/- def dimension (K : Simplex) : ℕ := Finset.card K.elems -/
def dimension {V : Type _} (K : Finset V) : ℕ := Finset.card K - 1

-- example_1 (simplexes)
instance edge12 : Simplex ℕ := ⟨{1,2}, (by simp)⟩ 

#check edge12
#print edge12

instance point1 : Simplex ℕ  := ⟨{1}, (by simp)⟩ 

instance point2 : Simplex ℕ := ⟨{2}, (by simp)⟩ 

example : dimensionsmplx point1 = 0 := by
  simp
-- end of example_1

-- def(face) : face is a sub-simplex, which is a subset
@[simp]
def face {V : Type _} (K : Finset V) (K' : Finset V) := K' ⊆ K

@[simp]
def all_faces {V : Type _} (K : Finset V) : Set (Finset V) :=  (Finset.powerset K)

lemma is_face {V : Type _} (K : Simplex V) (K' : Simplex V) : face K K' ↔ K' ∈ (all_faces K) := by
  simp
  -- constructor
  -- · intro sub
  --   use K'.s

  -- · intro hx
  --   rcases hx with ⟨x,ssub,eq⟩
  --   have h : x = K'.s
  --   · rw [← eq]
  --     simp
  --   rw [h] at ssub
  --   exact ssub


-- example_2 (face)
example : face {1,2} {1} := by
  unfold face
  · intro x 
    simp
    intro xe1
    left 
    exact xe1


-- lemma num_faces_of_simplex {V : Type _} (K: Simplex V) (h: dimensionsmplx K = n):  Set.ncard {K' : Simplex V| face K K'} = 2^(n+1) := by
--   unfold dimensionsmplx at h
--   -- rw [is_face]
--   -- unfold all_faces
--   sorry

lemma num_faces_finset {V : Type _} (K : Finset V) (h: dimension K = n): Set.ncard (all_faces K) = 2^(n+1) := by
  unfold dimension at h
  unfold all_faces
  have h' : Finset.card K = n+1 := by 
   calc Finset.card K = (Finset.card K - 1) + 1  := by sorry
                    _ = n + 1 := by rw [h]
  
  simp
  rw [h']

    
  
lemma num_faces_of_simplex_dim_i {V : Type _} (K : Simplex V) (h: dimensionsmplx K = n) (i : ℕ) : 
  Set.ncard {f : Simplex V | (face K f)∧(dimensionsmplx f = i) } =  Nat.choose (dimension K + 1) (i+1)  := by
  sorry

def Lℤ : Set (Finset ℤ) := {{n,n+1} | n : ℤ}∪{ {n} | n: ℤ}

lemma subsets_of_edge 
    -- {V : Type _} 
    (n m : ℤ)
    (t : Finset ℤ)
    (t_sub_nm : t ⊆ {n,m})
    (t_non_empty : t ≠ ∅)
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



lemma subsets_of_vertex 
    -- {V : Type _} 
    (n : ℤ)
    (t : Finset ℤ)
    (t_sub_n : t ⊆ {n})
    (t_non_empty : t ≠ ∅)
  : t = {n} := by 

  -- we compute the powerset of {n} in explicit terms
  let p := Finset.powerset ({n} : Finset ℤ)
  have p_explicit: p = {∅, {n}} := by rfl

  -- ... and then conclude
  have t_in_p : t ∈ p := by exact Finset.mem_powerset.mpr t_sub_n

  rw[p_explicit] at t_in_p
  simp[t_non_empty] at t_in_p
  assumption
 


instance realline : AbstractSimplicialCplx Lℤ where
  singletonInclusion := by
   unfold Lℤ
   intro p
   right
   simp
  
  FaceInclusion := by
   intros K h K' k 
   rcases k with ⟨non_empty, sub_K⟩
   unfold Lℤ at *
   simp
   rcases h with (h1|h2)
   simp at h1
   rcases h1 with ⟨n,h1⟩
   rw [← h1] at sub_K
   have k : K' = {n+1} ∨ K' = {n} ∨ K' = {n,n+1} := by
    apply subsets_of_edge
    assumption
    assumption
   

   rcases k with k_n1|(k_n|k_K)
   
   right
   use n+1
   rw [k_n1]

   right
   use n
   rw [k_n]

   left
   use n
   rw [k_K]

   simp at h2
   rcases h2 with ⟨n,h2⟩
   rw [← h2] at sub_K

   have k : K' = {n} := by
    apply subsets_of_vertex
    assumption
    assumption
  
   right
   use n
   rw [k]

  
  NoEmpty := by 
   unfold Lℤ
   simp
  -- end of example_3

lemma face_dim_le {V : Type _} (K K' : Simplex V) (h: dimensionsmplx K = n) (k: face K K') : dimensionsmplx K' ≤ n := by 
 unfold dimensionsmplx at *
 unfold face at k 
 have le: Finset.card K' ≤ Finset.card K := by exact Finset.card_le_of_subset k 
 simp at *
 have h1 : Finset.card K = n + 1 := by sorry
 linarith
  



-- def(skeleton) : a collection of simplexes modified version
 
def nskeleton {V : Type _} (X: Set (Finset V)) (n : ℕ):= {K | (K∈ X)∧(dimension K ≤ n)} 


section

-- lemma(n-skeleton is a simplicial complex) modified version
instance n_skeleton {V : Type _}(X : Set (Finset V)) (h : AbstractSimplicialCplx X) : AbstractSimplicialCplx (nskeleton X n) where  
  singletonInclusion := by 
   unfold nskeleton
   intro p
   constructor
   rcases h with ⟨h1, _, _⟩
   specialize h1 p
   assumption

   unfold dimension
   simp

  
  FaceInclusion := by
   intro K
   intro k 
   unfold nskeleton at *
   simp at *
   rcases k with ⟨k1,k2⟩
   intro K'
   intro _ne
   intro s
   constructor
   rcases h with ⟨_, h2, _⟩
   specialize h2 K
   simp [k1] at h2
   specialize h2 K'
   simp [_ne,s] at h2
   assumption

   have le: Finset.card K' ≤ Finset.card K := by exact Finset.card_le_of_subset s
   unfold dimension at *
   simp at *
   linarith
  
  
  NoEmpty := by 
   unfold nskeleton
   simp
   unfold dimension
   simp
   exact h.NoEmpty



/-
-- def(maximal element)
def max_elem {V : Type _} (X : Set (Finset V)) /-{_: AbstractSimplicialCplx X}-/ 
  {K : Finset V} (_: K ∈ X) : Prop 
  := (∀ K'∈ X, (K ⊂ K') → false)
  #check max_elem X

-- def(free face)
def free_face {V : Type _} {X : Set (Finset V)} {h: AbstractSimplicialCplx X} (K : Finset V) : Prop
  -- := (∃ K' ∈ X.X, face K K')∧(∃ K'∈ X.X, ∀ K'' ∈ X.X, (face K K')∧(face K K'') → (K'=K'')) 
  := (K ∈ X) ∧ (∃ K'∈ X, K ⊆ K') ∧ ∀ K'' ∈ X, (K ⊆ K'' ) → (K' = K'') 

lemma unique_simplex_is_maximal {V : Type _} {X : Set (Finset V)} (h: AbstractSimplicialCplx X) (K : Finset V) (k: K ∈ X)
  : (free_face K) → (∀ K'∈ X,  K' ⊆ K → max_elem K') := by
  sorry

lemma free_face_codim_1 {V : Type _} {X : Set (Simplex V)} (h: AbstractSimplicialCplx X) (K : Simplex V)
  : (free_face X K) → (∀ K'∈ X, dimension K + 1 = dimension K') := by
  sorry


-/

/-
lemma clique_1_skeleton {V : Type _} {X : Set (Finset V)} (h: AbstractSimplicialCplx X) : Prop := by sorry
  -- to be continue
  -- maybe an instance of a full graph

  
--
-/ 
