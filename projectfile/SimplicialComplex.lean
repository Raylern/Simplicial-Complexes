/- imports -/
import Mathlib.Tactic
  -- For tactics
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
  -- Finset.card (Finset V): the number of elements in a finite set
    -- used in definition of dimension
  -- Finset.one_lt_card_iff: card > 1 iff ∃ a,b ∈ S, a≠b
    -- used to prove lemma free_face_codimesion
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
  -- for subset operations
import Mathlib.Data.Finset.Powerset
  -- Finset.powerset : 
    -- used to define set of all faces
  -- Finset.powerset_len : r-subsets in A
    -- used to define faces of dimension r
import Mathlib.Data.Nat.Choose.Basic
  -- Nat.choose (n) (k) : n choose k
    -- used in lemma num_faces_of_simplex_dim_i
  -- Nat.succ_sub_succ_eq_sub : a.succ-b.succ=a-b
    -- used to prove an auxiliary theorem diff_pred_eq_diff
import Mathlib.Combinatorics.SimpleGraph.Basic
  -- SimpleGraph
    -- used to create instance one_skeleton_as_graph
import Mathlib.Combinatorics.SimpleGraph.Clique
  -- SimpleGraph.IsClique
    -- used in lemma one_skeleton_of_simplex_is_clique
  -- SimpleGraph.isClique_iff
    -- used to prove lemma one_skeleton_of_simplex_is_clique
  
/- end of imports -/


/- Auxiliary theorems -/

/-
statement : Any subset of a singleton is either the empty set or the whole set.
used in : not used
-/
theorem subset_of_singleton {α : Type _} (x : α) (s : Finset α) : s ⊆ {x} ↔ (s=∅) ∨ (s={x}) := by
  simp

/-
statement : Any subset of a pair of integers is either one of two singletons or the whole set.
used in : instance realline.FaceInclusion
-/
lemma subsets_of_edge (n m : ℤ) (t : Finset ℤ) (t_non_empty : t ≠ ∅) (t_sub_nm : t ⊆ {n,m})
  : t = {m} ∨ t = {n} ∨ t = {n,m} := by

  -- compute the powerset of {x,y} in explicit terms
  let p := Finset.powerset ({n,m} : Finset ℤ)
  have p_explicit: p = {∅, {m}, {n}, {n,m}} := by
     calc p = Finset.powerset (insert n {m}) := by rfl
         _ = Finset.powerset {m} ∪ Finset.image (insert n) (Finset.powerset {m}) := by  exact Finset.powerset_insert {m} n
         _ = {∅, {m}} ∪ Finset.image (insert n) {∅, {m}} := by congr
         _ = {∅, {m}} ∪ {{n}, {n,m}} := by simp
         _ = {∅, {m}, {n}, {n,m} } := by rfl

  -- and then conclude, simp will write it in 'or'
  have t_in_p : t ∈ p := by exact Finset.mem_powerset.mpr t_sub_nm
  rw [p_explicit] at t_in_p
  simp [t_non_empty] at t_in_p
  assumption


/-
statement : natural number x≤y implies their predecessor is le
used in : theorem face_dim_le
-/
theorem le_imp_pred_le {x y:ℕ} : x ≤ y → x.pred ≤ y.pred := by 
  rw [Nat.pred_le_iff]
  by_cases z: y=0
  · rw [z]             -- If y=0, y.pred=0. Treated specially
    simp
    intro xz
    rw [xz]
    simp
  · rw [Nat.succ_pred] -- If y>0, usual case in math
    simp
    exact z
    
/-
statement : {x,y}≠∅ 
used in : not used
Remark: having it because of meta Type used and Lean can't do it automatically
-/
theorem two_set_non_empty {V: Type _} (x y : V) {xyneq : x ≠ y}: (⟨{x,y},(by simp [xyneq])⟩ :Finset V) ≠ ∅ := by
  intro h
  have eq_card: Finset.card ⟨{x,y},(by simp [xyneq])⟩ = Finset.card ∅
  · rw [h]
  simp at eq_card

/-
statement : {x,y}≠{a}
used in : example::(no free face in realline) when proving {n}⊂{n,n+1} (used implicitly)
Remark: having it because of meta Type used and Lean can't do it automatically
-/
theorem two_set_non_singleton {V: Type _} (x y : V) {xyneq : x ≠ y}: ∀ (a:V), (⟨{x,y},(by simp [xyneq])⟩ :Finset V) ≠ ({a}:Finset V):= by
  intro a h
  have eq_card: Finset.card ⟨{x,y},(by simp [xyneq])⟩ = Finset.card {a}
  · rw [h]
  simp at eq_card

/-
statement : ⊂ + ⊆ => ⊂  
used in : lemma unique_simplex_is_maximal, lemma free_face_max_len
-/
theorem trans_lt_le_imp_lt {V: Type _} {p q r: Finset V} : p⊂q → q⊆r → p⊂r := by
  intro spq qr
  -- exact (trans spq qr) -- this don't work
  constructor
  · exact (Trans.trans spq.1 qr)
  · intro rp
    have qp : q⊆p
    ·  exact (Trans.trans qr rp)
    exact spq.2 qp

/-
statement : a.pred-b.pred=a-b given non_zero (since 0.pred=0)
used in : lemma free_face_codim_one
-/
theorem diff_pred_eq_diff (p q: ℕ) (p_nz : p ≠ 0) (q_nz : q ≠ 0) : p.pred - q.pred = p - q := by
  rw [← (Nat.succ_sub_succ_eq_sub p.pred q.pred)]
  rw [Nat.succ_pred]
  rw [Nat.succ_pred]
  exact q_nz
  exact p_nz

/-
statement : superset of a non-empty set is non-empty
used in : lemma free_face_codim_one
-/
theorem superset_nonempty {V : Type _} (S S': Finset V) (h: S≠∅) (s : S⊆S') : S'≠ ∅ := by
  intro S'_empty
  rw [S'_empty] at s
  exact h (Finset.subset_empty.1 s)

/- end of Auxiliary theorems -/




/- main library -/

namespace AbsSCplx

-- def(abstract simplex) : a finite set
  /-
    remark : we allow empty simplex and assume non-emptiness in some theorems required
  -/
def Simplex (V : Type _) : Type _ := Finset V

-- type coersion between simplex and finset
instance toFinset : Coe (Simplex V) (Finset V) where
  coe x := x

instance toSimplex : Coe (Finset V) (Simplex V) where
  coe x := x

instance toSetofSet : Coe (Set (Finset V)) (Set (Set V)) where
  coe x := x

#check Simplex ℕ

-- def(dimension of a AS) : cardinality of a finite set
-- @[simp]
def dimension {V : Type _} (K : Simplex V) : ℕ := (Finset.card K).pred




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
  /-
    remark : for convenience the simplex itself is included as its faces, 
    the version that it is not included is proper_face

    remark : all_faces is define to facilitate proving
  -/ 
@[simp]
def face {V : Type _} (K : Finset V) (f : Finset V) := f ⊆ K

@[simp]
def proper_face {V : Type _} (K : Finset V) (f : Finset V) := f ⊂ K

@[simp]
def all_faces {V : Type _} (K : Finset V) : Finset (Finset V) := (Finset.powerset K)
-- def all_faces {V : Type _} (K : Finset V) : Finset (Finset V) := (Finset.powerset K) \ {K} 

@[simp]
def all_faces_of_dim_i {V : Type _} (K : Finset V) (i:ℕ) : Finset (Finset V) := (Finset.powersetLen (i+1) K)

-- lemma(helps to prove some simplex is a faces)
lemma is_face {V : Type _} (K : Simplex V) (f : Simplex V) : face K f ↔ ↑f ∈ (all_faces K) := by
  simp only [face, all_faces, Finset.mem_powerset]




-- example_2 (face)
example : face edge12 point1 := by
  simp

def set12 : Finset ℤ := {1,2}
#eval ((Finset.powerset set12) \ {set12})
-- end of example_2




-- lemma(dimension of a face is less than the dim of simplex)
lemma face_dim_le {V : Type _} (K : Simplex V) (f : Simplex V) (h: face K f): dimension f ≤ dimension K := by
  unfold dimension at *
  unfold face at h
  have le: Finset.card f ≤ Finset.card K
  · exact Finset.card_le_of_subset h
  exact le_imp_pred_le le

-- lemma(dimension of a proper face is strictly less than the dim of simplex)
lemma proper_face_dim_lt {V : Type _} (K : Simplex V) (f : Simplex V) {non_empty : toFinset.coe f ≠ (∅:Finset V)} (h: proper_face K f): dimension f < dimension K := by
  unfold dimension at *
  unfold proper_face at h
  have lt: Finset.card f < Finset.card K
  · rw [lt_iff_le_and_ne]
    constructor
    · exact Finset.card_le_of_subset h.1
    · intro card_eq_of
      have : Finset.card f < Finset.card K
      · exact Finset.card_lt_card h
      linarith
  rw [Nat.lt_pred_iff, Nat.succ_pred]
  exact lt
  simp
  exact non_empty

-- lemma(total num of faces of a simplex is 2^(n+1))
lemma num_faces_of_simplex {V : Type _} (K : Simplex V) {non_empty : toFinset.coe K ≠ (∅:Finset V)} :
  Finset.card (all_faces K) = 2^(dimension K + 1) := by
  simp [dimension]
  rw [← Nat.succ_eq_add_one, Nat.succ_pred]
  simp
  exact non_empty

-- lemma(total num of faces of dim i of a simplex is (n+1) choose (i+1))
lemma num_faces_of_simplex_dim_i {V : Type _} (K : Simplex V) {h : toFinset.coe K ≠ (∅:Finset V)} (i : ℕ) : 
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
instance simplex_as_cplx {V : Type _} (K : Simplex V) : AbstractSimplicialCplx V where
  X := (all_faces K)\{∅}
  singletonInclusion := 
    (by
      intro p
      unfold all_faces
      simp
      intro x xK _ px
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
      intro K1 fK1 _
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
      rintro x ⟨xas,_⟩ px
      constructor
      · exact X.singletonInclusion p (by simp; use x)
      · simp [dimension]
    )
  noEmpty := 
    (by
      unfold nskeleton
      rintro ⟨sc,_⟩
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


-- def(corresponding simple graph for 1-skeleton)
instance one_skeleton_as_graph {V:Type _} [DecidableEq V] (X: AbstractSimplicialCplx V) : SimpleGraph V where
  Adj := fun (x:V) (y:V) ↦ if _ : x ≠ y then {x,y} ∈ (n_skeleton X 1).X else false
  -- 2 vertices are adjacent iff there is an 1-simplex in the 1-skeleton
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
lemma one_skeleton_of_simplex_is_clique {V : Type _} [DecidableEq V] (K : Simplex V): (one_skeleton_as_graph (simplex_as_cplx K)).IsClique (toFinset.coe K) := by
  rw [SimpleGraph.isClique_iff]
  -- clique iff any pair of vertices are connected
  unfold Set.Pairwise
  intro x xK y yK xyne 
  simp
  unfold SimpleGraph.Adj

  -- {x,y} is in the complex K
  have h : {x,y}∈ (simplex_as_cplx K).X
  · unfold simplex_as_cplx
    simp
    intro z
    simp
    rintro (zx|zy)
    · rw [zx]; exact xK
    · rw [zy]; exact yK

  -- {x,y} belongs to nskeleton K 1 iff {x,y} in complex K and of dimension less than 1
  have h : {x,y} ∈ (n_skeleton (simplex_as_cplx K) 1).X
  · unfold n_skeleton
    simp
    unfold nskeleton
    constructor
    · exact h          -- {x,y} in complex K
    · unfold dimension -- of dimension less than 1
      simp [xyne]
  unfold one_skeleton_as_graph
  simp
  constructor
  · exact xyne
  · exact h




-- def(maximum element) : 1. It is an element 2. it is maximal
@[simp]
def max_elem {V : Type _} (X : AbstractSimplicialCplx V) (M : Simplex V) : Prop 
--  := (K∈X.X) ∧ (∀ K'∈ X.X, (face K K') → false)
  := (M∈X.X) ∧ (∀ K ∈ X.X, (face K M) → K=M)  -- since in def(face) itself is included

-- def(free face) : a proper face of a unique simplex (in fact, maximal) in complex
def free_face {V : Type _} (X : AbstractSimplicialCplx V) (f : Simplex V) : Prop
  -- := (∃ K' ∈ X.X, face K K')∧(∃ K'∈ X.X, ∀ K'' ∈ X.X, (face K K')∧(face K K'') → (K'=K'')) 
  := (f∈X.X) ∧ (∃ M ∈ X.X, proper_face M f) ∧ (∀ M ∈ X.X, ∀ M' ∈ X.X, (proper_face M f)∧(proper_face M' f) → (M=M')) 




-- example_4 (maximal & free face)
example : max_elem realline edge12 := by -- {1,2} is a maximal element in realline
  unfold realline
  unfold Lℤ 
  simp
  unfold edge12
  constructor
  · left           -- {1,2} is an element in realline
    use 1
    simp
  · intro K hK feK -- no larger faces containing {1,2}
    rcases hK with (⟨n,h1⟩|⟨n,h2⟩)
    · rw [← h1] at feK -- if K is of form {n,n+1}
      have hn : n = 1
      · have in1 : 1 ∈ ({n,n+1}:Finset ℤ)
        · exact feK (by simp)
        have in2 : 2 ∈ ({n,n+1}:Finset ℤ)
        · exact feK (by simp)
        simp at in1 in2
        rcases in1 with (n1|n0)
        · symm; exact n1
        · rcases in2 with (n2|n12)
          · exfalso; linarith
          · exfalso; linarith
      rw [hn] at h1
      symm
      exact h1
    · rw [← h2] at feK -- if K is of form {n}
      exfalso
      have : Finset.card {1,2} ≤ Finset.card {n}
      · exact Finset.card_le_of_subset feK
      simp at this

example : ∀ K ∈ Lℤ, (free_face realline K) → false := by -- example that realline has no free faces
  /-
    idea of proof:
    assume it have a free face, say f, then show that it is properly contains
    in 2 distinct faces ({n-1,n}, {n,n+1}), which is not unique  
  -/
  intro K hdK frK   -- assume there is a free face
  unfold Lℤ at hdK
  unfold free_face at frK
  simp at *
  rcases frK with ⟨_,⟨K',⟨hK',fK'K⟩⟩,h⟩
  rcases hdK with (hK1|hK2)
  · -- assume free face is of form {n,n+1}
    -- which we will get contradiction, since it is not a proper face of anyone
    rcases hK1 with ⟨n, K1⟩ 
    unfold realline at hK'
    simp at hK'
    unfold Lℤ at hK'
    have dimlt: dimension K < dimension K' 
    · rw [← proper_face] at fK'K
      exact @proper_face_dim_lt ℤ K' K (by simp [← K1, Coe.coe]) fK'K
    rcases hK' with (hK1'|hK2')
    · rcases hK1' with ⟨m,K1'⟩ 
      rw [← K1, ← K1'] at dimlt
      unfold dimension at dimlt
      simp at dimlt
    · rcases hK2' with ⟨m,K2'⟩ 
      rw [← K1, ← K2'] at dimlt
      unfold dimension at dimlt
      simp at dimlt
  · -- assume free face is of form {n}
    -- then it is contained in {n,n+1} and {(n-1),(n-1)+1}, which are different
    rcases hK2 with ⟨n, K2⟩ 

    have hM : {n,n+1} ∈ realline.X
    · unfold realline
      unfold Lℤ
      simp

    have hM' : {(n-1),(n-1)+1}∈ realline.X
    · unfold realline
      unfold Lℤ
      simp
      left
      use n-1
      simp
    specialize h {n,n+1} hM {(n-1),(n-1)+1} hM'
    rw [← K2] at h
    simp at h

    have fMK : ({n}:Finset ℤ) ⊂ {n, n + 1}
    · constructor
      · simp
      · simp
        intro h
        have eq_card: Finset.card {n,n+1} = Finset.card ({n}:Finset ℤ)
        · rw [← h]
        simp at eq_card

    have fM'K : ({n}:Finset ℤ) ⊂ {n-1, n}
    · constructor
      · simp
      · simp
    specialize h fMK fM'K

    -- showing {n,n+1} and {(n-1),(n-1)+1}, which are different and get a contradiction
    have subs : ({n,n+1}:Finset ℤ) ⊆ {n-1,n}
    · rw [Finset.Subset.antisymm_iff] at h
      exact h.1
    
    have nin : (n+1) ∉ ({n-1,n}: Finset ℤ)
    · simp
      linarith
    apply nin

    have : (n+1) ∈ ({n,n+1}:Finset ℤ)
    · simp

    exact subs this
-- end of example_4



-- lemma(free face is a proper face of a unique maximal elem) if a free face is a proper face of simplex K, K is a maximal elem
lemma unique_simplex_is_maximal {V : Type _} (X : AbstractSimplicialCplx V) (f : Simplex V)
  : (free_face X f) → (∀ K ∈ X.X, proper_face K f → max_elem X K) := by
  intro fXf K hK ffK
  simp
  constructor
  · exact hK          -- K is contained in complex
  · intro K' hK' fKK' -- K is maximal
    unfold proper_face at ffK
    unfold free_face at fXf
    rcases fXf with ⟨_ , _ , heq⟩
    have ffK' : proper_face K' f
    · unfold proper_face 
      exact trans_lt_le_imp_lt ffK fKK'
    exact heq K' hK' K hK ⟨ffK', ffK⟩ 

-- lemma(an equivalent def of free face using maximal elem)
lemma free_face_max_elem  {V : Type _} (X : AbstractSimplicialCplx V) (K : Simplex V) {non_empty : K ≠ (∅:Finset V) } :
  free_face X K ↔ ∃ M ∈ X.X, (max_elem X M)∧(proper_face M K)∧(∀ M'∈ X.X,(proper_face M' K)→(M=M') ) := by
  constructor
  · -- direction ->
    intro ffXK
    unfold free_face at ffXK
    simp
    rcases ffXK with ⟨_,⟨M,hM,fKM⟩,max⟩
    use M
    constructor
    · exact hM   -- M is in the cplx
    · constructor
      · constructor -- M is maximal
        · exact hM
        · intro M' hM' fMM'

          have fKM' : proper_face M' K
          · simp at *
            exact trans_lt_le_imp_lt fKM fMM'
          symm
          exact max M hM M' hM' ⟨fKM,fKM'⟩
      · constructor -- proper face and uniqueness
        · exact fKM
        · intro M' hM' fKM'
          exact max M hM M' hM' ⟨fKM,fKM'⟩
  · -- direction <-
    rintro ⟨M, hM, maxM⟩
    simp at maxM
    rcases maxM with ⟨_,⟨fKM,hM'⟩⟩
    unfold free_face
    constructor
    · exact X.FaceInclusion M hM K ⟨non_empty, fKM.1⟩ -- M is in the cplx
    . constructor
      · use M                               -- proper face
        exact ⟨hM,fKM⟩
      · rintro M1 hM1 M1' hM1' ⟨fKM1, fKM1'⟩ -- uniqueness
        
        have eqMM1 : M=M1
        · exact hM' M1 hM1 fKM1
        
        have eqMM1' : M=M1'
        · exact hM' M1' hM1' fKM1'

        rw [← eqMM1,← eqMM1']

-- lemma(maximal elem itself, viewed as cplx is a subcplx)
lemma max_elem_is_subsimplicial_cplx {V : Type _} (X : AbstractSimplicialCplx V) (K : Simplex V) (h : max_elem X K) : 
  (simplex_as_cplx K).X ⊆ X.X := by
  simp at *
  rcases h with ⟨hK,_⟩
  intro f hf
  unfold simplex_as_cplx at hf
  simp at hf
  exact X.FaceInclusion K hK f (by simp [hf]) 

-- lemma(given free face exists, the codim between it and maximal elem is 1)
lemma free_face_codim_one {V : Type _} [DecidableEq V] (X : AbstractSimplicialCplx V) (K : Finset V) (h : free_face X K) {non_empty : K≠(∅:Finset V)}
  : ∀ K'∈ X.X, (proper_face K' K) → dimension K'=dimension K + 1 := by
  /-
    idea of the proof
    if 2 or more dimension less, the difference of sets is of 2 or more card,
    then, pick a, b together with "free_face" to form 2 different max faces
    remark DecidableEq is for diff of Finsets
  -/
  intro K' hK' fK'K
  unfold free_face at h
  rcases h with ⟨_, _, h⟩
  unfold proper_face at fK'K
  -- dim K' ∈ [dim K +1,∞), since K' is a proper face 
  have hd1 : dimension K < dimension K'
  · exact @proper_face_dim_lt _ K' K non_empty fK'K

  -- dim K' ∈ [0, dim K +1], proved by contradiction
  have hd2 : dimension K' ≤  dimension K + 1
  · by_contra contra -- if it is strictly greater, dim K' > dim K+1, we get contradiction
    simp at contra

    -- just write it differently
    have gt1 : 1 < dimension K'-dimension K
    · exact Iff.mpr lt_tsub_iff_left contra

    -- unfold definition dimension
    have card_gt_1 : 1 < Finset.card (K' \ K)
    · have K_non_empty  : Finset.card K ≠ 0
      · simp
        exact non_empty
      
      have K'_non_empty : Finset.card K' ≠ 0
      · simp
        exact superset_nonempty _ _ non_empty fK'K.1
      
      unfold dimension at gt1
      rw [diff_pred_eq_diff _ _ K'_non_empty K_non_empty] at gt1
      exact (trans gt1 (Finset.le_card_sdiff K K'))
    
    -- constructing counter example that K is a face of a unique simplex

    -- since card > 1, ∃ a b ∈ K'\K, a≠b
    rw [Finset.one_lt_card_iff] at card_gt_1
    rcases card_gt_1 with ⟨a,b,ha,hb,ab_neq⟩
    simp at ha hb

    -- 1st simplex for counter example K∪{a}
    have hKa : (K∪{a} : Finset V) ∈ X.X
    · have fKaK' : (K∪{a} : Finset V) ⊆ K'
      · rintro x hx
        simp at hx
        rcases hx with (xK|xa)
        · exact fK'K.1 xK
        · rw [xa]
          exact ha.1
      have Ka_non_empty : (K∪{a} : Finset V) ≠ ∅ 
      · intro emp
        rw [Finset.eq_empty_iff_forall_not_mem] at emp
        simp at emp
        exact emp a (by right; rfl)
      exact X.FaceInclusion K' hK' (K∪{a} : Finset V) ⟨Ka_non_empty, fKaK'⟩
    
    have fKaK : (K:Finset V) ⊂ ((K:Finset V)∪({a}:Finset V))
    · constructor
      · intro x xK
        simp
        left; exact xK
      · rw [Finset.not_subset]
        use a
        simp
        exact ha.2
        
    -- 2st simplex for counter example K∪{b}
    have hKb : (K∪{b} : Finset V) ∈ X.X
    · have fKbK' : (K∪{b} : Finset V) ⊆ K'
      · rintro x hx
        simp at hx
        rcases hx with (xK|xb)
        · exact fK'K.1 xK
        · rw [xb]
          exact hb.1
      have Kb_non_empty : (K∪{b} : Finset V) ≠ ∅ 
      · intro emp
        rw [Finset.eq_empty_iff_forall_not_mem] at emp
        simp at emp
        exact emp b (by right; rfl)
      exact X.FaceInclusion K' hK' (K∪{b} : Finset V) ⟨Kb_non_empty, fKbK'⟩

    have fKbK : (K:Finset V) ⊂ ((K:Finset V)∪({b}:Finset V))
    · constructor
      · intro x xK
        simp
        left; exact xK
      · rw [Finset.not_subset]
        use b
        simp
        exact hb.2

    -- proving that they are different simplex thus not unique
    have KaKb_neq : (K∪{a} : Finset V)≠(K∪{b} : Finset V)
    · simp
      rw [Finset.ext_iff]
      simp
      use a
      simp
      intro hor
      rcases hor with (haK|ab_eq)
      · exact ha.2 haK
      · exact ab_neq ab_eq

    -- using the counter example to construct false
    specialize h (K∪{a} : Finset V) hKa (K∪{b} : Finset V) hKb
    simp at h
    specialize h fKaK fKbK
    exact KaKb_neq h
  
  -- finally, using the 2 inequalities, dim K' ∈ [dim K +1,∞) and dim K' ∈ [0, dim K +1] to conclude codim
  linarith


/- TODO

  - Euler characteristic
  - simplicial homology

-/ 