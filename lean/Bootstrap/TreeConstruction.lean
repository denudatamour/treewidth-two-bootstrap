import Bootstrap.TreeBags
import Mathlib.Data.Finset.Union

namespace Bootstrap.TreeBags

variable {V U I : Type*} [DecidableEq V]

theorem map_tree [DecidableEq U] {k : ℕ} {F : Finset (Finset V)} (T : Tree k F) (e : V ↪ U) :
    Tree k (F.image (fun b => b.map e)) := by
  induction T with
  | root b hb =>
    simpa using Tree.root (k := k) (b.map e) (by simpa using hb)
  | @attach F old p hp b hw glue ih =>
    rw [Finset.image_insert]
    apply Tree.attach ih (p := p.map e) (Finset.mem_image_of_mem _ hp) _ (by simpa using hw)
    intro v hv prev
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨s,hs,hv⟩ := prev
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hs
    have hx' := Finset.mem_map.mp hv
    obtain ⟨y,hy,eq⟩ := hx'
    have he := e.injective eq
    subst y
    exact Finset.mem_map.mpr ⟨x,glue x hx ⟨a,ha,hy⟩,rfl⟩

/-- The tip of each new leaf is fresh. The rest of the bag lies in its chosen parent. -/
theorem fresh_leaves [Fintype I] {k : ℕ} {F : Finset (Finset V)} (T : Tree k F)
    (tip : I ↪ V) (oldPart parent : I → Finset V)
    (fresh : ∀ i, ¬ Occurs F (tip i)) (hp : ∀ i, parent i ∈ F)
    (contains : ∀ i, oldPart i ⊆ parent i) (width : ∀ i, (insert (tip i) (oldPart i)).card ≤ k+1) :
    ∃ F', Tree k F' ∧ F ⊆ F' ∧ ∀ i, insert (tip i) (oldPart i) ∈ F' ∧
      ∀ v ∈ insert (tip i) (oldPart i), v = tip i ∨ Occurs F v := by
  classical
  let leaf := fun i => insert (tip i) (oldPart i)
  have parts (i : I) (v : V) (h : v ∈ oldPart i) : Occurs F v := ⟨_,hp i,contains i h⟩
  have build := attach_family T Finset.univ leaf parent hp width (by
    intro i v hv old
    rcases Finset.mem_insert.mp hv with rfl | h
    · exact (fresh i old).elim
    · exact contains i h) (by
    intro i j neq v vi vj
    rcases Finset.mem_insert.mp vi with rfl | h
    · rcases Finset.mem_insert.mp vj with he | h
      · exact (neq (tip.injective he)).elim
      · exact parts j _ h
    · exact parts i _ h)
  refine ⟨_,build,Finset.subset_union_left,?_⟩
  intro i
  refine ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem leaf (Finset.mem_univ i)),?_⟩
  intro v hv
  exact (Finset.mem_insert.mp hv).imp_right (parts i v)

/-- Enlarge a width-two tree by one distinct new vertex for every old pair of anchors. -/
theorem starLeaves [Fintype I] {F : Finset (Finset V)} (T : Tree 2 F)
    (tip : I ↪ V) (a b : I → V) (fresh : ∀ i, ¬ Occurs F (tip i))
    (pairs : ∀ i, Together F (a i) (b i)) :
    ∃ F', Tree 2 F' ∧ F ⊆ F' ∧
      (∀ i, ({tip i,a i,b i} : Finset V) ∈ F') ∧
      ∀ v, Occurs F' v → Occurs F v ∨ ∃ i, tip i = v := by
  classical
  choose parent hp ha hb using pairs
  let leaf := fun i => ({tip i,a i,b i} : Finset V)
  have oldPart (i : I) (v : V) (h : v = a i ∨ v = b i) : Occurs F v := by
    rcases h with rfl | rfl
    · exact ⟨_,hp i,ha i⟩
    · exact ⟨_,hp i,hb i⟩
  have build := attach_family T Finset.univ leaf parent hp (by
    intro i
    exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (Finset.card_le_two))) (by
    intro i v hv seen
    simp only [leaf,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact (fresh i seen).elim
    · exact ha i
    · exact hb i) (by
    intro i j neq v hi hj
    simp only [leaf,Finset.mem_insert,Finset.mem_singleton] at hi hj
    rcases hi with rfl | h
    · exact hj.elim (fun e => (neq (tip.injective e)).elim) (oldPart j _)
    · exact oldPart i _ h)
  refine ⟨_,build,Finset.subset_union_left,fun i => Finset.mem_union_right _
    (Finset.mem_image_of_mem leaf (Finset.mem_univ i)),?_⟩
  rintro v ⟨bag,hbag,hv⟩
  rcases Finset.mem_union.mp hbag with old | new
  · exact Or.inl ⟨bag,old,hv⟩
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp new
    simp only [leaf,Finset.mem_insert,Finset.mem_singleton] at hv
    exact hv.elim (fun e => Or.inr ⟨i,e.symm⟩) (fun h => Or.inl (oldPart i v h))

/-- A concrete parent/leaf list. The size check and running-intersection check are decidable. -/
def rowsResult (F : Finset (Finset V)) : List (Finset V × Finset V) → Finset (Finset V)
  | [] => F
  | (_,b) :: rows => rowsResult (insert b F) rows

def rowsOK (k : ℕ) (F : Finset (Finset V)) : List (Finset V × Finset V) → Bool
  | [] => true
  | (p,b) :: rows =>
    decide (p ∈ F ∧ b.card ≤ k+1 ∧ b ∩ F.biUnion id ⊆ p) && rowsOK k (insert b F) rows

theorem rows_sound {k : ℕ} {F : Finset (Finset V)} (T : Tree k F)
    (rows : List (Finset V × Finset V)) (check : rowsOK k F rows = true) :
    Tree k (rowsResult F rows) := by
  induction rows generalizing F with
  | nil => exact T
  | cons row rows ih =>
    rcases row with ⟨p,b⟩
    have h := Bool.and_eq_true_iff.mp check
    have good := of_decide_eq_true h.1
    apply ih (Tree.attach T good.1 b good.2.1 ?_) h.2
    intro x hx seen
    obtain ⟨s,hs,xs⟩ := seen
    exact good.2.2 (Finset.mem_inter.mpr ⟨hx,Finset.mem_biUnion.mpr ⟨s,hs,xs⟩⟩)

end Bootstrap.TreeBags
