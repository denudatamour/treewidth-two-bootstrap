import Bootstrap.CompleteRoute
import Mathlib.Data.Fintype.EquivFin

/-! The two full neighbourhoods and their finite thresholds in Theorem II.1. -/
namespace Bootstrap.DegreeTwo

variable {W V : Type*}

/-- The witness for a genuinely born edge is a full copy in the completed round. -/
theorem birth_full_copy (H : SimpleGraph W) (G : SimpleGraph V) {x y : V}
    (new : (step H G).Adj x y) (old : ¬ G.Adj x y) :
    ∃ (f : W ↪ V) (u v : W), H.Adj u v ∧ f u = x ∧ f v = y ∧ FullCopy H (step H G) f := by
  obtain ⟨u,v,f,e,hx,hy,rest⟩ := new.resolve_left old
  refine ⟨f,u,v,e,hx,hy,?_⟩
  intro a b hab
  by_cases gap : (a=u ∧ b=v) ∨ (a=v ∧ b=u)
  · rcases gap with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simpa only [hx,hy] using new
    · simpa only [hx,hy] using (step H G).symm new
  · exact Or.inl (rest a b hab gap)

structure Pools (G : SimpleGraph V) (f : W ↪ V) (u v : W) (m : ℕ) where
  left : Finset V
  right : Finset V
  card_left : left.card = m
  card_right : right.card = m
  out_left : ∀ p ∈ left, Outside f p
  out_right : ∀ q ∈ right, Outside f q
  apart : ∀ p ∈ left, ∀ q ∈ right, p ≠ q
  mark_left : Marked G f (left : Set V) u
  mark_right : Marked G f (right : Set V) v

open scoped Classical in
theorem choose_pools [Fintype W] [Fintype V] (G : SimpleGraph V) (f : W ↪ V)
    (u v : W) (m : ℕ) (du : Fintype.card W - 1 + 2*m ≤ G.degree (f u))
    (dv : Fintype.card W - 1 + 2*m ≤ G.degree (f v)) :
    Nonempty (Pools G f u v m) := by
  classical
  let used := Finset.univ.map f
  let available (a : W) := G.neighborFinset (f a) \ used
  have used_card : used.card = Fintype.card W := by simp [used]
  have inside (a : W) : f a ∈ used := Finset.mem_map.mpr ⟨a,Finset.mem_univ a,rfl⟩
  have room (a : W) (h : Fintype.card W - 1 + 2*m ≤ G.degree (f a)) : 2*m ≤ (available a).card := by
    have sub : G.neighborFinset (f a) ∩ used ⊆ used.erase (f a) := by
      intro z hz
      obtain ⟨h₁,h₂⟩ := Finset.mem_inter.mp hz
      exact Finset.mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp h₁).ne.symm,h₂⟩
    have lim := Finset.card_le_card sub
    rw [Finset.card_erase_of_mem (inside a),used_card] at lim
    have split := Finset.card_sdiff_add_card_inter (G.neighborFinset (f a)) used
    change (available a).card + _ = _ at split
    change Fintype.card W - 1 + 2*m ≤ (G.neighborFinset (f a)).card at h
    omega
  obtain ⟨p,hp,pc⟩ := Finset.exists_subset_card_eq (s := available u) (n := m) (by have := room u du; omega)
  have rem : (available v).card ≤ (available v \ p).card + p.card := Finset.card_le_card_sdiff_add_card
  obtain ⟨q,hq,qc⟩ := Finset.exists_subset_card_eq (s := available v \ p) (n := m) (by have := room v dv; omega)
  have out (a : W) {z} (hz : z ∈ available a) : Outside f z := by
    intro i he
    exact (Finset.mem_sdiff.mp hz).2 (he ▸ inside i)
  have linked (a : W) {z} (hz : z ∈ available a) : G.Adj z (f a) :=
    G.symm ((G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hz).1)
  refine ⟨⟨p,q,pc,qc,fun _ h => out u (hp h),
    fun _ h => out v (Finset.mem_sdiff.mp (hq h)).1,?_,
    fun _ h => linked u (hp h), fun _ h => linked v (Finset.mem_sdiff.mp (hq h)).1⟩⟩
  rintro a ha b hb rfl
  exact (Finset.mem_sdiff.mp (hq hb)).2 ha

open scoped Classical in
/-- The shores of cardinality h+1 include both ends of the born edge. -/
theorem high_birth_seed [Fintype W] [Fintype V] (H : SimpleGraph W) [DecidableRel H.Adj]
    (G : SimpleGraph V) (conn : H.Connected) (root : W)
    (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    (long : ∃ i j, H.Adj i j ∧ H.degree i = 2 ∧ H.degree j = 2)
    (t : ℕ) {x y : V} (birth : (run H G (t+1)).Adj x y) (old : ¬ (run H G t).Adj x y)
    (dx : 3*Fintype.card W-1 ≤ (run H G (t+1)).degree x)
    (dy : 3*Fintype.card W-1 ≤ (run H G (t+1)).degree y) :
    ∃ (f : W ↪ V) (u v : W) (P : Pools (run H G (t+1)) f u v (Fintype.card W)),
      H.Adj u v ∧ f u = x ∧ f v = y ∧ FullCopy H (run H G (t+1)) f ∧
      Disjoint (insert y P.left) (insert x P.right) ∧
      (insert y P.left).card = Fintype.card W+1 ∧ (insert x P.right).card = Fintype.card W+1 ∧
      Joined (run H G (t+1+2*Fintype.card W)) (↑(insert y P.left) : Set V) (↑(insert x P.right) : Set V) ∧
      ∃ l, CompleteLongRoute H (standardBases H root) l ∧
        (Marked (run H G (t+1+2*Fintype.card W)) f P.left l ∨
         Marked (run H G (t+1+2*Fintype.card W)) f P.right l) := by
  classical
  obtain ⟨f,u,v,e,rfl,rfl,full⟩ := birth_full_copy H (run H G t) birth old
  have pos : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨root⟩
  obtain ⟨P⟩ := choose_pools (run H G (t+1)) f u v (Fintype.card W) (by omega) (by omega)
  have leftNon : P.left.Nonempty := Finset.card_pos.mp (by rw [P.card_left]; exact pos)
  have rightNon : P.right.Nonempty := Finset.card_pos.mp (by rw [P.card_right]; exact pos)
  obtain ⟨joined,head⟩ := lemma_II_2 H G f (t+1) full conn root cover long e
    (P.left : Set V) (P.right : Set V) leftNon rightNon P.out_left P.out_right P.apart P.mark_left P.mark_right
  have freeLeft (a : W) : f a ∉ P.left := fun h => P.out_left _ h a rfl
  have freeRight (a : W) : f a ∉ P.right := fun h => P.out_right _ h a rfl
  have extra : Disjoint (insert (f v) P.left) (insert (f u) P.right) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    rcases Finset.mem_insert.mp hz with rfl|hp
    · rcases Finset.mem_insert.mp hz' with hf'|hq
      · exact e.ne (f.injective hf'.symm)
      · exact freeRight v hq
    · rcases Finset.mem_insert.mp hz' with rfl|hq
      · exact freeLeft u hp
      · exact P.apart _ hp _ hq rfl
  refine ⟨f,u,v,P,e,rfl,rfl,full,extra,?_,?_,?_,head⟩
  · rw [Finset.card_insert_of_not_mem (freeLeft v),P.card_left]
  · rw [Finset.card_insert_of_not_mem (freeRight u),P.card_right]
  · intro p hp q hq
    have later := time_mono H G (by omega : t+1 ≤ t+1+2*Fintype.card W)
    rcases Finset.mem_insert.mp hp with rfl|hp
    · rcases Finset.mem_insert.mp hq with rfl|hq
      · exact later ((run H G (t+1)).symm birth)
      · exact later ((run H G (t+1)).symm (P.mark_right q hq))
    · rcases Finset.mem_insert.mp hq with rfl|hq
      · exact later (P.mark_left p hp)
      · exact joined p hp q hq

end Bootstrap.DegreeTwo

#print axioms Bootstrap.DegreeTwo.high_birth_seed
