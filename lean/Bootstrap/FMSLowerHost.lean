import Bootstrap.FMSPropagation

namespace Bootstrap.FMS

open DegreeTwo
variable {W V : Type*}

/-- The expanding clique contains the whole seed and the first k tail cells. -/
def initialSegment (h ℓ k : ℕ) : Finset (Fin h ⊕ Fin ℓ) :=
  Finset.univ.filter (fun z => level z ≤ k)

@[simp] theorem mem_segment {h ℓ k : ℕ} {z : Fin h ⊕ Fin ℓ} :
    z ∈ initialSegment h ℓ k ↔ level z ≤ k := by simp [initialSegment]

private theorem room (h ℓ k : ℕ) : h ≤ (initialSegment h ℓ k).card := by
  let emb : Fin h ↪ ↥(initialSegment h ℓ k) :=
    ⟨fun i => ⟨.inl i,mem_segment.mpr (Nat.zero_le k)⟩,
      fun _ _ he => Sum.inl.inj (congrArg Subtype.val he)⟩
  simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_embedding emb

private theorem predecessor {h ℓ k : ℕ} (seed : Fin h) {z : Fin h ⊕ Fin ℓ}
    (hz : level z = k+1) :
    ∃ y : Fin h ⊕ Fin ℓ, level y = k ∧ (tailGraph h ℓ).Adj z y := by
  have contact {y : Fin h ⊕ Fin ℓ} (hy : level y = k) : (tailGraph h ℓ).Adj z y := by
    refine ⟨fun e => ?_,Or.inr (Or.inr (by omega))⟩
    have := congrArg level e
    omega
  cases k with
  | zero => exact ⟨.inl seed,rfl,contact rfl⟩
  | succ k =>
    cases z with
    | inl z => simp [level] at hz
    | inr z =>
      have l : k < ℓ := by
        change z.val+1 = k+1+1 at hz
        have := z.isLt
        omega
      exact ⟨.inr ⟨k,l⟩,rfl,contact rfl⟩

theorem segment_clique [Fintype W] (H : SimpleGraph W) {a l r : W}
    (N : TwoNeighbours H a l r) (ℓ : ℕ) (seed : Fin (Fintype.card W)) (k : ℕ) :
    CliqueOn (run H (tailGraph (Fintype.card W) ℓ) k) (initialSegment (Fintype.card W) ℓ k) := by
  induction k with
  | zero =>
    intro x hx y hy ne
    exact ⟨ne,Or.inl ⟨Nat.le_zero.mp (mem_segment.mp hx),Nat.le_zero.mp (mem_segment.mp hy)⟩⟩
  | succ k ih =>
    let S := initialSegment (Fintype.card W) ℓ k
    let J := tailGraph (Fintype.card W) ℓ
    have enter (x : Fin (Fintype.card W) ⊕ Fin ℓ) (fresh : level x = k+1) :
        ∀ y ∈ S, (run H J (k+1)).Adj x y := by
      obtain ⟨p,levelp,contact⟩ := predecessor seed fresh
      have outside : x ∉ S := by
        intro hx
        have bound := mem_segment.mp hx
        omega
      have inside : p ∈ S := mem_segment.mpr levelp.le
      intro y hy
      apply clique_absorbs_contact H (run H J k) N S (room _ _ _) ih outside inside hy
      exact (time_mono H J (Nat.zero_le k)) contact
    intro x hx y hy ne
    have hx' := mem_segment.mp hx
    have hy' := mem_segment.mp hy
    by_cases xs : level x ≤ k
    · by_cases ys : level y ≤ k
      · exact run_le_succ H J k (ih (mem_segment.mpr xs) (mem_segment.mpr ys) ne)
      · exact (run H J (k+1)).symm (enter y (by omega) x (mem_segment.mpr xs))
    · by_cases ys : level y ≤ k
      · exact enter x (by omega) y (mem_segment.mpr ys)
      · exact False.elim (ne (level_injective_above_zero (by omega) (by omega)))

private theorem at_stop [Fintype V] (H : SimpleGraph W) (J : SimpleGraph V) (s : ℕ) :
    run H J s ≤ run H J (stabilizationTime H J) := by
  let t := stabilizationTime H J
  have fixed := stabilizationTime_spec H J
  have after (k : ℕ) : run H J (t+k) = run H J t := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change step H (run H J (t+k)) = run H J t
      rw [ih]
      exact fixed.symm
  by_cases h : s ≤ t
  · exact time_mono H J h
  · have eq : t+(s-t)=s := by omega
    rw [← eq,after]

/-- Every sufficiently long tail gives an ordinary host of exactly h+ℓ
vertices with at least ℓ/h rounds, where h is the rule order. -/
theorem path_host_bound [Fintype W] {H : SimpleGraph W} [DecidableRel H.Adj]
    (conn : H.Connected) (min : HasTwoNeighbours H) (high : ∃ w, 2 < H.degree w)
    {a l r : W} (N : TwoNeighbours H a l r) (ℓ : ℕ) (long : 2 ≤ ℓ) :
    ℓ ≤ Fintype.card W * maxTime H (Fintype.card W + ℓ) := by
  classical
  let h := Fintype.card W
  let J := tailGraph h ℓ
  let t := stabilizationTime H J
  let seed : Fin h := ⟨0,Fintype.card_pos_iff.mpr ⟨a⟩⟩
  let x : Fin h ⊕ Fin ℓ := .inr ⟨ℓ-1,by omega⟩
  let y : Fin h ⊕ Fin ℓ := .inl seed
  have hx : level x = ℓ := by change ℓ-1+1=ℓ; omega
  have hy : level y = 0 := rfl
  have xy : x ≠ y := by exact Sum.inr_ne_inl
  have filled : (run H J ℓ).Adj x y :=
    segment_clique H N ℓ seed ℓ (mem_segment.mpr hx.le) (mem_segment.mpr (hy ▸ Nat.zero_le ℓ)) xy
  have edge : (run H J t).Adj x y := at_stop H J ℓ filled
  have limited : ℓ ≤ t*h := by
    by_contra small
    have gap : t * Fintype.card W < level x := hx.symm ▸ Nat.lt_of_not_ge small
    have near := tail_frontier conn min high h ℓ t x y edge gap
    rw [hx,hy] at near
    rcases near with a|a <;> omega
  have cap : t ≤ maxTime H (h+ℓ) := by simpa [t,J] using le_maxTime_card H J
  calc
    ℓ ≤ t*h := limited
    _ = h*t := Nat.mul_comm _ _
    _ ≤ h * maxTime H (h+ℓ) := Nat.mul_le_mul_left h cap

end Bootstrap.FMS

#print axioms Bootstrap.FMS.segment_clique
#print axioms Bootstrap.FMS.path_host_bound
