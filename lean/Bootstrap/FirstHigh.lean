import Bootstrap.CliqueClock

namespace Bootstrap.DegreeTwo

open scoped Classical
variable {W V : Type*}

private noncomputable def chargeSet [Fintype V] (G : SimpleGraph V) (J : ℕ) : Finset (V × Fin J) :=
  Finset.univ.filter fun p => p.2.val < G.degree p.1

private theorem charge_bounded [Fintype V] (G : SimpleGraph V) (J : ℕ) :
    (chargeSet G J).card ≤ Fintype.card V * J := by
  simpa [Fintype.card_prod] using Finset.card_le_univ (chargeSet G J)

private theorem charge_strict [Fintype V] {G D : SimpleGraph V} {x y : V} (inc : G ≤ D)
    (old : ¬G.Adj x y) (born : D.Adj x y) (J : ℕ) (small : D.degree x < J) :
    (chargeSet G J).card < (chargeSet D J).card := by
  have more : G.degree x < D.degree x := by
    apply Finset.card_lt_card
    refine ⟨fun z hz => (D.mem_neighborFinset _ _).mpr (inc ((G.mem_neighborFinset _ _).mp hz)),?_⟩
    exact fun back => old ((G.mem_neighborFinset x y).mp (back ((D.mem_neighborFinset x y).mpr born)))
  have sub : chargeSet G J ⊆ chargeSet D J := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp hp).2).trans_le (SimpleGraph.degree_le_of_le inc)⟩
  let p : V × Fin J := (x,⟨G.degree x,by omega⟩)
  have newmem : p ∈ chargeSet D J := Finset.mem_filter.mpr ⟨Finset.mem_univ _,more⟩
  have oldmem : p ∉ chargeSet G J := fun h => (Nat.lt_irrefl _) (Finset.mem_filter.mp h).2
  exact Finset.card_lt_card ⟨sub,fun back => oldmem (back newmem)⟩

/-- Before |V| J charges, either the process stabilizes or it has a genuine
birth with both endpoints high in its completed round. -/
theorem first_high_or_fixed [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (J : ℕ) :
    ∃ t ≤ Fintype.card V * J, (run H G t = run H G (t+1)) ∨
      ∃ x y, ¬(run H G t).Adj x y ∧ (run H G (t+1)).Adj x y ∧
        J ≤ (run H G (t+1)).degree x ∧ J ≤ (run H G (t+1)).degree y := by
  classical
  by_contra no
  let cap := Fintype.card V * J
  let charge (t : ℕ) := (chargeSet (run H G t) J).card
  have inc (t : ℕ) (ht : t ≤ cap) : charge t < charge (t+1) := by
    have active : ¬ run H G t = run H G (t+1) := fun fix => no ⟨t,ht,Or.inl fix⟩
    have existsBorn : ∃ x y, ¬(run H G t).Adj x y ∧ (run H G (t+1)).Adj x y := by
      by_contra! none
      apply active
      exact le_antisymm (run_le_succ H G t) (fun x y born => by_contra (fun old => none x y old born))
    obtain ⟨x,y,old,born⟩ := existsBorn
    by_cases hx : J ≤ (run H G (t+1)).degree x
    · have hy : (run H G (t+1)).degree y < J := by
        by_contra! high
        exact no ⟨t,ht,Or.inr ⟨x,y,old,born,hx,high⟩⟩
      exact charge_strict (run_le_succ H G t) (fun e => old ((run H G t).symm e)) ((run H G (t+1)).symm born) J hy
    · exact charge_strict (run_le_succ H G t) old born J (by omega)
  have bounded (k : ℕ) (hk : k ≤ cap+1) : k ≤ charge k := by
    induction k with
    | zero => omega
    | succ k ih =>
      have := inc k (by omega)
      have := ih (by omega)
      omega
  have endCharge := bounded (cap+1) le_rfl
  have maxCharge : charge (cap+1) ≤ cap := charge_bounded _ _
  omega

end Bootstrap.DegreeTwo

#print axioms Bootstrap.DegreeTwo.first_high_or_fixed
