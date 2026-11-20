import Bootstrap.SubdivisionWindows

namespace Bootstrap.Subdivision

open DegreeTwo
variable {C E V : Type*}

private def band (s w : ℕ) : Finset ℕ := (Finset.range w).image (fun k => s+k)

private theorem band_card (s w : ℕ) : (band s w).card ≤ w := by
  simpa only [Finset.card_range] using (Finset.card_image_le
    (s := Finset.range w) (f := fun k => s+k))

private theorem in_band {s w t : ℕ} (st : s ≤ t) (tw : t < s+w) : t ∈ band s w :=
  Finset.mem_image.mpr ⟨t-s,Finset.mem_range.mpr (by omega),by omega⟩

/-- Work up to any horizon with a birth in every preceding round. The set
known contains the lifetime charges of previously created blocks. Each merger
adds the lifetime charge of exactly one new block to that set. -/
private theorem cover_horizon [Fintype C] [Fintype E] [Fintype V] (D : Data C E) (e₀ : E)
    (G : SimpleGraph V) (T r : ℕ) (radius : ∀ s, RadiusAt D s r)
    (active : ∀ t, t < T → ∃ x y, Born D.rule G t x y) (n : ℕ) :
    ∀ (s : ℕ) (P : Finset (Finset V)), Partition D (run D.rule G s) P → P.card ≤ n →
      ∀ known : Finset ℕ,
        (∀ A ∈ P, ∀ t, s ≤ t → t < T → InternalBirth D.rule G A t → t ∈ known) →
        ∃ extra : Finset ℕ, extra.card ≤ n*(r+4+internalBudget C)+2 ∧
          ∀ t, s ≤ t → t < T → LowWindow D.rule G (threshold C E) t ∨ t ∈ known ∨ t ∈ extra := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s P part hp known accounted
    by_cases fires : ∃ j, s ≤ j ∧ j < T ∧ Trigger D (run D.rule G (j+1)) (blockOf P) (threshold C E)
    · let j := Nat.find fires
      have hit : s ≤ j ∧ j < T ∧ Trigger D (run D.rule G (j+1)) (blockOf P) (threshold C E) := Nat.find_spec fires
      have sj := hit.1
      have jT := hit.2.1
      have quiet (i : ℕ) (si : s ≤ i) (ij : i < j) :
          ¬ Trigger D (run D.rule G (i+1)) (blockOf P) (threshold C E) :=
        fun tr => Nat.find_min fires ij ⟨si,by omega,tr⟩
      let next := j+1+r+1
      obtain ⟨Q,U,partQ,less,uQ,old⟩ := perform_merger D e₀ G (j+1) r radius P
        (part.mono (time_mono D.rule G (by omega : s ≤ j+1))) hit.2.2
      obtain ⟨inside,hinside,insidePays⟩ := internal_lifetime D e₀ G next T (partQ.certified U uQ)
      have recordQ (A : Finset V) (hA : A ∈ Q) (t : ℕ) (fromNext : next ≤ t) (ht : t<T)
          (born : InternalBirth D.rule G A t) : t ∈ known ∪ inside := by
        rcases old A hA with prev | eq
        · have st : s ≤ t := by dsimp [next] at fromNext; omega
          exact Finset.mem_union_left _ (accounted A prev t st ht born)
        · subst A
          exact Finset.mem_union_right _ (insidePays t fromNext ht born)
      obtain ⟨tail,htail,covTail⟩ := ih Q.card (by omega) next Q partQ le_rfl (known ∪ inside) recordQ
      let begin := band s 2
      let skip := band j (r+2)
      let extra := begin ∪ skip ∪ inside ∪ tail
      refine ⟨extra,?_,?_⟩
      · have cb : begin.card ≤ 2 := band_card _ _
        have cs : skip.card ≤ r+2 := band_card _ _
        have c₁ := Finset.card_union_le begin skip
        have c₂ := Finset.card_union_le (begin ∪ skip) inside
        have c₃ := Finset.card_union_le (begin ∪ skip ∪ inside) tail
        let fee := r+4+internalBudget C
        have prepay : Q.card*fee + fee ≤ n*fee := by
          simpa only [Nat.add_mul,Nat.one_mul] using
            Nat.mul_le_mul_right fee (by omega : Q.card+1 ≤ n)
        change tail.card ≤ Q.card*fee+2 at htail
        change (begin ∪ skip ∪ inside ∪ tail).card ≤ n*fee+2
        have val : fee = r+4+internalBudget C := rfl
        omega
      · intro t st ht
        by_cases first : t < j
        · rcases waiting_round D e₀ G P s j t part st first quiet (active t ht) with early | ⟨A,ha,bi⟩ | low
          · exact Or.inr (Or.inr (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (show t ∈ begin from in_band st early)))))
          · exact Or.inr (Or.inl (accounted A ha t st ht bi))
          · exact Or.inl low
        · by_cases during : t < next
          · have sk : t ∈ skip := by apply in_band <;> dsimp [next] at during <;> omega
            exact Or.inr (Or.inr (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ sk))))
          · rcases covTail t (by omega) ht with low | recorded | done_
            · exact Or.inl low
            · rcases Finset.mem_union.mp recorded with past | new_
              · exact Or.inr (Or.inl past)
              · exact Or.inr (Or.inr (Finset.mem_union_left _ (Finset.mem_union_right _ new_)))
            · exact Or.inr (Or.inr (Finset.mem_union_right _ done_))
    · have quiet (i : ℕ) (si : s ≤ i) (it : i < T) :
          ¬ Trigger D (run D.rule G (i+1)) (blockOf P) (threshold C E) :=
        fun tr => fires ⟨i,si,it,tr⟩
      refine ⟨band s 2,by have := band_card s 2; omega,?_⟩
      intro t st ht
      rcases waiting_round D e₀ G P s T t part st ht quiet (active t ht) with early | ⟨A,ha,bi⟩ | low
      · exact Or.inr (Or.inr (in_band st early))
      · exact Or.inr (Or.inl (accounted A ha t st ht bi))
      · exact Or.inl low

/-- Explicit linear bound for the actual first stable round. The final
additive two accounts for the first two rounds of the last waiting interval. -/
theorem stabilization_bound [Fintype C] [Fintype E] [Fintype V] (D : Data C E) (e₀ : E)
    (G : SimpleGraph V) (r : ℕ) (radius : ∀ s, RadiusAt D s r) :
    stabilizationTime D.rule G ≤ 3*(Fintype.card V*(threshold C E-1)) +
      Fintype.card V*(r+4+internalBudget C)+2 := by
  classical
  let T := stabilizationTime D.rule G
  have active (t : ℕ) (ht : t<T) := before_stop D.rule G ht
  have initial (A : Finset V) (ha : A ∈ (singletons (V := V))) (t : ℕ) (_ : 0 ≤ t) (_ : t<T)
      (inside : InternalBirth D.rule G A t) : t ∈ (∅ : Finset ℕ) := by
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨a,ha,b,hb,birth⟩ := inside
    exact False.elim (birth.1.ne ((Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm))
  obtain ⟨extra,he,cov⟩ := cover_horizon D e₀ G T r radius active (Fintype.card V) 0
    singletons (singleton_partition D G) (le_of_eq singletons_card) ∅ initial
  obtain ⟨low,hl,lowPays⟩ := count_low_windows D.rule G (threshold C E) T
  have sub : Finset.range T ⊆ low ∪ extra := by
    intro t ht
    have tt := Finset.mem_range.mp ht
    rcases cov t (Nat.zero_le _) tt with wind | empty | plus
    · exact Finset.mem_union_left _ (lowPays t tt wind)
    · exact False.elim (Finset.not_mem_empty _ empty)
    · exact Finset.mem_union_right _ plus
  have size := Finset.card_le_card sub
  rw [Finset.card_range] at size
  have total := Finset.card_union_le low extra
  change T ≤ _
  omega

/-- A fixed slope valid for every host order. -/
def slope (C E : Type*) [Fintype C] [Fintype E] : ℕ :=
  3*(threshold C E-1) + (Fintype.card C-1+4+internalBudget C) + 2

theorem maxTime_bound_of_edge [Fintype C] [Fintype E] (D : Data C E) (e₀ : E)
    (conn : D.baseGraph.Connected) (n : ℕ) : maxTime D.rule n ≤ slope C E * n := by
  classical
  cases n with
  | zero => simpa using maxTime_le_choose D.rule 0
  | succ n =>
    apply (maxTime_le_iff _ _ _).mpr
    intro G
    have bound := stabilization_bound D e₀ G (Fintype.card C-1) (radius_of_connected D conn)
    simp only [Fintype.card_fin] at bound
    have paid : 3*((n+1)*(threshold C E-1)) = (3*(threshold C E-1))*(n+1) := by ac_rfl
    rw [paid, Nat.mul_comm (n+1) (Fintype.card C-1+4+internalBudget C)] at bound
    unfold slope
    rw [Nat.add_mul,Nat.add_mul]
    omega

/-- Appendix A: the once-subdivision of every fixed finite connected loopless
multigraph has linear maximum running time. Parallel edges have distinct
midpoints, and the formula also applies when the edge type is empty. -/
theorem once_subdivision_linear [Fintype C] [Fintype E] (D : Data C E)
    (conn : D.baseGraph.Connected) : ∀ n, maxTime D.rule n ≤ slope C E * n := by
  classical
  by_cases used : Nonempty E
  · exact maxTime_bound_of_edge D (Classical.choice used) conn
  · have emptyRule : D.rule = ⊥ := by
      ext i j
      cases i with
      | inl c =>
        cases j with
        | inl d => rfl
        | inr e => exact False.elim (used ⟨e⟩)
      | inr e => exact False.elim (used ⟨e⟩)
    intro n
    apply (maxTime_le_iff _ _ _).mpr
    intro G
    have fixed : run D.rule G 0 = run D.rule G (0+1) := by
      change G = step D.rule G
      rw [emptyRule,step_empty_rule]
    exact le_trans (Nat.find_min' (stable_exists D.rule G) fixed) (Nat.zero_le _)

end Bootstrap.Subdivision

#print axioms Bootstrap.Subdivision.stabilization_bound
#print axioms Bootstrap.Subdivision.maxTime_bound_of_edge
#print axioms Bootstrap.Subdivision.once_subdivision_linear
