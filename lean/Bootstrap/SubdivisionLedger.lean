import Bootstrap.SubdivisionWindows

namespace Bootstrap.Subdivision

open DegreeTwo
variable {C E V W : Type*}

/-- Each recorded step is an actual first trigger in its waiting interval; the new partition
has fewer blocks, with at most one newly created block. The terminal interval has no trigger. -/
inductive MergeTrace [Fintype C] [Fintype E] [Fintype V] (D : Data C E)
    (G : SimpleGraph V) (T r : ℕ) : ℕ → Finset (Finset V) → ℕ → Prop where
  | stop {s P}
      (quiet : ∀ i, s ≤ i → i < T → ¬Trigger D (run D.rule G (i+1)) (blockOf P) (threshold C E)) :
      MergeTrace D G T r s P 0
  | merge {s P j Q U J} (start : s ≤ j) (before : j < T)
      (first : ∀ i, s ≤ i → i < j → ¬Trigger D (run D.rule G (i+1)) (blockOf P) (threshold C E))
      (hit : Trigger D (run D.rule G (j+1)) (blockOf P) (threshold C E))
      (newPart : Partition D (run D.rule G (j+1+r+1)) Q) (less : Q.card < P.card)
      (joined : U ∈ Q) (unchanged : ∀ A ∈ Q, A ∈ P ∨ A = U)
      (tail : MergeTrace D G T r (j+1+r+1) Q J) : MergeTrace D G T r s P (J+1)

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
        ∃ J : ℕ, (P.Nonempty → J < P.card) ∧ J ≤ n ∧ MergeTrace D G T r s P J ∧
          ∃ extra : Finset ℕ, extra.card ≤ J*(r+4+internalBudget C)+2 ∧
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
      obtain ⟨J,strictJ,_,trace,tail,htail,covTail⟩ := ih Q.card (by omega) next Q partQ le_rfl (known ∪ inside) recordQ
      let begin := band s 2
      let skip := band j (r+2)
      let extra := begin ∪ skip ∪ inside ∪ tail
      have smaller := strictJ ⟨U,uQ⟩
      refine ⟨J+1,fun _ => by omega,by omega,
        .merge sj jT quiet hit.2.2 partQ less uQ old trace,extra,?_,?_⟩
      · have cb : begin.card ≤ 2 := band_card _ _
        have cs : skip.card ≤ r+2 := band_card _ _
        have c₁ := Finset.card_union_le begin skip
        have c₂ := Finset.card_union_le (begin ∪ skip) inside
        have c₃ := Finset.card_union_le (begin ∪ skip ∪ inside) tail
        let fee := r+4+internalBudget C
        change tail.card ≤ J*fee+2 at htail
        change (begin ∪ skip ∪ inside ∪ tail).card ≤ (J+1)*fee+2
        rw [Nat.add_mul, Nat.one_mul]
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
      refine ⟨0,fun h => Finset.card_pos.mpr h,Nat.zero_le _,.stop quiet,band s 2,
        by simpa using band_card s 2,?_⟩
      intro t st ht
      rcases waiting_round D e₀ G P s T t part st ht quiet (active t ht) with early | ⟨A,ha,bi⟩ | low
      · exact Or.inr (Or.inr (in_band st early))
      · exact Or.inr (Or.inl (accounted A ha t st ht bi))
      · exact Or.inl low

private theorem low_accounting [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (K T : ℕ) :
    ∃ events I : Finset ℕ, (∀ t, t ∈ events ↔ t < T ∧ LowAt H G K t) ∧
      events.card ≤ Fintype.card V*(K-1) ∧ I.card ≤ 3*events.card ∧
      ∀ t, t < T → LowWindow H G K t → t ∈ I := by
  classical
  let events := (Finset.range T).filter (LowAt H G K)
  let I := (Finset.range T).filter (LowWindow H G K)
  have ev {t : ℕ} : t ∈ events ↔ t < T ∧ LowAt H G K t := by simp [events]
  have wi {t : ℕ} : t ∈ I ↔ t < T ∧ LowWindow H G K t := by simp [I]
  have bound : events.card ≤ Fintype.card V*(K-1) := by
    by_cases inhabited : Nonempty V
    · letI : Inhabited V := ⟨Classical.choice inhabited⟩
      have choosePay (t : ℕ) (h : LowAt H G K t) :
          ∃ p : V × V, Born H G t p.1 p.2 ∧ hostDegree (run H G (t+1)) p.1 < K := by
        obtain ⟨x,y,birth,low⟩ := h
        exact ⟨(x,y),birth,low⟩
      let pay := fun t => if h : LowAt H G K t then Classical.choose (choosePay t h) else (default,default)
      apply paid_rounds H G K events pay
      intro t ht
      have h := (ev.mp ht).2
      simpa [pay,h] using Classical.choose_spec (choosePay t h)
    · have empty : events = ∅ := Finset.eq_empty_iff_forall_not_mem.mpr (by
        intro t ht
        obtain ⟨x,_,_,_⟩ := (ev.mp ht).2
        exact inhabited ⟨x⟩)
      rw [empty]
      simp
  have cov (t : ℕ) (h : t ∈ I) : ∃ e ∈ events, e ≤ t ∧ t < e+3 := by
    obtain ⟨ht,e,low,et,near⟩ := wi.mp h
    exact ⟨e,ev.mpr ⟨by omega,low⟩,et,near⟩
  have count := window_card events I 3 cov
  exact ⟨events,I,fun _ => ev,bound,by simpa only [Nat.mul_comm events.card 3] using count,
    fun _ ht h => wi.mpr ⟨ht,h⟩⟩

theorem accounted_time [Fintype C] [Fintype E] [Fintype V] (D : Data C E) (e₀ : E)
    (G : SimpleGraph V) (r : ℕ) (radius : ∀ s, RadiusAt D s r) :
    ∃ (J : ℕ) (events : Finset ℕ),
      MergeTrace D G (stabilizationTime D.rule G) r 0 singletons J ∧
      J ≤ Fintype.card V - 1 ∧
      (∀ t, t ∈ events ↔ t < stabilizationTime D.rule G ∧ LowAt D.rule G (threshold C E) t) ∧
      events.card ≤ Fintype.card V*(threshold C E-1) ∧
      stabilizationTime D.rule G ≤ J*(r+4+internalBudget C)+2+3*events.card := by
  classical
  let T := stabilizationTime D.rule G
  have active (t : ℕ) (ht : t<T) := before_stop D.rule G ht
  have initial (A : Finset V) (ha : A ∈ (singletons (V := V))) (t : ℕ) (_ : 0 ≤ t) (_ : t<T)
      (inside : InternalBirth D.rule G A t) : t ∈ (∅ : Finset ℕ) := by
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨a,ha,b,hb,birth⟩ := inside
    exact False.elim (birth.1.ne ((Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm))
  obtain ⟨J,strictJ,limit,trace,extra,he,cov⟩ := cover_horizon D e₀ G T r radius active (Fintype.card V) 0
    singletons (singleton_partition D G) (le_of_eq singletons_card) ∅ initial
  obtain ⟨events,low,ev,cap,hl,lowPays⟩ := low_accounting D.rule G (threshold C E) T
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
  have count : J ≤ Fintype.card V - 1 := by
    by_cases nonempty : (singletons (V := V)).Nonempty
    · have strict := strictJ nonempty
      rw [singletons_card] at strict
      omega
    · have zero := Finset.not_nonempty_iff_eq_empty.mp nonempty
      have size₀ := singletons_card (V := V)
      rw [zero,Finset.card_empty] at size₀
      omega
  refine ⟨J,events,trace,count,ev,cap,?_⟩
  change T ≤ _
  omega


end Bootstrap.Subdivision

#print axioms Bootstrap.Subdivision.accounted_time
