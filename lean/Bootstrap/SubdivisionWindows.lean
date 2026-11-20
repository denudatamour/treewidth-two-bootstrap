import Bootstrap.SubdivisionPartition
import Bootstrap.OrdinaryTime

namespace Bootstrap.Subdivision

open DegreeTwo
variable {W C E V : Type*}

theorem Born.symm {H : SimpleGraph W} {G : SimpleGraph V} {t : ℕ} {x y : V}
    (h : Born H G t x y) : Born H G t y x :=
  ⟨(run H G (t+1)).symm h.1,fun hyx => h.2 ((run H G t).symm hyx)⟩

theorem before_stop [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) {t : ℕ}
    (ht : t < stabilizationTime H G) : ∃ x y, Born H G t x y := by
  classical
  by_contra no
  have fixed : run H G t = run H G (t+1) := by
    ext x y
    constructor
    · exact fun h => run_le_succ H G t h
    · intro h
      by_contra absent
      exact no ⟨x,y,h,absent⟩
  exact (Nat.not_le_of_gt ht) (Nat.find_min' (stable_exists H G) fixed)

def InternalBirth (H : SimpleGraph W) (G : SimpleGraph V) (A : Finset V) (t : ℕ) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, Born H G t x y

def LowAt [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (K t : ℕ) : Prop :=
  ∃ x y, Born H G t x y ∧ hostDegree (run H G (t+1)) x < K

def LowWindow [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (K t : ℕ) : Prop :=
  ∃ e, LowAt H G K e ∧ e ≤ t ∧ t < e+3

theorem internal_pairs (H : SimpleGraph W) (G : SimpleGraph V) (A : Finset V) (I : Finset ℕ)
    (hI : ∀ i ∈ I, InternalBirth H G A i) : I.card ≤ A.card.choose 2 := by
  classical
  have data (i : ↥I) : ∃ p : ↥A × ↥A, Born H G i p.1.1 p.2.1 := by
    obtain ⟨x,hx,y,hy,h⟩ := hI i i.2
    exact ⟨(⟨x,hx⟩,⟨y,hy⟩),h⟩
  let p := fun i : ↥I => Classical.choose (data i)
  have valid (i : ↥I) : Born H G i (p i).1.1 (p i).2.1 := Classical.choose_spec (data i)
  have distinct (i : ↥I) : (p i).1 ≠ (p i).2 := fun h => (valid i).1.ne (congrArg Subtype.val h)
  let f : ↥I ↪ UEdge ↥A := ⟨fun i => ⟨Sym2.mk (p i), fun h => distinct i ((Sym2.isDiag_iff_proj_eq (p i)).mp h)⟩,by
    intro i j eq
    have equal : Sym2.mk (p i) = Sym2.mk (p j) := congrArg Subtype.val eq
    rcases Sym2.mk_eq_mk_iff.mp equal with same | swapped
    · have hi := valid i
      rw [same] at hi
      exact Subtype.ext (birth_time_unique hi (valid j))
    · have hi := valid i
      rw [swapped] at hi
      exact Subtype.ext (birth_time_unique hi (valid j).symm)⟩
  have card : Fintype.card (UEdge ↥A) = (Fintype.card ↥A).choose 2 := Sym2.card_subtype_not_diag
  have bound := Fintype.card_le_of_embedding f
  rw [card] at bound
  simpa only [Fintype.card_coe] using bound

def internalBudget (C : Type*) [Fintype C] : ℕ := max 3 ((Fintype.card C).choose 2)

/-- At its creation a block can be charged for every future internal birth
in that same vertex set, even if it later merges with other blocks. -/
theorem internal_lifetime [Fintype C] [Fintype E] (D : Data C E) (e₀ : E)
    (G : SimpleGraph V) (s T : ℕ) {A : Finset V} (state : Block D (run D.rule G s) A) :
    ∃ I : Finset ℕ, I.card ≤ internalBudget C ∧
      ∀ t, s ≤ t → t < T → InternalBirth D.rule G A t → t ∈ I := by
  classical
  let I := (Finset.range T).filter (fun t => s ≤ t ∧ InternalBirth D.rule G A t)
  have spec {t : ℕ} : t ∈ I ↔ t < T ∧ s ≤ t ∧ InternalBirth D.rule G A t := by simp [I]
  refine ⟨I,?_, fun t st ht h => spec.mpr ⟨ht,st,h⟩⟩
  by_cases nonempty : I.Nonempty
  · rcases state with single | ⟨pool,nb,np,cert⟩
    · obtain ⟨i,hi⟩ := nonempty
      obtain ⟨x,hx,y,hy,born⟩ := (spec.mp hi).2.2
      exact False.elim (born.1.ne (single x hx y hy))
    · by_cases eq : Fintype.card C = A.card
      · have bound := internal_pairs D.rule G A I (fun _ hi => (spec.mp hi).2.2)
        rw [←eq] at bound
        exact le_trans bound (le_max_right _ _)
      · have large : Fintype.card C < A.card := by omega
        let first := I.min' nonempty
        have hf : first ∈ I := Finset.min'_mem I nonempty
        obtain ⟨x,hx,y,hy,hborn⟩ := (spec.mp hf).2.2
        have hsf := (spec.mp hf).2.1
        have block' := block_mono (time_mono D.rule G (by omega : s ≤ first+1))
          (show Block D (run D.rule G s) A from Or.inr ⟨pool,nb,np,cert⟩)
        have all := internal_two D e₀ G (first+1) block' large hx hy hborn.1
        have cover (t : ℕ) (ht : t ∈ I) : ∃ e ∈ ({first} : Finset ℕ), e ≤ t ∧ t < e+3 := by
          have early : first ≤ t := Finset.min'_le I t ht
          refine ⟨first,Finset.mem_singleton_self _,early,?_⟩
          by_contra no
          obtain ⟨a,ha,b,hb,bt⟩ := (spec.mp ht).2.2
          exact bt.2 (time_mono D.rule G (by omega : first+1+1+1 ≤ t) (all a ha b hb bt.1.ne))
        have bound := window_card {first} I 3 cover
        exact le_trans (by simpa using bound) (le_max_left 3 _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty]
    simp

theorem count_low_windows [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (K T : ℕ) :
    ∃ I : Finset ℕ, I.card ≤ 3*(Fintype.card V*(K-1)) ∧
      ∀ t, t < T → LowWindow H G K t → t ∈ I := by
  classical
  let events := (Finset.range T).filter (LowAt H G K)
  let I := (Finset.range T).filter (LowWindow H G K)
  have ev {t : ℕ} : t ∈ events ↔ t < T ∧ LowAt H G K t := by simp [events]
  have wi {t : ℕ} : t ∈ I ↔ t < T ∧ LowWindow H G K t := by simp [I]
  refine ⟨I,?_,fun t ht h => wi.mpr ⟨ht,h⟩⟩
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
  omega

/-- In a waiting interval, a round that is neither an initial waiting step
nor an internal birth belongs to the three-round window of a genuine low
first contact. Both blocks and the initial contact are found in the run. -/
theorem waiting_round [Fintype C] [Fintype E] [Fintype V] (D : Data C E) (e₀ : E)
    (G : SimpleGraph V) (P : Finset (Finset V)) (s stop t : ℕ)
    (part : Partition D (run D.rule G s) P) (st : s ≤ t) (before : t < stop)
    (quiet : ∀ i, s ≤ i → i < stop → ¬ Trigger D (run D.rule G (i+1)) (blockOf P) (threshold C E))
    (active : ∃ x y, Born D.rule G t x y) :
    t < s+2 ∨ (∃ A ∈ P, InternalBirth D.rule G A t) ∨ LowWindow D.rule G (threshold C E) t := by
  classical
  obtain ⟨x,y,birth⟩ := active
  let A := blockOf P x
  let B := blockOf P y
  have hx := part.spec x
  have hy := part.spec y
  by_cases same : A=B
  · exact Or.inr (Or.inl ⟨A,hx.1,x,hx.2,y,same.symm ▸ hy.2,birth⟩)
  · let contact := fun n => ∃ a ∈ A, ∃ b ∈ B, (run D.rule G n).Adj a b
    have witnessed : s ≤ t+1 ∧ contact (t+1) := ⟨by omega,x,hx.2,y,hy.2,birth.1⟩
    have ex : ∃ n, s ≤ n ∧ contact n := ⟨t+1,witnessed⟩
    let j := Nat.find ex
    have spec : s ≤ j ∧ contact j := Nat.find_spec ex
    have sj := spec.1
    have jt : j ≤ t+1 := Nat.find_min' ex witnessed
    obtain ⟨a,ha,b,hb,original⟩ := spec.2
    have grow := time_mono D.rule G sj
    have dis := part.apart A hx.1 B hy.1 same
    have final := rectangle_two D e₀ G j (block_mono grow (part.certified A hx.1))
      (block_mono grow (part.certified B hy.1)) dis ha hb original
    have latest : t < j+2 := by
      by_contra late
      exact birth.2 (time_mono D.rule G (by omega : j+1+1 ≤ t) (final x hx.2 y hy.2))
    by_cases immediately : j=s
    · exact Or.inl (by omega)
    · right
      right
      have index : j-1+1=j := by omega
      have new : (step D.rule (run D.rule G (j-1))).Adj a b := by
        change (run D.rule G (j-1+1)).Adj a b
        rwa [index]
      have first (p q : V) (pa : blockOf P p = blockOf P a) (qb : blockOf P q = blockOf P b) :
          ¬ (run D.rule G (j-1)).Adj p q := by
        intro edge
        have ap : blockOf P p = A := pa.trans (part.label_eq hx.1 ha)
        have bq : blockOf P q = B := qb.trans (part.label_eq hy.1 hb)
        exact Nat.find_min ex (by omega : j-1 < j)
          ⟨by omega,p,ap ▸ (part.spec p).2,q,bq ▸ (part.spec q).2,edge⟩
      have low := first_contact_low D (run D.rule G (j-1)) (blockOf P) (threshold C E)
        (quiet (j-1) (by omega) (by omega)) new first
      have newBirth : Born D.rule G (j-1) a b := ⟨new,first a b rfl rfl⟩
      refine ⟨j-1,?_,by omega,by omega⟩
      rcases low with h | h
      · exact ⟨a,b,newBirth,h⟩
      · exact ⟨b,a,newBirth.symm,h⟩

end Bootstrap.Subdivision

#print axioms Bootstrap.Subdivision.internal_pairs
#print axioms Bootstrap.Subdivision.internal_lifetime
#print axioms Bootstrap.Subdivision.count_low_windows
#print axioms Bootstrap.Subdivision.waiting_round
