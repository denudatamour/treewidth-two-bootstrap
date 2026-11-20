import Bootstrap.AppendixMergeSchedule
import Bootstrap.AppendixBudget

namespace Bootstrap.Subdivision.Appendix
open DegreeTwo
open scoped Classical
variable {C E V : Type*}

private def Covered (B : Finset (ℕ × UEdge V)) (t : ℕ) : Prop :=
  ∃ p∈B, p.1≤t ∧ t<p.1+3

private theorem waiting_window [Fintype C] [Fintype E] [Fintype V] (D : Data C E) (e₀ : E)
    (G : SimpleGraph V) (choose : Selection D G) (T : ℕ) (periods : List (Waiting V))
    (P : Finset (Finset V)) (s stop t : ℕ) (listed : (⟨s,stop,P⟩ : Waiting V) ∈ periods) (endT : stop≤T)
    (part : Partition D (run D.rule G s) P) (st : s ≤ t) (before : t < stop)
    (active : ∃ x y, Born D.rule G t x y) :
    t < s+2 ∨ (∃ A ∈ P, InternalBirth D.rule G A t) ∨ Covered (charges D G choose T periods) t := by
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
      have born : Born D.rule G (j-1) a b := ⟨new,first a b rfl rfl⟩
      let e : UEdge V := ⟨s(a,b),fun diag => born.1.ne ((Sym2.isDiag_iff_proj_eq (a,b)).mp diag)⟩
      have fresh : EdgeBorn D G (j-1) e := ⟨a,b,rfl,born⟩
      have bill : (j-1,e)∈charges D G choose T periods := by
        apply (mem_charges D G choose T periods _ _).mpr
        refine ⟨by omega,fresh,⟨s,stop,P⟩,listed,?_,?_,?_⟩
        · change s≤j-1
          omega
        · change j-1<stop
          omega
        · exact (choose _ _ fresh).first_crosses P a b rfl first
      exact ⟨(j-1,e),bill,by change j-1≤t; omega,by change t<j-1+3; omega⟩

private def band (s w : ℕ) := (Finset.range w).image (fun k => s+k)

private theorem band_card (s w : ℕ) : (band s w).card≤w := by
  simpa only [Finset.card_range] using (Finset.card_image_le (s:=Finset.range w) (f:=fun k => s+k))

private theorem in_band {s w t : ℕ} (lo : s≤t) (hi : t<s+w) : t∈band s w :=
  Finset.mem_image.mpr ⟨t-s,Finset.mem_range.mpr (by omega),by omega⟩

/-- Away from internal, initial, trigger and propagation rounds, the update
lies in the three-round window of a specifically charged ordinary edge. -/
private theorem cover [Fintype C] [Fintype E] [Fintype V] (D : Data C E) (e₀ : E) (G : SimpleGraph V)
    (T r : ℕ) (choose : Selection D G) (periods : List (Waiting V))
    (active : ∀ t, t<T → ∃ x y, Born D.rule G t x y)
    {s J : ℕ} {P : Finset (Finset V)} {L : List (Waiting V)} (trace : Schedule D G T r s P J L) :
    Partition D (run D.rule G s) P → (∀ I∈L, I∈periods) →
      ∀ known : Finset ℕ, (∀ A∈P, ∀ t, s≤t → t<T → InternalBirth D.rule G A t → t∈known) →
      ∃ extra : Finset ℕ, extra.card ≤ J*(r+4+internalBudget C)+2 ∧
        ∀ t, s≤t → t<T → Covered (charges D G choose T periods) t ∨ t∈known ∨ t∈extra := by
  classical
  induction trace with
  | @stop s P quiet =>
    intro part sub known accounted
    refine ⟨band s 2,by simpa using band_card s 2,?_⟩
    intro t st ht
    rcases waiting_window D e₀ G choose T periods P s T t (sub _ (by simp)) le_rfl part st ht
      (active t ht) with early|⟨A,hA,inside⟩|wind
    · exact Or.inr (Or.inr (in_band st early))
    · exact Or.inr (Or.inl (accounted A hA t st ht inside))
    · exact Or.inl wind
  | @merge s P j Q U J tail start before first op newPart less next ih =>
    intro part sub known accounted
    let s' := j+1+r+1
    obtain ⟨_,uQ,remains⟩ := op.facts
    obtain ⟨inside,hinside,insidePays⟩ := internal_lifetime D e₀ G s' T (newPart.certified U uQ)
    have recordQ (A : Finset V) (hA : A∈Q) (t : ℕ) (fromNext : s'≤t) (ht : t<T)
        (born : InternalBirth D.rule G A t) : t∈known ∪ inside := by
      rcases remains A hA with old|rfl
      · exact Finset.mem_union_left _ (accounted A old t (by dsimp [s'] at fromNext; omega) ht born)
      · exact Finset.mem_union_right _ (insidePays t fromNext ht born)
    obtain ⟨rest,hrest,covered⟩ := ih newPart (fun I hI => sub I (List.mem_cons_of_mem _ hI)) _ recordQ
    let early := band s 2
    let skip := band j (r+2)
    let extra := early ∪ skip ∪ inside ∪ rest
    refine ⟨extra,?_,?_⟩
    · have lim₁ := band_card s 2
      have lim₂ := band_card j (r+2)
      have c₁ := Finset.card_union_le early skip
      have c₂ := Finset.card_union_le (early ∪ skip) inside
      have c₃ := Finset.card_union_le (early ∪ skip ∪ inside) rest
      change early.card≤2 at lim₁
      change skip.card≤r+2 at lim₂
      dsimp only [extra]
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · intro t st ht
      by_cases wait : t<j
      · rcases waiting_window D e₀ G choose T periods P s j t (sub _ List.mem_cons_self)
          before.le part st wait (active t ht) with head|⟨A,hA,born⟩|wind
        · exact Or.inr (Or.inr (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (show t∈early from in_band st head)))))
        · exact Or.inr (Or.inl (accounted A hA t st ht born))
        · exact Or.inl wind
      by_cases during : t<s'
      · have sk : t∈skip := in_band (by omega) (by dsimp [s'] at during; omega)
        exact Or.inr (Or.inr (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ sk))))
      · rcases covered t (by change s'≤t; omega) ht with wind|old|done_
        · exact Or.inl wind
        · rcases Finset.mem_union.mp old with past|thisBlock
          · exact Or.inr (Or.inl past)
          · exact Or.inr (Or.inr (Finset.mem_union_left _ (Finset.mem_union_right _ thisBlock)))
        · exact Or.inr (Or.inr (Finset.mem_union_right _ done_))

end Bootstrap.Subdivision.Appendix

namespace Bootstrap.Subdivision.Appendix
open DegreeTwo
open scoped Classical
variable {C E V : Type*}

theorem charged_edge_unique [Fintype V] (D : Data C E) (G : SimpleGraph V) (choose : Selection D G)
    (T : ℕ) (L : List (Waiting V)) (e : UEdge V) {i j : ℕ}
    (a : (i,e)∈charges D G choose T L) (b : (j,e)∈charges D G choose T L) : i=j := by
  obtain ⟨⟨x,y,hxy,bi⟩,_⟩ := ((mem_charges D G choose T L i e).mp a).2
  obtain ⟨⟨p,q,hpq,bj⟩,_⟩ := ((mem_charges D G choose T L j e).mp b).2
  rcases Sym2.eq_iff.mp (hxy.trans hpq.symm) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact birth_time_unique bi bj
  · exact birth_time_unique bi bj.symm

/-- Projecting away the birth index preserves cardinality, so the bills count
ordinary unordered host edges once each. -/
theorem projected_charge_card [Fintype V] (D : Data C E) (G : SimpleGraph V) (choose : Selection D G)
    (T : ℕ) (L : List (Waiting V)) :
    ((charges D G choose T L).image Prod.snd).card = (charges D G choose T L).card := by
  apply Finset.card_image_of_injOn
  rintro ⟨i,a⟩ hi ⟨j,b⟩ hj eq
  change a=b at eq
  subst b
  exact Prod.ext (charged_edge_unique D G choose T L a hi hj) rfl

theorem time_for_schedule [Fintype C] [Fintype E] [Fintype V] (D : Data C E) (e₀ : E) (G : SimpleGraph V)
    (r J : ℕ) (L : List (Waiting V)) (trace : Schedule D G (stabilizationTime D.rule G) r 0 singletons J L)
    (choose : Selection D G) :
    let T := stabilizationTime D.rule G
    let B := charges D G choose T L
    T ≤ (r+1)*J+2*(J+1)+J+internalBudget C*J+3*B.card := by
  classical
  let T := stabilizationTime D.rule G
  let B := charges D G choose T L
  let starts := B.image Prod.fst
  let windows := (Finset.range T).filter (Covered B)
  have count : windows.card ≤ starts.card*3 := by
    apply window_card starts windows 3
    intro t sat
    obtain ⟨p,hp,lo,hi⟩ := (Finset.mem_filter.mp sat).2
    exact ⟨p.1,Finset.mem_image_of_mem _ hp,lo,hi⟩
  have atMost : starts.card≤B.card := Finset.card_image_le
  have initial (A : Finset V) (hA : A∈(singletons (V:=V))) (t : ℕ) (_ : 0≤t) (_ : t<T)
      (inside : InternalBirth D.rule G A t) : t∈(∅ : Finset ℕ) := by
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨a,ha,b,hb,born⟩ := inside
    exact (born.1.ne ((Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm)).elim
  obtain ⟨extra,size,cov⟩ := cover D e₀ G T r choose L (fun t => before_stop D.rule G) trace
    (singleton_partition D G) (fun _ h => h) ∅ initial
  have subset : Finset.range T ⊆ windows ∪ extra := by
    intro t ht
    rcases cov t (Nat.zero_le _) (Finset.mem_range.mp ht) with wind|no|done_
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht,wind⟩)
    · exact (Finset.not_mem_empty _ no).elim
    · exact Finset.mem_union_right _ done_
  have n := Finset.card_le_card subset
  rw [Finset.card_range] at n
  have u := Finset.card_union_le windows extra
  change T ≤ (r+1)*J+2*(J+1)+J+internalBudget C*J+3*B.card
  calc
    T ≤ J*(r+4+internalBudget C)+2+3*B.card := by omega
    _ = _ := by
      simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_one,
        Nat.mul_comm J r,Nat.mul_comm J (internalBudget C)]
      omega

private theorem has_base_edge [Fintype C] (D : Data C E) (c₂ : 2≤Fintype.card C)
    (conn : D.baseGraph.Connected) : Nonempty E := by
  haveI : Nontrivial C := Fintype.one_lt_card_iff_nontrivial.mp c₂
  obtain ⟨a,b,diff⟩ := exists_pair_ne C
  obtain ⟨p⟩ := conn a b
  cases p with
  | nil => exact (diff rfl).elim
  | cons adj _ => exact ⟨adj.choose⟩

/-- Appendix A's estimate with the paper's K, diameter and internal budget, the
actual number J of merges and exactly the charged base-crossing births. A
single schedule works for every legal choice of witnesses for the new edges. -/
theorem displayed_edge_budget [Fintype C] [Fintype E] [Fintype V] (D : Data C E)
    (c₂ : 2≤Fintype.card C) (conn : D.baseGraph.Connected) (G : SimpleGraph V) :
    let T := stabilizationTime D.rule G
    let r := D.baseGraph.diam
    ∃ J L, Schedule D G T r 0 singletons J L ∧ MergeTrace D G T r 0 singletons J ∧
      J ≤ Fintype.card V-1 ∧ L.length=J+1 ∧ (Fintype.card V=0 → T=0) ∧
      ∀ choose : Selection D G, let B := charges D G choose T L
        B.card≤(threshold C E-1)*Fintype.card V ∧
        T ≤ (r+1)*J+2*(J+1)+J+internalBudget C*J+3*B.card := by
  classical
  let T := stabilizationTime D.rule G
  let r := D.baseGraph.diam
  obtain ⟨e₀⟩ := has_base_edge D c₂ conn
  obtain ⟨J,L,trace⟩ := make_schedule D e₀ G T r (radius_diam D conn) 0 singletons (singleton_partition D G)
  have count := trace.count
  rw [singletons_card] at count
  refine ⟨J,L,trace,trace.merger_trace,count.1,count.2,?_,?_⟩
  · intro empty
    by_contra nonzero
    obtain ⟨v,_,_⟩ := before_stop D.rule G (by omega : 0<stabilizationTime D.rule G)
    have pos := Fintype.card_pos_iff.mpr (show Nonempty V from ⟨v⟩)
    omega
  · intro choose
    exact ⟨charge_cap D G choose T L trace.quiet,time_for_schedule D e₀ G r J L trace choose⟩

end Bootstrap.Subdivision.Appendix

#print axioms Bootstrap.Subdivision.Appendix.charged_edge_unique
#print axioms Bootstrap.Subdivision.Appendix.projected_charge_card
#print axioms Bootstrap.Subdivision.Appendix.time_for_schedule
#print axioms Bootstrap.Subdivision.Appendix.displayed_edge_budget
