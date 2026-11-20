import Bootstrap.SubdivisionWindows

namespace Bootstrap.Subdivision.Appendix
open DegreeTwo
open scoped Classical
variable {C E V : Type*}

/-- An unordered ordinary host edge born in the update from time t to t+1. -/
def EdgeBorn (D : Data C E) (G : SimpleGraph V) (t : ℕ) (e : UEdge V) : Prop :=
  ∃ x y, s(x,y)=e.val ∧ Born D.rule G t x y

/-- A full source injection and its missing incidence. Every other incidence
is checked in the old graph. The target is one undirected host edge. -/
structure Chosen (D : Data C E) (G : SimpleGraph V) (t : ℕ) (e : UEdge V) where
  embed : C ⊕ E ↪ V
  base : C
  midpoint : E
  incident : D.ends base midpoint
  target : s(embed (.inl base),embed (.inr midpoint)) = e.val
  old : ∀ i j, D.rule.Adj i j →
    ¬((i=.inl base ∧ j=.inr midpoint) ∨ (i=.inr midpoint ∧ j=.inl base)) →
    (run D.rule G t).Adj (embed i) (embed j)

/-- Any selection of one legitimate witness per ordinary birth. -/
abbrev Selection (D : Data C E) (G : SimpleGraph V) :=
  ∀ t e, EdgeBorn D G t e → Chosen D G t e

theorem witnesses_exist (D : Data C E) (G : SimpleGraph V) : Nonempty (Selection D G) := by
  classical
  suffices ∀ t e, EdgeBorn D G t e → Nonempty (Chosen D G t e) from
    ⟨fun t e h => Classical.choice (this t e h)⟩
  rintro t e ⟨x,y,xy,birth,absent⟩
  rcases birth with prev|⟨u,v,f,edge,fx,fy,old⟩
  · exact (absent prev).elim
  · cases u with
    | inl c =>
      cases v with
      | inl z => exact edge.elim
      | inr a => exact ⟨⟨f,c,a,edge,by rw [fx,fy,xy],old⟩⟩
    | inr a =>
      cases v with
      | inr z => exact edge.elim
      | inl c => exact ⟨⟨f,c,a,edge,by rw [fy,fx,Sym2.eq_swap,xy],
          fun i j h outside => old i j h (fun inj => outside inj.symm)⟩⟩

namespace Chosen
variable {D : Data C E} {G : SimpleGraph V} {t : ℕ} {e : UEdge V}

def endpoints (w : Chosen D G t e) : V × V := (w.embed (.inl w.base),w.embed (.inr w.midpoint))

theorem born (w : Chosen D G t e) (h : EdgeBorn D G t e) :
    Born D.rule G t w.endpoints.1 w.endpoints.2 := by
  obtain ⟨x,y,eq,b⟩ := h
  have hxy : s(w.endpoints.1,w.endpoints.2)=s(x,y) := w.target.trans eq.symm
  rcases Sym2.eq_iff.mp hxy with ⟨a,c⟩|⟨a,c⟩
  · rwa [a,c]
  · rw [a,c]
    exact b.symm

theorem full (w : Chosen D G t e) (h : EdgeBorn D G t e) : FullCopy D.rule (run D.rule G (t+1)) w.embed := by
  intro i j a
  by_cases gap : (i=.inl w.base ∧ j=.inr w.midpoint) ∨ (i=.inr w.midpoint ∧ j=.inl w.base)
  · rcases gap with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact (w.born h).1
    · exact (w.born h).1.symm
  · exact run_le_succ D.rule G t (w.old i j a gap)

def Crosses (w : Chosen D G t e) (P : Finset (Finset V)) : Prop :=
  ∃ i j : C, blockOf P (w.embed (.inl i)) ≠ blockOf P (w.embed (.inl j))

theorem first_crosses (w : Chosen D G t e) (P : Finset (Finset V)) (x y : V)
    (ends : s(x,y)=e.val)
    (first : ∀ a b, blockOf P a=blockOf P x → blockOf P b=blockOf P y → ¬(run D.rule G t).Adj a b) :
    w.Crosses P := by
  obtain ⟨c,ne,hit⟩ : ∃ c : C, c≠w.base ∧ D.ends c w.midpoint := by
    rcases w.incident with side|side
    · exact ⟨D.right _,fun h => (D.proper _) (side ▸ h.symm),Or.inr rfl⟩
    · exact ⟨D.left _,fun h => (D.proper _) (h.trans side),Or.inl rfl⟩
  have prior := w.old (.inl c) (.inr w.midpoint) hit (by
    rintro (⟨a,_⟩|⟨a,_⟩)
    · exact ne (Sum.inl.inj a)
    · cases a)
  refine ⟨c,w.base,?_⟩
  intro one
  rcases Sym2.eq_iff.mp (w.target.trans ends.symm) with ⟨bx,my⟩|⟨by',mx⟩
  · exact first _ _ (one.trans (congrArg (blockOf P) bx)) (congrArg (blockOf P) my) prior
  · exact first _ _ (congrArg (blockOf P) mx) (one.trans (congrArg (blockOf P) by')) prior.symm
end Chosen

/-- The half-open interval of updates s≤t<stop excludes the triggering update
and its merger period. The first two updates remain eligible for charging. -/
structure Waiting (V : Type*) where
  start : ℕ
  stop : ℕ
  blocks : Finset (Finset V)

def Quiet [Fintype C] [Fintype E] [Fintype V] (D : Data C E) (G : SimpleGraph V)
    (periods : List (Waiting V)) : Prop :=
  ∀ I ∈ periods, ∀ t, I.start≤t → t<I.stop →
    ¬Trigger D (run D.rule G (t+1)) (blockOf I.blocks) (threshold C E)

/-- One bill per unordered edge, including all simultaneous births whose
selected witness spans blocks during a nontriggering waiting update. -/
noncomputable def charges [Fintype V] (D : Data C E) (G : SimpleGraph V)
    (choose : Selection D G) (T : ℕ) (periods : List (Waiting V)) : Finset (ℕ × UEdge V) := by
  classical
  exact ((Finset.range T).product Finset.univ).filter fun p =>
    ∃ h : EdgeBorn D G p.1 p.2, ∃ I ∈ periods,
      I.start≤p.1 ∧ p.1<I.stop ∧ (choose p.1 p.2 h).Crosses I.blocks

theorem mem_charges [Fintype V] (D : Data C E) (G : SimpleGraph V) (choose : Selection D G)
    (T : ℕ) (periods : List (Waiting V)) (t : ℕ) (e : UEdge V) :
    (t,e)∈charges D G choose T periods ↔ t<T ∧ ∃ h : EdgeBorn D G t e, ∃ I∈periods,
      I.start≤t ∧ t<I.stop ∧ (choose t e h).Crosses I.blocks := by
  simp [charges]

theorem charge_cap [Fintype C] [Fintype E] [Fintype V] (D : Data C E) (G : SimpleGraph V)
    (choose : Selection D G) (T : ℕ) (periods : List (Waiting V)) (quiet : Quiet D G periods) :
    (charges D G choose T periods).card ≤ (threshold C E-1)*Fintype.card V := by
  classical
  let K := threshold C E
  let bills := charges D G choose T periods
  let S := lowSet D.rule G K
  have details (p : ↥bills) := (mem_charges D G choose T periods p.val.1 p.val.2).mp p.2
  let source (p : ↥bills) := choose p.val.1 p.val.2 (details p).2.choose
  have low (p : ↥bills) : hostDegree (run D.rule G (p.val.1+1)) (source p).endpoints.1 < K := by
    have h := (details p).2.choose_spec
    obtain ⟨I,hI,lo,hi,cross⟩ := h
    by_contra high
    exact quiet I hI _ lo hi ⟨(source p).embed,(source p).full (details p).2.choose,cross,
      (source p).base,Nat.le_of_not_gt high⟩
  have member (p : ↥bills) : (source p).endpoints.2 ∈ S (source p).endpoints.1 :=
    mem_lowSet.mpr ⟨p.val.1+1,((source p).born (details p).2.choose).1,low p⟩
  let enc (v : V) : ↥(S v) ↪ Fin (K-1) := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa [S] using lowSet_card D.rule G K v))
  let packed : (Σ v, ↥(S v)) ↪ V × Fin (K-1) := ⟨fun p => (p.1,enc p.1 p.2),by
    rintro ⟨v,w⟩ ⟨v',w'⟩ h
    have same : v=v' := congrArg Prod.fst h
    subst v'
    have rest : enc v w = enc v w' := congrArg Prod.snd h
    exact congrArg (Sigma.mk v) ((enc v).injective rest)⟩
  let tag (p : ↥bills) : Σ v, ↥(S v) := ⟨_,⟨_,member p⟩⟩
  have inj : Function.Injective tag := by
    intro p q eq
    have ends : (source p).endpoints=(source q).endpoints :=
      congrArg (fun z : Σ v, ↥(S v) => (z.1,z.2.val)) eq
    have first := congrArg Prod.fst ends
    have second := congrArg Prod.snd ends
    have b := (source p).born (details p).2.choose
    rw [first,second] at b
    have time := birth_time_unique b ((source q).born (details q).2.choose)
    have same : p.val.2.val=q.val.2.val := by
      have a : s((source p).endpoints.1,(source p).endpoints.2)=p.val.2.val := (source p).target
      rw [first,second] at a
      exact a.symm.trans (source q).target
    exact Subtype.ext (Prod.ext time (Subtype.ext same))
  have bound := Fintype.card_le_of_injective (fun p => packed (tag p)) (packed.injective.comp inj)
  simpa [Nat.mul_comm,bills,K] using bound

end Bootstrap.Subdivision.Appendix

#print axioms Bootstrap.Subdivision.Appendix.witnesses_exist
#print axioms Bootstrap.Subdivision.Appendix.Chosen.first_crosses
#print axioms Bootstrap.Subdivision.Appendix.charge_cap
