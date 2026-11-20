import Bootstrap.OrdinaryTime

/-! Isolated-vertex padding in the ordinary (untyped, injective) process, used after (5). -/
namespace Bootstrap

variable {W V Z : Type*}

/-- Each rule vertex has two distinct neighbours, the pointwise minimum-degree assumption. -/
def HasTwoNeighbours (H : SimpleGraph W) : Prop :=
  ∀ w, ∃ i j, i ≠ j ∧ H.Adj w i ∧ H.Adj w j

/-- Add isolated vertices of any type, keeping all old vertices as the left summand. -/
def padIsolates (G : SimpleGraph V) (Z : Type*) : SimpleGraph (V ⊕ Z) where
  Adj x y := ∃ i j : V, Sum.inl i = x ∧ Sum.inl j = y ∧ G.Adj i j
  symm := by
    rintro x y ⟨i, j, hi, hj, h⟩
    exact ⟨j, i, hj, hi, G.symm h⟩
  loopless := by
    rintro x ⟨i, j, hi, hj, h⟩
    exact (G.ne_of_adj h) (Sum.inl.inj (hi.trans hj.symm))

@[simp] theorem pad_adj_inl (G : SimpleGraph V) (x y : V) :
    (padIsolates G Z).Adj (.inl x) (.inl y) ↔ G.Adj x y := by
  change (∃ i j, (Sum.inl i : V ⊕ Z) = .inl x ∧ Sum.inl j = .inl y ∧ G.Adj i j) ↔ _
  simp

private theorem incident_after_deletion (H : SimpleGraph W) (hdeg : HasTwoNeighbours H)
    (a b : W) (hab : H.Adj a b) (w : W) :
    ∃ j, H.Adj w j ∧ ¬ ((w = a ∧ j = b) ∨ (w = b ∧ j = a)) := by
  obtain ⟨i,j,hij,hi,hj⟩ := hdeg w
  by_cases h : (w = a ∧ i = b) ∨ (w = b ∧ i = a)
  · refine ⟨j, hj, ?_⟩
    have hne : a ≠ b := H.ne_of_adj hab
    rintro (⟨ha,hb⟩ | ⟨hb,ha⟩) <;> rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> subst_vars <;> simp_all
  · exact ⟨i,hi,h⟩

theorem witness_pad_iff (H : SimpleGraph W) (hdeg : HasTwoNeighbours H)
    (G : SimpleGraph V) (Z : Type*) (x y : V ⊕ Z) :
    Witness H (padIsolates G Z) x y ↔
      ∃ i j : V, Sum.inl i = x ∧ Sum.inl j = y ∧ Witness H G i j := by
  classical
  constructor
  · rintro ⟨a,b,f,hab,hx,hy,hold⟩
    have imageOld (w : W) : ∃ v : V, Sum.inl v = f w := by
      obtain ⟨j,hj,hsurv⟩ := incident_after_deletion H hdeg a b hab w
      obtain ⟨i, _, hi, _, _⟩ := hold w j hj hsurv
      exact ⟨i,hi⟩
    choose g hg using imageOld
    let emb : W ↪ V := ⟨g, fun i j he => f.injective ((hg i).symm.trans
      ((congrArg (Sum.inl : V → V ⊕ Z) he).trans (hg j)))⟩
    refine ⟨g a, g b, (hg a).trans hx, (hg b).trans hy, a, b, emb, hab, rfl, rfl, ?_⟩
    intro i j hij hn
    apply (pad_adj_inl (Z := Z) G (g i) (g j)).mp
    rw [hg i, hg j]
    exact hold i j hij hn
  · rintro ⟨i,j,rfl,rfl,a,b,f,hab,hx,hy,hold⟩
    let incl : V ↪ V ⊕ Z := ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩
    refine ⟨a,b,f.trans incl,hab,congrArg Sum.inl hx,congrArg Sum.inl hy,?_⟩
    intro k l hkl hn
    exact ⟨f k, f l, rfl, rfl, hold k l hkl hn⟩

theorem pad_step (H : SimpleGraph W) (hdeg : HasTwoNeighbours H) (G : SimpleGraph V)
    (Z : Type*) : step H (padIsolates G Z) = padIsolates (step H G) Z := by
  ext x y
  change ((padIsolates G Z).Adj x y ∨ Witness H (padIsolates G Z) x y) ↔ _
  rw [witness_pad_iff H hdeg G Z]
  constructor
  · rintro (⟨i,j,hi,hj,h⟩ | ⟨i,j,hi,hj,h⟩)
    · exact ⟨i,j,hi,hj,Or.inl h⟩
    · exact ⟨i,j,hi,hj,Or.inr h⟩
  · rintro ⟨i,j,hi,hj,h | h⟩
    · exact Or.inl ⟨i,j,hi,hj,h⟩
    · exact Or.inr ⟨i,j,hi,hj,h⟩

theorem pad_run (H : SimpleGraph W) (hdeg : HasTwoNeighbours H) (G : SimpleGraph V)
    (Z : Type*) (t : ℕ) : run H (padIsolates G Z) t = padIsolates (run H G t) Z := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, pad_step H hdeg, run_succ]

theorem pad_injective (Z : Type*) :
    Function.Injective (fun G : SimpleGraph V => padIsolates G Z) := by
  intro G G' he
  change padIsolates G Z = padIsolates G' Z at he
  ext x y
  exact (pad_adj_inl (Z := Z) G x y).symm.trans
    ((show (padIsolates G Z).Adj (.inl x) (.inl y) ↔
      (padIsolates G' Z).Adj (.inl x) (.inl y) by rw [he]).trans (pad_adj_inl G' x y))

theorem stabilizationTime_pad [Fintype V] [Fintype Z] (H : SimpleGraph W)
    (hdeg : HasTwoNeighbours H) (G : SimpleGraph V) :
    stabilizationTime H (padIsolates G Z) = stabilizationTime H G := by
  apply stabilizationTime_eq_of_fixed_iff
  intro t
  rw [pad_run H hdeg, pad_run H hdeg]
  exact (pad_injective Z).eq_iff

theorem le_maxTime_of_padding [Fintype V] (H : SimpleGraph W)
    (hdeg : HasTwoNeighbours H) (G : SimpleGraph V) (k : ℕ) :
    stabilizationTime H G ≤ maxTime H (Fintype.card V + k) := by
  have h := le_maxTime_card H (padIsolates G (Fin k))
  rw [stabilizationTime_pad H hdeg] at h
  simpa using h

end Bootstrap

#print axioms Bootstrap.witness_pad_iff
#print axioms Bootstrap.pad_run
#print axioms Bootstrap.stabilizationTime_pad
#print axioms Bootstrap.le_maxTime_of_padding
