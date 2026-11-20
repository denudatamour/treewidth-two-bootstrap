import Bootstrap.SubdivisionLinear

namespace Bootstrap

variable {W U V : Type*}

theorem witness_rule_iso {H : SimpleGraph W} {H' : SimpleGraph U} (e : H ≃g H')
    (J : SimpleGraph V) {x y : V} (w : Witness H J x y) : Witness H' J x y := by
  obtain ⟨u,v,f,edge,hx,hy,keep⟩ := w
  let g := e.symm.toEquiv.toEmbedding.trans f
  have inverse (a : U) (i : W) (h : e.symm a = i) : a = e i := by
    calc
      a = e (e.symm a) := (e.toEquiv.apply_symm_apply a).symm
      _ = e i := congrArg e h
  refine ⟨e u,e v,g,e.map_adj_iff.mpr edge,?_,?_,?_⟩
  · change f (e.symm (e u)) = x
    simpa using hx
  · change f (e.symm (e v)) = y
    simpa using hy
  · intro a b hab hn
    apply keep (e.symm a) (e.symm b) (e.symm.map_adj_iff.mpr hab)
    rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
    · exact hn (Or.inl ⟨inverse _ _ ha,inverse _ _ hb⟩)
    · exact hn (Or.inr ⟨inverse _ _ ha,inverse _ _ hb⟩)

theorem step_rule_iso {H : SimpleGraph W} {H' : SimpleGraph U} (e : H ≃g H') (J : SimpleGraph V) :
    step H J = step H' J := by
  ext x y
  exact ⟨fun h => h.elim Or.inl (fun w => Or.inr (witness_rule_iso e J w)),
    fun h => h.elim Or.inl (fun w => Or.inr (witness_rule_iso e.symm J w))⟩

theorem run_rule_iso {H : SimpleGraph W} {H' : SimpleGraph U} (e : H ≃g H')
    (J : SimpleGraph V) (n : ℕ) : run H J n = run H' J n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ,run_succ,ih,step_rule_iso e]

theorem stabilizationTime_rule_iso [Fintype V] {H : SimpleGraph W} {H' : SimpleGraph U}
    (e : H ≃g H') (J : SimpleGraph V) : stabilizationTime H J = stabilizationTime H' J := by
  classical
  apply Nat.le_antisymm
  · apply Nat.find_min' (stable_exists H J)
    rw [run_rule_iso e,run_rule_iso e]
    exact stabilizationTime_spec H' J
  · apply Nat.find_min' (stable_exists H' J)
    rw [run_rule_iso e.symm,run_rule_iso e.symm]
    exact stabilizationTime_spec H J

theorem maxTime_rule_iso {H : SimpleGraph W} {H' : SimpleGraph U} (e : H ≃g H') (n : ℕ) :
    maxTime H n = maxTime H' n := by
  apply Nat.le_antisymm
  · apply (maxTime_le_iff _ _ _).mpr
    intro J
    rw [stabilizationTime_rule_iso e]
    exact le_maxTime _ _
  · apply (maxTime_le_iff _ _ _).mpr
    intro J
    rw [stabilizationTime_rule_iso e.symm]
    exact le_maxTime _ _

namespace Subdivision

open DegreeTwo
variable {C E : Type*}

def Data.project (D : Data C E) : C ⊕ E → C
  | .inl c => c
  | .inr e => D.left e

private theorem adjacent_projects (D : Data C E) {i j : C ⊕ E} (h : D.rule.Adj i j) :
    D.baseGraph.Reachable (D.project i) (D.project j) := by
  have link (c : C) (e : E) (ed : D.ends c e) : D.baseGraph.Reachable c (D.left e) := by
    rcases ed with eq | eq
    · subst c
      exact .rfl
    · subst c
      exact SimpleGraph.Adj.reachable (G := D.baseGraph) ⟨e,Or.inr ⟨rfl,rfl⟩⟩
  cases i with
  | inl c =>
    cases j with
    | inl c' => exact False.elim h
    | inr e => exact link c e h
  | inr e =>
    cases j with
    | inl c => exact (link c e h).symm
    | inr d => exact False.elim h

theorem connected_base_of_rule (D : Data C E) (conn : D.rule.Connected) : D.baseGraph.Connected := by
  letI : Nonempty C := conn.nonempty.map D.project
  have walks {i j : C ⊕ E} (path : D.rule.Reachable i j) : D.baseGraph.Reachable (D.project i) (D.project j) := by
    have reach := (D.rule.reachable_iff_reflTransGen i j).mp path
    clear path
    induction reach with
    | refl => exact .rfl
    | tail _ e ih => exact ih.trans (adjacent_projects D e)
  exact ⟨fun i j => walks (conn (.inl i) (.inl j))⟩

/-- Undo the once-subdivision using the degree predicates of the original
rule. Parallel edges are retained by using the old degree-two roles as the
edge indices. The resulting isomorphism is a theorem about H itself. -/
theorem suppress_short_routes [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    (short : ¬ ∃ i j, H.Adj i j ∧ H.degree i = 2 ∧ H.degree j = 2) :
    ∃ D : Data {w : W // H.degree w ≠ 2} {w : W // H.degree w = 2}, Nonempty (D.rule ≃g H) := by
  classical
  let C := {w : W // H.degree w ≠ 2}
  let E := {w : W // H.degree w = 2}
  have ports (e : E) : ∃ a b : C, TwoNeighbours H e.1 a.1 b.1 := by
    obtain ⟨l,r,N⟩ := (hasTwo_iff_degree H e.1).mpr e.2
    have dl : H.degree l ≠ 2 := fun h => short ⟨e.1,l,N.left,e.2,h⟩
    have dr : H.degree r ≠ 2 := fun h => short ⟨e.1,r,N.right,e.2,h⟩
    exact ⟨⟨l,dl⟩,⟨r,dr⟩,N⟩
  let left := fun e : E => Classical.choose (ports e)
  let right := fun e : E => Classical.choose (Classical.choose_spec (ports e))
  have spec (e : E) : TwoNeighbours H e.1 (left e).1 (right e).1 :=
    Classical.choose_spec (Classical.choose_spec (ports e))
  let D : Data C E := ⟨left,right,fun e eq => (spec e).distinct (congrArg Subtype.val eq)⟩
  let f : C ⊕ E ≃ W := {
    toFun := Sum.elim Subtype.val Subtype.val
    invFun := fun w => if h : H.degree w = 2 then .inr ⟨w,h⟩ else .inl ⟨w,h⟩
    left_inv := by
      rintro (⟨w,hw⟩ | ⟨w,hw⟩) <;> simp [hw]
    right_inv := by
      intro w
      by_cases h : H.degree w = 2 <;> simp [h] }
  have link (c : C) (e : E) : H.Adj c.1 e.1 ↔ D.ends c e := by
    constructor
    · intro h
      rcases (spec e).only c.1 (H.symm h) with eq | eq
      · exact Or.inl (Subtype.ext eq)
      · exact Or.inr (Subtype.ext eq)
    · rintro (rfl | rfl)
      · exact H.symm (spec e).left
      · exact H.symm (spec e).right
  refine ⟨D,⟨⟨f,?_⟩⟩⟩
  intro i j
  cases i with
  | inl c =>
    cases j with
    | inl d =>
      change H.Adj c.1 d.1 ↔ False
      refine ⟨?_,False.elim⟩
      intro h
      rcases cover _ _ h with eq | eq
      · exact c.2 eq
      · exact d.2 eq
    | inr e => exact link c e
  | inr e =>
    cases j with
    | inl c => exact ⟨fun h => (link c e).mp (H.symm h),fun h => H.symm ((link c e).mpr h)⟩
    | inr d =>
      change H.Adj e.1 d.1 ↔ False
      exact ⟨fun h => short ⟨e.1,d.1,h,e.2,d.2⟩,False.elim⟩

/-- The no-long-route branch of Theorem II.1 for arbitrary graph labels,
without a subdivision presentation as input. -/
theorem short_rule_linear [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (conn : H.Connected)
    (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    (short : ¬ ∃ i j, H.Adj i j ∧ H.degree i = 2 ∧ H.degree j = 2) :
    ∃ K : ℕ, ∀ n, maxTime H n ≤ K*n := by
  classical
  obtain ⟨D,⟨iso⟩⟩ := suppress_short_routes H cover short
  have linked := connected_base_of_rule D (iso.connected_iff.mpr conn)
  refine ⟨slope {w : W // H.degree w ≠ 2} {w : W // H.degree w = 2},fun n => ?_⟩
  rw [← maxTime_rule_iso iso n]
  exact once_subdivision_linear D linked n

end Subdivision
end Bootstrap

#print axioms Bootstrap.maxTime_rule_iso
#print axioms Bootstrap.Subdivision.suppress_short_routes
#print axioms Bootstrap.Subdivision.short_rule_linear
