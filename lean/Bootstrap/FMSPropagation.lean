import Bootstrap.FMSComponent

namespace Bootstrap.FMS

variable {W V : Type*}

/-- The seed clique has height zero. Each positive height has a single vertex. -/
def level {h ℓ : ℕ} : Fin h ⊕ Fin ℓ → ℕ
  | .inl _ => 0
  | .inr i => i.val+1

def tailGraph (h ℓ : ℕ) : SimpleGraph (Fin h ⊕ Fin ℓ) where
  Adj x y := x ≠ y ∧ ((level x=0 ∧ level y=0) ∨ Near (level x) (level y))
  symm := by
    rintro x y ⟨ne,⟨hx,hy⟩|near⟩
    · exact ⟨ne.symm,Or.inl ⟨hy,hx⟩⟩
    · exact ⟨ne.symm,Or.inr near.symm⟩
  loopless := fun _ e => e.1 rfl

theorem level_injective_above_zero {h ℓ : ℕ} {x y : Fin h ⊕ Fin ℓ}
    (hx : 0 < level x) (same : level x = level y) : x = y := by
  cases x with
  | inl x => simp [level] at hx
  | inr x =>
    cases y with
    | inl y => simp [level] at same
    | inr y =>
      apply congrArg Sum.inr
      apply Fin.ext
      exact Nat.add_right_cancel same

private theorem walk_stays {D : SimpleGraph W} {J : SimpleGraph V} (f : W ↪ V)
    (height : V → ℕ) (cut : ℕ)
    (keep : ∀ i j, D.Adj i j → J.Adj (f i) (f j))
    (bounded : ∀ x y, J.Adj x y → cut < height x → Near (height x) (height y))
    {i j : W} (p : D.Walk i j) (start : cut+p.length < height (f i)) :
    cut < height (f j) := by
  induction p with
  | nil => exact start
  | @cons a b c e tail ih =>
    change cut+(tail.length+1) < height (f a) at start
    have near := bounded _ _ (keep _ _ e) (by omega)
    apply ih
    rcases near with h|h <;> omega

/-- Beyond t times the rule order, even an ordinary witness cannot make a
non-nearest-neighbour edge. The component of either far endpoint would fit
inside the untouched tail by following simple witness paths. -/
theorem frontier [Fintype W] {H : SimpleGraph W} [DecidableRel H.Adj]
    (conn : H.Connected) (min : HasTwoNeighbours H) (high : ∃ w, 2 < H.degree w)
    {J : SimpleGraph V} (height : V → ℕ)
    (unique : ∀ x y, 0 < height x → height x = height y → x=y)
    (initial : ∀ x y, J.Adj x y → 0 < height x → Near (height x) (height y))
    (t : ℕ) : ∀ x y, (run H J t).Adj x y →
      t * Fintype.card W < height x → Near (height x) (height y) := by
  induction t with
  | zero => simpa using initial
  | succ t ih =>
    intro x y e far
    rw [Nat.succ_mul] at far
    rcases e with old|⟨u,v,f,uv,hx,_,copy⟩
    · exact ih x y old (by omega)
    let D := deleted H u v
    have keep (i j : W) (edge : D.Adj i j) : (run H J t).Adj (f i) (f j) :=
      copy i j edge.1 edge.2
    have large (i : W) (reachable : D.Reachable u i) : t * Fintype.card W < height (f i) := by
      obtain ⟨p,hp⟩ := reachable.exists_isPath
      have len := hp.length_lt
      apply walk_stays f height (t * Fintype.card W) keep ih p
      rw [hx]
      omega
    apply False.elim
    apply component_not_path conn min high uv u (fun i => height (f i))
    · intro i j ri _ same
      exact f.injective (unique _ _ (Nat.zero_lt_of_lt (large i ri)) same)
    · intro i j ri edge
      exact ih _ _ (keep _ _ edge) (large i ri)

theorem tail_frontier [Fintype W] {H : SimpleGraph W} [DecidableRel H.Adj]
    (conn : H.Connected) (min : HasTwoNeighbours H) (high : ∃ w, 2 < H.degree w)
    (h ℓ t : ℕ) (x y : Fin h ⊕ Fin ℓ) (e : (run H (tailGraph h ℓ) t).Adj x y)
    (far : t * Fintype.card W < level x) : Near (level x) (level y) := by
  apply frontier conn min high level (fun _ _ => level_injective_above_zero) _ t x y e far
  rintro i j ⟨_,⟨hi,_⟩|near⟩ pos
  · omega
  · exact near

end Bootstrap.FMS

#print axioms Bootstrap.FMS.frontier
#print axioms Bootstrap.FMS.tail_frontier
