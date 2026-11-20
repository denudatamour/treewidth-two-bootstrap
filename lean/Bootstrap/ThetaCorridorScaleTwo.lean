import Bootstrap.ThetaCorridor

namespace Bootstrap.Theta.Corridor

private theorem even_joint (r : Fin 3 → ℕ) (x : V r 2)
    (even : naturalColor (M r 2) 0 x=false) : ∃ b, Junction r 2 b x := by
  cases x with
  | inl b => exact ⟨b,rfl⟩
  | inr p =>
    obtain ⟨i,j⟩ := p
    have hi : ¬(j.val+1)%2=1 := of_decide_eq_false even
    exact ⟨_,by omega,rfl⟩

private theorem odd_port (r : Fin 3 → ℕ) (x : V r 2)
    (odd : naturalColor (M r 2) 0 x=true) (b : Bool) : Port r 2 b x := by
  cases x with
  | inl z => cases z <;> contradiction
  | inr p =>
    obtain ⟨i,j⟩ := p
    have rem : (j.val+1)%2=1 := of_decide_eq_true odd
    let t := decide (((j.val+1)/2)%2=1)
    by_cases bt : b=t
    · exact Or.inl ⟨rem,bt⟩
    · apply Or.inr
      refine ⟨by omega,?_⟩
      change b=(!t)
      have flip (x y : Bool) (h : x ≠ y) : x=(!y) := by cases x <;> cases y <;> simp_all
      exact flip b t bt

/-- At scale two an internal position is both ports of its segment.
In either colouring convention the segment graph already contains the
natural complete bipartite graph. -/
theorem scale_two_complete (r : Fin 3 → ℕ) (pos : ∀ i, 0<r i) (c : Bool)
    (inc : segmentGraph r 2 c ≤ F r 2) :
    F r 2 = completeBetween (naturalColor (M r 2) 0) := by
  have even (i : Fin 3) : (M r 2 i+2)%2=0%2 := by
    change (r i*2-2+2)%2=0
    have hr := pos i
    rw [Nat.sub_add_cancel (by omega)]
    exact Nat.mul_mod_left _ _
  apply le_antisymm (terminal_le_natural _ (by decide) 0 even)
  have cross (x y : V r 2) (hx : naturalColor (M r 2) 0 x=false)
      (hy : naturalColor (M r 2) 0 y=true) : (F r 2).Adj x y := by
    obtain ⟨b,hb⟩ := even_joint r x hx
    have ne : x ≠ y := fun e => Bool.false_ne_true (hx.symm.trans (e ▸ hy))
    exact inc (Or.inr ⟨ne,Or.inl ⟨b,b,hb,odd_port r y hy b,fun _ => rfl⟩⟩)
  intro x y e
  change naturalColor (M r 2) 0 x ≠ naturalColor (M r 2) 0 y at e
  cases hx : naturalColor (M r 2) 0 x <;> cases hy : naturalColor (M r 2) 0 y
  · exact False.elim (e (hx.trans hy.symm))
  · exact cross x y hx hy
  · exact (F r 2).symm (cross y x hy hx)
  · exact False.elim (e (hx.trans hy.symm))

end Bootstrap.Theta.Corridor

#print axioms Bootstrap.Theta.Corridor.scale_two_complete
