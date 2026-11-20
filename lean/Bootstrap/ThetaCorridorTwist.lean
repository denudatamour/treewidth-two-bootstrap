import Bootstrap.ThetaCorridor

namespace Bootstrap.Theta.Corridor

/-- Both rearrangements are local to the long arm. The uncoloured twist uses
its first two segments. The coloured twist uses its first three, with the
second segment traversed in the opposite orientation to the first and third. -/
def twistIndex (coloured : Bool) (d z : ℕ) : ℕ :=
  if coloured then
    if d-1 ≤ z ∧ z ≤ 3*d-3 then z+2 else
      if z=3*d-2 then d else if z=3*d-1 then d-1 else z
  else
    if 0<z ∧ z≤d-2 then 2*d-z else if d-2<z ∧ z<2*d then z-(d-2) else z

def span (coloured : Bool) (d : ℕ) : ℕ := if coloured then 3*d else 2*d

theorem twist_injective (c : Bool) (d : ℕ) (hd : 3 ≤ d) : Function.Injective (twistIndex c d) := by
  intro x y e
  cases c <;> simp only [twistIndex,Bool.false_eq_true,if_false,if_true] at e <;>
    split_ifs at e <;> omega

theorem twist_bounds (c : Bool) {d z L : ℕ} (hd : 3 ≤ d) (room : span c d ≤ L)
    (pos : 0<z) (bound : z<L) : 0 < twistIndex c d z ∧ twistIndex c d z < L := by
  cases c <;> simp only [span,twistIndex,Bool.false_eq_true,if_false,if_true] at room ⊢ <;>
    split_ifs <;> omega

private noncomputable def finTwist (c : Bool) {d l : ℕ} (hd : 3 ≤ d) (room : span c d ≤ l+2) :
    Equiv.Perm (Fin (l+1)) := by
  let f (j : Fin (l+1)) : Fin (l+1) :=
    ⟨twistIndex c d (j.val+1) - 1,by
      have h : 0 < twistIndex c d (j.val+1) ∧ twistIndex c d (j.val+1) < l+2 :=
        twist_bounds c hd room (by omega) (by have := j.isLt; omega)
      omega⟩
  have value (j : Fin (l+1)) : (f j).val+1 = twistIndex c d (j.val+1) := by
    have h : 0 < twistIndex c d (j.val+1) ∧ twistIndex c d (j.val+1) < l+2 :=
      twist_bounds c hd room (by omega) (by have := j.isLt; omega)
    exact Nat.sub_add_cancel h.1
  have inj : Function.Injective f := by
    intro i j e
    have eq := (value i).symm.trans ((congrArg (fun k : Fin (l+1) => k.val+1) e).trans (value j))
    exact Fin.ext (Nat.add_right_cancel (twist_injective c d hd eq))
  exact Equiv.ofBijective f ⟨inj,Finite.surjective_of_injective inj⟩

private theorem finTwist_value (c : Bool) {d l : ℕ} (hd : 3 ≤ d) (room : span c d ≤ l+2)
    (j : Fin (l+1)) : (finTwist c hd room j).val+1 = twistIndex c d (j.val+1) := by
  change twistIndex c d (j.val+1)-1+1 = _
  have h : 0 < twistIndex c d (j.val+1) ∧ twistIndex c d (j.val+1) < l+2 :=
      twist_bounds c hd room (by omega) (by have := j.isLt; omega)
  exact Nat.sub_add_cancel h.1

noncomputable def twist {k : ℕ} (m : Fin k → ℕ) (a : Fin k) (c : Bool) (d : ℕ)
    (hd : 3 ≤ d) (room : span c d ≤ m a+2) : Equiv.Perm (Vertex m) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sigmaCongrRight
    (fun i => if h : i=a then finTwist c hd (by rw [h]; exact room) else Equiv.refl _))

@[simp] theorem twist_pole {k : ℕ} (m : Fin k → ℕ) (a : Fin k) (c : Bool) (d : ℕ)
    (hd : 3 ≤ d) (room : span c d ≤ m a+2) (b : Bool) :
    twist m a c d hd room (pole m b) = pole m b := rfl

theorem twist_point {k : ℕ} (m : Fin k → ℕ) (a : Fin k) (c : Bool) (d : ℕ)
    (hd : 3 ≤ d) (room : span c d ≤ m a+2) (i : Fin k) (z : ℕ) (bound : z ≤ m i+2) :
    twist m a c d hd room (point m i z) = point m i (if i=a then twistIndex c d z else z) := by
  by_cases zero : z=0
  · subst z
    have eq : twistIndex c d 0=0 := by
      cases c <;> simp only [twistIndex,Bool.false_eq_true,if_false,if_true] <;> split_ifs <;> omega
    simp [eq]
  by_cases last : z=m i+2
  · subst z
    by_cases h : i=a
    · subst i
      have eq : twistIndex c d (m a+2) = m a+2 := by
        cases c <;> simp only [span,twistIndex,Bool.false_eq_true,if_false,if_true] at room ⊢ <;>
          split_ifs <;> omega
      simp [eq]
    · simp [h]
  · have lt : z<m i+2 := by omega
    have pos : 0<z := by omega
    let j : Fin (m i+1) := ⟨z-1,by omega⟩
    have jval : j.val+1=z := by dsimp [j]; omega
    rw [show point m i z = inner m i j from point_interior m pos lt]
    by_cases h : i=a
    · subst i
      rw [if_pos rfl]
      change inner m a ((if h : a=a then finTwist c hd (by rw [h]; exact room) else Equiv.refl _) j) = _
      rw [dif_pos rfl,←jval,←finTwist_value c hd room j,point_inner]
    · rw [if_neg h,←jval,point_inner]
      change inner m i ((if e : i=a then finTwist c hd (by rw [e]; exact room) else Equiv.refl _) j) = _
      rw [dif_neg h]
      rfl

end Bootstrap.Theta.Corridor

#print axioms Bootstrap.Theta.Corridor.twist_point
