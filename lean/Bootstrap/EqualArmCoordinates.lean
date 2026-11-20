import Bootstrap.ThetaRules

/-! Coordinates and rigidity of paths in theta graphs with three equal arms. -/
namespace Bootstrap.Theta.EqualArms

abbrev M (m : Nat) := fun _ : Fin 3 => m
abbrev V (m : Nat) := Vertex (M m)
abbrev H (m : Nat) := graph (M m)
abbrev L (m : Nat) := m + 2

/-- An arm coordinate counted from the left pole; its endpoints have coordinates 0 and L m. -/
def point (m : Nat) (i : Fin 3) (t : Nat) : V m :=
  if t = 0 then pole (M m) false else
    if h : t ≤ m + 1 then inner (M m) i ⟨t-1,by change t-1 < m+1; omega⟩ else pole (M m) true

def oriented (m : Nat) (b : Bool) (i : Fin 3) (t : Nat) : V m :=
  point m i (if b then L m - t else t)

def level {m : Nat} : V m → Nat
  | .inl false => 0
  | .inl true => L m
  | .inr ⟨_,j⟩ => j.val + 1

def armNumber {m : Nat} : V m → Option (Fin 3)
  | .inl _ => none
  | .inr ⟨i,_⟩ => some i

@[simp] theorem point_zero (m : Nat) (i : Fin 3) : point m i 0 = pole (M m) false := by
  simp [point]

@[simp] theorem point_last (m : Nat) (i : Fin 3) : point m i (L m) = pole (M m) true := by
  simp [point,L]

theorem point_inner (m : Nat) (i : Fin 3) (j : Fin (m+1)) :
    point m i (j.val+1) = inner (M m) i j := by
  have jh : j.val+1 ≤ m+1 := by omega
  simp [point,jh]

theorem level_point (m : Nat) (i : Fin 3) (t : Nat) (ht : t ≤ L m) : level (point m i t) = t := by
  unfold point
  split
  · rename_i eq
    exact eq.symm
  · split
    · change t-1+1 = t
      omega
    · change L m = t
      unfold L at *
      omega

theorem arm_point (m : Nat) (i : Fin 3) (t : Nat) (h₀ : 0 < t) (ht : t < L m) :
    armNumber (point m i t) = some i := by
  have l : t ≤ m+1 := by unfold L at ht; omega
  simp [point,Nat.ne_of_gt h₀,l,inner,armNumber]

@[simp] theorem oriented_zero (m : Nat) (b : Bool) (i : Fin 3) :
    oriented m b i 0 = pole (M m) b := by cases b <;> simp [oriented]

@[simp] theorem oriented_last (m : Nat) (b : Bool) (i : Fin 3) :
    oriented m b i (L m) = pole (M m) (!b) := by cases b <;> simp [oriented]

theorem oriented_reverse (m : Nat) (b : Bool) (i : Fin 3) (t : Nat) (ht : t ≤ L m) :
    oriented m (!b) i (L m - t) = oriented m b i t := by
  cases b <;> simp [oriented,Nat.sub_sub_self ht]

theorem oriented_inj (m : Nat) (b : Bool) (i : Fin 3) {s t : Nat}
    (hs : s ≤ L m) (ht : t ≤ L m) (eq : oriented m b i s = oriented m b i t) : s = t := by
  have z := congrArg level eq
  cases b
  · simpa only [oriented,Bool.false_eq_true,if_false,level_point _ _ _ hs,level_point _ _ _ ht] using z
  · change level (point m i (L m-s)) = level (point m i (L m-t)) at z
    rw [level_point _ _ _ (Nat.sub_le ..),level_point _ _ _ (Nat.sub_le ..)] at z
    omega

theorem oriented_arm_inj (m : Nat) (b : Bool) {i j : Fin 3} {t : Nat}
    (h₀ : 0 < t) (ht : t < L m) (eq : oriented m b i t = oriented m b j t) : i = j := by
  have z := congrArg armNumber eq
  cases b
  · change armNumber (point m i t) = armNumber (point m j t) at z
    simpa only [arm_point _ _ _ h₀ ht, Option.some.injEq] using z
  · have h₁ : 0 < L m-t := by omega
    have h₂ : L m-t < L m := by omega
    change armNumber (point m i (L m-t)) = armNumber (point m j (L m-t)) at z
    simpa only [arm_point _ _ _ h₁ h₂, Option.some.injEq] using z

theorem point_edge (m : Nat) (i : Fin 3) (t : Nat) (ht : t < L m) :
    (H m).Adj (point m i t) (point m i (t+1)) := by
  by_cases zero : t = 0
  · subst t
    rw [point_zero, show (0+1 : Nat) = (0 : Fin (m+1)).val + 1 from rfl,point_inner]
    rfl
  have lt : t ≤ m+1 := by unfold L at ht; omega
  let j : Fin (m+1) := ⟨t-1,by omega⟩
  have e : point m i t = inner (M m) i j := by
    simp [point,zero,lt,j]
  rw [e]
  by_cases last : t+1 = L m
  · rw [last,point_last]
    change t-1 = m
    unfold L at last
    omega
  · let q : Fin (m+1) := ⟨t,by unfold L at *; omega⟩
    rw [show t+1 = q.val+1 from rfl,point_inner]
    exact ⟨rfl,Or.inl (by change t-1+1 = t; omega)⟩

theorem oriented_edge (m : Nat) (b : Bool) (i : Fin 3) (t : Nat) (ht : t < L m) :
    (H m).Adj (oriented m b i t) (oriented m b i (t+1)) := by
  cases b
  · exact point_edge m i t ht
  · have h₁ : L m - (t+1) < L m := by omega
    have h₂ : L m - (t+1) + 1 = L m-t := by omega
    simpa only [oriented, Bool.true_eq, if_true, ←h₂] using (point_edge m i _ h₁).symm

theorem pole_neighbor (m : Nat) (b : Bool) {v : V m} (h : (H m).Adj (pole (M m) b) v) :
    ∃ i, v = oriented m b i 1 := by
  rcases v with c | ⟨i,j⟩
  · exact False.elim h
  · refine ⟨i,?_⟩
    cases b
    · change j.val = 0 at h
      have eq : oriented m false i 1 = inner (M m) i j := by
        change point m i 1 = _
        rw [show 1 = j.val+1 by omega,point_inner]
      exact eq.symm
    · change j.val = m at h
      have eq : oriented m true i 1 = inner (M m) i j := by
        change point m i (L m-1) = _
        rw [show L m-1 = j.val+1 by unfold L; omega,point_inner]
      exact eq.symm

private theorem middle_two (m : Nat) (b : Bool) (i : Fin 3) {t : Nat}
    (h₀ : 0 < t) (ht : t < L m) :
    DegreeTwo.TwoNeighbours (H m) (oriented m b i t)
      (oriented m b i (t-1)) (oriented m b i (t+1)) := by
  have n : DegreeTwo.HasTwo (H m) (oriented m b i t) := by
    have interior (a : Nat) (a₀ : 0 < a) (aL : a < L m) : DegreeTwo.HasTwo (H m) (point m i a) := by
      have l : a ≤ m+1 := by unfold L at aL; omega
      simp only [point,Nat.ne_of_gt a₀,if_false,dif_pos l]
      exact twoNeighbours_inner _ _ _
    cases b
    · exact interior t h₀ ht
    · exact interior (L m-t) (by omega) (by omega)
  apply n.pair
  · have ed := (oriented_edge m b i (t-1) (by omega)).symm
    rwa [show t-1+1=t by omega] at ed
  · exact oriented_edge _ _ _ _ ht
  · intro e
    have := oriented_inj _ _ _ (s:=t-1) (t:=t+1) (by omega) (by omega) e
    omega

/-- A nonrepeating image path which has entered an arm from a pole follows that
arm until the opposite pole or until its prescribed segment ends. -/
theorem trace (m : Nat) (f : V m ↪ V m) (b c : Bool) (i a : Fin 3) (n : Nat)
    (bound : n ≤ L m) (start : f (pole (M m) b) = pole (M m) c)
    (first : f (oriented m b i 1) = oriented m c a 1)
    (keep : ∀ t, t < n → (H m).Adj (f (oriented m b i t)) (f (oriented m b i (t+1)))) :
    ∀ t, t ≤ n → f (oriented m b i t) = oriented m c a t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro le
    cases t with
    | zero => simpa only [oriented_zero] using start
    | succ t =>
      cases t with
      | zero => exact first
      | succ t =>
        have mid := middle_two m c a (t := t+1) (by omega) (by omega)
        have midEq := ih (t+1) (by omega) (by omega)
        have edge := keep (t+1) (by omega)
        rw [midEq] at edge
        rcases mid.only _ edge with back | forward
        · have old := ih t (by omega) (by omega)
          have wrong : f (oriented m b i (t+2)) = f (oriented m b i t) := by
            simpa only [Nat.add_sub_cancel,old] using back
          have := oriented_inj m b i (s:=t+2) (t:=t) (by omega) (by omega) (f.injective wrong)
          omega
        · exact forward

end Bootstrap.Theta.EqualArms

#print axioms Bootstrap.Theta.EqualArms.trace
