import Bootstrap.ThetaReflections

namespace Bootstrap.Theta

open scoped Classical
variable {k : ℕ}

def indexZ (n : ℕ) [NeZero n] (z : ℤ) : Fin n := z • (1 : Fin n)

theorem indexZ_nat (n : ℕ) [NeZero n] (z : ℕ) : indexZ n (z:ℤ) = (z : Fin n) := by simp [indexZ]
theorem indexZ_add (n : ℕ) [NeZero n] (x y : ℤ) : indexZ n (x+y) = indexZ n x+indexZ n y := add_zsmul _ _ _
theorem indexZ_neg (n : ℕ) [NeZero n] (x : ℤ) : indexZ n (-x) = -indexZ n x := neg_zsmul _ _
theorem indexZ_length (n : ℕ) [NeZero n] : indexZ n (n:ℤ)=0 := by
  apply Fin.ext
  rw [indexZ_nat,Fin.val_natCast,Nat.mod_self]
  rfl

theorem indexZ_val (n : ℕ) [NeZero n] (x : Fin n) : indexZ n (x.val:ℤ)=x := by
  apply Fin.ext
  rw [indexZ_nat,Fin.val_natCast,Nat.mod_eq_of_lt x.isLt]

def intPt (m : Fin k → ℕ) (i j : Fin k) (z : ℤ) : Vertex m := cyclePt m i j (indexZ _ z)

/-- Position on the closed arm, including both poles. -/
def armPt (m : Fin k → ℕ) (i : Fin k) (t : ℕ) : Vertex m :=
  if t=0 then pole m false else
  if lt : t < armSize m i then inner m i ⟨t-1,by dsimp [armSize] at lt; omega⟩ else pole m true

theorem armPt_zero (m : Fin k → ℕ) (i : Fin k) : armPt m i 0=pole m false := by simp [armPt]
theorem armPt_last (m : Fin k → ℕ) (i : Fin k) : armPt m i (armSize m i)=pole m true := by
  simp [armPt,armSize]
theorem armPt_inner (m : Fin k → ℕ) (i : Fin k) (d : Fin (m i+1)) :
    armPt m i (d.val+1)=inner m i d := by
  have h := d.isLt
  have lt : d.val+1 < armSize m i := by dsimp [armSize]; omega
  simp [armPt,lt]

theorem intPt_first (m : Fin k → ℕ) (i j : Fin k) (t : ℕ) (ht : t ≤ armSize m i) :
    intPt m i j (t:ℤ) = armPt m i t := by
  have lt : t<perimeter m i j := by dsimp [perimeter,armSize] at *; omega
  have val : (indexZ (perimeter m i j) (t:ℤ)).val = t := by
    rw [indexZ_nat,Fin.val_natCast,Nat.mod_eq_of_lt lt]
  unfold intPt cyclePt armPt
  simp only [val]
  split_ifs <;> first | rfl | (exfalso;omega)

theorem intPt_second (m : Fin k → ℕ) (i j : Fin k) (t : ℕ) (ht : t ≤ armSize m j) :
    intPt m i j (-(t:ℤ)) = armPt m j t := by
  by_cases zero : t=0
  · subst t; simpa using intPt_first m i j 0 (Nat.zero_le _)
  have lt : t<perimeter m i j := by dsimp [perimeter,armSize] at *; omega
  have cap : perimeter m i j - t < perimeter m i j := by omega
  have val : (indexZ (perimeter m i j) (-(t:ℤ))).val = perimeter m i j - t := by
    rw [indexZ_neg,indexZ_nat,Fin.coe_neg,Fin.val_natCast,Nat.mod_eq_of_lt lt,Nat.mod_eq_of_lt cap]
  have a : perimeter m i j=armSize m i+armSize m j := rfl
  have p : 0 < armSize m i := by simp [armSize]
  unfold intPt cyclePt armPt
  simp only [val]
  split_ifs <;> first | rfl | (exfalso;omega) |
    (apply congrArg (inner m j); apply Fin.ext; dsimp; omega)

theorem intPt_period (m : Fin k → ℕ) (i j : Fin k) (x : ℤ) :
    intPt m i j (x+(perimeter m i j : ℤ))=intPt m i j x := by
  simp only [intPt,indexZ_add,indexZ_length,add_zero]

theorem false_reflect_int (m : Fin k → ℕ) {i j : Fin k} (ij : i≠j) (x : ℤ) :
    reflection m ij false (intPt m i j x)=intPt m i j (-x) := by
  unfold intPt
  rw [reflection_pt,indexZ_neg]
  apply congrArg (cyclePt m i j)
  change 0+0-_=_
  simp

theorem rotate_int (m : Fin k → ℕ) {i j : Fin k} (ij : i≠j) (x : ℤ) :
    (reflection m ij true * reflection m ij false) (intPt m i j x) =
      intPt m i j (x+2*(armSize m i : ℤ)) := by
  unfold intPt
  rw [rotation_pt,show x+2*(armSize m i:ℤ)=x+armSize m i+armSize m i by omega,indexZ_add,indexZ_add]
  have c : indexZ (perimeter m i j) (armSize m i:ℤ)=vertexCoord m i j (pole m true) := by
    apply Fin.ext
    rw [indexZ_nat,Fin.val_natCast,Nat.mod_eq_of_lt (by dsimp [perimeter,armSize]; omega)]
    rfl
  rw [c]

theorem third_of_ne {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t) (a : Fin 3)
    (ai : a≠i) (aj : a≠j) : a=t := by
  apply Fin.ext
  have neq {u v : Fin 3} (h : u≠v) : u.val≠v.val := fun e => h (Fin.ext e)
  have := neq ij; have := neq it; have := neq jt; have := neq ai; have := neq aj
  omega

end Bootstrap.Theta

#print axioms Bootstrap.Theta.intPt_second
#print axioms Bootstrap.Theta.rotate_int
