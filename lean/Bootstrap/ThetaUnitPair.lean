import Bootstrap.ThetaExternalSeeds
import Bootstrap.ThetaVertexOrbits
import Bootstrap.ThetaCoordinateModulo

namespace Bootstrap.Theta

open scoped Classical

theorem shift_pair (m : Fin 3 → ℕ) {i j : Fin 3} (ij : i≠j) (x y s : ℤ)
    (hs : ((2*armSize m i).gcd (perimeter m i j):ℤ) ∣ s) :
    (thetaClosure m).Adj (intPt m i j (x+s)) (intPt m i j (y+s)) ↔
      (thetaClosure m).Adj (intPt m i j x) (intPt m i j y) := by
  obtain ⟨p,hp,act,_⟩ := translation_of_dvd m ij hs
  rw [←act,←act]; exact preserves_of_mem m hp _ _

theorem one_difference (m : Fin 3 → ℕ) (i j : Fin 3) (z : ℤ) :
    (thetaClosure m).Adj (intPt m i j z) (intPt m i j (z+1)) := by
  apply initial_le_terminal (graph m) (graph m)
  apply adj_of_consecutive
  left
  rw [indexZ_add]
  have one : indexZ (perimeter m i j) 1=1 := by simp [indexZ]
  rw [one]

set_option maxHeartbeats 1200000 in
private theorem full_cycle (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    (order : armSize m i ≤ armSize m j) (unit : (2*armSize m i).gcd (perimeter m i j)=1)
    (x y : Fin (perimeter m i j)) (ne : x≠y) :
    (thetaClosure m).Adj (cyclePt m i j x) (cyclePt m i j y) := by
  let n := perimeter m i j
  have unitDiv (k : ℤ) : ((2*armSize m i).gcd (perimeter m i j):ℤ) ∣ k := by simp [unit]
  have small (d : ℕ) (pos : 0<d) (short : d≤armSize m j) :
      (thetaClosure m).Adj (intPt m i j 0) (intPt m i j (d:ℤ)) := by
    by_cases one : d=1
    · subst d; simpa using one_difference m i j 0
    let e := d-1
    have eSmall : e<armSize m j := by dsimp [e];omega
    have as := seed_multiple m ij it jt eSmall (unitDiv e)
    rw [←intPt_first m i j 1 (by dsimp [armSize];omega),←intPt_second m i j e eSmall.le] at as
    have raised := (shift_pair m ij 1 (-(e:ℤ)) (e:ℤ) (unitDiv _)).mpr as
    have fit : 1+(e:ℤ)=(d:ℤ) := by dsimp [e]; omega
    rw [fit,neg_add_cancel] at raised
    exact (thetaClosure m).symm raised
  have zeroTo (z : Fin n) (nz : z≠0) :
      (thetaClosure m).Adj (intPt m i j 0) (intPt m i j (z.val:ℤ)) := by
    have positive : 0<z.val := Nat.pos_of_ne_zero (fun h => nz (Fin.ext h))
    by_cases short : z.val≤armSize m j
    · exact small z.val positive short
    let d := n-z.val
    have dpos : 0<d := Nat.sub_pos_of_lt z.isLt
    have dshort : d≤armSize m j := by dsimp [d,n,perimeter]; omega
    have edge := (preserves_of_mem m (reflection_mem m ij false) _ _).mpr (small d dpos dshort)
    rw [false_reflect_int,false_reflect_int,neg_zero] at edge
    have rep : intPt m i j (-(d:ℤ))=intPt m i j (z.val:ℤ) := by
      have eq : -(d:ℤ)+(perimeter m i j:ℤ)=(z.val:ℤ) := by dsimp [d,n];have := z.isLt;omega
      rw [←eq,intPt_period]
    exact rep ▸ edge
  let d := y-x
  have nz : d≠0 := fun h => ne (sub_eq_zero.mp h).symm
  have base := zeroTo d nz
  have move := (shift_pair m ij 0 (d.val:ℤ) (x.val:ℤ) (unitDiv _)).mpr base
  have eq : indexZ (perimeter m i j) ((d.val:ℤ)+x.val)=y := by rw [indexZ_add,indexZ_val,indexZ_val];exact sub_add_cancel _ _
  simpa only [intPt,zero_add,indexZ_val,eq] using move

private theorem opposite_arm_universal (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    (order : armSize m i≤armSize m j) (unit : (2*armSize m i).gcd (perimeter m i j)=1) :
    ∀ z : ℤ, (thetaClosure m).Adj (armPt m j 1) (intPt m i t z) := by
  let adj (z : ℤ) := (thetaClosure m).Adj (armPt m j 1) (intPt m i t z)
  have off := first_off m ij.symm jt
  have even' (z : ℤ) : adj (-z)=adj z := by
    have eq := preserves_of_mem m (reflection_mem m it false) (armPt m j 1) (intPt m i t z)
    rw [reflection_off m it false off,false_reflect_int] at eq
    exact propext eq
  have repeat' (z : ℤ) : adj (z+2*(armSize m i:ℤ))=adj z := by
    let p := reflection m it true * reflection m it false
    have hp : p∈reflectionGroup m := (reflectionGroup m).mul_mem (reflection_mem m it true) (reflection_mem m it false)
    have eq := preserves_of_mem m hp (armPt m j 1) (intPt m i t z)
    change _ ↔ _ at eq
    have fix : p (armPt m j 1)=armPt m j 1 := by dsimp only [p]; rw [Equiv.Perm.mul_apply,reflection_off m it false off,reflection_off m it true off]
    rw [fix,show p (intPt m i t z)=_ from rotate_int m it z] at eq
    exact propext eq
  have mid (q : ℕ) (hq : q≤armSize m i) : adj (q:ℤ)=True := by
    apply propext; refine ⟨fun _ => trivial,fun _ => ?_⟩
    dsimp only [adj]
    rw [intPt_first m i t q hq,←intPt_first m i j q hq,←intPt_second m i j 1 (by dsimp [armSize];omega)]
    apply full_cycle m ij it jt order unit
    intro eq
    have small : q+1<perimeter m i j := by dsimp [perimeter,armSize] at *;omega
    have diff := (indexZ_eq_iff (n:=perimeter m i j) q (-(1:ℤ))).mp eq.symm
    have positive : 0<(q:ℤ)-(-1) := by omega
    have bound := Int.le_of_dvd positive diff
    omega
  have all := ThetaPeriodArithmetic.interval_determines (by dsimp [armSize];omega : 0<armSize m i)
    adj (fun _ => True) even' (fun _ => rfl) repeat' (fun _ => rfl) mid
  intro z
  exact (congrFun all z).mpr trivial

/-- A coprime pair of opposite parities makes the ordinary theta self-closure complete.
The exact numeric input is gcd(2a,a+b)=1 on the pair ordered by length. -/
theorem unit_pair_complete (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    (order : armSize m i≤armSize m j) (unit : (2*armSize m i).gcd (perimeter m i j)=1) :
    thetaClosure m = ⊤ := by
  have cross := opposite_arm_universal m ij it jt order unit
  have pole_all (v : Vertex m) (ne : pole m false ≠ v) : (thetaClosure m).Adj (pole m false) v := by
    by_cases on' : OnCycle i j v
    · have src : OnCycle i j (pole m false) := trivial
      have r₁ := pt_coord m ij (pole m false) src
      have r₂ := pt_coord m ij v on'
      have diff : vertexCoord m i j (pole m false) ≠ vertexCoord m i j v :=
        fun h => ne (r₁.symm.trans ((congrArg (cyclePt m i j) h).trans r₂))
      exact r₁ ▸ r₂ ▸ full_cycle m ij it jt order unit _ _ diff
    rcases v with b|⟨a,d⟩
    · exact False.elim (on' trivial)
    have third := third_of_ne ij it jt a (fun h => on' (Or.inl h)) (fun h => on' (Or.inr h))
    subst a
    have q := cross (-(d.val+1:ℕ):ℤ)
    have hl : d.val+1≤armSize m t := by have := d.isLt;dsimp [armSize];omega
    rw [intPt_second m i t (d.val+1) hl,armPt_inner] at q
    have one : ((2*armSize m i).gcd (perimeter m i j):ℤ) ∣ 1 := by simp [unit]
    obtain ⟨p,hp,act,fix⟩ := translation_of_dvd m ij one
    have as := (preserves_of_mem m hp _ _).mpr q
    have old : intPt m i j (-1)=armPt m j 1 := intPt_second m i j 1 (by dsimp [armSize];omega)
    rw [←old,act,show (-1:ℤ)+1=0 by decide,intPt_zero,fix (inner m t d) on'] at as
    exact as
  have gcd : Nat.gcd (2*armSize m i) (Nat.gcd (perimeter m i j) (perimeter m i t))=1 := by
    rw [←Nat.gcd_assoc,unit,Nat.gcd_one_left]
  apply top_unique
  intro x y xy
  obtain ⟨p,hp,atPole⟩ := transitive_when_one m ij it jt gcd (pole m false) x
  have neq : pole m false ≠ p⁻¹ y := by
    intro eq
    have eq' := congrArg p eq
    rw [atPole,Equiv.Perm.apply_inv_self] at eq'
    exact xy.ne eq'
  have e := (preserves_of_mem m hp _ _).mpr (pole_all _ neq)
  rwa [atPole,Equiv.Perm.apply_inv_self] at e

end Bootstrap.Theta

#print axioms Bootstrap.Theta.unit_pair_complete
