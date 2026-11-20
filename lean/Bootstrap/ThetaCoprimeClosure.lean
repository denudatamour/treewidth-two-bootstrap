import Bootstrap.ThetaSeedArithmetic
import Bootstrap.ThetaParityExtension
import Bootstrap.ThetaUnitPair
import Bootstrap.ThetaLabelInvariance

namespace Bootstrap.Theta

open scoped Classical

private theorem pair_dvd_two (a b : ℕ) (cop : a.Coprime b) : (2*a).gcd (a+b) ∣ 2 := by
  simpa [cop.gcd_eq_one] using ThetaPeriodArithmetic.two_gcd_multiple a b

theorem coprime_opposite_complete (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    (order : armSize m i≤armSize m j) (cop : (armSize m i).Coprime (armSize m j))
    (opp : armSize m i%2 ≠ armSize m j%2) : thetaClosure m=⊤ := by
  apply unit_pair_complete m ij it jt order
  let a := armSize m i
  let b := armSize m j
  change (2*a).gcd (a+b)=1
  have dvd := pair_dvd_two a b cop
  have one_or_two := (Nat.dvd_prime Nat.prime_two).mp dvd
  rcases one_or_two with h|h
  · exact h
  · have ev := Nat.gcd_dvd_right (2*a) (a+b)
    rw [h] at ev
    change a%2≠b%2 at opp
    omega

theorem pair_eq_two (a b : ℕ) (cop : a.Coprime b) (oa : a%2=1) (ob : b%2=1) :
    (2*a).gcd (a+b)=2 := by
  apply Nat.dvd_antisymm (pair_dvd_two a b cop)
  exact Nat.dvd_gcd (dvd_mul_right _ _) (by omega)

theorem outside_to_pole (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    (two : (2*armSize m i).gcd (perimeter m i j)=2) (d : Fin (m t+1))
    (e : (thetaClosure m).Adj (armPt m j 2) (inner m t d)) :
    (thetaClosure m).Adj (pole m false) (inner m t d) := by
  obtain ⟨p,hp,act,fix⟩ := translation_of_dvd m ij
    (show ((2*armSize m i).gcd (perimeter m i j):ℤ)∣2 by simp [two])
  have r := (preserves_of_mem m hp _ _).mpr e
  have rep : intPt m i j (-2)=armPt m j 2 := intPt_second m i j 2 (by dsimp [armSize];omega)
  rw [←rep,act,neg_add_cancel,intPt_zero,fix (inner m t d) (fun h => h.elim it.symm jt.symm)] at r
  exact r

theorem right_even_depth (m : Fin 3 → ℕ) {j : Fin 3} (ob : armSize m j%2=1) :
    ∃ w : Fin (m j+1), w.val=1 ∧ armPt m j 2=inner m j w := by
  have len : 1 < m j+1 := by dsimp [armSize] at ob;omega
  exact ⟨⟨1,len⟩,rfl,armPt_inner m j ⟨1,len⟩⟩

private theorem complete_of_universal (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    (g : (2*armSize m i).gcd ((perimeter m i j).gcd (perimeter m i t))=1)
    (U : ∀v,pole m false≠v → (thetaClosure m).Adj (pole m false) v) : thetaClosure m=⊤ := by
  apply top_unique
  intro x y xy
  obtain ⟨p,hp,atPole⟩ := transitive_when_one m ij it jt g (pole m false) x
  have ne : pole m false≠p⁻¹ y := by
    intro e
    have h := congrArg p e
    rw [atPole,Equiv.Perm.apply_inv_self] at h
    exact xy.ne h
  have h := (preserves_of_mem m hp _ _).mpr (U _ ne)
  rwa [atPole,Equiv.Perm.apply_inv_self] at h

/-- A full-closure neighbour across every parity on the long arm gives every even
difference on its two-arm cycle. The even representatives are chosen on opposite arms. -/
private theorem pole_cycle_mixed (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    (ord : armSize m i≤armSize m j) (two : (2*armSize m i).gcd (perimeter m i j)=2)
    (oa : armSize m i%2=1) (ob : armSize m j%2=1)
    (cross : ∀w : Fin (m j+1),∀ z:ℤ,(thetaClosure m).Adj (inner m j w) (intPt m i t z))
    (z : Fin (perimeter m i j)) (nz : 0<z.val) :
    (thetaClosure m).Adj (pole m false) (cyclePt m i j z) := by
  let a := armSize m i
  let b := armSize m j
  let L := perimeter m i j
  have len : L=a+b := rfl
  have apos : 2≤a := by dsimp [a,armSize];omega
  have bpos : 2≤b := by dsimp [b,armSize];omega
  change a%2=1 at oa
  change b%2=1 at ob
  have bound : z.val<L := z.isLt
  have even' : perimeter m i j%2=0 := by change L%2=0;omega
  rw [←intPt_zero m i j,show cyclePt m i j z=intPt m i j (z.val:ℤ) from (congrArg (cyclePt m i j) (indexZ_val _ z)).symm]
  by_cases od : z.val%2=1
  · exact cycle_parity_int m ij it jt ord two even' (by omega)
  let k := max z.val (a+1)
  let c := k-z.val
  let e := L-k
  have ks : a<k ∧ k<L ∧ k%2=0 ∧ z.val≤k ∧ c≤a ∧ c%2=0 ∧ 0<e ∧ e<b := by
    dsimp [k,c,e]
    rcases le_total z.val (a+1) with h|h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  let w : Fin (m j+1) := ⟨e-1,by have : b=m j+2 := rfl; omega⟩
  have ew : w.val+1=e := by dsimp [w];omega
  have hit := cross w (c:ℤ)
  rw [←armPt_inner m j w,ew,←intPt_second m i j e ks.2.2.2.2.2.2.2.le,
    intPt_first m i t c ks.2.2.2.2.1,←intPt_first m i j c ks.2.2.2.2.1] at hit
  have coord : intPt m i j (-(e:ℤ))=intPt m i j (k:ℤ) := by
    have eq : -(e:ℤ)+(perimeter m i j:ℤ)=(k:ℤ) := by dsimp [e];change -(↑(L-k):ℤ)+ ↑L=↑k;omega
    rw [←eq,intPt_period]
  rw [coord] at hit
  have div : ((2*armSize m i).gcd (perimeter m i j):ℤ)∣-(c:ℤ) := by rw [two]; exact ⟨-((c/2:ℕ):ℤ),by omega⟩
  have moved := (shift_pair m ij (c:ℤ) (k:ℤ) (-(c:ℤ)) div).mpr ((thetaClosure m).symm hit)
  have diff : (k:ℤ)+ -(c:ℤ)=(z.val:ℤ) := by dsimp [c];omega
  rwa [add_neg_cancel,diff] at moved

theorem coprime_odd_complete (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    (ord : armSize m i≤armSize m j) (cop : (armSize m i).Coprime (armSize m j))
    (oa : armSize m i%2=1) (ob : armSize m j%2=1) (ec : armSize m t%2=0) : thetaClosure m=⊤ := by
  have two := pair_eq_two _ _ cop oa ob
  change (2*armSize m i).gcd (perimeter m i j)=2 at two
  have eper : perimeter m i j%2=0 := by dsimp [perimeter];omega
  have oper : Odd (perimeter m i t) := Nat.odd_iff.mpr (by dsimp [perimeter];omega)
  let g := (2*armSize m i).gcd (perimeter m i t)
  have gc : g.Coprime 2 := Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) oper.coprime_two_right
  have gd : g ∣ armSize m i := gc.dvd_of_dvd_mul_left (Nat.gcd_dvd_left _ _)
  have gs : g≤armSize m i := Nat.le_of_dvd (by dsimp [armSize];omega) gd
  have cross (w : Fin (m j+1)) (z : ℤ) := opposite_interval m ij it jt ord two eper w z
    (Or.inl ⟨Nat.odd_iff.mp (Nat.coprime_two_right.mp gc),gs⟩)
  apply complete_of_universal m ij it jt (by rw [←Nat.gcd_assoc,two]; exact oper.coprime_two_left.gcd_eq_one)
  intro v ne
  by_cases on' : OnCycle i j v
  · let z := vertexCoord m i j v
    have rep : cyclePt m i j z=v := pt_coord m ij v on'
    refine rep ▸ pole_cycle_mixed m ij it jt ord two oa ob cross z ?_
    by_contra! hz
    have eq : z=0 := Fin.ext (by simpa only [Fin.val_zero] using (show z.val = 0 by omega))
    have zero : cyclePt m i j 0=pole m false := (show intPt m i j 0=pole m false from intPt_zero m i j)
    exact ne (zero.symm.trans (eq ▸ rep))
  rcases v with pole'|⟨u,w⟩
  · exact False.elim (on' trivial)
  have third := third_of_ne ij it jt u (fun h => on' (Or.inl h)) (fun h => on' (Or.inr h))
  subst u
  obtain ⟨z,hz,pt⟩ := right_even_depth m ob
  apply outside_to_pole m ij it jt two w
  have hit := cross z (-((w.val+1:ℕ):ℤ))
  rw [intPt_second m i t _ (by have := w.isLt;dsimp [armSize];omega),armPt_inner] at hit
  rw [pt]; exact hit

end Bootstrap.Theta

#print axioms Bootstrap.Theta.coprime_opposite_complete
#print axioms Bootstrap.Theta.coprime_odd_complete
