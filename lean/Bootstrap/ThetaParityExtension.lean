import Bootstrap.ThetaParityCycle
import Bootstrap.ThetaPeriodArithmetic

namespace Bootstrap.Theta

open scoped Classical

theorem indexZ_parity {n : ℕ} [NeZero n] (even' : n%2=0) (z : ℤ) :
    ((indexZ n z).val:ℤ)%2=z%2 := by
  have dv := (indexZ_eq_iff (n:=n) (indexZ n z).val z).mp (indexZ_val n _)
  have two : (2:ℤ)∣(n:ℤ) := ⟨(n/2:ℕ),by omega⟩
  obtain ⟨q,eq⟩ := two.trans dv
  omega

theorem cycle_parity_int (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    (order : armSize m i≤armSize m j) (two : (2*armSize m i).gcd (perimeter m i j)=2)
    (even' : perimeter m i j%2=0) {x y : ℤ} (diff : x%2≠y%2) :
    (thetaClosure m).Adj (intPt m i j x) (intPt m i j y) := by
  apply cycle_between_parities m ij it jt order two even'
  have x' := indexZ_parity even' x
  have y' := indexZ_parity even' y
  omega

/-- Either an odd modulus allows both parities in a short signed interval,
or an even modulus preserves the prescribed parity there. -/
private theorem signed_interval (a g col : ℕ) (z : ℤ) (pos : 0<g) (colb : col<2)
    (enough : (g%2=1 ∧ g≤a) ∨ (g%2=0 ∧ g≤2*a ∧ z%2=col)) :
    ∃ w : ℤ, -(a:ℤ)≤w ∧ w≤a ∧ w%2=col ∧ (g:ℤ)∣z-w := by
  let r := z%(g:ℤ)
  have lo : 0≤r := Int.emod_nonneg _ (by omega)
  have hi : r<g := Int.emod_lt_of_pos _ (by omega)
  have div : (g:ℤ)∣z-r := ⟨z/g,by have := Int.emod_add_ediv z g;dsimp [r];omega⟩
  have div' : (g:ℤ)∣z-(r-g) := by
    obtain ⟨q,hq⟩ := div
    exact ⟨q+1,by rw [Int.mul_add,Int.mul_one];omega⟩
  rcases enough with ⟨odd,small⟩|⟨even',small,colz⟩
  · by_cases ok : r%2=col
    · exact ⟨r,by omega,by omega,ok,div⟩
    · exact ⟨r-g,by omega,by omega,by omega,div'⟩
  · have two : (2:ℤ)∣(g:ℤ) := ⟨(g/2:ℕ),by omega⟩
    obtain ⟨q,eq⟩ := two.trans div
    by_cases small' : r≤a
    · exact ⟨r,by omega,small',by omega,div⟩
    · exact ⟨r-g,by omega,by omega,by omega,div'⟩

theorem opposite_interval (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    (order : armSize m i≤armSize m j) (two : (2*armSize m i).gcd (perimeter m i j)=2)
    (even' : perimeter m i j%2=0) (d : Fin (m j+1)) (z : ℤ)
    (enough : let g := (2*armSize m i).gcd (perimeter m i t)
              (g%2=1 ∧ g≤armSize m i) ∨ (g%2=0 ∧ g≤2*armSize m i ∧ z%2≠((d.val+1:ℕ):ℤ)%2)) :
    (thetaClosure m).Adj (inner m j d) (intPt m i t z) := by
  let g := (2*armSize m i).gcd (perimeter m i t)
  let col := 1-(d.val+1)%2
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ (by dsimp [armSize];omega)
  have cb : col<2 := by dsimp [col];omega
  have need : (g%2=1 ∧ g≤armSize m i) ∨ (g%2=0 ∧ g≤2*armSize m i ∧ z%2=col) := by
    rcases enough with h|⟨he,hs,diff⟩
    · exact Or.inl h
    · exact Or.inr ⟨he,hs,by dsimp [col];omega⟩
  obtain ⟨w,lo,hi,colour,div⟩ := signed_interval (armSize m i) g col z gp cb need
  have off : ¬OnCycle i t (inner m j d) := fun h => h.elim ij.symm jt
  have atNat (q : ℕ) (small : q≤armSize m i) (par : q%2=col) :
      (thetaClosure m).Adj (inner m j d) (intPt m i t (q:ℤ)) := by
    have room : d.val+1≤armSize m j := by have := d.isLt; dsimp [armSize];omega
    have diff : (-((d.val+1:ℕ):ℤ))%2 ≠ (q:ℤ)%2 := by dsimp [col] at *;omega
    have h := cycle_parity_int m ij it jt order two even' diff
    rwa [intPt_second m i j (d.val+1) room,armPt_inner,intPt_first m i j q small,
      ←intPt_first m i t q small] at h
  have hit : (thetaClosure m).Adj (inner m j d) (intPt m i t w) := by
    by_cases wp : 0≤w
    · have eq := Int.toNat_of_nonneg wp
      exact eq ▸ atNat w.toNat (by omega) (by omega)
    · have eq : ((-w).toNat:ℤ) = -w := Int.toNat_of_nonneg (by omega)
      have h := atNat (-w).toNat (by omega) (by omega)
      rw [eq] at h
      have dst := (preserves_of_mem m (reflection_mem m it false) _ _).mpr h
      rwa [reflection_off m it false off,false_reflect_int,neg_neg] at dst
  obtain ⟨p,hp,act,fix⟩ := translation_of_dvd m it div
  have move := (preserves_of_mem m hp _ _).mpr hit
  rwa [fix (inner m j d) off,act,show w+(z-w)=z by omega] at move

end Bootstrap.Theta

#print axioms Bootstrap.Theta.opposite_interval
