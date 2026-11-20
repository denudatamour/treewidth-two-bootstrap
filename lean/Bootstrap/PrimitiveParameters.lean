import Bootstrap.Asymptotics

namespace Bootstrap.Theta.Contraction

/-- The exact shift sizes and the last interval for the contraction. -/
structure Parameters (a b c s t f : Nat) : Prop where
  small : 2 ≤ f
  last : ∃ K : Nat, 1 ≤ K ∧ a = K*s+f
  room : s ≤ c
  outside : f*t < b+c
  positive : 0 < t
  inside_rotation : (2*a).gcd (a+c) ∣ s
  outside_rotation : (2*b).gcd (b+c) ∣ t

private theorem rotation_double (a c : Nat) : (2*a).gcd (a+c) ∣ 2*(a.gcd c) := by
  let q := (2*a).gcd (a+c)
  have ha : q ∣ 2*a := Nat.gcd_dvd_left _ _
  have hs : q ∣ a+c := Nat.gcd_dvd_right _ _
  have hc : q ∣ 2*c := by
    have h := Nat.dvd_sub (dvd_mul_of_dvd_right hs 2) ha
    simpa only [show 2*(a+c)-2*a=2*c by omega] using h
  rw [←Nat.gcd_mul_left]
  exact Nat.dvd_gcd ha hc

private theorem rotation_single (a c : Nat) (par : a%2 ≠ c%2) :
    (2*a).gcd (a+c) ∣ a.gcd c := by
  let q := (2*a).gcd (a+c)
  have odd : q % 2 = 1 := by
    by_contra bad
    have dv : 2 ∣ q := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    have dv' := dv.trans (Nat.gcd_dvd_right (2*a) (a+c))
    have hz := Nat.dvd_iff_mod_eq_zero.mp dv'
    omega
  have cp : q.Coprime 2 := by
    change q.gcd 2 = 1
    rw [Nat.gcd_comm,Nat.gcd_rec 2 q,odd]
    decide
  exact cp.dvd_of_dvd_mul_left (rotation_double a c)

private theorem product_fits (a b c : Nat) (cpos : 0 < c) (prim : (a.gcd b).gcd c = 1) :
    a.gcd c * b.gcd c ≤ c := by
  let f := a.gcd c
  let g := b.gcd c
  have cop : f.Coprime g := by
    apply Nat.eq_one_of_dvd_one
    rw [←prim]
    have lf := Nat.gcd_dvd_left f g
    have rg := Nat.gcd_dvd_right f g
    exact Nat.dvd_gcd (Nat.dvd_gcd (lf.trans (Nat.gcd_dvd_left a c))
      (rg.trans (Nat.gcd_dvd_left b c))) (lf.trans (Nat.gcd_dvd_right a c))
  exact Nat.le_of_dvd cpos (cop.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right a c) (Nat.gcd_dvd_right b c))

private theorem ratio_two (a b c : Nat) (apos : 0 < a) (prim : (a.gcd b).gcd c = 1)
    (pair : 1 < a.gcd b) : 2 ≤ a / (a.gcd c) := by
  let f := a.gcd c
  let r := a/f
  have eq : r*f=a := Nat.div_mul_cancel (Nat.gcd_dvd_left a c)
  change 2 ≤ r
  have nz : r ≠ 0 := fun h => Nat.ne_of_gt apos (eq.symm.trans (by rw [h,Nat.zero_mul]))
  by_cases one : r = 1
  · have same : f=a := by simpa only [one,Nat.one_mul] using eq
    have ac : a ∣ c := same ▸ (Nat.gcd_dvd_right a c)
    have g1 := Nat.dvd_gcd (dvd_refl (a.gcd b)) ((Nat.gcd_dvd_left a b).trans ac)
    rw [prim] at g1
    have := Nat.eq_one_of_dvd_one g1
    omega
  · exact lt_of_le_of_ne (Nat.pos_of_ne_zero nz) (Ne.symm one)

theorem mixed_parameters (a b c : Nat) (apos : 0 < a) (bpos : 0 < b) (cpos : 0 < c)
    (prim : (a.gcd b).gcd c = 1) (bad : 1 < a.gcd b) (bigF : 2 ≤ a.gcd c)
    (pa : a%2 ≠ c%2) (pb : b%2 ≠ c%2) :
    Parameters a b c (a.gcd c) (b.gcd c) (a.gcd c) := by
  let f := a.gcd c
  let r := a/f
  have r₂ : 2 ≤ r := ratio_two a b c apos prim bad
  have rf : r*f = a := Nat.div_mul_cancel (Nat.gcd_dvd_left a c)
  refine ⟨bigF,⟨r-1,by omega,?_⟩,Nat.le_of_dvd cpos (Nat.gcd_dvd_right a c),?_,
    Nat.gcd_pos_of_pos_left _ bpos,rotation_single _ _ pa,rotation_single _ _ pb⟩
  · change a = (r-1)*f+f
    calc
      a = ((r-1)+1)*f := by rw [show r-1+1=r by omega,rf]
      _ = _ := by rw [Nat.add_mul,Nat.one_mul]
  · have := product_fits a b c cpos prim
    omega

theorem odd_parameters (a b c : Nat) (apos : 0 < a) (bpos : 0 < b) (cpos : 0 < c)
    (order : c < b) (prim : (a.gcd b).gcd c = 1) (bad : 1 < a.gcd b)
    (bigF : 2 ≤ a.gcd c) (bigG : 2 ≤ b.gcd c) (odd : a%2 = 1) :
    Parameters a b c (2*(a.gcd c)) (2*(b.gcd c)) (a.gcd c) := by
  let f := a.gcd c
  let g := b.gcd c
  let r := a/f
  have r₂ := ratio_two a b c apos prim bad
  change 2 ≤ r at r₂
  have rf : r*f = a := Nat.div_mul_cancel (Nat.gcd_dvd_left a c)
  have ro : r%2 = 1 := by
    by_contra bad
    have zero : r%2=0 := by omega
    have v := congrArg (fun q : Nat => q%2) rf
    change (r*f)%2 = a%2 at v
    rw [Nat.mul_mod,zero,Nat.zero_mul,odd] at v
    omega
  have fits : f*g ≤ c := product_fits a b c cpos prim
  have room : 2*f ≤ c := (Nat.mul_comm 2 f).le.trans ((Nat.mul_le_mul_left f bigG).trans fits)
  refine ⟨bigF,⟨r/2,by omega,?_⟩,room,?_,Nat.mul_pos (by decide) (Nat.gcd_pos_of_pos_left _ bpos),
    rotation_double _ _,rotation_double _ _⟩
  · change a = (r/2)*(2*f)+f
    calc
      a = ((r/2)*2+1)*f := by rw [show (r/2)*2+1=r by omega,rf]
      _ = _ := by rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc]
  · change f*(2*g) < b+c
    have eq : f*(2*g) = 2*(f*g) := Nat.mul_left_comm f 2 g
    rw [eq]
    omega

end Bootstrap.Theta.Contraction

#print axioms Bootstrap.Theta.Contraction.mixed_parameters
#print axioms Bootstrap.Theta.Contraction.odd_parameters
