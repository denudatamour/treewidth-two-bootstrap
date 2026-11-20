import Bootstrap.ThetaPeriodArithmetic
import Mathlib.Data.Nat.Prime.Basic

namespace Bootstrap.ThetaPeriodArithmetic

/-- Both rotations on a cycle through arms u,v generate a period which divides 2 gcd(u,v). -/
theorem two_gcd_multiple (u v : ℕ) : (2*u).gcd (u+v) ∣ 2*(u.gcd v) := by
  let f := (2*u).gcd (u+v)
  have a : f ∣ 2*u := Nat.gcd_dvd_left _ _
  have ab : f ∣ u+v := Nat.gcd_dvd_right _ _
  have both := Nat.dvd_sub (ab.mul_left 2) a
  have b : f ∣ 2*v := by simpa only [Nat.mul_add,Nat.add_sub_cancel_left] using both
  simpa only [Nat.gcd_mul_left] using Nat.dvd_gcd a b

private theorem odd_divisor {u v : ℕ} (hu : u ∣ v) (h : Odd v) : Odd u :=
  Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_left hu h.coprime_two_right)

/-- Use the natural magnitude of a signed representative; its sign selects the rotation or reflection. -/
private theorem extract_seed {u v h g b K : ℕ} {z k q : ℤ}
    (up : u ∣ h) (vp : v ∣ g) (small : h*K < b) (lo : -(K:ℤ) ≤ k) (hi : k ≤ K)
    (rep : z=k*h+q*g) :
    ∃ d : ℕ, d < b ∧ (u:ℤ) ∣ (d:ℤ) ∧ ((v:ℤ) ∣ z-d ∨ (v:ℤ) ∣ z+d) := by
  have hk : k.natAbs ≤ K := by cases k <;> simp_all <;> omega
  let d := h*k.natAbs
  have h₁ : d < b := (Nat.mul_le_mul_left h hk).trans_lt small
  have h₂ : (u:ℤ) ∣ (d:ℤ) := Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_left up _)
  have rem : (v:ℤ) ∣ q*(g:ℤ) := dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr vp) q
  refine ⟨d,h₁,h₂,?_⟩
  cases k with
  | ofNat j =>
    left
    have ds : (d:ℤ) = (j:ℤ)*h := by dsimp [d];simp [mul_comm]
    rw [ds,rep]; simpa using rem
  | negSucc j =>
    right
    have ds : (d:ℤ) = ((j:ℤ)+1)*h := by dsimp [d];simp [mul_comm]
    have zh : z = -(((j:ℤ)+1)*h)+q*g := by
      rw [rep]
      change (-((j:ℤ)+1))*(h:ℤ)+q*g = _
      ring
    rw [ds,zh]; simpa using rem

/-- The grid of multiples coming from the first pair of reflections meets every required
orbit of the second pair. Odd perimeter admits every z; even target coordinates also suffice. -/
theorem primitive_seed_residues (a b c : ℕ) (hb : 0 < b) (primitive : a.Coprime (b.gcd c))
    (oddg : Odd (b.gcd c)) (z : ℤ) (admissible : Odd (b+c) ∨ (2:ℤ) ∣ z) :
    ∃ d : ℕ, d < b ∧ ((2*a).gcd (a+b):ℤ) ∣ (d:ℤ) ∧
      (((2*b).gcd (b+c):ℤ) ∣ z-d ∨ ((2*b).gcd (b+c):ℤ) ∣ z+d) := by
  let e := a.gcd b
  let g := b.gcd c
  let K := (g-1)/2
  let t := (2*b).gcd (b+c)
  have he : 0 < e := Nat.gcd_pos_of_pos_right a hb
  have hg : 0 < g := Nat.gcd_pos_of_pos_left c hb
  have cop : e.Coprime g := Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left a b) primitive
  have prod : e*g ≤ b := Nat.le_of_dvd hb
    (cop.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right a b) (Nat.gcd_dvd_left b c))
  have godd : g%2=1 := Nat.odd_iff.mp oddg
  have wid : g ≤ 2*K+1 := by dsimp [K];omega
  have small : (2*e)*K < b := by
    calc
      (2*e)*K = e*(2*K) := by ac_rfl
      _ < e*g := Nat.mul_lt_mul_of_pos_left (by dsimp [K];omega) he
      _ ≤ b := prod
  rcases admissible with mixed | ⟨w,zw⟩
  · have tc : t.Coprime 2 := (odd_divisor (Nat.gcd_dvd_right (2*b) (b+c)) mixed).coprime_two_right
    have tg : t ∣ g := tc.dvd_of_dvd_mul_left (two_gcd_multiple b c)
    obtain ⟨k,q,lo,hi,rep⟩ := centered_residues (2*e) g K
      (Nat.coprime_mul_iff_left.mpr ⟨oddg.coprime_two_left,cop⟩) hg wid z
    exact extract_seed (two_gcd_multiple a b) tg small lo hi rep
  · obtain ⟨k,q,lo,hi,rep⟩ := centered_residues e g K cop hg wid w
    apply extract_seed (k := k) (q := q) (two_gcd_multiple a b) (two_gcd_multiple b c) small lo hi
    rw [zw,rep]
    push_cast
    ring

theorem mixed_seed_residues (a b c : ℕ) (hb : 0 < b) (primitive : a.Coprime (b.gcd c))
    (mixed : (b+c)%2=1) (z : ℤ) :
    ∃ d : ℕ, d < b ∧ ((2*a).gcd (a+b):ℤ) ∣ (d:ℤ) ∧
      (((2*b).gcd (b+c):ℤ) ∣ z-d ∨ ((2*b).gcd (b+c):ℤ) ∣ z+d) := by
  have odd := Nat.odd_iff.mpr mixed
  exact primitive_seed_residues a b c hb primitive
    (odd_divisor (dvd_add (Nat.gcd_dvd_left b c) (Nat.gcd_dvd_right b c)) odd) z (Or.inl odd)

theorem odd_seed_residues (a b c : ℕ) (hb : 0 < b) (primitive : a.Coprime (b.gcd c))
    (odd : b%2=1) (z : ℤ) (even : (2:ℤ) ∣ z) :
    ∃ d : ℕ, d < b ∧ ((2*a).gcd (a+b):ℤ) ∣ (d:ℤ) ∧
      (((2*b).gcd (b+c):ℤ) ∣ z-d ∨ ((2*b).gcd (b+c):ℤ) ∣ z+d) :=
  primitive_seed_residues a b c hb primitive (odd_divisor (Nat.gcd_dvd_left b c)
    (Nat.odd_iff.mpr odd)) z (Or.inr even)

end Bootstrap.ThetaPeriodArithmetic

#print axioms Bootstrap.ThetaPeriodArithmetic.mixed_seed_residues
#print axioms Bootstrap.ThetaPeriodArithmetic.odd_seed_residues
