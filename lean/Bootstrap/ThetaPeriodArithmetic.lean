import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Periodic labels on the two cycles through a shared theta arm. -/
namespace Bootstrap.ThetaPeriodArithmetic

open Function

variable {L : Type*}

private theorem gcd_period {f : ℤ → L} {u v : ℕ}
    (pu : Periodic f (u : ℤ)) (pv : Periodic f (v : ℤ)) :
    Periodic f ((Nat.gcd u v : ℕ) : ℤ) := by
  rw [Nat.gcd_eq_gcd_ab u v]
  simpa only [Int.cast_id, mul_comm] using
    (pu.int_mul (Nat.gcdA u v)).add_period (pv.int_mul (Nat.gcdB u v))

private theorem value_of_dvd {f : ℤ → L} {p x y : ℤ}
    (per : Periodic f p) (h : p ∣ x-y) : f x = f y := by
  obtain ⟨k,hk⟩ := h
  have eq : x = y + k*p := by rw [Int.mul_comm p k] at hk; omega
  simpa only [eq] using per.int_mul k y

private theorem mod_value {f : ℤ → L} {p : ℤ} (per : Periodic f p) (z : ℤ) :
    f z = f (z % p) := by
  apply value_of_dvd per
  exact ⟨z / p,by have := Int.emod_add_ediv z p; omega⟩

/-- An even function of period 2a is fixed by its values at the integers from 0 to a. -/
theorem interval_determines {a : ℕ} (ha : 0 < a) (B C : ℤ → L)
    (negB : ∀ z, B (-z) = B z) (negC : ∀ z, C (-z) = C z)
    (twoB : Periodic B (2*(a:ℤ))) (twoC : Periodic C (2*(a:ℤ)))
    (agree : ∀ j : ℕ, j ≤ a → B (j:ℤ) = C (j:ℤ)) : B = C := by
  funext z
  let p := 2*(a:ℤ)
  let r := z % p
  have pos : 0 < p := by dsimp [p];omega
  have lo : 0 ≤ r := Int.emod_nonneg _ pos.ne'
  have hi : r < p := Int.emod_lt_of_pos _ pos
  have bridge (w : ℤ) (low : 0 ≤ w) (up : w ≤ (a:ℤ)) : B w = C w := by
    have eq := Int.toNat_of_nonneg low
    have a' : w.toNat ≤ a := by omega
    simpa only [eq] using agree w.toNat a'
  have br : B z = B r := mod_value twoB z
  have cr : C z = C r := mod_value twoC z
  rw [br,cr]
  by_cases small : r ≤ (a:ℤ)
  · exact bridge r lo small
  · have lo' : 0 ≤ p-r := by omega
    have hi' : p-r ≤ (a:ℤ) := by dsimp [p] at *;omega
    have reflectB : B (p-r) = B r := (twoB.sub_eq' (x := r)).trans (negB r)
    have reflectC : C (p-r) = C r := (twoC.sub_eq' (x := r)).trans (negC r)
    exact reflectB.symm.trans ((bridge _ lo' hi').trans reflectC)

/-- The common period is gcd(2a, a+b, a+c), and an integer and its negative carry the same label. -/
theorem glued_periods (a b c : ℕ) (ha : 0 < a) (B C : ℤ → L)
    (negB : ∀ z, B (-z) = B z) (negC : ∀ z, C (-z) = C z)
    (twoB : ∀ z, B (z+2*(a:ℤ)) = B z) (twoC : ∀ z, C (z+2*(a:ℤ)) = C z)
    (pB : ∀ z, B (z+(a:ℤ)+b) = B z) (pC : ∀ z, C (z+(a:ℤ)+c) = C z)
    (agree : ∀ j : ℕ, j ≤ a → B (j:ℤ) = C (j:ℤ)) :
    B = C ∧ ∀ x y : ℤ,
      (((Nat.gcd (2*a) (Nat.gcd (a+b) (a+c)) : ℕ) : ℤ) ∣ x-y ∨
       ((Nat.gcd (2*a) (Nat.gcd (a+b) (a+c)) : ℕ) : ℤ) ∣ x+y) → B x = B y := by
  have eq := interval_determines ha B C negB negC twoB twoC agree
  subst C
  have ab : Periodic B ((a+b:ℕ):ℤ) := by
    intro z; simpa only [Nat.cast_add,←Int.add_assoc] using pB z
  have ac : Periodic B ((a+c:ℕ):ℤ) := by
    intro z; simpa only [Nat.cast_add,←Int.add_assoc] using pC z
  have da : Periodic B ((2*a:ℕ):ℤ) := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using twoB
  have period := gcd_period da (gcd_period ab ac)
  refine ⟨rfl,?_⟩
  intro x y h
  rcases h with h | h
  · exact value_of_dvd period h
  · exact (value_of_dvd (x := x) (y := -y) period (by simpa using h)).trans (negB y)

/-- Any 2K+1 consecutive multiples of h meet every class modulo the coprime modulus g
when their number is at least g. Use the representatives centered at zero. -/
theorem centered_residues (h g K : ℕ) (hg : h.Coprime g) (gpos : 0 < g)
    (width : g ≤ 2*K+1) (z : ℤ) :
    ∃ k q : ℤ, -(K:ℤ) ≤ k ∧ k ≤ K ∧ z = k*h+q*g := by
  have one : (1:ℤ) = (h:ℤ)*Nat.gcdA h g + (g:ℤ)*Nat.gcdB h g := by
    simpa only [hg.gcd_eq_one,Nat.cast_one] using Nat.gcd_eq_gcd_ab h g
  let k₀ := z * Nat.gcdA h g
  let k := (k₀ + K) % (g:ℤ) - K
  let t := (k₀ + K) / (g:ℤ)
  have pg : 0 < (g:ℤ) := by omega
  have lo := Int.emod_nonneg (k₀+K) pg.ne'
  have hi := Int.emod_lt_of_pos (k₀+K) pg
  have split : k+(g:ℤ)*t = k₀ := by
    have := Int.emod_add_ediv (k₀+K) (g:ℤ)
    dsimp [k,t]
    omega
  have orig : z = k₀*(h:ℤ)+(z*Nat.gcdB h g)*(g:ℤ) := by
    calc
      z = z*1 := (mul_one z).symm
      _ = z*((h:ℤ)*Nat.gcdA h g+(g:ℤ)*Nat.gcdB h g) := congrArg (fun u : ℤ => z*u) one
      _ = _ := by dsimp [k₀]; ring
  refine ⟨k,z*Nat.gcdB h g+t*h,by dsimp [k]; omega,by dsimp [k];omega,?_⟩
  calc
    z = k₀*(h:ℤ)+(z*Nat.gcdB h g)*(g:ℤ) := orig
    _ = _ := by rw [←split]; ring

end Bootstrap.ThetaPeriodArithmetic

#print axioms Bootstrap.ThetaPeriodArithmetic.glued_periods
#print axioms Bootstrap.ThetaPeriodArithmetic.centered_residues
