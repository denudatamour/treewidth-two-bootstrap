import Bootstrap.Padding
import Mathlib.Data.Nat.GCD.Basic

/-! The all-orders and asymptotic deductions at the end of Theorem III.1. -/
namespace Bootstrap

variable {W : Type*}

def HasLinearUpper (H : SimpleGraph W) : Prop :=
  ∃ C n₀ : ℕ, ∀ n, n₀ ≤ n → maxTime H n ≤ C * n

/-- Integer constants express the usual positive real quadratic order on natural sizes. -/
def HasQuadraticOrder (H : SimpleGraph W) : Prop :=
  (∃ A n₀ : ℕ, 0 < A ∧ ∀ n, n₀ ≤ n → n*n ≤ A * maxTime H n) ∧
    (∃ B n₀ : ℕ, 0 < B ∧ ∀ n, n₀ ≤ n → maxTime H n ≤ B * (n*n))

def familyOrder (k : ℕ) := 69360 * (2*k + 1)
def familyTime (k : ℕ) := k * (k+1) / 2

theorem consecutive_period (k : ℕ) : k.lcm (k+1) / 2 = familyTime k := by
  have cop : k.Coprime (k+1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  rw [cop.lcm_eq_mul]
  rfl

theorem maxTime_le_square (H : SimpleGraph W) (n : ℕ) : maxTime H n ≤ n*n := by
  calc
    maxTime H n ≤ n.choose 2 := maxTime_le_choose H n
    _ = _ := Nat.choose_two_right n
    _ ≤ n*(n-1) := Nat.div_le_self _ _
    _ ≤ n*n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/-- Once the ordinary hosts at consecutive cycle lengths are known, padding supplies all large orders. -/
theorem quadratic_of_family (H : SimpleGraph W) (hdeg : HasTwoNeighbours H)
    (hosts : ∀ k, 3 ≤ k → ∃ G : SimpleGraph (Fin (familyOrder k)),
      familyTime k ≤ stabilizationTime H G) : HasQuadraticOrder H := by
  refine ⟨⟨(277440*277440)*2,624240,by decide,?_⟩,
    ⟨1,0,by decide,fun n _ => by simpa using maxTime_le_square H n⟩⟩
  intro n hn
  let k := (n/69360 - 1)/2
  have kmin : 3 ≤ k := by dsimp [k]; omega
  have hlen : familyOrder k ≤ n := by dsimp [familyOrder,k]; omega
  have hsize : n ≤ 277440*k := by dsimp [k]; omega
  obtain ⟨G,hG⟩ := hosts k kmin
  have pad := le_maxTime_of_padding H hdeg G (n - familyOrder k)
  rw [Fintype.card_fin, Nat.add_sub_of_le hlen] at pad
  have hpoly : k*k + k = k*(k+1) := by simp [Nat.mul_add]
  have htime : k*k ≤ 2 * familyTime k := by unfold familyTime; omega
  calc
    n*n ≤ (277440*k)*(277440*k) := Nat.mul_le_mul hsize hsize
    _ = (277440*277440)*(k*k) := by ac_rfl
    _ ≤ (277440*277440)*(2*familyTime k) := Nat.mul_le_mul_left _ htime
    _ = ((277440*277440)*2)*familyTime k := by ac_rfl
    _ ≤ ((277440*277440)*2)*maxTime H n := Nat.mul_le_mul_left _ (hG.trans pad)

theorem quadratic_excludes_linear (H : SimpleGraph W) (hq : HasQuadraticOrder H) :
    ¬ HasLinearUpper H := by
  obtain ⟨⟨A,n₀,_,hA⟩,_⟩ := hq
  rintro ⟨C,n₁,hC⟩
  let n := A*C + n₀ + n₁ + 1
  have hn : 0 < n := by dsimp [n]; omega
  have ha := hA n (by dsimp [n]; omega)
  have hu := hC n (by dsimp [n]; omega)
  have hbound : n*n ≤ (A*C)*n := by
    calc
      n*n ≤ A * maxTime H n := ha
      _ ≤ A * (C*n) := Nat.mul_le_mul_left _ hu
      _ = (A*C)*n := (Nat.mul_assoc _ _ _).symm
  have hlt := Nat.mul_lt_mul_of_pos_right (show A*C < n by dsimp [n]; omega) hn
  exact (Nat.not_lt_of_ge hbound) hlt

end Bootstrap

#print axioms Bootstrap.consecutive_period
#print axioms Bootstrap.quadratic_of_family
#print axioms Bootstrap.quadratic_excludes_linear
