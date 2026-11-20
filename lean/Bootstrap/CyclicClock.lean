import Std

namespace Bootstrap.CyclicClock

variable {X : Type u}

/-- Simultaneous expansion by both unit shifts, retaining the old set. -/
def step (forward backward : X → X) (E : X → Prop) (x : X) : Prop :=
  E x ∨ (∃ y, E y ∧ forward y = x) ∨ (∃ y, E y ∧ backward y = x)

def run (forward backward : X → X) (seed : X) : Nat → X → Prop
  | 0 => fun x => seed = x
  | t + 1 => step forward backward (run forward backward seed t)

theorem run_iff_interval (k : Int → X) (forward backward : X → X)
    (hf : ∀ i, forward (k i) = k (i + 1))
    (hb : ∀ i, backward (k i) = k (i - 1)) (t : Nat) (x : X) :
    run forward backward (k 0) t x ↔
      ∃ i : Int, -(t : Int) ≤ i ∧ i ≤ (t : Int) ∧ k i = x := by
  induction t generalizing x with
  | zero =>
    change (k 0 = x) ↔ _
    constructor
    · intro hx
      exact ⟨0, by omega, by omega, hx⟩
    · rintro ⟨i, hl, hu, hi⟩
      have hz : i = 0 := by omega
      simpa [hz] using hi
  | succ t ih =>
    change (run forward backward (k 0) t x ∨
      (∃ y, run forward backward (k 0) t y ∧ forward y = x) ∨
      (∃ y, run forward backward (k 0) t y ∧ backward y = x)) ↔ _
    constructor
    · rintro (h | ⟨y, h, hxy⟩ | ⟨y, h, hxy⟩)
      · obtain ⟨i, hl, hu, hi⟩ := (ih x).mp h
        exact ⟨i, by omega, by omega, hi⟩
      · obtain ⟨i, hl, hu, rfl⟩ := (ih y).mp h
        exact ⟨i + 1, by omega, by omega, (hf i).symm.trans hxy⟩
      · obtain ⟨i, hl, hu, rfl⟩ := (ih y).mp h
        exact ⟨i - 1, by omega, by omega, (hb i).symm.trans hxy⟩
    · rintro ⟨i, hl, hu, hi⟩
      by_cases hpos : (t : Int) < i
      · right; left
        refine ⟨k (i - 1), (ih _).mpr ⟨i - 1, by omega, by omega, rfl⟩, ?_⟩
        rw [hf, show i - 1 + 1 = i by omega, hi]
      · by_cases hneg : i < -(t : Int)
        · right; right
          refine ⟨k (i + 1), (ih _).mpr ⟨i + 1, by omega, by omega, rfl⟩, ?_⟩
          rw [hb, show i + 1 - 1 = i by omega, hi]
        · left
          exact (ih _).mpr ⟨i, by omega, by omega, hi⟩

def period (k : Int → X) (d : Nat) : Prop :=
  ∀ i j : Int, k i = k j ↔ i % (d : Int) = j % (d : Int)

private theorem centeredRepresentative {d t : Nat} (hd : 0 < d) (ht : d / 2 ≤ t) (i : Int) :
    ∃ j : Int, -(t : Int) ≤ j ∧ j ≤ (t : Int) ∧ j % (d : Int) = i % (d : Int) := by
  have hp : 0 < (d : Int) := by omega
  have hlo := Int.emod_nonneg i (show (d : Int) ≠ 0 by omega)
  have hhi := Int.emod_lt_of_pos i hp
  by_cases h : i % (d : Int) ≤ (t : Int)
  · exact ⟨i % (d : Int), by omega, h, Int.emod_emod _ _⟩
  · refine ⟨i % (d : Int) - (d : Int), by omega, by omega, ?_⟩
    rw [Int.emod_sub_emod, Int.emod_sub_cancel]

theorem run_iff_orbit_of_half_le (k : Int → X) (forward backward : X → X)
    (hf : ∀ i, forward (k i) = k (i + 1))
    (hb : ∀ i, backward (k i) = k (i - 1))
    {d : Nat} (hd : 0 < d) (hk : period k d) {t : Nat} (ht : d / 2 ≤ t) (x : X) :
    run forward backward (k 0) t x ↔ ∃ i : Int, k i = x := by
  rw [run_iff_interval k forward backward hf hb t x]
  constructor
  · rintro ⟨i, _, _, hi⟩
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, hl, hu, hj⟩ := centeredRepresentative hd ht i
    exact ⟨j, hl, hu, ((hk j i).mpr hj).trans hi⟩

private theorem rem_eq_iff_dvd (i j m : Int) :
    i % m = j % m ↔ m ∣ i - j :=
  Int.emod_eq_emod_iff_emod_sub_eq_zero.trans Int.dvd_iff_emod_eq_zero.symm

theorem run_fixed_iff (k : Int → X) (forward backward : X → X)
    (hf : ∀ i, forward (k i) = k (i + 1))
    (hb : ∀ i, backward (k i) = k (i - 1))
    {d : Nat} (hd : 0 < d) (hk : period k d) (t : Nat) :
    run forward backward (k 0) t = run forward backward (k 0) (t + 1) ↔ d / 2 ≤ t := by
  constructor
  · intro hfix
    by_cases h : d / 2 ≤ t
    · exact h
    · exfalso
      have hnew : run forward backward (k 0) (t + 1) (k ((t : Int) + 1)) :=
        (run_iff_interval k forward backward hf hb _ _).mpr
          ⟨(t : Int) + 1, by omega, by omega, rfl⟩
      have hold : run forward backward (k 0) t (k ((t : Int) + 1)) := by
        rw [hfix]
        exact hnew
      obtain ⟨j, hl, hu, he⟩ := (run_iff_interval k forward backward hf hb _ _).mp hold
      have hdiv : (d : Int) ∣ (t : Int) + 1 - j :=
        (rem_eq_iff_dvd _ _ _).mp ((hk _ _).mp he).symm
      have hgap := Int.le_of_dvd (show 0 < (t : Int) + 1 - j by omega) hdiv
      omega
  · intro ht
    funext x
    apply propext
    exact (run_iff_orbit_of_half_le k forward backward hf hb hd hk ht x).trans
      (run_iff_orbit_of_half_le k forward backward hf hb hd hk (t := t + 1) (by omega) x).symm

def residue (p : Nat) (hp : 0 < p) (i : Int) : Fin p :=
  ⟨(i % (p : Int)).toNat, by
    have hhi := Int.emod_lt_of_pos i (show 0 < (p : Int) by omega)
    omega⟩

private theorem residue_val (p : Nat) (hp : 0 < p) (i : Int) :
    ((residue p hp i).val : Int) = i % (p : Int) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

theorem residue_eq_iff (p : Nat) (hp : 0 < p) (i j : Int) :
    residue p hp i = residue p hp j ↔ i % (p : Int) = j % (p : Int) := by
  constructor
  · intro h
    have e := congrArg (fun x : Fin p => (x.val : Int)) h
    simpa only [residue_val] using e
  · intro h
    apply Fin.ext
    exact congrArg Int.toNat h

/-- The orbit of (0,0) in the product of the two cyclic index sets. -/
def diagonal (p q : Nat) (hp : 0 < p) (hq : 0 < q) (i : Int) : Fin p × Fin q :=
  (residue p hp i, residue q hq i)

def shift (p q : Nat) (hp : 0 < p) (hq : 0 < q) (s : Int) (x : Fin p × Fin q) :
    Fin p × Fin q :=
  (residue p hp ((x.1.val : Int) + s), residue q hq ((x.2.val : Int) + s))

private theorem residue_shift (p : Nat) (hp : 0 < p) (i s : Int) :
    residue p hp (((residue p hp i).val : Int) + s) = residue p hp (i + s) := by
  apply (residue_eq_iff _ _ _ _).mpr
  rw [residue_val, Int.emod_add_emod]

theorem shift_diagonal (p q : Nat) (hp : 0 < p) (hq : 0 < q) (i s : Int) :
    shift p q hp hq s (diagonal p q hp hq i) = diagonal p q hp hq (i + s) :=
  Prod.ext (residue_shift p hp i s) (residue_shift q hq i s)

theorem diagonal_period (p q : Nat) (hp : 0 < p) (hq : 0 < q) :
    period (diagonal p q hp hq) (p.lcm q) := by
  intro i j
  change ((residue p hp i, residue q hq i) = (residue p hp j, residue q hq j)) ↔ _
  rw [Prod.mk.injEq, residue_eq_iff, residue_eq_iff, rem_eq_iff_dvd, rem_eq_iff_dvd,
    rem_eq_iff_dvd]
  constructor
  · rintro ⟨hpr, hqr⟩
    apply Int.natAbs_dvd_natAbs.mp
    change p.lcm q ∣ (i - j).natAbs
    exact Nat.lcm_dvd (Int.natAbs_dvd_natAbs.mpr hpr) (Int.natAbs_dvd_natAbs.mpr hqr)
  · intro h
    exact ⟨Int.dvd_trans (Int.ofNat_dvd.mpr (Nat.dvd_lcm_left p q)) h,
      Int.dvd_trans (Int.ofNat_dvd.mpr (Nat.dvd_lcm_right p q)) h⟩

private theorem shift_back (p q : Nat) (hp : 0 < p) (hq : 0 < q) (i : Int) :
    shift p q hp hq (-1) (diagonal p q hp hq i) = diagonal p q hp hq (i - 1) := by
  simpa [Int.sub_eq_add_neg] using shift_diagonal p q hp hq i (-1)

def crossRun (p q : Nat) (hp : 0 < p) (hq : 0 < q) : Nat → (Fin p × Fin q) → Prop :=
  run (shift p q hp hq 1) (shift p q hp hq (-1)) (diagonal p q hp hq 0)

theorem crossRun_iff_interval (p q : Nat) (hp : 0 < p) (hq : 0 < q)
    (t : Nat) (x : Fin p × Fin q) :
    crossRun p q hp hq t x ↔
      ∃ i : Int, -(t : Int) ≤ i ∧ i ≤ (t : Int) ∧ diagonal p q hp hq i = x :=
  run_iff_interval _ _ _ (fun i => shift_diagonal p q hp hq i 1) (shift_back p q hp hq) t x

theorem crossRun_fixed_iff (p q : Nat) (hp : 0 < p) (hq : 0 < q) (t : Nat) :
    crossRun p q hp hq t = crossRun p q hp hq (t + 1) ↔ p.lcm q / 2 ≤ t :=
  run_fixed_iff _ _ _ (fun i => shift_diagonal p q hp hq i 1) (shift_back p q hp hq)
    (Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))) (diagonal_period p q hp hq) t

end Bootstrap.CyclicClock

#print axioms Bootstrap.CyclicClock.run_iff_interval
#print axioms Bootstrap.CyclicClock.run_iff_orbit_of_half_le
#print axioms Bootstrap.CyclicClock.run_fixed_iff
#print axioms Bootstrap.CyclicClock.diagonal_period
#print axioms Bootstrap.CyclicClock.crossRun_iff_interval
#print axioms Bootstrap.CyclicClock.crossRun_fixed_iff
