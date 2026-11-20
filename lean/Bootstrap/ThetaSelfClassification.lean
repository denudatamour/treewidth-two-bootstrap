import Bootstrap.ThetaPrimitiveClosure
import Bootstrap.EqualArmClosure
import Bootstrap.ThetaCorridorClosure
import Mathlib.Tactic.FinCases

namespace Bootstrap.Theta

/-- A graph is bipartite exactly when it admits a proper map into two colours. -/
def HasBipartition {X : Type*} (G : SimpleGraph X) : Prop :=
  ∃ B : X → Bool, ∀ x y, G.Adj x y → B x ≠ B y

/-- Two-colourability of the actual graph is equivalent to agreement of its arm parities. -/
theorem colorable_two_iff_arm_parity (m : Fin 3 → ℕ) :
    HasBipartition (graph m) ↔ ∀ i, (m i+2)%2=(m 0+2)%2 := by
  constructor
  · rintro ⟨B,proper⟩
    let p := Corridor.point m
    have next (i : Fin 3) (j : ℕ) (hj : j<m i+2) :
        B (p i (j+1))=(!B (p i j)) := by
      have diff := proper _ _ (Corridor.point_edge m i hj)
      change B (p i j) ≠ B (p i (j+1)) at diff
      cases a : B (p i j) <;> cases b : B (p i (j+1)) <;> simp_all
    have along (i : Fin 3) (j : ℕ) (h : j≤m i+2) :
        B (p i j) = (if j%2=1 then !B (pole m false) else B (pole m false)) := by
      induction j with
      | zero => simp [p]
      | succ j ih =>
        rw [next i j h,ih (by omega)]
        by_cases e : j%2=1
        · have e' : ¬(j+1)%2=1 := by omega
          simp [e,e']
        · have e' : (j+1)%2=1 := by omega
          simp [e,e']
    intro i
    have a := along i (m i+2) le_rfl
    have b := along 0 (m 0+2) le_rfl
    simp only [p,Corridor.point_end] at a b
    cases z : B (pole m false) <;> rw [z] at a b <;> split_ifs at a b <;> simp_all
  · intro same
    exact ⟨naturalColor m _,fun _ _ edge => natural_proper m _ same edge⟩

end Bootstrap.Theta

namespace Bootstrap.Theta

open scoped Classical

/-- Common divisor of the three actual edge lengths. -/
def lengthGcd (L : Fin 3 → ℕ) : ℕ := (L 0).gcd ((L 1).gcd (L 2))

private theorem gcd_dvd_length (L : Fin 3 → ℕ) (i : Fin 3) : lengthGcd L ∣ L i := by
  fin_cases i
  · exact Nat.gcd_dvd_left _ _
  · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)

private theorem divide_lengths (L : Fin 3 → ℕ) (pos : ∀ i, 0<L i) :
    let d := lengthGcd L
    let r := fun i => L i/d
    0<d ∧ (∀ i, 0<r i) ∧ (∀ i, r i*d=L i) ∧ lengthGcd r=1 := by
  dsimp only
  let d := lengthGcd L
  let r (i : Fin 3) := L i/d
  have hd : 0<d := Nat.gcd_pos_of_pos_left _ (pos 0)
  have lens (i : Fin 3) : r i*d=L i := Nat.div_mul_cancel (gcd_dvd_length L i)
  have rp (i : Fin 3) : 0<r i := Nat.div_pos (Nat.le_of_dvd (pos i) (gcd_dvd_length L i)) hd
  refine ⟨hd,rp,lens,?_⟩
  have h : (lengthGcd r)*d = lengthGcd (fun i => r i*d) := by
    simp only [lengthGcd,Nat.gcd_mul_right]
  rw [show (fun i => r i*d)=L from funext lens] at h
  exact Nat.eq_of_mul_eq_mul_right hd (h.trans (Nat.one_mul d).symm)

private theorem odd_of_primitive_uniform (r : Fin 3 → ℕ) (prim : lengthGcd r=1)
    (same : ∀ i, r i%2=r 0%2) : ∀ i, r i%2=1 := by
  have one : r 0%2=1 := by
    by_contra bad
    have div (i : Fin 3) : 2∣r i := by have := same i; omega
    have impossible : 2∣lengthGcd r := Nat.dvd_gcd (div 0) (Nat.dvd_gcd (div 1) (div 2))
    rw [prim] at impossible
    omega
  exact fun i => (same i).trans one

private theorem scaled_parity (r : Fin 3 → ℕ) (d : ℕ) (prim : lengthGcd r=1) :
    ((∀ i, r i%2=1) ∨ d%2=0) ↔ ∀ i, (r i*d)%2=(r 0*d)%2 := by
  constructor
  · rintro (odd|even) i
    · simp [Nat.mul_mod,odd]
    · simp [Nat.mul_mod,even]
  · intro same
    by_cases even : d%2=0
    · exact Or.inr even
    have odd : d%2=1 := by omega
    exact Or.inl (odd_of_primitive_uniform r prim fun i => by simpa [Nat.mul_mod,odd] using same i)

private theorem colors_congr (m : Fin 3 → ℕ) {p q : ℕ} (same : p%2=q%2) :
    naturalColor m p=naturalColor m q := by
  funext x
  rcases x with b|⟨i,j⟩
  · cases b <;> simp [naturalColor,same]
  · rfl

/-- The segment incidence needed for the nonprimitive and unequal case. -/
def ScaledSegmentInclusion : Prop :=
  ∀ (r : Fin 3 → ℕ) (d : ℕ), 2≤d → (∀ i, 0<r i) → lengthGcd r=1 → (∃ i,1<r i) →
    Corridor.segmentGraph r d (decide (∀ i, r i%2=1)) ≤ Corridor.F r d

theorem unequal_self_of_scaled (inc : ScaledSegmentInclusion) (m : Fin 3 → ℕ)
    (unequal : ¬∀ i, armSize m i=armSize m 0) :
    thetaClosure m = if HasBipartition (graph m) then completeBetween (naturalColor m (armSize m 0)) else ⊤ := by
  classical
  let L := armSize m
  let d := lengthGcd L
  let r (i : Fin 3) := L i/d
  have pos (i : Fin 3) : 0<L i := by dsimp [L,armSize]; omega
  obtain ⟨dp,rp,lens,prim⟩ := divide_lengths L pos
  change 0<d at dp
  change ∀ i, 0<r i at rp
  change ∀ i, r i*d=L i at lens
  change lengthGcd r=1 at prim
  by_cases unit : d=1
  · have base : Primitive m := unit
    by_cases bip : HasBipartition (graph m)
    · rw [if_pos bip]
      have par := (colorable_two_iff_arm_parity m).mp bip
      have odd := odd_of_primitive_uniform L unit par
      rw [←colors_congr m (p:=1) (q:=L 0) (odd 0).symm]
      exact primitive_odd_closure m base odd
    · rw [if_neg bip]
      have mix : MixedParity m := by
        by_contra! none
        apply bip
        apply (colorable_two_iff_arm_parity m).mpr
        intro i
        by_contra neq
        exact none ⟨i,0,neq⟩
      exact primitive_mixed_closure m base mix
  have big : 2≤d := by omega
  have long : ∃ i, 1<r i := by
    by_contra! small
    apply unequal
    intro i
    change L i=L 0
    have all (j : Fin 3) : r j=1 := by have := rp j; have := small j; omega
    rw [←lens i,←lens 0,all i,all 0]
  let c := decide (∀ i, r i%2=1)
  have col : c=true → ∀ i, r i%2=1 := of_decide_eq_true
  have geom := Corridor.self_closure_of_segment r big rp c col (inc r d big rp prim long) long
  have eq : Corridor.M r d=m := by
    funext i
    change r i*d-2=m i
    rw [lens i]
    dsimp [L,armSize]
    omega
  have scaled : thetaClosure m = if c=true ∨ d%2=0 then completeBetween (naturalColor m d) else ⊤ := by
    change thetaClosure (Corridor.M r d) = _ at geom
    rwa [eq] at geom
  have equiv : (c=true ∨ d%2=0) ↔ HasBipartition (graph m) := by
    rw [colorable_two_iff_arm_parity]
    change ((decide (∀ i, r i%2=1))=true ∨ d%2=0) ↔ ∀ i, L i%2=L 0%2
    simp only [decide_eq_true_eq]
    rw [scaled_parity r d prim]
    simp only [lens]
  rw [scaled]
  by_cases bip : HasBipartition (graph m)
  · rw [if_pos bip,if_pos (equiv.mpr bip)]
    have par : d%2=L 0%2 := by
      rw [←lens 0,Nat.mul_mod]
      rcases equiv.mpr bip with ct|even
      · rw [col ct 0,Nat.one_mul,Nat.mod_mod]
      · simp [even]
    rw [colors_congr m par]
  · rw [if_neg bip,if_neg (fun h => bip (equiv.mp h))]

/-- The three clauses of the self-closure classification, including its shortest theta. -/
theorem self_classification_of_scaled (inc : ScaledSegmentInclusion) (a b c : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    let L := threeLengths a b c
    let G := rule L
    (¬HasBipartition G → terminalGraph G G=⊤) ∧
    (HasBipartition G → ¬(a=b ∧ b=c) → terminalGraph G G=completeBetween (naturalColor (fun i => L i-2) a)) ∧
    (a=b ∧ b=c → terminalGraph G G=G) ∧
    (a=2 → b=2 → c=2 → Nonempty (G ≃g completeBipartiteGraph Bool (Fin 3))) := by
  classical
  let L := threeLengths a b c
  let m (i : Fin 3) := L i-2
  have lower (i : Fin 3) : 2≤L i := by simp only [L,threeLengths]; split_ifs <;> assumption
  have len (i : Fin 3) : armSize m i=L i := arm_length L lower i
  have abc := three_arm_lengths a b c
  have zero : armSize m 0=a := (len 0).trans abc.1
  have equal (all : ∀ i, armSize m i=armSize m 0) : a=b ∧ b=c := by
    have one := all 1
    have two := all 2
    rw [len 1,zero] at one
    rw [len 2,zero] at two
    exact ⟨one.symm.trans abc.2.1,(abc.2.1.symm.trans one).trans (two.symm.trans abc.2.2)⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro nonbip
    change ¬HasBipartition (graph m) at nonbip
    have ne : ¬∀ i, armSize m i=armSize m 0 := fun all => nonbip ((colorable_two_iff_arm_parity m).mpr
      (fun i => congrArg (fun n : ℕ => n%2) (all i)))
    simpa only [if_neg nonbip] using unequal_self_of_scaled inc m ne
  · intro bip uneq
    change HasBipartition (graph m) at bip
    simpa only [if_pos bip,zero] using unequal_self_of_scaled inc m (fun all => uneq (equal all))
  · rintro ⟨rfl,rfl⟩
    exact equal_length_self_closure _
  · rintro rfl rfl rfl
    have eq : threeLengths 2 2 2 = fun _ => 2 := funext (by intro i; simp [threeLengths])
    change Nonempty (rule (threeLengths 2 2 2) ≃g completeBipartiteGraph Bool (Fin 3))
    rw [eq]
    exact ⟨EqualArms.shortest_iso⟩

end Bootstrap.Theta

#print axioms Bootstrap.Theta.colorable_two_iff_arm_parity
#print axioms Bootstrap.Theta.unequal_self_of_scaled
#print axioms Bootstrap.Theta.self_classification_of_scaled
