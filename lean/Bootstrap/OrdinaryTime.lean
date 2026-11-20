import Bootstrap.Orbits
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Lattice.Fold

/-! Equation (1) of the preprint, on labelled hosts and under relabelling. -/
namespace Bootstrap

variable {W V U : Type*}

theorem stabilizationTime_eq_of_fixed_iff [Fintype V] [Fintype U]
    (H : SimpleGraph W) (G : SimpleGraph V) (G' : SimpleGraph U)
    (h : ∀ t, (run H G t = run H G (t+1)) ↔ (run H G' t = run H G' (t+1))) :
    stabilizationTime H G = stabilizationTime H G' := by
  classical
  apply Nat.le_antisymm
  · exact Nat.find_min' (stable_exists H G) ((h _).mpr (stabilizationTime_spec H G'))
  · exact Nat.find_min' (stable_exists H G') ((h _).mp (stabilizationTime_spec H G))

theorem stabilizationTime_eq_of_first [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (r : ℕ) (h : ∀ t, run H G t = run H G (t+1) ↔ r ≤ t) :
    stabilizationTime H G = r := by
  classical
  exact Nat.le_antisymm (Nat.find_min' (stable_exists H G) ((h r).mpr le_rfl))
    ((h _).mp (stabilizationTime_spec H G))

theorem run_equivariant (H : SimpleGraph W) (G : SimpleGraph V) (G' : SimpleGraph U)
    (e : V ≃ U) (hg : ∀ x y, G'.Adj (e x) (e y) ↔ G.Adj x y) (t : ℕ) :
    ∀ x y, (run H G' t).Adj (e x) (e y) ↔ (run H G t).Adj x y := by
  induction t with
  | zero => exact hg
  | succ t ih => exact step_equivariant H _ _ e ih

theorem stabilizationTime_relabel [Fintype V] [Fintype U] (H : SimpleGraph W)
    (G : SimpleGraph V) (G' : SimpleGraph U) (e : V ≃ U)
    (hg : ∀ x y, G'.Adj (e x) (e y) ↔ G.Adj x y) :
    stabilizationTime H G = stabilizationTime H G' := by
  apply stabilizationTime_eq_of_fixed_iff
  intro t
  have equivAt := run_equivariant H G G' e hg
  constructor
  · intro fix
    ext a b
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    rw [equivAt t, equivAt (t+1), fix]
  · intro fix
    ext x y
    rw [← equivAt t, ← equivAt (t+1), fix]

/-- The maximum over all simple starting graphs on a fixed labelled vertex set. -/
noncomputable def maxTime (H : SimpleGraph W) (n : ℕ) : ℕ := by
  classical
  exact Finset.univ.sup (fun G : SimpleGraph (Fin n) => stabilizationTime H G)

theorem le_maxTime (H : SimpleGraph W) {n : ℕ} (G : SimpleGraph (Fin n)) :
    stabilizationTime H G ≤ maxTime H n := by
  classical
  exact Finset.le_sup (s := Finset.univ) (f := fun F : SimpleGraph (Fin n) => stabilizationTime H F)
    (Finset.mem_univ G)

theorem le_maxTime_card [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) :
    stabilizationTime H G ≤ maxTime H (Fintype.card V) := by
  classical
  let e := Fintype.equivFin V
  let G' : SimpleGraph (Fin (Fintype.card V)) :=
    { Adj := fun x y => G.Adj (e.symm x) (e.symm y)
      symm := fun _ _ h => G.symm h
      loopless := fun x => G.loopless _ }
  have h := stabilizationTime_relabel H G G' e (by intro x y; change G.Adj _ _ ↔ G.Adj _ _; simp)
  exact h.le.trans (le_maxTime H G')

theorem maxTime_le_iff (H : SimpleGraph W) (n b : ℕ) :
    maxTime H n ≤ b ↔ ∀ G : SimpleGraph (Fin n), stabilizationTime H G ≤ b := by
  classical
  simp [maxTime, Finset.sup_le_iff]

theorem stabilizationTime_le_choose [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) :
    stabilizationTime H G ≤ (Fintype.card V).choose 2 := by
  classical
  let Γ : Subgroup (Equiv.Perm V) := ⊥
  calc
    stabilizationTime H G ≤ (missingOrbits Γ G).card :=
      stabilizationTime_le_missing H Γ G (invariant_bot G)
    _ ≤ Fintype.card (Orbit Γ) := Finset.card_le_univ _
    _ ≤ Fintype.card (UEdge V) :=
      Fintype.card_le_of_surjective (orbitOf Γ) (fun o => Quotient.exists_rep o)
    _ = _ := Sym2.card_subtype_not_diag

theorem maxTime_le_choose (H : SimpleGraph W) (n : ℕ) :
    maxTime H n ≤ n.choose 2 := by
  apply (maxTime_le_iff H n _).mpr
  intro G
  simpa using stabilizationTime_le_choose H G

end Bootstrap

#print axioms Bootstrap.stabilizationTime_relabel
#print axioms Bootstrap.le_maxTime_card
#print axioms Bootstrap.maxTime_le_iff
#print axioms Bootstrap.maxTime_le_choose
