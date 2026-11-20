/-
Author: Haimin Zhou. Local internal-review formalization pilot.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Sym
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

/-! Ordinary injective non-induced copies; all witnesses read one current graph.
This source is under development until the recorded build succeeds.
-/
namespace Bootstrap

variable {W V U : Type*}

def Witness (H : SimpleGraph W) (G : SimpleGraph V) (x y : V) : Prop :=
  ∃ (u v : W) (f : W ↪ V), H.Adj u v ∧ f u = x ∧ f v = y ∧
    ∀ i j, H.Adj i j → ¬ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) →
      G.Adj (f i) (f j)

def step (H : SimpleGraph W) (G : SimpleGraph V) : SimpleGraph V where
  Adj x y := G.Adj x y ∨ Witness H G x y
  symm := by
    intro x y h
    rcases h with h | ⟨u, v, f, huv, hux, hvy, hr⟩
    · exact Or.inl (G.symm h)
    · refine Or.inr ⟨v, u, f, H.symm huv, hvy, hux, ?_⟩
      intro i j hij hn
      apply hr i j hij
      tauto
  loopless := by
    intro x h
    rcases h with h | ⟨u, v, f, huv, hux, hvx, hr⟩
    · exact G.loopless x h
    · have heq : u = v := f.injective (hux.trans hvx.symm)
      subst v
      exact H.loopless u huv

theorem le_step (H : SimpleGraph W) (G : SimpleGraph V) : G ≤ step H G := by
  intro x y h
  exact Or.inl h

theorem step_no_embedding (H : SimpleGraph W) (G : SimpleGraph V)
    (hno : ¬ Nonempty (W ↪ V)) : step H G = G := by
  ext x y
  constructor
  · rintro (h | ⟨u, v, f, _, _, _, _⟩)
    · exact h
    · exact False.elim (hno ⟨f⟩)
  · exact Or.inl

theorem step_empty_rule (G : SimpleGraph V) : step (⊥ : SimpleGraph W) G = G := by
  ext x y
  constructor
  · rintro (h | ⟨u, v, f, he, _, _, _⟩)
    · exact h
    · exact False.elim he
  · exact Or.inl

theorem step_mono (H : SimpleGraph W) : Monotone (step H (V := V)) := by
  intro G G' h x y hxy
  rcases hxy with hxy | ⟨u, v, f, huv, hux, hvy, hr⟩
  · exact Or.inl (h hxy)
  · exact Or.inr ⟨u, v, f, huv, hux, hvy, fun i j hij hn => h (hr i j hij hn)⟩

def run (H : SimpleGraph W) (G : SimpleGraph V) : ℕ → SimpleGraph V
  | 0 => G
  | n + 1 => step H (run H G n)

@[simp] theorem run_zero (H : SimpleGraph W) (G : SimpleGraph V) : run H G 0 = G := rfl
@[simp] theorem run_succ (H : SimpleGraph W) (G : SimpleGraph V) (n : ℕ) :
    run H G (n + 1) = step H (run H G n) := rfl

theorem run_le_succ (H : SimpleGraph W) (G : SimpleGraph V) (n : ℕ) :
    run H G n ≤ run H G (n + 1) := le_step H _

theorem witness_transport (H : SimpleGraph W) (G : SimpleGraph V)
    (G' : SimpleGraph U) (g : V ≃ U)
    (hg : ∀ x y, G.Adj x y → G'.Adj (g x) (g y))
    {x y : V} (h : Witness H G x y) : Witness H G' (g x) (g y) := by
  rcases h with ⟨u, v, f, huv, hux, hvy, hr⟩
  refine ⟨u, v, f.trans g.toEmbedding, huv, ?_, ?_, ?_⟩
  · exact congrArg g hux
  · exact congrArg g hvy
  · intro i j hij hn
    exact hg _ _ (hr i j hij hn)

theorem step_transport (H : SimpleGraph W) (G : SimpleGraph V)
    (G' : SimpleGraph U) (g : V ≃ U)
    (hg : ∀ x y, G.Adj x y → G'.Adj (g x) (g y))
    {x y : V} (h : (step H G).Adj x y) : (step H G').Adj (g x) (g y) := by
  rcases h with h | h
  · exact Or.inl (hg _ _ h)
  · exact Or.inr (witness_transport H G G' g hg h)

theorem step_equivariant (H : SimpleGraph W) (G : SimpleGraph V)
    (G' : SimpleGraph U) (g : V ≃ U)
    (hg : ∀ x y, G'.Adj (g x) (g y) ↔ G.Adj x y) (x y : V) :
    (step H G').Adj (g x) (g y) ↔ (step H G).Adj x y := by
  constructor
  · intro h
    have back : ∀ x y, G'.Adj x y → G.Adj (g.symm x) (g.symm y) := by
      intro x y hxy
      apply (hg (g.symm x) (g.symm y)).mp
      simpa using hxy
    simpa using step_transport H G' G g.symm back h
  · exact step_transport H G G' g (fun x y => (hg x y).mpr)

def Invariant (Γ : Subgroup (Equiv.Perm V)) (G : SimpleGraph V) : Prop :=
  ∀ g : Γ, ∀ x y, G.Adj (g.val x) (g.val y) ↔ G.Adj x y

theorem invariant_step (H : SimpleGraph W) (Γ : Subgroup (Equiv.Perm V))
    (G : SimpleGraph V) (hG : Invariant Γ G) : Invariant Γ (step H G) := by
  intro g x y
  exact step_equivariant H G G g.val (hG g) x y

theorem invariant_run (H : SimpleGraph W) (Γ : Subgroup (Equiv.Perm V))
    (G : SimpleGraph V) (hG : Invariant Γ G) (n : ℕ) : Invariant Γ (run H G n) := by
  induction n with
  | zero => exact hG
  | succ n ih => exact invariant_step H Γ _ ih

end Bootstrap

#print axioms Bootstrap.step_mono
#print axioms Bootstrap.step_equivariant
#print axioms Bootstrap.invariant_run
