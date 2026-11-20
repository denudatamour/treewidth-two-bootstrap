import Bootstrap.ConnectedDegreeTwo
import Bootstrap.Asymptotics
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-! Parallel internally disjoint arms with two common poles, in an ordinary simple graph.
An arm indexed by i has m i + 1 private vertices and m i + 2 edges. -/
namespace Bootstrap.Theta

variable {k : Nat}

abbrev Vertex (m : Fin k → Nat) := Bool ⊕ (Σ i : Fin k, Fin (m i + 1))

def pole (m : Fin k → Nat) (b : Bool) : Vertex m := .inl b

def inner (m : Fin k → Nat) (i : Fin k) (j : Fin (m i + 1)) : Vertex m := .inr ⟨i,j⟩

private def touch (b : Bool) (m j : Nat) : Prop := if b then j = m else j = 0

private def arc (m : Fin k → Nat) : Vertex m → Vertex m → Prop
  | .inl _, .inl _ => False
  | .inl b, .inr ⟨i,j⟩ => touch b (m i) j
  | .inr ⟨i,j⟩, .inl b => touch b (m i) j
  | .inr ⟨i,j⟩, .inr ⟨s,t⟩ => i = s ∧ (j.val + 1 = t.val ∨ t.val + 1 = j.val)

def graph (m : Fin k → Nat) : SimpleGraph (Vertex m) where
  Adj := arc m
  symm := by
    rintro (b | ⟨i,j⟩) (c | ⟨s,t⟩) h
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm,h.2.symm⟩
  loopless := by
    rintro (b | ⟨i,j⟩)
    · exact id
    · change ¬ (_ ∧ (_ ∨ _))
      omega

instance (m : Fin k → Nat) : DecidableRel (graph m).Adj := by
  rintro (b | ⟨i,j⟩) (c | ⟨s,t⟩)
  · exact inferInstanceAs (Decidable False)
  · cases b <;> exact inferInstanceAs (Decidable (_ = _))
  · cases c <;> exact inferInstanceAs (Decidable (_ = _))
  · exact inferInstanceAs (Decidable (i = s ∧ (j.val + 1 = t.val ∨ t.val + 1 = j.val)))

private def before (m : Fin k → Nat) (i : Fin k) (j : Fin (m i + 1)) : Vertex m :=
  if h : 0 < j.val then inner m i ⟨j.val - 1, by omega⟩ else pole m false

private def afterV (m : Fin k → Nat) (i : Fin k) (j : Fin (m i + 1)) : Vertex m :=
  if h : j.val < m i then inner m i ⟨j.val + 1, by omega⟩ else pole m true

theorem twoNeighbours_inner (m : Fin k → Nat) (i : Fin k) (j : Fin (m i + 1)) :
    DegreeTwo.HasTwo (graph m) (inner m i j) := by
  refine ⟨before m i j,afterV m i j,⟨?_,?_,?_,?_⟩⟩
  · unfold before
    split
    · exact ⟨rfl,Or.inr (by simp; omega)⟩
    · change j.val = 0
      omega
  · unfold afterV
    split
    · exact ⟨rfl,Or.inl rfl⟩
    · change j.val = m i
      omega
  · unfold before afterV
    split <;> split
    · intro e
      have h := congrArg (fun v : Vertex m => Sum.elim (fun _ => 0) (fun p => p.2.val) v) e
      change j.val - 1 = j.val + 1 at h
      omega
    all_goals simp [inner,pole]
  · rintro (b | ⟨s,t⟩) h
    · cases b
      · change j.val = 0 at h
        exact Or.inl (by simp [before,h,pole])
      · change j.val = m i at h
        exact Or.inr (by simp [afterV,h,pole])
    · obtain ⟨rfl,h | h⟩ := h
      · right
        have lt : j.val < m i := by omega
        rw [afterV,dif_pos lt]
        exact congrArg (inner m i) (Fin.ext h.symm)
      · left
        have lt : 0 < j.val := by omega
        rw [before,dif_pos lt]
        exact congrArg (inner m i) (Fin.ext (by change t.val = j.val - 1; omega))

theorem degree_inner (m : Fin k → Nat) (i : Fin k) (j : Fin (m i + 1)) :
    (graph m).degree (inner m i j) = 2 :=
  (DegreeTwo.hasTwo_iff_degree _ _).mp (twoNeighbours_inner m i j)

private def endIndex (m : Fin k → Nat) (b : Bool) (i : Fin k) : Fin (m i + 1) :=
  if b then Fin.last (m i) else 0

private def neighborsOfPole (m : Fin k → Nat) (b : Bool) :
    (graph m).neighborSet (pole m b) ≃ Fin k where
  toFun z := match z with
    | ⟨.inl _, h⟩ => False.elim h
    | ⟨.inr ⟨i,_⟩, _⟩ => i
  invFun i := ⟨inner m i (endIndex m b i), by
    cases b <;> rfl⟩
  left_inv := by
    rintro ⟨c | ⟨i,j⟩,h⟩
    · exact False.elim h
    · apply Subtype.ext
      apply congrArg (inner m i)
      apply Fin.ext
      cases b
      · change j.val = 0 at h
        exact h.symm
      · change j.val = m i at h
        exact h.symm
  right_inv _ := rfl

theorem degree_pole (m : Fin k → Nat) (b : Bool) : (graph m).degree (pole m b) = k := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr (neighborsOfPole m b)).trans (Fintype.card_fin k)

theorem connected (m : Fin k → Nat) (hk : 0 < k) : (graph m).Connected := by
  have reach (i : Fin k) (j : Fin (m i + 1)) :
      (graph m).Reachable (pole m false) (inner m i j) := by
    induction j using Fin.induction with
    | zero => exact (show (graph m).Adj (pole m false) (inner m i 0) from rfl).reachable
    | succ j ih =>
      exact ih.trans (show (graph m).Adj (inner m i j.castSucc) (inner m i j.succ) from
        ⟨rfl,Or.inl rfl⟩).reachable
  apply ((graph m).connected_iff_exists_forall_reachable).mpr
  refine ⟨pole m false,?_⟩
  rintro (b | ⟨i,j⟩)
  · cases b
    · exact SimpleGraph.Reachable.refl _
    · let t : Fin k := ⟨0,hk⟩
      exact (reach t (Fin.last (m t))).trans
        (show (graph m).Adj (inner m t (Fin.last (m t))) (pole m true) from rfl).reachable
  · exact reach i j

theorem degree_two_endpoint (m : Fin k → Nat) {x y : Vertex m} (h : (graph m).Adj x y) :
    (graph m).degree x = 2 ∨ (graph m).degree y = 2 := by
  rcases x with b | ⟨i,j⟩
  · rcases y with c | ⟨i,j⟩
    · exact False.elim h
    · exact Or.inr (degree_inner m i j)
  · exact Or.inl (degree_inner m i j)

theorem minDegree (m : Fin k → Nat) (hk : 2 ≤ k) : (graph m).minDegree = 2 := by
  haveI : Nonempty (Vertex m) := ⟨pole m false⟩
  apply Nat.le_antisymm
  · let i : Fin k := ⟨0,by omega⟩
    exact ((graph m).minDegree_le_degree (inner m i 0)).trans (degree_inner m i 0).le
  · apply (graph m).le_minDegree_of_forall_le_degree
    rintro (b | ⟨i,j⟩)
    · exact hk.trans (degree_pole m b).ge
    · exact (degree_inner m i j).ge

theorem maxDegree (m : Fin k → Nat) (hk : 2 ≤ k) : (graph m).maxDegree = k := by
  apply Nat.le_antisymm
  · apply (graph m).maxDegree_le_of_forall_degree_le
    rintro (b | ⟨i,j⟩)
    · exact (degree_pole m b).le
    · exact (degree_inner m i j).le.trans hk
  · exact (degree_pole m false).ge.trans ((graph m).degree_le_maxDegree (pole m false))

/-- Ordinary rule on poles and private internal vertices, parametrized by edge lengths. -/
abbrev rule (lengths : Fin k → Nat) := graph (fun i => lengths i - 2)

theorem arm_length (lengths : Fin k → Nat) (hl : ∀ i, 2 ≤ lengths i) (i : Fin k) :
    (lengths i - 2) + 2 = lengths i := Nat.sub_add_cancel (hl i)

/-- The complete structural hypotheses of the two bounds in Theorem II.1. -/
theorem rule_class (lengths : Fin k → Nat) (hk : 3 ≤ k) :
    (rule lengths).Connected ∧
    (∀ x y, (rule lengths).Adj x y → (rule lengths).degree x = 2 ∨ (rule lengths).degree y = 2) ∧
    (rule lengths).minDegree = 2 ∧ (rule lengths).maxDegree = k :=
  ⟨connected _ (by omega), fun _ _ => degree_two_endpoint _, minDegree _ (by omega),
    maxDegree _ (by omega)⟩

/-- Applying an upper bound proved for the degree-two class to any of the stated arm lengths. -/
theorem linear_upper_of_degree_two (lengths : Fin k → Nat) (hk : 3 ≤ k)
    (upper : (rule lengths).Connected →
      (∀ x y, (rule lengths).Adj x y → (rule lengths).degree x = 2 ∨ (rule lengths).degree y = 2) →
      HasLinearUpper (rule lengths)) : HasLinearUpper (rule lengths) := by
  obtain ⟨hc,he,_,_⟩ := rule_class lengths hk
  exact upper hc he

/-- The lower-bound assumptions for the fixed-rule theorem of Fabian, Morris and Szabó. -/
theorem linear_lower_of_degree_bounds (lengths : Fin k → Nat) (hk : 3 ≤ k)
    (lower : 2 ≤ (rule lengths).minDegree → 3 ≤ (rule lengths).maxDegree →
      ∃ A n₀ : Nat, 0 < A ∧ ∀ n, n₀ ≤ n → n ≤ A * maxTime (rule lengths) n) :
    ∃ A n₀ : Nat, 0 < A ∧ ∀ n, n₀ ≤ n → n ≤ A * maxTime (rule lengths) n := by
  obtain ⟨_,_,hm,hM⟩ := rule_class lengths hk
  exact lower hm.ge (hk.trans hM.ge)

def threeLengths (a b c : Nat) (i : Fin 3) : Nat :=
  if i = 0 then a else if i = 1 then b else c

theorem three_arm_lengths (a b c : Nat) :
    threeLengths a b c 0 = a ∧ threeLengths a b c 1 = b ∧ threeLengths a b c 2 = c := by
  simp [threeLengths]

theorem theta_class (a b c : Nat) :
    (rule (threeLengths a b c)).Connected ∧
    (∀ x y, (rule (threeLengths a b c)).Adj x y →
      (rule (threeLengths a b c)).degree x = 2 ∨ (rule (threeLengths a b c)).degree y = 2) ∧
    (rule (threeLengths a b c)).minDegree = 2 ∧ (rule (threeLengths a b c)).maxDegree = 3 :=
  rule_class _ (by decide)

end Bootstrap.Theta

#print axioms Bootstrap.Theta.rule_class
#print axioms Bootstrap.Theta.linear_upper_of_degree_two
#print axioms Bootstrap.Theta.linear_lower_of_degree_bounds
#print axioms Bootstrap.Theta.theta_class
