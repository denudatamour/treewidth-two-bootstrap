import Bootstrap.RuleBooks
import Bootstrap.MarkerMaps
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Bootstrap.RuleStructure

open Localization
variable {R : Type*}

private abbrev Fiber (t : Fin 10) :=
  (Fin (20 + t.val) ⊕ Fin (50 - t.val)) ⊕
    (Fin (103 * (2 * (20 + t.val) - 3)) ⊕ Fin (103 * (2 * (50 - t.val) - 3)))

private def fiberEquiv (c : R → Fin 10) : HostVertex c ≃ (r : R) × Fiber (c r) where
  toFun
    | .core (.primary r) k => ⟨r, .inl (.inl k)⟩
    | .core (.secondary r) k => ⟨r, .inl (.inr k)⟩
    | .page (.primary r) k => ⟨r, .inr (.inl k)⟩
    | .page (.secondary r) k => ⟨r, .inr (.inr k)⟩
  invFun
    | ⟨r, .inl (.inl k)⟩ => .core (.primary r) k
    | ⟨r, .inl (.inr k)⟩ => .core (.secondary r) k
    | ⟨r, .inr (.inl k)⟩ => .page (.primary r) k
    | ⟨r, .inr (.inr k)⟩ => .page (.secondary r) k
  left_inv := by rintro (⟨r | r, k⟩ | ⟨r | r, k⟩) <;> rfl
  right_inv := by rintro ⟨r, (⟨k⟩ | ⟨k⟩) | (⟨k⟩ | ⟨k⟩)⟩ <;> rfl

private theorem card_fiber (t : Fin 10) : Fintype.card (Fiber t) = 13872 := by
  simp only [Fiber, Fintype.card_sum, Fintype.card_fin]
  have ht := t.isLt
  omega

noncomputable def hostIndex (c : R → Fin 10) : HostVertex c ≃ R × Fin 13872 :=
  (fiberEquiv c).trans (Equiv.sigmaEquivProdOfEquiv fun r =>
    Fintype.equivFinOfCardEq (card_fiber (c r)))

noncomputable instance hostFintype [Fintype R] (c : R → Fin 10) : Fintype (HostVertex c) :=
  Fintype.ofEquiv (R × Fin 13872) (hostIndex c).symm

theorem card_hostVertex [Fintype R] (c : R → Fin 10) :
    Fintype.card (HostVertex c) = 13872 * Fintype.card R := by
  rw [Fintype.card_congr (hostIndex c), Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]

instance kindFintype : Fintype TypedRound.Kind where
  elems := [.endpoint, .u false, .u true, .v false, .v true].toFinset
  complete := by rintro ( _ | b | b ) <;> first | decide | (cases b <;> decide)

theorem card_kind : Fintype.card TypedRound.Kind = 5 := by decide

theorem source_order : Fintype.card (HostVertex MarkedSimulation.sourceCode) = 166464 := by
  rw [card_hostVertex, TypedRound.rule_counts.1]

theorem host_order (p q : Nat) :
    Fintype.card (HostVertex (@MarkedSimulation.hostCode (Fin p) (Fin q))) = 69360 * (p + q) := by
  rw [card_hostVertex]
  change 13872 * Fintype.card ((TypedRound.Kind × Fin p) ⊕ (TypedRound.Kind × Fin q)) = _
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, card_kind,
    Fintype.card_fin, Fintype.card_fin]
  omega

theorem page_adj_iff (L : SimpleGraph R) (c : R → Fin 10) (port : R → R → Fin 2)
    (b : Block R) (k : Fin (pageCount c b)) (x : HostVertex c) :
    (Localization.rule L c port).Adj (.page b k) x ↔
      x = .core b (pageLo c b k) ∨ x = .core b (pageHi c b k) := by
  constructor
  · rintro (h | h)
    · cases h with
      | pageLeft => exact Or.inl rfl
      | pageRight => exact Or.inr rfl
    · cases h
  · rintro (rfl | rfl)
    · exact Or.inl (.pageLeft b k)
    · exact Or.inl (.pageRight b k)

theorem page_degree [Fintype R] (L : SimpleGraph R) (c : R → Fin 10) (port : R → R → Fin 2)
    [DecidableRel (Localization.rule L c port).Adj] (b : Block R) (k : Fin (pageCount c b)) :
    (Localization.rule L c port).degree (.page b k) = 2 := by
  classical
  let g := Localization.rule L c port
  have hset : g.neighborFinset (.page b k) =
      {Vertex.core b (pageLo c b k), Vertex.core b (pageHi c b k)} := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    exact page_adj_iff _ _ _ _ _ _
  have hn : pageLo c b k ≠ pageHi c b k :=
    fun h => (Nat.ne_of_lt (pageLo_lt_hi c b k)) (congrArg Fin.val h)
  change (g.neighborFinset (.page b k)).card = 2
  rw [hset]
  apply Finset.card_pair
  exact (coreEmbedding (blockSize c) (pageCount c) b).injective.ne hn

theorem core_degree_lower [Fintype R] (L : SimpleGraph R) (c : R → Fin 10)
    (port : R → R → Fin 2) [DecidableRel (Localization.rule L c port).Adj]
    (b : Block R) (j : Fin (blockSize c b)) :
    103 ≤ (Localization.rule L c port).degree (.core b j) := by
  let g := Localization.rule L c port
  have has : ∃ d, CoreEdge j d := by
    by_cases h : j = hubIdx c b 0
    · refine ⟨hubIdx c b 1, ?_, Or.inr ?_⟩
      · intro hd
        have he : (0 : Nat) = 1 := congrArg Fin.val (h.symm.trans hd)
        omega
      · change (1 : Nat) < 2
        decide
    · exact ⟨hubIdx c b 0, h, Or.inr (by change (0 : Nat) < 2; decide)⟩
  obtain ⟨d, hd⟩ := has
  obtain ⟨w, hw⟩ := ((ruleBook L c port b).thick j d hd).2
  let f : Fin 103 ↪ g.neighborSet (.core b j) :=
    ⟨fun i => ⟨w i, (hw i).1⟩, fun i l e => w.injective (congrArg Subtype.val e)⟩
  have hb := Fintype.card_le_of_embedding f
  simpa only [Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree] using hb

theorem rule_minDegree [Fintype R] (L : SimpleGraph R) (c : R → Fin 10) (port : R → R → Fin 2)
    [DecidableRel (Localization.rule L c port).Adj] (r : R) :
    (Localization.rule L c port).minDegree = 2 := by
  let b : Block R := .primary r
  have hp : 0 < pageCount c b := by
    have := blockSize_three c b
    unfold pageCount
    omega
  let k : Fin (pageCount c b) := ⟨0, hp⟩
  letI : Nonempty (HostVertex c) := ⟨.page b k⟩
  apply Nat.le_antisymm
  · exact ((Localization.rule L c port).minDegree_le_degree (.page b k)).trans_eq
      (page_degree L c port b k)
  · apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro x
    cases x with
    | page e j => exact (page_degree L c port e j).ge
    | core e j => exact Nat.le_trans (by decide : 2 ≤ 103) (core_degree_lower L c port e j)

open scoped Classical in
theorem source_minDegree :
    (Localization.rule TypedRound.rule MarkedSimulation.sourceCode MarkedSimulation.port).minDegree = 2 :=
  rule_minDegree _ _ _ (Sum.inl (TypedRound.LocalRole.endpoint false))

end Bootstrap.RuleStructure

#print axioms Bootstrap.RuleStructure.source_order
#print axioms Bootstrap.RuleStructure.host_order
#print axioms Bootstrap.RuleStructure.source_minDegree
