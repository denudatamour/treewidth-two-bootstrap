import Bootstrap.RuleStructure
import Mathlib.Data.Fintype.Sigma

namespace Bootstrap.RuleEdgeCount
open Localization
private abbrev Role := TypedRound.Role
private abbrev Code := MarkedSimulation.sourceCode
private abbrev Port := MarkedSimulation.port
private abbrev V := HostVertex Code
private abbrev H := Localization.rule TypedRound.rule Code Port

private def low (s j : Nat) := if j < s - 1 then 0 else 1
private def high (s j : Nat) := if j < s - 1 then j + 1 else j - (s - 1) + 2
private def ordinal (s a d : Nat) := if a = 0 then d - 1 else (s - 1) + (d - 2)

private theorem ord_bounds {s j : Nat} (hs : 3 ≤ s) (hj : j < 2*s-3) :
    low s j < high s j ∧ high s j < s ∧ low s j < 2 ∧ ordinal s (low s j) (high s j) = j := by
  by_cases h : j < s - 1 <;> simp [low, high, h, ordinal] <;> omega

private theorem ord_spec {s a d : Nat} (hs : 3 ≤ s) (ha : a < 2) (had : a < d) (hd : d < s) :
    ordinal s a d < 2*s-3 ∧ low s (ordinal s a d) = a ∧ high s (ordinal s a d) = d := by
  by_cases h : a = 0 <;> simp only [ordinal, h, if_true, if_false, low, high] <;>
    split <;> omega

private abbrev Num (b : Block Role) := Fin (2 * blockSize Code b - 3)
private def lo (b : Block Role) (j : Num b) : Fin (blockSize Code b) :=
  ⟨low _ j.val, Nat.lt_trans (ord_bounds (blockSize_three Code b) j.isLt).1
    (ord_bounds (blockSize_three Code b) j.isLt).2.1⟩
private def hi (b : Block Role) (j : Num b) : Fin (blockSize Code b) :=
  ⟨high _ j.val, (ord_bounds (blockSize_three Code b) j.isLt).2.1⟩

private inductive Label
  | book (b : Block Role) (j : Num b)
  | page (b : Block Role) (j : Fin (pageCount Code b)) (right : Bool)
  | matching (r : Role) (j : Fin 2)
  | logical (e : TypedRound.Edge)

private def ends : Label → V × V
  | .book b j => (.core b (lo b j), .core b (hi b j))
  | .page b j false => (.page b j, .core b (pageLo Code b j))
  | .page b j true => (.page b j, .core b (pageHi Code b j))
  | .matching r k => (.core (.primary r) (hubIdx Code (.primary r) k),
    .core (.secondary r) (hubIdx Code (.secondary r) k))
  | .logical e => (portPoint Code Port e.fromRole e.toRole, portPoint Code Port e.toRole e.fromRole)

private def encoded (l : Label) := s((ends l).1, (ends l).2)

private inductive Key
  | book (b : Block Role) (j : Nat)
  | page (b : Block Role) (j : Nat) (right : Bool)
  | matching (r : Role) (j : Nat)
  | logical (e : Sym2 Role)
  | invalid

open scoped Classical in
private noncomputable def coreKey (b d : Block Role) (x y : Nat) : Key :=
  if b = d then .book b (ordinal (blockSize Code b) (min x y) (max x y))
  else match b, d with
    | .primary r, .primary s => .logical s(r,s)
    | .primary r, .secondary _ => .matching r x
    | .secondary _, .primary r => .matching r y
    | .secondary _, .secondary _ => .invalid

private theorem coreKey_comm (b d : Block Role) (x y : Nat) : coreKey b d x y = coreKey d b y x := by
  classical
  by_cases h : b = d
  · subst d; simp only [coreKey, if_pos rfl, if_true]; rw [Nat.min_comm x y, Nat.max_comm x y]
  · have hh := Ne.symm h
    cases b <;> cases d <;> simp only [coreKey, if_neg h, if_neg hh]
    exact congrArg Key.logical Sym2.eq_swap

private noncomputable def signature : V → V → Key
  | .core b x, .core d y => coreKey b d x.val y.val
  | .page b j, .core _ x => .page b j.val (decide (x.val ≠ (pageLo Code b j).val))
  | .core _ x, .page b j => .page b j.val (decide (x.val ≠ (pageLo Code b j).val))
  | .page _ _, .page _ _ => .invalid

private theorem signature_comm (x y : V) : signature x y = signature y x := by
  cases x <;> cases y <;> first | rfl | exact coreKey_comm _ _ _ _

private def key : Label → Key
  | .book b j => .book b j.val
  | .page b j side => .page b j.val side
  | .matching r j => .matching r j.val
  | .logical e => .logical s(e.fromRole,e.toRole)

private theorem signature_ends (l : Label) : signature (ends l).1 (ends l).2 = key l := by
  classical
  cases l with
  | book b j =>
    obtain ⟨hlt, _, _, hord⟩ := ord_bounds (blockSize_three Code b) j.isLt
    simp only [ends, signature, key, coreKey, if_pos rfl, if_true, lo, hi,
      Nat.min_eq_left (Nat.le_of_lt hlt), Nat.max_eq_right (Nat.le_of_lt hlt), hord]
  | page b j side =>
    cases side
    · simp [ends, signature, key]
    · have hn := Nat.ne_of_gt (pageLo_lt_hi Code b j)
      simp [ends, signature, key, hn]
  | matching r j => simp [ends, signature, key, coreKey, hubIdx]
  | logical e =>
    have hn : Block.primary e.fromRole ≠ Block.primary e.toRole :=
      fun h => e.distinct (Block.primary.inj h)
    simp [ends, signature, key, portPoint, coreKey, hn]

private theorem logical_key : ∀ e e' : TypedRound.Edge,
    s(e.fromRole,e.toRole) = s(e'.fromRole,e'.toRole) → e = e' := by decide

private theorem key_injective : Function.Injective key := by
  intro x y h
  cases x <;> cases y <;> try contradiction
  case book.book b j d k =>
    obtain ⟨rfl, he⟩ := Key.book.inj h
    exact congrArg (Label.book b) (Fin.ext he)
  case page.page b j side d k side' =>
    obtain ⟨rfl, he, rfl⟩ := Key.page.inj h
    exact congrArg (fun t => Label.page b t side) (Fin.ext he)
  case matching.matching r j s k =>
    obtain ⟨rfl, he⟩ := Key.matching.inj h
    exact congrArg (Label.matching r) (Fin.ext he)
  case logical.logical e f => exact congrArg Label.logical (logical_key e f (Key.logical.inj h))

private theorem signature_eq_of_sym {a b c d : V} (h : s(a,b) = s(c,d)) :
    signature a b = signature c d := by
  rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact signature_comm _ _

private theorem encoded_injective : Function.Injective encoded := by
  intro x y h
  apply key_injective
  rw [← signature_ends x, ← signature_ends y]
  exact signature_eq_of_sym h

private theorem encoded_mem (l : Label) : encoded l ∈ H.edgeSet := by
  change H.Adj (ends l).1 (ends l).2
  cases l with
  | book b j =>
    obtain ⟨hlt, _, hl, _⟩ := ord_bounds (blockSize_three Code b) j.isLt
    exact Or.inl (.book b _ _ ⟨fun e => (Nat.ne_of_lt hlt) (congrArg Fin.val e), Or.inl hl⟩)
  | page b j side =>
    cases side
    · exact Or.inl (.pageLeft b j)
    · exact Or.inl (.pageRight b j)
  | matching r j => exact Or.inl (.matching r j)
  | logical e => exact Or.inl (.logical _ _ ⟨e, Or.inl ⟨rfl,rfl⟩⟩)

private theorem cover_ordered {b : Block Role} {a d : Fin (blockSize Code b)}
    (ha : a.val < 2) (had : a.val < d.val) :
    ∃ l, encoded l = s((Vertex.core b a : V), Vertex.core b d) := by
  obtain ⟨hb, hlow, hhigh⟩ := ord_spec (blockSize_three Code b) ha had d.isLt
  let j : Num b := ⟨ordinal (blockSize Code b) a.val d.val, hb⟩
  have hl : lo b j = a := Fin.ext hlow
  have hh : hi b j = d := Fin.ext hhigh
  refine ⟨.book b j, ?_⟩
  change s(Vertex.core b (lo b j), Vertex.core b (hi b j)) = _
  rw [hl, hh]

private theorem arc_covered {x y : V} (h : Arc TypedRound.rule Code Port x y) :
    ∃ l, encoded l = s(x,y) := by
  cases h with
  | book b a d he =>
    have hn : a.val ≠ d.val := fun hh => he.1 (Fin.ext hh)
    by_cases hd : a.val < d.val
    · exact cover_ordered (by rcases he.2 with hh | hh <;> omega) hd
    · obtain ⟨l, hl⟩ := cover_ordered (b := b) (a := d) (d := a)
        (by rcases he.2 with hh | hh <;> omega) (by omega)
      exact ⟨l, hl.trans Sym2.eq_swap⟩
  | pageLeft b j => exact ⟨.page b j false, rfl⟩
  | pageRight b j => exact ⟨.page b j true, rfl⟩
  | matching r j => exact ⟨.matching r j, rfl⟩
  | logical r s h =>
    obtain ⟨e, hp⟩ := h
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨.logical e, rfl⟩
    · exact ⟨.logical e, Sym2.eq_swap⟩

private def asEdge (l : Label) : H.edgeSet := ⟨encoded l, encoded_mem l⟩

private theorem asEdge_bijective : Function.Bijective asEdge := by
  constructor
  · intro x y h
    exact encoded_injective (congrArg Subtype.val h)
  · rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
      change H.Adj x y at he
      rcases he with h | h
      · obtain ⟨l, hl⟩ := arc_covered h
        exact ⟨l, Subtype.ext hl⟩
      · obtain ⟨l, hl⟩ := arc_covered h
        exact ⟨l, Subtype.ext (hl.trans Sym2.eq_swap)⟩

private abbrev Local (r : Role) :=
  (Num (.primary r) ⊕ Num (.secondary r)) ⊕
   (((Fin (pageCount Code (.primary r)) × Bool) ⊕
     (Fin (pageCount Code (.secondary r)) × Bool)) ⊕ Fin 2)

private def labelEquiv : Label ≃ ((r : Role) × Local r) ⊕ TypedRound.Edge where
  toFun
    | .book (.primary r) j => .inl ⟨r, .inl (.inl j)⟩
    | .book (.secondary r) j => .inl ⟨r, .inl (.inr j)⟩
    | .page (.primary r) k s => .inl ⟨r, .inr (.inl (.inl (k,s)))⟩
    | .page (.secondary r) k s => .inl ⟨r, .inr (.inl (.inr (k,s)))⟩
    | .matching r j => .inl ⟨r, .inr (.inr j)⟩
    | .logical e => .inr e
  invFun
    | .inl ⟨r, .inl (.inl j)⟩ => .book (.primary r) j
    | .inl ⟨r, .inl (.inr j)⟩ => .book (.secondary r) j
    | .inl ⟨r, .inr (.inl (.inl (k,s)))⟩ => .page (.primary r) k s
    | .inl ⟨r, .inr (.inl (.inr (k,s)))⟩ => .page (.secondary r) k s
    | .inl ⟨r, .inr (.inr j)⟩ => .matching r j
    | .inr e => .logical e
  left_inv := by
    intro l
    cases l with
    | book b j => cases b <;> rfl
    | page b j s => cases b <;> rfl
    | matching | logical => rfl
  right_inv := by
    rintro (⟨r, (j | j) | ((⟨k,s⟩ | ⟨k,s⟩) | j)⟩ | e) <;> rfl

private theorem local_card (r : Role) : Fintype.card (Local r) = 27740 := by
  simp only [Local, Num, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    pageCount, blockSize]
  have ht := (Code r).isLt
  omega

private noncomputable def allEquiv : Label ≃ (Role × Fin 27740) ⊕ TypedRound.Edge :=
  labelEquiv.trans (Equiv.sumCongr (Equiv.sigmaEquivProdOfEquiv fun r =>
    Fintype.equivFinOfCardEq (local_card r)) (Equiv.refl _))

private noncomputable instance : Fintype Label := Fintype.ofEquiv _ allEquiv.symm

open scoped Classical in
/-- Each undirected ordinary edge has exactly one of the labels counted above. -/
theorem source_edge_count :
    (Localization.rule TypedRound.rule MarkedSimulation.sourceCode MarkedSimulation.port).edgeFinset.card
      = 332894 := by
  classical
  let e := Equiv.ofBijective asEdge asEdge_bijective
  rw [SimpleGraph.edgeFinset_card, ← Fintype.card_congr e, Fintype.card_congr allEquiv,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, TypedRound.rule_counts.1,
    TypedRound.rule_counts.2.1]

end Bootstrap.RuleEdgeCount

#print axioms Bootstrap.RuleEdgeCount.source_edge_count
