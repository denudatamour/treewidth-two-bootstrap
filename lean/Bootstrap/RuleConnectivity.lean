import Bootstrap.RuleBooks
import Bootstrap.MarkerMaps
import Mathlib.Combinatorics.SimpleGraph.Path

namespace Bootstrap.RuleConnectivity

open Localization
variable {V : Type*}

private abbrev Without (G : SimpleGraph V) (z : V) := G.induce {x | x ≠ z}

private def Avoid (G : SimpleGraph V) (z x y : V) : Prop :=
  ∃ (hx : x ≠ z) (hy : y ≠ z), (Without G z).Reachable ⟨x, hx⟩ ⟨y, hy⟩

private theorem Avoid.refl {G : SimpleGraph V} {z x : V} (h : x ≠ z) : Avoid G z x x :=
  ⟨h, h, SimpleGraph.Reachable.refl _⟩

private theorem Avoid.adj {G : SimpleGraph V} {z x y : V} (h : G.Adj x y)
    (hx : x ≠ z) (hy : y ≠ z) : Avoid G z x y :=
  ⟨hx, hy, (show (Without G z).Adj ⟨x,hx⟩ ⟨y,hy⟩ from h).reachable⟩

private theorem Avoid.trans {G : SimpleGraph V} {z x y w : V} (h : Avoid G z x y)
    (h' : Avoid G z y w) : Avoid G z x w := by
  obtain ⟨hx, _, hxy⟩ := h
  obtain ⟨_, hw, hyw⟩ := h'
  exact ⟨hx, hw, hxy.trans hyw⟩

private theorem Avoid.symm {G : SimpleGraph V} {z x y : V} (h : Avoid G z x y) : Avoid G z y x := by
  obtain ⟨hx, hy, hxy⟩ := h
  exact ⟨hy, hx, hxy.symm⟩

private theorem segment {n : Nat} (G : SimpleGraph V) (z : V) (f : Fin (n+1) → V)
    (h : ∀ a b, a.val + 1 = b.val → G.Adj (f a) (f b)) (i j : Fin (n+1))
    (hle : i.val ≤ j.val) (hs : ∀ k : Fin (n+1), i.val ≤ k.val → k.val ≤ j.val → f k ≠ z) :
    Avoid G z (f i) (f j) := by
  induction j using Fin.induction with
  | zero =>
    have he : i = 0 := Fin.ext (by change i.val = 0; change i.val ≤ 0 at hle; omega)
    subst i
    exact Avoid.refl (hs 0 (Nat.le_refl _) (Nat.le_refl _))
  | succ j ih =>
    by_cases he : i = j.succ
    · subst i
      exact Avoid.refl (hs _ (by omega) (by omega))
    · have hne : i.val ≠ j.val + 1 := fun hh => he (Fin.ext hh)
      have hi : i.val ≤ j.val := by change i.val ≤ j.val + 1 at hle; omega
      have hj : j.castSucc.val ≤ j.succ.val := by change j.val ≤ j.val+1; omega
      exact (ih hi (fun k hk hk' => hs k hk (Nat.le_trans hk' hj))).trans
        (Avoid.adj (h j.castSucc j.succ rfl) (hs _ hi hj) (hs _ hle (by omega)))

private theorem ordered_cycle {n : Nat} (G : SimpleGraph V) (z : V) (f : Fin (n+1) ↪ V)
    (edges : ∀ a b, a.val + 1 = b.val → G.Adj (f a) (f b))
    (wrap : G.Adj (f (Fin.last n)) (f 0)) (i j : Fin (n+1))
    (hle : i.val ≤ j.val) (hi : f i ≠ z) (hj : f j ≠ z) : Avoid G z (f i) (f j) := by
  classical
  by_cases hc : ∃ k, f k = z
  · obtain ⟨r, hr⟩ := hc
    have ei : i.val ≠ r.val := fun he => hi ((congrArg f (Fin.ext he)).trans hr)
    have ej : j.val ≠ r.val := fun he => hj ((congrArg f (Fin.ext he)).trans hr)
    have safe (k : Fin (n+1)) (he : k.val ≠ r.val) : f k ≠ z := fun hz =>
      he (congrArg Fin.val (f.injective (hz.trans hr.symm)))
    by_cases hm : i.val < r.val ∧ r.val < j.val
    · have hlast : (Fin.last n).val = n := rfl
      have hzero : (0 : Fin (n+1)).val = 0 := rfl
      have hbound := j.isLt
      have lower := segment G z f edges 0 i (by omega) (fun k _ hk => safe k (by omega))
      have upper := segment G z f edges j (Fin.last n) (by omega) (fun k hk _ => safe k (by omega))
      have back := Avoid.adj wrap (safe _ (by omega)) (safe _ (by omega))
      exact (lower.symm.trans back.symm).trans upper.symm
    · exact segment G z f edges i j hle (fun k hk hk' => safe k (by omega))
  · exact segment G z f edges i j hle (fun k _ _ hk => hc ⟨k,hk⟩)

private theorem along_cycle {n : Nat} (G : SimpleGraph V) (z : V) (f : Fin (n+1) ↪ V)
    (edges : ∀ a b, a.val + 1 = b.val → G.Adj (f a) (f b))
    (wrap : G.Adj (f (Fin.last n)) (f 0)) (i j : Fin (n+1))
    (hi : f i ≠ z) (hj : f j ≠ z) : Avoid G z (f i) (f j) := by
  by_cases h : i.val ≤ j.val
  · exact ordered_cycle G z f edges wrap i j h hi hj
  · exact (ordered_cycle G z f edges wrap j i (by omega) hj hi).symm

private abbrev Role := TypedRound.Role
private abbrev Tag := Role × Fin 2
private abbrev Code := MarkedSimulation.sourceCode
private abbrev H := Localization.rule TypedRound.rule Code MarkedSimulation.port

private def tagMap : Tag ↪ HostVertex Code where
  toFun x := .core (.primary x.1) (hubIdx Code (.primary x.1) x.2)
  inj' := by
    intro a b he
    exact Prod.ext (Block.primary.inj (congrArg Localization.owner he))
      (Fin.ext (congrArg MarkedSimulation.vindex he))

private def tagAdj (x y : Tag) : Prop :=
  (x.1 = y.1 ∧ x.2 ≠ y.2) ∨ (TypedRound.rule.Adj x.1 y.1 ∧
    x.2 = MarkedSimulation.port x.1 y.1 ∧ y.2 = MarkedSimulation.port y.1 x.1)

private instance (r s : Role) : Decidable (TypedRound.rule.Adj r s) :=
  inferInstanceAs (Decidable (∃ e : TypedRound.Edge, TypedRound.Pair r s e.fromRole e.toRole))

private instance (x y : Tag) : Decidable (tagAdj x y) := by unfold tagAdj; infer_instance

private theorem tagAdj_edge {x y : Tag} (h : tagAdj x y) : H.Adj (tagMap x) (tagMap y) := by
  rcases x with ⟨r,k⟩
  rcases y with ⟨s,l⟩
  rcases h with ⟨he,hkl⟩ | ⟨hL,hk,hl⟩
  · change r = s at he
    subst s
    apply Or.inl
    apply Arc.book
    change k ≠ l at hkl
    exact ⟨fun he' => hkl (Fin.ext (congrArg (@Fin.val (blockSize Code (.primary r))) he')), Or.inl k.isLt⟩
  · change k = MarkedSimulation.port r s at hk
    change l = MarkedSimulation.port s r at hl
    subst k
    subst l
    exact Or.inl (.logical r s hL)

/-- One track on each side, both cross edges, and the subdividing primary hubs. -/
private def ring (a b : Bool) (i : Fin 16) : Tag :=
  let entries : Array Tag := #[
    (.inl (.endpoint false),0), (.inl (.endpoint false),1),
    (.inl (.u a),0), (.inl (.u a),1), (.inl (.v a),1), (.inl (.v a),0),
    (.inl (.endpoint true),1), (.inl (.endpoint true),0),
    (.inr (.endpoint true),0), (.inr (.endpoint true),1),
    (.inr (.v b),0), (.inr (.v b),1), (.inr (.u b),1), (.inr (.u b),0),
    (.inr (.endpoint false),1), (.inr (.endpoint false),0)]
  entries[i.val]'(by exact i.isLt)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem ring_checks :
    (∀ a b : Bool, ∀ i j : Fin 16, ring a b i = ring a b j → i = j) ∧
    (∀ a b : Bool, ∀ i j : Fin 16, i.val + 1 = j.val → tagAdj (ring a b i) (ring a b j)) ∧
    (∀ a b : Bool, tagAdj (ring a b 15) (ring a b 0)) ∧
    (∀ x : Tag, ∃ a b : Bool, ∃ i : Fin 16, ring a b i = x) := by
  decide

private def ringEmb (a b : Bool) : Fin 16 ↪ HostVertex Code :=
  (⟨ring a b, fun {i j} h => ring_checks.1 a b i j h⟩ : Fin 16 ↪ Tag).trans tagMap

private theorem along_ring (z : HostVertex Code) (a b : Bool) (i j : Fin 16)
    (hi : tagMap (ring a b i) ≠ z) (hj : tagMap (ring a b j) ≠ z) :
    Avoid H z (tagMap (ring a b i)) (tagMap (ring a b j)) :=
  along_cycle H z (ringEmb a b) (fun s t he => tagAdj_edge (ring_checks.2.1 a b s t he))
    (tagAdj_edge (ring_checks.2.2.1 a b)) i j hi hj

private theorem hubs_connect (z : HostVertex Code) (x y : Tag)
    (hx : tagMap x ≠ z) (hy : tagMap y ≠ z) : Avoid H z (tagMap x) (tagMap y) := by
  obtain ⟨a,b,i,rfl⟩ := ring_checks.2.2.2 x
  obtain ⟨a',b',j,rfl⟩ := ring_checks.2.2.2 y
  by_cases h : tagMap (ring a b 0) = z
  · have hn : tagMap (ring a b 1) ≠ z := by
      intro h'
      have he := tagMap.injective (h.trans h'.symm)
      have : (0 : Fin 2) = 1 := congrArg Prod.snd he
      exact (by decide : (0 : Fin 2) ≠ 1) this
    exact (along_ring z a b i 1 hx hn).trans (along_ring z a' b' 1 j hn hy)
  · exact (along_ring z a b i 0 hx h).trans (along_ring z a' b' 0 j h hy)

private def safeBit (z : HostVertex Code) : Fin 2 := if MarkedSimulation.vindex z = 0 then 1 else 0

private theorem safeHub (z : HostVertex Code) (b : Block Role) :
    (Vertex.core b (hubIdx Code b (safeBit z)) : HostVertex Code) ≠ z := by
  intro he
  have h := congrArg MarkedSimulation.vindex he
  change (safeBit z).val = MarkedSimulation.vindex z at h
  unfold safeBit at h
  split at h <;> simp_all

private theorem core_to_local (z : HostVertex Code) (b : Block Role) (a : Fin (blockSize Code b))
    (h : Vertex.core b a ≠ z) :
    Avoid H z (.core b a) (.core b (hubIdx Code b (safeBit z))) := by
  by_cases he : a = hubIdx Code b (safeBit z)
  · subst a; exact Avoid.refl h
  · exact Avoid.adj (Or.inl (.book b _ _ ⟨he, Or.inr (safeBit z).isLt⟩)) h (safeHub z b)

private theorem core_to_hub (z : HostVertex Code) (b : Block Role) (a : Fin (blockSize Code b))
    (h : Vertex.core b a ≠ z) : ∃ x : Tag, Avoid H z (.core b a) (tagMap x) := by
  cases b with
  | primary r => exact ⟨(r, safeBit z), core_to_local z _ a h⟩
  | secondary r =>
    exact ⟨(r, safeBit z), (core_to_local z _ a h).trans
      (Avoid.adj (Or.inr (.matching r (safeBit z))) (safeHub z _) (safeHub z _))⟩

private theorem to_hub (z x : HostVertex Code) (hx : x ≠ z) :
    ∃ u : Tag, Avoid H z x (tagMap u) := by
  cases x with
  | core b a => exact core_to_hub z b a hx
  | page b k =>
    by_cases he : Vertex.core b (pageLo Code b k) = z
    · have hs : Vertex.core b (pageHi Code b k) ≠ z := by
        intro h'
        have hv := congrArg MarkedSimulation.vindex (he.trans h'.symm)
        exact (Nat.ne_of_lt (pageLo_lt_hi Code b k)) hv
      obtain ⟨u, hu⟩ := core_to_hub z _ _ hs
      exact ⟨u, (Avoid.adj (Or.inl (.pageRight b k)) hx hs).trans hu⟩
    · obtain ⟨u, hu⟩ := core_to_hub z _ _ he
      exact ⟨u, (Avoid.adj (Or.inl (.pageLeft b k)) hx he).trans hu⟩

/-- The actual fixed source is connected after deletion of each individual vertex. -/
theorem source_deleted_connected (z : HostVertex MarkedSimulation.sourceCode) :
    ((Localization.rule TypedRound.rule MarkedSimulation.sourceCode MarkedSimulation.port).induce
      {x | x ≠ z}).Connected := by
  letI hn : Nonempty {x : HostVertex Code // x ≠ z} :=
    ⟨⟨_, safeHub z (.primary (.inl (.endpoint false)))⟩⟩
  refine @SimpleGraph.Connected.mk _ _ ?_ hn
  intro x y
  obtain ⟨a, xa⟩ := to_hub z x.val x.property
  obtain ⟨b, yb⟩ := to_hub z y.val y.property
  have ha : tagMap a ≠ z := xa.choose_spec.choose
  have hb : tagMap b ≠ z := yb.choose_spec.choose
  obtain ⟨_, _, walk⟩ := (xa.trans (hubs_connect z a b ha hb)).trans yb.symm
  exact walk

/-- The fixed source itself is connected. -/
theorem source_connected :
    (Localization.rule TypedRound.rule MarkedSimulation.sourceCode MarkedSimulation.port).Connected := by
  let b : Block Role := .primary (.inl (.endpoint false))
  letI hn : Nonempty (HostVertex Code) := ⟨.core b (hubIdx Code b 0)⟩
  refine @SimpleGraph.Connected.mk _ _ ?_ hn
  intro x y
  have hthird : ∃ k : Fin 3, k.val ≠ MarkedSimulation.vindex x ∧ k.val ≠ MarkedSimulation.vindex y := by
    by_cases h₀ : 0 ≠ MarkedSimulation.vindex x ∧ 0 ≠ MarkedSimulation.vindex y
    · exact ⟨0, h₀⟩
    by_cases h₁ : 1 ≠ MarkedSimulation.vindex x ∧ 1 ≠ MarkedSimulation.vindex y
    · exact ⟨1, h₁⟩
    · exact ⟨2, by change 2 ≠ _ ∧ 2 ≠ _; omega⟩
  obtain ⟨k, hx, hy⟩ := hthird
  let a : Fin (blockSize Code b) := ⟨k.val, Nat.lt_of_lt_of_le k.isLt (blockSize_three Code b)⟩
  let z : HostVertex Code := .core b a
  have hzx : x ≠ z := fun e => hx (congrArg MarkedSimulation.vindex e.symm)
  have hzy : y ≠ z := fun e => hy (congrArg MarkedSimulation.vindex e.symm)
  let inc : Without H z →g H := ⟨Subtype.val, fun h => h⟩
  exact ((source_deleted_connected z).preconnected ⟨x,hzx⟩ ⟨y,hzy⟩).map inc

end Bootstrap.RuleConnectivity

#print axioms Bootstrap.RuleConnectivity.source_deleted_connected
#print axioms Bootstrap.RuleConnectivity.source_connected
