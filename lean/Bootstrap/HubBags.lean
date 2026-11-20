import Bootstrap.TreeConstruction
import Bootstrap.RuleBooks
import Bootstrap.MarkerMaps

/-! An explicit tree decomposition of the 48 book hubs. All finite certificate checks
are reduced by the Lean kernel. Additional core vertices and pages are attached separately. -/
namespace Bootstrap.SourceBags

open TreeBags Localization MarkedSimulation

abbrev HVertex := HostVertex sourceCode

private instance : DecidableEq (Block TypedRound.Role)
  | .primary i, .primary j => decidable_of_iff (i = j) ⟨congrArg Block.primary,Block.primary.inj⟩
  | .secondary i, .secondary j => decidable_of_iff (i = j) ⟨congrArg Block.secondary,Block.secondary.inj⟩
  | .primary _, .secondary _ => isFalse (by intro h; cases h)
  | .secondary _, .primary _ => isFalse (by intro h; cases h)

def baseRoot : Finset (Fin 48) := {47}

def baseRows : List (Finset (Fin 48) × Finset (Fin 48)) := [
  ({47}, {46,47}),
  ({46,47}, {45,46,47}),
  ({45,46,47}, {44,45,46}),
  ({44,45,46}, {41,44,45}),
  ({41,44,45}, {40,41,44}),
  ({40,41,44}, {43,40,41}),
  ({43,40,41}, {42,40,43}),
  ({40,41,44}, {13,40,44}),
  ({13,40,44}, {9,13,40}),
  ({9,13,40}, {37,9,13}),
  ({37,9,13}, {36,13,37}),
  ({36,13,37}, {39,36,37}),
  ({39,36,37}, {38,36,39}),
  ({37,9,13}, {33,9,37}),
  ({33,9,37}, {32,9,33}),
  ({32,9,33}, {35,32,33}),
  ({35,32,33}, {34,32,35}),
  ({9,13,40}, {5,9,13}),
  ({5,9,13}, {1,5,9}),
  ({1,5,9}, {29,1,5}),
  ({29,1,5}, {28,5,29}),
  ({28,5,29}, {31,28,29}),
  ({31,28,29}, {30,28,31}),
  ({29,1,5}, {25,1,29}),
  ({25,1,29}, {24,1,25}),
  ({24,1,25}, {27,24,25}),
  ({27,24,25}, {26,24,27}),
  ({1,5,9}, {21,1,5}),
  ({21,1,5}, {20,5,21}),
  ({20,5,21}, {23,20,21}),
  ({23,20,21}, {22,20,23}),
  ({21,1,5}, {17,1,21}),
  ({17,1,21}, {16,1,17}),
  ({16,1,17}, {19,16,17}),
  ({19,16,17}, {18,16,19}),
  ({5,9,13}, {12,5,13}),
  ({12,5,13}, {15,12,13}),
  ({15,12,13}, {14,12,15}),
  ({1,5,9}, {8,1,9}),
  ({8,1,9}, {11,8,9}),
  ({11,8,9}, {10,8,11}),
  ({12,5,13}, {4,5,12}),
  ({4,5,12}, {7,4,5}),
  ({7,4,5}, {6,4,7}),
  ({8,1,9}, {0,1,8}),
  ({0,1,8}, {3,0,1}),
  ({3,0,1}, {2,0,3}) ]

def baseBags : Finset (Finset (Fin 48)) := rowsResult {baseRoot} baseRows

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem baseTree : Tree 2 baseBags := rows_sound (Tree.root _ (by decide)) baseRows (by decide)

def baseIndex (b : Block TypedRound.Role) (k : Fin 2) : Fin 48 :=
  match b with
  | .primary r => ⟨4*(roleOrdinal r).val + k.val, by have := (roleOrdinal r).isLt; have := k.isLt; omega⟩
  | .secondary r => ⟨4*(roleOrdinal r).val + 2 + k.val, by have := (roleOrdinal r).isLt; have := k.isLt; omega⟩

private def ordinalRole (i : Nat) : TypedRound.Role :=
  match i with
  | 0 => .inl (.endpoint false)
  | 1 => .inl (.endpoint true)
  | 2 => .inr (.endpoint false)
  | 3 => .inr (.endpoint true)
  | 4 => .inl (.u false)
  | 5 => .inl (.v false)
  | 6 => .inl (.u true)
  | 7 => .inl (.v true)
  | 8 => .inr (.u false)
  | 9 => .inr (.v false)
  | 10 => .inr (.u true)
  | _ => .inr (.v true)

def decodeBlock (i : Fin 48) : Block TypedRound.Role :=
  if i.val % 4 < 2 then .primary (ordinalRole (i.val / 4)) else .secondary (ordinalRole (i.val / 4))

def decodeSlot (i : Fin 48) : Fin 2 := ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩

private theorem decode_encode_aux (r : TypedRound.Role) (k : Fin 2) :
    (decodeBlock (baseIndex (.primary r) k) = .primary r ∧ decodeSlot (baseIndex (.primary r) k) = k) ∧
    (decodeBlock (baseIndex (.secondary r) k) = .secondary r ∧ decodeSlot (baseIndex (.secondary r) k) = k) := by
  have hr : ∀ s : TypedRound.Role, ∀ j : Fin 2,
      (decodeBlock (baseIndex (.primary s) j) = .primary s ∧ decodeSlot (baseIndex (.primary s) j) = j) ∧
      (decodeBlock (baseIndex (.secondary s) j) = .secondary s ∧ decodeSlot (baseIndex (.secondary s) j) = j) := by
    decide
  exact hr r k

private theorem encode_decode :
    ∀ i : Fin 48, baseIndex (decodeBlock i) (decodeSlot i) = i := by decide

def hub (b : Block TypedRound.Role) (k : Fin 2) : HVertex := .core b (hubIdx sourceCode b k)

private theorem hub_pair_injective {b d : Block TypedRound.Role} {j k : Fin 2}
    (h : hub b j = hub d k) : b = d ∧ j = k := by
  have e : b = d := congrArg owner h
  subst d
  have s := (coreEmbedding _ _ b).injective h
  exact ⟨rfl,Fin.ext (congrArg (fun t : Fin (blockSize sourceCode b) => t.val) s)⟩

def hubMap : Fin 48 ↪ HVertex where
  toFun i := hub (decodeBlock i) (decodeSlot i)
  inj' := by
    intro i j eq
    have h := hub_pair_injective eq
    rw [← encode_decode i, ← encode_decode j]
    exact congrArg₂ baseIndex h.1 h.2

@[simp] theorem hubMap_index (b : Block TypedRound.Role) (k : Fin 2) :
    hubMap (baseIndex b k) = hub b k := by
  change hub (decodeBlock (baseIndex b k)) (decodeSlot (baseIndex b k)) = _
  cases b with
  | primary r =>
    have h := (decode_encode_aux r k).1
    rw [h.1,h.2]
  | secondary r =>
    have h := (decode_encode_aux r k).2
    rw [h.1,h.2]

/-- The direct finite check only enumerates the base hubs and 14 logical edges. -/
private def share (a b : Fin 48) : Bool :=
  decide (∃ s ∈ baseBags, a ∈ s ∧ b ∈ s)

private theorem share_sound {a b : Fin 48} (h : share a b = true) : TreeBags.Together baseBags a b := by
  change ∃ s ∈ baseBags, a ∈ s ∧ b ∈ s
  exact of_decide_eq_true h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
private theorem hubPairs : ∀ r : TypedRound.Role,
    share (baseIndex (.primary r) 0) (baseIndex (.primary r) 1) = true ∧
    share (baseIndex (.secondary r) 0) (baseIndex (.secondary r) 1) = true ∧
    ∀ k : Fin 2, share (baseIndex (.primary r) k) (baseIndex (.secondary r) k) = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
private theorem logicalPairs : ∀ e : TypedRound.Edge,
    share (baseIndex (.primary e.fromRole) (port e.fromRole e.toRole))
      (baseIndex (.primary e.toRole) (port e.toRole e.fromRole)) = true := by decide

open scoped Classical in
noncomputable def hubs : Finset (Finset HVertex) := baseBags.image (fun b => b.map hubMap)

open scoped Classical in
theorem hubs_tree : Tree 2 hubs := map_tree baseTree hubMap

theorem hub_pair {i j : Fin 48} (h : Together baseBags i j) : Together hubs (hubMap i) (hubMap j) := by
  classical
  obtain ⟨b,hb,hi,hj⟩ := h
  exact ⟨b.map hubMap, Finset.mem_image_of_mem _ hb, Finset.mem_map_of_mem _ hi, Finset.mem_map_of_mem _ hj⟩

theorem base_edge (b : Block TypedRound.Role) : Together hubs (hub b 0) (hub b 1) := by
  cases b with
  | primary r => simpa using hub_pair (share_sound (hubPairs r).1)
  | secondary r => simpa using hub_pair (share_sound (hubPairs r).2.1)

theorem matching_edge (r : TypedRound.Role) (k : Fin 2) :
    Together hubs (hub (.primary r) k) (hub (.secondary r) k) := by
  simpa using hub_pair (share_sound ((hubPairs r).2.2 k))

theorem logical_edge {r s : TypedRound.Role} (adj : TypedRound.rule.Adj r s) :
    Together hubs (portPoint sourceCode port r s) (portPoint sourceCode port s r) := by
  obtain ⟨e, d | d⟩ := adj
  · rcases d with ⟨rfl,rfl⟩
    simpa [hub,portPoint,portIdx] using hub_pair (share_sound (logicalPairs e))
  · rcases d with ⟨rfl,rfl⟩
    simpa [hub,portPoint,portIdx] using together_symm (hub_pair (share_sound (logicalPairs e)))

theorem only_hubs {v : HVertex} (seen : Occurs hubs v) :
    ∃ (b : Block TypedRound.Role) (k : Fin 2), v = hub b k := by
  classical
  obtain ⟨bag,hbag,hv⟩ := seen
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hbag
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hv
  exact ⟨decodeBlock i,decodeSlot i,rfl⟩

end Bootstrap.SourceBags

#print axioms Bootstrap.SourceBags.hubs_tree
#print axioms Bootstrap.SourceBags.logical_edge
