import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Lean.Elab.Tactic.Omega

/-! A type-preserving round of the twelve-vertex auxiliary rule (Lemma III.2). -/
namespace TypedRound

inductive LocalRole where
  | endpoint (atEnd : Bool)
  | u (track : Bool)
  | v (track : Bool)
  deriving DecidableEq

inductive Kind where
  | endpoint
  | u (track : Bool)
  | v (track : Bool)
  deriving DecidableEq

def LocalRole.kind : LocalRole → Kind
  | .endpoint _ => .endpoint
  | .u k => .u k
  | .v k => .v k

abbrev Role := LocalRole ⊕ LocalRole
abbrev Host (A B : Type*) := (Kind × A) ⊕ (Kind × B)

def roleType : Role → Kind ⊕ Kind := Sum.map LocalRole.kind LocalRole.kind
def hostType {A B : Type*} : Host A B → Kind ⊕ Kind := Sum.map Prod.fst Prod.fst

inductive Segment where
  | first | middle | last
  deriving DecidableEq

def Segment.fromRole : Segment → Bool → LocalRole
  | .first, _ => .endpoint false
  | .middle, k => .u k
  | .last, k => .v k

def Segment.toRole : Segment → Bool → LocalRole
  | .first, k => .u k
  | .middle, k => .v k
  | .last, _ => .endpoint true

inductive Edge where
  | xTrack (track : Bool) (segment : Segment)
  | yTrack (track : Bool) (segment : Segment)
  | cross (atEnd : Bool)
  deriving DecidableEq

def Edge.fromRole : Edge → Role
  | .xTrack k t => .inl (t.fromRole k)
  | .yTrack k t => .inr (t.fromRole k)
  | .cross b => .inl (.endpoint b)

def Edge.toRole : Edge → Role
  | .xTrack k t => .inl (t.toRole k)
  | .yTrack k t => .inr (t.toRole k)
  | .cross b => .inr (.endpoint b)

theorem Edge.distinct (e : Edge) : e.fromRole ≠ e.toRole := by
  cases e with
  | xTrack k t => cases t <;> simp [Edge.fromRole, Edge.toRole, Segment.fromRole, Segment.toRole]
  | yTrack k t => cases t <;> simp [Edge.fromRole, Edge.toRole, Segment.fromRole, Segment.toRole]
  | cross b => simp [Edge.fromRole, Edge.toRole]

def Pair {V : Type*} (x y a b : V) : Prop :=
  (x = a ∧ y = b) ∨ (x = b ∧ y = a)

theorem Pair.swap {V : Type*} {x y a b : V} (h : Pair x y a b) : Pair y x a b := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl⟩

def rule : SimpleGraph Role where
  Adj u v := ∃ e : Edge, Pair u v e.fromRole e.toRole
  symm := by rintro _ _ ⟨e, h⟩; exact ⟨e, h.swap⟩
  loopless := by
    rintro u ⟨e, ⟨h,h'⟩ | ⟨h,h'⟩⟩
    · exact e.distinct (h.symm.trans h')
    · exact e.distinct (h'.symm.trans h)

variable {A B : Type*}

def xEnd (i : A) : Host A B := .inl (.endpoint, i)
def yEnd (j : B) : Host A B := .inr (.endpoint, j)

/-- A path occurrence from its initial endpoint to its successor, before symmetrising. -/
def pathArc (next : A → A) : Kind × A → Kind × A → Prop
  | (.endpoint,i), (.u _,j) => i = j
  | (.u k,i), (.v l,j) => k = l ∧ i = j
  | (.v _,i), (.endpoint,j) => next i = j
  | _, _ => False

def fixedArc (sx : A → A) (sy : B → B) : Host A B → Host A B → Prop
  | .inl x, .inl y => pathArc sx x y
  | .inr x, .inr y => pathArc sy x y
  | _, _ => False

def host (sx : A → A) (sy : B → B) (E : A → B → Prop) : SimpleGraph (Host A B) where
  Adj a b := (fixedArc sx sy a b ∨ fixedArc sx sy b a) ∨
      ∃ i j, E i j ∧ Pair a b (xEnd i) (yEnd j)
  symm := by
    rintro a b ((h|h)|⟨i,j,h,hp⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨i,j,h,hp.swap⟩
  loopless := by
    rintro a ((h|h)|⟨i,j,_, ⟨h,h'⟩ | ⟨h,h'⟩⟩)
    · rcases a with ⟨k,i⟩ | ⟨k,j⟩ <;> cases k <;> exact h
    · rcases a with ⟨k,i⟩ | ⟨k,j⟩ <;> cases k <;> exact h
    · cases h.symm.trans h'
    · cases h'.symm.trans h

structure Positions (A B : Type*) where
  x : LocalRole → A
  y : LocalRole → B

def Positions.image (w : Positions A B) : Role → Host A B :=
  Sum.map (fun r => (r.kind,w.x r)) (fun r => (r.kind,w.y r))

def Preserves (f : Role → Host A B) : Prop := ∀ r, hostType (f r) = roleType r

theorem Positions.preserves (w : Positions A B) : Preserves w.image := by
  rintro (r|r) <;> rfl

/-- Positions are coordinates for all type-preserving maps. No incidence is assumed here. -/
theorem positions_of_preserves {f : Role → Host A B} (h : Preserves f) :
    ∃ w : Positions A B, f = w.image := by
  have hx (r : LocalRole) : ∃ i : A, f (.inl r) = .inl (r.kind,i) := by
    have ht := h (.inl r)
    rcases he : f (.inl r) with ⟨k,i⟩ | ⟨k,j⟩
    · have hk : k = r.kind := by simpa [hostType, roleType, he] using ht
      exact ⟨i, by rw [hk]⟩
    · simp [hostType, roleType, he] at ht
  have hy (r : LocalRole) : ∃ j : B, f (.inr r) = .inr (r.kind,j) := by
    have ht := h (.inr r)
    rcases he : f (.inr r) with ⟨k,i⟩ | ⟨k,j⟩
    · simp [hostType, roleType, he] at ht
    · have hk : k = r.kind := by simpa [hostType, roleType, he] using ht
      exact ⟨j, by rw [hk]⟩
  choose xx hhx using hx
  choose yy hhy using hy
  exact ⟨⟨xx,yy⟩, funext fun r => by cases r with
    | inl a => exact hhx a
    | inr b => exact hhy b⟩

/-- All the other source edges are read in the current host, through one injection. -/
def step (G : SimpleGraph (Host A B)) : SimpleGraph (Host A B) where
  Adj a b := G.Adj a b ∨ ∃ (e : Edge) (f : Role ↪ Host A B), Preserves f ∧
    Pair a b (f e.fromRole) (f e.toRole) ∧ ∀ d, d ≠ e → G.Adj (f d.fromRole) (f d.toRole)
  symm := by
    rintro a b (h | ⟨e,f,ht,hp,hr⟩)
    · exact Or.inl (G.symm h)
    · exact Or.inr ⟨e,f,ht,hp.swap,hr⟩
  loopless := by
    rintro a (h | ⟨e,f,_, (⟨h,h'⟩ | ⟨h,h'⟩),_⟩)
    · exact G.loopless a h
    · exact e.distinct (f.injective (h.symm.trans h'))
    · exact e.distinct (f.injective (h'.symm.trans h))

def segmentOK (s : A → A) (a : LocalRole → A) (k : Bool) : Segment → Prop
  | .first => a (.endpoint false) = a (.u k)
  | .middle => a (.u k) = a (.v k)
  | .last => s (a (.v k)) = a (.endpoint true)

def edgeOK (sx : A → A) (sy : B → B) (E : A → B → Prop) (w : Positions A B) : Edge → Prop
  | .xTrack k t => segmentOK sx w.x k t
  | .yTrack k t => segmentOK sy w.y k t
  | .cross b => E (w.x (.endpoint b)) (w.y (.endpoint b))

theorem edgeOK_iff (sx : A → A) (sy : B → B) (E : A → B → Prop) (w : Positions A B) (e : Edge) :
    (host sx sy E).Adj (w.image e.fromRole) (w.image e.toRole) ↔ edgeOK sx sy E w e := by
  cases e with
  | xTrack k t =>
    cases t <;> simp [host, fixedArc, pathArc, Positions.image, Edge.fromRole, Edge.toRole,
      Segment.fromRole, Segment.toRole, LocalRole.kind, xEnd, yEnd, Pair, edgeOK, segmentOK]
  | yTrack k t =>
    cases t <;> simp [host, fixedArc, pathArc, Positions.image, Edge.fromRole, Edge.toRole,
      Segment.fromRole, Segment.toRole, LocalRole.kind, xEnd, yEnd, Pair, edgeOK, segmentOK]
  | cross b =>
    simp [host, fixedArc, Positions.image, Edge.fromRole, Edge.toRole, LocalRole.kind,
      xEnd, yEnd, Pair, edgeOK]

private theorem full_track {s : A → A} {a : LocalRole → A} {k : Bool}
    (h : ∀ t, segmentOK s a k t) :
    s (a (.endpoint false)) = a (.endpoint true) :=
  (congrArg s ((h .first).trans (h .middle))).trans (h .last)

/-- The other track fixes the endpoints even when an edge of this one was omitted. -/
theorem repair_track {s : A → A} (hs : Function.Injective s) (a : LocalRole → A)
    (k : Bool) (t : Segment)
    (h : ∀ l z, (l,z) ≠ (k,t) → segmentOK s a l z) :
    segmentOK s a k t := by
  have hframe := full_track (s := s) (a := a) (k := !k) fun z => h (!k) z (by simp)
  cases t with
  | first =>
    have hm := h k .middle (by simp)
    have hl := h k .last (by simp)
    exact (hs (hframe.trans hl.symm)).trans hm.symm
  | middle =>
    have hf := h k .first (by simp)
    have hl := h k .last (by simp)
    exact hf.symm.trans (hs (hframe.trans hl.symm))
  | last =>
    have hf := h k .first (by simp)
    have hm := h k .middle (by simp)
    exact (congrArg s (hf.trans hm)).symm.trans hframe

/-- E, its simultaneous forward translate, and its simultaneous backward translate. -/
def grow (sx : A → A) (sy : B → B) (E : A → B → Prop) (i : A) (j : B) : Prop :=
  E i j ∨ (∃ a b, sx a = i ∧ sy b = j ∧ E a b) ∨ E (sx i) (sy j)

private theorem forced {sx : A → A} {sy : B → B}
    (hx : Function.Injective sx) (hy : Function.Injective sy)
    (E : A → B → Prop) (w : Positions A B) (e : Edge)
    (h : ∀ d, d ≠ e → edgeOK sx sy E w d) :
    edgeOK sx sy (grow sx sy E) w e := by
  cases e with
  | xTrack k t =>
    apply repair_track hx w.x k t
    intro l z hn
    apply h (.xTrack l z)
    intro hEq
    cases hEq
    exact hn rfl
  | yTrack k t =>
    apply repair_track hy w.y k t
    intro l z hn
    apply h (.yTrack l z)
    intro hEq
    cases hEq
    exact hn rfl
  | cross b =>
    have fx := full_track (s := sx) (a := w.x) (k := false)
      (fun t => h (.xTrack false t) (by simp))
    have fy := full_track (s := sy) (a := w.y) (k := false)
      (fun t => h (.yTrack false t) (by simp))
    cases b
    · apply Or.inr; apply Or.inr
      rw [fx,fy]
      exact h (.cross true) (by simp)
    · exact Or.inr (Or.inl ⟨_,_,fx,fy,h (.cross false) (by simp)⟩)

private def baseAt (s : A → A) (i : A) : LocalRole → A
  | .endpoint true => s i
  | _ => i

private theorem baseAt_injective (s : A → A) (i : A) (hi : i ≠ s i) :
    Function.Injective (fun r : LocalRole => (r.kind,baseAt s i r)) := by
  intro r d he
  cases r with
  | endpoint b =>
    cases d with
    | endpoint c => cases b <;> cases c <;> simp_all [LocalRole.kind,baseAt,Ne.symm hi]
    | u l => simp [LocalRole.kind] at he
    | v l => simp [LocalRole.kind] at he
  | u k => cases d <;> simp_all [LocalRole.kind]
  | v k => cases d <;> simp_all [LocalRole.kind]

private def base (sx : A → A) (sy : B → B) (i : A) (j : B) : Positions A B :=
  ⟨baseAt sx i,baseAt sy j⟩

private def baseEmbedding (sx : A → A) (sy : B → B) (i : A) (j : B)
    (hi : i ≠ sx i) (hj : j ≠ sy j) : Role ↪ Host A B where
  toFun := (base sx sy i j).image
  inj' := Sum.map_injective.mpr ⟨baseAt_injective sx i hi,baseAt_injective sy j hj⟩

private theorem base_other (sx : A → A) (sy : B → B) (E : A → B → Prop)
    (i : A) (j : B) (b : Bool)
    (other : edgeOK sx sy E (base sx sy i j) (.cross (!b))) :
    ∀ d, d ≠ .cross b → edgeOK sx sy E (base sx sy i j) d := by
  intro d hd
  cases d with
  | xTrack k t => cases t <;> rfl
  | yTrack k t => cases t <;> rfl
  | cross c =>
    cases b <;> cases c <;> simp_all

private theorem add_cross (sx : A → A) (sy : B → B) (E : A → B → Prop)
    (nx : ∀ i, i ≠ sx i) (ny : ∀ j, j ≠ sy j) (i : A) (j : B) (b : Bool)
    (other : edgeOK sx sy E (base sx sy i j) (.cross (!b))) :
    (step (host sx sy E)).Adj
      ((base sx sy i j).image (Edge.cross b).fromRole)
      ((base sx sy i j).image (Edge.cross b).toRole) := by
  refine Or.inr ⟨.cross b, baseEmbedding sx sy i j (nx i) (ny j),
    (base sx sy i j).preserves, Or.inl ⟨rfl,rfl⟩, ?_⟩
  intro d hd
  exact (edgeOK_iff sx sy E _ d).2 (base_other sx sy E i j b other d hd)

private theorem grown_cross (sx : A → A) (sy : B → B) (E : A → B → Prop)
    (nx : ∀ i, i ≠ sx i) (ny : ∀ j, j ≠ sy j) {i : A} {j : B}
    (hg : grow sx sy E i j) : (step (host sx sy E)).Adj (xEnd i) (yEnd j) := by
  rcases hg with h | ⟨a,b,rfl,rfl,h⟩ | h
  · exact Or.inl (Or.inr ⟨i,j,h,Or.inl ⟨rfl,rfl⟩⟩)
  · exact add_cross sx sy E nx ny a b true h
  · exact add_cross sx sy E nx ny i j false h

/-- The two inclusions cover all vertex pairs, including every proposed track edge. -/
theorem one_round {sx : A → A} {sy : B → B}
    (hx : Function.Injective sx) (hy : Function.Injective sy)
    (nx : ∀ i, i ≠ sx i) (ny : ∀ j, j ≠ sy j) (E : A → B → Prop) :
    step (host sx sy E) = host sx sy (grow sx sy E) := by
  ext x y
  constructor
  · rintro (hold | ⟨e,f,hf,hxy,hr⟩)
    · rcases hold with h | ⟨i,j,he,hp⟩
      · exact Or.inl h
      · exact Or.inr ⟨i,j,Or.inl he,hp⟩
    obtain ⟨w,hw⟩ := positions_of_preserves (f := f) hf
    have rest (d : Edge) (hd : d ≠ e) : edgeOK sx sy E w d := by
      apply (edgeOK_iff sx sy E w d).1
      simpa only [← hw] using hr d hd
    have he : (host sx sy (grow sx sy E)).Adj (f e.fromRole) (f e.toRole) := by
      rw [hw]
      exact (edgeOK_iff sx sy _ w e).2 (forced hx hy E w e rest)
    rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact he
    · exact (host sx sy _).symm he
  · rintro (h | ⟨i,j,h,hp⟩)
    · exact Or.inl (Or.inl h)
    have hc := grown_cross sx sy E nx ny h
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hc
    · exact (step _).symm hc

/-- Successor on a cycle of length n. The branch at the last vertex wraps to zero. -/
def nextIndex {n : ℕ} (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val+1,h⟩ else ⟨0, Nat.zero_lt_of_lt i.isLt⟩

theorem nextIndex_injective (n : ℕ) : Function.Injective (@nextIndex n) := by
  intro a b he
  have hh := congrArg Fin.val he
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  unfold nextIndex at hh
  split at hh <;> split at hh <;> dsimp at hh <;> omega

theorem nextIndex_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : i ≠ nextIndex i := by
  intro he
  have hh := congrArg Fin.val he
  have hi := i.isLt
  unfold nextIndex at hh
  split at hh <;> dsimp at hh <;> omega

/-- The published hypotheses p,q ≥ 3 in particular give the distinct consecutive endpoints. -/
theorem one_typed_round {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (E : Fin p → Fin q → Prop) :
    step (host nextIndex nextIndex E) = host nextIndex nextIndex (grow nextIndex nextIndex E) :=
  one_round (nextIndex_injective p) (nextIndex_injective q)
    (nextIndex_ne (by omega : 2 ≤ p)) (nextIndex_ne (by omega : 2 ≤ q)) E

private def localRoles : List LocalRole :=
  [.endpoint false,.endpoint true,.u false,.u true,.v false,.v true]

instance : Fintype Role where
  elems := (localRoles.map Sum.inl ++ localRoles.map Sum.inr).toFinset
  complete := by
    rintro (r|r) <;> cases r <;> rename_i b <;> cases b <;> decide

private def kinds : List Kind := [.endpoint,.u false,.u true,.v false,.v true]

instance : Fintype (Kind ⊕ Kind) where
  elems := (kinds.map Sum.inl ++ kinds.map Sum.inr).toFinset
  complete := by
    rintro (k|k) <;> cases k <;> first | decide | (rename_i b; cases b <;> decide)

private def edgeList : List Edge :=
  [.xTrack false .first,.xTrack false .middle,.xTrack false .last,
   .xTrack true .first,.xTrack true .middle,.xTrack true .last,
   .yTrack false .first,.yTrack false .middle,.yTrack false .last,
   .yTrack true .first,.yTrack true .middle,.yTrack true .last,
   .cross false,.cross true]

instance : Fintype Edge where
  elems := edgeList.toFinset
  complete := by
    intro e
    cases e with
    | xTrack k t => cases k <;> cases t <;> decide
    | yTrack k t => cases k <;> cases t <;> decide
    | cross b => cases b <;> decide

theorem rule_counts :
    Fintype.card Role = 12 ∧ Fintype.card Edge = 14 ∧ Fintype.card (Kind ⊕ Kind) = 10 := by
  decide

private instance {V : Type*} [DecidableEq V] (x y a b : V) : Decidable (Pair x y a b) :=
  inferInstanceAs (Decidable ((x = a ∧ y = b) ∨ (x = b ∧ y = a)))

theorem Edge.unordered_unique : ∀ d e : Edge,
    Pair d.fromRole d.toRole e.fromRole e.toRole → d = e := by decide

private theorem Pair.swapLast {V : Type*} {x y a b : V} (h : Pair x y a b) :
    Pair x y b a := h.elim Or.inr Or.inl

/-- An ordinary non-induced injection of the entire rule with just one undirected edge
omitted, plus the explicit type-preservation condition. -/
def OrdinaryTypedWitness (G : SimpleGraph (Host A B)) (x y : Host A B) : Prop :=
  ∃ (u v : Role) (f : Role ↪ Host A B), rule.Adj u v ∧ Preserves f ∧ f u = x ∧ f v = y ∧
    ∀ a b, rule.Adj a b → ¬ Pair a b u v → G.Adj (f a) (f b)

theorem step_iff_ordinary (G : SimpleGraph (Host A B)) (x y : Host A B) :
    (step G).Adj x y ↔ G.Adj x y ∨ OrdinaryTypedWitness G x y := by
  constructor
  · rintro (old | ⟨e,f,ht,hp,hr⟩)
    · exact Or.inl old
    have rest (u v : Role) (huv : Pair u v e.fromRole e.toRole) :
        ∀ a b, rule.Adj a b → ¬ Pair a b u v → G.Adj (f a) (f b) := by
      rintro a b ⟨d,hd⟩ hn
      have dne : d ≠ e := by
        rintro rfl
        rcases huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hn hd
        · exact hn hd.swapLast
      rcases hd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hr d dne
      · exact G.symm (hr d dne)
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have hh : Pair e.fromRole e.toRole e.fromRole e.toRole := Or.inl ⟨rfl,rfl⟩
      exact Or.inr ⟨_,_,f,⟨e,hh⟩,ht,rfl,rfl,rest _ _ hh⟩
    · have hh : Pair e.toRole e.fromRole e.fromRole e.toRole := Or.inr ⟨rfl,rfl⟩
      exact Or.inr ⟨_,_,f,⟨e,hh⟩,ht,rfl,rfl,rest _ _ hh⟩
  · rintro (old | ⟨u,v,f,⟨e,huv⟩,ht,hx,hy,hr⟩)
    · exact Or.inl old
    have rest (d : Edge) (hd : d ≠ e) : G.Adj (f d.fromRole) (f d.toRole) := by
      apply hr _ _ ⟨d,Or.inl ⟨rfl,rfl⟩⟩
      intro h
      apply hd
      apply Edge.unordered_unique
      rcases huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact h
      · exact h.swapLast
    refine Or.inr ⟨e,f,ht,?_,rest⟩
    rw [← hx,← hy]
    rcases huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩

end TypedRound
