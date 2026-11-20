import Bootstrap.DegreeTwoTransfer
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path

namespace Bootstrap.DegreeTwo

variable {W V : Type*}

def HasTwo (H : SimpleGraph W) (w : W) : Prop := ∃ l r, TwoNeighbours H w l r

theorem hasTwo_iff_degree (H : SimpleGraph W) [Fintype W] [DecidableRel H.Adj] (w : W) :
    HasTwo H w ↔ H.degree w = 2 := by
  classical
  change HasTwo H w ↔ (H.neighborFinset w).card = 2
  rw [Finset.card_eq_two]
  constructor
  · rintro ⟨l,r,N⟩
    refine ⟨l,r,N.distinct,?_⟩
    ext j
    simp only [H.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact N.only j
    · rintro (rfl | rfl)
      · exact N.left
      · exact N.right
  · rintro ⟨l,r,hlr,he⟩
    have iff_adj (j : W) : H.Adj w j ↔ j = l ∨ j = r := by
      rw [← H.mem_neighborFinset w j, he]
      simp
    exact ⟨l,r,⟨(iff_adj l).mpr (Or.inl rfl), (iff_adj r).mpr (Or.inr rfl),
      hlr, fun j e => (iff_adj j).mp e⟩⟩

theorem HasTwo.other {H : SimpleGraph W} {w l : W} (hw : HasTwo H w) (e : H.Adj w l) :
    ∃ r, TwoNeighbours H w l r := by
  obtain ⟨a,b,N⟩ := hw
  rcases N.only l e with h | h
  · subst l
    exact ⟨b,N⟩
  · subst l
    exact ⟨a,N.reverse⟩

theorem HasTwo.pair {H : SimpleGraph W} {w l r : W} (hw : HasTwo H w)
    (hl : H.Adj w l) (hr : H.Adj w r) (hne : l ≠ r) : TwoNeighbours H w l r := by
  obtain ⟨z,N⟩ := hw.other hl
  rcases N.only r hr with h | h
  · exact False.elim (hne h.symm)
  · subst r
    exact N

/-- A base followed by two consecutive interior roles of a long route.
The fourth role may be the base (a returning three-edge route). -/
def LongStart (H : SimpleGraph W) (base : Set W) (l : W) : Prop :=
  l ∈ base ∧ ∃ a b r, a ∉ base ∧ b ∉ base ∧ TwoNeighbours H a l b ∧ TwoNeighbours H b a r

/-- Vertices joined through an exact degree-two middle role. The set parameter
restricts the endpoints when working only on the base component. -/
def transferGraph (H : SimpleGraph W) (allow : Set W) : SimpleGraph W where
  Adj x y := x ∈ allow ∧ y ∈ allow ∧ ∃ m, TwoNeighbours H m x y
  symm := by
    rintro x y ⟨hx,hy,m,N⟩
    exact ⟨hy,hx,m,N.reverse⟩
  loopless := by
    rintro x ⟨_,_,m,N⟩
    exact N.distinct rfl

theorem chain_append {H : SimpleGraph W} {m n : ℕ} {a b c : W}
    (ab : Chain H m a b) (bc : Chain H n b c) : Chain H (m+n) a c := by
  induction n generalizing c with
  | zero =>
    have e : b = c := bc
    subst c
    exact ab
  | succ n ih =>
    obtain ⟨u,w,prev,N⟩ := bc
    exact ⟨u,w,ih prev,N⟩

private theorem chain_of_walk {H : SimpleGraph W} {allow : Set W} {x y : W}
    (p : (transferGraph H allow).Walk x y) : Chain H p.length x y := by
  induction p with
  | nil => rfl
  | @cons u v w e tail ih =>
    obtain ⟨_,_,m,N⟩ := e
    have first : Chain H 1 u v := ⟨u,m,rfl,N⟩
    simpa [SimpleGraph.Walk.length, Nat.add_comm] using chain_append first ih

theorem bounded_chain [Fintype W] {H : SimpleGraph W} {allow : Set W} {x y : W}
    (reach : (transferGraph H allow).Reachable x y) :
    ∃ n < Fintype.card W, Chain H n x y := by
  obtain ⟨p,hp⟩ := reach.exists_isPath
  exact ⟨p.length, hp.length_lt, chain_of_walk p⟩

private theorem closed_covers {H : SimpleGraph W} (conn : H.Connected) (D : W → Prop)
    {x : W} (hx : D x) (extend : ∀ i j, D i → H.Adj i j → D j) (y : W) : D y := by
  have path := (H.reachable_iff_reflTransGen x y).mp (conn x y)
  induction path with
  | refl => exact hx
  | tail _ e ih => exact extend _ _ ih e

/-- In a component of interior roles containing an edge, one of its initial
ends can transmit a mark to the incident base of a long route. -/
private theorem internal_head {H : SimpleGraph W} (conn : H.Connected) (base : Set W)
    (nonempty : base.Nonempty) (deg : ∀ z ∉ base, HasTwo H z)
    {u v : W} (iu : u ∉ base) (iv : v ∉ base) (edge : H.Adj u v) :
    ∃ l, LongStart H base l ∧ ((transferGraph H Set.univ).Reachable u l ∨
      (transferGraph H Set.univ).Reachable v l) := by
  classical
  let K := transferGraph H Set.univ
  let Seen := fun z => K.Reachable u z ∨ K.Reachable v z
  let D := fun z => z ∉ base ∧ Seen z ∧ ∃ s, s ∉ base ∧ H.Adj z s ∧ Seen s
  by_contra bad
  have start : D u := ⟨iu,Or.inl .rfl,v,iv,edge,Or.inr .rfl⟩
  have extend (i j : W) (di : D i) (e : H.Adj i j) : D j := by
    obtain ⟨ii,si,s,is_,es,ss⟩ := di
    have sj : Seen j := by
      by_cases eq : s = j
      · rw [← eq]
        exact ss
      · have step' : K.Adj s j := ⟨Set.mem_univ _,Set.mem_univ _,i,(deg i ii).pair es e eq⟩
        rcases ss with ss | ss
        · exact Or.inl (ss.trans step'.reachable)
        · exact Or.inr (ss.trans step'.reachable)
    by_cases jb : j ∈ base
    · have js : j ≠ s := fun h => is_ (h ▸ jb)
      have A := (deg i ii).pair e es js
      obtain ⟨r,B⟩ := (deg s is_).other (H.symm es)
      exact False.elim (bad ⟨j,⟨jb,i,s,r,ii,is_,A,B⟩,sj⟩)
    · exact ⟨jb,sj,i,ii,H.symm e,si⟩
  obtain ⟨c,hc⟩ := nonempty
  exact (closed_covers conn D start extend c).1 hc

/-- A base component connected by short links meets a long route. -/
private theorem short_component_head {H : SimpleGraph W} (conn : H.Connected) (base : Set W)
    (indep : ∀ i ∈ base, ∀ j ∈ base, ¬ H.Adj i j) (deg : ∀ z ∉ base, HasTwo H z)
    (long : ∃ a b, a ∉ base ∧ b ∉ base ∧ H.Adj a b) {u : W} (bu : u ∈ base) :
    ∃ l, LongStart H base l ∧ (transferGraph H base).Reachable u l := by
  classical
  let K := transferGraph H base
  let C := fun z => z ∈ base ∧ K.Reachable u z
  let D := fun z => C z ∨ ∃ c, C c ∧ H.Adj c z
  by_contra bad
  have impossible (c i j : W) (cc : C c) (ii : i ∉ base) (ij : j ∉ base)
      (ci : H.Adj c i) (e : H.Adj i j) : False := by
    have cj : c ≠ j := fun h => ij (h ▸ cc.1)
    have A := (deg i ii).pair (H.symm ci) e cj
    obtain ⟨r,B⟩ := (deg j ij).other (H.symm e)
    exact bad ⟨c,⟨cc.1,i,j,r,ii,ij,A,B⟩,cc.2⟩
  have start : D u := Or.inl ⟨bu,.rfl⟩
  have extend (i j : W) (di : D i) (e : H.Adj i j) : D j := by
    rcases di with ci | ⟨c,cc,ci⟩
    · exact Or.inr ⟨i,ci,e⟩
    · have ii : i ∉ base := fun hi => indep c cc.1 i hi ci
      by_cases cj : c = j
      · rw [← cj]
        exact Or.inl cc
      · by_cases jb : j ∈ base
        · have step' : K.Adj c j := ⟨cc.1,jb,i,(deg i ii).pair (H.symm ci) e cj⟩
          exact Or.inl ⟨jb,cc.2.trans step'.reachable⟩
        · exact False.elim (impossible c i j cc ii jb ci e)
  obtain ⟨a,b,ia,ib,e⟩ := long
  rcases closed_covers conn D start extend a with ca | ⟨c,cc,ca⟩
  · exact ia ca.1
  · exact impossible c a b cc ia ib ca e

def TwoShoreConclusion (H : SimpleGraph W) (J : SimpleGraph V) (f : W ↪ V)
    (base : Set W) (P Q : Set V) : Prop :=
  Joined J P Q ∧ ∃ l, LongStart H base l ∧ (Marked J f P l ∨ Marked J f Q l)

private theorem shore_swap {H : SimpleGraph W} {J : SimpleGraph V} {f : W ↪ V}
    {base : Set W} {P Q : Set V} (h : TwoShoreConclusion H J f base P Q) :
    TwoShoreConclusion H J f base Q P := by
  obtain ⟨cross,l,hl,m⟩ := h
  exact ⟨fun q hq p hp => J.symm (cross p hp q hq),l,hl,m.symm⟩

private theorem based_edge [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (f : W ↪ V) (t : ℕ) (hf : FullCopy H (run H G t) f) (conn : H.Connected)
    (base : Set W) (indep : ∀ i ∈ base, ∀ j ∈ base, ¬ H.Adj i j)
    (deg : ∀ z ∉ base, HasTwo H z) (long : ∃ a b, a ∉ base ∧ b ∉ base ∧ H.Adj a b)
    {u w : W} (bu : u ∈ base) (edge : H.Adj u w) (P Q : Set V) (hP : P.Nonempty)
    (hp : ∀ p ∈ P, Outside f p) (hq : ∀ q ∈ Q, Outside f q)
    (hdis : ∀ p ∈ P, ∀ q ∈ Q, p ≠ q)
    (mp : Marked (run H G t) f P u) (mq : Marked (run H G t) f Q w) :
    TwoShoreConclusion H (run H G (t+2*Fintype.card W)) f base P Q := by
  classical
  have iw : w ∉ base := fun h => indep u bu w h edge
  obtain ⟨v,S⟩ := (deg w iw).other (H.symm edge)
  have hcard : 1 < Fintype.card W := Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨u,v,S.distinct⟩⟩
  by_cases bv : v ∈ base
  · obtain ⟨l,head,reach⟩ := short_component_head conn base indep deg long bu
    obtain ⟨a,b,r,ia,ib,A,B⟩ := head.2
    obtain ⟨d,hd,path⟩ := bounded_chain reach
    have hrw : r ≠ w := by
      intro e
      have wb : H.Adj w b := e ▸ H.symm B.right
      rcases S.only b wb with h | h
      · exact ib (h.symm ▸ bu)
      · exact ib (h.symm ▸ bv)
    let k := max 1 d
    have hk : 1 ≤ k := le_max_left _ _
    have hdk : d ≤ k := le_max_right _ _
    have kh : k < Fintype.card W := max_lt hcard hd
    obtain ⟨cross,mark⟩ := short_route H G f t hf S A B hrw k d hk hdk path P Q hP hp hq hdis mp mq
    have grow := time_mono H G (by omega : t+k+k+1+1 ≤ t+2*Fintype.card W)
    exact ⟨fun p hp' q hq' => grow (cross p hp' q hq'),l,head,Or.inl (fun p h => grow (mark p h))⟩
  · obtain ⟨r,B⟩ := (deg v bv).other (H.symm S.right)
    have grow := time_mono H G (by omega : t+1+1 ≤ t+2*Fintype.card W)
    refine ⟨?_,u,⟨bu,w,v,r,iw,bv,S,B⟩,Or.inl ?_⟩
    · intro p hp' q hq'
      apply grow
      exact two_middle H _ f (full_later (by omega : t ≤ t+1) hf) S B p q
        (hp p hp') (hq q hq') (hdis p hp' q hq') (run_le_succ H G t (mp p hp'))
        (one_step H _ f hf B q (hq q hq') (mq q hq'))
    · intro p h
      exact time_mono H G (by omega : t ≤ t+2*Fintype.card W) (mp p h)

private theorem interior_edge [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (f : W ↪ V) (t : ℕ) (hf : FullCopy H (run H G t) f) (conn : H.Connected)
    (base : Set W) (live : base.Nonempty) (deg : ∀ z ∉ base, HasTwo H z)
    {u v : W} (iu : u ∉ base) (iv : v ∉ base) (edge : H.Adj u v) (P Q : Set V)
    (hp : ∀ p ∈ P, Outside f p) (hq : ∀ q ∈ Q, Outside f q)
    (hdis : ∀ p ∈ P, ∀ q ∈ Q, p ≠ q)
    (mp : Marked (run H G t) f P u) (mq : Marked (run H G t) f Q v) :
    TwoShoreConclusion H (run H G (t+2*Fintype.card W)) f base P Q := by
  obtain ⟨l,A⟩ := (deg u iu).other edge
  obtain ⟨r,B⟩ := (deg v iv).other (H.symm edge)
  have hcard : 1 < Fintype.card W := Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨v,l,A.distinct⟩⟩
  constructor
  · intro p hp' q hq'
    apply time_mono H G (by omega : t+1+1 ≤ t+2*Fintype.card W)
    apply (run H G (t+1+1)).symm
    exact two_middle H _ f (full_later (by omega : t ≤ t+1) hf) A.reverse B q p
      (hq q hq') (hp p hp') (hdis p hp' q hq').symm
      (one_step H _ f hf A q (hq q hq') (mq q hq'))
      (one_step H _ f hf B p (hp p hp') (mp p hp'))
  · obtain ⟨s,head,reach⟩ := internal_head conn base live deg iu iv edge
    refine ⟨s,head,?_⟩
    rcases reach with reach | reach
    · obtain ⟨d,hd,path⟩ := bounded_chain reach
      exact Or.inl (fun p h => time_mono H G (by omega : t+d ≤ t+2*Fintype.card W)
        (along_chain H G f t hf path p (hp p h) (mp p h)))
    · obtain ⟨d,hd,path⟩ := bounded_chain reach
      exact Or.inr (fun q h => time_mono H G (by omega : t+d ≤ t+2*Fintype.card W)
        (along_chain H G f t hf path q (hq q h) (mq q h)))

/-- II.2 for every rule edge. Connectedness finds the incident long route
inside the proof. The hypotheses on the base set also permit a singleton
base when the entire graph is a cycle. -/
theorem two_sets_with_base [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (f : W ↪ V) (t : ℕ) (hf : FullCopy H (run H G t) f) (conn : H.Connected)
    (base : Set W) (live : base.Nonempty) (indep : ∀ i ∈ base, ∀ j ∈ base, ¬ H.Adj i j)
    (deg : ∀ z ∉ base, HasTwo H z) (long : ∃ a b, a ∉ base ∧ b ∉ base ∧ H.Adj a b)
    {x y : W} (edge : H.Adj x y) (P Q : Set V) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hp : ∀ p ∈ P, Outside f p) (hq : ∀ q ∈ Q, Outside f q)
    (hdis : ∀ p ∈ P, ∀ q ∈ Q, p ≠ q)
    (mp : Marked (run H G t) f P x) (mq : Marked (run H G t) f Q y) :
    TwoShoreConclusion H (run H G (t+2*Fintype.card W)) f base P Q := by
  classical
  by_cases bx : x ∈ base
  · exact based_edge H G f t hf conn base indep deg long bx edge P Q hP hp hq hdis mp mq
  · by_cases by_ : y ∈ base
    · exact shore_swap (based_edge H G f t hf conn base indep deg long by_ (H.symm edge) Q P
        hQ hq hp (fun q hq' p hp' => (hdis p hp' q hq').symm) mq mp)
    · exact interior_edge H G f t hf conn base live deg bx by_ edge P Q hp hq hdis mp mq

/-- In a 2-regular graph choose the given cycle base; otherwise take precisely
the roles whose degree is different from two. -/
noncomputable def standardBases [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (root : W) : Set W := by
  classical
  exact if ∃ z, H.degree z ≠ 2 then {z | H.degree z ≠ 2} else {root}

private theorem standard_base_properties [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (root : W) (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    (long : ∃ i j, H.Adj i j ∧ H.degree i = 2 ∧ H.degree j = 2) :
    (standardBases H root).Nonempty ∧
    (∀ i ∈ standardBases H root, ∀ j ∈ standardBases H root, ¬ H.Adj i j) ∧
    (∀ z ∉ standardBases H root, HasTwo H z) ∧
    ∃ a b, a ∉ standardBases H root ∧ b ∉ standardBases H root ∧ H.Adj a b := by
  classical
  by_cases ex : ∃ w, H.degree w ≠ 2
  · simp only [standardBases, if_pos ex, Set.mem_setOf_eq]
    refine ⟨ex, ?_, ?_, ?_⟩
    · intro i hi j hj e
      rcases cover i j e with h | h
      · exact hi h
      · exact hj h
    · intro z hz
      exact (hasTwo_iff_degree H z).mpr (Classical.not_not.mp hz)
    · obtain ⟨a,b,e,da,db⟩ := long
      exact ⟨a,b,fun h => h da,fun h => h db,e⟩
  · have all : ∀ z, H.degree z = 2 := by
      intro z
      by_contra h
      exact ex ⟨z,h⟩
    simp only [standardBases, if_neg ex, Set.mem_singleton_iff]
    obtain ⟨a,b,N⟩ := (hasTwo_iff_degree H root).mpr (all root)
    obtain ⟨s,T⟩ := ((hasTwo_iff_degree H a).mpr (all a)).other (H.symm N.left)
    refine ⟨⟨root,rfl⟩, ?_, fun z _ => (hasTwo_iff_degree H z).mpr (all z), ?_⟩
    · rintro i rfl j rfl
      exact H.loopless _
    · exact ⟨a,s,(fun e => H.loopless root (e ▸ N.left)), T.distinct.symm, T.right⟩

/-- Lemma II.2 in the ordinary synchronous process, starting at any round.
An edge between degree-two roles is the three-or-more-edge route regime;
in a cycle the root is the arbitrarily chosen base. -/
theorem two_sets_of_neighbours_connected [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (G : SimpleGraph V) (f : W ↪ V) (t : ℕ) (hf : FullCopy H (run H G t) f)
    (conn : H.Connected) (root : W)
    (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    (long : ∃ i j, H.Adj i j ∧ H.degree i = 2 ∧ H.degree j = 2)
    {x y : W} (edge : H.Adj x y) (P Q : Set V) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hp : ∀ p ∈ P, Outside f p) (hq : ∀ q ∈ Q, Outside f q)
    (hdis : ∀ p ∈ P, ∀ q ∈ Q, p ≠ q)
    (mp : Marked (run H G t) f P x) (mq : Marked (run H G t) f Q y) :
    TwoShoreConclusion H (run H G (t+2*Fintype.card W)) f (standardBases H root) P Q := by
  obtain ⟨live,indep,deg,exists_long⟩ := standard_base_properties H root cover long
  exact two_sets_with_base H G f t hf conn _ live indep deg exists_long edge P Q hP hQ hp hq hdis mp mq

end Bootstrap.DegreeTwo

#print axioms Bootstrap.DegreeTwo.hasTwo_iff_degree
#print axioms Bootstrap.DegreeTwo.bounded_chain
#print axioms Bootstrap.DegreeTwo.two_sets_with_base
#print axioms Bootstrap.DegreeTwo.two_sets_of_neighbours_connected
