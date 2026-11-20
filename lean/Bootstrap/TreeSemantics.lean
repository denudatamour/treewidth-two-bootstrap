import Bootstrap.TreeBags
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Option

namespace Bootstrap.TreeSemantics

variable {V J : Type*}

/-- A usual tree decomposition indexed by J. Vertices carrying each graph vertex
form a nonempty connected induced subgraph of the index tree. -/
structure Decomposition (G : SimpleGraph V) (J : Type*) (k : Nat) where
  tree : SimpleGraph J
  isTree : tree.IsTree
  bag : J → Finset V
  width : ∀ i, (bag i).card ≤ k + 1
  vertex : ∀ v, ∃ i, v ∈ bag i
  edge : ∀ x y, G.Adj x y → ∃ i, x ∈ bag i ∧ y ∈ bag i
  running : ∀ v, (tree.induce {i | v ∈ bag i}).Connected

/-- Quantification over all finite index trees. Finite indices have representatives in Type. -/
def WidthLE (G : SimpleGraph V) (k : Nat) : Prop :=
  ∃ (J : Type) (_ : Fintype J), Nonempty (Decomposition G J k)

private def leaf (T : SimpleGraph J) (p : J) : SimpleGraph (Option J) where
  Adj
    | some i, some j => T.Adj i j
    | none, some j => p = j
    | some i, none => i = p
    | none, none => False
  symm := by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h.symm
    · exact h.symm
    · exact T.symm h
  loopless := by
    intro x h
    cases x
    · exact h
    · exact T.irrefl h

private def oldHom (T : SimpleGraph J) (p : J) : T →g leaf T p :=
  ⟨some, fun h => h⟩

private theorem leaf_connected (T : SimpleGraph J) (p : J) (ht : T.Connected) :
    (leaf T p).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨some p, ?_⟩
  rintro (_ | j)
  · exact (show (leaf T p).Adj (some p) none from rfl).reachable
  · exact (ht p j).map (oldHom T p)

private def edgeCode (T : SimpleGraph J) (p : J) : Option T.edgeSet → (leaf T p).edgeSet
  | none => ⟨s(none,some p), rfl⟩
  | some e => (oldHom T p).mapEdgeSet e

private theorem new_not_old (p : J) (e : Sym2 J) :
    Sym2.map some e ≠ s(none,some p) := by
  induction e using Sym2.inductionOn with
  | _ a b => simp [Sym2.map_pair_eq, Sym2.eq_iff]

private theorem edgeCode_bijective (T : SimpleGraph J) (p : J) :
    Function.Bijective (edgeCode T p) := by
  constructor
  · intro x y h
    cases x with
    | none => cases y with
      | none => rfl
      | some e => exact False.elim (new_not_old p e.val (congrArg Subtype.val h).symm)
    | some e => cases y with
      | none => exact False.elim (new_not_old p e.val (congrArg Subtype.val h))
      | some e' =>
        exact congrArg some (Subtype.ext (Sym2.map.injective (Option.some_injective J)
          (congrArg Subtype.val h)))
  · rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
      change (leaf T p).Adj x y at he
      cases x with
      | none => cases y with
        | none => exact False.elim he
        | some j => change p = j at he; subst j; exact ⟨none, rfl⟩
      | some i => cases y with
        | none =>
          change i = p at he
          subst i
          exact ⟨none, Subtype.ext Sym2.eq_swap⟩
        | some j => exact ⟨some ⟨s(i,j), he⟩, rfl⟩

private theorem leaf_tree [Fintype J] (T : SimpleGraph J) (p : J) (ht : T.IsTree) :
    (leaf T p).IsTree := by
  classical
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨leaf_connected _ _ ht.isConnected, ?_⟩
  let e := Equiv.ofBijective (edgeCode T p) (edgeCode_bijective T p)
  have card := ht.card_edgeFinset
  rw [SimpleGraph.edgeFinset_card] at card
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_option, card,
    Nat.card_eq_fintype_card, Fintype.card_option]

private def extendBag (bag : J → Finset V) (b : Finset V) : Option J → Finset V
  | none => b
  | some j => bag j

private theorem leaf_fiber (T : SimpleGraph J) (p : J) (bag : J → Finset V) (b : Finset V)
    (v : V) (old : (T.induce {j | v ∈ bag j}).Preconnected)
    (glue : ∀ j, v ∈ b → v ∈ bag j → v ∈ bag p) :
    ((leaf T p).induce {j | v ∈ extendBag bag b j}).Preconnected := by
  let emb : T.induce {j | v ∈ bag j} →g (leaf T p).induce {j | v ∈ extendBag bag b j} :=
    ⟨fun j => ⟨some j.val,j.property⟩, fun h => h⟩
  have reach (j : J) (hb : v ∈ b) (hj : v ∈ bag j) :
      ((leaf T p).induce {t | v ∈ extendBag bag b t}).Reachable ⟨none,hb⟩ ⟨some j,hj⟩ := by
    let hp := glue j hb hj
    have link : ((leaf T p).induce {t | v ∈ extendBag bag b t}).Adj ⟨none,hb⟩ ⟨some p,hp⟩ := rfl
    exact link.reachable.trans ((old ⟨p,hp⟩ ⟨j,hj⟩).map emb)
  rintro ⟨_ | i, hi⟩ ⟨_ | j, hj⟩
  · exact SimpleGraph.Reachable.refl _
  · exact reach j hi hj
  · exact (reach i hj hi).symm
  · exact (old ⟨i,hi⟩ ⟨j,hj⟩).map emb

private structure Realization (F : Finset (Finset V)) where
  Index : Type
  [finite : Fintype Index]
  tree : SimpleGraph Index
  ht : tree.IsTree
  bag : Index → Finset V
  labels : ∀ b, b ∈ F ↔ ∃ j, bag j = b
  fiber : ∀ v, (tree.induce {j | v ∈ bag j}).Preconnected

private theorem realize [DecidableEq V] {k : Nat} {F : Finset (Finset V)}
    (T : TreeBags.Tree k F) : Nonempty (Realization F) := by
  classical
  induction T with
  | root b _ =>
    refine ⟨{
      Index := Unit
      tree := ⊥
      ht := ⟨?_, SimpleGraph.isAcyclic_bot⟩
      bag := fun _ => b
      labels := ?_
      fiber := ?_ }⟩
    · exact (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
        ⟨(), fun j => by cases j; exact SimpleGraph.Reachable.refl _⟩
    · intro d
      simp [eq_comm]
    · intro v x y
      obtain rfl := Subsingleton.elim x y
      exact SimpleGraph.Reachable.refl _
  | @attach F t p hp b hw glue ih =>
    obtain ⟨D⟩ := ih
    letI := D.finite
    obtain ⟨j, hj⟩ := (D.labels p).mp hp
    refine ⟨{
      Index := Option D.Index
      tree := leaf D.tree j
      ht := leaf_tree D.tree j D.ht
      bag := extendBag D.bag b
      labels := ?_
      fiber := ?_ }⟩
    · intro d
      constructor
      · intro hd
        rcases Finset.mem_insert.mp hd with rfl | ho
        · exact ⟨none,rfl⟩
        · obtain ⟨i,hi⟩ := (D.labels d).mp ho
          exact ⟨some i,hi⟩
      · rintro ⟨_ | i, h⟩
        · exact Finset.mem_insert.mpr (Or.inl h.symm)
        · exact Finset.mem_insert_of_mem ((D.labels d).mpr ⟨i,h⟩)
    · intro v
      apply leaf_fiber _ _ _ _ _ (D.fiber v)
      intro i hv hi
      rw [hj]
      exact glue v hv ⟨D.bag i, (D.labels _).mpr ⟨i,rfl⟩, hi⟩

theorem of_parent_bags [DecidableEq V] {G : SimpleGraph V} {k : Nat}
    (h : TreeBags.WidthLE G k) : WidthLE G k := by
  obtain ⟨F,T,covers,edges⟩ := h
  obtain ⟨D⟩ := realize T
  have allv (v : V) : ∃ j, v ∈ D.bag j := by
    obtain ⟨b,hb,hv⟩ := covers v
    obtain ⟨j,rfl⟩ := (D.labels b).mp hb
    exact ⟨j,hv⟩
  refine ⟨D.Index,D.finite,⟨{
    tree := D.tree
    isTree := D.ht
    bag := D.bag
    width := ?_
    vertex := allv
    edge := ?_
    running := ?_ }⟩⟩
  · intro j
    exact TreeBags.bag_size T ((D.labels _).mpr ⟨j,rfl⟩)
  · intro x y hxy
    obtain ⟨b,hb,hx,hy⟩ := edges _ _ hxy
    obtain ⟨j,rfl⟩ := (D.labels b).mp hb
    exact ⟨j,hx,hy⟩
  · intro v
    obtain ⟨j,hv⟩ := allv v
    exact @SimpleGraph.Connected.mk _ _ (D.fiber v) ⟨⟨j,hv⟩⟩

private def restricted (T : SimpleGraph J) (A : Set J) : SimpleGraph J where
  Adj x y := T.Adj x y ∧ x ∈ A ∧ y ∈ A
  symm := fun _ _ h => ⟨T.symm h.1, h.2.2, h.2.1⟩
  loopless := fun _ h => T.irrefl h.1

private theorem restricted_le (T : SimpleGraph J) (A : Set J) : restricted T A ≤ T :=
  fun _ _ h => h.1

private theorem restricted_reach {T : SimpleGraph J} {A : Set J}
    (h : (T.induce A).Connected) {x y : J} (hx : x ∈ A) (hy : y ∈ A) :
    (restricted T A).Reachable x y := by
  let inc : T.induce A →g restricted T A :=
    ⟨Subtype.val, fun {a b} h => ⟨h,a.property,b.property⟩⟩
  exact (h ⟨x,hx⟩ ⟨y,hy⟩).map inc

private theorem lift_edges {T T' : SimpleGraph J} {x y : J}
    (h : T ≤ T') (p : T.Path x y) :
    (p.map (SimpleGraph.Hom.ofLE h) (fun _ _ he => he)).val.edges = p.val.edges := by
  change (p.val.map (SimpleGraph.Hom.ofLE h)).edges = _
  rw [SimpleGraph.Walk.edges_map]
  change p.val.edges.map (Sym2.map id) = _
  simp [Sym2.map_id]

private theorem crossing (T : SimpleGraph J) (A B C : Set J) {x y : J}
    (p : (restricted T A).Walk x y) (xa : x ∈ A) (xb : x ∈ B) (yc : y ∈ C)
    (cover : ∀ {i j : J}, s(i,j) ∈ p.edges → (i ∈ B ∧ j ∈ B) ∨ (i ∈ C ∧ j ∈ C)) :
    ∃ m, m ∈ A ∧ m ∈ B ∧ m ∈ C := by
  induction p with
  | nil => exact ⟨_,xa,xb,yc⟩
  | @cons x v w e p ih =>
    have hs : s(x,v) ∈ (SimpleGraph.Walk.cons e p).edges := by simp
    rcases cover hs with h | h
    · apply ih e.2.2 h.2 yc
      intro a b hm
      apply cover
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
      exact Or.inr hm
    · exact ⟨x,xa,xb,h.1⟩

/-- Three pairwise intersecting connected subtrees of a tree have a common vertex. -/
theorem three_subtrees (T : SimpleGraph J) (ht : T.IsTree) (A B C : Set J)
    (hA : (T.induce A).Connected) (hB : (T.induce B).Connected) (hC : (T.induce C).Connected)
    {x y z : J} (xa : x ∈ A) (xb : x ∈ B) (ya : y ∈ A) (yc : y ∈ C)
    (zb : z ∈ B) (zc : z ∈ C) : ∃ m, m ∈ A ∧ m ∈ B ∧ m ∈ C := by
  classical
  let Q := restricted T B ⊔ restricted T C
  have r₁ := restricted_reach hA xa ya
  have r₂ : Q.Reachable x y :=
    ((restricted_reach hB xb zb).mono le_sup_left).trans
      ((restricted_reach hC zc yc).mono le_sup_right)
  let p := r₁.some.toPath
  let q := r₂.some.toPath
  have a := restricted_le T A
  have b : Q ≤ T := sup_le (restricted_le T B) (restricted_le T C)
  have same := ht.IsAcyclic.path_unique (p.map (SimpleGraph.Hom.ofLE a) (fun _ _ h => h))
    (q.map (SimpleGraph.Hom.ofLE b) (fun _ _ h => h))
  have he : p.val.edges = q.val.edges := (lift_edges a p).symm.trans
    ((congrArg (fun w : T.Path x y => w.val.edges) same).trans (lift_edges b q))
  apply crossing T A B C p.val xa xb yc
  intro i j hij
  have hq := q.val.adj_of_mem_edges (he ▸ hij)
  rcases hq with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2

theorem triangle_bag {G : SimpleGraph V} {k : Nat} (D : Decomposition G J k) {x y z : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    ∃ i, x ∈ D.bag i ∧ y ∈ D.bag i ∧ z ∈ D.bag i := by
  obtain ⟨a,ax,ay⟩ := D.edge _ _ hxy
  obtain ⟨b,bx,bz⟩ := D.edge _ _ hxz
  obtain ⟨c,cy,cz⟩ := D.edge _ _ hyz
  exact three_subtrees D.tree D.isTree _ _ _ (D.running x) (D.running y) (D.running z)
    ax ay bx bz cy cz

theorem triangle_forbids_width_one (G : SimpleGraph V) {x y z : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) : ¬WidthLE G 1 := by
  classical
  rintro ⟨_,_,⟨D⟩⟩
  obtain ⟨b,bx,by',bz⟩ := triangle_bag D hxy hxz hyz
  have hs : ({x,y,z} : Finset V) ⊆ D.bag b := by
    simpa [Finset.insert_subset_iff] using ⟨bx,by',bz⟩
  have hc : ({x,y,z} : Finset V).card = 3 := by simp [hxy.ne,hxz.ne,hyz.ne]
  have hab := Finset.card_le_card hs
  have hbound := D.width b
  omega

end Bootstrap.TreeSemantics

#print axioms Bootstrap.TreeSemantics.of_parent_bags
#print axioms Bootstrap.TreeSemantics.three_subtrees
#print axioms Bootstrap.TreeSemantics.triangle_forbids_width_one
