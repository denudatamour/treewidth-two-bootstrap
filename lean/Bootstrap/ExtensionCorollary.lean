import Bootstrap.Suppression
import Bootstrap.TreeSemantics
import Bootstrap.CliqueClock
import Bootstrap.Counterexample

/-! The degree-two extension consequence (Corollary II.3). -/
namespace Bootstrap.Suppression

variable {V J : Type*}

private theorem union_connected (K : SimpleGraph J) (A B : Set J)
    (hA : (K.induce A).Connected) (hB : (K.induce B).Connected) (j : J)
    (ja : j ∈ A) (jb : j ∈ B) : (K.induce (A ∪ B)).Connected := by
  let root : ↥(A ∪ B) := ⟨j,Or.inl ja⟩
  apply ((K.induce (A ∪ B)).connected_iff_exists_forall_reachable).mpr
  refine ⟨root,?_⟩
  rintro ⟨u,hu⟩
  rcases hu with hu | hu
  · exact (hA ⟨j,ja⟩ ⟨u,hu⟩).map (K.induceHomOfLE (Set.subset_union_left (t := B))).toHom
  · exact (hB ⟨j,jb⟩ ⟨u,hu⟩).map (K.induceHomOfLE (Set.subset_union_right (s := A))).toHom

/-- Pushing each old bag through an edge contraction preserves the usual tree
decomposition bound. The newly merged occurrence set is a union of intersecting subtrees. -/
theorem standard_width_suppress {H : SimpleGraph V} {v : V} {x y : Rest v} (hne : x ≠ y)
    (N : DegreeTwo.TwoNeighbours H v x.val y.val) {k : Nat} (w : TreeSemantics.WidthLE H k) :
    TreeSemantics.WidthLE (graph H v x y hne) k := by
  classical
  obtain ⟨J,fJ,⟨D⟩⟩ := w
  let bag (i : J) := (D.bag i).image (foldV v x)
  have mem (a : Rest v) (i : J) :
      a ∈ bag i ↔ a.val ∈ D.bag i ∨ (a = x ∧ v ∈ D.bag i) := by
    constructor
    · rintro h
      obtain ⟨t,ht,eq⟩ := Finset.mem_image.mp h
      by_cases tv : t = v
      · subst t
        exact Or.inr ⟨((fold_here v x).symm.trans eq).symm,ht⟩
      · have e : (⟨t,tv⟩ : Rest v) = a := (fold_rest v x ⟨t,tv⟩).symm.trans eq
        exact Or.inl ((congrArg Subtype.val e) ▸ ht)
    · rintro (h | ⟨rfl,h⟩)
      · exact Finset.mem_image.mpr ⟨a.val,h,fold_rest v x a⟩
      · exact Finset.mem_image.mpr ⟨v,h,fold_here v _⟩
  refine ⟨J,fJ,⟨⟨D.tree,D.isTree,bag,fun i => Finset.card_image_le.trans (D.width i),
    ?_,?_,?_⟩⟩⟩
  · intro a
    obtain ⟨i,h⟩ := D.vertex a.val
    exact ⟨i,(mem a i).mpr (Or.inl h)⟩
  · have joined : ∃ i, x ∈ bag i ∧ y ∈ bag i := by
      obtain ⟨i,vi,yi⟩ := D.edge v y.val N.right
      exact ⟨i,(mem _ i).mpr (Or.inr ⟨rfl,vi⟩),(mem _ i).mpr (Or.inl yi)⟩
    rintro a b (h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · obtain ⟨i,ai,bi⟩ := D.edge _ _ h
      exact ⟨i,(mem _ i).mpr (Or.inl ai),(mem _ i).mpr (Or.inl bi)⟩
    · exact joined
    · obtain ⟨i,xi,yi⟩ := joined
      exact ⟨i,yi,xi⟩
  · intro a
    by_cases ax : a = x
    · subst a
      have eq : {i | x ∈ bag i} = {i | x.val ∈ D.bag i} ∪ {i | v ∈ D.bag i} := by
        ext i
        simpa only [Set.mem_setOf_eq,Set.mem_union,true_and] using mem x i
      rw [eq]
      obtain ⟨j,jv,jx⟩ := D.edge v x.val N.left
      exact union_connected _ _ _ (D.running x.val) (D.running v) j jx jv
    · have eq : {i | a ∈ bag i} = {i | a.val ∈ D.bag i} := by
        ext i
        simpa only [Set.mem_setOf_eq,ax,false_and,or_false] using mem a i
      rw [eq]
      exact D.running a.val

/-- A 2-connected graph on three vertices is a triangle. Its ordinary bootstrap process
has a linear upper bound, by the already proved one-monochromatic-edge bound. -/
theorem three_vertex_base [Fintype V] {H : SimpleGraph V} (T : TwoConnected H)
    (three : Fintype.card V = 3) : ¬TreeSemantics.WidthLE H 1 ∧ HasLinearUpper H := by
  classical
  obtain ⟨a⟩ := T.connected.nonempty
  obtain ⟨b,c,ab,ac,bc'⟩ := two_neighbors T a
  have cover (t : V) : t = a ∨ t = b ∨ t = c := by
    have eq : ({a,b,c} : Finset V) = Finset.univ := Finset.eq_of_subset_of_card_le
      (Finset.subset_univ _) (by simp [ab.ne,ac.ne,bc',three])
    have ht : t ∈ ({a,b,c} : Finset V) := eq ▸ Finset.mem_univ t
    simpa using ht
  have bc : H.Adj b c := by
    by_contra bad
    have only (t : V) (h : H.Adj b t) : t = a := by
      rcases cover t with e | rfl | rfl
      · exact e
      · exact (H.irrefl h).elim
      · exact (bad h).elim
    obtain ⟨i,j,bi,bj,ij⟩ := two_neighbors T b
    exact ij ((only i bi).trans (only j bj).symm)
  have deg (t : V) : H.degree t = 2 := by
    obtain ⟨i,j,ti,tj,ij⟩ := two_neighbors T t
    have low : 1 < (H.neighborFinset t).card := Finset.one_lt_card.mpr
      ⟨i,(H.mem_neighborFinset _ _).mpr ti,j,(H.mem_neighborFinset _ _).mpr tj,ij⟩
    have high := H.degree_lt_card_verts t
    change 1 < H.degree t at low
    omega
  have mono : DegreeTwo.OneMonochrome H := by
    refine ⟨fun t => decide (t = a),b,c,bc,by simp [ab.ne.symm,ac.ne.symm],?_⟩
    intro i j ij same
    rcases cover i with i₀ | i₀ | i₀ <;> rcases cover j with j₀ | j₀ | j₀ <;>
      subst i <;> subst j <;> simp_all [ab.ne,ac.ne,ab.ne.symm,ac.ne.symm]
  exact ⟨TreeSemantics.triangle_forbids_width_one H ab ac bc,
    DegreeTwo.linear_of_one_monochrome H T.connected a (fun i _ _ => Or.inl (deg i))
      ⟨a,b,ab,deg a,deg b⟩ mono⟩

/-- Two actual ordinary rules with the extension, exact treewidth and asymptotic
properties of Corollary II.3. -/
def LinearBreak : Prop :=
  ∃ (U V : Type) (fU : Fintype U) (fV : Fintype V) (A : SimpleGraph U) (B : SimpleGraph V),
    @TwoConnected U fU A ∧ @TwoConnected V fV B ∧
    TreeSemantics.WidthLE A 2 ∧ ¬TreeSemantics.WidthLE A 1 ∧
    TreeSemantics.WidthLE B 2 ∧ ¬TreeSemantics.WidthLE B 1 ∧
    Extension A B ∧ HasLinearUpper A ∧ ¬HasLinearUpper B

private theorem descent (n : Nat) : ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V),
    Fintype.card V = n → TwoConnected H → TreeBags.WidthLE H 2 →
    (¬TreeSemantics.WidthLE H 1) ∧ (¬HasLinearUpper H → LinearBreak) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V fV dV H card T W
    classical
    by_cases three : Fintype.card V = 3
    · obtain ⟨nw,lin⟩ := three_vertex_base T three
      exact ⟨nw,fun bad => (bad lin).elim⟩
    · have four : 4 ≤ Fintype.card V := by have := T.order; omega
      obtain ⟨v,x,y,hne,N,W'⟩ := reducible T W
      let H' := graph H v x y hne
      have T' : TwoConnected H' := preserves_twoConnected T four hne N
      have less : Fintype.card (Rest v) < n := by rw [order_rest v, ←card]; omega
      obtain ⟨nw',next⟩ := ih _ less (Rest v) H' rfl T' W'
      have nw : ¬TreeSemantics.WidthLE H 1 := fun w => nw' (standard_width_suppress hne N w)
      refine ⟨nw,?_⟩
      intro bad
      by_cases lin : HasLinearUpper H'
      · exact ⟨Rest v,V,_,_,H',H,T',T,TreeSemantics.of_parent_bags W',nw',
          TreeSemantics.of_parent_bags W,nw,⟨v,x,y,hne,N,⟨SimpleGraph.Iso.refl⟩⟩,lin,bad⟩
      · exact next lin

theorem forbids_standard_width_one {V : Type} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    (T : TwoConnected H) (W : TreeBags.WidthLE H 2) : ¬TreeSemantics.WidthLE H 1 :=
  (descent (Fintype.card V) V H rfl T W).1

theorem descent_of_non_linear {V : Type} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    (T : TwoConnected H) (W : TreeBags.WidthLE H 2) (bad : ¬HasLinearUpper H) :
    LinearBreak := (descent (Fintype.card V) V H rfl T W).2 bad

end Bootstrap.Suppression

namespace Bootstrap.Preprint

/-- Corollary II.3 for the ordinary process; the nonlinear endpoint of the descent
is the fixed rule in Theorem III.1. -/
theorem corollary_II_3 : Suppression.LinearBreak := by
  classical
  apply Suppression.descent_of_non_linear (H := MarkedSimulation.ordinaryRule) _
    SourceBags.source_width_at_most_two ordinary_not_linear
  refine ⟨?_,RuleConnectivity.source_connected,RuleConnectivity.source_deleted_connected⟩
  rw [RuleStructure.source_order]
  decide

end Bootstrap.Preprint

#print axioms Bootstrap.Suppression.standard_width_suppress
#print axioms Bootstrap.Suppression.three_vertex_base
#print axioms Bootstrap.Preprint.corollary_II_3
