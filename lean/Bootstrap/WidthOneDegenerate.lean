import Bootstrap.TreeSemantics

/-! Finite sets in a graph of treewidth at most one contain a vertex with at most
one neighbour in the set. We trim a walk of decomposition bags until its first
bag is the only occurrence of one of the required vertices on the walk. -/

namespace Bootstrap.TreeLinear

variable {W J : Type*}

/-- Every nonempty finite vertex set has a vertex with at most one neighbour in the set. -/
def OneDegenerate (H : SimpleGraph W) : Prop :=
  ∀ S : Finset W, S.Nonempty → ∃ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
    H.Adj x y → H.Adj x z → y = z

/-- The bags visited by a walk induce a connected graph. -/
private theorem support_connected {T : SimpleGraph J} {u v : J} (p : T.Walk u v) :
    (T.induce {j | j ∈ p.support}).Connected := by
  induction p with
  | @nil u =>
    apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
    refine ⟨⟨u, by simp⟩, ?_⟩
    rintro ⟨j,hj⟩
    have e : j = u := by simpa using hj
    subst j
    exact SimpleGraph.Reachable.refl _
  | @cons u v w uv p ih =>
    let A : Set J := {j | j ∈ (SimpleGraph.Walk.cons uv p).support}
    have inc : {j | j ∈ p.support} ⊆ A := fun j hj => by
      exact List.mem_cons_of_mem _ hj
    let f := (T.induceHomOfLE inc).toHom
    let a : A := ⟨u, List.mem_cons_self⟩
    let b : {j | j ∈ p.support} := ⟨v,p.start_mem_support⟩
    have ab : (T.induce A).Adj a (f b) := uv
    apply ((T.induce A).connected_iff_exists_forall_reachable).mpr
    refine ⟨a, ?_⟩
    rintro ⟨j,hj⟩
    rcases List.mem_cons.mp hj with rfl | tail
    · exact SimpleGraph.Reachable.refl _
    · exact ab.reachable.trans ((ih b ⟨j,tail⟩).map f)

/-- A walk through at least one occurrence of each requested vertex. -/
private theorem covering_walk {H : SimpleGraph W} {k : ℕ}
    (D : TreeSemantics.Decomposition H J k) (root : J) (S : Finset W) :
    ∃ p : D.tree.Walk root root, ∀ x ∈ S, ∃ j ∈ p.support, x ∈ D.bag j := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨.nil, by simp⟩
  | @insert x S _ ih =>
    obtain ⟨p,hp⟩ := ih
    obtain ⟨i,hi⟩ := D.vertex x
    let q := (D.isTree.isConnected root i).some
    refine ⟨p.append (q.append q.reverse), ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨i, (p.mem_support_append_iff _).mpr (Or.inr
          ((q.mem_support_append_iff _).mpr (Or.inl q.end_mem_support))), hi⟩
    · obtain ⟨j,hj,hb⟩ := hp y hy
      exact ⟨j,(p.mem_support_append_iff _).mpr (Or.inl hj),hb⟩

/-- On a shortest suffix covering the requested vertices, one vertex occurs
only in its first bag. Each neighbour must occur there too, by subtree Helly. -/
private theorem corner_on_walk {H : SimpleGraph W} {k : ℕ}
    (D : TreeSemantics.Decomposition H J k) {S : Finset W} (hS : S.Nonempty)
    {u v : J} (p : D.tree.Walk u v)
    (cover : ∀ x ∈ S, ∃ j ∈ p.support, x ∈ D.bag j) :
    ∃ x ∈ S, ∃ i, x ∈ D.bag i ∧ ∀ y ∈ S, H.Adj x y → y ∈ D.bag i := by
  classical
  induction p with
  | @nil u =>
    obtain ⟨x,hx⟩ := hS
    have here (y) (hy : y ∈ S) : y ∈ D.bag u := by
      obtain ⟨j,hj,hb⟩ := cover y hy
      obtain rfl := SimpleGraph.Walk.mem_support_nil_iff.mp hj
      exact hb
    exact ⟨x,hx,u,here x hx,fun y hy _ => here y hy⟩
  | @cons u v w uv p ih =>
    by_cases allTail : ∀ x ∈ S, ∃ j ∈ p.support, x ∈ D.bag j
    · exact ih allTail
    · push_neg at allTail
      obtain ⟨x,hx,miss⟩ := allTail
      have only (j) (hj : j ∈ (SimpleGraph.Walk.cons uv p).support)
          (hb : x ∈ D.bag j) : j = u := by
        rcases List.mem_cons.mp hj with e | tail
        · exact e
        · exact (miss j tail hb).elim
      obtain ⟨i,hi,hb⟩ := cover x hx
      have xu : x ∈ D.bag u := only i hi hb ▸ hb
      refine ⟨x,hx,u,xu,?_⟩
      intro y hy hxy
      obtain ⟨a,ax,ay⟩ := D.edge x y hxy
      obtain ⟨b,bs,by'⟩ := cover y hy
      let q := SimpleGraph.Walk.cons uv p
      obtain ⟨j,jx,jy,js⟩ := TreeSemantics.three_subtrees D.tree D.isTree
        {j | x ∈ D.bag j} {j | y ∈ D.bag j} {j | j ∈ q.support}
        (D.running x) (D.running y) (support_connected q)
        ax ay xu q.start_mem_support by' bs
      exact only j js jx ▸ jy

/-- Standard treewidth at most one implies one-degeneracy. -/
theorem oneDegenerate_of_width_one {H : SimpleGraph W} (hw : TreeSemantics.WidthLE H 1) :
    OneDegenerate H := by
  classical
  obtain ⟨J,_,⟨D⟩⟩ := hw
  intro S hS
  obtain ⟨root⟩ := D.isTree.isConnected.nonempty
  obtain ⟨p,hp⟩ := covering_walk D root S
  obtain ⟨x,hx,i,xi,near⟩ := corner_on_walk D hS p hp
  refine ⟨x,hx,?_⟩
  intro y hy z hz hxy hxz
  by_contra hyz
  have sub : ({x,y,z} : Finset W) ⊆ D.bag i := by
    simpa [Finset.insert_subset_iff] using And.intro xi ⟨near y hy hxy,near z hz hxz⟩
  have lower := Finset.card_le_card sub
  have three : ({x,y,z} : Finset W).card = 3 := by simp [hxy.ne,hxz.ne,hyz]
  have upper := D.width i
  omega

end Bootstrap.TreeLinear

#print axioms Bootstrap.TreeLinear.oneDegenerate_of_width_one
