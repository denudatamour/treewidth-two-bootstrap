import Bootstrap.ConnectedDegreeTwo
import Bootstrap.TreeBags

/-! Suppress a degree-two vertex in an ordinary graph. The two neighbours are joined in
the smaller graph whether or not they were already joined in the larger graph. -/
namespace Bootstrap.Suppression

variable {V U : Type*}

abbrev Rest (v : V) := {a : V // a ≠ v}

/-- A finite graph of order at least three, connected also after any single deletion. -/
structure TwoConnected [Fintype V] (H : SimpleGraph V) : Prop where
  order : 3 ≤ Fintype.card V
  connected : H.Connected
  delete : ∀ z, (H.induce {a | a ≠ z}).Connected

def graph (H : SimpleGraph V) (v : V) (x y : Rest v) (hxy : x ≠ y) :
    SimpleGraph (Rest v) where
  Adj a b := H.Adj a.val b.val ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x)
  symm := by
    rintro a b (h | ⟨ax,by'⟩ | ⟨ay,bx⟩)
    · exact Or.inl (H.symm h)
    · exact Or.inr (Or.inr ⟨by',ax⟩)
    · exact Or.inr (Or.inl ⟨bx,ay⟩)
  loopless := by
    rintro a (h | ⟨ax,ay⟩ | ⟨ay,ax⟩)
    · exact H.irrefl h
    all_goals exact hxy (ax.symm.trans ay)

/-- Reversing suppression subdivides the joined edge if it was absent in H, and adds
a common neighbour along that edge if it was present in H. The old rule is identified
up to ordinary graph isomorphism. -/
def Extension (A : SimpleGraph U) (H : SimpleGraph V) : Prop :=
  ∃ (v : V) (x y : Rest v) (hne : x ≠ y),
    DegreeTwo.TwoNeighbours H v x.val y.val ∧ Nonempty (A ≃g graph H v x y hne)

noncomputable def foldV (v : V) (s : Rest v) (a : V) : Rest v := by
  classical
  exact if h : a = v then s else ⟨a,h⟩

@[simp] theorem fold_here (v : V) (s : Rest v) : foldV v s v = s := by
  classical
  simp [foldV]

@[simp] theorem fold_rest (v : V) (s a : Rest v) : foldV v s a.val = a := by
  classical
  simp [foldV, a.property]

private theorem fold_edge {H : SimpleGraph V} {v : V} {x y : Rest v} (hne : x ≠ y)
    (N : DegreeTwo.TwoNeighbours H v x.val y.val) {s : Rest v} (hs : s = x ∨ s = y)
    {a b : V} (h : H.Adj a b) :
    foldV v s a = foldV v s b ∨ (graph H v x y hne).Adj (foldV v s a) (foldV v s b) := by
  classical
  have first {b : V} (e : H.Adj v b) : foldV v s v = foldV v s b ∨
      (graph H v x y hne).Adj (foldV v s v) (foldV v s b) := by
    rcases N.only b e with rfl | rfl <;> simp only [fold_here, fold_rest]
    · rcases hs with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))
    · rcases hs with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))
      · exact Or.inl rfl
  by_cases av : a = v
  · subst a
    exact first h
  by_cases bv : b = v
  · subst b
    rcases first (H.symm h) with e | e
    · exact Or.inl e.symm
    · exact Or.inr e.symm
  · change foldV v s (⟨a,av⟩ : Rest v).val = foldV v s (⟨b,bv⟩ : Rest v).val ∨ _
    simp only [fold_rest, foldV, dif_neg av, dif_neg bv]
    exact Or.inr (Or.inl h)

private theorem weak_map {G : SimpleGraph V} {K : SimpleGraph U} (f : V → U)
    (h : ∀ a b, G.Adj a b → f a = f b ∨ K.Adj (f a) (f b)) {a b : V}
    (r : G.Reachable a b) : K.Reachable (f a) (f b) := by
  obtain ⟨p⟩ := r
  induction p with
  | nil => exact .refl _
  | cons e _ ih =>
    rcases h _ _ e with eq | e'
    · exact eq ▸ ih
    · exact e'.reachable.trans ih

theorem order_rest [Fintype V] (v : V) [Fintype (Rest v)] :
    Fintype.card (Rest v) = Fintype.card V - 1 := by
  classical
  simp [Rest]

theorem preserves_twoConnected [Fintype V] {H : SimpleGraph V} (T : TwoConnected H)
    (four : 4 ≤ Fintype.card V) {v : V} [Fintype (Rest v)] {x y : Rest v} (hne : x ≠ y)
    (N : DegreeTwo.TwoNeighbours H v x.val y.val) : TwoConnected (graph H v x y hne) := by
  classical
  refine ⟨by rw [order_rest]; omega,?_,?_⟩
  · haveI : Nonempty (Rest v) := ⟨x⟩
    constructor
    intro a b
    simpa only [fold_rest] using weak_map (foldV v x) (fun _ _ => fold_edge hne N (Or.inl rfl))
      (T.connected a.val b.val)
  · intro z
    obtain ⟨s,hs,sz⟩ : ∃ s : Rest v, (s = x ∨ s = y) ∧ s ≠ z := by
      by_cases e : x = z
      · exact ⟨y,Or.inr rfl,fun t => hne (e.trans t.symm)⟩
      · exact ⟨x,Or.inl rfl,e⟩
    refine @SimpleGraph.Connected.mk _ _ ?_ ⟨⟨s,sz⟩⟩
    intro a b
    let f (t : {u : V // u ≠ z.val}) : {u : Rest v // u ≠ z} :=
      ⟨foldV v s t.val, by
        by_cases e : t.val = v
        · simpa only [e,fold_here] using sz
        · change foldV v s (⟨t.val,e⟩ : Rest v).val ≠ z
          rw [fold_rest]
          exact fun eq => t.property (congrArg Subtype.val eq)⟩
    let lift (t : {u : Rest v // u ≠ z}) : {u : V // u ≠ z.val} :=
      ⟨t.val.val, fun eq => t.property (Subtype.ext eq)⟩
    have fix (t : {u : Rest v // u ≠ z}) : f (lift t) = t :=
      Subtype.ext (fold_rest v s t.val)
    have mapped := @weak_map _ _ (H.induce {u | u ≠ z.val})
      ((graph H v x y hne).induce {u | u ≠ z}) f (by
        intro c d cd
        rcases fold_edge hne N hs cd with e | e
        · exact Or.inl (Subtype.ext e)
        · exact Or.inr e) (lift a) (lift b) (T.delete z.val (lift a) (lift b))
    simpa only [fix] using mapped

private theorem first_neighbor {G : SimpleGraph V} {a b : V} (ab : a ≠ b)
    (r : G.Reachable a b) : ∃ c, G.Adj a c := by
  obtain ⟨p⟩ := r
  cases p with
  | nil => exact (ab rfl).elim
  | cons h _ => exact ⟨_,h⟩

theorem two_neighbors [Fintype V] {H : SimpleGraph V} (T : TwoConnected H) (v : V) :
    ∃ x y, H.Adj v x ∧ H.Adj v y ∧ x ≠ y := by
  classical
  have o := T.order
  have other : ∀ (s : Finset V), s.card < Fintype.card V → ∃ z, z ∉ s := by
    intro s hs
    by_contra! no
    have eq : s = Finset.univ := Finset.eq_univ_of_forall no
    simp only [eq, Finset.card_univ, lt_self_iff_false] at hs
  obtain ⟨t,ht⟩ := other {v} (by simp; omega)
  have tv : t ≠ v := by simpa using ht
  obtain ⟨x,vx⟩ := first_neighbor tv.symm (T.connected v t)
  obtain ⟨u,hu⟩ := other {v,x} (by simp [vx.ne]; omega)
  have uv : u ≠ v ∧ u ≠ x := by simpa using hu
  let v' : {a : V // a ≠ x} := ⟨v,vx.ne⟩
  let u' : {a : V // a ≠ x} := ⟨u,uv.2⟩
  obtain ⟨y,hy⟩ := first_neighbor (a := v') (b := u')
    (fun e => uv.1 (congrArg Subtype.val e).symm) (T.delete x v' u')
  exact ⟨x,y.val,vx,hy,y.property.symm⟩


section Bags
open TreeBags

/-- The newest bag introducing any vertex contains every co-occurring neighbour of
one of those vertices. Bags which introduce none can be passed over. -/
private theorem simplicial_bag [DecidableEq V] [Nonempty V] {k : Nat}
    {F : Finset (Finset V)} (T : Tree k F) (allV : ∀ a, Occurs F a) :
    ∃ (v : V) (b : Finset V), b ∈ F ∧ v ∈ b ∧ ∀ a, Together F v a → a ∈ b := by
  classical
  induction T with
  | root b width =>
    let v : V := Classical.arbitrary _
    obtain ⟨D,hD,hv⟩ := allV v
    have e : D = b := Finset.mem_singleton.mp hD
    refine ⟨v,b,Finset.mem_singleton_self _,e ▸ hv,?_⟩
    rintro a ⟨D,hD,_,ha⟩
    exact (Finset.mem_singleton.mp hD : D = b) ▸ ha
  | @attach F old p hp l wl glue ih =>
    by_cases oldV : ∀ v, Occurs F v
    · obtain ⟨v,b,hb,vb,h⟩ := ih oldV
      refine ⟨v,b,Finset.mem_insert_of_mem hb,vb,?_⟩
      rintro a ⟨D,hD,vD,aD⟩
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact h a ⟨p,hp,glue v vD (oldV v),glue a aD (oldV a)⟩
      · exact h a ⟨D,hD,vD,aD⟩
    · push_neg at oldV
      obtain ⟨v,hv⟩ := oldV
      obtain ⟨D,hD,vD⟩ := allV v
      rcases Finset.mem_insert.mp hD with rfl | hD
      · refine ⟨v,D,Finset.mem_insert_self _ _,vD,?_⟩
        rintro a ⟨b,hb,vb,ab⟩
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact ab
        · exact (hv ⟨b,hb,vb⟩).elim
      · exact (hv ⟨D,hD,vD⟩).elim

/-- Restrict all bags to the surviving vertex set. -/
private theorem restrict_tree [DecidableEq V] (v : V) {k : Nat} {F : Finset (Finset V)}
    (T : Tree k F) :
    Tree k (F.image (fun b => b.subtype (fun a => a ≠ v))) := by
  classical
  let f (b : Finset V) := b.subtype (fun a => a ≠ v)
  have wc (b : Finset V) : (f b).card ≤ b.card := by
    change (Finset.map _ (Finset.attach (b.filter _))).card ≤ _
    simpa only [Finset.card_map,Finset.card_attach] using Finset.card_filter_le b _
  induction T with
  | root b h =>
    rw [Finset.image_singleton]
    exact Tree.root (f b) ((wc b).trans h)
  | @attach F old p hp b wb glue ih =>
    rw [Finset.image_insert]
    apply Tree.attach ih (p := f p) (Finset.mem_image_of_mem _ hp) _ ((wc b).trans wb)
    intro a ab old
    obtain ⟨D,hD,aD⟩ := old
    obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hD
    exact Finset.mem_subtype.mpr (glue a.val (Finset.mem_subtype.mp ab)
      ⟨E,hE,Finset.mem_subtype.mp aD⟩)

theorem reducible [Fintype V] [DecidableEq V] {H : SimpleGraph V} (TC : TwoConnected H)
    (W : TreeBags.WidthLE H 2) :
    ∃ (v : V) (x y : Rest v) (hne : x ≠ y), DegreeTwo.TwoNeighbours H v x.val y.val ∧
      TreeBags.WidthLE (graph H v x y hne) 2 := by
  classical
  haveI : Nonempty V := TC.connected.nonempty
  obtain ⟨F,T,allV,edges⟩ := W
  obtain ⟨v,b,hb,vb,neighbors⟩ := simplicial_bag T allV
  obtain ⟨x,y,vx,vy,xy⟩ := two_neighbors TC v
  have xb := neighbors x (edges v x vx)
  have yb := neighbors y (edges v y vy)
  have sub : ({v,x,y} : Finset V) ⊆ b := by
    simpa [Finset.insert_subset_iff] using ⟨vb,xb,yb⟩
  have eq : ({v,x,y} : Finset V) = b := Finset.eq_of_subset_of_card_le sub (by
    simpa [vx.ne,vy.ne,xy] using bag_size T hb)
  let a : Rest v := ⟨x,vx.ne.symm⟩
  let c : Rest v := ⟨y,vy.ne.symm⟩
  have ac : a ≠ c := fun e => xy (congrArg Subtype.val e)
  refine ⟨v,a,c,ac,⟨vx,vy,xy,?_⟩,?_⟩
  · intro t vt
    have ht := neighbors t (edges v t vt)
    rw [← eq] at ht
    rcases Finset.mem_insert.mp ht with e | h
    · exact (vt.ne e.symm).elim
    · simpa using h
  · let f (D : Finset V) := D.subtype (fun u => u ≠ v)
    refine ⟨F.image f,restrict_tree v T,?_,?_⟩
    · intro t
      obtain ⟨D,hD,tD⟩ := allV t.val
      exact ⟨f D,Finset.mem_image_of_mem _ hD,Finset.mem_subtype.mpr tD⟩
    · rintro s t (st | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · obtain ⟨D,hD,sD,tD⟩ := edges _ _ st
        exact ⟨f D,Finset.mem_image_of_mem _ hD,Finset.mem_subtype.mpr sD,Finset.mem_subtype.mpr tD⟩
      · exact ⟨f b,Finset.mem_image_of_mem _ hb,Finset.mem_subtype.mpr xb,Finset.mem_subtype.mpr yb⟩
      · exact ⟨f b,Finset.mem_image_of_mem _ hb,Finset.mem_subtype.mpr yb,Finset.mem_subtype.mpr xb⟩
end Bags

end Bootstrap.Suppression

#print axioms Bootstrap.Suppression.preserves_twoConnected
#print axioms Bootstrap.Suppression.two_neighbors
#print axioms Bootstrap.Suppression.reducible
