import Bootstrap.ExtensionCorollary

namespace Bootstrap.Suppression

variable {U V : Type*}

/-- The designated edge as a symmetric predicate on ordered endpoints. -/
def EdgePair (i j a b : U) := (a = i ∧ b = j) ∨ (a = j ∧ b = i)

/-- Forward formulation of one operation. The injection labels all old vertices,
its complement consists of one new vertex, and the old adjacency relation is
either retained or has precisely the designated edge removed. -/
def ForwardExtension (A : SimpleGraph U) (B : SimpleGraph V) : Prop :=
  ∃ (f : U ↪ V) (w : V) (i j : U), i ≠ j ∧ A.Adj i j ∧
    (∀ t, t ∈ Set.range f ↔ t ≠ w) ∧
    (∀ t, B.Adj w (f t) ↔ t = i ∨ t = j) ∧
    ((∀ a b, B.Adj (f a) (f b) ↔ A.Adj a b) ∨
     (∀ a b, B.Adj (f a) (f b) ↔ A.Adj a b ∧ ¬EdgePair i j a b))

theorem Extension.forward {A : SimpleGraph U} {B : SimpleGraph V} (ext : Extension A B) :
    ForwardExtension A B := by
  classical
  obtain ⟨w,x,y,xy,N,⟨e⟩⟩ := ext
  let f : U ↪ V := e.toEquiv.toEmbedding.trans (Function.Embedding.subtype _)
  let i : U := e.symm x
  let j : U := e.symm y
  have xi : e i = x := e.toEquiv.apply_symm_apply x
  have yj : e j = y := e.toEquiv.apply_symm_apply y
  have eqI (a : U) : e a = x ↔ a = i := ⟨fun h => e.injective (h.trans xi.symm),fun h => (congrArg e h).trans xi⟩
  have eqJ (a : U) : e a = y ↔ a = j := ⟨fun h => e.injective (h.trans yj.symm),fun h => (congrArg e h).trans yj⟩
  have rel (a b : U) : A.Adj a b ↔ B.Adj (f a) (f b) ∨ EdgePair i j a b := by
    rw [← e.map_adj_iff]
    change (B.Adj (f a) (f b) ∨ (e a = x ∧ e b = y) ∨ (e a = y ∧ e b = x)) ↔ _
    simp only [eqI,eqJ,EdgePair]
  have ij : i ≠ j := fun h => xy (xi.symm.trans ((congrArg e h).trans yj))
  refine ⟨f,w,i,j,ij,(rel i j).mpr (Or.inr (Or.inl ⟨rfl,rfl⟩)),?_,?_,?_⟩
  · intro t
    constructor
    · rintro ⟨a,rfl⟩
      exact (e a).property
    · intro tw
      let z : Rest w := ⟨t,tw⟩
      exact ⟨e.symm z,congrArg Subtype.val (e.toEquiv.apply_symm_apply z)⟩
  · intro t
    constructor
    · intro h
      rcases N.only (f t) h with a | a
      · exact Or.inl ((eqI t).mp (Subtype.ext a))
      · exact Or.inr ((eqJ t).mp (Subtype.ext a))
    · rintro (rfl | rfl)
      · change B.Adj w (e i).val
        rw [xi]
        exact N.left
      · change B.Adj w (e j).val
        rw [yj]
        exact N.right
  · by_cases retained : B.Adj (f i) (f j)
    · left
      intro a b
      refine ⟨fun h => (rel a b).mpr (Or.inl h),fun h => ?_⟩
      rcases (rel a b).mp h with h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact h
      · exact retained
      · exact B.symm retained
    · right
      intro a b
      constructor
      · intro h
        refine ⟨(rel a b).mpr (Or.inl h),?_⟩
        rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
        · exact retained h
        · exact retained (B.symm h)
      · rintro ⟨h,different⟩
        exact ((rel a b).mp h).resolve_right different

/-- Corollary II.3 with both forward operations stated by their exact ordinary adjacency. -/
theorem corollary_forward :
    ∃ (U V : Type) (fU : Fintype U) (fV : Fintype V) (A : SimpleGraph U) (B : SimpleGraph V),
      @TwoConnected U fU A ∧ @TwoConnected V fV B ∧
      TreeSemantics.WidthLE A 2 ∧ ¬TreeSemantics.WidthLE A 1 ∧
      TreeSemantics.WidthLE B 2 ∧ ¬TreeSemantics.WidthLE B 1 ∧
      ForwardExtension A B ∧ HasLinearUpper A ∧ ¬HasLinearUpper B := by
  obtain ⟨U,V,fu,fv,A,B,ca,cb,wa,na,wb,nb,e,l,n⟩ := Preprint.corollary_II_3
  exact ⟨U,V,fu,fv,A,B,ca,cb,wa,na,wb,nb,e.forward,l,n⟩

end Bootstrap.Suppression

#print axioms Bootstrap.Suppression.corollary_forward
