import Bootstrap.HubBags
import Bootstrap.RuleStructure
import Bootstrap.MarkedSimulation

namespace Bootstrap.SourceBags

open Localization MarkedSimulation TreeBags

private theorem zero_or_one (k : Fin 2) : k = 0 ∨ k = 1 := by
  by_cases hz : k.val = 0
  · exact Or.inl (Fin.ext hz)
  · exact Or.inr (Fin.ext (by have := k.isLt; omega))

private def Extra : HVertex → Prop
  | .core _ j => 2 ≤ j.val
  | .page _ _ => False

private def IsPage : HVertex → Prop
  | .core _ _ => False
  | .page _ _ => True

private def leftEnd : {v : HVertex // IsPage v} → HVertex
  | ⟨.core _ _, h⟩ => h.elim
  | ⟨.page b j, _⟩ => .core b (pageLo sourceCode b j)

private def rightEnd : {v : HVertex // IsPage v} → HVertex
  | ⟨.core _ _, h⟩ => h.elim
  | ⟨.page b j, _⟩ => .core b (pageHi sourceCode b j)

private theorem pageAnchors (b : Block TypedRound.Role) (j : Fin (pageCount sourceCode b)) :
    CoreEdge (pageLo sourceCode b j) (pageHi sourceCode b j) := by
  refine ⟨fun h => (Nat.ne_of_lt (pageLo_lt_hi sourceCode b j)) (congrArg Fin.val h),Or.inl ?_⟩
  simp only [pageLo]
  split <;> decide

private theorem both_hubs_mem {s : Finset HVertex} {b : Block TypedRound.Role}
    (h₀ : hub b 0 ∈ s) (h₁ : hub b 1 ∈ s) (k : Fin 2) : hub b k ∈ s := by
  rcases zero_or_one k with rfl | rfl <;> assumption

private theorem together_incl {F F' : Finset (Finset HVertex)} (h : F ⊆ F') {x y : HVertex}
    (ht : TreeBags.Together F x y) : TreeBags.Together F' x y := by
  obtain ⟨s,hs,hx,hy⟩ := ht
  exact ⟨s,h hs,hx,hy⟩

open scoped Classical in
theorem source_width_at_most_two : WidthLE ordinaryRule 2 := by
  classical
  let first : {v : HVertex // Extra v} ↪ HVertex := Function.Embedding.subtype _
  let a := fun v : {v : HVertex // Extra v} => hub (owner v.val) 0
  let b := fun v : {v : HVertex // Extra v} => hub (owner v.val) 1
  have fresh (i : {v : HVertex // Extra v}) : ¬ Occurs hubs (first i) := by
    intro already
    obtain ⟨d,k,h⟩ := only_hubs already
    have prop := i.property
    change i.val = hub d k at h
    rw [h] at prop
    change 2 ≤ k.val at prop
    exact (Nat.not_le_of_gt k.isLt) prop
  obtain ⟨F,T,subF,added,onlyF⟩ := starLeaves hubs_tree first a b fresh (fun i => base_edge (owner i.val))
  have coreHub (d : Block TypedRound.Role) (j : Fin (blockSize sourceCode d)) (k : Fin 2) :
      TreeBags.Together F (.core d j) (hub d k) := by
    by_cases hj : j.val < 2
    · let t : Fin 2 := ⟨j.val,hj⟩
      have h : (Vertex.core d j : HVertex) = hub d t := rfl
      obtain ⟨s,hs,h₀,h₁⟩ := base_edge d
      exact ⟨s,subF hs,h.symm ▸ both_hubs_mem h₀ h₁ t,both_hubs_mem h₀ h₁ k⟩
    · let v : {x : HVertex // Extra x} := ⟨.core d j, Nat.le_of_not_gt hj⟩
      refine ⟨_,added v, Finset.mem_insert_self _ _,?_⟩
      rcases zero_or_one k with rfl | rfl
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have corePair (d : Block TypedRound.Role) (i j : Fin (blockSize sourceCode d)) (h : CoreEdge i j) :
      TreeBags.Together F (.core d i) (.core d j) := by
    rcases h.2 with hi | hj
    · exact together_symm (coreHub d j ⟨i.val,hi⟩)
    · exact coreHub d i ⟨j.val,hj⟩
  let second : {v : HVertex // IsPage v} ↪ HVertex := Function.Embedding.subtype _
  have newPage (i : {v : HVertex // IsPage v}) : ¬ Occurs F (second i) := by
    intro seen
    rcases i with ⟨v,hv⟩
    cases v with
    | core _ _ => exact hv.elim
    | page d j =>
      rcases onlyF _ seen with old | ⟨c,eq⟩
      · obtain ⟨d',k,e⟩ := only_hubs old
        cases e
      · have hc := c.property
        change c.val = .page d j at eq
        rw [eq] at hc
        exact hc
  have anchors (i : {v : HVertex // IsPage v}) : TreeBags.Together F (leftEnd i) (rightEnd i) := by
    rcases i with ⟨v,h⟩
    cases v with
    | core _ _ => exact h.elim
    | page d j => exact corePair d _ _ (pageAnchors d j)
  obtain ⟨F',T',sub',pages,_⟩ := starLeaves T second leftEnd rightEnd newPage anchors
  have pagesAt (d : Block TypedRound.Role) (j : Fin (pageCount sourceCode d)) :
      ({Vertex.page d j,Vertex.core d (pageLo sourceCode d j),Vertex.core d (pageHi sourceCode d j)}
        : Finset HVertex) ∈ F' := pages ⟨.page d j,True.intro⟩
  have arcCovered {x y : HVertex} (h : Arc TypedRound.rule sourceCode port x y) :
      TreeBags.Together F' x y := by
    cases h with
    | book d i j e => exact together_incl sub' (corePair d i j e)
    | matching r k => exact together_incl sub' (together_incl subF (matching_edge r k))
    | logical r s h => exact together_incl sub' (together_incl subF (logical_edge h))
    | pageLeft d j =>
      exact ⟨_,pagesAt d j, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
    | pageRight d j =>
      exact ⟨_,pagesAt d j, Finset.mem_insert_self _ _,
        Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
  refine ⟨F',T',?_,fun _ _ h => h.elim arcCovered (fun e => together_symm (arcCovered e))⟩
  intro v
  cases v with
  | core d j =>
    obtain ⟨s,hs,mem,_⟩ := coreHub d j 0
    exact ⟨s,sub' hs,mem⟩
  | page d j => exact ⟨_,pagesAt d j,Finset.mem_insert_self _ _⟩

theorem source_triangle : ∃ a b c : HVertex, ordinaryRule.Adj a b ∧ ordinaryRule.Adj a c ∧ ordinaryRule.Adj b c := by
  let d : Block TypedRound.Role := .primary (.inl (.endpoint false))
  let a : Fin (blockSize sourceCode d) := hubIdx sourceCode d 0
  let b : Fin (blockSize sourceCode d) := hubIdx sourceCode d 1
  let c : Fin (blockSize sourceCode d) := ⟨2,blockSize_three _ _⟩
  refine ⟨.core d a,.core d b,.core d c,Or.inl (.book d a b ?_),Or.inl (.book d a c ?_),Or.inl (.book d b c ?_)⟩
  all_goals unfold CoreEdge; decide

open scoped Classical in
theorem source_width_exactly_two : WidthLE ordinaryRule 2 ∧ ¬ WidthLE ordinaryRule 1 := by
  obtain ⟨a,b,c,ab,ac,bc⟩ := source_triangle
  exact ⟨source_width_at_most_two,triangle_forbids_width_one _ ab ac bc⟩

end Bootstrap.SourceBags

#print axioms Bootstrap.SourceBags.source_width_exactly_two
