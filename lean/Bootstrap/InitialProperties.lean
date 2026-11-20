import Bootstrap.MarkedSimulation
import Bootstrap.RuleStructure
import Bootstrap.OrdinaryTime
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Bootstrap.MarkedSimulation

open Localization
open TypedRound (Kind)

private def zeroFin {n : ℕ} (h : 0 < n) : Fin n := ⟨0,h⟩

/-- One full track connects each endpoint to the next; no wrap is needed to reach
a prescribed index from zero. -/
private theorem side_reachable {n : ℕ} {V : Type*} (hn : 0 < n) (G : SimpleGraph V)
    (put : Kind × Fin n → V)
    (arc : ∀ a b, TypedRound.pathArc TypedRound.nextIndex a b → G.Adj (put a) (put b))
    (u : Kind × Fin n) : G.Reachable (put (.endpoint,zeroFin hn)) (put u) := by
  have stepPath (i : Fin n) :
      G.Reachable (put (.endpoint,i)) (put (.endpoint,TypedRound.nextIndex i)) :=
    (arc (.endpoint,i) (.u false,i) rfl).reachable.trans
      ((arc (.u false,i) (.v false,i) ⟨rfl,rfl⟩).reachable.trans
       (arc (.v false,i) (.endpoint,TypedRound.nextIndex i) rfl).reachable)
  have toEnd (i : Fin n) : G.Reachable (put (.endpoint,zeroFin hn)) (put (.endpoint,i)) := by
    rcases i with ⟨i,hi⟩
    induction i with
    | zero => exact SimpleGraph.Reachable.rfl
    | succ i ih =>
      let prev : Fin n := ⟨i,by omega⟩
      have he : TypedRound.nextIndex prev = ⟨i+1,hi⟩ := by
        simp [TypedRound.nextIndex,prev,hi]
      rw [← he]
      exact (ih (by omega)).trans (stepPath prev)
  rcases u with ⟨k,i⟩
  cases k with
  | endpoint => exact toEnd i
  | u b => exact (toEnd i).trans (arc (.endpoint,i) (.u b,i) rfl).reachable
  | v b => exact (toEnd i).trans ((arc (.endpoint,i) (.u b,i) rfl).reachable.trans
      (arc (.u b,i) (.v b,i) ⟨rfl,rfl⟩).reachable)

theorem logical_initial_connected {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (TypedRound.host TypedRound.nextIndex TypedRound.nextIndex (@TypedRound.origin p q)).Connected := by
  let G := TypedRound.host TypedRound.nextIndex TypedRound.nextIndex (@TypedRound.origin p q)
  let a : TypedRound.Host (Fin p) (Fin q) := TypedRound.xEnd (zeroFin hp)
  let b : TypedRound.Host (Fin p) (Fin q) := TypedRound.yEnd (zeroFin hq)
  have cross : G.Adj a b :=
    (TypedRound.cross_edge_iff _ _ _ _ _).2 ⟨rfl,rfl⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨a,?_⟩
  rintro (u|u)
  · exact side_reachable hp G Sum.inl (fun _ _ h => Or.inl (Or.inl h)) u
  · exact cross.reachable.trans (side_reachable hq G Sum.inr (fun _ _ h => Or.inl (Or.inl h)) u)

private def representative {I : Type*} (ty : I → Fin 10) (i : I) : HostVertex ty :=
  .core (.primary i) (hubIdx ty (.primary i) 0)

private def primaryHom {I : Type*} (F : SimpleGraph I) (ty : I → Fin 10) :
    F →g Localization.host F ty where
  toFun := representative ty
  map_rel' h := ⟨fun e => h.ne (congrArg vertexRole e),Or.inr h⟩

private theorem reaches_primary {I : Type*} (F : SimpleGraph I) (ty : I → Fin 10)
    (x : HostVertex ty) : (Localization.host F ty).Reachable x (representative ty (vertexRole x)) := by
  have secondary (i : I) (a : Fin (blockSize ty (.secondary i))) :
      (Localization.host F ty).Adj (.core (.secondary i) a) (representative ty i) := by
    constructor
    · intro e
      cases e
    · exact Or.inr rfl
  cases x with
  | core b a =>
    cases b with
    | primary i =>
      by_cases he : a = hubIdx ty (.primary i) 0
      · subst a; exact SimpleGraph.Reachable.rfl
      · apply SimpleGraph.Adj.reachable
        constructor
        · intro e
          exact he (Fin.ext (congrArg vindex e))
        · exact Or.inl rfl
    | secondary i => exact (secondary i a).reachable
  | page b a =>
    cases b with
    | primary i =>
      exact (show (Localization.host F ty).Adj (.page (.primary i) a) (representative ty i) from rfl).reachable
    | secondary i =>
      let k := hubIdx ty (.secondary i) 0
      have he : (Localization.host F ty).Adj (.page (.secondary i) a) (.core (.secondary i) k) := rfl
      exact he.reachable.trans (secondary i k).reachable

theorem connected_expansion {I : Type*} (F : SimpleGraph I) (ty : I → Fin 10)
    (hF : F.Connected) : (Localization.host F ty).Connected := by
  obtain ⟨r⟩ := hF.nonempty
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨representative ty r,fun y => ?_⟩
  exact ((hF r (vertexRole y)).map (primaryHom F ty)).trans (reaches_primary F ty y).symm

theorem initial_connected {p q : ℕ} (hp : 0 < p) (hq : 0 < q) : (initial p q).Connected :=
  connected_expansion _ _ (logical_initial_connected hp hq)

end Bootstrap.MarkedSimulation

#print axioms Bootstrap.MarkedSimulation.initial_connected


namespace Bootstrap.MarkedSimulation

open Localization
open TypedRound (Kind)
open scoped Classical BigOperators

private def previous {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  if i.val = 0 then ⟨n-1,by omega⟩ else ⟨i.val-1,by have := i.isLt; omega⟩

private theorem next_previous {n : ℕ} (hn : 0 < n) (i : Fin n) :
    TypedRound.nextIndex (previous hn i) = i := by
  apply Fin.ext
  have hi := i.isLt
  unfold previous
  split
  · rename_i h
    simp [TypedRound.nextIndex,h,show ¬ n - 1 + 1 < n by omega]
  · rename_i h
    have ht : i.val-1+1 < n := by omega
    simp [TypedRound.nextIndex,ht]
    omega

private def sideList {n : ℕ} {V : Type*} (hn : 0 < n) (put : Kind × Fin n → V)
    (other : V) : Kind × Fin n → List V
  | (.endpoint,i) => [put (.u false,i),put (.u true,i),put (.v false,previous hn i),
      put (.v true,previous hn i),other]
  | (.u k,i) => [put (.endpoint,i),put (.v k,i)]
  | (.v k,i) => [put (.u k,i),put (.endpoint,TypedRound.nextIndex i)]

private theorem listed_track {n : ℕ} {V : Type*} (hn : 0 < n) (put : Kind × Fin n → V) (other : V)
    (a b : Kind × Fin n)
    (h : TypedRound.pathArc TypedRound.nextIndex a b ∨ TypedRound.pathArc TypedRound.nextIndex b a) :
    put b ∈ sideList hn put other a := by
  rcases a with ⟨k,i⟩
  rcases b with ⟨l,j⟩
  cases k with
  | endpoint =>
    cases l with
    | endpoint => exact False.elim (h.elim id id)
    | u l =>
      have he : i = j := by simpa [TypedRound.pathArc] using h
      subst j; cases l <;> simp [sideList]
    | v l =>
      have he : TypedRound.nextIndex j = i := by simpa [TypedRound.pathArc] using h
      have he' := TypedRound.nextIndex_injective n (he.trans (next_previous hn i).symm)
      subst j; cases l <;> simp [sideList]
  | u k =>
    cases l with
    | endpoint =>
      have he : j = i := by simpa [TypedRound.pathArc] using h
      simp [sideList,he]
    | u l => exact False.elim (h.elim id id)
    | v l =>
      obtain ⟨rfl,rfl⟩ : k = l ∧ i = j := by simpa [TypedRound.pathArc] using h
      simp [sideList]
  | v k =>
    cases l with
    | endpoint =>
      have he : TypedRound.nextIndex i = j := by simpa [TypedRound.pathArc] using h
      simp [sideList,he]
    | u l =>
      obtain ⟨rfl,rfl⟩ : l = k ∧ j = i := by simpa [TypedRound.pathArc] using h
      simp [sideList]
    | v l => exact False.elim (h.elim id id)

private def candidates {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    TypedRound.Host (Fin p) (Fin q) → List (TypedRound.Host (Fin p) (Fin q))
  | .inl a => sideList hp Sum.inl (TypedRound.yEnd ⟨0,hq⟩) a
  | .inr b => sideList hq Sum.inr (TypedRound.xEnd ⟨0,hp⟩) b

private theorem candidates_length {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (x : TypedRound.Host (Fin p) (Fin q)) : (candidates hp hq x).length ≤ 5 := by
  rcases x with ⟨k,i⟩|⟨k,j⟩ <;> cases k <;> simp [candidates,sideList]

private theorem candidates_cover {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {x y : TypedRound.Host (Fin p) (Fin q)}
    (h : (TypedRound.host TypedRound.nextIndex TypedRound.nextIndex (@TypedRound.origin p q)).Adj x y) :
    y ∈ candidates hp hq x := by
  rcases h with ht|⟨i,j,hi,hpair⟩
  · rcases x with a|a <;> rcases y with b|b
    · exact listed_track hp Sum.inl _ a b ht
    · exact False.elim (ht.elim id id)
    · exact False.elim (ht.elim id id)
    · exact listed_track hq Sum.inr _ a b ht
  · have hi0 : i = ⟨0,hp⟩ := Fin.ext hi.1
    have hj0 : j = ⟨0,hq⟩ := Fin.ext hi.2
    rcases hpair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      simp [candidates,sideList,TypedRound.xEnd,TypedRound.yEnd,hi0,hj0]

private def pageEmbedding {I : Type*} (code : I → Fin 10) (b : Block I) :
    Fin (pageCount code b) ↪ HostVertex code where
  toFun := Vertex.page b
  inj' := fun _ _ h => Fin.ext (congrArg vindex h)

private def allPages {I : Type*} (code : I → Fin 10) (b : Block I) : Finset (HostVertex code) :=
  Finset.univ.map (pageEmbedding code b)

private noncomputable def marker {I : Type*} (code : I → Fin 10) (i : I) : Finset (HostVertex code) :=
  (clique (blockSize code) (pageCount code) (.primary i) ∪
    clique (blockSize code) (pageCount code) (.secondary i)) ∪
  (allPages code (.primary i) ∪ allPages code (.secondary i))

private theorem in_marker {I : Type*} (code : I → Fin 10) (x : HostVertex code) :
    x ∈ marker code (vertexRole x) := by
  have inPages (b : Block I) (a : Fin (pageCount code b)) : Vertex.page b a ∈ allPages code b :=
    Finset.mem_map.mpr ⟨a,Finset.mem_univ a,rfl⟩
  cases x with
  | core b a =>
    cases b with
    | primary i => exact Finset.mem_union_left _ (Finset.mem_union_left _ (core_mem _ _ _ _))
    | secondary i => exact Finset.mem_union_left _ (Finset.mem_union_right _ (core_mem _ _ _ _))
  | page b a =>
    cases b with
    | primary i => exact Finset.mem_union_right _ (Finset.mem_union_left _ (inPages _ _))
    | secondary i => exact Finset.mem_union_right _ (Finset.mem_union_right _ (inPages _ _))

private theorem marker_card_le {I : Type*} (code : I → Fin 10) (i : I) : (marker code i).card ≤ 13872 := by
  let a := clique (blockSize code) (pageCount code) (.primary i)
  let b := clique (blockSize code) (pageCount code) (.secondary i)
  let c := allPages code (.primary i)
  let d := allPages code (.secondary i)
  have hub := Finset.card_union_le a b
  have leaves := Finset.card_union_le c d
  have total := Finset.card_union_le (a ∪ b) (c ∪ d)
  change ((a ∪ b) ∪ (c ∪ d)).card ≤ 13872
  have ac : a.card = 20+(code i).val := by simp [a,blockSize]
  have bc : b.card = 50-(code i).val := by simp [b,blockSize]
  have cc : c.card = 103*(2*(20+(code i).val)-3) := by simp [c,allPages,pageCount,blockSize]
  have dc : d.card = 103*(2*(50-(code i).val)-3) := by simp [d,allPages,pageCount,blockSize]
  have hi := (code i).isLt
  omega

private theorem external_primary {I : Type*} (F : SimpleGraph I) (code : I → Fin 10)
    {x y : HostVertex code} (hne : vertexRole x ≠ vertexRole y)
    (he : (Localization.host F code).Adj x y) :
    F.Adj (vertexRole x) (vertexRole y) ∧
      y ∈ clique (blockSize code) (pageCount code) (.primary (vertexRole y)) := by
  cases x with
  | page i a =>
    cases y with
    | page j b => exact False.elim he
    | core j b => exact False.elim (hne (congrArg blockRole he))
  | core i a =>
    cases y with
    | page j b => exact False.elim (hne (congrArg blockRole he))
    | core j b =>
      rcases he.2 with hij|adj
      · exact False.elim (hne (congrArg blockRole hij))
      cases i with
      | primary i => cases j with
        | primary j => exact ⟨adj,core_mem _ _ _ _⟩
        | secondary j => exact False.elim (hne adj)
      | secondary i => cases j with
        | primary j => exact False.elim (hne adj)
        | secondary j => exact False.elim adj

theorem initial_degree_le {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (v : OrdinaryVertex (Fin p) (Fin q)) : (initial p q).degree v ≤ 14016 := by
  let f := TypedRound.host TypedRound.nextIndex TypedRound.nextIndex (@TypedRound.origin p q)
  let base := marker hostCode (vertexRole v)
  let S := (candidates hp hq (vertexRole v)).toFinset
  let U := fun j : TypedRound.Host (Fin p) (Fin q) => clique (blockSize hostCode) (pageCount hostCode) (.primary j)
  have inc : (initial p q).neighborFinset v ⊆ base.erase v ∪ S.biUnion U := by
    intro y hy
    have e := ((initial p q).mem_neighborFinset v y).mp hy
    by_cases h : vertexRole v = vertexRole y
    · apply Finset.mem_union_left
      exact Finset.mem_erase.mpr ⟨e.ne.symm,by simpa [base,h] using in_marker hostCode y⟩
    · obtain ⟨he,hm⟩ := external_primary f hostCode h e
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨vertexRole y,List.mem_toFinset.mpr (candidates_cover hp hq he),hm⟩)
  have ub (j : TypedRound.Host (Fin p) (Fin q)) : (U j).card ≤ 29 := by
    rw [show (U j).card = 20+(hostCode j).val by simp [U,blockSize]]
    have := (hostCode j).isLt
    omega
  have hS : S.card ≤ 5 := (List.toFinset_card_le _).trans (candidates_length hp hq _)
  have sumCap (T : Finset (TypedRound.Host (Fin p) (Fin q))) :
      (∑ j ∈ T, (U j).card) ≤ T.card * 29 := by
    induction T using Finset.induction_on with
    | empty => simp
    | insert j T hj ih =>
      rw [Finset.sum_insert hj,Finset.card_insert_of_not_mem hj,Nat.add_mul]
      have h := ub j
      omega
  have hU : (S.biUnion U).card ≤ S.card * 29 := Finset.card_biUnion_le.trans (sumCap S)
  have he := Finset.card_erase_of_mem (show v ∈ base from in_marker hostCode v)
  have hm := marker_card_le hostCode (vertexRole v)
  change base.card ≤ 13872 at hm
  have pair := Finset.card_union_le (base.erase v) (S.biUnion U)
  have deg := Finset.card_le_card inc
  change ((initial p q).neighborFinset v).card ≤ 14016
  omega

theorem initial_maxDegree_le {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (initial p q).maxDegree ≤ 14016 :=
  (initial p q).maxDegree_le_of_forall_degree_le _ (initial_degree_le hp hq)

/-- First stabilization in the ordinary graph process, with the finite host instance. -/
theorem initial_stabilizationTime {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) :
    Bootstrap.stabilizationTime ordinaryRule (initial p q) = p.lcm q / 2 :=
  Bootstrap.stabilizationTime_eq_of_first ordinaryRule (initial p q) _ (ordinary_fixed_iff hp hq)

end Bootstrap.MarkedSimulation

#print axioms Bootstrap.MarkedSimulation.initial_stabilizationTime
#print axioms Bootstrap.MarkedSimulation.initial_degree_le
#print axioms Bootstrap.MarkedSimulation.initial_maxDegree_le
