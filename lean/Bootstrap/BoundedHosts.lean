import Bootstrap.QuadraticRule
import Bootstrap.InitialProperties

/-! The degree-restricted maximum in the final sentence of Theorem III.1. -/
namespace Bootstrap

open MarkedSimulation RuleStructure

open scoped Classical in
def BoundedDegree {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : Prop := G.maxDegree ≤ d

theorem boundedDegree_pad {V Z : Type*} [Fintype V] [Fintype Z] (G : SimpleGraph V) {d : ℕ}
    (hG : BoundedDegree G d) : BoundedDegree (padIsolates G Z) d := by
  classical
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  intro v
  cases v with
  | inl x =>
    let f : V ↪ V ⊕ Z := ⟨Sum.inl,fun _ _ he => Sum.inl.inj he⟩
    have eq : (padIsolates G Z).neighborFinset (.inl x) = (G.neighborFinset x).map f := by
      ext w
      rw [Finset.mem_map, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨i,j,hi,hj,hij⟩
        have ei := Sum.inl.inj hi
        exact ⟨j, (SimpleGraph.mem_neighborFinset G _ _).mpr (ei ▸ hij), hj⟩
      · rintro ⟨j,hj,rfl⟩
        exact ⟨x,j,rfl,rfl,(SimpleGraph.mem_neighborFinset G _ _).mp hj⟩
    calc
      (padIsolates G Z).degree (.inl x) = G.degree x := by
        rw [←SimpleGraph.card_neighborFinset_eq_degree,eq,Finset.card_map,SimpleGraph.card_neighborFinset_eq_degree]
      _ ≤ d := (G.degree_le_maxDegree x).trans hG
  | inr z =>
    have empty : (padIsolates G Z).neighborFinset (.inr z) = ∅ := by
      apply Finset.eq_empty_of_forall_not_mem
      intro w hw
      obtain ⟨_,_,eq,_,_⟩ := (SimpleGraph.mem_neighborFinset _ _ _).mp hw
      cases eq
    rw [← SimpleGraph.card_neighborFinset_eq_degree,empty,Finset.card_empty]
    exact Nat.zero_le _

theorem boundedDegree_relabel {V U : Type*} [Fintype V] [Fintype U] (G : SimpleGraph V)
    (e : U ≃ V) {d : ℕ} (h : BoundedDegree G d) : BoundedDegree (G.comap e) d := by
  classical
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  intro x
  let iso := SimpleGraph.Iso.comap e G
  have eq := Fintype.card_congr (iso.mapNeighborSet x)
  calc
    (G.comap e).degree x = G.degree (e x) := by
      simpa only [SimpleGraph.card_neighborSet_eq_degree] using eq
    _ ≤ d := (G.degree_le_maxDegree _).trans h

/-- Largest ordinary running time among labelled hosts of maximum degree at most d. -/
noncomputable def boundedMaxTime {W : Type*} (H : SimpleGraph W) (d n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun G : SimpleGraph (Fin n) => BoundedDegree G d)).sup
    (fun G => stabilizationTime H G)

theorem time_le_boundedMax {W : Type*} (H : SimpleGraph W) {d n : ℕ}
    (G : SimpleGraph (Fin n)) (hg : BoundedDegree G d) :
    stabilizationTime H G ≤ boundedMaxTime H d n := by
  classical
  exact Finset.le_sup (s := Finset.univ.filter (fun F : SimpleGraph (Fin n) => BoundedDegree F d))
    (f := fun F => stabilizationTime H F) (Finset.mem_filter.mpr ⟨Finset.mem_univ G,hg⟩)

theorem boundedMax_le_max {W : Type*} (H : SimpleGraph W) (d n : ℕ) :
    boundedMaxTime H d n ≤ maxTime H n := by
  classical
  apply Finset.sup_le
  exact fun G _ => le_maxTime H G

theorem bounded_all_orders (n : ℕ) (hn : 624240 ≤ n) :
    ∃ G : SimpleGraph (Fin n), BoundedDegree G 14016 ∧
      n*n ≤ ((277440*277440)*2) * stabilizationTime ordinaryRule G := by
  classical
  let k := (n/69360 - 1)/2
  have hk : 3 ≤ k := by dsimp [k]; omega
  have length : familyOrder k ≤ n := by dsimp [familyOrder,k]; omega
  have hsize : n ≤ 277440*k := by dsimp [k]; omega
  let V := OrdinaryVertex (Fin k) (Fin (k+1))
  let G := initial k (k+1)
  have c : Fintype.card V = familyOrder k := by rw [host_order]; unfold familyOrder; omega
  let Z := Fin (n-familyOrder k)
  let P := padIsolates G Z
  have length' : Fintype.card (V ⊕ Z) = n := by
    rw [Fintype.card_sum,c,Fintype.card_fin,Nat.add_sub_of_le length]
  let e := (Fintype.equivFinOfCardEq length').symm
  let F : SimpleGraph (Fin n) := P.comap e
  refine ⟨F,boundedDegree_relabel P e (boundedDegree_pad G (initial_maxDegree_le (by omega) (by omega))),?_⟩
  have htime : stabilizationTime ordinaryRule F = familyTime k := by
    have rel := stabilizationTime_relabel ordinaryRule F P e (fun _ _ => Iff.rfl)
    rw [rel,stabilizationTime_pad ordinaryRule (hasTwoNeighbours_of_minDegree ordinaryRule source_minDegree.ge),
      ordinary_time hk (by omega),consecutive_period]
  rw [htime]
  have hp : k*k + k = k*(k+1) := by simp [Nat.mul_add]
  have ht : k*k ≤ 2 * familyTime k := by unfold familyTime; omega
  calc
    n*n ≤ (277440*k)*(277440*k) := Nat.mul_le_mul hsize hsize
    _ = (277440*277440)*(k*k) := by ac_rfl
    _ ≤ (277440*277440)*(2*familyTime k) := Nat.mul_le_mul_left _ ht
    _ = _ := by ac_rfl

theorem bounded_quadratic :
    (∀ n ≥ 624240, n*n ≤ ((277440*277440)*2) * boundedMaxTime ordinaryRule 14016 n) ∧
    (∀ n, boundedMaxTime ordinaryRule 14016 n ≤ n*n) := by
  refine ⟨?_,fun n => (boundedMax_le_max _ _ n).trans (maxTime_le_square _ n)⟩
  intro n hn
  obtain ⟨G,d,t⟩ := bounded_all_orders n hn
  exact t.trans (Nat.mul_le_mul_left _ (time_le_boundedMax ordinaryRule G d))

end Bootstrap

#print axioms Bootstrap.bounded_all_orders
#print axioms Bootstrap.bounded_quadratic
