import Bootstrap.ThetaRules
import Bootstrap.Suppression

namespace Bootstrap.Theta

variable {k : Nat}

private abbrev deleted (m : Fin k → Nat) (z : Vertex m) := (graph m).induce {u | u ≠ z}

private theorem left_part (m : Fin k → Nat) {z : Vertex m} (hl : pole m false ≠ z)
    (i : Fin k) (j : Fin (m i + 1)) (h : ∀ t, t ≤ j → inner m i t ≠ z) :
    (deleted m z).Reachable ⟨pole m false,hl⟩ ⟨inner m i j,h j le_rfl⟩ := by
  induction j using Fin.induction with
  | zero =>
    apply SimpleGraph.Adj.reachable
    change (0 : Fin (m i + 1)).val = 0
    rfl
  | succ j ih =>
    have earlier := ih (fun t ht => h t (ht.trans j.castSucc_le_succ))
    apply earlier.trans
    apply SimpleGraph.Adj.reachable
    change (graph m).Adj (inner m i j.castSucc) (inner m i j.succ)
    exact ⟨rfl,Or.inl rfl⟩

private theorem right_part (m : Fin k → Nat) {z : Vertex m} (hr : pole m true ≠ z)
    (i : Fin k) (j : Fin (m i + 1)) (h : ∀ t, j ≤ t → inner m i t ≠ z) :
    (deleted m z).Reachable ⟨inner m i j,h j le_rfl⟩ ⟨pole m true,hr⟩ := by
  induction j using Fin.reverseInduction with
  | last =>
    apply SimpleGraph.Adj.reachable
    change (Fin.last (m i)).val = m i
    rfl
  | cast j ih =>
    have later := ih (fun t ht => h t (j.castSucc_le_succ.trans ht))
    apply SimpleGraph.Reachable.trans _ later
    apply SimpleGraph.Adj.reachable
    change (graph m).Adj (inner m i j.castSucc) (inner m i j.succ)
    exact ⟨rfl,Or.inl rfl⟩

private theorem different_arm (m : Fin k → Nat) {i s : Fin k} (h : i ≠ s)
    (j : Fin (m i + 1)) (t : Fin (m s + 1)) : inner m i j ≠ inner m s t :=
  fun e => h (congrArg Sigma.fst (Sum.inr.inj e))

private theorem different_index (m : Fin k → Nat) (i : Fin k) {j t : Fin (m i + 1)}
    (h : j ≠ t) : inner m i j ≠ inner m i t := by
  intro e
  apply h
  apply Fin.ext
  exact congrArg (fun v : Vertex m => Sum.elim (fun _ => 0) (fun p => p.2.val) v) e

/-- Removing a pole leaves all arms attached to the other pole. Removing an internal
vertex only breaks one arm, and another whole arm still joins the poles. -/
theorem deleted_connected (m : Fin k → Nat) (hk : 2 ≤ k) (z : Vertex m) :
    ((graph m).induce {u | u ≠ z}).Connected := by
  rcases z with b | ⟨s,t⟩
  · cases b
    · have hr : pole m true ≠ pole m false := by simp [pole]
      apply ((deleted m (pole m false)).connected_iff_exists_forall_reachable).mpr
      refine ⟨⟨pole m true,hr⟩,?_⟩
      rintro ⟨b | ⟨i,j⟩,h⟩
      · cases b
        · exact (h rfl).elim
        · exact .refl _
      · exact (right_part m hr i j (fun _ _ => by simp [inner,pole])).symm
    · have hl : pole m false ≠ pole m true := by simp [pole]
      apply ((deleted m (pole m true)).connected_iff_exists_forall_reachable).mpr
      refine ⟨⟨pole m false,hl⟩,?_⟩
      rintro ⟨b | ⟨i,j⟩,h⟩
      · cases b
        · exact .refl _
        · exact (h rfl).elim
      · exact left_part m hl i j (fun _ _ => by simp [inner,pole])
  · have hl : pole m false ≠ inner m s t := by simp [pole,inner]
    have hr : pole m true ≠ inner m s t := by simp [pole,inner]
    obtain ⟨i,hi⟩ : ∃ i : Fin k, i ≠ s := by
      let i₀ : Fin k := ⟨0,by omega⟩
      let i₁ : Fin k := ⟨1,by omega⟩
      by_cases e : i₀ = s
      · refine ⟨i₁,fun e' => ?_⟩
        have bad : (1 : Nat) = 0 := congrArg Fin.val (e'.trans e.symm)
        omega
      · exact ⟨i₀,e⟩
    have poles : (deleted m (inner m s t)).Reachable ⟨pole m false,hl⟩ ⟨pole m true,hr⟩ :=
      (left_part m hl i 0 (fun q _ => different_arm m hi q t)).trans
      (right_part m hr i 0 (fun q _ => different_arm m hi q t))
    apply ((deleted m (inner m s t)).connected_iff_exists_forall_reachable).mpr
    refine ⟨⟨pole m false,hl⟩,?_⟩
    rintro ⟨b | ⟨j,u⟩,h⟩
    · cases b
      · exact .refl _
      · exact poles
    · by_cases e : j = s
      · subst j
        have ne : u ≠ t := fun eq => h (congrArg (inner m s) eq)
        rcases lt_or_gt_of_ne ne with lt | gt
        · exact left_part m hl s u (fun q hq => different_index m s (ne_of_lt (hq.trans_lt lt)))
        · exact poles.trans (right_part m hr s u
            (fun q hq => different_index m s (ne_of_gt (gt.trans_le hq)))).symm
      · exact left_part m hl j u (fun q _ => different_arm m e q t)

theorem twoConnected (m : Fin k → Nat) (hk : 2 ≤ k) : Suppression.TwoConnected (graph m) := by
  classical
  let i : Fin k := ⟨0,by omega⟩
  have bound := Finset.card_le_univ ({pole m false,pole m true,inner m i 0} : Finset (Vertex m))
  have three : ({pole m false,pole m true,inner m i 0} : Finset (Vertex m)).card = 3 := by
    simp [pole,inner]
  exact ⟨three ▸ bound,connected _ (by omega),deleted_connected _ hk⟩

end Bootstrap.Theta

#print axioms Bootstrap.Theta.deleted_connected
#print axioms Bootstrap.Theta.twoConnected
