import Bootstrap.ThetaRules
import Bootstrap.TreeConstruction
import Bootstrap.TreeSemantics
import Mathlib.Data.Fin.Tuple.Reflection

namespace Bootstrap.Theta

open TreeBags

variable {k : ℕ}

private abbrev Bags (m : Fin k → ℕ) := Finset (Finset (Vertex m))
private def poles (m : Fin k → ℕ) : Finset (Vertex m) := {pole m false,pole m true}
private def earlier (m : Fin k → ℕ) (i : Fin k) (j : Fin (m i + 1)) : Vertex m :=
  if h : j.val = 0 then pole m false else inner m i ⟨j.val-1,by omega⟩
private def armBag (m : Fin k → ℕ) (i : Fin k) (j : Fin (m i + 1)) : Finset (Vertex m) :=
  {inner m i j,earlier m i j,pole m true}

private def rank (m : Fin k → ℕ) : Vertex m → ℕ
  | .inl _ => 0
  | .inr ⟨_,j⟩ => j.val+1

/-- Process all arms simultaneously from their left poles, using one width-two bag per internal vertex. -/
private theorem stages (m : Fin k → ℕ) (t : ℕ) :
    ∃ F : Bags m, Tree 2 F ∧ poles m ∈ F ∧
      (∀ i j, j.val < t → armBag m i j ∈ F) ∧ ∀ v, Occurs F v → rank m v ≤ t := by
  classical
  induction t with
  | zero =>
    refine ⟨{poles m},Tree.root _ (Finset.card_le_two.trans (by decide)),Finset.mem_singleton_self _,?_,?_⟩
    · exact fun _ _ h => (Nat.not_lt_zero _ h).elim
    · rintro v ⟨b,hb,hv⟩
      obtain rfl := Finset.mem_singleton.mp hb
      rcases Finset.mem_insert.mp hv with rfl | h
      · exact Nat.le_refl _
      · obtain rfl := Finset.mem_singleton.mp h
        exact Nat.le_refl _
  | succ t ih =>
    obtain ⟨F,tree,root,bag,seen⟩ := ih
    let I := {i : Fin k // t ≤ m i}
    let pos := fun a : I => (⟨t,by have := a.property; omega⟩ : Fin (m a.val + 1))
    let tip : I ↪ Vertex m := ⟨fun a => inner m a.val (pos a),by
      intro a b h
      exact Subtype.ext (congrArg Sigma.fst (Sum.inr.inj h))⟩
    let old := fun a : I => earlier m a.val (pos a)
    have fresh (a : I) : ¬Occurs F (tip a) := by
      intro h
      have ht := seen _ h
      exact Nat.not_succ_le_self t ht
    have parents (a : I) : Together F (old a) (pole m true) := by
      by_cases ht : t = 0
      · have e : old a = pole m false := dif_pos ht
        exact ⟨poles m,root,e ▸ Finset.mem_insert_self _ _,Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
      · let j : Fin (m a.val + 1) := ⟨t-1,by have := a.property; omega⟩
        have e : old a = inner m a.val j := dif_neg ht
        refine ⟨armBag m a.val j,bag _ _ (by dsimp [j];omega),e ▸ Finset.mem_insert_self _ _,?_⟩
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    obtain ⟨F',tree',sub,add,only⟩ := starLeaves tree tip old (fun _ => pole m true) fresh parents
    refine ⟨F',tree',sub root,?_,?_⟩
    · intro i j hj
      by_cases oldrank : j.val < t
      · exact sub (bag i j oldrank)
      · have eq : j.val = t := by omega
        let a : I := ⟨i,by have := j.isLt; omega⟩
        have e : j = pos a := Fin.ext eq
        rw [e]; exact add a
    · intro v hv
      rcases only v hv with hold | ⟨a,rfl⟩
      · exact Nat.le_succ_of_le (seen _ hold)
      · exact Nat.le_refl _

theorem parent_width_two (m : Fin k → ℕ) : TreeBags.WidthLE (graph m) 2 := by
  classical
  let t := Finset.univ.sup (fun i => m i + 1)
  obtain ⟨F,T,root,bag,_⟩ := stages m t
  have present (i : Fin k) (j : Fin (m i + 1)) : armBag m i j ∈ F :=
    bag _ _ (j.isLt.trans_le (Finset.le_sup (f := fun i => m i + 1) (Finset.mem_univ i)))
  have ab (i : Fin k) (j : Fin (m i + 1)) : Together F (inner m i j) (earlier m i j) :=
    ⟨_,present i j,Finset.mem_insert_self _ _,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
  have right (i : Fin k) (j : Fin (m i + 1)) : Together F (inner m i j) (pole m true) :=
    ⟨_,present i j,Finset.mem_insert_self _ _,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
  have poleInner (b : Bool) (i : Fin k) (j : Fin (m i + 1)) (h : (graph m).Adj (pole m b) (inner m i j)) :
      Together F (inner m i j) (pole m b) := by
    cases b
    · change j.val = 0 at h
      simpa only [earlier,dif_pos h] using ab i j
    · exact right i j
  have next (i : Fin k) (j l : Fin (m i + 1)) (h : j.val + 1 = l.val) :
      Together F (inner m i l) (inner m i j) := by
    have nz : l.val ≠ 0 := by omega
    have eq : earlier m i l = inner m i j := by
      unfold earlier
      rw [dif_neg nz]
      exact congrArg (inner m i) (Fin.ext (by dsimp;omega))
    simpa only [eq] using ab i l
  refine ⟨F,T,?_,?_⟩
  · rintro (b | ⟨i,j⟩)
    · cases b
      · exact ⟨_,root,Finset.mem_insert_self _ _⟩
      · exact ⟨_,root,Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
    · exact ⟨_,present i j,Finset.mem_insert_self _ _⟩
  · rintro (b | ⟨i,j⟩) (c | ⟨s,l⟩) h
    · exact False.elim h
    · exact together_symm (poleInner b s l h)
    · exact poleInner c i j ((graph m).symm h)
    · obtain ⟨rfl,h | h⟩ := h
      · exact together_symm (next i j l h)
      · exact next i l j h

theorem standard_width_two (m : Fin k → ℕ) : TreeSemantics.WidthLE (graph m) 2 :=
  TreeSemantics.of_parent_bags (parent_width_two m)

theorem theta_order (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    Fintype.card (Vertex (fun i => threeLengths a b c i - 2)) = a+b+c-1 := by
  simp only [Vertex,Fintype.card_sum,Fintype.card_bool,Fintype.card_sigma,Fintype.card_fin]
  rw [Fin.sum_univ_three]
  simp [threeLengths]
  omega

end Bootstrap.Theta

#print axioms Bootstrap.Theta.parent_width_two
#print axioms Bootstrap.Theta.theta_order
