import Bootstrap.DegreeTwoTransfer
import Bootstrap.OrdinaryTime

namespace Bootstrap.TreeLinear

open scoped Classical
variable {W V : Type*}

/-- An injective non-induced copy. -/
def Contains (H : SimpleGraph W) (D : SimpleGraph V) : Prop :=
  ∃ f : W ↪ V,∀ x y,H.Adj x y → D.Adj (f x) (f y)

/-- Ordered adjacent pairs with both vertices in the given finite set. -/
noncomputable def arcs (D : SimpleGraph V) (S : Finset V) : Finset (V×V) :=
  (S.product S).filter (fun e => D.Adj e.1 e.2)

@[simp] theorem mem_arcs (D : SimpleGraph V) (S : Finset V) (x y : V) :
    (x,y)∈arcs D S ↔ x∈S ∧ y∈S ∧ D.Adj x y := by
  simp [arcs,and_assoc]

private def endpoints (x y a b : V) := (x=a ∧ y=b) ∨ (x=b ∧ y=a)

private def choices {k : ℕ} (a b : Fin k → V) (ne : ∀i,a i≠b i) : SimpleGraph V where
  Adj x y := ∃ i,endpoints x y (a i) (b i)
  symm := by rintro x y ⟨i,h⟩;exact ⟨i,by unfold endpoints at *;tauto⟩
  loopless := by rintro x ⟨i,⟨e,f⟩|⟨f,e⟩⟩ <;> exact ne i (e.symm.trans f)

private theorem choice_free [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (hasEdge : ∃u v,H.Adj u v) {k : ℕ} (a b : Fin k → V) (ne : ∀i,a i≠b i)
    (old : ∀i,¬(run H G (2*i.val+1)).Adj (a i) (b i))
    (born : ∀i,(run H G (2*i.val+2)).Adj (a i) (b i)) :
    ¬ Contains H (choices a b ne) := by
  classical
  rintro ⟨f,copy⟩
  let S := Finset.univ.filter (fun i : Fin k => ∃x y,H.Adj x y ∧ f x=a i ∧ f y=b i)
  have assigned (x y : W) (e : H.Adj x y) :
      ∃i∈S,endpoints (f x) (f y) (a i) (b i) := by
    obtain ⟨i,h⟩ := copy x y e
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,h⟩
    rcases h with ⟨u,v⟩|⟨u,v⟩
    · exact ⟨x,y,e,u,v⟩
    · exact ⟨y,x,H.symm e,v,u⟩
  obtain ⟨x₀,y₀,e₀⟩ := hasEdge
  obtain ⟨i₀,h₀,_⟩ := assigned x₀ y₀ e₀
  obtain ⟨j,hj,maximal⟩ := S.exists_max_image Fin.val ⟨i₀,h₀⟩
  obtain ⟨u,v,uv,hx,hy⟩ := (Finset.mem_filter.mp hj).2
  apply old j
  apply Or.inr
  refine ⟨u,v,f,uv,hx,hy,?_⟩
  intro x y e diff
  obtain ⟨i,hi,id⟩ := assigned x y e
  have lt : i.val<j.val := by
    have le := maximal i hi
    by_contra bad
    have eq : i=j := Fin.ext (by omega)
    subst i
    apply diff
    rcases id with ⟨a',b'⟩|⟨a',b'⟩
    · exact Or.inl ⟨f.injective (a'.trans hx.symm),f.injective (b'.trans hy.symm)⟩
    · exact Or.inr ⟨f.injective (a'.trans hy.symm),f.injective (b'.trans hx.symm)⟩
  have atJ := DegreeTwo.time_mono H G (show 2*i.val+2≤2*j.val by omega) (born i)
  rcases id with ⟨r,s⟩|⟨r,s⟩
  · rwa [r,s]
  · rw [r,s];exact (run H G _).symm atJ

/-- Choosing one genuine new edge from every positive even birth round
makes a rule-free graph. Any extremal bound on its directed edges therefore
bounds the stabilization time, even for a rule with only one edge. -/
theorem time_of_free_budget [Fintype W] [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (B : ℕ)
    (budget : ∀ D : SimpleGraph V, ¬Contains H D → (arcs D Finset.univ).card≤B) :
    stabilizationTime H G≤2*B+1 := by
  classical
  by_contra! long
  let k := B+1
  have fresh (i : Fin k) : ∃x y, ¬(run H G (2*i.val+1)).Adj x y ∧
      (run H G (2*i.val+2)).Adj x y := by
    by_contra! no
    have fixed : run H G (2*i.val+1)=run H G (2*i.val+1+1) := by
      apply le_antisymm (run_le_succ H G _)
      intro x y born
      by_contra old
      exact no x y old born
    have tooSoon := Nat.find_min' (stable_exists H G) fixed
    change stabilizationTime H G≤2*i.val+1 at tooSoon
    have lim := i.isLt
    dsimp [k] at lim
    omega
  choose a b old born using fresh
  have ne (i : Fin k) := (born i).ne
  let D := choices a b ne
  let z : Fin k := ⟨0,by dsimp [k];omega⟩
  have hasEdge : ∃u v,H.Adj u v := by
    rcases born z with h|⟨u,v,_,h,_,_,_⟩
    · exact (old z h).elim
    · exact ⟨u,v,h⟩
  have bound := budget D (choice_free H G hasEdge a b ne old born)
  let f (i : Fin k) : {e // e∈arcs D Finset.univ} :=
    ⟨(a i,b i),(mem_arcs ..).mpr ⟨Finset.mem_univ _,Finset.mem_univ _,⟨i,Or.inl ⟨rfl,rfl⟩⟩⟩⟩
  have impossible {i j : Fin k} (lt : i.val<j.val) (eq : f i=f j) : False := by
    have h := DegreeTwo.time_mono H G (show 2*i.val+2≤2*j.val+1 by omega) (born i)
    have e : (a i,b i)=(a j,b j) := congrArg Subtype.val eq
    rw [Prod.mk.inj e |>.1,Prod.mk.inj e |>.2] at h
    exact old j h
  have inj : Function.Injective f := by
    intro i j eq
    rcases lt_trichotomy i.val j.val with h|h|h
    · exact (impossible h eq).elim
    · exact Fin.ext h
    · exact (impossible h eq.symm).elim
  have count := Fintype.card_le_of_injective _ inj
  rw [Fintype.card_fin,Fintype.card_coe] at count
  dsimp [k] at count
  omega

end Bootstrap.TreeLinear

#print axioms Bootstrap.TreeLinear.time_of_free_budget
