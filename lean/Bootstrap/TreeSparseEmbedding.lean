import Bootstrap.TreeExtremalClock
import Bootstrap.Asymptotics
import Mathlib.Tactic.Ring

namespace Bootstrap.TreeLinear

open scoped Classical
variable {W V : Type*}

/-- A finite one-degenerate rule embeds in a nonempty set in which every
vertex has at least as many neighbours as there are rule vertices. -/
theorem embed_in_dense_set [Fintype W] (H : SimpleGraph W) (D : SimpleGraph V)
    (peel : ∀ P : Finset W, P.Nonempty → ∃ x∈P, ∀ y∈P, ∀ z∈P,H.Adj x y → H.Adj x z → y=z)
    (S : Finset V) (live : S.Nonempty)
    (minimum : ∀ v∈S, Fintype.card W≤(S.filter (D.Adj v)).card) : Contains H D := by
  classical
  have embedPart (P : Finset W) : ∃ f : W → V,
      (∀ u∈P,f u∈S) ∧ (∀u∈P,∀v∈P,f u=f v → u=v) ∧
      (∀u∈P,∀v∈P,H.Adj u v → D.Adj (f u) (f v)) := by
    induction P using Finset.strongInductionOn with
    | _ P ih =>
      by_cases empty : P=∅
      · obtain ⟨v,_⟩ := live
        exact ⟨fun _ => v,by simp [empty]⟩
      obtain ⟨x,hx,uniqueN⟩ := peel P (Finset.nonempty_iff_ne_empty.mpr empty)
      let Q := P.erase x
      have smaller : Q ⊂ P := Finset.erase_ssubset hx
      obtain ⟨f,inS,inj,edges⟩ := ih Q smaller
      have spare (p : V) (hp : p∈S) : ∃ v∈S,D.Adj p v ∧ v∉Q.image f := by
        have bounds : (Q.image f).card<Fintype.card W :=
          (Finset.card_image_le.trans_lt (Finset.card_lt_card smaller)).trans_le (Finset.card_le_univ _)
        have large := minimum p hp
        by_contra! no
        have sub : S.filter (D.Adj p) ⊆ Q.image f := by
          intro v hv
          obtain ⟨sv,edge⟩ := Finset.mem_filter.mp hv
          exact no v sv edge
        have := Finset.card_le_card sub
        omega
      have chooseNew : ∃ v∈S,v∉Q.image f ∧ ∀ y∈Q,H.Adj x y → D.Adj v (f y) := by
        by_cases yes : ∃ y∈Q,H.Adj x y
        · obtain ⟨t,ht,xt⟩ := yes
          obtain ⟨v,hv,e,unused⟩ := spare (f t) (inS t ht)
          refine ⟨v,hv,unused,fun y hy xy => ?_⟩
          have eq := uniqueN _ (Finset.mem_of_mem_erase hy) _ (Finset.mem_of_mem_erase ht) xy xt
          rw [eq];exact D.symm e
        · obtain ⟨p,hp⟩ := live
          obtain ⟨v,hv,_,unused⟩ := spare p hp
          exact ⟨v,hv,unused,fun y hy xy => (yes ⟨y,hy,xy⟩).elim⟩
      obtain ⟨v,hv,unused,matchN⟩ := chooseNew
      let g (y : W) := if y=x then v else f y
      have atX : g x=v := if_pos rfl
      have kept {u : W} (hu : u≠x) : g u=f u := if_neg hu
      have mem {u : W} (hu : u∈P) (ne : u≠x) : u∈Q := Finset.mem_erase.mpr ⟨ne,hu⟩
      refine ⟨g,?_,?_,?_⟩
      · intro u hu
        by_cases ux : u=x
        · rwa [ux,atX]
        · rw [kept ux];exact inS _ (mem hu ux)
      · intro u hu w hw eq
        by_cases ux : u=x <;> by_cases wx : w=x
        · exact ux.trans wx.symm
        · rw [ux,atX,kept wx] at eq
          exact (unused (Finset.mem_image.mpr ⟨w,mem hw wx,eq.symm⟩)).elim
        · rw [wx,atX,kept ux] at eq
          exact (unused (Finset.mem_image.mpr ⟨u,mem hu ux,eq⟩)).elim
        · rw [kept ux,kept wx] at eq
          exact inj _ (mem hu ux) _ (mem hw wx) eq
      · intro u hu w hw e
        by_cases ux : u=x <;> by_cases wx : w=x
        · exact (e.ne (ux.trans wx.symm)).elim
        · rw [ux,atX,kept wx]
          exact matchN w (mem hw wx) (ux ▸ e)
        · rw [wx,atX,kept ux]
          exact D.symm (matchN u (mem hu ux) (wx ▸ H.symm e))
        · rw [kept ux,kept wx]
          exact edges _ (mem hu ux) _ (mem hw wx) e
  obtain ⟨f,_,inj,edges⟩ := embedPart Finset.univ
  exact ⟨⟨f,fun u v eq => inj u (Finset.mem_univ _) v (Finset.mem_univ _) eq⟩,
    fun u v h => edges u (Finset.mem_univ _) v (Finset.mem_univ _) h⟩

private theorem arcs_erase (D : SimpleGraph V) (S : Finset V) (v : V) :
    (arcs D S).card ≤ (arcs D (S.erase v)).card+2*(S.filter (D.Adj v)).card := by
  classical
  let N := S.filter (D.Adj v)
  let a : Finset (V×V) := ({v} : Finset V).product N
  let b : Finset (V×V) := N.product {v}
  have cover : arcs D S ⊆ arcs D (S.erase v) ∪ a ∪ b := by
    rintro ⟨u,w⟩ hu
    obtain ⟨us,ws,e⟩ := (mem_arcs ..).mp hu
    by_cases uv : u=v
    · subst u
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_product.mpr ⟨Finset.mem_singleton_self _,Finset.mem_filter.mpr ⟨ws,e⟩⟩))
    by_cases wv : w=v
    · subst w
      exact Finset.mem_union_right _ (Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨us,D.symm e⟩,Finset.mem_singleton_self _⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((mem_arcs ..).mpr
        ⟨Finset.mem_erase.mpr ⟨uv,us⟩,Finset.mem_erase.mpr ⟨wv,ws⟩,e⟩))
  have ca : a.card=N.card := by simp [a]
  have cb : b.card=N.card := by simp [b]
  have u := Finset.card_union_le (arcs D (S.erase v)) a
  have t := Finset.card_union_le (arcs D (S.erase v) ∪ a) b
  have h := Finset.card_le_card cover
  change _≤_+2*N.card
  omega

theorem sparse_free_arcs [Fintype W] (H : SimpleGraph W) (D : SimpleGraph V)
    (peel : ∀ P : Finset W, P.Nonempty → ∃ x∈P, ∀ y∈P, ∀ z∈P,H.Adj x y → H.Adj x z → y=z)
    (free : ¬Contains H D) (S : Finset V) : (arcs D S).card ≤ (2*Fintype.card W)*S.card := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases empty : S=∅
    · simp [empty,arcs]
    have live := Finset.nonempty_iff_ne_empty.mpr empty
    have low : ∃v∈S,(S.filter (D.Adj v)).card < Fintype.card W := by
      by_contra! no
      exact free (embed_in_dense_set H D peel S live no)
    obtain ⟨v,hv,deg⟩ := low
    have first := arcs_erase D S v
    have smaller := ih (S.erase v) (Finset.erase_ssubset hv)
    have cs : (S.erase v).card+1=S.card := Finset.card_erase_add_one hv
    have sums := congrArg (fun k : ℕ => (2*Fintype.card W)*k) cs
    simp only [Nat.mul_add,Nat.mul_one] at sums
    omega

theorem linear_of_degenerate [Fintype W] (H : SimpleGraph W)
    (peel : ∀ P : Finset W, P.Nonempty → ∃ x∈P, ∀ y∈P, ∀ z∈P,H.Adj x y → H.Adj x z → y=z) :
    HasLinearUpper H := by
  refine ⟨4*Fintype.card W+1,1,fun n hn => (maxTime_le_iff ..).mpr fun G => ?_⟩
  have time := time_of_free_budget H G ((2*Fintype.card W)*n) (fun D free => by
    simpa using sparse_free_arcs H D peel free Finset.univ)
  calc
    _ ≤ 2*(2*Fintype.card W*n)+1 := time
    _ ≤ (4*Fintype.card W+1)*n := by
      have eq : 2*(2*Fintype.card W*n)=(4*Fintype.card W)*n := by ring
      rw [eq,Nat.add_mul,Nat.one_mul];omega

end Bootstrap.TreeLinear

#print axioms Bootstrap.TreeLinear.embed_in_dense_set
#print axioms Bootstrap.TreeLinear.sparse_free_arcs
#print axioms Bootstrap.TreeLinear.linear_of_degenerate
