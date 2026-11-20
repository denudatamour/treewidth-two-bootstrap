import Bootstrap.ThetaVertexOrbits
import Bootstrap.ThetaCoordinateModulo
import Bootstrap.ThetaSelfBipartite

namespace Bootstrap.Theta

open scoped Classical

def naturalDepth (m : Fin 3 → ℕ) (a : Fin 3) : Vertex m → ℕ
  | .inl false => 0
  | .inl true => armSize m a
  | .inr ⟨_,d⟩ => d.val+1

def labelPerms {V A : Type*} (f : V→A) : Subgroup (Equiv.Perm V) where
  carrier := {p | ∀v,f (p v)=f v}
  one_mem' := fun _ => rfl
  mul_mem' := fun hp hq v => (hp _).trans (hq v)
  inv_mem' := by intro p hp v;simpa only [Equiv.Perm.apply_inv_self] using (hp (p⁻¹ v)).symm

theorem true_reflect_int (m : Fin 3 → ℕ) {i j : Fin 3} (ij : i≠j) (z : ℤ) :
    reflection m ij true (intPt m i j z)=intPt m i j (-z+2*(armSize m i:ℤ)) := by
  have e := rotate_int m ij (-z)
  rwa [Equiv.Perm.mul_apply,false_reflect_int,neg_neg] at e

private theorem label_intPt {A : Type*} (f : ℤ→A) (m : Fin 3 → ℕ) (a : Fin 3)
    (ng : ∀ z,f (-z)=f z) (ends : ∀i,f (armSize m i)=f (armSize m a))
    (per : ∀ i j, i≠j → ∀ x y : ℤ,(perimeter m i j:ℤ) ∣ x-y → f x=f y)
    {i j : Fin 3} (ij : i≠j) (z : ℤ) : f (naturalDepth m a (intPt m i j z))=f z := by
  have rep (v : Vertex m) (hc : OnCycle i j v) : ∃ q : ℤ, intPt m i j q=v ∧ f (naturalDepth m a v)=f q := by
    rcases v with b|⟨r,d⟩
    · cases b
      · exact ⟨0,(intPt_first m i j 0 (Nat.zero_le _)).trans (armPt_zero m _),rfl⟩
      · exact ⟨armSize m i,(intPt_first m i j _ le_rfl).trans (armPt_last m _),(ends i).symm⟩
    · rcases hc with rfl|rfl
      · have h : d.val+1≤armSize m r := by have := d.isLt;dsimp [armSize];omega
        exact ⟨(d.val+1:ℕ),(intPt_first m r j _ h).trans (armPt_inner m r d),rfl⟩
      · have h : d.val+1≤armSize m r := by have := d.isLt;dsimp [armSize];omega
        exact ⟨-((d.val+1:ℕ):ℤ),(intPt_second m i r _ h).trans (armPt_inner m r d),(ng _).symm⟩
  obtain ⟨q,eq,lab⟩ := rep (intPt m i j z) (cyclePt_on ..)
  exact lab.trans (per i j ij q z ((intPt_mod_iff m ij q z).mp eq))

/-- Every reflection preserves a signed periodic label with consistent values at the right pole. -/
theorem group_preserves_label {A : Type*} (f : ℤ→A) (m : Fin 3 → ℕ) (a : Fin 3)
    (ng : ∀ z,f (-z)=f z) (ends : ∀i,f (armSize m i)=f (armSize m a))
    (per : ∀i j, i≠j → ∀ x y : ℤ, (perimeter m i j:ℤ) ∣ x-y → f x=f y)
    (two : ∀i z,f (z+2*(armSize m i:ℤ))=f z) :
    reflectionGroup m ≤ labelPerms (fun x => f (naturalDepth m a x)) := by
  apply (Subgroup.closure_le _).mpr
  rintro p ⟨i,j,ij,b,rfl⟩ x
  by_cases off : ¬OnCycle i j x
  · rw [reflection_off m ij b off]
  obtain ⟨z,eq⟩ : ∃ z : ℤ,intPt m i j z=x := by
    let q := vertexCoord m i j x
    exact ⟨q.val,(congrArg (cyclePt m i j) (indexZ_val _ q)).trans (pt_coord m ij x (by tauto))⟩
  subst x
  change f (naturalDepth m a (reflection m ij b (intPt m i j z))) = f (naturalDepth m a (intPt m i j z))
  cases b
  · rw [false_reflect_int,label_intPt f m a ng ends per ij,label_intPt f m a ng ends per ij,ng]
  · rw [true_reflect_int,label_intPt f m a ng ends per ij,label_intPt f m a ng ends per ij,two,ng]

theorem group_preserves_color (m : Fin 3 → ℕ) (par : ℕ) (same : ∀i,armSize m i%2=par%2) :
    reflectionGroup m ≤ labelPerms (naturalColor m par) := by
  let f (z : ℤ) := decide (z%2=1)
  have even' (i j : Fin 3) : (2:ℤ)∣(perimeter m i j:ℤ) := by
    have h1 := same i;have h2 := same j
    exact ⟨((perimeter m i j)/2:ℕ),by dsimp [perimeter] at *;omega⟩
  have hlabel (x : Vertex m) : naturalColor m par x=f (naturalDepth m 0 x) := by
    rcases x with b|⟨i,d⟩
    · cases b
      · rfl
      · change decide (par%2=1)=decide ((armSize m 0:ℤ)%2=1)
        exact decide_eq_decide.mpr (by have := same 0;omega)
    · change decide ((d.val+1)%2=1)=decide (((d.val+1:ℕ):ℤ)%2=1)
      exact decide_eq_decide.mpr (by omega)
  have h := group_preserves_label f m 0 (fun z => decide_eq_decide.mpr (by omega))
    (fun i => decide_eq_decide.mpr (by have := same i;have := same 0;omega))
    (fun i j _ x y div => by
      obtain ⟨q,hq⟩ := (even' i j).trans div
      exact decide_eq_decide.mpr (by omega))
    (fun i z => decide_eq_decide.mpr (by omega))
  intro p hp x
  rw [hlabel,hlabel]
  exact h hp x

end Bootstrap.Theta

#print axioms Bootstrap.Theta.group_preserves_color
