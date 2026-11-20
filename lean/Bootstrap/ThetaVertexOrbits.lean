import Bootstrap.ThetaTranslationGroup
import Bootstrap.ThetaPeriodArithmetic

namespace Bootstrap.Theta

open scoped Classical

def reflectionRelated (m : Fin 3 → ℕ) (x y : Vertex m) :=
  ∃ p : Equiv.Perm (Vertex m), p ∈ reflectionGroup m ∧ p x=y

private def orbitSetoid (m : Fin 3 → ℕ) : Setoid (Vertex m) where
  r := reflectionRelated m
  iseqv := by
    refine ⟨fun _ => ⟨1,(reflectionGroup m).one_mem,rfl⟩,?_,?_⟩
    · rintro x y ⟨p,hp,rfl⟩
      exact ⟨p⁻¹,(reflectionGroup m).inv_mem hp,Equiv.Perm.inv_apply_self _ _⟩
    · rintro x y z ⟨p,hp,rfl⟩ ⟨q,hq,rfl⟩
      exact ⟨q*p,(reflectionGroup m).mul_mem hq hp,rfl⟩

private def label (m : Fin 3 → ℕ) (x : Vertex m) := Quotient.mk (orbitSetoid m) x

private theorem label_same (m : Fin 3 → ℕ) {p : Equiv.Perm (Vertex m)} (hp : p∈reflectionGroup m)
    (x : Vertex m) : label m (p x)=label m x := Eq.symm (Quotient.sound ⟨p,hp,rfl⟩)

/-- The common orbit label depends only on signed residue of the natural arm depth. -/
theorem related_of_dvd (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    (s v : Fin 3) (x y : ℕ) (hx : x≤armSize m s) (hy : y≤armSize m v)
    (hdiv : let g := Nat.gcd (2*armSize m i) (Nat.gcd (perimeter m i j) (perimeter m i t))
            (g:ℤ) ∣ (x:ℤ)-y ∨ (g:ℤ) ∣ (x:ℤ)+y) :
    reflectionRelated m (armPt m s x) (armPt m v y) := by
  classical
  let B (z : ℤ) := label m (intPt m i j z)
  let C (z : ℤ) := label m (intPt m i t z)
  have neg {a b : Fin 3} (ab : a≠b) (z : ℤ) : label m (intPt m a b (-z)) = label m (intPt m a b z) := by
    rw [←false_reflect_int m ab]
    exact label_same m (reflection_mem m ab false) _
  have two {a b : Fin 3} (ab : a≠b) (z : ℤ) : label m (intPt m a b (z+2*(armSize m a:ℤ))) = label m (intPt m a b z) := by
    rw [←rotate_int m ab]
    exact label_same m ((reflectionGroup m).mul_mem (reflection_mem m ab true) (reflection_mem m ab false)) _
  have period (a b : Fin 3) (z : ℤ) : label m (intPt m a b (z+(armSize m a:ℤ)+armSize m b))=label m (intPt m a b z) := by
    have e : z+(armSize m a:ℤ)+armSize m b=z+(perimeter m a b:ℤ) := by dsimp [perimeter]; omega
    rw [e,intPt_period]
  have common (d : ℕ) (hd : d≤armSize m i) : B d = C d := by
    dsimp [B,C]
    rw [intPt_first m i j d hd,intPt_first m i t d hd]
  obtain ⟨eq,dvd⟩ := ThetaPeriodArithmetic.glued_periods (armSize m i) (armSize m j) (armSize m t)
    (by dsimp [armSize]; omega) B C (neg ij) (neg it) (two ij) (two it) (period i j) (period i t) common
  have repr (a : Fin 3) (d : ℕ) (hd : d≤armSize m a) : label m (armPt m a d)=B d := by
    by_cases ai : a=i
    · subst a
      exact congrArg (label m) (intPt_first m i j d hd).symm
    by_cases aj : a=j
    · subst a
      exact (congrArg (label m) (intPt_second m i j d hd).symm).trans (neg ij d)
    have at' := third_of_ne ij it jt a ai aj
    subst a
    have inC : label m (armPt m t d)=C d := (congrArg (label m) (intPt_second m i t d hd).symm).trans (neg it d)
    exact inC.trans (congrFun eq d).symm
  apply Quotient.exact (s := orbitSetoid m)
  exact (repr s x hx).trans ((dvd x y hdiv).trans (repr v y hy).symm)

theorem arm_representation (m : Fin 3 → ℕ) (v : Vertex m) :
    ∃ i d, d≤armSize m i ∧ armPt m i d=v := by
  rcases v with b|⟨i,d⟩
  · cases b
    · exact ⟨0,0,Nat.zero_le _,armPt_zero m 0⟩
    · exact ⟨0,armSize m 0,le_rfl,armPt_last m 0⟩
  · exact ⟨i,d.val+1,by have := d.isLt;dsimp [armSize];omega,armPt_inner m i d⟩

theorem transitive_when_one (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    (one : Nat.gcd (2*armSize m i) (Nat.gcd (perimeter m i j) (perimeter m i t)) = 1) (x y : Vertex m) :
    reflectionRelated m x y := by
  obtain ⟨a,s,hs,rfl⟩ := arm_representation m x
  obtain ⟨b,d,hd,rfl⟩ := arm_representation m y
  exact related_of_dvd m ij it jt a b s d hs hd (by dsimp; simp [one])

end Bootstrap.Theta

#print axioms Bootstrap.Theta.related_of_dvd
#print axioms Bootstrap.Theta.transitive_when_one
