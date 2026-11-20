import Bootstrap.EqualArmCoordinates

namespace Bootstrap.Theta.EqualArms

variable {m : Nat}

private def Pair {X : Type*} (x y u v : X) := (x = u ∧ y = v) ∨ (x = v ∧ y = u)

private theorem pair_comp {X : Type*} {x y u v a b : X} (h : Pair x y u v) (r : Pair u v a b) :
    Pair x y a b := by
  unfold Pair at *
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> tauto

private theorem represented_pole (b : Bool) {z : V m} (h : (H m).Adj (pole (M m) b) z) :
    ∃ (i : Fin 3) (g : Nat), g < L m ∧ Pair (pole (M m) b) z (point m i g) (point m i (g+1)) := by
  obtain ⟨i,rfl⟩ := pole_neighbor m b h
  cases b
  · exact ⟨i,0,by unfold L; omega,Or.inl ⟨(point_zero ..).symm,rfl⟩⟩
  · refine ⟨i,L m-1,by unfold L; omega,Or.inr ⟨?_,rfl⟩⟩
    rw [show L m-1+1=L m by unfold L; omega,point_last]

private theorem represented {x y : V m} (xy : (H m).Adj x y) :
    ∃ (i : Fin 3) (g : Nat), g < L m ∧ Pair x y (point m i g) (point m i (g+1)) := by
  rcases x with b | ⟨i,j⟩
  · exact represented_pole b xy
  · rcases y with c | ⟨s,q⟩
    · obtain ⟨s,g,hg,hp⟩ := represented_pole c xy.symm
      exact ⟨s,g,hg,pair_comp (Or.inr ⟨rfl,rfl⟩) hp⟩
    · obtain ⟨rfl,eq | eq⟩ := xy
      · refine ⟨i,j.val+1,by unfold L; have b := j.isLt; change j.val < m+1 at b; omega,
          Or.inl ⟨(point_inner m i j).symm,?_⟩⟩
        rw [eq,point_inner]
        rfl
      · refine ⟨i,q.val+1,by unfold L; have b := q.isLt; change q.val < m+1 at b; omega,
          Or.inr ⟨?_,(point_inner m i q).symm⟩⟩
        rw [eq,point_inner]
        rfl

private theorem unique_edge {i d : Fin 3} {t g : Nat} (ht : t < L m) (hg : g < L m)
    (eq : Pair (point m i t) (point m i (t+1)) (point m d g) (point m d (g+1))) :
    i = d ∧ t = g := by
  rcases eq with ⟨a,b⟩ | ⟨a,b⟩ <;> have ha := congrArg level a <;> have hb := congrArg level b
  · rw [level_point _ _ _ ht.le,level_point _ _ _ hg.le] at ha
    subst g
    refine ⟨?_,rfl⟩
    by_cases z : t = 0
    · subst t
      exact oriented_arm_inj m false (by decide : 0 < 1) (by unfold L; omega) b
    · exact oriented_arm_inj m false (by omega : 0 < t) ht a
  · rw [level_point _ _ _ ht.le,level_point _ _ _ (by omega)] at ha
    rw [level_point _ _ _ (by omega),level_point _ _ _ hg.le] at hb
    omega

/-- The entire chain of every arm is preserved except for the one designated edge. -/
def Good (f : V m ↪ V m) (d : Fin 3) (g : Nat) : Prop :=
  ∀ i t, t < L m → i ≠ d ∨ t ≠ g →
    (H m).Adj (f (point m i t)) (f (point m i (t+1)))

theorem witness_gap {x y : V m} (w : Witness (H m) (H m) x y) :
    ∃ (f : V m ↪ V m) (d : Fin 3) (g : Nat), g < L m ∧ Good f d g ∧
      ((x = f (point m d g) ∧ y = f (point m d (g+1))) ∨
       (y = f (point m d g) ∧ x = f (point m d (g+1)))) := by
  obtain ⟨u,v,f,edge,rfl,rfl,keep⟩ := w
  obtain ⟨d,g,hg,pair⟩ := represented edge
  refine ⟨f,d,g,hg,?_,?_⟩
  · intro i t ht different
    apply keep _ _ (point_edge _ _ _ ht)
    intro eq
    obtain ⟨hd,hg'⟩ := unique_edge ht hg (pair_comp eq pair)
    exact different.elim (fun h => h hd) (fun h => h hg')
  · rcases pair with ⟨a,b⟩ | ⟨a,b⟩
    · exact Or.inl ⟨congrArg f a,congrArg f b⟩
    · exact Or.inr ⟨congrArg f b,congrArg f a⟩

def gap (m : Nat) (b : Bool) (g : Nat) := if b then L m - 1 - g else g

theorem Good.direction {f : V m ↪ V m} {d : Fin 3} {g : Nat} (good : Good f d g)
    (hg : g < L m) (b : Bool) (i : Fin 3) (t : Nat) (ht : t < L m)
    (keep : i ≠ d ∨ t ≠ gap m b g) :
    (H m).Adj (f (oriented m b i t)) (f (oriented m b i (t+1))) := by
  cases b
  · exact good i t ht keep
  · change (H m).Adj (f (point m i (L m-t))) (f (point m i (L m-(t+1))))
    have ht' : L m-(t+1) < L m := by omega
    have different : i ≠ d ∨ L m-(t+1) ≠ g := by
      rcases keep with h | h
      · exact Or.inl h
      · change t ≠ L m-1-g at h
        exact Or.inr (by omega)
    have e := (good i _ ht' different).symm
    rwa [show L m-(t+1)+1=L m-t by omega] at e

private theorem one_lt_end (m : Nat) : 1 < L m := by unfold L; omega

private theorem pole_image {f : V m ↪ V m} {b : Bool}
    (all : ∀ i, (H m).Adj (f (pole (M m) b)) (f (oriented m b i 1))) :
    ∃ c, f (pole (M m) b) = pole (M m) c := by
  let v := f (pole (M m) b)
  let a (i : Fin 3) : (H m).neighborSet v := ⟨_,all i⟩
  have inj : Function.Injective a := by
    intro i j e
    exact oriented_arm_inj m b (by decide) (one_lt_end m) (f.injective (congrArg Subtype.val e))
  have high := Fintype.card_le_of_injective a inj
  rw [Fintype.card_fin,SimpleGraph.card_neighborSet_eq_degree] at high
  change ∃ c, v = pole (M m) c
  cases eq : v with
  | inl c => exact ⟨c,rfl⟩
  | inr p =>
    rcases p with ⟨i,j⟩
    have deg : (H m).degree v = 2 := eq ▸ degree_inner (M m) i j
    omega

theorem choose_trace {f : V m ↪ V m} {b c : Bool} {i : Fin 3} {n : Nat}
    (hn : 0 < n) (bound : n ≤ L m) (start : f (pole (M m) b) = pole (M m) c)
    (keep : ∀ t, t < n → (H m).Adj (f (oriented m b i t)) (f (oriented m b i (t+1)))) :
    ∃ a, ∀ t, t ≤ n → f (oriented m b i t) = oriented m c a t := by
  have first := keep 0 hn
  rw [oriented_zero,start] at first
  obtain ⟨a,ha⟩ := pole_neighbor m c first
  exact ⟨a,trace m f b c i a n bound start ha keep⟩

theorem poles {f : V m ↪ V m} {d : Fin 3} {g : Nat} (hg : g < L m) (good : Good f d g) :
    ∃ c, f (pole (M m) false) = pole (M m) c ∧ f (pole (M m) true) = pole (M m) (!c) := by
  obtain ⟨b,hb⟩ : ∃ b, 0 ≠ gap m b g := by
    by_cases z : g = 0
    · refine ⟨true,?_⟩
      unfold gap L
      simp [z]
    · exact ⟨false,fun e => z (show g = 0 from e.symm)⟩
  have all (i : Fin 3) := good.direction hg b i 0 (by unfold L; omega) (Or.inr hb)
  simp only [oriented_zero] at all
  obtain ⟨c,hc⟩ := pole_image all
  obtain ⟨j,hj⟩ : ∃ j : Fin 3, j ≠ d := exists_ne _
  obtain ⟨a,ha⟩ := choose_trace (n:=L m) (b:=b) (c:=c) (i:=j) (by unfold L; omega) le_rfl hc
    (fun t ht => good.direction hg b j t ht (Or.inl hj))
  have other := ha (L m) le_rfl
  simp only [oriented_last] at other
  cases b
  · exact ⟨c,hc,other⟩
  · exact ⟨!c,other,by simpa using hc⟩

end Bootstrap.Theta.EqualArms

#print axioms Bootstrap.Theta.EqualArms.witness_gap
#print axioms Bootstrap.Theta.EqualArms.poles
