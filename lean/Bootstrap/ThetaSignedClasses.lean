import Bootstrap.ThetaLabelInvariance
import Bootstrap.ThetaIncidence
import Bootstrap.ThetaExternalSeeds
import Mathlib.Data.Int.ModEq

namespace Bootstrap.Theta

open scoped Classical

def orbitMod (m : Fin 3 → ℕ) :=
  (2*armSize m 0).gcd ((perimeter m 0 1).gcd (perimeter m 0 2))

def SignedClass (n x y : ℤ) : Prop := x ≡ y [ZMOD n] ∨ x ≡ -y [ZMOD n]

theorem SignedClass.symm {n x y : ℤ} : SignedClass n x y → SignedClass n y x := by
  rintro (h|h)
  · exact Or.inl h.symm
  · exact Or.inr (by simpa only [neg_neg] using h.neg.symm)

theorem SignedClass.trans {n x y z : ℤ} (h : SignedClass n x y) (k : SignedClass n y z) :
    SignedClass n x z := by
  rcases h with h|h <;> rcases k with k|k
  · exact Or.inl (h.trans k)
  · exact Or.inr (h.trans k)
  · exact Or.inr (h.trans k.neg)
  · exact Or.inl (by simpa only [neg_neg] using h.trans k.neg)

theorem SignedClass.change {n x y c : ℤ} (h : SignedClass n x y) :
    SignedClass n x c ↔ SignedClass n y c :=
  ⟨h.symm.trans,h.trans⟩

theorem signed_dvd (n x y : ℤ) : SignedClass n x y ↔ n∣x-y ∨ n∣x+y := by
  unfold SignedClass
  rw [Int.modEq_comm (a:=x) (b:=y),Int.modEq_comm (a:=x) (b:=-y),
    Int.modEq_iff_dvd,Int.modEq_iff_dvd,sub_neg_eq_add]

def depthClass (m : Fin 3 → ℕ) (c : ℤ) (v : Vertex m) : Prop :=
  SignedClass (orbitMod m) (naturalDepth m 0 v) c

private theorem raw_mod (m : Fin 3 → ℕ) :
    (∀ i, (armSize m i:ℤ) ≡ armSize m 0 [ZMOD (orbitMod m:ℤ)]) ∧
    (∀ i, (orbitMod m:ℤ) ∣ 2*(armSize m i:ℤ)) ∧
    (∀ i j, (orbitMod m:ℤ) ∣ (perimeter m i j:ℤ)) := by
  let g : ℤ := orbitMod m
  have g0N : orbitMod m ∣ 2*armSize m 0 := Nat.gcd_dvd_left _ _
  have g1N : orbitMod m ∣ perimeter m 0 1 := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have g2N : orbitMod m ∣ perimeter m 0 2 := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have g0 : g ∣ 2*(armSize m 0:ℤ) := by dsimp only [g];exact_mod_cast g0N
  have g1 : g ∣ (armSize m 0:ℤ) + armSize m 1 := by dsimp only [g];change orbitMod m ∣ armSize m 0+armSize m 1 at g1N;exact_mod_cast g1N
  have g2 : g ∣ (armSize m 0:ℤ) + armSize m 2 := by dsimp only [g];change orbitMod m ∣ armSize m 0+armSize m 2 at g2N;exact_mod_cast g2N
  have atI (i : Fin 3) : (armSize m i:ℤ) ≡ armSize m 0 [ZMOD g] := by
    by_cases e : i=0
    · rw [e]
    have hi : g ∣ (armSize m 0:ℤ)+armSize m i := by
      by_cases f : i=1
      · exact f ▸ g1
      · have k := third_of_ne (show (0:Fin 3)≠1 by decide)
          (show (0:Fin 3)≠2 by decide) (by decide) i e f
        exact k ▸ g2
    exact Int.modEq_iff_dvd.mpr (by convert dvd_sub g0 hi using 1 <;> omega)
  have sums (i j : Fin 3) : g ∣ (armSize m i:ℤ)+armSize m j := by
    convert dvd_sub (dvd_sub g0 (atI i).dvd) (atI j).dvd using 1 <;> omega
  exact ⟨atI,fun i => by simpa [two_mul] using sums i i,fun i j => by simpa [perimeter] using sums i j⟩

theorem group_preserves_class (m : Fin 3 → ℕ) (c : ℤ) {p : Equiv.Perm (Vertex m)} (hp : p ∈ reflectionGroup m)
    (v : Vertex m) : depthClass m c (p v) ↔ depthClass m c v := by
  obtain ⟨ends,two,sums⟩ := raw_mod m
  let n : ℤ := orbitMod m
  let tag (z : ℤ) := SignedClass n z c
  have perm := group_preserves_label tag m 0
    (fun z => propext (SignedClass.change (c:=c) (show SignedClass n (-z) z from Or.inr Int.ModEq.rfl)))
    (fun i => propext (SignedClass.change (c:=c) (Or.inl (ends i))))
    (fun i j _ x y d => propext (SignedClass.change (c:=c) (Or.inl (Int.modEq_iff_dvd.mpr ((sums i j).trans d)).symm)))
    (fun i z => propext (SignedClass.change (c:=c) (Or.inl (Int.modEq_iff_dvd.mpr
      (by convert dvd_neg.mpr (two i) using 1 <;> omega)))))
  exact Iff.of_eq (perm hp v)

private theorem depth_rep (m : Fin 3 → ℕ) (v : Vertex m) :
    ∃ i, naturalDepth m 0 v≤armSize m i ∧ armPt m i (naturalDepth m 0 v)=v := by
  rcases v with c|⟨i,j⟩
  · cases c
    · exact ⟨0,Nat.zero_le _,armPt_zero m _⟩
    · exact ⟨0,le_rfl,armPt_last m _⟩
  · exact ⟨i,by change j.val+1≤m i+2;have := j.isLt;omega,armPt_inner m i j⟩

theorem reflectionRelated_iff_signed (m : Fin 3 → ℕ) (v w : Vertex m) :
    reflectionRelated m v w ↔ SignedClass (orbitMod m) (naturalDepth m 0 v) (naturalDepth m 0 w) := by
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact (group_preserves_class m (naturalDepth m 0 (p v)) hp v).mp (Or.inl Int.ModEq.rfl)
  · intro h
    obtain ⟨i,hi,ei⟩ := depth_rep m v
    obtain ⟨j,hj,ej⟩ := depth_rep m w
    rw [←ei,←ej]
    exact related_of_dvd m (show (0:Fin 3)≠1 by decide) (show (0:Fin 3)≠2 by decide) (by decide)
      i j _ _ hi hj ((signed_dvd _ _ _).mp h)

/-- Two nonempty signed residue classes of relatively prime sizes have
complete terminal incidence as soon as one original or terminal edge joins them. -/
theorem complete_class_incidence (m : Fin 3 → ℕ) (A B : Vertex m → Prop) (a b : ℤ)
    (ha : ∀ x,A x ↔ depthClass m a x) (hb : ∀ x,B x ↔ depthClass m b x)
    (cop : (Fintype.card {x // A x}).Coprime (Fintype.card {x // B x}))
    (hit : ∃ x y,A x ∧ B y ∧ (thetaClosure m).Adj x y) :
    ∀ x y,A x → B y → (thetaClosure m).Adj x y := by
  classical
  let R (x : {v // A v}) (y : {v // B v}) := (thetaClosure m).Adj x.val y.val
  have move (P : Vertex m → Prop) (c : ℤ) (eq : ∀ x,P x ↔ depthClass m c x)
      (x y : {v // P v}) : reflectionRelated m x.val y.val :=
    (reflectionRelated_iff_signed ..).mpr (((eq _).mp x.2).trans ((eq _).mp y.2).symm)
  let perm (P : Vertex m → Prop) (c : ℤ) (eq : ∀ x,P x ↔ depthClass m c x)
      (p : Equiv.Perm (Vertex m)) (hp : p∈reflectionGroup m) : {v // P v} ≃ {v // P v} :=
    p.subtypeEquiv (fun x => (eq x).trans
      ((group_preserves_class m c hp x).symm.trans (eq (p x)).symm))
  have all : ∀ x y,R x y := by
    apply ThetaIncidence.full_of_transitive R cop
    · obtain ⟨x,y,hx,hy,e⟩ := hit
      exact ⟨⟨x,hx⟩,⟨y,hy⟩,e⟩
    · intro x x'
      obtain ⟨p,hp,eq⟩ := move A a ha x x'
      refine ⟨perm B b hb p hp,fun y => ?_⟩
      change (thetaClosure m).Adj x.val y.val ↔ (thetaClosure m).Adj x'.val (p y.val)
      rw [←eq];exact (preserves_of_mem m hp _ _).symm
    · intro y y'
      obtain ⟨p,hp,eq⟩ := move B b hb y y'
      refine ⟨perm A a ha p hp,fun x => ?_⟩
      change (thetaClosure m).Adj x.val y.val ↔ (thetaClosure m).Adj (p x.val) y'.val
      rw [←eq];exact (preserves_of_mem m hp _ _).symm
  exact fun x y hx hy => all ⟨x,hx⟩ ⟨y,hy⟩

end Bootstrap.Theta

#print axioms Bootstrap.Theta.reflectionRelated_iff_signed
#print axioms Bootstrap.Theta.complete_class_incidence
