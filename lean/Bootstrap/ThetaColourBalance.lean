import Bootstrap.ThetaIncidence
import Bootstrap.ThetaSelfBipartite

namespace Bootstrap.Theta

variable {V : Type*} {k : ℕ}
open scoped Classical

/-- Complement of the available edges within the prescribed two-colour host. -/
def missingBetween (c : V → Bool) (F : SimpleGraph V) : SimpleGraph V where
  Adj x y := c x ≠ c y ∧ ¬ F.Adj x y
  symm := fun _ _ h => ⟨h.1.symm,fun e => h.2 (F.symm e)⟩
  loopless := fun _ h => h.1 rfl

theorem transported_degree [Fintype V] (Q : SimpleGraph V) (p : Equiv.Perm V)
    (stable : ∀ i j, Q.Adj (p i) (p j) ↔ Q.Adj i j) (x : V) : Q.degree (p x) = Q.degree x := by
  let iso : Q ≃g Q := ⟨p, fun {i j} => stable i j⟩
  have e := Fintype.card_congr (iso.mapNeighborSet x)
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using e.symm

theorem transported_missing_degree [Fintype V] (c : V → Bool) (F : SimpleGraph V)
    (p : Equiv.Perm V) (edges : ∀ i j, F.Adj (p i) (p j) ↔ F.Adj i j)
    (colours : ∀ i j, c (p i) = c (p j) ↔ c i = c j) (x : V) :
    (missingBetween c F).degree (p x) = (missingBetween c F).degree x := by
  apply transported_degree _ p _ x
  intro i j
  change (_ ≠ _ ∧ ¬ _) ↔ (_ ≠ _ ∧ ¬ _)
  exact and_congr (not_congr (colours i j)) (not_congr (edges i j))

/-- Biregularity on two equally sized parts gives one common degree on the full graph. -/
theorem uniform_degree [Fintype V] (Q : SimpleGraph V) (c : V → Bool)
    (x₀ y₀ : V) (hx : c x₀ = false) (hy : c y₀ = true)
    (size : Fintype.card {x // c x = false} = Fintype.card {x // c x = true})
    (proper : ∀ x y, Q.Adj x y → c x ≠ c y)
    (same : ∀ x y, c x = c y → Q.degree x = Q.degree y) :
    ∀ z, Q.degree z = Q.degree x₀ := by
  classical
  let A := {x // c x = false}
  let B := {x // c x = true}
  letI : Nonempty A := ⟨⟨x₀,hx⟩⟩
  let R := fun (a : A) (b : B) => Q.Adj a.val b.val
  have row (a : A) : Fintype.card {b : B // R a b} = Q.degree a.val := by
    let f : {b : B // R a b} ≃ Q.neighborSet a.val :=
      ⟨fun b => ⟨b.val.val,b.property⟩,
       fun z => ⟨⟨z.val,by
         have diff := proper _ _ z.property
         rw [a.property] at diff
         cases eq : c z.val <;> simp_all⟩,z.property⟩,fun _ => rfl,fun _ => rfl⟩
    exact (Fintype.card_congr f).trans (SimpleGraph.card_neighborSet_eq_degree _ _)
  have col (b : B) : Fintype.card {a : A // R a b} = Q.degree b.val := by
    let f : {a : A // R a b} ≃ Q.neighborSet b.val :=
      ⟨fun a => ⟨a.val.val,Q.symm a.property⟩,
       fun z => ⟨⟨z.val,by
         have diff := proper _ _ z.property
         rw [b.property] at diff
         cases eq : c z.val <;> simp_all⟩,Q.symm z.property⟩,fun _ => rfl,fun _ => rfl⟩
    exact (Fintype.card_congr f).trans (SimpleGraph.card_neighborSet_eq_degree _ _)
  have balance := ThetaIncidence.regular_degrees_eq R (Q.degree x₀) (Q.degree y₀) size
    (fun a => (row a).trans (same _ _ (a.property.trans hx.symm)))
    (fun b => (col b).trans (same _ _ (b.property.trans hy.symm)))
  intro z
  cases h : c z with
  | false => exact same _ _ (h.trans hx.symm)
  | true => exact (same _ _ (h.trans hy.symm)).trans balance.symm

def reversePosition (m : Fin k → ℕ) : Vertex m → Vertex m
  | .inl b => .inl (!b)
  | .inr ⟨i,j⟩ => inner m i j.rev

theorem reverse_twice (m : Fin k → ℕ) (x : Vertex m) : reversePosition m (reversePosition m x) = x := by
  rcases x with b | ⟨i,j⟩
  · cases b <;> rfl
  · simp [reversePosition,inner]

/-- On odd arms reversing every arm gives a bijection of the natural colour classes. -/
theorem odd_sides_equal (m : Fin k → ℕ) (odd : ∀ i, (m i + 2)%2 = 1) :
    Fintype.card {x // naturalColor m 1 x = false} = Fintype.card {x // naturalColor m 1 x = true} := by
  let p : Vertex m ≃ Vertex m := ⟨reversePosition m,reversePosition m,reverse_twice m,reverse_twice m⟩
  have flip (x : Vertex m) : naturalColor m 1 x = false ↔ naturalColor m 1 (p x) = true := by
    rcases x with b | ⟨i,j⟩
    · cases b <;> simp [p,reversePosition,naturalColor]
    · change (decide ((j.val+1)%2=1) = false) ↔ (decide ((j.rev.val+1)%2=1) = true)
      simp only [decide_eq_false_iff_not,decide_eq_true_eq,Fin.val_rev]
      have := odd i
      have := j.isLt
      omega
  exact Fintype.card_congr (p.subtypeEquiv flip)

end Bootstrap.Theta

#print axioms Bootstrap.Theta.uniform_degree
#print axioms Bootstrap.Theta.odd_sides_equal
