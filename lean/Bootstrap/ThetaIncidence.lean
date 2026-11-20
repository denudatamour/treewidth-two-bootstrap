import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.GCD.Basic

/-! Coprime transitive vertex classes in the theta self-closure argument. -/
namespace Bootstrap.ThetaIncidence

variable {A B : Type*}

open scoped Classical

/-- For a finite relation regular on both sides, both degree sums count precisely the same pairs. -/
theorem regular_degree_balance [Fintype A] [Fintype B] (R : A → B → Prop) (d e : ℕ)
    (rows : ∀ a, Fintype.card {b // R a b} = d) (cols : ∀ b, Fintype.card {a // R a b} = e) :
    Fintype.card A*d = Fintype.card B*e := by
  classical
  let swap : (Σ a : A, {b // R a b}) ≃ (Σ b : B, {a // R a b}) :=
    ⟨fun z => ⟨z.2.val,z.1,z.2.property⟩,fun z => ⟨z.2.val,z.1,z.2.property⟩,
      fun _ => rfl,fun _ => rfl⟩
  have h := Fintype.card_congr swap
  simp only [Fintype.card_sigma] at h
  simpa [rows,cols] using h

/-- With equally large nonempty sides a biregular graph has a common degree. -/
theorem regular_degrees_eq [Fintype A] [Fintype B] [Nonempty A] (R : A → B → Prop) (d e : ℕ)
    (sides : Fintype.card A = Fintype.card B)
    (rows : ∀ a, Fintype.card {b // R a b} = d) (cols : ∀ b, Fintype.card {a // R a b} = e) :
    d = e := by
  have bal := regular_degree_balance R d e rows cols
  rw [←sides] at bal
  exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos bal

/-- A finite nonempty incidence relation regular on each side is complete
when the two side sizes are relatively prime. -/
theorem full_of_regular [Fintype A] [Fintype B] (R : A → B → Prop)
    (cop : (Fintype.card A).Coprime (Fintype.card B))
    (hit : ∃ a b, R a b)
    (row : ∀ a a', Fintype.card {b // R a b} = Fintype.card {b // R a' b})
    (col : ∀ b b', Fintype.card {a // R a b} = Fintype.card {a // R a b'}) :
    ∀ a b, R a b := by
  classical
  obtain ⟨a₀,b₀,h₀⟩ := hit
  let d := Fintype.card {b // R a₀ b}
  let e := Fintype.card {a // R a b₀}
  have double : Fintype.card A*d = Fintype.card B*e :=
    regular_degree_balance R d e (fun x => row x a₀) (fun y => col y b₀)
  have dv : Fintype.card B ∣ d := cop.symm.dvd_of_dvd_mul_left ⟨e,double⟩
  have dp : 0 < d := Fintype.card_pos_iff.mpr ⟨⟨b₀,h₀⟩⟩
  have size : d = Fintype.card B :=
    Nat.le_antisymm (Fintype.card_subtype_le (R a₀)) (Nat.le_of_dvd dp dv)
  intro a b
  have all : Function.Bijective (Subtype.val : {y // R a y} → B) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨Subtype.val_injective,(row a a₀).trans size⟩
  obtain ⟨y,hy⟩ := all.surjective b
  exact hy ▸ y.property

/-- Row and column comparisons may be supplied by any permutations transporting the given relation. -/
theorem full_of_transitive [Fintype A] [Fintype B] (R : A → B → Prop)
    (cop : (Fintype.card A).Coprime (Fintype.card B)) (hit : ∃ a b, R a b)
    (row : ∀ a a', ∃ f : B ≃ B, ∀ b, R a b ↔ R a' (f b))
    (col : ∀ b b', ∃ f : A ≃ A, ∀ a, R a b ↔ R (f a) b') :
    ∀ a b, R a b := by
  classical
  apply full_of_regular R cop hit
  · intro a a'
    obtain ⟨f,h⟩ := row a a'
    exact Fintype.card_congr (f.subtypeEquiv h)
  · intro b b'
    obtain ⟨f,h⟩ := col b b'
    exact Fintype.card_congr (f.subtypeEquiv h)

end Bootstrap.ThetaIncidence

#print axioms Bootstrap.ThetaIncidence.full_of_transitive
