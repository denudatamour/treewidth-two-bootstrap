import Bootstrap.FMSLowerHost

namespace Bootstrap

variable {W : Type*}

/-- Integer constants for a positive linear lower bound on every sufficiently large order. -/
def HasLinearLower (H : SimpleGraph W) : Prop :=
  ∃ A n₀ : ℕ, 0 < A ∧ ∀ n, n₀ ≤ n → n ≤ A * maxTime H n

def HasLinearOrder (H : SimpleGraph W) : Prop := HasLinearLower H ∧ HasLinearUpper H

namespace FMS

theorem two_neighbours_of_minimum [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (minimum : ∀ w, 2 ≤ H.degree w) : HasTwoNeighbours H := by
  intro w
  have size : 1 < (H.neighborFinset w).card := minimum w
  obtain ⟨i,j,wi,wj,ne⟩ := Finset.one_lt_card_iff.mp size
  exact ⟨i,j,ne,(H.mem_neighborFinset w i).mp wi,(H.mem_neighborFinset w j).mp wj⟩

/-- The minimum-degree-two specialization of Fabian, Morris and Szabó,
Theorem 1.4. The clique has h vertices, which allows the use of the ordinary
single-contact absorption lemma without changing the linear order. -/
theorem linear_lower_of_degree_two [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (conn : H.Connected) (minimum : ∀ w, 2 ≤ H.degree w) (high : ∃ w, 2 < H.degree w)
    {a : W} (two : H.degree a = 2) : HasLinearLower H := by
  let h := Fintype.card W
  have pos : 0 < h := Fintype.card_pos_iff.mpr ⟨a⟩
  obtain ⟨l,r,N⟩ := (DegreeTwo.hasTwo_iff_degree H a).mpr two
  refine ⟨2*h,2*h+2,by omega,?_⟩
  intro n large
  have tail := path_host_bound conn (two_neighbours_of_minimum H minimum) high N (n-h) (by omega)
  change n-h ≤ h * maxTime H (h+(n-h)) at tail
  rw [Nat.add_sub_of_le (show h ≤ n by omega)] at tail
  calc
    n ≤ 2*(n-h) := by omega
    _ ≤ 2 * (h * maxTime H n) := Nat.mul_le_mul_left 2 tail
    _ = (2*h) * maxTime H n := (Nat.mul_assoc _ _ _).symm

/-- The lower-bound clause of Theorem II.1 follows because an edge at
a degree-at-least-three role has a degree-two opposite endpoint. -/
theorem linear_lower_of_edge_cover [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (conn : H.Connected) (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    (minimum : ∀ w, 2 ≤ H.degree w) (high : ∃ w, 2 < H.degree w) :
    HasLinearLower H := by
  obtain ⟨w,hw⟩ := high
  obtain ⟨i,j,_,wi,_⟩ := two_neighbours_of_minimum H minimum w
  apply linear_lower_of_degree_two H conn minimum ⟨w,hw⟩ (a:=i)
  rcases cover _ _ wi with h|h
  · omega
  · exact h

end FMS
end Bootstrap

#print axioms Bootstrap.FMS.linear_lower_of_degree_two
#print axioms Bootstrap.FMS.linear_lower_of_edge_cover
