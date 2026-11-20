import Bootstrap.ThetaSelfBipartite

namespace Bootstrap.Theta.Corridor

abbrev M (r : Fin 3 → ℕ) (d : ℕ) := fun i => r i*d-2
abbrev V (r : Fin 3 → ℕ) (d : ℕ) := Vertex (M r d)
abbrev H (r : Fin 3 → ℕ) (d : ℕ) := graph (M r d)
noncomputable abbrev F (r : Fin 3 → ℕ) (d : ℕ) := terminalGraph (H r d) (H r d)

/-- The two endpoint labels in the oriented segment construction. -/
def Junction (r : Fin 3 → ℕ) (d : ℕ) (c : Bool) : V r d → Prop
  | .inl b => c=b
  | .inr ⟨_,j⟩ => (j.val+1)%d=0 ∧ c=decide (((j.val+1)/d)%2=1)

/-- A midpoint at scale two has both port labels. At larger scales the
first and last internal positions have the labels of their respective ends. -/
def Port (r : Fin 3 → ℕ) (d : ℕ) (c : Bool) : V r d → Prop
  | .inl _ => False
  | .inr ⟨_,j⟩ =>
    ((j.val+1)%d=1 ∧ c=decide (((j.val+1)/d)%2=1)) ∨
      ((j.val+1)%d+1=d ∧ c=!(decide (((j.val+1)/d)%2=1)))

def incidence (r : Fin 3 → ℕ) (d : ℕ) (coloured : Bool) (x y : V r d) :=
  ∃ a b : Bool, Junction r d a x ∧ Port r d b y ∧ (coloured=true → a=b)

/-- Keep the actual theta edges and complete the indicated junction-port
incidences. In the uncoloured case both labels are allowed. -/
def segmentGraph (r : Fin 3 → ℕ) (d : ℕ) (coloured : Bool) : SimpleGraph (V r d) where
  Adj x y := (H r d).Adj x y ∨ (x ≠ y ∧ (incidence r d coloured x y ∨ incidence r d coloured y x))
  symm := by
    rintro x y (e|⟨ne,h⟩)
    · exact Or.inl ((H r d).symm e)
    · exact Or.inr ⟨ne.symm,h.symm⟩
  loopless := fun x h => h.elim ((H r d).loopless x) (fun p => p.1 rfl)

theorem seed_le_segment (r : Fin 3 → ℕ) (d : ℕ) (c : Bool) :
    H r d ≤ segmentGraph r d c := fun _ _ e => Or.inl e

/-- The coordinate z on arm i, counted from its common left pole. -/
def point {k : ℕ} (m : Fin k → ℕ) (i : Fin k) (z : ℕ) : Vertex m :=
  if z=0 then pole m false else if h : z < m i+2 then inner m i ⟨z-1,by omega⟩ else pole m true

@[simp] theorem point_zero {k : ℕ} (m : Fin k → ℕ) (i : Fin k) : point m i 0 = pole m false := by
  simp [point]

@[simp] theorem point_end {k : ℕ} (m : Fin k → ℕ) (i : Fin k) : point m i (m i+2) = pole m true := by
  simp [point]

theorem point_inner {k : ℕ} (m : Fin k → ℕ) (i : Fin k) (j : Fin (m i+1)) :
    point m i (j.val+1) = inner m i j := by
  have bound : j.val+1 < m i+2 := by have := j.isLt; omega
  simp [point,bound]

theorem point_interior {k : ℕ} (m : Fin k → ℕ) {i : Fin k} {z : ℕ}
    (pos : 0 < z) (bound : z < m i+2) :
    point m i z = inner m i ⟨z-1,by omega⟩ := by simp [point,pos.ne',bound]

theorem point_edge {k : ℕ} (m : Fin k → ℕ) (i : Fin k) {z : ℕ} (step : z < m i+2) :
    (graph m).Adj (point m i z) (point m i (z+1)) := by
  by_cases zero : z=0
  · subst z
    rw [point_zero,show 0+1=(0 : Fin (m i+1)).val+1 from rfl,point_inner]
    rfl
  rw [point_interior m (by omega) step]
  by_cases last : z+1 = m i+2
  · rw [last,point_end]
    change z-1=m i
    omega
  · rw [point_interior m (by omega) (by omega : z+1<m i+2)]
    exact ⟨rfl,Or.inl (by change z-1+1=z+1-1; omega)⟩

private theorem edge_at_pole {k : ℕ} (m : Fin k → ℕ) (b : Bool) (i : Fin k) (j : Fin (m i+1))
    (edge : (graph m).Adj (pole m b) (inner m i j)) :
    ∃ z < m i+2, (pole m b = point m i z ∧ inner m i j = point m i (z+1)) ∨
      (inner m i j = point m i z ∧ pole m b = point m i (z+1)) := by
  cases b with
  | false =>
    change j.val=0 at edge
    refine ⟨0,by omega,Or.inl ⟨(point_zero _ _).symm,?_⟩⟩
    rw [← point_inner m i j,edge]
  | true =>
    change j.val=m i at edge
    refine ⟨j.val+1,by omega,Or.inr ⟨(point_inner _ _ _).symm,?_⟩⟩
    rw [edge,show m i+1+1=m i+2 from rfl,point_end]

theorem edge_coordinates {k : ℕ} (m : Fin k → ℕ) {x y : Vertex m} (e : (graph m).Adj x y) :
    ∃ i z, z < m i+2 ∧ ((x=point m i z ∧ y=point m i (z+1)) ∨
      (y=point m i z ∧ x=point m i (z+1))) := by
  cases x with
  | inl a =>
    cases y with
    | inl b => exact False.elim e
    | inr p => obtain ⟨i,j⟩ := p; exact ⟨i,edge_at_pole m a i j e⟩
  | inr p =>
    obtain ⟨i,j⟩ := p
    cases y with
    | inl b =>
      obtain ⟨z,hz,h⟩ := edge_at_pole m b i j ((graph m).symm e)
      exact ⟨i,z,hz,h.symm⟩
    | inr q =>
      obtain ⟨l,t⟩ := q
      obtain ⟨rfl,q|q⟩ := e
      · refine ⟨i,j.val+1,by have := j.isLt; omega,Or.inl ⟨(point_inner _ _ _).symm,?_⟩⟩
        rw [q,point_inner]
        rfl
      · refine ⟨i,t.val+1,by have := t.isLt; omega,Or.inr ⟨(point_inner _ _ _).symm,?_⟩⟩
        rw [q,point_inner]
        rfl

/-- Complete a spanning permutation with one exceptional edge inside the
terminal graph; all of its edge images may already use the closure. -/
theorem terminal_near_perm {X : Type*} [Fintype X] (J : SimpleGraph X) (p : Equiv.Perm X)
    {u v : X} (uv : J.Adj u v)
    (maps : ∀ i j, J.Adj i j → ¬((i=u ∧ j=v) ∨ (i=v ∧ j=u)) →
      (terminalGraph J J).Adj (p i) (p j)) :
    ∀ x y, (terminalGraph J J).Adj (p x) (p y) ↔ (terminalGraph J J).Adj x y := by
  have born : (terminalGraph J J).Adj (p u) (p v) :=
    (terminal_fixed J J).le (Or.inr ⟨u,v,p.toEmbedding,uv,rfl,rfl,maps⟩)
  apply terminal_perm
  intro i j e
  by_cases ex : (i=u ∧ j=v) ∨ (i=v ∧ j=u)
  · rcases ex with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact born
    · exact (terminalGraph J J).symm born
  · exact maps i j e ex

end Bootstrap.Theta.Corridor

#print axioms Bootstrap.Theta.Corridor.edge_coordinates
#print axioms Bootstrap.Theta.Corridor.terminal_near_perm
