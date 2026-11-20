import Bootstrap.OrdinaryTime
import Bootstrap.DegreeTwoTransfer

namespace Bootstrap

variable {W V : Type*}

noncomputable def terminalGraph [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) : SimpleGraph V :=
  run H G (stabilizationTime H G)

theorem terminal_fixed [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) :
    step H (terminalGraph H G) = terminalGraph H G := (stabilizationTime_spec H G).symm

theorem initial_le_terminal [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) :
    G ≤ terminalGraph H G := DegreeTwo.time_mono H G (Nat.zero_le _)

theorem run_le_closed (H : SimpleGraph W) (G D : SimpleGraph V) (start : G ≤ D)
    (fixed : step H D ≤ D) (t : ℕ) : run H G t ≤ D := by
  induction t with
  | zero => exact start
  | succ t ih => exact (step_mono H ih).trans fixed

theorem terminal_le_closed [Fintype V] (H : SimpleGraph W) (G D : SimpleGraph V) (start : G ≤ D)
    (fixed : step H D ≤ D) : terminalGraph H G ≤ D := run_le_closed H G D start fixed _

theorem terminal_mono [Fintype V] (H : SimpleGraph W) {G R : SimpleGraph V} (start : G ≤ R) :
    terminalGraph H G ≤ terminalGraph H R :=
  terminal_le_closed H G _ (start.trans (initial_le_terminal H R)) (terminal_fixed H R).le

theorem terminal_sandwich [Fintype V] (H : SimpleGraph W) {G R : SimpleGraph V}
    (base : G ≤ R) (upper : R ≤ terminalGraph H G) : terminalGraph H R = terminalGraph H G :=
  le_antisymm (terminal_le_closed H R _ upper (terminal_fixed H G).le) (terminal_mono H base)

private theorem finite_perm_reflects [Fintype V] (G : SimpleGraph V) (p : Equiv.Perm V)
    (carry : ∀ x y, G.Adj x y → G.Adj (p x) (p y)) :
    ∀ x y, G.Adj (p x) (p y) ↔ G.Adj x y := by
  classical
  let E := {z : V × V // G.Adj z.1 z.2}
  let map (z : E) : E := ⟨(p z.val.1,p z.val.2),carry _ _ z.property⟩
  have inj : Function.Injective map := by
    intro x y e
    apply Subtype.ext
    exact Prod.ext (p.injective (congrArg (fun z : E => z.val.1) e))
      (p.injective (congrArg (fun z : E => z.val.2) e))
  have onto := Finite.surjective_of_injective inj
  intro x y
  refine ⟨?_,carry x y⟩
  intro e
  obtain ⟨z,eq⟩ := onto (⟨(p x,p y),e⟩ : E)
  have h1 : z.val.1=x := p.injective (congrArg (fun k : E => k.val.1) eq)
  have h2 : z.val.2=y := p.injective (congrArg (fun k : E => k.val.2) eq)
  simpa only [←h1,←h2] using z.property

/-- A spanning injection that puts the whole seed in its eventual closure
acts as an automorphism of that closure. -/
theorem terminal_perm [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (p : Equiv.Perm V)
    (seed : ∀ x y, G.Adj x y → (terminalGraph H G).Adj (p x) (p y)) :
    ∀ x y, (terminalGraph H G).Adj (p x) (p y) ↔ (terminalGraph H G).Adj x y := by
  apply finite_perm_reflects
  have maps (t : ℕ) : ∀ x y, (run H G t).Adj x y → (terminalGraph H G).Adj (p x) (p y) := by
    induction t with
    | zero => exact seed
    | succ t ih =>
      intro x y e
      exact (terminal_fixed H G).le (step_transport H _ _ p ih e)
  exact maps (stabilizationTime H G)

/-- Delete one edge from the source before checking the images of all others. -/
theorem self_near_perm [Fintype V] (H : SimpleGraph V) (p : Equiv.Perm V)
    {u v : V} (uv : H.Adj u v) (maps : ∀ i j, H.Adj i j →
      ¬((i=u ∧ j=v) ∨ (i=v ∧ j=u)) → H.Adj (p i) (p j)) :
    ∀ x y, (terminalGraph H H).Adj (p x) (p y) ↔ (terminalGraph H H).Adj x y := by
  classical
  have born : (step H H).Adj (p u) (p v) := Or.inr ⟨u,v,p.toEmbedding,uv,rfl,rfl,maps⟩
  have inc : step H H ≤ terminalGraph H H := (step_mono H (initial_le_terminal H H)).trans (terminal_fixed H H).le
  apply terminal_perm
  intro i j e
  by_cases exceptional : (i=u ∧ j=v) ∨ (i=v ∧ j=u)
  · rcases exceptional with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact inc born
    · exact inc ((step H H).symm born)
  · exact initial_le_terminal H H (maps i j e exceptional)

end Bootstrap

#print axioms Bootstrap.terminal_perm
#print axioms Bootstrap.self_near_perm
