import Bootstrap.TerminalSymmetry
import Bootstrap.ThetaConnectivity
import Bootstrap.BipartiteComponents

namespace Bootstrap

variable {W V : Type*}

/-- For any two-connected finite ordinary graph, deleting any single edge
preserves connectedness. Neighbours other than the far end reconnect the
one excluded vertex to the connected vertex-deleted graph. -/
theorem connected_delete_of_twoConnected [Fintype W] {H : SimpleGraph W}
    (conn : Suppression.TwoConnected H) (u v : W) :
    (H.deleteEdges {s(u,v)}).Connected := by
  classical
  let J := H.deleteEdges {s(u,v)}
  let A := H.induce {x | x ≠ u}
  let hom : A →g J :=
    { toFun := Subtype.val
      map_rel' := by
        intro i j edge
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨edge,?_⟩
        intro hit
        rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hit) with h|h
        · exact i.property h.1
        · exact j.property h.2 }
  obtain ⟨a,b,ua,ub,distinct⟩ := Suppression.two_neighbors conn u
  obtain ⟨w,uw,wv⟩ : ∃ w, H.Adj u w ∧ w ≠ v := by
    by_cases eq : a=v
    · exact ⟨b,ub,fun bv => distinct (eq.trans bv.symm)⟩
    · exact ⟨a,ua,eq⟩
  have first : J.Adj u w := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨uw,?_⟩
    intro hit
    rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hit) with h|h
    · exact wv h.2
    · exact uw.ne h.2.symm
  apply J.connected_iff_exists_forall_reachable.mpr
  refine ⟨u,fun z => ?_⟩
  by_cases zu : z = u
  · subst z
    exact .refl _
  · exact first.reachable.trans ((conn.delete u ⟨w,uw.ne.symm⟩ ⟨z,zu⟩).map hom)

namespace Theta

variable {k : ℕ}

theorem edge_deleted_connected (m : Fin k → ℕ) (hk : 2 ≤ k) (u v : Vertex m) :
    ((graph m).deleteEdges {s(u,v)}).Connected :=
  connected_delete_of_twoConnected (twoConnected m hk) u v

/-- The left pole is at distance zero, the right pole has the common arm
parity, and the j-th private vertex is at position j+1 on its arm. -/
def naturalColor (m : Fin k → ℕ) (par : ℕ) : Vertex m → Bool
  | .inl false => false
  | .inl true => decide (par%2=1)
  | .inr ⟨_,j⟩ => decide ((j.val+1)%2=1)

def completeBetween (colour : V → Bool) : SimpleGraph V where
  Adj x y := colour x ≠ colour y
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h rfl

private theorem pole_inner_colour (m : Fin k → ℕ) (par : ℕ) (same : ∀ i, (m i+2)%2=par%2)
    (b : Bool) (i : Fin k) (j : Fin (m i+1))
    (e : (graph m).Adj (pole m b) (inner m i j)) :
    naturalColor m par (pole m b) ≠ naturalColor m par (inner m i j) := by
  cases b with
  | false =>
    change j.val = 0 at e
    simp [naturalColor,pole,inner,e]
  | true =>
    change j.val = m i at e
    intro eq
    have congr := decide_eq_decide.mp eq
    have hi := same i
    omega

theorem natural_proper (m : Fin k → ℕ) (par : ℕ) (same : ∀ i, (m i+2)%2=par%2) :
    graph m ≤ completeBetween (naturalColor m par) := by
  rintro (b|⟨i,j⟩) (c|⟨s,t⟩) edge
  · exact False.elim edge
  · exact pole_inner_colour m par same b s t edge
  · exact (pole_inner_colour m par same c i j ((graph m).symm edge)).symm
  · obtain ⟨rfl,h|h⟩ := edge <;> intro eq <;>
      have eq' := decide_eq_decide.mp eq <;> omega

end Theta

private theorem equal_flip {a b c d : Bool} (ab : a ≠ b) (cd : c ≠ d) :
    (a != c) = (b != d) := by cases a <;> cases b <;> cases c <;> cases d <;> simp_all

private theorem force_flip {a b c d : Bool} (ab : a ≠ b) (eq : (a != c) = (b != d)) :
    c ≠ d := by cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- On a connected edge-deleted rule a proper two-colouring is unique up
to a simultaneous flip. Hence the rule cannot have a colouring with exactly
one monochromatic edge. -/
theorem no_monochrome_of_connected_deletions (H : SimpleGraph W) (c : W → Bool)
    (proper : ∀ i j, H.Adj i j → c i ≠ c j)
    (connected : ∀ u v, H.Adj u v → (H.deleteEdges {s(u,v)}).Connected) :
    ¬ DegreeTwo.OneMonochrome H := by
  rintro ⟨d,u,v,uv,mono,only⟩
  let J := H.deleteEdges {s(u,v)}
  have localEq (x y : W) (e : J.Adj x y) : (c x != d x) = (c y != d y) := by
    obtain ⟨inH,miss⟩ := SimpleGraph.deleteEdges_adj.mp e
    apply equal_flip (proper _ _ inH)
    intro eq
    exact miss (Set.mem_singleton_iff.mpr (Sym2.eq_iff.mpr (only _ _ inH eq)))
  have reach := (J.reachable_iff_reflTransGen u v).mp (connected u v uv u v)
  have fixed {z : W} (h : Relation.ReflTransGen J.Adj u z) : (c u != d u) = (c z != d z) := by
    induction h with
    | refl => rfl
    | tail _ edge ih => exact ih.trans (localEq _ _ edge)
  exact (force_flip (proper _ _ uv) (fixed reach)) mono

namespace Theta

variable {k : ℕ}

theorem run_le_natural (m : Fin k → ℕ) (hk : 2 ≤ k) (par : ℕ)
    (same : ∀ i, (m i+2)%2=par%2) (t : ℕ) :
    run (graph m) (graph m) t ≤ completeBetween (naturalColor m par) := by
  have colour := natural_proper m par same
  have no := no_monochrome_of_connected_deletions (graph m) (naturalColor m par)
    (fun _ _ edge => colour edge) (fun u v _ => edge_deleted_connected m hk u v)
  induction t with
  | zero => exact colour
  | succ t ih =>
    exact fun {x y} e => DegreeTwo.proper_step (graph m) no _ (naturalColor m par)
      (fun _ _ edge => ih edge) x y e

/-- The self-closure of every same-parity multiple-arm graph lies in its
natural complete bipartite graph. Covers both even and odd common parity. -/
theorem terminal_le_natural (m : Fin k → ℕ) (hk : 2 ≤ k) (par : ℕ)
    (same : ∀ i, (m i+2)%2=par%2) :
    terminalGraph (graph m) (graph m) ≤ completeBetween (naturalColor m par) :=
  run_le_natural m hk par same _

theorem rule_terminal_le_natural (lengths : Fin k → ℕ) (hk : 2 ≤ k)
    (hl : ∀ i, 2 ≤ lengths i) (par : ℕ) (same : ∀ i, (lengths i)%2=par%2) :
    terminalGraph (rule lengths) (rule lengths) ≤
      completeBetween (naturalColor (fun i => lengths i-2) par) :=
  terminal_le_natural _ hk par (fun i => (congrArg (fun n : ℕ => n%2)
    (arm_length lengths hl i)).trans (same i))

end Theta
end Bootstrap

#print axioms Bootstrap.Theta.edge_deleted_connected
#print axioms Bootstrap.Theta.run_le_natural

#print axioms Bootstrap.Theta.terminal_le_natural
#print axioms Bootstrap.Theta.rule_terminal_le_natural
