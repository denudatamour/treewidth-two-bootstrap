import Bootstrap.ThetaSelfClassification
import Bootstrap.ThetaMixedIncidence
import Bootstrap.ThetaOppositeSlot

namespace Bootstrap.Theta

/-- For every arithmetic scale, the ordinary self-process fills the required
junction--port incidences in its monochrome or two-colour segment graph. -/
theorem scaled_segment_inclusion : ScaledSegmentInclusion := by
  classical
  intro r d hd pos prim _
  by_cases odd : ∀i,r i%2=1
  · simpa [odd] using Corridor.colored_segment_lower r hd pos prim odd
  · have mix : ∃i j,r i%2≠r j%2 := by
      by_contra! same
      have one : r 0%2=1 := by
        by_contra bad
        have div (i : Fin 3) : 2∣r i := by have := same i 0;omega
        have impossible : 2∣lengthGcd r := Nat.dvd_gcd (div 0) (Nat.dvd_gcd (div 1) (div 2))
        rw [prim] at impossible
        omega
      exact odd (fun i => (same i 0).trans one)
    simpa [odd] using Corridor.mixed_lower_of_middle r hd pos prim mix (Corridor.opposite_slot_swap r hd pos mix)

/-- Self-closure of the ordinary three-arm theta itself for all arm lengths
at least two, including the identification of the shortest equal-arm rule. -/
theorem self_closure_classification (a b c : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    let L := threeLengths a b c
    let G := rule L
    (¬HasBipartition G → terminalGraph G G=⊤) ∧
    (HasBipartition G → ¬(a=b ∧ b=c) → terminalGraph G G=completeBetween (naturalColor (fun i => L i-2) a)) ∧
    (a=b ∧ b=c → terminalGraph G G=G) ∧
    (a=2 → b=2 → c=2 → Nonempty (G ≃g completeBipartiteGraph Bool (Fin 3))) :=
  self_classification_of_scaled scaled_segment_inclusion a b c ha hb hc

end Bootstrap.Theta

#print axioms Bootstrap.Theta.scaled_segment_inclusion
#print axioms Bootstrap.Theta.self_closure_classification
