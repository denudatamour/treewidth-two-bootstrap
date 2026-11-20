import Bootstrap.ThetaExternalSeeds
import Bootstrap.ThetaSeedArithmetic

namespace Bootstrap.Theta

/-- For a primitive triple, an exterior cycle of odd perimeter supplies every seed. -/
theorem primitive_seed_mixed (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    (prim : (armSize m i).gcd ((armSize m j).gcd (armSize m t))=1)
    (opp : armSize m j%2 ≠ armSize m t%2) (z : ℤ) :
    (thetaClosure m).Adj (armPt m i 1) (intPt m j t z) := by
  obtain ⟨d,hd,div,cover⟩ := ThetaPeriodArithmetic.mixed_seed_residues
    (armSize m i) (armSize m j) (armSize m t) (by dsimp [armSize];omega) prim (by omega) z
  exact seed_grid m ij it jt hd div z cover

/-- For a primitive odd triple the external seeds give every even coordinate. -/
theorem primitive_seed_odd (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    (prim : (armSize m i).gcd ((armSize m j).gcd (armSize m t))=1)
    (_oi : armSize m i%2=1) (oj : armSize m j%2=1) (_ot : armSize m t%2=1)
    (z : ℤ) (ev : z%2=0) :
    (thetaClosure m).Adj (armPt m i 1) (intPt m j t z) := by
  obtain ⟨d,hd,div,cover⟩ := ThetaPeriodArithmetic.odd_seed_residues
    (armSize m i) (armSize m j) (armSize m t) (by dsimp [armSize];omega) prim oj z
    (show (2:ℤ)∣z from ⟨z/2,by omega⟩)
  exact seed_grid m ij it jt hd div z cover

end Bootstrap.Theta

#print axioms Bootstrap.Theta.primitive_seed_mixed
#print axioms Bootstrap.Theta.primitive_seed_odd
