import Bootstrap.ThetaExternalSeeds
import Bootstrap.ThetaCoordinateModulo

namespace Bootstrap.Theta

open scoped Classical

/-- A reflection followed by the allowed two-step translation fixes the coordinate 1. -/
private theorem mirror_one (m : Fin 3 → ℕ) {i j : Fin 3} (ij : i≠j)
    (two : (2*armSize m i).gcd (perimeter m i j)=2) {z : ℤ}
    (e : (thetaClosure m).Adj (intPt m i j 1) (intPt m i j z)) :
    (thetaClosure m).Adj (intPt m i j 1) (intPt m i j (2-z)) := by
  have r := (preserves_of_mem m (reflection_mem m ij false) _ _).mpr e
  rw [false_reflect_int,false_reflect_int] at r
  have dv : ((2*armSize m i).gcd (perimeter m i j):ℤ) ∣ 2 := by simp [two]
  obtain ⟨p,hp,act,_⟩ := translation_of_dvd m ij dv
  have s := (preserves_of_mem m hp _ _).mpr r
  rwa [act,act,show (-(1:ℤ))+2=1 by decide,show -z+2=2-z by omega] at s

theorem cycle_between_parities (m : Fin 3 → ℕ) {i j t : Fin 3} (ij : i≠j) (it : i≠t) (jt : j≠t)
    (order : armSize m i≤armSize m j) (two : (2*armSize m i).gcd (perimeter m i j)=2)
    (even' : perimeter m i j%2=0) (x y : Fin (perimeter m i j)) (diff : x.val%2≠y.val%2) :
    (thetaClosure m).Adj (cyclePt m i j x) (cyclePt m i j y) := by
  let a := armSize m i
  let b := armSize m j
  let n := perimeter m i j
  have len : n=a+b := rfl
  have sm (d : ℕ) (hd : d≤b) (odd : d%2=1) :
      (thetaClosure m).Adj (intPt m i j 1) (intPt m i j (1+(d:ℤ))) := by
    let e := d-1
    have es : e<armSize m j := by dsimp [e];change d≤armSize m j at hd;omega
    have dv : ((2*armSize m i).gcd (perimeter m i j):ℤ) ∣ (e:ℤ) := by
      rw [two]
      exact ⟨(e/2:ℕ),by dsimp [e];omega⟩
    have seed := seed_multiple m ij it jt es dv
    rw [←intPt_first m i j 1 (by dsimp [armSize];omega),←intPt_second m i j e es.le] at seed
    have reflected' := mirror_one m ij two seed
    have eq : 2- (-(e:ℤ))=1+(d:ℤ) := by dsimp [e];omega
    exact eq ▸ reflected'
  have all' (d : ℕ) (small : d<n) (odd : d%2=1) :
      (thetaClosure m).Adj (intPt m i j 1) (intPt m i j (1+(d:ℤ))) := by
    by_cases short : d≤b
    · exact sm d short odd
    let r := n-d
    have rodd : r%2=1 := by change n%2=0 at even'; dsimp [r];omega
    have rs : r≤b := by change a≤b at order; dsimp [r];omega
    have e := mirror_one m ij two (sm r rs rodd)
    have eq : 2-(1+(r:ℤ))+(perimeter m i j:ℤ)=1+(d:ℤ) := by
      change 2-(1+(r:ℤ))+(n:ℤ)=1+(d:ℤ)
      dsimp [r]; omega
    have rep := intPt_period m i j (2-(1+(r:ℤ)))
    rw [eq] at rep
    rw [rep]
    exact e
  have give (u v : Fin n) (ou : u.val%2=1) (ev : v.val%2=0) :
      (thetaClosure m).Adj (cyclePt m i j u) (cyclePt m i j v) := by
    let d := if u.val≤v.val then v.val-u.val else v.val+n-u.val
    have ub := u.isLt
    have vb := v.isLt
    have small : d<n := by dsimp [d];split <;>omega
    have odd : d%2=1 := by change n%2=0 at even';dsimp [d];split <;>omega
    have allowed : ((2*armSize m i).gcd (perimeter m i j):ℤ) ∣ (u.val:ℤ)-1 := by
      rw [two];exact ⟨(u.val/2:ℕ),by omega⟩
    obtain ⟨p,hp,act,_⟩ := translation_of_dvd m ij allowed
    have edge := (preserves_of_mem m hp _ _).mpr (all' d small odd)
    rw [act,act,show 1+((u.val:ℤ)-1)=u.val by omega,show 1+(d:ℤ)+((u.val:ℤ)-1)=(u.val:ℤ)+d by omega] at edge
    have dest : intPt m i j ((u.val:ℤ)+d)=intPt m i j (v.val:ℤ) := by
      by_cases before : u.val≤v.val
      · have eq : (u.val:ℤ)+d=v.val := by dsimp [d];rw [if_pos before];omega
        rw [eq]
      · have eq : (u.val:ℤ)+d=(v.val:ℤ)+(perimeter m i j:ℤ) := by
          change (u.val:ℤ)+d=(v.val:ℤ)+(n:ℤ)
          dsimp [d];rw [if_neg before];omega
        rw [eq,intPt_period]
    rw [dest] at edge
    simpa only [intPt,indexZ_val] using edge
  by_cases xo : x.val%2=1
  · exact give x y xo (by omega)
  · exact (thetaClosure m).symm (give y x (by omega) (by omega))

end Bootstrap.Theta

#print axioms Bootstrap.Theta.cycle_between_parities
