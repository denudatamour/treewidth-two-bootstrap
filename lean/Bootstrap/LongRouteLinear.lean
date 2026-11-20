import Bootstrap.BicliqueCompletion
import Bootstrap.FirstHigh
import Bootstrap.NonbipLinear

namespace Bootstrap.DegreeTwo

open scoped Classical
variable {W V : Type*}

theorem bipartite_connected_clock [Fintype W] [Fintype V] (H : SimpleGraph W) [DecidableRel H.Adj]
    (G : SimpleGraph V) (conn : H.Connected) (root : W) (hostConn : G.Connected)
    (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    (long : ∃ i j, H.Adj i j ∧ H.degree i = 2 ∧ H.degree j = 2)
    (c : W → Bool) (proper : ∀ i j, H.Adj i j → c i ≠ c j) (no : ¬OneMonochrome H) :
    stabilizationTime H G ≤ ((3*Fintype.card W-1)+2*Fintype.card W+4)*Fintype.card V := by
  classical
  let n := Fintype.card V
  let h := Fintype.card W
  let J := 3*h-1
  have pos : 1 ≤ n := Fintype.card_pos_iff.mpr hostConn.nonempty
  have cap : n*J+2*h+1+n+2 ≤ (J+2*h+4)*n := by
    have factor := Nat.mul_le_mul_left (2*h+3) pos
    rw [Nat.mul_one] at factor
    rw [show J+2*h+4 = J+1+(2*h+3) by omega,Nat.add_mul,Nat.add_mul,Nat.one_mul,Nat.mul_comm J n]
    omega
  obtain ⟨t,time,which⟩ := first_high_or_fixed H G J
  change t ≤ n*J at time
  rcases which with fix|⟨x,y,old,born,dx,dy⟩
  · exact (Nat.find_min' (stable_exists H G) fix).trans ((show t ≤ n*J+2*h+1+n+2 by omega).trans cap)
  obtain ⟨f,u,v,p,_,_,_,_,apart,pl,qr,cross,_⟩ := high_birth_seed H G conn root cover long t born old dx dy
  obtain ⟨a,b,ab,da,db⟩ := long
  obtain ⟨l,rev⟩ := ((hasTwo_iff_degree H a).mpr da).other ab
  obtain ⟨r,B⟩ := ((hasTwo_iff_degree H b).mpr db).other (H.symm ab)
  let k := t+1+2*h
  let S : Biclique (W := W) (run H G k) := ⟨insert y p.left,insert x p.right,by omega,by omega,apart,cross⟩
  obtain ⟨D,span⟩ := biclique_spans H G hostConn c proper rev.reverse k n S (by dsimp [n]; omega)
  have fin := spanning_stable H G (k+n) c proper no rev.reverse B D span
  exact fin.trans ((show k+n+2 ≤ n*J+2*h+1+n+2 by dsimp [k]; omega).trans cap)

theorem bipartite_long_linear [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (conn : H.Connected) (root : W)
    (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    (long : ∃ i j, H.Adj i j ∧ H.degree i = 2 ∧ H.degree j = 2)
    (bip : ProperBoolColor H) : HasLinearUpper H := by
  classical
  by_cases mono : OneMonochrome H
  · exact linear_of_one_monochrome H conn root cover long mono
  obtain ⟨c,proper⟩ := bip
  let C := (3*Fintype.card W-1)+2*Fintype.card W+4
  refine ⟨C,0,?_⟩
  intro n _
  apply (maxTime_le_iff H n _).mpr
  intro G
  apply stable_of_components H conn c proper mono G
  intro A
  have comp := bipartite_connected_clock H (G.induce A.supp) conn root A.connected_induce_supp cover long c proper mono
  have size : Fintype.card A.supp ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding (Function.Embedding.subtype (· ∈ A.supp))
  exact comp.trans (Nat.mul_le_mul_left C size)

/-- Every order is included, including the empty host. -/
private theorem all_orders (H : SimpleGraph W) (linear : HasLinearUpper H) :
    ∃ K : ℕ, ∀ n, maxTime H n ≤ K*n := by
  obtain ⟨C,n₀,bound⟩ := linear
  refine ⟨max C n₀,?_⟩
  intro n
  by_cases large : n₀ ≤ n
  · exact (bound n large).trans (Nat.mul_le_mul_right n (le_max_left _ _))
  · exact (maxTime_le_square H n).trans (Nat.mul_le_mul_right n ((show n ≤ n₀ by omega).trans (le_max_right _ _)))

/-- The full long-route branch of Theorem II.1 in the ordinary process. -/
theorem long_rule_linear [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (conn : H.Connected)
    (cover : ∀ i j, H.Adj i j → H.degree i = 2 ∨ H.degree j = 2)
    (long : ∃ i j, H.Adj i j ∧ H.degree i = 2 ∧ H.degree j = 2) :
    ∃ K : ℕ, ∀ n, maxTime H n ≤ K*n := by
  classical
  obtain ⟨root⟩ := conn.nonempty
  apply all_orders H
  by_cases bip : ProperBoolColor H
  · exact bipartite_long_linear H conn root cover long bip
  · exact nonbip_long_linear H conn root cover long bip

end Bootstrap.DegreeTwo

#print axioms Bootstrap.DegreeTwo.bipartite_connected_clock
#print axioms Bootstrap.DegreeTwo.long_rule_linear
