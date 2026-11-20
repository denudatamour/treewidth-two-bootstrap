import Bootstrap.PrimitiveThetaGeometry
import Bootstrap.PrimitiveParameters
import Bootstrap.ThetaColourBalance

namespace Bootstrap.Theta.Contraction

open scoped Classical

/-- The concrete two-arm rotations and left-pole reflections available in a permutation group. -/
structure Motions (m : Fin 3 → Nat) (Γ : Subgroup (Equiv.Perm (Vertex m))) : Prop where
  translate : ∀ i j, i ≠ j → ∀ d : Nat, (2*armSize m i).gcd (perimeter m i j) ∣ d →
    ∃ p ∈ Γ, (∀ z : Int, p (intPt m i j z) = intPt m i j (z+d)) ∧
      ∀ w, ¬OnCycle i j w → p w = w
  negate : ∀ i j, i ≠ j → ∃ p ∈ Γ, ∀ z : Int, p (intPt m i j z) = intPt m i j (-z)

def Respects {V : Type*} (Γ : Subgroup (Equiv.Perm V)) (Q : SimpleGraph V) : Prop :=
  ∀ p ∈ Γ, ∀ x y, Q.Adj (p x) (p y) ↔ Q.Adj x y

private theorem chart_empty (m : Fin 3 → Nat) {a b c : Fin 3}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (Q : SimpleGraph (Vertex m))
    {Γ : Subgroup (Equiv.Perm (Vertex m))} (M : Motions m Γ) (inv : Respects Γ Q)
    (s t f ρ : Nat) (P : Parameters (armSize m a) (armSize m b) (armSize m c) s t f)
    (reg : ∀ x, Q.degree x = ρ) (thin : Thin Q (natPoint m a c) (perimeter m a c) s f)
    (seed : ∀ n, n < perimeter m b c → ¬Q.Adj (armPt m a 1) (natPoint m b c n)) : Q = ⊥ := by
  classical
  let p := natPoint m a c
  let A := armSize m a
  let L := perimeter m a c
  have wrap : A+s ≤ L := Nat.add_le_add_left P.room _
  obtain ⟨K,hK,hA⟩ := P.last
  obtain ⟨σ,hσ,sh,_⟩ := M.translate a c ac s P.inside_rotation
  let S : Q ≃g Q := ⟨σ,fun {x y} => inv σ hσ x y⟩
  have stepS (u : Nat) (_ : u+s < L) : S (p u) = p (u+s) := by
    simpa only [p,natPoint,Nat.cast_add] using sh (u:Int)
  obtain ⟨β,hβ,move,fix⟩ := M.translate b c bc t P.outside_rotation
  let B : Q ≃g Q := ⟨β,fun {x y} => inv β hβ x y⟩
  have orbit := outside_rotation m ab ac bc Q f t P.positive P.outside B move fix
  have start (w : Vertex m) (hw : Q.Adj (p 1) w) : w ∈ strip p 1 A := by
    by_contra neg
    have on' : OnCycle b c w := by
      by_contra h
      exact neg ((strip_off m ab ac bc w).mpr h)
    let z := vertexCoord m b c w
    have eq : natPoint m b c z.val = w := by
      rw [natPoint,intPt,indexZ_val]
      exact pt_coord m bc w on'
    have fst : p 1=armPt m a 1 := intPt_first m a c 1 (by simp [armSize])
    exact seed z.val z.isLt (by rw [←fst,eq];exact hw)
  have cut := closed_of_seed Q p L A s f K ρ P.small hA wrap (chart_inj m ac) S stepS reg thin orbit start
  refine empty_of_closed Q p L A s f K ρ P.small hK hA wrap (chart_inj m ac) S stepS ?_ reg cut
  rcases thin with h | ⟨twice,_⟩
  · exact Or.inl h
  · obtain ⟨η,hη,flip⟩ := M.negate a c ac
    let E : Q ≃g Q := ⟨η,fun {x y} => inv η hη x y⟩
    refine Or.inr ⟨twice,E.trans S,?_⟩
    intro u us
    change σ (η (intPt m a c (u:Int))) = intPt m a c ((s-u : Nat):Int)
    rw [flip,sh]
    congr 1
    omega

private theorem two_color_transport {V : Type*} (G : SimpleGraph V) (conn : G.Connected)
    (c d : V → Bool) (pc : ∀ x y, G.Adj x y → c x ≠ c y)
    (pd : ∀ x y, G.Adj x y → d x ≠ d y) (x y : V) : c x = c y ↔ d x = d y := by
  have keep (i j : V) (ij : G.Adj i j) : c i = d i ↔ c j = d j := by
    have K : ∀ a b c d : Bool, a ≠ c → b ≠ d → (a=b ↔ c=d) := by decide
    exact K _ _ _ _ (pc i j ij) (pd i j ij)
  obtain ⟨path⟩ := conn x y
  have endeq : c x = d x ↔ c y = d y := by
    induction path with
    | nil => rfl
    | cons e _ ih => exact (keep _ _ e).trans ih
  have K : ∀ a b c d : Bool, (a=b ↔ c=d) → (a=c ↔ b=d) := by decide
  exact K _ _ _ _ endeq

/-- The mixed primitive branch without a coprime pair. The only geometric inputs
outside this module are the actual reflection motions, vertex transitivity and the seed. -/
theorem mixed_from_seed (m : Fin 3 → Nat) {a b c : Fin 3}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (Γ : Subgroup (Equiv.Perm (Vertex m)))
    (M : Motions m Γ) (F : SimpleGraph (Vertex m)) (inv : Respects Γ F)
    (trans : ∀ x y : Vertex m, ∃ p ∈ Γ, p x = y)
    (prim : ((armSize m a).gcd (armSize m b)).gcd (armSize m c) = 1)
    (notAB : 1 < (armSize m a).gcd (armSize m b)) (notAC : 1 < (armSize m a).gcd (armSize m c))
    (pa : armSize m a % 2 ≠ armSize m c % 2) (pb : armSize m b % 2 ≠ armSize m c % 2)
    (seed : ∀ z : Int, F.Adj (armPt m a 1) (intPt m b c z)) : F = ⊤ := by
  classical
  let Q := Fᶜ
  letI : DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _
  have qi : Respects Γ Q := by
    intro p hp x y
    change Fᶜ.Adj (p x) (p y) ↔ Fᶜ.Adj x y
    rw [F.compl_adj,F.compl_adj]
    exact and_congr (not_congr p.injective.eq_iff) (not_congr (inv p hp x y))
  let u := pole m false
  have reg (x) : Q.degree x = Q.degree u := by
    obtain ⟨p,hp,hu⟩ := trans u x
    exact hu ▸ transported_degree Q p (qi p hp) u
  have P := mixed_parameters _ _ _ (by simp [armSize]) (by simp [armSize]) (by simp [armSize])
    prim notAB notAC pa pb
  have empty := chart_empty m ab ac bc Q M qi _ _ _ _ P reg (Or.inl rfl)
    (fun z _ e => ((F.compl_adj _ _).mp e).2 (seed z))
  apply top_unique
  intro x y e
  by_contra bad
  have miss : Q.Adj x y := (F.compl_adj x y).mpr ⟨e.ne,bad⟩
  rw [empty] at miss
  exact miss

/-- The all-odd primitive branch without a coprime pair. Equal natural sides and
transitivity within each colour give the regularity required by the contraction. -/
theorem odd_from_seed (m : Fin 3 → Nat) {a b c : Fin 3}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (Γ : Subgroup (Equiv.Perm (Vertex m)))
    (M : Motions m Γ) (F : SimpleGraph (Vertex m)) (inv : Respects Γ F)
    (base : graph m ≤ F) (upper : F ≤ completeBetween (naturalColor m 1))
    (trans : ∀ x y : Vertex m, naturalColor m 1 x = naturalColor m 1 y → ∃ p ∈ Γ, p x = y)
    (prim : ((armSize m a).gcd (armSize m b)).gcd (armSize m c) = 1)
    (notAB : 1 < (armSize m a).gcd (armSize m b)) (notAC : 1 < (armSize m a).gcd (armSize m c))
    (notBC : 1 < (armSize m b).gcd (armSize m c)) (order : armSize m c < armSize m b)
    (odd : ∀ i, armSize m i % 2 = 1)
    (seed : ∀ z : Int, z%2=0 → F.Adj (armPt m a 1) (intPt m b c z)) :
    F = completeBetween (naturalColor m 1) := by
  classical
  let d := naturalColor m 1
  let Q := missingBetween d F
  have cross (x y) (h : Q.Adj x y) : d x ≠ d y := h.1
  have qi : Respects Γ Q := by
    intro p hp x y
    have eqv := two_color_transport (graph m) (connected m (by decide)) d (fun z => d (p z))
      (fun _ _ e => upper (base e)) (fun u v e => upper ((inv p hp u v).mpr (base e))) x y
    exact and_congr (not_congr eqv.symm) (not_congr (inv p hp x y))
  let u := pole m false
  have reg := uniform_degree Q d u (pole m true) rfl rfl (odd_sides_equal m odd) cross (by
    intro x y eq
    obtain ⟨p,hp,px⟩ := trans x y eq
    exact (px ▸ transported_degree Q p (qi p hp) x).symm)
  have P := odd_parameters _ _ _ (by simp [armSize]) (by simp [armSize]) (by simp [armSize])
    order prim notAB notAC notBC (odd a)
  have empty := chart_empty m ab ac bc Q M qi _ _ _ _ P reg (odd_thin m a c odd Q cross _) (by
    intro n hn e
    have xcol : d (armPt m a 1) = true := by
      rw [show 1 = (0 : Fin (m a+1)).val+1 from rfl,armPt_inner]
      rfl
    have dxy := cross _ _ e
    rw [xcol] at dxy
    change true ≠ naturalColor m 1 (natPoint m b c n) at dxy
    rw [color_natPoint m b c odd n hn] at dxy
    have e0 : n%2=0 := by
      by_contra bad
      have : n%2=1 := by omega
      simp [this] at dxy
    exact e.2 (seed n (by exact_mod_cast e0)))
  apply le_antisymm upper
  intro x y e
  by_contra bad
  have miss : Q.Adj x y := ⟨e,bad⟩
  rw [empty] at miss
  exact miss

end Bootstrap.Theta.Contraction

#print axioms Bootstrap.Theta.Contraction.mixed_from_seed
#print axioms Bootstrap.Theta.Contraction.odd_from_seed
