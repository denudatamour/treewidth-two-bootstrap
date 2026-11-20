import Bootstrap.CliqueAbsorption
import Bootstrap.Asymptotics
import Bootstrap.SubdivisionAccounting

/-! The minimum-degree-two specialization of Section 4 (Lemma 4.1, Claim 4.2
and Theorem 1.4) of Fabian, Morris and Szabó, arXiv:2311.18786v2,
https://arxiv.org/html/2311.18786v2#S4 . -/
namespace Bootstrap.FMS

open DegreeTwo
variable {W V : Type*}

def deleted (H : SimpleGraph W) (u v : W) : SimpleGraph W where
  Adj i j := H.Adj i j ∧ ¬ ((i=u ∧ j=v) ∨ (i=v ∧ j=u))
  symm := by
    rintro i j ⟨e,remaining⟩
    refine ⟨H.symm e,?_⟩
    rintro (⟨h₁,h₂⟩|⟨h₁,h₂⟩)
    · exact remaining (Or.inr ⟨h₂,h₁⟩)
    · exact remaining (Or.inl ⟨h₂,h₁⟩)
  loopless := fun i e => H.loopless i e.1

def Near (a b : ℕ) : Prop := a+1=b ∨ b+1=a

private theorem avoid_one {a b c z : W} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    (a ≠ z ∧ b ≠ z) ∨ (a ≠ z ∧ c ≠ z) ∨ (b ≠ z ∧ c ≠ z) := by
  classical
  by_cases h : a=z
  · subst z
    exact Or.inr (Or.inr ⟨ab.symm,ac.symm⟩)
  · by_cases h' : b=z
    · subst z
      exact Or.inr (Or.inl ⟨h,bc.symm⟩)
    · exact Or.inl ⟨h,h'⟩

private theorem some_survives {H : SimpleGraph W} {u v : W} (min : HasTwoNeighbours H)
    (uv : H.Adj u v) (w : W) : ∃ j, (deleted H u v).Adj w j := by
  classical
  obtain ⟨a,b,ab,wa,wb⟩ := min w
  by_cases missing : (w=u ∧ a=v) ∨ (w=v ∧ a=u)
  · refine ⟨b,wb,?_⟩
    have ne := uv.ne
    rintro (⟨w₁,w₂⟩|⟨w₁,w₂⟩) <;> rcases missing with ⟨m₁,m₂⟩|⟨m₁,m₂⟩ <;> subst_vars <;> simp_all
  · exact ⟨a,wa,missing⟩

/-- No connected component of H minus one edge admits an injective
nearest-neighbour labelling on a path. Minimum/maximum labels must be the
two deleted ends, and a source role with three neighbours is impossible. -/
theorem component_not_path [Fintype W] {H : SimpleGraph W} [DecidableRel H.Adj]
    (conn : H.Connected) (min : HasTwoNeighbours H) (high : ∃ w, 2 < H.degree w)
    {u v : W} (uv : H.Adj u v) (s : W) (num : W → ℕ)
    (inj : ∀ i j, (deleted H u v).Reachable s i → (deleted H u v).Reachable s j →
      num i = num j → i = j)
    (edges : ∀ i j, (deleted H u v).Reachable s i → (deleted H u v).Adj i j →
      Near (num i) (num j)) : False := by
  classical
  let D := deleted H u v
  let A := Finset.univ.filter (D.Reachable s)
  have member {i : W} : i ∈ A ↔ D.Reachable s i := by simp [A]
  have live : A.Nonempty := ⟨s,member.mpr .rfl⟩
  obtain ⟨lo,hlo,minimum⟩ := A.exists_min_image num live
  obtain ⟨hi,hhi,maximum⟩ := A.exists_max_image num live
  have next {i j : W} (m : i ∈ A) (e : D.Adj i j) : j ∈ A :=
    member.mpr ((member.mp m).trans e.reachable)
  have unique_lo (i j : W) (li : D.Adj lo i) (lj : D.Adj lo j) : i=j := by
    have ai := next hlo li
    have aj := next hlo lj
    have mi := minimum i ai
    have mj := minimum j aj
    have ni := edges lo i (member.mp hlo) li
    have nj := edges lo j (member.mp hlo) lj
    exact inj i j (member.mp ai) (member.mp aj) (by rcases ni with p|p <;> rcases nj with q|q <;> omega)
  have unique_hi (i j : W) (li : D.Adj hi i) (lj : D.Adj hi j) : i=j := by
    have ai := next hhi li
    have aj := next hhi lj
    have mi := maximum i ai
    have mj := maximum j aj
    have ni := edges hi i (member.mp hhi) li
    have nj := edges hi j (member.mp hhi) lj
    exact inj i j (member.mp ai) (member.mp aj) (by rcases ni with p|p <;> rcases nj with q|q <;> omega)
  have off {w j : W} (wu : w ≠ u) (wv : w ≠ v) (e : H.Adj w j) : D.Adj w j :=
    ⟨e,fun cut => cut.elim (fun a => wu a.1) (fun b => wv b.1)⟩
  have ends (w : W) (one : ∀ i j, D.Adj w i → D.Adj w j → i=j) : w=u ∨ w=v := by
    by_cases eq : w=u
    · exact Or.inl eq
    · by_cases eq' : w=v
      · exact Or.inr eq'
      · obtain ⟨a,b,ab,ea,eb⟩ := min w
        exact False.elim (ab (one a b (off eq eq' ea) (off eq eq' eb)))
  have different : lo ≠ hi := by
    intro eq
    obtain ⟨a,ea⟩ := some_survives min uv lo
    have ma := minimum a (next hlo ea)
    have mx := maximum a (next hlo ea)
    rw [←eq] at mx
    exact ea.ne (inj lo a (member.mp hlo) (member.mp (next hlo ea)) (by omega))
  have extreme : (lo=u ∧ hi=v) ∨ (lo=v ∧ hi=u) := by
    rcases ends lo unique_lo with l | l <;> rcases ends hi unique_hi with h | h
    · exact False.elim (different (l.trans h.symm))
    · exact Or.inl ⟨l,h⟩
    · exact Or.inr ⟨l,h⟩
    · exact False.elim (different (l.trans h.symm))
  have both : u ∈ A ∧ v ∈ A := by
    rcases extreme with ⟨l,h⟩|⟨l,h⟩
    · exact ⟨l ▸ hlo,h ▸ hhi⟩
    · exact ⟨h ▸ hhi,l ▸ hlo⟩
  have inside (w : W) : w ∈ A := by
    have path := (H.reachable_iff_reflTransGen s w).mp (conn s w)
    induction path with
    | refl => exact member.mpr .rfl
    | @tail a b _ edge ih =>
      by_cases cut : (a=u ∧ b=v) ∨ (a=v ∧ b=u)
      · rcases cut with ⟨_,rfl⟩|⟨_,rfl⟩
        · exact both.2
        · exact both.1
      · exact next ih ⟨edge,cut⟩
  obtain ⟨w,deg⟩ := high
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := Finset.two_lt_card_iff.mp (show 2 < (H.neighborFinset w).card from deg)
  have wa := (H.mem_neighborFinset w a).mp ha
  have wb := (H.mem_neighborFinset w b).mp hb
  have wc := (H.mem_neighborFinset w c).mp hc
  have not_endpoint (z : W) (one : ∀ i j, D.Adj w i → D.Adj w j → i=j)
      (keep : ∀ j, j ≠ z → H.Adj w j → D.Adj w j) : False := by
    rcases avoid_one (z := z) ab ac bc with ⟨az,bz⟩|⟨az,cz⟩|⟨bz,cz⟩
    · exact ab (one a b (keep a az wa) (keep b bz wb))
    · exact ac (one a c (keep a az wa) (keep c cz wc))
    · exact bc (one b c (keep b bz wb) (keep c cz wc))
  have at_end (bound : w=u ∨ w=v) : w=lo ∨ w=hi := by
    rcases bound with e|e <;> rcases extreme with ⟨l,h⟩|⟨l,h⟩
    · exact Or.inl (e.trans l.symm)
    · exact Or.inr (e.trans h.symm)
    · exact Or.inr (e.trans h.symm)
    · exact Or.inl (e.trans l.symm)
  have one (bound : w=u ∨ w=v) (i j : W) (e : D.Adj w i) (f : D.Adj w j) : i=j := by
    rcases at_end bound with eq|eq
    · exact unique_lo i j (eq ▸ e) (eq ▸ f)
    · exact unique_hi i j (eq ▸ e) (eq ▸ f)
  by_cases wu : w=u
  · apply not_endpoint v (one (Or.inl wu))
    intro j jv e
    exact ⟨e,fun cut => cut.elim (fun p => jv p.2) (fun p => uv.ne (wu.symm.trans p.1))⟩
  by_cases wv : w=v
  · apply not_endpoint u (one (Or.inr wv))
    intro j ju e
    exact ⟨e,fun cut => cut.elim (fun p => uv.ne (p.1.symm.trans wv)) (fun p => ju p.2)⟩
  have na := edges w a (member.mp (inside w)) (off wu wv wa)
  have nb := edges w b (member.mp (inside w)) (off wu wv wb)
  have nc := edges w c (member.mp (inside w)) (off wu wv wc)
  have clash : num a=num b ∨ num a=num c ∨ num b=num c := by
    rcases na with e|e <;> rcases nb with f|f <;> rcases nc with g|g <;> omega
  rcases clash with h|h|h
  · exact ab (inj a b (member.mp (inside a)) (member.mp (inside b)) h)
  · exact ac (inj a c (member.mp (inside a)) (member.mp (inside c)) h)
  · exact bc (inj b c (member.mp (inside b)) (member.mp (inside c)) h)

end Bootstrap.FMS
#print axioms Bootstrap.FMS.component_not_path
