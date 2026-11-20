import Bootstrap.MarkerMaps
import Bootstrap.RuleBooks
import Bootstrap.TypedClock
import Bootstrap.Process

/-! Projection and lifting of an omitted logical edge, and one ordinary synchronous round. -/
namespace Bootstrap.MarkedSimulation

open Localization
open TypedRound (Role)

variable {A B : Type*}

abbrev ordinaryRule : SimpleGraph (HostVertex sourceCode) :=
  Localization.rule TypedRound.rule sourceCode port

abbrev OrdinaryVertex (A B : Type*) :=
  HostVertex (@hostCode A B)

abbrev expansion (F : SimpleGraph (TypedRound.Host A B)) : SimpleGraph (OrdinaryVertex A B) :=
  Localization.host F hostCode

def Located (w : HostVertex sourceCode ↪ OrdinaryVertex A B) : Prop :=
  ∃ f : Role ↪ TypedRound.Host A B, (∀ r, hostCode (f r) = sourceCode r) ∧
    ∀ (b : Block Role) (i : Fin (blockSize sourceCode b)),
      w (.core b i) ∈ clique (blockSize hostCode) (pageCount hostCode) (blockMap f b)

private theorem expand_mono {I : Type*} (code : I → Fin 10) {F D : SimpleGraph I} (h : F ≤ D) :
    Localization.host F code ≤ Localization.host D code := by
  have hdes : designated F ≤ designated D := by
    intro a b hab
    cases a <;> cases b <;> first | exact h hab | exact hab
  intro x y he
  cases x with
  | page i a => cases y <;> exact he
  | core i a =>
    cases y with
    | page _ _ => exact he
    | core j b => exact ⟨he.1,he.2.imp_right (fun g => hdes g)⟩

private theorem matches_old {I : Type*} (F : SimpleGraph I) (code : I → Fin 10)
    {x y : HostVertex code} {i : I}
    (hx : x ∈ clique (blockSize code) (pageCount code) (.primary i))
    (hy : y ∈ clique (blockSize code) (pageCount code) (.secondary i)) :
    (Localization.host F code).Adj x y := by
  obtain ⟨a,rfl⟩ := (mem_clique _ _).mp hx
  obtain ⟨b,rfl⟩ := (mem_clique _ _).mp hy
  constructor
  · intro h
    cases h
  · exact Or.inr rfl

private theorem internal_old {I : Type*} (F : SimpleGraph I) (code : I → Fin 10)
    {x y : HostVertex code} {b : Block I} (hne : x ≠ y)
    (hx : x ∈ clique (blockSize code) (pageCount code) b)
    (hy : y ∈ clique (blockSize code) (pageCount code) b) :
    (Localization.host F code).Adj x y := by
  obtain ⟨a,rfl⟩ := (mem_clique _ _).mp hx
  obtain ⟨d,rfl⟩ := (mem_clique _ _).mp hy
  exact ⟨hne,Or.inl rfl⟩

private theorem replace_contact {I : Type*} (F : SimpleGraph I) (code : I → Fin 10)
    {z x y : HostVertex code} {b : Block I} (hne : z ≠ y)
    (hx : x ∈ clique (blockSize code) (pageCount code) b)
    (hy : y ∈ clique (blockSize code) (pageCount code) b) (h : (Localization.host F code).Adj z x) :
    (Localization.host F code).Adj z y := by
  obtain ⟨a,rfl⟩ := (mem_clique _ _).mp hx
  obtain ⟨d,rfl⟩ := (mem_clique _ _).mp hy
  cases z with
  | core _ _ => exact ⟨hne,h.2⟩
  | page _ _ => exact h

private theorem swap_omitted {S : Type*} {u v a b : S} (hm : Missing u v a b) :
    Missing v u a b := hm.elim Or.inr Or.inl

private theorem swap_test {S : Type*} {u v a b : S} (hm : Missing u v a b) :
    Missing u v b a := by
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl⟩

/-- Projection uses the injective assignment of occupied markers obtained by localization. -/
theorem project_logical (F : SimpleGraph (TypedRound.Host A B)) (u v : Role)
    (huv : TypedRound.rule.Adj u v) (w : HostVertex sourceCode ↪ OrdinaryVertex A B)
    (f : Role ↪ TypedRound.Host A B) (hh : ∀ r, hostCode (f r) = sourceCode r)
    (hc : ∀ (b : Block Role) (i : Fin (blockSize sourceCode b)),
      w (.core b i) ∈ clique (blockSize hostCode) (pageCount hostCode) (blockMap f b))
    (hr : MapsExcept ordinaryRule (expansion F) (portPoint sourceCode port u v)
      (portPoint sourceCode port v u) w) :
    TypedRound.OrdinaryTypedWitness F (f u) (f v) := by
  refine ⟨u,v,f,huv,(codes_iff_preserves f).1 hh,rfl,rfl,?_⟩
  intro a b hab hn
  have old := hr (portPoint sourceCode port a b) (portPoint sourceCode port b a)
    (Or.inl (Arc.logical a b hab)) (by
      rintro (⟨h,h'⟩|⟨h,h'⟩)
      · exact hn (Or.inl ⟨congrArg vertexRole h,congrArg vertexRole h'⟩)
      · exact hn (Or.inr ⟨congrArg vertexRole h,congrArg vertexRole h'⟩))
  exact (primary_pair_iff (f.injective.ne hab.ne) (hc _ _) (hc _ _)).1 old

/-- A typed witness for an omitted logical edge lifts to a physical injection. Both target core positions are arbitrary. -/
theorem lift_logical (F : SimpleGraph (TypedRound.Host A B)) (u v : Role)
    (huv : TypedRound.rule.Adj u v) (f : Role ↪ TypedRound.Host A B) (hf : TypedRound.Preserves f)
    (hr : ∀ a b, TypedRound.rule.Adj a b → ¬ TypedRound.Pair a b u v → F.Adj (f a) (f b))
    (x : Fin (blockSize hostCode (.primary (f u)))) (y : Fin (blockSize hostCode (.primary (f v)))) :
    Bootstrap.Witness ordinaryRule (expansion F) (.core (.primary (f u)) x) (.core (.primary (f v)) y) := by
  have eqc := (codes_iff_preserves f).2 hf
  obtain ⟨P,hx,hy⟩ := prescribe_ports f eqc huv.ne (portIdx sourceCode u (port u v))
    (portIdx sourceCode v (port v u)) x y
  let w := liftEmbedding f eqc P
  let p := portPoint sourceCode port u v
  let q := portPoint sourceCode port v u
  have oriented (a b : HostVertex sourceCode) (hab : Arc TypedRound.rule sourceCode port a b)
      (hn : ¬ Missing p q a b) : (expansion F).Adj (w a) (w b) := by
    have ne : w a ≠ w b := w.injective.ne (show ordinaryRule.Adj a b from Or.inl hab).ne
    cases hab with
    | book b a d h => exact ⟨ne,Or.inl rfl⟩
    | pageLeft b k => rfl
    | pageRight b k => rfl
    | matching r k => exact ⟨ne,Or.inr rfl⟩
    | logical a b hab =>
      have hn' : ¬ TypedRound.Pair a b u v := by
        rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
        · exact hn (Or.inl ⟨rfl,rfl⟩)
        · exact hn (Or.inr ⟨rfl,rfl⟩)
      exact ⟨ne,Or.inr (hr a b hab hn')⟩
  refine ⟨p,q,w,Or.inl (Arc.logical u v huv),hx,hy,?_⟩
  rintro a b (hab|hba) hn
  · exact oriented a b hab hn
  · exact (expansion F).symm (oriented b a hba (fun h => hn (swap_test h)))

private theorem lift_host_edges {I : Type*} {F D : SimpleGraph I} {code : I → Fin 10}
    {G : SimpleGraph (HostVertex code)} (old : Localization.host F code ≤ G)
    (new : ∀ (i j : I), D.Adj i j → ∀ a b, G.Adj (.core (.primary i) a) (.core (.primary j) b)) :
    Localization.host D code ≤ G := by
  intro x y he
  cases x with
  | page i a => cases y <;> exact old he
  | core i a =>
    cases y with
    | page _ _ => exact old he
    | core j b =>
      rcases he.2 with h|h
      · exact old ⟨he.1,Or.inl h⟩
      cases i with
      | primary i => cases j with
        | primary j => exact new i j h a b
        | secondary j => exact old ⟨he.1,Or.inr h⟩
      | secondary i => cases j <;> exact old ⟨he.1,Or.inr h⟩

/-- The reverse inclusion of the ordinary simulation needs no localization hypothesis. -/
theorem expansion_step_le (F : SimpleGraph (TypedRound.Host A B)) :
    expansion (TypedRound.step F) ≤ Bootstrap.step ordinaryRule (expansion F) := by
  apply lift_host_edges (F := F) (Bootstrap.le_step ordinaryRule (expansion F))
  intro i j hij a b
  rcases (TypedRound.step_iff_ordinary F i j).1 hij with h | ⟨u,v,f,huv,ht,rfl,rfl,hr⟩
  · exact Or.inl ⟨fun e => h.ne (Block.primary.inj (congrArg vblock e)),Or.inr h⟩
  · exact Or.inr (lift_logical F u v huv f ht hr a b)


private theorem located_of_maps {F : SimpleGraph (TypedRound.Host A B)} (hF : TriangleFree F)
    {u v : HostVertex sourceCode} {w : HostVertex sourceCode ↪ OrdinaryVertex A B}
    (hw : MapsExcept ordinaryRule (expansion F) u v w) : Located w := by
  obtain ⟨f,h⟩ := localize_rule TypedRound.rule sourceCode port hF hw
  refine ⟨f,fun r => (h r).1,?_⟩
  intro b i
  cases b with
  | primary r =>
    change w (.core (.primary r) i) ∈ clique _ _ (.primary (f r))
    rw [← (h r).2.1]
    exact Finset.mem_map.mpr ⟨_,core_mem _ _ _ _,rfl⟩
  | secondary r =>
    change w (.core (.secondary r) i) ∈ clique _ _ (.secondary (f r))
    rw [← (h r).2.2]
    exact Finset.mem_map.mpr ⟨_,core_mem _ _ _ _,rfl⟩

/-- Project an ordinary witness. Private-page, book, and matching targets are old edges. -/
theorem ordinary_step_le (F : SimpleGraph (TypedRound.Host A B)) (hF : TriangleFree F) :
    Bootstrap.step ordinaryRule (expansion F) ≤ expansion (TypedRound.step F) := by
  have mono : expansion F ≤ expansion (TypedRound.step F) :=
    expand_mono hostCode (fun _ _ old => Or.inl old)
  intro x y hxy
  rcases hxy with old|⟨u,v,w,huv,rfl,rfl,hw⟩
  · exact mono old
  obtain ⟨f,ht,hcore⟩ := located_of_maps hF (w := w) hw
  have oriented (a b : HostVertex sourceCode) (hab : Arc TypedRound.rule sourceCode port a b)
      (hr : MapsExcept ordinaryRule (expansion F) a b w) :
      (expansion (TypedRound.step F)).Adj (w a) (w b) := by
    have ne : w a ≠ w b := w.injective.ne (show ordinaryRule.Adj a b from Or.inl hab).ne
    cases hab with
    | book b a d h => exact mono (internal_old F hostCode ne (hcore _ _) (hcore _ _))
    | matching r k => exact mono (matches_old F hostCode (hcore _ _) (hcore _ _))
    | pageLeft b k =>
      have hadj := hr (.page b k) (.core b (pageHi sourceCode b k)) (Or.inl (Arc.pageRight b k))
        (by
          rintro (⟨_,he⟩|⟨he,_⟩)
          · exact (Nat.ne_of_gt (pageLo_lt_hi sourceCode b k)) (congrArg vindex he)
          · cases he)
      exact mono (replace_contact F hostCode ne (hcore _ _) (hcore _ _) hadj)
    | pageRight b k =>
      have hadj := hr (.page b k) (.core b (pageLo sourceCode b k)) (Or.inl (Arc.pageLeft b k))
        (by
          rintro (⟨_,he⟩|⟨he,_⟩)
          · exact (Nat.ne_of_lt (pageLo_lt_hi sourceCode b k)) (congrArg vindex he)
          · cases he)
      exact mono (replace_contact F hostCode ne (hcore _ _) (hcore _ _) hadj)
    | logical r s hrs =>
      have hlogical := project_logical F r s hrs w f ht hcore hr
      exact (primary_pair_iff (f.injective.ne hrs.ne) (hcore _ _) (hcore _ _)).2
        ((TypedRound.step_iff_ordinary F _ _).2 (Or.inr hlogical))
  rcases huv with hab|hba
  · exact oriented _ _ hab hw
  · exact (expansion (TypedRound.step F)).symm
      (oriented _ _ hba (fun a b ab hn => hw a b ab (fun h => hn (swap_omitted h))))

theorem ordinary_step_eq (F : SimpleGraph (TypedRound.Host A B)) (hF : TriangleFree F) :
    Bootstrap.step ordinaryRule (expansion F) = expansion (TypedRound.step F) :=
  le_antisymm (ordinary_step_le F hF) (expansion_step_le F)

/-- Lemma III.5, for every cross relation and every pair of host cycle lengths. -/
theorem exact_ordinary_round {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (E : Fin p → Fin q → Prop) :
    Bootstrap.step ordinaryRule (expansion (TypedRound.host TypedRound.nextIndex TypedRound.nextIndex E)) =
      expansion (TypedRound.host TypedRound.nextIndex TypedRound.nextIndex
        (TypedRound.grow TypedRound.nextIndex TypedRound.nextIndex E)) := by
  have hx := TypedRound.nextIndex_ne (show 2 ≤ p by omega)
  have hy := TypedRound.nextIndex_ne (show 2 ≤ q by omega)
  rw [ordinary_step_eq _ (TypedRound.triangleFree hx hy E),TypedRound.one_typed_round hp hq]

private theorem expansion_injective {I : Type*} (code : I → Fin 10) :
    Function.Injective (fun F : SimpleGraph I => Localization.host F code) := by
  intro F D h
  ext i j
  by_cases he : i = j
  · subst j; simp
  let a := hubIdx code (.primary i) 0
  let b := hubIdx code (.primary j) 0
  have ff := primary_pair_iff (F := F) he (core_mem _ _ _ a) (core_mem _ _ _ b)
  have dd := primary_pair_iff (F := D) he (core_mem _ _ _ a) (core_mem _ _ _ b)
  change Localization.host F code = Localization.host D code at h
  rw [← ff,← dd,h]

abbrev initial (p q : ℕ) : SimpleGraph (OrdinaryVertex (Fin p) (Fin q)) :=
  expansion (TypedRound.host TypedRound.nextIndex TypedRound.nextIndex (@TypedRound.origin p q))

theorem ordinary_run_eq {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (t : ℕ) :
    Bootstrap.run ordinaryRule (initial p q) t = expansion
      (TypedRound.graphRun (TypedRound.host TypedRound.nextIndex TypedRound.nextIndex
        (@TypedRound.origin p q)) t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Bootstrap.run_succ,ih]
    change Bootstrap.step _ (expansion _) = expansion (TypedRound.step _)
    apply ordinary_step_eq
    rw [TypedRound.graphRun_eq_clock hp hq]
    exact TypedRound.triangleFree (TypedRound.nextIndex_ne (by omega : 2 ≤ p))
      (TypedRound.nextIndex_ne (by omega : 2 ≤ q)) _

theorem ordinary_fixed_iff {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (t : ℕ) :
    Bootstrap.run ordinaryRule (initial p q) t = Bootstrap.run ordinaryRule (initial p q) (t+1) ↔
      p.lcm q / 2 ≤ t := by
  rw [ordinary_run_eq hp hq,ordinary_run_eq hp hq]
  exact (expansion_injective hostCode).eq_iff.trans (TypedRound.typed_fixed_iff hp hq t)

end Bootstrap.MarkedSimulation

#print axioms Bootstrap.MarkedSimulation.expansion_step_le
#print axioms Bootstrap.MarkedSimulation.ordinary_step_le
#print axioms Bootstrap.MarkedSimulation.exact_ordinary_round
#print axioms Bootstrap.MarkedSimulation.ordinary_fixed_iff
