import Bootstrap.Localization
import Bootstrap.TypedRound
import Mathlib.GroupTheory.Perm.Basic

/-! The numerical types and least-neighbour ports, and bijections of complete markers. -/
namespace Bootstrap.MarkedSimulation

open Localization
open TypedRound (Kind LocalRole Role)

def kindId : Kind ⊕ Kind → Fin 10
  | .inl .endpoint => 0
  | .inr .endpoint => 1
  | .inl (.u false) => 2
  | .inl (.v false) => 3
  | .inl (.u true) => 4
  | .inl (.v true) => 5
  | .inr (.u false) => 6
  | .inr (.v false) => 7
  | .inr (.u true) => 8
  | .inr (.v true) => 9

theorem kindId_injective : Function.Injective kindId := by decide

def sourceCode (r : Role) : Fin 10 := kindId (TypedRound.roleType r)
def hostCode {A B : Type*} (v : TypedRound.Host A B) : Fin 10 := kindId (TypedRound.hostType v)

theorem codes_iff_preserves {A B : Type*} (f : Role → TypedRound.Host A B) :
    (∀ r, hostCode (f r) = sourceCode r) ↔ TypedRound.Preserves f :=
  ⟨fun h r => kindId_injective (h r),fun h r => congrArg kindId (h r)⟩

def roleOrdinal : Role → Fin 12
  | .inl (.endpoint false) => 0
  | .inl (.endpoint true) => 1
  | .inr (.endpoint false) => 2
  | .inr (.endpoint true) => 3
  | .inl (.u false) => 4
  | .inl (.v false) => 5
  | .inl (.u true) => 6
  | .inl (.v true) => 7
  | .inr (.u false) => 8
  | .inr (.v false) => 9
  | .inr (.u true) => 10
  | .inr (.v true) => 11

def selected : Role → Role
  | .inl (.endpoint b) => .inr (.endpoint b)
  | .inr (.endpoint b) => .inl (.endpoint b)
  | .inl (.u _) => .inl (.endpoint false)
  | .inl (.v _) => .inl (.endpoint true)
  | .inr (.u _) => .inr (.endpoint false)
  | .inr (.v _) => .inr (.endpoint true)

private instance (x y : Role) : Decidable (TypedRound.rule.Adj x y) :=
  inferInstanceAs (Decidable (∃ e : TypedRound.Edge,
    TypedRound.Pair x y e.fromRole e.toRole))

theorem selected_least : ∀ r : Role, TypedRound.rule.Adj r (selected r) ∧
    ∀ s : Role, TypedRound.rule.Adj r s → roleOrdinal (selected r) ≤ roleOrdinal s := by
  decide

def port (r s : Role) : Fin 2 := if s = selected r then 0 else 1

variable {R I : Type*}

def blockMap (f : R → I) : Block R → Block I
  | .primary r => .primary (f r)
  | .secondary r => .secondary (f r)

theorem blockMap_injective {f : R → I} (hi : Function.Injective f) :
    Function.Injective (blockMap f) := by
  intro r s h
  cases r with
  | primary r => cases s with
    | primary s => exact congrArg Block.primary (hi (Block.primary.inj h))
    | secondary _ => cases h
  | secondary r => cases s with
    | primary _ => cases h
    | secondary s => exact congrArg Block.secondary (hi (Block.secondary.inj h))

def vblock {S T : I → ℕ} : Vertex S T → I
  | .core b _ => b
  | .page b _ => b

def vindex {S T : I → ℕ} : Vertex S T → ℕ
  | .core _ a => a.val
  | .page _ a => a.val

def blockRole : Block R → R
  | .primary r => r
  | .secondary r => r

def vertexRole {code : R → Fin 10} (x : HostVertex code) : R := blockRole (vblock x)

theorem block_size_eq {sc : R → Fin 10} {hc : I → Fin 10}
    {f : R → I} (eqc : ∀ r, hc (f r) = sc r) (b : Block R) :
    blockSize sc b = blockSize hc (blockMap f b) := by
  cases b <;> simp [blockSize,blockMap,eqc]

theorem page_count_eq {sc : R → Fin 10} {hc : I → Fin 10}
    {f : R → I} (eqc : ∀ r, hc (f r) = sc r) (b : Block R) :
    pageCount sc b = pageCount hc (blockMap f b) := by
  simp only [pageCount,block_size_eq eqc]

abbrev CorePerm {R : Type*} (sc : R → Fin 10) :=
  (b : Block R) → Equiv.Perm (Fin (blockSize sc b))

def place {sc : R → Fin 10} {hc : I → Fin 10} {f : R → I}
    (eqc : ∀ r, hc (f r) = sc r) (P : CorePerm sc) : HostVertex sc → HostVertex hc
  | .core b a => .core (blockMap f b) (Fin.cast (block_size_eq eqc b) (P b a))
  | .page b a => .page (blockMap f b) (Fin.cast (page_count_eq eqc b) a)

theorem place_injective {sc : R → Fin 10} {hc : I → Fin 10} {f : R → I}
    (hf : Function.Injective f) (eqc : ∀ r, hc (f r) = sc r) (P : CorePerm sc) :
    Function.Injective (place eqc P) := by
  intro x y h
  have hb := blockMap_injective hf
  cases x with
  | core b a => cases y with
    | core c z =>
      have ht : b = c := hb (congrArg vblock h)
      subst c
      have hv : (P b a).val = (P b z).val := congrArg vindex h
      exact congrArg (Vertex.core b) ((P b).injective (Fin.ext hv))
    | page _ _ => cases h
  | page b a => cases y with
    | core _ _ => cases h
    | page c z =>
      have ht : b = c := hb (congrArg vblock h)
      subst c
      have hv : a.val = z.val := congrArg vindex h
      exact congrArg (Vertex.page b) (Fin.ext hv)

def liftEmbedding {sc : R → Fin 10} {hc : I → Fin 10} (f : R ↪ I)
    (eqc : ∀ r, hc (f r) = sc r) (P : CorePerm sc) : HostVertex sc ↪ HostVertex hc :=
  ⟨place eqc P,place_injective f.injective eqc P⟩

/-- Both incidences can be sent to arbitrary prescribed core vertices. -/
theorem prescribe_ports {sc : R → Fin 10} {hc : I → Fin 10}
    (f : R ↪ I) (eqc : ∀ r, hc (f r) = sc r) {u v : R} (hne : u ≠ v)
    (a : Fin (blockSize sc (.primary u))) (b : Fin (blockSize sc (.primary v)))
    (x : Fin (blockSize hc (.primary (f u)))) (y : Fin (blockSize hc (.primary (f v)))) :
    ∃ P : CorePerm sc,
      liftEmbedding f eqc P (.core (.primary u) a) = .core (.primary (f u)) x ∧
      liftEmbedding f eqc P (.core (.primary v) b) = .core (.primary (f v)) y := by
  classical
  have huv : (Block.primary u : Block R) ≠ .primary v := fun h => hne (Block.primary.inj h)
  let P₀ : CorePerm sc := fun _ => Equiv.refl _
  let swapU := Equiv.swap a (Fin.cast (block_size_eq eqc (.primary u)).symm x)
  let swapV := Equiv.swap b (Fin.cast (block_size_eq eqc (.primary v)).symm y)
  let P := Function.update (Function.update P₀ (.primary u) swapU) (.primary v) swapV
  refine ⟨P,?_,?_⟩
  · change Vertex.core _ (Fin.cast _ (P (.primary u) a)) = Vertex.core _ x
    apply congrArg (Vertex.core _)
    simp [P,Function.update_of_ne huv,swapU]
  · change Vertex.core _ (Fin.cast _ (P (.primary v) b)) = Vertex.core _ y
    apply congrArg (Vertex.core _)
    simp [P,swapV]

theorem primary_pair_iff {F : SimpleGraph I} {code : I → Fin 10} {i j : I}
    (hij : i ≠ j) {x y : HostVertex code}
    (hx : x ∈ clique (blockSize code) (pageCount code) (.primary i))
    (hy : y ∈ clique (blockSize code) (pageCount code) (.primary j)) :
    (host F code).Adj x y ↔ F.Adj i j := by
  obtain ⟨a,rfl⟩ := (mem_clique _ _).mp hx
  obtain ⟨b,rfl⟩ := (mem_clique _ _).mp hy
  have hb : (Block.primary i : Block I) ≠ .primary j := fun h => hij (Block.primary.inj h)
  constructor
  · intro h
    exact h.2.resolve_left hb
  · intro h
    exact ⟨fun z => hb (congrArg vblock z),Or.inr h⟩

end Bootstrap.MarkedSimulation
