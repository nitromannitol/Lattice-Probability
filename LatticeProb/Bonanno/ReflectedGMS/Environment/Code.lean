/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.Code at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.AELineConnectivity
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Equiv.Option

/-! Canonically labelled countable compact environment codes.
The valid subtype has only its trace sigma algebra. In particular, this file
makes no claim that the geometric validity set is Borel. -/
set_option autoImplicit false
open MeasureTheory Set TopologicalSpace
namespace ReflectedGMS.Code

abbrev CompactCell := NonemptyCompacts Plane

/-- Hausdorff/Vietoris Borel structure on nonempty compact cells. -/
instance compactCellMeasurableSpace : MeasurableSpace CompactCell := borel CompactCell
instance compactCellBorelSpace : BorelSpace CompactCell := ⟨rfl⟩

/-- An absent label is the isolated extra point of the compact-cell sum space. -/
def slotEquiv : Option CompactCell ≃ CompactCell ⊕ PUnit.{1} :=
  Equiv.optionEquivSumPUnit CompactCell

instance slotTopologicalSpace : TopologicalSpace (Option CompactCell) :=
  TopologicalSpace.induced slotEquiv inferInstance

instance slotMeasurableSpace : MeasurableSpace (Option CompactCell) :=
  MeasurableSpace.comap slotEquiv (borel (CompactCell ⊕ PUnit.{1}))

instance slotBorelSpace : BorelSpace (Option CompactCell) := by
  constructor
  change MeasurableSpace.comap slotEquiv _ =
    @borel _ (TopologicalSpace.induced slotEquiv _)
  exact borel_comap.symm

instance slotPolishSpace : PolishSpace (Option CompactCell) :=
  slotEquiv.polishSpace_induced

/-- Countable product of optional compact cells and real conductances. -/
abbrev RawCode := (ℕ → Option CompactCell) × (ℕ → ℕ → ℝ)

/-- Fixed enumeration of every rational pair; repetition is harmless. -/
def rationalPair (n : ℕ) : ℚ × ℚ := (Encodable.decode n).getD (0, 0)

theorem rationalPair_surjective : Function.Surjective rationalPair :=
  Encodable.surjective_decode_getD (ℚ × ℚ) (0, 0)

/-- The fixed rational-plane sequence whose least interior-hit index labels each cell. -/
def rationalPoint (n : ℕ) : Plane :=
  WithLp.toLp 2 ![(rationalPair n).1, (rationalPair n).2]

theorem rationalPoint_exhausts (a b : ℚ) :
    ∃ n, rationalPoint n = WithLp.toLp 2 ![(a : ℝ), (b : ℝ)] := by
  obtain ⟨n, hn⟩ := rationalPair_surjective (a, b)
  exact ⟨n, by simp [rationalPoint, hn]⟩

/-- Actual active labels; absent slots do not become graph vertices. -/
abbrev Vertex (r : RawCode) := {n : ℕ // (r.1 n).isSome}

def cell (r : RawCode) (v : Vertex r) : CompactCell := (r.1 v.val).get v.property

/-- Membership at this index and exclusion at every smaller index. -/
def LeastInteriorLabel (K : CompactCell) (n : ℕ) : Prop :=
  rationalPoint n ∈ interior (K : Set Plane) ∧
    ∀ m : ℕ, m < n → rationalPoint m ∉ interior (K : Set Plane)

def CanonicalLabels (r : RawCode) : Prop :=
  ∀ v : Vertex r, LeastInteriorLabel (cell r v) v.val

/-- Real conductances are symmetric, nonnegative, loop-free, supported on active
labels, and have finite rows. Finite rows encode local graph finiteness and
supply the summability required by `ConductanceGraph`. -/
structure AdmissibleConductance (r : RawCode) : Prop where
  symm : ∀ n m, r.2 n m = r.2 m n
  nonneg : ∀ n m, 0 ≤ r.2 n m
  self : ∀ n, r.2 n n = 0
  absent : ∀ n m, r.1 n = none ∨ r.1 m = none → r.2 n m = 0
  finiteRow : ∀ n, (Function.support (r.2 n)).Finite

/-- Decode the actual weighted graph on the present slots. -/
noncomputable def decodeRaw (r : RawCode) (h : AdmissibleConductance r) :
    IndexedCells (Vertex r) where
  cell := cell r
  graph := {
    c := fun v w => r.2 v.val w.val
    c_symm := fun v w => h.symm v.val w.val
    c_nonneg := fun v w => h.nonneg v.val w.val
    c_self := fun v => h.self v.val
    summable_c := fun v => summable_of_hasFiniteSupport
      ((h.finiteRow v.val).preimage Subtype.val_injective.injOn) }

/-- Exact pathwise validity: admissibility, all geometry clauses, AE-LC with
all real endpoints, and least rational interior labels. -/
def Valid (r : RawCode) : Prop :=
  ∃ h : AdmissibleConductance r,
    Geometry (decodeRaw r h) ∧ AELineConnected (decodeRaw r h) ∧ CanonicalLabels r

/-- Trace-measurable valid environments; no Borel assertion about `Valid`. -/
abbrev Env := {r : RawCode // Valid r}

noncomputable def decode (e : Env) : IndexedCells (Vertex e.val) :=
  decodeRaw e.val e.property.choose

theorem decode_geometry (e : Env) : Geometry (decode e) := e.property.choose_spec.1

theorem decode_aeLineConnected (e : Env) : AELineConnected (decode e) :=
  e.property.choose_spec.2.1

theorem decode_canonicalLabels (e : Env) : CanonicalLabels e.val :=
  e.property.choose_spec.2.2

theorem measurable_inclusion : Measurable (Subtype.val : Env → RawCode) :=
  measurable_subtype_coe

end ReflectedGMS.Code
