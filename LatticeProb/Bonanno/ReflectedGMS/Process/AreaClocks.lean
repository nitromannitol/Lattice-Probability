/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.AreaClocks at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.StatementIngredients
import LatticeProb.Bonanno.ReflectedWalk.Existence

/-! Both area-clock paths use the repository's actual reflected construction.
No new random-walk, clock-summing, or coupled-chain implementation is introduced.
Infinite lifetime, recurrence and homeomorphic time-change are conclusions to
be proved; the definitions do not assume these conclusions. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
namespace ReflectedGMS.AreaClocks
open ReflectedWalk

variable {V : Type*}

/-- The desired vertex exit rate; area and total conductance are reused. -/
noncomputable def areaRate (F : IndexedCells V) (v : V) : ℝ :=
  F.graph.pi v / StatementIngredients.cellArea F v

noncomputable def areaHoldingLength (F : IndexedCells V) (v : V) : ℝ :=
  StatementIngredients.cellArea F v / F.graph.pi v

/-- Preserve every coupled discrete chain and replace unit exponential lengths
by 1. Feeding this sample into the same constructed path gives exact holdings. -/
def exactHoldingSample (ω : Existence.Sample V) : Existence.Sample V :=
  (ω.1, fun _ => 1)

/-- The canonical constructed exponential-area-clock path. -/
noncomputable def exponentialAreaPath (F : IndexedCells V) (D : F.graph.Exhaustion)
    (t : ℝ≥0) (ω : Existence.Sample V) : Option V :=
  Existence.process D (areaRate F) t ω

/-- The exact-holding version on the same ordered coupled-chain realization. -/
noncomputable def exactAreaPath (F : IndexedCells V) (D : F.graph.Exhaustion)
    (t : ℝ≥0) (ω : Existence.Sample V) : Option V :=
  Existence.process D (areaRate F) t (exactHoldingSample ω)

/-- Homeomorphic time change on the entire half-line, with the order retained.
The same sample appears on both sides, so this is a pathwise statement. -/
def IsHomeomorphicTimeChange (X Y : ℝ≥0 → Option V) : Prop :=
  ∃ h : ℝ≥0 ≃ₜ ℝ≥0, StrictMono h ∧ h 0 = 0 ∧ ∀ t, X t = Y (h t)

/-- Reuses the existing reflected recurrence property for every vertex.
Its quantifiers are under each fixed starting law in the final theorem. -/
def ReturnsToEveryVertex {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → Option V) : Prop :=
  ∀ᵐ ω ∂P, ∀ v : V, ∀ T : ℝ≥0, ∃ t, T ≤ t ∧ X t ω = some v

section Measurability
variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

 theorem measurable_exactHoldingSample :
    Measurable (exactHoldingSample (V := V)) :=
  measurable_fst.prodMk measurable_const

 theorem measurable_exponentialAreaPath (F : IndexedCells V)
    (D : F.graph.Exhaustion) (t : ℝ≥0) : Measurable (exponentialAreaPath F D t) :=
  Existence.measurable_process D (areaRate F) t

 theorem measurable_exactAreaPath (F : IndexedCells V)
    (D : F.graph.Exhaustion) (t : ℝ≥0) : Measurable (exactAreaPath F D t) :=
  (Existence.measurable_process D (areaRate F) t).comp measurable_exactHoldingSample
end Measurability

section CanonicalLaw
variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] [Nontrivial V]

/-- The same actual sample law for both clocks; the sample's coupled chains
and unit exponential variables are those already constructed in ReflectedWalk. -/
noncomputable abbrev areaSampleLaw (F : IndexedCells V) (D : F.graph.Exhaustion)
    (hG : F.graph.toSimpleGraph.Connected) (start : V) :=
  Existence.sampleLaw D hG start

/-- The existing admissible fast-clock construction on the same sample. -/
noncomputable def canonicalFastPath (F : IndexedCells V) (D : F.graph.Exhaustion)
    (hG : F.graph.toSimpleGraph.Connected) : ℝ≥0 → Existence.Sample V → Option V :=
  Existence.process D (D.rateFunction hG)

end CanonicalLaw
end ReflectedGMS.AreaClocks
