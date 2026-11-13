/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.MartingaleIngredients at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.StatementIngredients
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Cadlag

/-!
Minimal process-statement adapters over mathlib's filtration, stopping-time,
localization, martingale, predictability and bounded-variation definitions.
These are conclusion predicates. They do not construct the reflected process,
its full-form realization or a martingale decomposition.
-/
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ReflectedGMS.MartingaleIngredients

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An adapted process localized by mathlib stopping times tending to infinity.
The local property is the existing conditional-expectation martingale predicate. -/
def IsLocalMartingale (P : Measure Ω) (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M : ℝ≥0 → Ω → E) : Prop :=
  StronglyAdapted F M ∧ Locally (fun N => Martingale N F P) F M P

/-- One common localizing sequence makes the stopped process a martingale and
square integrable at every time; no new conditional-expectation API is used. -/
def IsLocallySquareIntegrableMartingale (P : Measure Ω)
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → E) : Prop :=
  StronglyAdapted F M ∧
    Locally (fun N => Martingale N F P ∧ ∀ t, MemLp (N t) 2 P) F M P

theorem IsLocallySquareIntegrableMartingale.isLocalMartingale
    {P : Measure Ω} {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {M : ℝ≥0 → Ω → E} (hM : IsLocallySquareIntegrableMartingale P F M) :
    IsLocalMartingale P F M :=
  ⟨hM.1, hM.2.mono (fun _ h => h.1)⟩

/-- The actual continuous predictable finite-variation covariation criterion:
`M*N-A` is a local martingale and `A` starts at zero. Predictability is
mathlib's measurability for the predictable sigma algebra, not an uninterpreted
label. Local square integrability of the coordinates is imposed by the full
ordinary-edge bracket predicate below. -/
def IsContinuousPredictableCovariation (P : Measure Ω)
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M N A : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyPredictable F A ∧
  (∀ᵐ ω ∂P, A 0 ω = 0 ∧ Continuous (fun t => A t ω) ∧
    ∀ T : ℝ≥0, BoundedVariationOn (fun t => A t ω) (Icc 0 T)) ∧
  IsLocalMartingale P F (fun t ω => M t ω * N t ω - A t ω)

/-- Ordinary-edge Gamma at a vertex, zero at every collapsed end state.
The sole graph sum is reused verbatim from the statement-ingredient module. -/
noncomputable def stateBracketDensity (cells : IndexedCells V) (Φ : V → Plane)
    (x : Option V) : Matrix (Fin 2) (Fin 2) ℝ :=
  match x with
  | some v => StatementIngredients.bracketDensity cells Φ v
  | none => 0

@[simp] theorem stateBracketDensity_none (cells : IndexedCells V) (Φ : V → Plane) :
    stateBracketDensity cells Φ none = 0 := rfl

@[simp] theorem stateBracketDensity_some (cells : IndexedCells V) (Φ : V → Plane)
    (v : V) :
    stateBracketDensity cells Φ (some v) =
      StatementIngredients.bracketDensity cells Φ v := rfl

/-- The manuscript's actual Lebesgue time integral. Restricting to real
`[0,t]` makes `Real.toNNReal` just the time-domain inclusion. -/
noncomputable def ordinaryEdgeBracket (cells : IndexedCells V) (Φ : V → Plane)
    (X : ℝ≥0 → Ω → Option V) (i j : Fin 2) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), stateBracketDensity cells Φ (X s.toNNReal ω) i j

/-- Full predictable-bracket conclusion, including local integrability so the
Bochner integral cannot silently default to zero. The compensated products
range over the whole time axis, including reflection times; no extra singular
or continuous boundary bracket is left unspecified. -/
def HasOrdinaryEdgeBracket (cells : IndexedCells V) (Φ : V → Plane)
    (P : Measure Ω) (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (X : ℝ≥0 → Ω → Option V) (M : ℝ≥0 → Ω → Plane) : Prop :=
  IsLocallySquareIntegrableMartingale P F M ∧
  (∀ᵐ ω ∂P, IsCadlag (fun t => M t ω) ∧
    ∀ (i j : Fin 2) (t : ℝ≥0),
      IntervalIntegrable
        (fun s : ℝ => stateBracketDensity cells Φ (X s.toNNReal ω) i j)
        volume 0 (t : ℝ)) ∧
  ∀ i j : Fin 2, IsContinuousPredictableCovariation P F
    (fun t ω => M t ω i) (fun t ω => M t ω j)
    (ordinaryEdgeBracket cells Φ X i j)

end ReflectedGMS.MartingaleIngredients
