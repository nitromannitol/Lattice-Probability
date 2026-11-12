/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.AreaP3bSup at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Opens of namespaces with no copied declaration are removed (FinArea). -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FractionalMoments
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceAS
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.TwoRadiusTilt

/-!
# M4-P3(b), area version, part 4: the rate form of the step bound and the sup bound

Continuation of `AreaP3bMoment` (handoff `handoff/M4-AREA-P3B.md`, "Remaining" items 1–2).

* `integral_abs_massFunC_step_le_rate'` / `integral_abs_massFunC_step_le_rate`: the raw two-radius
  step bound `integral_abs_massFunC_step_le`, in *rate form*. Writing
  `L = ½ log(δ/radius k)`, `radius k = δ e^{-2L}`, `θ = max 0 ((3γ−2)/2)`, `K = 2 log R − log D −
  log(2d)`, `e₁ = 2 − γ² + θ²/2`, `β = min e₁ ((2−γ)²/4)`, the raw bound's two terms are
  `2δ²√(πc₁V)e^{−e₁L}` and `2c₂Vδ²e^{−βL}` (using `|S| ≤ Vδ²` and `2γ² − θ² − 4 = −2e₁`), so with
  `C = cRate γ K V` the bound is `C δ² e^{−βL}`: the scale enters only through the ratio `δ/radius k`
  and the constant is independent of `k`. This is the input of the fractional-moment sup bound.
* `lintegral_iSup_massFunC_inner_rpow_le`: fractional moments of `⨆_{m} W_{k+m}` with
  `W_j = massFunC γ S δ j (innerS …)`, for `p ∈ (0,1]`, in the shape consumed by the interior
  fractional-moment node `fracMoment_area_interior`; same structure as
  `FracMom.lintegral_iSup_innerMass_rpow_le` (boundary case).

Source: Duplantier–Sheffield, Invent. Math. 185 (2011) §3.1 (the circle average has independent
increments; the mass at scale `2^{-k}` is a geometric-type multiplicative cascade, whence the
`sup` fractional moment). The interior decomposition `innerS`/`omZ` is the own adaptation recorded
in the M4-AREA-P3B handoff and in DEVIATIONS.md (L-M4 item 7); the algebra of the rate form is an
own elementary computation (the handoff's recipe, checked step by step).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace AreaP3b

open GaussTK KernelId TwoRadiusC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ### The rate form of the step bound -/

/-- The `√(·)`-constant of the rate form (being the constant of the `√`-term of the two-radius
lemma). -/
def cRateA (γ K : ℝ) : ℝ :=
  (1 + exp ((2 * γ) ^ 2 / 4 * log 2)) * exp ((2 * γ - max 0 ((3 * γ - 2) / 2)) ^ 2 * K / 2)

/-- The `|S|`-constant of the rate form (the constant of the `|S|`-term of the two-radius
lemma). -/
def cRateB (γ K : ℝ) : ℝ := exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2)

/-- The constant of the rate form of the step bound (see `integral_abs_massFunC_step_le_rate`). -/
def cRate (γ K V : ℝ) : ℝ := 2 * √(π * cRateA γ K * V) + 2 * cRateB γ K * V

theorem cRate_nonneg {γ K V : ℝ} (hV : 0 ≤ V) : 0 ≤ cRate γ K V := by
  have hA : 0 ≤ cRateA γ K := by rw [cRateA]; positivity
  have hB : 0 ≤ cRateB γ K := by rw [cRateB]; positivity
  rw [cRate]
  exact add_nonneg (mul_nonneg two_pos.le (Real.sqrt_nonneg _))
    (mul_nonneg (mul_nonneg two_pos.le hB) hV)

/-! ### The sup bound -/

/-- `2 - γ² + θ²/2 > 0` for `0 < γ < 2`, `θ = max 0 ((3γ−2)/2)`: the first entry of the rate
`β = min e₁ ((2−γ)²/4)` is positive, so the geometric series below converges. -/
theorem areaRateExp_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    0 < 2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2 := by
  by_cases h : (3 * γ - 2) / 2 ≤ 0
  · rw [max_eq_left h]
    have h1 : γ ≤ 2 / 3 := by linarith
    have h2 : 0 ≤ γ * (2 / 3 - γ) := mul_nonneg hγ.le (by linarith)
    have h3 : γ ^ 2 ≤ 2 / 3 * γ := by linarith [h2]
    have h4 : 2 / 3 * γ ≤ 4 / 9 := by linarith [h1]
    linarith
  · rw [max_eq_right (le_of_lt (not_le.mp h))]
    have h1 : 0 < (2 - γ) * (10 - γ) := mul_pos (by linarith) (by linarith)
    have h2 : 2 - γ ^ 2 + ((3 * γ - 2) / 2) ^ 2 / 2 = ((2 - γ) * (10 - γ)) / 8 := by ring
    rw [h2]
    exact div_pos h1 (by norm_num)

end AreaP3b
end QuantumZipper
