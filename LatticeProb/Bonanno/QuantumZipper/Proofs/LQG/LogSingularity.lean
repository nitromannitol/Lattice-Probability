/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.LogSingularity at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Opens of namespaces with no copied declaration are removed (Positivity). -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LocalRule
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.CameronMartin
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryExistence
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceAS
import Mathlib.Logic.Equiv.List
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FractionalMoments
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.L2Space
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible

/-!
# M4-P4: boundary log singularities of strength `α < Q`

Blueprint `M4_BLUEPRINT.md`, node M4-P4 (boundary part).

For `s ∈ ℝ` and `α ∈ ℝ` let `ψ(v) = α (−log ‖v − s‖)` and `Y = Z + ofFun ψ`.

* (i) `bdryApprox_add_log`: for regular `x`, exactly
  `bdryApprox γ (x + ofFun ψ) k = max(2^{-k}, |t−s|)^{−αγ/2} · bdryApprox γ x k`.
* (ii) `isVagueLimitOnR_add_log`: away from `s`, if `bdryApprox γ x → ν` then
  `bdryApprox γ (x + ofFun ψ) → |t−s|^{−αγ/2} ν` vaguely on `ℝ \ {s}` (LocalRule).
* (iii) `isVagueLimitR_of_local_of_tight`: local convergence on `ℝ \ {s}` plus uniform smallness
  of the approximations near `s` give global vague convergence, with no atom at `s`;
  `tight_of_annuli` derives the uniform smallness from summable dyadic annulus bounds; and
  `ae_logSingularity` assembles the a.s. statement, taking the M4-P3(b) fractional-moment bound
  (not yet built) as the explicit hypothesis `P3bBound`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace LogSing

open GoodSample GaussTK

/-! ### (i) The exact mean-value identity -/

/-- The density factor `max(2^{-k}, |t−s|)^{−αγ/2}`. -/
def logFactor (γ α s : ℝ) (k : ℕ) (t : ℝ) : ℝ := max (radius k) |t - s| ^ (-(α * γ / 2))

/-! ### (ii) Away from the singularity -/

/-! ### (iii-a) Global vague convergence from local convergence and tightness at `s` -/

section Cut

variable {s : ℝ} {j : ℕ} {t : ℝ}

theorem exists_cutS_lt {δ : ℝ} (hδ : 0 < δ) : ∃ j : ℕ, 2 / ((j : ℝ) + 1) < δ := by
  obtain ⟨j, hj⟩ := exists_nat_gt (2 / δ)
  refine ⟨j, ?_⟩
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hδ] at hj
  nlinarith

end Cut

/-! ### (iii-b) Uniform smallness near `s` from dyadic interval bounds -/

/-- The exponent `b = α⁺ γ / 2`. -/
def expB (γ α : ℝ) : ℝ := max α 0 * γ / 2

/-- The weight `w_n = 2^{(n+1) b}`. -/
def annW (γ α : ℝ) (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (radius (n + 1) ^ (-expB γ α))

theorem radius_zero' : radius 0 = 1 := by simp [radius]

theorem expB_nonneg {γ : ℝ} (hγ : 0 < γ) (α : ℝ) : 0 ≤ expB γ α :=
  div_nonneg (mul_nonneg (le_max_right _ _) hγ.le) zero_le_two

theorem rpow_neg_le_of_le {γ α r x : ℝ} (hγ : 0 < γ) (hr : 0 < r) (hrx : r ≤ x) (hx1 : x ≤ 1) :
    x ^ (-(α * γ / 2)) ≤ r ^ (-expB γ α) := by
  unfold expB
  rcases le_or_gt 0 α with hα | hα
  · rw [max_eq_left hα]
    exact Real.rpow_le_rpow_of_nonpos hr hrx (by nlinarith)
  · rw [max_eq_right hα.le, zero_mul, zero_div, neg_zero, Real.rpow_zero]
    exact Real.rpow_le_one (hr.le.trans hrx) hx1 (by nlinarith)

theorem radius_rpow_mono {γ : ℝ} (hγ : 0 < γ) (α : ℝ) {j k : ℕ} (h : j ≤ k) :
    radius j ^ (-expB γ α) ≤ radius k ^ (-expB γ α) :=
  Real.rpow_le_rpow_of_nonpos (radius_pos k) (AreaExist.aradius_anti h)
    (neg_nonpos.2 (expB_nonneg hγ α))

/-! ### (iii-c) The almost sure statement, under the M4-P3(b) bound -/

theorem radius_rpow (j : ℕ) (x : ℝ) : radius j ^ x = (2 : ℝ) ^ (-(j : ℝ) * x) := by
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num),
    Real.rpow_natCast]
  unfold radius
  rw [inv_pow]

/-- The geometric series behind "`α < Q − γp/2`". -/
theorem summable_annuli {b e p : ℝ} (hp : 0 ≤ p) (hneg : b * p + e < 0) :
    Summable fun n : ℕ => (radius (n + 1) ^ (-b)) ^ p * (2 : ℝ) ^ ((n : ℝ) * e) := by
  have hr : (2 : ℝ) ^ (b * p + e) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
  refine ((summable_geometric_of_lt_one (by positivity) hr).mul_left
    ((2 : ℝ) ^ (b * p))).congr fun n => ?_
  rw [radius_rpow, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul
    (by norm_num), ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  ring

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

open BdryExist (zField)

end Prob

end LogSing
end QuantumZipper
