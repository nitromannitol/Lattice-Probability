/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.BoundaryExistence at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Opens of namespaces with no copied declaration are removed (GaussTK). -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.TwoRadius
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures

/-!
# M4-B3, part 1: the two-radius lemma for the free field's approximating boundary measures

Blueprint `M4_BLUEPRINT.md`, nodes M4-B2 (instantiation) and M4-B3.

For the free field `X` (`IsFreeGFFModConstH X P`) and `R > 0` we work with the normalized field
`zField X R ω = addConst (X ω) (-X ω (fc(0,R)))` (`Z` of blueprint §0). The additive constant
only multiplies the approximating measures by `e^{γ c/2}` (handled in `BoundaryExistenceAS`).

* `ae_avgReg_spec`, `avgReg_zField_ae_eq`: almost surely the dyadic regularization `avgReg`
  converges everywhere on `Hbar`, and at each fixed point it equals the raw folded-circle value.
* `trlHyp_field`: the Gaussian hypotheses `TRLHyp` of the two-radius lemma hold for
  `U t = avgReg (Z) k t` (coarse radius `2^{-k}`) and `Δ t = avgReg (Z) (k+1) t - U t`, on any
  set `S` with `|t| + 1 ≤ R` (M4-R1/R2 through `GaussianToolkit`).
* `integral_abs_bdryApprox_step_le_rate`: for `f` bounded measurable, vanishing off `S`,
  `E|∫ f dν_k - ∫ f dν_{k+1}| ≤ C e^{-β k log 2}` with `β = bdryRate γ > 0` for every
  `γ ∈ (0,2)`, where `ν_k = bdryApprox γ (Z ω) k`.
* `integral_abs_bdryApprox_le_rate`: the telescoped form, for `k ≤ k'`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal

namespace QuantumZipper
namespace BdryExist

open TwoRadius

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The normalized field `Z = X − X(fc(0,R))`. -/
def zField (X : Ω → FieldSample) (R : ℝ) (ω : Ω) : FieldSample :=
  addConst (X ω) (-X ω (foldedCircle 0 R))

theorem radius_le_one (k : ℕ) : radius k ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

/-! ### Almost sure identification of `avgReg` -/

/-! ### Gaussian laws and variances -/

/-! ### The Gaussian hypotheses of the two-radius lemma (M4-R1/R2 → `TRLHyp`) -/

/-! ### Pathwise integrals and integrability -/

/-! ### The two-radius bound for consecutive dyadic levels -/

theorem geom_sum_le_inv_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, q ^ i ≤ 1 / (1 - q) := by
  have h1 : 0 < 1 - q := by linarith
  have e : (q ^ n - 1) / (q - 1) = (1 - q ^ n) / (1 - q) := by
    rw [← neg_sub (1 : ℝ) (q ^ n), ← neg_sub (1 : ℝ) q, neg_div_neg_eq]
  rw [geom_sum_eq hq1.ne, e]
  exact (div_le_div_iff_of_pos_right h1).2 (by linarith [pow_nonneg hq0 n])

end BdryExist
end QuantumZipper
