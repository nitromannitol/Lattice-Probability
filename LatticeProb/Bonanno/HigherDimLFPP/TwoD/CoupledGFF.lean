/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.TwoD.CoupledGFF at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.TwoD.CircleKernel
import LatticeProb.Bonanno.HigherDimLFPP.Field.Version
import LatticeProb.Bonanno.HigherDimLFPP.Field.FiniteRange
import LatticeProb.Bonanno.HigherDimLFPP.Field.Exists

/-!
# The coupled circle-average process (packet P-X10, target T2)

Source: `source/higher-dimensional-lfpp-limit.pdf`, App. A.2 (Lemma A.1, two-dimensional part:
"circle averages of radius ε, including the normalization that the unit-circle average at the
origin is zero", coupled with `H_{ε,1}` through the same noise); planning audit HA5, findings A2-1,
A2-6 and Details D12, Claim 2; ruling H12.

For a white noise `W` on `L²(ℝ × ℝ²)` and an admissible kernel `κ`, a continuous version of
`z ↦ W(circVec κ r z)` (`IsCircleVersion`, HA5's `IsCircleVersion`) is, jointly in `r > 0`, the
circle-average process of the whole-plane GFF normalized by `h₁(0) = 0` in the sense of the 2D
library (`LQGDimension.IsGFFCircleAverage`):

* `isGFFCircleAverage_of_isCircleVersion` / `coupledIsGFF` (HA5 D12, Claim 2): Gaussian process
  and mean zero by isonormality, covariance `gffCircleCov` by Claim 1 (`inner_circVec`),
  continuity by construction;
* `exists_isCircleVersion`: such versions exist, by the Kolmogorov–Čentsov theorem
  (`LQGMetric.WhiteNoise.exists_meas_continuous_modification_N`) with moments of order `6`:
  `Var(h_r(z) - h_r(w)) ≤ 2 |z - w| / r` (`norm_circVec_sub_sq_le`) gives
  `E|h_r(z) - h_r(w)|⁶ ≤ C (|z - w| / r)³` and `3 > 2`;
* `exists_coupledRealization`: one probability space carrying a white noise, versions `H ε` of
  `H_{ε,1}` (`ε ∈ (0,1)`) and versions `h r` of the circle averages (`r > 0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP

/-- `Y` is a continuous version of the white-noise circle average
`z ↦ ⟨h, σ_{r,z} - σ_{1,0}⟩ = W(circVec κ r z)` (HA5's `IsCircleVersion`). -/
structure IsCircleVersion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : WN 2 → Ω → ℝ)
    (κ : Rd 2 → ℝ) (r : ℝ) (Y : ℂ → Ω → ℝ) : Prop where
  continuous : ∀ ω, Continuous fun z => Y z ω
  measurable : ∀ z, Measurable (Y z)
  ae_eq : ∀ z, Y z =ᵐ[P] W (circVec κ r z)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN 2 → Ω → ℝ} {κ : Rd 2 → ℝ}

/-- **HA5 D12, Claim 2** (target T2): continuous versions of the white-noise circle averages form,
jointly in `r > 0`, a circle-average process of the whole-plane GFF normalized by `h₁(0) = 0`. -/
theorem isGFFCircleAverage_of_isCircleVersion (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    {h : ℝ → ℂ → Ω → ℝ} (hh : ∀ r > 0, IsCircleVersion P W κ r (h r)) :
    LQGDimension.IsGFFCircleAverage h P where
  isProbabilityMeasure := hW.isProbabilityMeasure
  isGaussianProcess :=
    (hW.isGaussianProcess_comp fun p : Ioi (0 : ℝ) × ℂ => circVec κ p.1 p.2).congr
      fun p => ((hh p.1 p.1.2).ae_eq p.2).symm
  integral_eq_zero ε hε z := by
    rw [integral_congr_ae ((hh ε hε).ae_eq z), hW.integral_eq_zero]
  covariance_eq ε hε δ hδ z w := by
    rw [covariance_congr_ae ((hh ε hε).ae_eq z) ((hh δ hδ).ae_eq w), hW.cov_eq,
      inner_circVec hκ hε hδ]
  continuous ε hε ω := (hh ε hε).continuous ω

/-! ### Existence of continuous versions -/

namespace TwoD

/-- Coordinates `q ↦ q₀ + i q₁` of the plane. -/
def coordC (q : Fin 2 → ℝ) : ℂ := ⟨q 0, q 1⟩

theorem coordC_coord (z : ℂ) : coordC (LQGDimension.Osc37.coord z) = z := by
  apply Complex.ext <;> rfl

theorem continuous_coord : Continuous LQGDimension.Osc37.coord := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact Complex.continuous_re
  · exact Complex.continuous_im

/-- `|z - w| ≤ 2 ‖q - q'‖_∞` in coordinates. -/
theorem norm_coordC_sub_le (q q' : Fin 2 → ℝ) : ‖coordC q - coordC q'‖ ≤ 2 * ‖q - q'‖ := by
  have h0 : |q 0 - q' 0| ≤ ‖q - q'‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (q - q') 0
  have h1 : |q 1 - q' 1| ≤ ‖q - q'‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (q - q') 1
  calc ‖coordC q - coordC q'‖ ≤ |(coordC q - coordC q').re| + |(coordC q - coordC q').im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |q 0 - q' 0| + |q 1 - q' 1| := rfl
    _ ≤ 2 * ‖q - q'‖ := by linarith

end TwoD

open TwoD

/-- **Continuous versions of the circle averages** (target T2, Kolmogorov): for `r > 0` the
process `z ↦ W(circVec κ r z)` has a version that is continuous for every `ω` and measurable at
every point. -/
theorem exists_isCircleVersion (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {r : ℝ}
    (hr : 0 < r) : ∃ Y : ℂ → Ω → ℝ, IsCircleVersion P W κ r Y := by
  set Z : (Fin 2 → ℝ) → Ω → ℝ := fun q => W (circVec κ r (coordC q)) with hZ
  have hZm : ∀ q, Measurable (Z q) := fun q => hW.measurable _
  set c : ℝ := 4 / r with hc
  have hc0 : 0 ≤ c := by positivity
  set M : ℝ := QuantumZipper.gaussianAbsMoment (2 * 3) with hM
  have hM0 : 0 ≤ M := QuantumZipper.gaussianAbsMoment_nonneg _
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧
      QuantumZipper.KolmG.MomentBoundG Z P (2 * 3) (3 : ℝ) K R := by
    intro R
    refine ⟨c ^ 3 * M, by positivity, fun q _ q' _ => ?_⟩
    have hlaw := hW.hasLaw_sub (circVec κ r (coordC q)) (circVec κ r (coordC q'))
    have hE := QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq (P := P)
      ((hW.measurable _).sub (hW.measurable _)) 3 hlaw.map_eq
    simp only [Pi.sub_apply] at hE
    simp only [hZ]
    rw [hE]
    refine ENNReal.ofReal_le_ofReal ?_
    set v : ℝ := ‖circVec κ r (coordC q) - circVec κ r (coordC q')‖ ^ 2 with hv
    have hv0 : 0 ≤ v := sq_nonneg _
    have hvc : v ≤ c * ‖q - q'‖ := by
      calc v ≤ 2 * ‖coordC q - coordC q'‖ / r := norm_circVec_sub_sq_le hκ hr _ _
        _ ≤ 2 * (2 * ‖q - q'‖) / r := by
            gcongr
            exact norm_coordC_sub_le q q'
        _ = c * ‖q - q'‖ := by rw [hc]; ring
    have hcoe : ((v.toNNReal : NNReal) : ℝ) = v := Real.coe_toNNReal _ hv0
    rw [hcoe, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc v ^ 3 * M ≤ (c * ‖q - q'‖) ^ 3 * M := by gcongr
      _ = c ^ 3 * M * ‖q - q'‖ ^ 3 := by ring
  have hpos : ((2 : ℕ) : ℝ) < (3 : ℝ) := by norm_num
  obtain ⟨Y, hYc, hYm, hYZ⟩ := LQGMetric.WhiteNoise.exists_meas_continuous_modification_N
    (P := P) (Z := Z) hZm (p := 2 * 3) (by norm_num) hpos hmom
  refine ⟨fun z ω => Y (LQGDimension.Osc37.coord z) ω,
    ⟨fun ω => (hYc ω).comp continuous_coord, fun z => hYm _, fun z => ?_⟩⟩
  have h := hYZ (LQGDimension.Osc37.coord z)
  simp only [hZ, coordC_coord] at h
  exact h

/-- **A coupled realization** (HA5 D12): one probability space (with `Ω : Type`) carrying a white
noise `W` on `L²(ℝ × ℝ²)`, continuous versions `H ε` of `H_{ε,1}` for `ε ∈ (0,1)` and continuous
versions `h r` of the circle averages `W(circVec κ r ·)` for `r > 0`. -/
theorem exists_coupledRealization (hκ : IsLFPPKernel κ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : WN 2 → Ω → ℝ)
      (H : ℝ → Rd 2 → Ω → ℝ) (h : ℝ → ℂ → Ω → ℝ),
      IsWhiteNoise P W ∧ (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) ∧
        ∀ r > 0, IsCircleVersion P W κ r (h r) := by
  obtain ⟨W, hW⟩ := exists_isWhiteNoise 2
  have hH : ∀ ε : ℝ, ∃ H : Rd 2 → (ℕ → ℝ) → ℝ,
      0 < ε → IsBandVersion LQGDimension.ExistAsm.stdP W κ ε 1 H := by
    intro ε
    by_cases hε : 0 < ε
    · obtain ⟨H, hH⟩ := exists_isBandVersion hκ hW hε 1
      exact ⟨H, fun _ => hH⟩
    · exact ⟨0, fun h => absurd h hε⟩
  have hh : ∀ r : ℝ, ∃ Y : ℂ → (ℕ → ℝ) → ℝ,
      0 < r → IsCircleVersion LQGDimension.ExistAsm.stdP W κ r Y := by
    intro r
    by_cases hr : 0 < r
    · obtain ⟨Y, hY⟩ := exists_isCircleVersion hκ hW hr
      exact ⟨Y, fun _ => hY⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose H hH using hH
  choose h hh using hh
  exact ⟨ℕ → ℝ, inferInstance, LQGDimension.ExistAsm.stdP, W, H, h, hW,
    fun ε hε => hH ε hε.1, fun r hr => hh r hr⟩

end HigherDimLFPP
