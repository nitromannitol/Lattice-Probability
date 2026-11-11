import Mathlib
import LatticeProb.Gauss.GFFAffineInvariance
import LatticeProb.LQG.LQGMeasureDerived

/-!
# Gaussian tail of the circle average of the whole-plane GFF at the origin: LP form

LP copy of `HarmonicBalls/Proofs/Sec2/CircleAverageTail.lean` (lines 1-100). The Step
`CircleAverageDyadicTailStep` (`HarmonicBalls/Steps/Sec2/VolumeGrowth.lean:324`) is copied as the definition
`CircleAverageDyadicTailStepLP` with the LP names, and it is PROVED here, not assumed.

Argument (as in the HB docstring): for `r ∈ (0, 1]` the covariance kernel of the whole-plane GFF normalized at
`|z| = 1` is `-log |x - y|` on `∂B_r(0) × ∂B_r(0)` (`wholePlaneCov_eq_neg_log`, Duplantier-Sheffield 2011); the average of
`log |· - x|` over `∂B_r(0)` is `log r` for `|x| = r` (Jensen's formula); hence `Var h^ℂ_r(0) = log (1/r)`, the variable
`h^ℂ_{2^{-k}}(0)` is centred Gaussian with variance `k log 2`, and the Chernoff bound for a Gaussian moment generating
function gives the tail (Berestycki-Powell, *Gaussian free field, Liouville quantum gravity and Gaussian multiplicative chaos*).
The statement and the proof use no Harmonic-balls object.
-/

universe u

namespace LatticeProb.LQG.LQGMeasureNonatomicMass

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open LatticeProb.Gauss LatticeProb.LQG
open LatticeProb.LQG.ProfileDerived (dyadicScale_pos)

/-- LP form of `CircleAverageDyadicTailStep` (`HarmonicBalls/Steps/Sec2/VolumeGrowth.lean:324`). For the whole-plane GFF
normalized by `h^ℂ_1(0) = 0`, `h^ℂ_{2^{-k}}(0)` is centred Gaussian with variance `k log 2`, so
`P[|h^ℂ_{2^{-k}}(0)| ≥ L] ≤ 2 exp(-L² / (2 (k+1) log 2))` for `L ≥ 0`. A definition, proved below. -/
def CircleAverageDyadicTailStepLP : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → ∀ k : ℕ, ∀ L : ℝ, 0 ≤ L →
      P {ω | L ≤ |hcirc ω (dyadicScale k) 0|} ≤
        ENNReal.ofReal (2 * Real.exp (-(L ^ 2) / (2 * (((k : ℝ) + 1) * Real.log 2))))

/-- `Var h^ℂ_r(0) = -log r` for `r ∈ (0, 1]`: the kernel `wholePlaneCov` averaged over `∂B_r(0) × ∂B_r(0)`. -/
theorem wholePlaneGFFCov_circle_zero_lp {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    wholePlaneGFFCov (.circle r 0) (.circle r 0) = -Real.log r := by
  change Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) 0 r) 0 r = -Real.log r
  rw [Real.circleAverage_congr_sphere (f₂ := fun _ => -Real.log r), Real.circleAverage_const]
  intro x hx
  have hx' : ‖x‖ = r := by simpa [abs_of_pos hr] using hx
  have h : Real.circleAverage (fun y => wholePlaneCov x y) 0 r =
      Real.circleAverage (fun y => -Real.log ‖y - x‖) 0 r := by
    apply Real.circleAverage_congr_sphere
    intro y hy
    have hy' : ‖y‖ = r := by simpa [abs_of_pos hr] using hy
    simp only
    rw [wholePlaneCov_eq_neg_log (hx'.le.trans hr1) (hy'.le.trans hr1), norm_sub_rev]
  show Real.circleAverage (fun y => wholePlaneCov x y) 0 r = -Real.log r
  rw [h]
  have h0 := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (c := 0) (a := x) hr.ne'
  rw [zero_sub, norm_neg, hx', inv_mul_cancel₀ hr.ne', Real.posLog_one, add_zero] at h0
  rw [Real.circleAverage_def] at h0 ⊢
  rw [intervalIntegral.integral_neg, smul_neg, h0]

/-- `CircleAverageDyadicTailStepLP` is proved from `IsWholePlaneGFF` (LP copy of `circleAverageDyadicTailStep_holds`). -/
theorem circleAverageDyadicTailStep_lp : CircleAverageDyadicTailStepLP.{u} := by
  intro Ω _ P hC hcirc hh k L hL
  have hP := hh.isProbabilityMeasure
  have hr := dyadicScale_pos k
  have hr1 : dyadicScale k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set X : Ω → ℝ := fun ω => hcirc ω (dyadicScale k) 0 with hX
  have hG : HasGaussianLaw X P := hh.hasGaussianLaw_circle hr 0
  have hmean : ∫ ω, X ω ∂P = 0 := hh.integral_eq_zero (.circle (dyadicScale k) 0) hr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogr : -Real.log (dyadicScale k) = k * Real.log 2 := by
    rw [dyadicScale, Real.log_pow, Real.log_inv]; ring
  have hvar : Var[X; P] = k * Real.log 2 := by
    rw [← covariance_self hG.aemeasurable]
    have hcov := hh.covariance_eq (.circle (dyadicScale k) 0) (.circle (dyadicScale k) 0) hr hr
    rw [wholePlaneGFFCov_circle_zero_lp hr hr1, hlogr] at hcov
    exact hcov
  set v : NNReal := ((k : ℝ) * Real.log 2).toNNReal with hv_def
  have hv : (v : ℝ) = k * Real.log 2 := Real.coe_toNNReal _ (by positivity)
  have hlaw : HasLaw X (gaussianReal 0 v) P :=
    ⟨hG.aemeasurable, by rw [hG.map_eq_gaussianReal, hmean, hvar]⟩
  have hint : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) P := by
    intro t
    have h := integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
    rw [← hlaw.map_eq] at h
    exact (integrable_map_measure (by fun_prop) hG.aemeasurable).1 h
  set v' : ℝ := ((k : ℝ) + 1) * Real.log 2 with hv'
  have hv'0 : 0 < v' := by positivity
  have hvv' : (v : ℝ) ≤ v' := by rw [hv, hv']; nlinarith
  set s : ℝ := L / v' with hs
  have hs0 : 0 ≤ s := by positivity
  have hbound : Real.exp (-s * L) * Real.exp (0 * s + v * s ^ 2 / 2) ≤
      Real.exp (-(L ^ 2) / (2 * v')) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    calc -s * L + (0 * s + v * s ^ 2 / 2) ≤ -s * L + v' * s ^ 2 / 2 := by nlinarith [sq_nonneg s]
      _ = -(L ^ 2) / (2 * v') := by rw [hs]; field_simp; ring
  have hup : P.real {ω | L ≤ X ω} ≤ Real.exp (-(L ^ 2) / (2 * v')) := by
    refine (measure_ge_le_exp_mul_mgf L hs0 (hint s)).trans ?_
    rw [mgf_gaussianReal hlaw]; exact hbound
  have hlow : P.real {ω | X ω ≤ -L} ≤ Real.exp (-(L ^ 2) / (2 * v')) := by
    refine (measure_le_le_exp_mul_mgf (-L) (neg_nonpos.2 hs0) (hint (-s))).trans ?_
    rw [mgf_gaussianReal hlaw]
    convert hbound using 3 <;> ring
  have hsub : {ω | L ≤ |X ω|} ⊆ {ω | L ≤ X ω} ∪ {ω | X ω ≤ -L} := by
    intro ω hω
    rcases le_abs'.1 (show L ≤ |X ω| from hω) with h | h
    · exact Or.inr h
    · exact Or.inl h
  calc P {ω | L ≤ |hcirc ω (dyadicScale k) 0|} ≤ P {ω | L ≤ X ω} + P {ω | X ω ≤ -L} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = ENNReal.ofReal (P.real {ω | L ≤ X ω}) + ENNReal.ofReal (P.real {ω | X ω ≤ -L}) := by
        rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-(L ^ 2) / (2 * v'))) + ENNReal.ofReal (Real.exp (-(L ^ 2) / (2 * v'))) :=
        add_le_add (ENNReal.ofReal_le_ofReal hup) (ENNReal.ofReal_le_ofReal hlow)
    _ = ENNReal.ofReal (2 * Real.exp (-(L ^ 2) / (2 * v'))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end LatticeProb.LQG.LQGMeasureNonatomicMass
