/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GffLin at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffCV

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A.s. linearity of the extended zero-boundary GFF on a square (DFGPS L2.8, T:883–885 input)

For the ZB analogue of DFGPS Lemma 2.1 (T:883–885) one compares `p_{ε²/2} * h̊ (x)` with the
localized mollification `ĥ̊*_ε(x)`; both are pairings of the process `Xh` (`IsZBGFFProcessExt`)
and their difference is the pairing with the difference of the densities, which needs
`Xh ρ − Xh σ = Xh (ρ − σ)` a.s. On a square `D = (a, a+L)²` this follows from the spectral form
of the covariance (`HeatSq.zeroGFFTestCov_sqOpen_spectral`): the variance of
`Xh ρ − Xh σ − Xh (ρ − σ)` is `∑ w_p (ρ̂_p − σ̂_p − (ρ−σ)^_p)² = 0`.
(Standard: the GFF as a stochastic process is linear, Berestycki–Powell arXiv:2404.16642 §1.2.)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace LQGMetric.DFGPS

open QuantumZipper QuantumZipper.K3 HeatSq Blueprint

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma sqCoef_bddSub {a L : ℝ} (ρ σ : BddOn (sqOpen a L)) (p : ℕ × ℕ) :
    sqCoef a L (bddSub ρ σ).1 p = sqCoef a L ρ.1 p - sqCoef a L σ.1 p := by
  have hρi := integrable_of_bdd_sq ρ.2.1 ρ.2.2.1.choose_spec ρ.2.2.2
  have hσi := integrable_of_bdd_sq σ.2.1 σ.2.2.1.choose_spec σ.2.2.2
  unfold sqCoef
  rw [← integral_sub]
  · congr 1; funext z; simp only [bddSub]; ring
  · exact hρi.mul_bdd (continuous_sqMode a L p).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact abs_sqMode_le a L p z)
  · exact hσi.mul_bdd (continuous_sqMode a L p).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact abs_sqMode_le a L p z)

/-- **A.s. linearity**: `Xh ρ − Xh σ = Xh (ρ − σ)` a.s. (square domains). -/
theorem zbExt_sub_ae [IsProbabilityMeasure P] {a L : ℝ} (hL : 0 < L)
    {Xh : BddOn (sqOpen a L) → Ω → ℝ} (hX : IsZBGFFProcessExt (sqOpens a L) Xh P)
    (ρ σ : BddOn (sqOpen a L)) :
    (fun ω => Xh ρ ω - Xh σ ω) =ᵐ[P] Xh (bddSub ρ σ) := by
  set f := bddSub ρ σ
  have h2 : ∀ τ, MemLp (Xh τ) 2 P := fun τ => (hX.gaussian.hasGaussianLaw_eval τ).memLp_two
  set D : Ω → ℝ := Xh ρ - Xh σ - Xh f with hD
  have hD2 : MemLp D 2 P := ((h2 ρ).sub (h2 σ)).sub (h2 f)
  -- the covariance of `D` with itself vanishes
  set Q := zeroGFFTestCov (sqOpens a L) with hQ
  have hc : ∀ α β : BddOn (sqOpen a L), cov[Xh α, Xh β; P] = Q α.1 β.1 :=
    fun α β => hX.covariance_eq α β
  have hm : ∀ α : BddOn (sqOpen a L), ∫ ω, Xh α ω ∂P = 0 := fun α => hX.centered α
  have hcov : cov[D, D; P] =
      (Q ρ.1 ρ.1 - Q σ.1 ρ.1 - Q f.1 ρ.1) - (Q ρ.1 σ.1 - Q σ.1 σ.1 - Q f.1 σ.1) -
        (Q ρ.1 f.1 - Q σ.1 f.1 - Q f.1 f.1) := by
    rw [hD, covariance_sub_right hD2 ((h2 ρ).sub (h2 σ)) (h2 f),
      covariance_sub_right hD2 (h2 ρ) (h2 σ),
      covariance_sub_left ((h2 ρ).sub (h2 σ)) (h2 f) (h2 ρ),
      covariance_sub_left (h2 ρ) (h2 σ) (h2 ρ),
      covariance_sub_left ((h2 ρ).sub (h2 σ)) (h2 f) (h2 σ),
      covariance_sub_left (h2 ρ) (h2 σ) (h2 σ),
      covariance_sub_left ((h2 ρ).sub (h2 σ)) (h2 f) (h2 f),
      covariance_sub_left (h2 ρ) (h2 σ) (h2 f)]
    simp only [hc]
  have hzero : (Q ρ.1 ρ.1 - Q σ.1 ρ.1 - Q f.1 ρ.1) - (Q ρ.1 σ.1 - Q σ.1 σ.1 - Q f.1 σ.1) -
      (Q ρ.1 f.1 - Q σ.1 f.1 - Q f.1 f.1) = 0 := by
    have S := fun (α β : BddOn (sqOpen a L)) => zeroGFFTestCov_sqOpen_spectral hL α β
    have hs := (((S ρ ρ).sub (S σ ρ)).sub (S f ρ)).sub (((S ρ σ).sub (S σ σ)).sub (S f σ))
      |>.sub (((S ρ f).sub (S σ f)).sub (S f f))
    refine hs.unique (hasSum_zero.congr_fun fun p => ?_)
    simp only [f, sqCoef_bddSub]
    ring
  have hvar : Var[D; P] = 0 := by
    rw [← covariance_self hD2.aestronglyMeasurable.aemeasurable, hcov, hzero]
  have hmean : P[D] = 0 := by
    rw [hD, integral_sub' (((h2 ρ).sub (h2 σ)).integrable one_le_two)
      ((h2 f).integrable one_le_two), integral_sub' ((h2 ρ).integrable one_le_two)
      ((h2 σ).integrable one_le_two), hm, hm, hm]
    ring
  have hint : ∫ ω, D ω ^ 2 ∂P = 0 := by
    rw [variance_eq_integral hD2.aestronglyMeasurable.aemeasurable, hmean] at hvar
    simpa using hvar
  have hae : (fun ω => D ω ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hD2.integrable_sq).1 hint
  filter_upwards [hae] with ω hω
  have : D ω = 0 := by simpa using hω
  simp only [hD, Pi.sub_apply] at this
  linarith

end LQGMetric.DFGPS
