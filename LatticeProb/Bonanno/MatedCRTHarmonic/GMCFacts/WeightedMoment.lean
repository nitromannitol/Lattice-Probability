/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.WeightedMoment at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.OuterMoment
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability

/-!
# Moments of the `|z|^{−γ²}`-weighted LQG mass of the unit disc

For a whole-plane GFF circle-average process `H` normalized by `h_1(0) = 0` (measurable coordinates) with LQG measure
`μ` (the `IsLQGAreaOf`), the weighted mass `wDiscMass γ μ = ∫_{B_1(0)} |z|^{−γ²} dμ(z)` is the mass of the unit disc for
the field `h − γ log|·|` (the circle-average embedding of a γ-quantum cone near `0`). It is a.e.-measurable
(`aemeasurable_wDiscMass`), and for `0 < p < 4/γ² − 1`, `E[wDiscMass^p] < ∞` (`lintegral_wDiscMass_rpow_lt_top`): [16, Lemma A.3]
with `α = γ`.

Proof ([16]): split `B_1(0) ∖ {0}` into the dyadic annuli
`B_{2^{-n}} ∖ B_{2^{-n-1}}`, on which `|z|^{−γ²} ≤ 2^{(n+1)γ²}`; `E μ(B_{2^{-n}})^p ≤ C 2^{−n ζ(p)}` with
`ζ(p) = (2 + γ²/2)p − γ²p²/2` (`exists_lintegral_ball_origin_rpow_le`, `lintegral_ball_one_rpow_lt_top`); sum by
subadditivity (`p ≤ 1`) or Minkowski (`p ≥ 1`); the geometric series converges iff `p < 4/γ² − 1`.

Measurability: integrals of continuous compactly supported functions are a.s. limits of the measurable approximations;
open sets and the weight are reached by monotone limits of QuantumZipper's `LQGMeas.openBump`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Finset Filter Topology
open QuantumZipper.LQGMeas
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCFacts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}

/-! ### Measurability -/

lemma measurable_lintegral_lqgApprox (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) (γ : ℝ) (k : ℕ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun ω => ∫⁻ z, f z ∂(GMSLemma27.lqgApprox γ H k ω) := by
  have hdr : 0 < GMSLemma27.dyadicRadius k := by
    rw [dyadicRadius_eq_radius]; exact QuantumZipper.radius_pos k
  have hj := measurable_uncurry_coord hH hHm hdr
  have hd : Measurable fun p : ℂ × Ω => ENNReal.ofReal
      (GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) * Real.exp (γ * H (GMSLemma27.dyadicRadius k) p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul ((hj.const_mul γ).exp))
  have e : ∀ ω, ∫⁻ z, f z ∂(GMSLemma27.lqgApprox γ H k ω) = ∫⁻ z, ENNReal.ofReal
      (GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) * Real.exp (γ * H (GMSLemma27.dyadicRadius k) z ω)) * f z := by
    intro ω
    simp only [GMSLemma27.lqgApprox]
    exact lintegral_withDensity_eq_lintegral_mul _ (hd.comp (measurable_id.prodMk measurable_const)) hf
  simp_rw [e]
  exact (hd.mul (hf.comp measurable_fst)).lintegral_prod_left'

/-- **Integrals of continuous compactly supported functions against the LQG measure are a.e.-measurable.** -/
theorem aemeasurable_lintegral_ofReal (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} {μ : Ω → Measure ℂ} (hμ : GMSLemma27.IsLQGAreaOf γ H μ P)
    {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f) (hf0 : ∀ z, 0 ≤ f z) :
    AEMeasurable (fun ω => ∫⁻ z, ENNReal.ofReal (f z) ∂μ ω) P := by
  refine aemeasurable_of_tendsto_metrizable_ae atTop
    (f := fun k ω => ∫⁻ z, ENNReal.ofReal (f z) ∂(GMSLemma27.lqgApprox γ H k ω))
    (fun k => (measurable_lintegral_lqgApprox hH hHm γ k
      (ENNReal.measurable_ofReal.comp hf.measurable)).aemeasurable) ?_
  filter_upwards [hμ] with ω ⟨hlf, hc⟩
  have h1 := (ENNReal.continuous_ofReal.tendsto _).comp (hc f hf hfs)
  have e1 : ∀ k, ENNReal.ofReal (∫ z, f z ∂(GMSLemma27.lqgApprox γ H k ω)) =
      ∫⁻ z, ENNReal.ofReal (f z) ∂(GMSLemma27.lqgApprox γ H k ω) := fun k => by
    have := isLocallyFiniteMeasure_lqgApprox hH γ k ω
    exact ofReal_integral_eq_lintegral_ofReal (hf.integrable_of_hasCompactSupport hfs) (ae_of_all _ hf0)
  have e2 : ENNReal.ofReal (∫ z, f z ∂(μ ω)) = ∫⁻ z, ENNReal.ofReal (f z) ∂μ ω :=
    ofReal_integral_eq_lintegral_ofReal (hf.integrable_of_hasCompactSupport hfs) (ae_of_all _ hf0)
  simp only [Function.comp_def, e1, e2] at h1
  exact h1

/-- The LQG mass of a ball is a.e.-measurable. -/
theorem aemeasurable_measure_ball (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} {μ : Ω → Measure ℂ} (hμ : GMSLemma27.IsLQGAreaOf γ H μ P)
    (x : ℂ) (ρ : ℝ) : AEMeasurable (fun ω => μ ω (ball x ρ)) P := by
  have hUc : (ball x ρ)ᶜ.Nonempty :=
    (Set.nonempty_compl.2 (isCompact_closedBall x ρ).ne_univ).mono
      (compl_subset_compl.2 ball_subset_closedBall)
  have key : ∀ ω, μ ω (ball x ρ) = ⨆ n : ℕ, ∫⁻ z, ENNReal.ofReal (openBump (ball x ρ) n z) ∂μ ω :=
    fun ω => measure_open_eq_iSup _ isOpen_ball hUc
  simp_rw [key]
  exact AEMeasurable.iSup fun n => aemeasurable_lintegral_ofReal hH hHm hμ (continuous_openBump _ n)
    (hasCompactSupport_openBump isBounded_ball n) (openBump_nonneg _ n)

/-! ### The weighted mass -/

/-! ### Dyadic annuli -/

/-! ### Summation: subadditivity and Minkowski -/

/-! ### The moment bound -/

end MatedCRTHarmonic.GMCFacts
