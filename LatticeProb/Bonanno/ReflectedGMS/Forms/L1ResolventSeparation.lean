/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.L1ResolventSeparation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.WeakSquareDynkin
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationarySpeedMeasure
import LatticeProb.Bonanno.ReflectedGMS.Forms.StrongContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Separation of weighted L1 functions by vertex resolvents

The normalized vertex occupation resolvents at rates `n + 1` converge to the
corresponding vertex indicators.  Their uniform Markov bound then permits
dominated convergence against every function integrable for the atomic speed
measure.  Thus the full family of vertex-resolvent tests separates weighted
`L¹` functions, without introducing another function space.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.FullNetworkForm

open ComplexSequenceSpace SemigroupMultiplier

variable {V : Type*}

/-- Every positive-parameter full-form resolvent is an `L²(m)` contraction. -/
theorem parameterizedResolvent_opNorm_le_one
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    {h : ℝ} (hh : 0 < h) :
    ‖parameterizedResolvent G m h‖ ≤ 1 := by
  rw [← complexify_norm,
    complexify_parameterizedResolvent_eq_cfc_eulerStep G m hh]
  apply norm_cfc_le zero_le_one
  intro x hx
  have hmem := eulerStep_mem_Icc hh
    (complexOneResolvent_spectrum_subset G m hx)
  rw [Real.norm_eq_abs, abs_of_nonneg hmem.1]
  exact hmem.2

/-- Along the concrete parameters `1/(n+1)`, the full-form resolvents converge
strongly to the identity on the existing weighted vertex `L²` space. -/
theorem parameterizedResolvent_nat_tendsto_identity
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (f : ValueSpace V) :
    Tendsto (fun n : ℕ => parameterizedResolvent G m (1 / ((n : ℝ) + 1)) f)
      atTop (𝓝 f) := by
  let S : ℕ → ValueSpace V →L[ℝ] ValueSpace V :=
    fun n => parameterizedResolvent G m (1 / ((n : ℝ) + 1))
  apply contraction_tendsto_of_denseRange atTop S (oneResolvent G m)
  · intro n
    exact parameterizedResolvent_opNorm_le_one G m (by positivity)
  · exact denseRange_oneResolvent G m hm
  · intro y
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    let h : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    have hS_norm (n : ℕ) : ‖S n‖ ≤ 1 :=
      parameterizedResolvent_opNorm_le_one G m (by positivity)
    have herror (n : ℕ) :
        ‖S n (oneResolvent G m y) - oneResolvent G m y‖ ≤
          2 * h n * ‖y‖ := by
      have hh : 0 < h n := by positivity
      let B := resolventDenominator G m (h n)
      have hB : IsUnit B := resolventDenominator_isUnit G m hh
      have hcancel : S n * B = oneResolvent G m := by
        dsimp only [S, B, h, parameterizedResolvent]
        rw [mul_assoc, Ring.inverse_mul_cancel B hB, mul_one]
      have happ := congrArg
        (fun T : ValueSpace V →L[ℝ] ValueSpace V => T y) hcancel
      have heq :
          S n (oneResolvent G m y) - oneResolvent G m y =
            h n • (S n (oneResolvent G m y) - S n y) := by
        change S n (h n • y + (1 - h n) • oneResolvent G m y) =
          oneResolvent G m y at happ
        rw [map_add, map_smul, map_smul] at happ
        calc
          S n (oneResolvent G m y) - oneResolvent G m y =
              S n (oneResolvent G m y) -
                (h n • S n y + (1 - h n) • S n (oneResolvent G m y)) := by
                  rw [happ]
          _ = h n • (S n (oneResolvent G m y) - S n y) := by module
      rw [heq, norm_smul, Real.norm_of_nonneg hh.le]
      calc
        h n * ‖S n (oneResolvent G m y) - S n y‖
            ≤ h n * (‖S n (oneResolvent G m y)‖ + ‖S n y‖) := by
              gcongr
              exact norm_sub_le _ _
        _ ≤ h n * (‖oneResolvent G m y‖ + ‖y‖) := by
              gcongr
              · simpa only [one_mul] using
                  (S n).le_of_opNorm_le (hS_norm n) (oneResolvent G m y)
              · simpa only [one_mul] using
                  (S n).le_of_opNorm_le (hS_norm n) y
        _ ≤ 2 * h n * ‖y‖ := by
              have hR := oneResolvent_apply_norm_le G m y
              nlinarith [norm_nonneg y]
    apply squeeze_zero (fun _ => norm_nonneg _) herror
    have hh0 : Tendsto h atTop (𝓝 0) := by
      simpa only [h] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [mul_assoc] using (hh0.const_mul (2 : ℝ)).mul_const ‖y‖

/-- The normalized occupation potential at rates `n+1` converges pointwise to
the target-vertex indicator. -/
theorem natSucc_mul_vertexOccupationPotential_tendsto
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (x y : V) :
    Tendsto
      (fun n : ℕ => ((n : ℝ) + 1) *
        vertexOccupationPotential G m ((n : ℝ) + 1) x y)
      atTop (𝓝 (G.indic y x)) := by
  let d := weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)
  let ev : ValueSpace V →L[ℝ] ℝ :=
    (Real.sqrt (m x))⁻¹ • lp.evalCLM ℝ (fun _ : V => ℝ) 2 x
  have hconv := (ev.continuous.tendsto d).comp
    (parameterizedResolvent_nat_tendsto_identity G m hm d)
  have hev (u : ValueSpace V) : ev u = unweight m u x := by
    change (Real.sqrt (m x))⁻¹ * u x = u x / Real.sqrt (m x)
    rw [div_eq_mul_inv, mul_comm]
  have hevd : ev d = G.indic y x := by
    rw [hev]
    dsimp only [d]
    rw [unweight_weightedValue m hm]
  rw [← hevd]
  apply hconv.congr'
  filter_upwards with n
  rw [vertexOccupationPotential_eq_resolvent G m (by positivity)]
  simp only [one_div, d]
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hn]
  exact hev _

end ReflectedGMS.FullNetworkForm

namespace ReflectedGMS

open FullNetworkForm

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [DecidableEq V]

/-- Dominated convergence upgrades normalized vertex-resolvent convergence to
all weighted `L¹(m)` test functions. -/
theorem natSucc_mul_integral_mul_vertexOccupationPotential_tendsto
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (f : V → ℝ)
    (hf : Integrable f (vertexSpeedMeasure m)) (y : V) :
    Tendsto
      (fun n : ℕ => ∫ z, f z * (((n : ℝ) + 1) *
        vertexOccupationPotential G m ((n : ℝ) + 1) z y)
          ∂vertexSpeedMeasure m)
      atTop (𝓝 (m y * f y)) := by
  have hdc := tendsto_integral_of_dominated_convergence
    (μ := vertexSpeedMeasure m) (fun z => ‖f z‖)
    (fun n => (measurable_of_countable _).aestronglyMeasurable)
    hf.norm
    (fun n => ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      have hU0 := vertexOccupationPotential_nonneg G m hm
        (show 0 < (n : ℝ) + 1 by positivity) z y
      have hU1 := vertexOccupationPotential_le_inv G m hm
        (show 0 < (n : ℝ) + 1 by positivity) z y
      have hnorm : |((n : ℝ) + 1) *
          vertexOccupationPotential G m ((n : ℝ) + 1) z y| ≤ 1 := by
        rw [abs_of_nonneg (mul_nonneg (by positivity) hU0)]
        have := mul_le_mul_of_nonneg_left hU1
          (show 0 ≤ (n : ℝ) + 1 by positivity)
        calc
          _ ≤ ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) := this
          _ = 1 := by field_simp
      simpa only [Real.norm_eq_abs, mul_one] using
        mul_le_mul_of_nonneg_left hnorm (abs_nonneg (f z)))
    (ae_of_all _ fun z =>
      (tendsto_const_nhds.mul
        (natSucc_mul_vertexOccupationPotential_tendsto G m hm z y)))
  have hfun : (fun z => f z * G.indic y z) = ({y} : Set V).indicator f := by
    funext z
    by_cases hzy : z = y
    · subst z
      simp [ReflectedWalk.ConductanceGraph.indic]
    · simp [ReflectedWalk.ConductanceGraph.indic, hzy]
  have htarget :
      (∫ z, f z * G.indic y z ∂vertexSpeedMeasure m) = m y * f y := by
    rw [hfun, integral_indicator (μ := vertexSpeedMeasure m)
      (f := f) (measurableSet_singleton y), integral_singleton]
    simp [Measure.real, vertexSpeedMeasure_singleton,
      ENNReal.toReal_ofReal (hm y).le]
  rw [htarget] at hdc
  exact hdc

/-- Vanishing against every positive-rate vertex occupation resolvent forces a
weighted `L¹(m)` function to vanish pointwise. -/
theorem eq_zero_of_integral_mul_vertexOccupationPotential_eq_zero
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (f : V → ℝ)
    (hf : Integrable f (vertexSpeedMeasure m))
    (hzero : ∀ (alpha : ℝ), 0 < alpha → ∀ y : V,
      (∫ z, f z * vertexOccupationPotential G m alpha z y
        ∂vertexSpeedMeasure m) = 0) :
    f = 0 := by
  funext y
  have hlim := natSucc_mul_integral_mul_vertexOccupationPotential_tendsto
    G m hm f hf y
  have hall (n : ℕ) :
      (∫ z, f z * (((n : ℝ) + 1) *
        vertexOccupationPotential G m ((n : ℝ) + 1) z y)
          ∂vertexSpeedMeasure m) = 0 := by
    calc
      _ = ((n : ℝ) + 1) *
          ∫ z, f z * vertexOccupationPotential G m ((n : ℝ) + 1) z y
            ∂vertexSpeedMeasure m := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with z
          ring
      _ = 0 := by rw [hzero ((n : ℝ) + 1) (by positivity) y, mul_zero]
  have hzeroLim : Tendsto
      (fun n : ℕ => ∫ z, f z * (((n : ℝ) + 1) *
        vertexOccupationPotential G m ((n : ℝ) + 1) z y)
          ∂vertexSpeedMeasure m)
      atTop (𝓝 0) := by
    simpa only [hall] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hmass : m y * f y = 0 := tendsto_nhds_unique hlim hzeroLim
  exact (mul_eq_zero.mp hmass).resolve_left (hm y).ne'

end ReflectedGMS
