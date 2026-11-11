import Mathlib
import LatticeProb.Gauss.GFF
import LatticeProb.LQG.LQGMeasure
import LatticeProb.LQG.LQGMeasureDerived

/-! # The Weyl relation off the origin: LP form

LP form of the frozen statement `LocalLQGInsertionWeylOffOrigin` (`HarmonicBalls/FirstPass/Frozen/S8c.lean:85`):
same binders, quantifiers and conclusion, stated for the LP definitions `IsWholePlaneGFF`
(`LatticeProb/Gauss/GFF.lean`), `IsLQGMeasureOfField`, `IsLQGLimit`, `lqgApprox`, `dyadicScale`, `lqgQ`
(`LatticeProb/LQG/LQGMeasure.lean`) and `ProfileDerived.dyadicScale_pos` (`LatticeProb/LQG/LQGMeasureDerived.lean`).

Proof: the derivation of `localLQGInsertionWeylOffOrigin_derived` (`HarmonicBalls/FirstPass/S8c/WeylOffOriginDerived.lean`),
copied in LP form. The Weyl factor and its test identity are copied from `HarmonicBalls/FirstPass/S11i/SingularWeyl.lean`
(lines 30-163), the Radon identification from `HarmonicBalls/FirstPass/S8c/WeylOffOriginRadon.lean`. The Riesz-Markov
uniqueness step is Mathlib's `MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported`, the call that
`HarmonicBalls/FirstPass/S8d/RadonUnique.lean` also makes (here `radonUniqueLP`). No new mathematics: the steps are the
vague limits of the circle-average approximations (Duplantier-Sheffield 2011, Prop. 1.1), the identity
`h_ε(z) = h^ℂ_ε(z) - α₀ log|z|` for `ε < |z|` (Jensen's formula for `log ‖·‖` on circles about `z`), which makes the
approximating densities differ by the Weyl factor `‖z‖^{-γα₀}` off the origin, and the Riesz-Markov uniqueness of
Radon measures on `ℂ`. The almost-sure joint continuity of the circle averages
(`IsWholePlaneGFF.ae_continuousOn_circle`) gives the measurability of the dyadic approximants. The terminology follows
Duplantier-Sheffield, *Liouville quantum gravity and KPZ* (2011), and Berestycki-Powell, *Gaussian free field, Liouville
quantum gravity and Gaussian multiplicative chaos*.

The statement and the proof use no Harmonic-balls object. The bridge to `HarmonicBalls.LocalLQGInsertionWeylOffOrigin` is
`HarmonicBalls/FirstPass/LPBridge/WeylOffOrigin.lean`.
-/

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal
open LatticeProb.Gauss LatticeProb.LQG
open LatticeProb.LQG.ProfileDerived (dyadicScale_pos)

universe u

namespace LatticeProb.LQG.WeylOffOriginDerived

/-! ## Weyl factor and test identity (from `FirstPass/S11i/SingularWeyl.lean`, LP form) -/

/-- The Weyl factor `w(z) = exp (-(γ α) · log ‖z‖)`: equal to `‖z‖ ^ (-γ α)` for `z ≠ 0` and `1` at `0`
(Lean's convention `Real.log 0 = 0`). Write-up Step 12, identity (1). -/
noncomputable def weylFactor (γ α : ℝ) (z : ℂ) : ℝ :=
  Real.exp (-(γ * α) * Real.log ‖z‖)

lemma weylFactor_pos (γ α : ℝ) (z : ℂ) : 0 < weylFactor γ α z :=
  Real.exp_pos _

lemma weylFactor_measurable (γ α : ℝ) : Measurable (weylFactor γ α) := by
  unfold weylFactor
  fun_prop

lemma weylFactor_continuousAt {γ α : ℝ} {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (weylFactor γ α) z := by
  have hlog : ContinuousAt (fun x : ℂ => Real.log ‖x‖) z :=
    ContinuousAt.log continuous_norm.continuousAt (norm_ne_zero_iff.2 hz)
  unfold weylFactor
  exact Real.continuous_exp.continuousAt.comp (continuousAt_const.mul hlog)

/-- Mean value property of `log ‖·‖` on a circle not enclosing `0`: for `0 < r < |z|` the circle average of
`log |x|` over `∂B_r(z)` is `log |z|` (Jensen's formula, Mathlib). -/
lemma circleAverage_log_norm_eq {z : ℂ} {r : ℝ} (hr : 0 < r) (hrz : r < ‖z‖) :
    Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r = Real.log ‖z‖ := by
  have hz : 0 < ‖z‖ := hr.trans hrz
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := z) hr.ne'
  simp only [sub_zero] at h
  have hge : 1 ≤ r⁻¹ * ‖z‖ := by
    rw [← div_eq_inv_mul, one_le_div hr]
    exact hrz.le
  rw [h, Real.posLog_eq_log (by rw [abs_of_nonneg (zero_le_one.trans hge)]; exact hge),
    Real.log_mul (inv_ne_zero hr.ne') hz.ne', Real.log_inv]
  ring

/-- The field circle averages of `h = h^ℂ - α log|·|` and of `h^ℂ` differ by `α log|z|` for `0 < r < |z|`. -/
lemma fieldCircleAverage_eq_sub {α : ℝ} {hc : ℝ → ℂ → ℝ} {r : ℝ} {z : ℂ} (hr : 0 < r) (hrz : r < ‖z‖) :
    fieldCircleAverage α hc r z = fieldCircleAverage 0 hc r z - α * Real.log ‖z‖ := by
  unfold fieldCircleAverage
  rw [circleAverage_log_norm_eq hr hrz]
  ring

/-- The field circle average `z ↦ fieldCircleAverage α hc r z` is measurable when `hc r` is, for `r > 0`
(the logarithmic term is `log r + log⁺(r⁻¹ |z|)` by Jensen's formula). -/
lemma measurable_fieldCircleAverage {α : ℝ} {hc : ℝ → ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hm : Measurable (hc r)) : Measurable (fun z : ℂ => fieldCircleAverage α hc r z) := by
  have hJ : ∀ z : ℂ, Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r =
      Real.log r + Real.posLog (r⁻¹ * ‖z‖) := by
    intro z
    have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := z) hr.ne'
    simpa only [sub_zero] using h
  have hL : Measurable (fun z : ℂ => Real.log r + Real.posLog (r⁻¹ * ‖z‖)) :=
    measurable_const.add (Real.continuous_posLog.measurable.comp (measurable_const.mul measurable_norm))
  have heq : (fun z : ℂ => fieldCircleAverage α hc r z) =
      fun z : ℂ => hc r z - α * (Real.log r + Real.posLog (r⁻¹ * ‖z‖)) := by
    funext z
    unfold fieldCircleAverage
    rw [hJ z]
  rw [heq]
  exact hm.sub (measurable_const.mul hL)

/-- **Dyadic circle averages are almost surely measurable in the centre (derived).** Under `IsWholePlaneGFF`,
almost surely the circle averages are jointly continuous on `(0, ∞) × ℂ` (`IsWholePlaneGFF.ae_continuousOn_circle`,
Duplantier-Sheffield 2011, Prop. 3.1). For each dyadic radius `2^{-k} > 0` the map `z ↦ hcirc ω (2^{-k}) z` is then
continuous, hence measurable. This replaces the retired frozen input `CircleAverageVersionMeasurableStmt`. -/
lemma ae_measurable_dyadic_circleAverage {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, Measurable (fun z : ℂ => hcirc ω (dyadicScale k) z) := by
  filter_upwards [hGFF.ae_continuousOn_circle] with ω hω k
  have hcont : ContinuousOn (fun z : ℂ => hcirc ω (dyadicScale k) z) Set.univ :=
    hω.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z _ => ⟨dyadicScale_pos k, Set.mem_univ z⟩)
  exact (continuousOn_univ.1 hcont).measurable

/-- The Lebesgue density integral of the approximation `ε^{γ²/2} e^{γ h_ε(z)} dz`. -/
lemma integral_lqgApprox {γ : ℝ} {hε : ℝ → ℂ → ℝ} {ε : ℝ} (hε0 : 0 ≤ ε) (hm : Measurable (hε ε))
    (f : ℂ → ℝ) :
    ∫ z, f z ∂(lqgApprox γ hε ε) = ∫ z, ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z) * f z := by
  unfold lqgApprox
  have hmeas : Measurable (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z))) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul hm)))
  rw [integral_withDensity_eq_integral_toReal_smul hmeas (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  congr 1
  funext z
  rw [smul_eq_mul, ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg hε0 _) (Real.exp_pos _).le)]

/-- Continuity of `z ↦ f(z) w(z)` when `f` vanishes on a ball about `0`. -/
lemma continuous_mul_weylFactor {γ α δ : ℝ} {f : ℂ → ℝ} (hf : Continuous f) (hδ : 0 < δ)
    (hfδ : ∀ z : ℂ, ‖z‖ < δ → f z = 0) : Continuous (fun z => f z * weylFactor γ α z) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    refine (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℝ)) 0).congr ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ] with x hx
    rw [mem_ball_zero_iff] at hx
    simp [hfδ x hx]
  · exact hf.continuousAt.mul (weylFactor_continuousAt hz)

/-- Test identity: for `f` continuous with compact support, vanishing on `B_δ(0)`, the vague limits give
`∫ f dμ_α = ∫ f w dμ_0`. -/
lemma integral_test_eq {γ α δ : ℝ} {hg hh : ℝ → ℂ → ℝ} {m0 mα : Measure ℂ}
    (hcomp : ∀ r z, 0 < r → r < ‖z‖ → hh r z = hg r z - α * Real.log ‖z‖)
    (hgm : ∀ k : ℕ, Measurable (hg (dyadicScale k)))
    (hhm : ∀ k : ℕ, Measurable (hh (dyadicScale k)))
    (hg_lim : IsLQGLimit γ hg m0) (hh_lim : IsLQGLimit γ hh mα)
    {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f) (hδ : 0 < δ)
    (hfδ : ∀ z : ℂ, ‖z‖ < δ → f z = 0) :
    ∫ z, f z ∂mα = ∫ z, f z * weylFactor γ α z ∂m0 := by
  have hfw : Continuous (fun z => f z * weylFactor γ α z) := continuous_mul_weylFactor hf hδ hfδ
  have hfws : HasCompactSupport (fun z => f z * weylFactor γ α z) := hfs.mul_right
  have hev : ∀ᶠ k : ℕ in atTop, dyadicScale k < δ := by
    have h0 : Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact h0.eventually (gt_mem_nhds hδ)
  have heq : (fun k : ℕ => ∫ z, f z ∂(lqgApprox γ hh (dyadicScale k))) =ᶠ[atTop]
      (fun k : ℕ => ∫ z, f z * weylFactor γ α z ∂(lqgApprox γ hg (dyadicScale k))) := by
    filter_upwards [hev] with k hk
    rw [integral_lqgApprox (dyadicScale_pos k).le (hhm k) f,
      integral_lqgApprox (dyadicScale_pos k).le (hgm k)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : ‖z‖ < δ
    · simp [hfδ z hz]
    · have hz' : δ ≤ ‖z‖ := not_lt.1 hz
      have hεz : dyadicScale k < ‖z‖ := lt_of_lt_of_le hk hz'
      have hexp : Real.exp (γ * hh (dyadicScale k) z) =
          Real.exp (γ * hg (dyadicScale k) z) * weylFactor γ α z := by
        rw [hcomp _ z (dyadicScale_pos k) hεz, weylFactor, ← Real.exp_add]
        congr 1
        ring
      simp only [hexp]
      ring
  have h1 := hh_lim.tendsto_integral f hf hfs
  have h2 := hg_lim.tendsto_integral (fun z => f z * weylFactor γ α z) hfw hfws
  exact tendsto_nhds_unique h1 (Tendsto.congr' heq.symm h2)

/-! ## Riesz-Markov uniqueness of Radon measures on `ℂ` -/

/-- Uniqueness of locally finite measures on `ℂ` from their integrals against continuous compactly supported real
functions (Riesz-Markov uniqueness, Rudin, Real and Complex Analysis, Thm 2.14). This is Mathlib's
`MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported`; locally finite Borel measures on `ℂ` are regular. -/
theorem radonUniqueLP (m m' : Measure ℂ) (hm : IsLocallyFiniteMeasure m) (hm' : IsLocallyFiniteMeasure m')
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → ∫ z, f z ∂m = ∫ z, f z ∂m') : m = m' := by
  exact Measure.ext_of_integral_eq_on_compactlySupported
    (fun g => h (g : ℂ → ℝ) g.continuous g.hasCompactSupport)

/-! ## Weyl change off the origin: Radon identification (from `FirstPass/S8c/WeylOffOriginRadon.lean`, LP form) -/

/-- The measure `μ` weighted by the (possibly non-measurable at `0`) density `ofReal ∘ w`. -/
noncomputable def withDensityOffOrigin (μ : Measure ℂ) (w : ℂ → ℝ) : Measure ℂ :=
  μ.withDensity fun z => ENNReal.ofReal (w z)

/-- Continuous cut-off `k ↦ max 0 (min 1 (k‖z‖ - 1))`: zero for `‖z‖ < 1/(k+1)`, equal to `1` once `k‖z‖ ≥ 2`,
and nondecreasing in `k`. -/
noncomputable def offOriginCutoff (k : ℕ) (z : ℂ) : ℝ :=
  max 0 (min 1 ((k : ℝ) * ‖z‖ - 1))

lemma offOriginCutoff_continuous (k : ℕ) : Continuous (offOriginCutoff k) := by
  unfold offOriginCutoff
  fun_prop

lemma offOriginCutoff_nonneg (k : ℕ) (z : ℂ) : 0 ≤ offOriginCutoff k z :=
  le_max_left _ _

lemma offOriginCutoff_le_one (k : ℕ) (z : ℂ) : offOriginCutoff k z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma offOriginCutoff_monotone (z : ℂ) : Monotone fun k : ℕ => offOriginCutoff k z := by
  intro k k' hkk'
  have hk : (k : ℝ) * ‖z‖ ≤ (k' : ℝ) * ‖z‖ :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 hkk') (norm_nonneg z)
  show offOriginCutoff k z ≤ offOriginCutoff k' z
  unfold offOriginCutoff
  exact max_le_max le_rfl (min_le_min le_rfl (by linarith))

lemma offOriginCutoff_eq_zero {k : ℕ} {z : ℂ} (hz : ‖z‖ < 1 / ((k : ℝ) + 1)) :
    offOriginCutoff k z = 0 := by
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : ‖z‖ * ((k : ℝ) + 1) < 1 := (lt_div_iff₀ hpos).1 hz
  have h2 : (k : ℝ) * ‖z‖ - 1 ≤ 0 := by nlinarith [norm_nonneg z]
  unfold offOriginCutoff
  rw [min_eq_right (show (k : ℝ) * ‖z‖ - 1 ≤ 1 by linarith [norm_nonneg z]), max_eq_left h2]

lemma offOriginCutoff_zero_point (k : ℕ) : offOriginCutoff k 0 = 0 := by
  apply offOriginCutoff_eq_zero
  rw [norm_zero]
  positivity

lemma offOriginCutoff_eq_one {z : ℂ} (hz : z ≠ 0) : ∃ k : ℕ, offOriginCutoff k z = 1 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ‖z‖)
  refine ⟨k, ?_⟩
  have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2 : 2 < (k : ℝ) * ‖z‖ := (div_lt_iff₀ hnz).1 hk
  unfold offOriginCutoff
  rw [min_eq_left (show (1 : ℝ) ≤ (k : ℝ) * ‖z‖ - 1 by linarith),
    max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]

/-- Continuous bump `max 0 (min 1 (R + 1 - ‖z‖))`: one on `‖z‖ ≤ R`, zero on `‖z‖ > R + 1`. -/
noncomputable def offOriginBump (R : ℝ) (z : ℂ) : ℝ :=
  max 0 (min 1 (R + 1 - ‖z‖))

lemma offOriginBump_continuous (R : ℝ) : Continuous (offOriginBump R) := by
  unfold offOriginBump
  fun_prop

lemma offOriginBump_nonneg (R : ℝ) (z : ℂ) : 0 ≤ offOriginBump R z :=
  le_max_left _ _

lemma offOriginBump_le_one (R : ℝ) (z : ℂ) : offOriginBump R z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma offOriginBump_eq_one {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) : offOriginBump R z = 1 := by
  unfold offOriginBump
  rw [min_eq_left (show (1 : ℝ) ≤ R + 1 - ‖z‖ by linarith), max_eq_right zero_le_one]

lemma offOriginBump_eq_zero {R : ℝ} {z : ℂ} (hz : R + 1 < ‖z‖) : offOriginBump R z = 0 := by
  unfold offOriginBump
  rw [min_eq_right (show R + 1 - ‖z‖ ≤ 1 by linarith), max_eq_left (show R + 1 - ‖z‖ ≤ 0 by linarith)]

lemma offOriginBump_hasCompactSupport (R : ℝ) : HasCompactSupport (offOriginBump R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + 1)) (fun z hz => ?_)
  have hz' : R + 1 < ‖z‖ := by
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    exact hz
  exact offOriginBump_eq_zero hz'

/-- A continuous function on `ℂ` minus the origin, extended to `ℂ`, is measurable. -/
lemma measurable_of_continuousOn_compl_singleton {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) :
    Measurable w := by
  classical
  have hV : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton (0 : ℂ)).compl
  have h := ContinuousOn.measurable_piecewise (f := w) (g := fun _ => w 0) (s := ({0}ᶜ : Set ℂ)) hw
    continuousOn_const hV
  convert h using 1
  funext z
  by_cases hz : z = 0
  · subst hz
    simp [Set.piecewise]
  · simp [Set.piecewise, hz]

/-- Test functions vanishing near `0`: the Bochner identity `∫ f dm = ∫ f w dμ`, rewritten for lower integrals
against `ν = μ.withDensity (ofReal ∘ w)`. -/
lemma lintegral_ofReal_eq_of_vanishing {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ] {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ)
    (f : ℂ → ℝ) (hf : Continuous f) (hcf : HasCompactSupport f) (hf0 : ∀ z, 0 ≤ f z)
    (δ : ℝ) (hδ : 0 < δ) (hfδ : ∀ z : ℂ, ‖z‖ < δ → f z = 0) :
    ∫⁻ z, ENNReal.ofReal (f z) ∂m = ∫⁻ z, ENNReal.ofReal (f z) ∂(withDensityOffOrigin μ w) := by
  -- the product `f * w` vanishes on the ball of radius `δ`, hence is continuous on `ℂ`
  have hFc : Continuous fun z => f z * w z := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = 0
    · subst hz
      have hev : (fun z => f z * w z) =ᶠ[𝓝 (0 : ℂ)] fun _ => (0 : ℝ) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ] with z hz'
        have hz'' : ‖z‖ < δ := by simpa using hz'
        simp [hfδ z hz'']
      exact continuousAt_const.congr hev.symm
    · have hV : ({0}ᶜ : Set ℂ) ∈ 𝓝 z := isOpen_compl_singleton.mem_nhds hz
      exact hf.continuousAt.mul (hw.continuousAt hV)
  have hFsupp : HasCompactSupport fun z => f z * w z :=
    (show HasCompactSupport (f * w) from hcf.mul_right)
  have hFint : Integrable (fun z => f z * w z) μ := hFc.integrable_of_hasCompactSupport hFsupp
  have hfint : Integrable f m := hf.integrable_of_hasCompactSupport hcf
  have hA : ∫ z, f z ∂m = (∫⁻ z, ENNReal.ofReal (f z) ∂m).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hf.aestronglyMeasurable
  have hB : ∫ z, f z * w z ∂μ = (∫⁻ z, ENNReal.ofReal (f z * w z) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z => mul_nonneg (hf0 z) (hw0 z)) hFc.aestronglyMeasurable
  have hAfin : ∫⁻ z, ENNReal.ofReal (f z) ∂m ≠ ⊤ := hfint.lintegral_lt_top.ne
  have hBfin : ∫⁻ z, ENNReal.ofReal (f z * w z) ∂μ ≠ ⊤ := hFint.lintegral_lt_top.ne
  have hAB : ∫⁻ z, ENNReal.ofReal (f z) ∂m = ∫⁻ z, ENNReal.ofReal (f z * w z) ∂μ :=
    (ENNReal.toReal_eq_toReal_iff' hAfin hBfin).1 (by
      rw [← hA, ← hB]
      exact h f hf hcf ⟨δ, hδ, hfδ⟩)
  have hmeas : Measurable fun z => ENNReal.ofReal (w z) :=
    ENNReal.measurable_ofReal.comp (measurable_of_continuousOn_compl_singleton hw)
  have hfmeas : Measurable fun z => ENNReal.ofReal (f z) :=
    ENNReal.measurable_ofReal.comp hf.measurable
  unfold withDensityOffOrigin
  rw [lintegral_withDensity_eq_lintegral_mul μ hmeas hfmeas, hAB]
  refine lintegral_congr fun z => ?_
  simp only [Pi.mul_apply]
  rw [ENNReal.ofReal_mul (hf0 z), mul_comm]

/-- Monotone convergence along the cut-offs: the identity of `lintegral_ofReal_eq_of_vanishing` holds on `{0}ᶜ`
for every nonnegative continuous compactly supported `g`. -/
lemma lintegral_ofReal_restrict_compl_zero_eq {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ] {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ)
    (g : ℂ → ℝ) (hg : Continuous g) (hcg : HasCompactSupport g) (hg0 : ∀ z, 0 ≤ g z) :
    ∫⁻ z, ENNReal.ofReal (g z) ∂(m.restrict ({0}ᶜ : Set ℂ)) =
      ∫⁻ z, ENNReal.ofReal (g z) ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) := by
  have hV : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton (0 : ℂ)).compl
  have hF : ∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (g z * offOriginCutoff k z) ∂m =
      ∫⁻ z, ENNReal.ofReal (g z * offOriginCutoff k z) ∂(withDensityOffOrigin μ w) := by
    intro k
    refine lintegral_ofReal_eq_of_vanishing hw hw0 h _ (hg.mul (offOriginCutoff_continuous k))
      (show HasCompactSupport (g * offOriginCutoff k) from hcg.mul_right)
      (fun z => mul_nonneg (hg0 z) (offOriginCutoff_nonneg k z))
      (1 / ((k : ℝ) + 1)) (by positivity) (fun z hz => ?_)
    simp only [offOriginCutoff_eq_zero hz, mul_zero]
  have hsup : ∀ z : ℂ, (⨆ k : ℕ, ENNReal.ofReal (g z * offOriginCutoff k z)) =
      ({0}ᶜ : Set ℂ).indicator (fun z => ENNReal.ofReal (g z)) z := by
    intro z
    by_cases hz : z = 0
    · subst hz
      simp only [offOriginCutoff_zero_point, mul_zero, ENNReal.ofReal_zero, iSup_const]
      rw [Set.indicator_of_notMem (show (0 : ℂ) ∉ ({0}ᶜ : Set ℂ) by simp)]
    · rw [Set.indicator_of_mem (show z ∈ ({0}ᶜ : Set ℂ) from hz)]
      obtain ⟨k0, hk0⟩ := offOriginCutoff_eq_one hz
      refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le k0 (le_of_eq ?_))
      · exact ENNReal.ofReal_le_ofReal
          (mul_le_of_le_one_right (hg0 z) (offOriginCutoff_le_one k z))
      · rw [hk0, mul_one]
  have hmeasF : ∀ k : ℕ, Measurable fun z => ENNReal.ofReal (g z * offOriginCutoff k z) := fun k =>
    ENNReal.measurable_ofReal.comp (hg.mul (offOriginCutoff_continuous k)).measurable
  have hmonoF : Monotone fun (k : ℕ) (z : ℂ) => ENNReal.ofReal (g z * offOriginCutoff k z) := by
    intro k k' hkk' z
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (offOriginCutoff_monotone z hkk') (hg0 z))
  calc ∫⁻ z, ENNReal.ofReal (g z) ∂(m.restrict ({0}ᶜ : Set ℂ))
      = ∫⁻ z, ({0}ᶜ : Set ℂ).indicator (fun z => ENNReal.ofReal (g z)) z ∂m :=
        (lintegral_indicator hV _).symm
    _ = ∫⁻ z, ⨆ k : ℕ, ENNReal.ofReal (g z * offOriginCutoff k z) ∂m :=
        lintegral_congr fun z => (hsup z).symm
    _ = ⨆ k : ℕ, ∫⁻ z, ENNReal.ofReal (g z * offOriginCutoff k z) ∂m :=
        lintegral_iSup hmeasF hmonoF
    _ = ⨆ k : ℕ, ∫⁻ z, ENNReal.ofReal (g z * offOriginCutoff k z) ∂(withDensityOffOrigin μ w) :=
        iSup_congr fun k => hF k
    _ = ∫⁻ z, ⨆ k : ℕ, ENNReal.ofReal (g z * offOriginCutoff k z) ∂(withDensityOffOrigin μ w) :=
        (lintegral_iSup hmeasF hmonoF).symm
    _ = ∫⁻ z, ({0}ᶜ : Set ℂ).indicator (fun z => ENNReal.ofReal (g z)) z ∂(withDensityOffOrigin μ w) :=
        lintegral_congr fun z => hsup z
    _ = ∫⁻ z, ENNReal.ofReal (g z) ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) :=
        lintegral_indicator hV _

/-- Local finiteness of `ν|V` on balls about `0`: `ν(closedBall 0 R) ≤ m(closedBall 0 (R+1))`, via the bump. -/
lemma withDensityOffOrigin_restrict_closedBall_lt_top {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ] {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ)
    (R : ℝ) :
    ((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) (Metric.closedBall 0 R) < ⊤ := by
  have hbound : ((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) (Metric.closedBall 0 R) ≤
      ∫⁻ z, ENNReal.ofReal (offOriginBump R z) ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) := by
    refine (lintegral_indicator_one measurableSet_closedBall).symm.trans_le (lintegral_mono fun z => ?_)
    by_cases hz : ‖z‖ ≤ R
    · have hmem : z ∈ Metric.closedBall (0 : ℂ) R := mem_closedBall_zero_iff.2 hz
      rw [Set.indicator_of_mem hmem, offOriginBump_eq_one hz, Pi.one_apply]
      simp
    · have hmem : z ∉ Metric.closedBall (0 : ℂ) R := fun h' => hz (mem_closedBall_zero_iff.1 h')
      rw [Set.indicator_of_notMem hmem]
      exact zero_le
  have hlw := lintegral_ofReal_restrict_compl_zero_eq hw hw0 h (offOriginBump R)
    (offOriginBump_continuous R) (offOriginBump_hasCompactSupport R) (offOriginBump_nonneg R)
  have hpt : ∀ z : ℂ, ENNReal.ofReal (offOriginBump R z) ≤
      (Metric.closedBall (0 : ℂ) (R + 1)).indicator 1 z := by
    intro z
    by_cases hz : ‖z‖ ≤ R + 1
    · have hmem : z ∈ Metric.closedBall (0 : ℂ) (R + 1) := mem_closedBall_zero_iff.2 hz
      rw [Set.indicator_of_mem hmem, Pi.one_apply]
      exact ENNReal.ofReal_le_one.2 (offOriginBump_le_one R z)
    · have hmem : z ∉ Metric.closedBall (0 : ℂ) (R + 1) := fun h' => hz (mem_closedBall_zero_iff.1 h')
      rw [Set.indicator_of_notMem hmem, offOriginBump_eq_zero (not_le.1 hz), ENNReal.ofReal_zero]
  have hm_le : ∫⁻ z, ENNReal.ofReal (offOriginBump R z) ∂(m.restrict ({0}ᶜ : Set ℂ)) ≤
      m (Metric.closedBall 0 (R + 1)) := by
    calc ∫⁻ z, ENNReal.ofReal (offOriginBump R z) ∂(m.restrict ({0}ᶜ : Set ℂ))
        ≤ ∫⁻ z, ENNReal.ofReal (offOriginBump R z) ∂m := lintegral_mono' Measure.restrict_le_self le_rfl
      _ ≤ ∫⁻ z, (Metric.closedBall (0 : ℂ) (R + 1)).indicator 1 z ∂m := lintegral_mono hpt
      _ = m (Metric.closedBall 0 (R + 1)) := lintegral_indicator_one measurableSet_closedBall
  calc ((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) (Metric.closedBall 0 R)
      ≤ ∫⁻ z, ENNReal.ofReal (offOriginBump R z) ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) := hbound
    _ = ∫⁻ z, ENNReal.ofReal (offOriginBump R z) ∂(m.restrict ({0}ᶜ : Set ℂ)) := hlw.symm
    _ ≤ m (Metric.closedBall 0 (R + 1)) := hm_le
    _ < ⊤ := measure_closedBall_lt_top

/-- `ν|V` is locally finite. -/
lemma isLocallyFiniteMeasure_withDensityOffOrigin_restrict {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ] {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ) :
    IsLocallyFiniteMeasure ((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) := by
  refine ⟨fun x => ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩⟩
  refine lt_of_le_of_lt (measure_mono ?_)
    (withDensityOffOrigin_restrict_closedBall_lt_top hw hw0 h (‖x‖ + 1))
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  rw [mem_closedBall_zero_iff]
  linarith [norm_sub_norm_le z x]

/-- Lower integrals of `ofReal g` (any continuous compactly supported real `g`) agree on `{0}ᶜ`. -/
lemma lintegral_ofReal_restrict_compl_zero_eq' {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ] {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ)
    (g : ℂ → ℝ) (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∫⁻ z, ENNReal.ofReal (g z) ∂(m.restrict ({0}ᶜ : Set ℂ)) =
      ∫⁻ z, ENNReal.ofReal (g z) ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) := by
  have e : ∀ x : ℝ, ENNReal.ofReal x = ENNReal.ofReal (max x 0) := fun x => by
    rcases le_total x 0 with hx | hx
    · rw [ENNReal.ofReal_of_nonpos hx, max_eq_right hx, ENNReal.ofReal_zero]
    · rw [max_eq_left hx]
  have hcg' : HasCompactSupport fun z => max (g z) 0 :=
    HasCompactSupport.comp_left (g := fun x : ℝ => max x 0) hcg (by simp)
  calc ∫⁻ z, ENNReal.ofReal (g z) ∂(m.restrict ({0}ᶜ : Set ℂ))
      = ∫⁻ z, ENNReal.ofReal (max (g z) 0) ∂(m.restrict ({0}ᶜ : Set ℂ)) :=
        lintegral_congr fun z => e (g z)
    _ = ∫⁻ z, ENNReal.ofReal (max (g z) 0) ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) :=
        lintegral_ofReal_restrict_compl_zero_eq hw hw0 h _ (hg.max continuous_const) hcg'
          (fun z => le_max_right _ _)
    _ = ∫⁻ z, ENNReal.ofReal (g z) ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) :=
        (lintegral_congr fun z => e (g z)).symm

/-- Integrals of continuous compactly supported real `f` agree on `{0}ᶜ`. -/
lemma integral_restrict_compl_zero_eq {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ] {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ)
    (f : ℂ → ℝ) (hf : Continuous f) (hcf : HasCompactSupport f) :
    ∫ z, f z ∂(m.restrict ({0}ᶜ : Set ℂ)) =
      ∫ z, f z ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) := by
  have := isLocallyFiniteMeasure_withDensityOffOrigin_restrict hw hw0 h
  have hi1 : Integrable f (m.restrict ({0}ᶜ : Set ℂ)) := hf.integrable_of_hasCompactSupport hcf
  have hi2 : Integrable f ((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) :=
    hf.integrable_of_hasCompactSupport hcf
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi2,
    lintegral_ofReal_restrict_compl_zero_eq' hw hw0 h f hf hcf,
    lintegral_ofReal_restrict_compl_zero_eq' hw hw0 h (fun z => -f z) hf.neg hcf.neg]

/-- Riesz-Markov uniqueness on the open set `{0}ᶜ`: `m|V = ν|V`. -/
lemma restrict_compl_zero_eq {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ] {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ) :
    m.restrict ({0}ᶜ : Set ℂ) = (withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ) :=
  radonUniqueLP _ _ inferInstance
    (isLocallyFiniteMeasure_withDensityOffOrigin_restrict hw hw0 h)
    (fun f hf hcf => integral_restrict_compl_zero_eq hw hw0 h f hf hcf)

/-- **Step 5-6.** Let `m, μ` be locally finite measures on `ℂ` and `w : ℂ → ℝ` nonnegative,
continuous off the origin. If `∫ f dm = ∫ f · w dμ` for every continuous compactly supported real `f` vanishing near
`0`, then `m s = ∫⁻_s ofReal (w z) dμ` for every measurable `s` avoiding `0`.
(Weyl off-origin identity; for `m = λ_ω`, `μ = μ_ω`, `w z = ‖z‖^(γα₀)`, as in the write-up.) -/
theorem eq_withDensity_offOrigin_of_integral_eq {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ]
    {w : ℂ → ℝ} (hw : ContinuousOn w {0}ᶜ) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ) :
    ∀ s : Set ℂ, MeasurableSet s → (0 : ℂ) ∉ s → m s = ∫⁻ z in s, ENNReal.ofReal (w z) ∂μ := by
  intro s hs h0
  have hsV : s ⊆ ({0}ᶜ : Set ℂ) := by
    intro z hz
    rw [Set.mem_compl_singleton_iff]
    intro hz0
    exact h0 (hz0 ▸ hz)
  calc m s = m.restrict ({0}ᶜ : Set ℂ) s := by
        rw [Measure.restrict_apply hs, Set.inter_eq_left.2 hsV]
    _ = (withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ) s := by
        rw [restrict_compl_zero_eq hw hw0 h]
    _ = withDensityOffOrigin μ w s := by
        rw [Measure.restrict_apply hs, Set.inter_eq_left.2 hsV]
    _ = ∫⁻ z in s, ENNReal.ofReal (w z) ∂μ := by
        unfold withDensityOffOrigin
        exact withDensity_apply _ hs


/-! ## The almost-sure identity of integrals and the Weyl relation (from `FirstPass/S8c/WeylOffOriginDerived.lean`) -/

/-- Steps 1-4 of the derivation of the Weyl relation off the origin (Duplantier-Sheffield 2011, vague limits
of the LQG approximations). Almost surely, for every continuous compactly supported `f : ℂ → ℝ` vanishing on a ball
about `0`, the no-insertion measure `lam ω` and the insertion-`α₀` measure `μ ω` satisfy
`∫ f d(lam ω) = ∫ f(z) ‖z‖^(γ α₀) d(μ ω)`. The two vague limits are taken for one common conull set. -/
theorem ae_integral_eq_rpow_of_isLQGMeasureOfField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {γ α₀ : ℝ} {μ lam : Ω → Measure ℂ}
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hlam : IsLQGMeasureOfField P γ 0 hcirc lam) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂(lam ω) = ∫ z, f z * ‖z‖ ^ (γ * α₀) ∂(μ ω) := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  have hlam' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (lam ω) := hlam
  filter_upwards [hμ', hlam', ae_measurable_dyadic_circleAverage hGFF] with ω hμω hlamω hmeas
  intro f hf hfs hfδ'
  obtain ⟨δ, hδ, hfδ⟩ := hfδ'
  -- the density `‖z‖^(γ α₀)` is the Weyl factor of `-α₀` off the origin, and both vanish near the origin
  have hpt : ∀ z : ℂ, f z * ‖z‖ ^ (γ * α₀) = f z * weylFactor γ (-α₀) z := by
    intro z
    by_cases hz : ‖z‖ < δ
    · simp [hfδ z hz]
    · have hpos : 0 < ‖z‖ := lt_of_lt_of_le hδ (not_lt.1 hz)
      congr 1
      rw [weylFactor, Real.rpow_def_of_pos hpos]
      congr 1
      ring
  have hinv : ∀ z : ℂ, weylFactor γ (-α₀) z * weylFactor γ α₀ z = 1 := by
    intro z
    rw [weylFactor, weylFactor, ← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  have hlhs : ∀ z : ℂ, f z * weylFactor γ (-α₀) z * weylFactor γ α₀ z = f z := by
    intro z
    rw [mul_assoc, hinv z, mul_one]
  have hcont : Continuous (fun z => f z * weylFactor γ (-α₀) z) :=
    continuous_mul_weylFactor hf hδ hfδ
  have hcs : HasCompactSupport (fun z => f z * weylFactor γ (-α₀) z) := hfs.mul_right
  have hgz : ∀ z : ℂ, ‖z‖ < δ → f z * weylFactor γ (-α₀) z = 0 := fun z hz => by
    simp [hfδ z hz]
  -- Step 3 and Step 4: the approximation identity and the two vague limits, for the test function
  -- `f · weylFactor γ (-α₀)`
  have key := integral_test_eq (γ := γ) (α := α₀) (δ := δ)
    (hg := fun r z => fieldCircleAverage 0 (hcirc ω) r z)
    (hh := fun r z => fieldCircleAverage α₀ (hcirc ω) r z) (m0 := lam ω) (mα := μ ω)
    (fun r z hr hrz => fieldCircleAverage_eq_sub hr hrz)
    (fun k => measurable_fieldCircleAverage (α := 0) (hc := hcirc ω) (dyadicScale_pos k)
      (hmeas k))
    (fun k => measurable_fieldCircleAverage (α := α₀) (hc := hcirc ω) (dyadicScale_pos k)
      (hmeas k))
    hlamω hμω hcont hcs hδ hgz
  calc ∫ z, f z ∂(lam ω)
      = ∫ z, f z * weylFactor γ (-α₀) z * weylFactor γ α₀ z ∂(lam ω) :=
        integral_congr_ae (Eventually.of_forall fun z => (hlhs z).symm)
    _ = ∫ z, f z * weylFactor γ (-α₀) z ∂(μ ω) := key.symm
    _ = ∫ z, f z * ‖z‖ ^ (γ * α₀) ∂(μ ω) :=
        integral_congr_ae (Eventually.of_forall fun z => (hpt z).symm)

/-- LP form of `LocalLQGInsertionWeylOffOrigin` (`HarmonicBalls/FirstPass/Frozen/S8c.lean:85`), with the same binders,
quantifiers and conclusion, for the LP definitions `IsWholePlaneGFF`, `IsLQGMeasureOfField` and `lqgQ`.
Almost surely, the no-insertion LQG measure `lam` of the whole-plane GFF satisfies `lam = |z|^{γ α₀} μ` on the complement
of `0`, where `μ` is the LQG measure of insertion `α₀` (`h = h^ℂ - α₀ log|·|`, so `μ_h = |z|^{-γ α₀} μ_H` off `0`).
Source: Duplantier-Sheffield, Ann. Probab. 2011 (LQG measures as vague limits, Prop. 1.1, and the Weyl change of
variables); Bou-Rabee-Gwynne, arXiv:2208.11795, p. 9, (2.6) and Fact 2.1 (III). -/
def LocalLQGInsertionWeylOffOriginLP : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ lam : Ω → Measure ℂ),
    ∀ _hGFF : IsWholePlaneGFF P hC hcirc, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ _hlam : IsLQGMeasureOfField P γ 0 hcirc lam,
    ∀ᵐ ω ∂P, ∀ s : Set ℂ, MeasurableSet s → (0 : ℂ) ∉ s →
      lam ω s = ∫⁻ z in s, ENNReal.ofReal (‖z‖ ^ (γ * α₀)) ∂(μ ω)

/-- **Weyl relation off the origin, hypothesis-free (derived).** `LocalLQGInsertionWeylOffOrigin`
(`FirstPass/Frozen/S8c.lean`) holds with no hypotheses. Almost surely, the no-insertion measure `lam` of the
whole-plane GFF satisfies `lam = |z|^{γ α₀} μ` on the complement of `0`, where `μ` has insertion `α₀`. Steps 1-4 are
`ae_integral_eq_rpow_of_isLQGMeasureOfField`; Steps 5-6 are `eq_withDensity_offOrigin_of_integral_eq`
(`FirstPass/S8c/WeylOffOriginRadon.lean`), applied for each ω in the common conull set (Step 7). -/
theorem localLQGInsertionWeylOffOrigin_lp : LocalLQGInsertionWeylOffOriginLP.{u} := by
  intro Ω _ P _ γ α₀ _hC hcirc μ lam hGFF _hγ0 _hγ2 _hα hμ hlam
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  have hlam' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (lam ω) := hlam
  have hw : ContinuousOn (fun z : ℂ => ‖z‖ ^ (γ * α₀)) {0}ᶜ := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    exact ((continuous_norm.continuousAt (x := z)).rpow_const
      (Or.inl (norm_ne_zero_iff.2 hz0))).continuousWithinAt
  have hw0 : ∀ z : ℂ, 0 ≤ ‖z‖ ^ (γ * α₀) := fun z => Real.rpow_nonneg (norm_nonneg z) _
  filter_upwards [ae_integral_eq_rpow_of_isLQGMeasureOfField hGFF hμ hlam, hμ', hlam']
    with ω hω hμω hlamω
  intro s hs h0s
  have := hlamω.isLocallyFiniteMeasure
  have := hμω.isLocallyFiniteMeasure
  exact eq_withDensity_offOrigin_of_integral_eq
    (w := fun z : ℂ => ‖z‖ ^ (γ * α₀)) hw hw0 hω s hs h0s

end LatticeProb.LQG.WeylOffOriginDerived
