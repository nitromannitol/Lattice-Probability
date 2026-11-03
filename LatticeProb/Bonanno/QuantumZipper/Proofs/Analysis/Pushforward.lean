/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Analysis.Pushforward at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Pushforward of measures and densities under injective holomorphic maps

Self-contained complex-analysis / measure-theory facts about an injective holomorphic map
`f : ℂ → ℂ` with nonvanishing derivative on an open set `U`, used for the change of
variables `z ↦ f z` (Theorem 1.2, reverse coupling):

* `abs_det_fderiv_eq_normSq`: the real Jacobian determinant of `f` is `‖f'‖²`.
* `lintegral_comp_holo`: the induced change-of-variables formula for the Lebesgue integral.
* `map_withDensity_eq`: the pushforward of a density supported on `s ⊆ U` under `f`.
* `bounded_density`: a uniform bound for that pushforward density on compact sets.
* `log_dist_comparison`: a two-sided comparison of `log‖f x - f y‖` with `log‖x - y‖`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace QuantumZipper

/-- The determinant of the real Fréchet derivative of a function complex-differentiable at
`z` equals the squared norm of its complex derivative. This is the standard fact that
multiplication by a complex number `c`, viewed as an `ℝ`-linear self-map of `ℂ`, has
determinant `Complex.normSq c = ‖c‖ ^ 2`. -/
theorem abs_det_fderiv_eq_normSq {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    |(fderiv ℝ f z).det| = ‖deriv f z‖ ^ 2 := by
  have hrs : fderiv ℝ f z = (fderiv ℂ f z).restrictScalars ℝ :=
    hf.fderiv_restrictScalars (𝕜 := ℝ)
  have hval : (fderiv ℂ f z : ℂ →ₗ[ℂ] ℂ).det = deriv f z := by
    rw [LinearMap.det_ring]; rfl
  have hd : (fderiv ℝ f z).det = Complex.normSq (deriv f z) := by
    rw [hrs]
    show LinearMap.det (((fderiv ℂ f z).restrictScalars ℝ : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = _
    rw [ContinuousLinearMap.coe_restrictScalars, LinearMap.det_restrictScalars, hval,
      Algebra.norm_complex_apply]
  rw [hd, Complex.normSq_eq_norm_sq]
  exact abs_of_nonneg (sq_nonneg _)

section Setup

variable {U : Set ℂ} {f : ℂ → ℂ}

/-- Under the standing hypotheses, `f` has a real Fréchet derivative within any subset of
`U` at every point of that subset. -/
private theorem hasFDerivWithinAt_of_holo (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {s : Set ℂ} (hsU : s ⊆ U) : ∀ z ∈ s, HasFDerivWithinAt f (fderiv ℝ f z) s z := by
  intro z hz
  have hzU : z ∈ U := hsU hz
  have hdiff : DifferentiableAt ℂ f z := hf.differentiableAt (hU.mem_nhds hzU)
  exact hdiff.real_of_complex.hasFDerivAt.hasFDerivWithinAt

/-- Change of variables for the Lebesgue integral along an injective holomorphic map: the
Jacobian is `‖f'‖²`. -/
theorem lintegral_comp_holo (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : Set.InjOn f U) (hderiv : ∀ z ∈ U, deriv f z ≠ 0)
    {s : Set ℂ} (hs : MeasurableSet s) (hsU : s ⊆ U) (g : ℂ → ℝ≥0∞) :
    ∫⁻ w in f '' s, g w = ∫⁻ z in s, ENNReal.ofReal (‖deriv f z‖ ^ 2) * g (f z) := by
  have hfd := hasFDerivWithinAt_of_holo hU hf hsU
  have hinjs : Set.InjOn f s := hinj.mono hsU
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hfd hinjs g]
  apply setLIntegral_congr_fun hs
  intro z hz
  show ENNReal.ofReal |(fderiv ℝ f z).det| * g (f z) = ENNReal.ofReal (‖deriv f z‖ ^ 2) * g (f z)
  rw [abs_det_fderiv_eq_normSq (hf.differentiableAt (hU.mem_nhds (hsU hz)))]

/-- A helper: if `h` vanishes outside `t₀`, the integral of `h` over `t` equals the integral
of `h` over `t₀ ∩ t`. -/
private theorem setLIntegral_eq_inter_of_vanishing {h : ℂ → ℝ≥0∞} {t t₀ : Set ℂ}
    (ht : MeasurableSet t) (ht0 : MeasurableSet t₀) (hh : ∀ z, z ∉ t₀ → h z = 0) :
    ∫⁻ z in t, h z ∂volume = ∫⁻ z in t₀ ∩ t, h z ∂volume := by
  have heq : t.indicator h = (t₀ ∩ t).indicator h := by
    funext z
    by_cases hz : z ∈ t <;> by_cases hz0 : z ∈ t₀ <;> simp [hz, hz0, hh]
  rw [← lintegral_indicator ht, ← lintegral_indicator (ht0.inter ht), heq]

/-- The density on `f '' s` obtained by pushing forward `ρ` (a density supported on `s`)
along the injective holomorphic map `f`: the Jacobian `‖f'‖²` divides out. -/
def pushDensity (f : ℂ → ℂ) (s : Set ℂ) (ρ : ℂ → ℝ≥0∞) : ℂ → ℝ≥0∞ :=
  Set.indicator (f '' s) fun w =>
    ρ (Function.invFunOn f s w) / ENNReal.ofReal (‖deriv f (Function.invFunOn f s w)‖ ^ 2)

theorem pushDensity_eq_zero_of_not_mem {s : Set ℂ} {ρ : ℂ → ℝ≥0∞} {w : ℂ}
    (hw : w ∉ f '' s) : pushDensity f s ρ w = 0 :=
  Set.indicator_of_notMem hw _

/-- The pushforward of the measure `volume.withDensity ρ` (with `ρ` supported on `s ⊆ U`)
along `f` is again a Lebesgue density, given by `pushDensity`. -/
theorem map_withDensity_eq (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : Set.InjOn f U) (hfm : Measurable f) (hderiv : ∀ z ∈ U, deriv f z ≠ 0)
    {s : Set ℂ} (hs : MeasurableSet s) (hsU : s ⊆ U)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) (hρs : ∀ z, z ∉ s → ρ z = 0) :
    (volume.withDensity ρ).map f = volume.withDensity (pushDensity f s ρ) := by
  have hinjs : Set.InjOn f s := hinj.mono hsU
  have hleft := hinjs.leftInvOn_invFunOn
  have hfderiv := hasFDerivWithinAt_of_holo hU hf hsU
  have hfs_meas : MeasurableSet (f '' s) := measurable_image_of_fderivWithin hs hfderiv hinjs
  apply Measure.ext
  intro A hA
  have hs' : MeasurableSet (s ∩ f ⁻¹' A) := hs.inter (hfm hA)
  have step1 : (volume.withDensity ρ).map f A = ∫⁻ z in s ∩ f ⁻¹' A, ρ z ∂volume := by
    rw [Measure.map_apply hfm hA, withDensity_apply _ (hfm hA)]
    exact setLIntegral_eq_inter_of_vanishing (hfm hA) hs hρs
  have step2 : ∫⁻ z in s ∩ f ⁻¹' A, ρ z ∂volume
      = ∫⁻ z in s ∩ f ⁻¹' A, ENNReal.ofReal (‖deriv f z‖ ^ 2) * pushDensity f s ρ (f z) := by
    apply setLIntegral_congr_fun hs'
    intro z hz
    obtain ⟨hzs, -⟩ := hz
    have hzU : z ∈ U := hsU hzs
    have hne0 : deriv f z ≠ 0 := hderiv z hzU
    have hpos : (0 : ℝ) < ‖deriv f z‖ ^ 2 := by
      have := norm_pos_iff.mpr hne0; positivity
    have hane : ENNReal.ofReal (‖deriv f z‖ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
    have hatop : ENNReal.ofReal (‖deriv f z‖ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmem : f z ∈ f '' s := ⟨z, hzs, rfl⟩
    have hinv : Function.invFunOn f s (f z) = z := hleft hzs
    show ρ z = ENNReal.ofReal (‖deriv f z‖ ^ 2) * pushDensity f s ρ (f z)
    unfold pushDensity
    rw [Set.indicator_of_mem hmem, hinv, ENNReal.mul_div_cancel hane hatop]
  have step3 : ∫⁻ z in s ∩ f ⁻¹' A, ENNReal.ofReal (‖deriv f z‖ ^ 2) * pushDensity f s ρ (f z)
      = ∫⁻ w in f '' (s ∩ f ⁻¹' A), pushDensity f s ρ w :=
    (lintegral_comp_holo hU hf hinj hderiv hs' (Set.inter_subset_left.trans hsU)
      (pushDensity f s ρ)).symm
  have step4 : f '' (s ∩ f ⁻¹' A) = f '' s ∩ A := Set.image_inter_preimage f s A
  have step5 : ∫⁻ w in f '' s ∩ A, pushDensity f s ρ w
      = ∫⁻ w in A, pushDensity f s ρ w :=
    (setLIntegral_eq_inter_of_vanishing hA hfs_meas
      (fun w hw => pushDensity_eq_zero_of_not_mem hw)).symm
  have step6 : volume.withDensity (pushDensity f s ρ) A = ∫⁻ w in A, pushDensity f s ρ w :=
    withDensity_apply _ hA
  rw [step1, step2, step3, step4, step5, step6]

/-- On a compact `K ⊆ U` containing `s`, with `ρ` bounded by `M` on `s`, the pushforward
density is bounded by `M / c` where `c` is the (positive) minimum of `‖f'‖²` on `K`, and it
vanishes outside the compact set `f '' K`. -/
theorem bounded_density (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : Set.InjOn f U) (hderiv : ∀ z ∈ U, deriv f z ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    {s : Set ℂ} (hsK : s ⊆ K)
    {ρ : ℂ → ℝ≥0∞} (hρs : ∀ z, z ∉ s → ρ z = 0)
    {M : ℝ≥0∞} (hρM : ∀ z ∈ s, ρ z ≤ M) :
    ∃ c : ℝ, 0 < c ∧ (∀ w, pushDensity f s ρ w ≤ M / ENNReal.ofReal c) ∧
      IsCompact (f '' K) ∧ ∀ w, w ∉ f '' K → pushDensity f s ρ w = 0 := by
  have hsU : s ⊆ U := hsK.trans hKU
  have hcontK : ContinuousOn f K := hf.continuousOn.mono hKU
  have hfK_compact : IsCompact (f '' K) := hK.image_of_continuousOn hcontK
  have hderivcont : ContinuousOn (deriv f) U :=
    (hf.contDiffOn (n := (1 : ℕ∞)) hU).continuousOn_deriv_of_isOpen hU le_rfl
  have hvanish : ∀ w, w ∉ f '' K → pushDensity f s ρ w = 0 := by
    intro w hw
    exact pushDensity_eq_zero_of_not_mem (fun hmem => hw (Set.image_mono hsK hmem))
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, fun w => ?_, hfK_compact, hvanish⟩
    have hse : s = ∅ := Set.subset_eq_empty hsK hKe
    have : pushDensity f s ρ w = 0 :=
      pushDensity_eq_zero_of_not_mem (by rw [hse, Set.image_empty]; simp)
    rw [this]; exact bot_le
  · have hcontsq : ContinuousOn (fun z => ‖deriv f z‖ ^ 2) K :=
      ((hderivcont.mono hKU).norm).pow 2
    obtain ⟨z₀, hz₀K, hz₀min⟩ := hK.exists_isMinOn hKne hcontsq
    have hz₀U : z₀ ∈ U := hKU hz₀K
    have hcpos : 0 < ‖deriv f z₀‖ ^ 2 := by
      have := norm_pos_iff.mpr (hderiv z₀ hz₀U); positivity
    refine ⟨‖deriv f z₀‖ ^ 2, hcpos, fun w => ?_, hfK_compact, hvanish⟩
    by_cases hw : w ∈ f '' s
    · obtain ⟨z, hzs, rfl⟩ := hw
      have hzK : z ∈ K := hsK hzs
      have hzU : z ∈ U := hKU hzK
      have hcle : ‖deriv f z₀‖ ^ 2 ≤ ‖deriv f z‖ ^ 2 := hz₀min hzK
      have hinv : Function.invFunOn f s (f z) = z := (hinj.mono hsU).leftInvOn_invFunOn hzs
      have hmem2 : f z ∈ f '' s := ⟨z, hzs, rfl⟩
      show pushDensity f s ρ (f z) ≤ M / ENNReal.ofReal (‖deriv f z₀‖ ^ 2)
      unfold pushDensity
      rw [Set.indicator_of_mem hmem2, hinv]
      exact ENNReal.div_le_div (hρM z hzs) (ENNReal.ofReal_le_ofReal hcle)
    · rw [pushDensity_eq_zero_of_not_mem hw]; exact bot_le

/-- On a compact `K ⊆ U`, `f` is bi-Lipschitz in the logarithmic sense: `log‖f x - f y‖`
and `log‖x - y‖` differ by at most a constant `C`, for distinct `x, y ∈ K`. -/
theorem log_dist_comparison (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : Set.InjOn f U) (hderiv : ∀ z ∈ U, deriv f z ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, x ≠ y →
      |Real.log ‖f x - f y‖ - Real.log ‖x - y‖| ≤ C := by
  -- Step 1: an upper Lipschitz bound on `K`, from local `C¹`-ness of holomorphic maps.
  have hlocLip : LocallyLipschitzOn U f := by
    intro z hz
    have hCD : ContDiffAt ℂ 1 f z := (hf.contDiffOn hU).contDiffAt (hU.mem_nhds hz)
    obtain ⟨K', t, ht, hLip⟩ := hCD.exists_lipschitzOnWith
    exact ⟨K', t, mem_nhdsWithin_of_mem_nhds ht, hLip⟩
  obtain ⟨C₀, hC₀⟩ := (hlocLip.mono hKU).exists_lipschitzOnWith_of_compact hK
  set C₁ : ℝ := max (C₀ : ℝ) 1 with hC1_def
  have hC1pos : 0 < C₁ := lt_max_of_lt_right one_pos
  have hUpper : ∀ x ∈ K, ∀ y ∈ K, ‖f x - f y‖ ≤ C₁ * ‖x - y‖ := by
    intro x hx y hy
    have hd := hC₀.dist_le_mul x hx y hy
    simp only [Complex.dist_eq] at hd
    calc ‖f x - f y‖ ≤ (C₀ : ℝ) * ‖x - y‖ := hd
      _ ≤ C₁ * ‖x - y‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  -- Step 2: a lower bound on `K`, by a sequential-compactness contradiction argument.
  have hLower : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ y ∈ K, c * ‖x - y‖ ≤ ‖f x - f y‖ := by
    by_contra hcon
    push_neg at hcon
    have key : ∀ n : ℕ, ∃ x ∈ K, ∃ y ∈ K, ‖f x - f y‖ < (1 / (n + 1) : ℝ) * ‖x - y‖ := by
      intro n
      obtain ⟨x, hx, y, hy, hxy⟩ := hcon (1 / (n + 1)) (by positivity)
      exact ⟨x, hx, y, hy, hxy⟩
    choose xs hxs ys hys hlt using key
    have hmem : ∀ n, (xs n, ys n) ∈ K ×ˢ K := fun n => ⟨hxs n, hys n⟩
    obtain ⟨⟨x, y⟩, hxy, φ, hφmono, hφtend⟩ := (hK.prod hK).isSeqCompact hmem
    have hxtend : Tendsto (fun n => xs (φ n)) atTop (𝓝 x) :=
      (continuous_fst.tendsto _).comp hφtend
    have hytend : Tendsto (fun n => ys (φ n)) atTop (𝓝 y) :=
      (continuous_snd.tendsto _).comp hφtend
    have hxK : x ∈ K := hxy.1
    have hyK : y ∈ K := hxy.2
    have hφreal : Tendsto (fun n => (φ n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hφmono.tendsto_atTop
    have hφplus1 : Tendsto (fun n => (φ n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 hφreal
    have hratio0 : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hφplus1
    rcases eq_or_ne x y with hxy' | hxy'
    · -- Diagonal case: contradict the nonvanishing strict derivative at `x`.
      subst hxy'
      have hzU : x ∈ U := hKU hxK
      have hstrict : HasStrictDerivAt f (deriv f x) x := by
        have hCD : ContDiffAt ℂ 1 f x := (hf.contDiffOn hU).contDiffAt (hU.mem_nhds hzU)
        exact hCD.hasStrictDerivAt one_ne_zero
      have hd0 : deriv f x ≠ 0 := hderiv x hzU
      have hdpos : 0 < ‖deriv f x‖ := norm_pos_iff.mpr hd0
      have hlO := hstrict.hasStrictFDerivAt.isLittleO
      have hev1 : ∀ᶠ n in atTop,
          ‖f (xs (φ n)) - f (ys (φ n)) -
              (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f x))
                (xs (φ n) - ys (φ n))‖ ≤ (‖deriv f x‖ / 2) * ‖xs (φ n) - ys (φ n)‖ :=
        hφtend.eventually (hlO.def (show (0:ℝ) < ‖deriv f x‖ / 2 by linarith))
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
        smul_eq_mul] at hev1
      have hev2 : ∀ᶠ n in atTop, (1 / ((φ n : ℝ) + 1)) < ‖deriv f x‖ / 2 :=
        (tendsto_order.mp hratio0).2 _ (by linarith)
      obtain ⟨n, h1, h2⟩ := (hev1.and hev2).exists
      have key2 : (‖deriv f x‖ / 2) * ‖xs (φ n) - ys (φ n)‖ ≤ ‖f (xs (φ n)) - f (ys (φ n))‖ := by
        have htri := norm_sub_norm_le ((xs (φ n) - ys (φ n)) * deriv f x)
          (f (xs (φ n)) - f (ys (φ n)))
        rw [norm_sub_rev ((xs (φ n) - ys (φ n)) * deriv f x) (f (xs (φ n)) - f (ys (φ n))),
          norm_mul] at htri
        linarith [htri, h1]
      have hfinal :
          (‖deriv f x‖ / 2) * ‖xs (φ n) - ys (φ n)‖ <
            (‖deriv f x‖ / 2) * ‖xs (φ n) - ys (φ n)‖ :=
        calc (‖deriv f x‖ / 2) * ‖xs (φ n) - ys (φ n)‖
            ≤ ‖f (xs (φ n)) - f (ys (φ n))‖ := key2
          _ < (1 / ((φ n : ℝ) + 1)) * ‖xs (φ n) - ys (φ n)‖ := hlt (φ n)
          _ ≤ (‖deriv f x‖ / 2) * ‖xs (φ n) - ys (φ n)‖ :=
              mul_le_mul_of_nonneg_right h2.le (norm_nonneg _)
      exact absurd hfinal (lt_irrefl _)
    · -- Off-diagonal case: contradict injectivity via continuity.
      have hcontf : ContinuousOn f U := hf.continuousOn
      have hfx : Tendsto (fun n => f (xs (φ n))) atTop (𝓝 (f x)) :=
        (hcontf.continuousAt (hU.mem_nhds (hKU hxK))).tendsto.comp hxtend
      have hfy : Tendsto (fun n => f (ys (φ n))) atTop (𝓝 (f y)) :=
        (hcontf.continuousAt (hU.mem_nhds (hKU hyK))).tendsto.comp hytend
      have hnum : Tendsto (fun n => ‖f (xs (φ n)) - f (ys (φ n))‖) atTop (𝓝 ‖f x - f y‖) :=
        (hfx.sub hfy).norm
      have hden : Tendsto (fun n => ‖xs (φ n) - ys (φ n)‖) atTop (𝓝 ‖x - y‖) :=
        (hxtend.sub hytend).norm
      have hrhs0 : Tendsto (fun n => (1 / ((φ n : ℝ) + 1)) * ‖xs (φ n) - ys (φ n)‖) atTop (𝓝 0) := by
        have := hratio0.mul hden
        simpa using this
      have hle : ‖f x - f y‖ ≤ 0 := by
        apply le_of_tendsto_of_tendsto hnum hrhs0
        filter_upwards with n
        exact (hlt (φ n)).le
      have hfxfy : f x = f y := sub_eq_zero.mp (norm_le_zero_iff.mp hle)
      exact hxy' (hinj (hKU hxK) (hKU hyK) hfxfy)
  obtain ⟨c, hcpos, hLower'⟩ := hLower
  refine ⟨max (Real.log C₁) (-Real.log c), fun x hx y hy hxyne => ?_⟩
  have hxyne' : x - y ≠ 0 := sub_ne_zero.mpr hxyne
  have hdistpos : 0 < ‖x - y‖ := norm_pos_iff.mpr hxyne'
  have hfxyne : f x ≠ f y := fun h => hxyne (hinj (hKU hx) (hKU hy) h)
  have hfdistpos : 0 < ‖f x - f y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hfxyne)
  have hub : ‖f x - f y‖ / ‖x - y‖ ≤ C₁ := by
    rw [div_le_iff₀ hdistpos]; exact hUpper x hx y hy
  have hlb : c ≤ ‖f x - f y‖ / ‖x - y‖ := by
    rw [le_div_iff₀ hdistpos]; exact hLower' x hx y hy
  have hlog_ub : Real.log ‖f x - f y‖ - Real.log ‖x - y‖ ≤ Real.log C₁ := by
    rw [← Real.log_div (ne_of_gt hfdistpos) (ne_of_gt hdistpos)]
    exact (Real.log_le_log_iff (div_pos hfdistpos hdistpos) hC1pos).mpr hub
  have hlog_lb : Real.log c ≤ Real.log ‖f x - f y‖ - Real.log ‖x - y‖ := by
    rw [← Real.log_div (ne_of_gt hfdistpos) (ne_of_gt hdistpos)]
    exact (Real.log_le_log_iff hcpos (div_pos hfdistpos hdistpos)).mpr hlb
  rw [abs_le]
  exact ⟨by linarith [le_max_right (Real.log C₁) (-Real.log c)],
    by linarith [le_max_left (Real.log C₁) (-Real.log c)]⟩

end Setup

end QuantumZipper
