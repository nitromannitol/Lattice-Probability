/-
The integration step of the Herbst argument.

`LatticeProb.Prob.HerbstFromLSI` proves that the Gaussian log-Sobolev inequality
gives the entropy bound `Ent(h_λ) ≤(λ L)² / 2` for the tilted density
`h_λ = exp(λ (f - ∫f)) / M(λ)` of an `L`-Lipschitz functional `f`, where
`M(λ) = ∫ exp(λ (f - ∫f))` is the moment generating function of `f - ∫f`.
Writing `P = log M`, that entropy bound is `λ P'(λ) - P(λ) ≤ (λ L)² / 2`, the
differential inequality for `M`.

This module finishes the argument.  It differentiates `M` under the integral
sign, turns the entropy bound into `(P(λ)/λ)' ≤ L²/2`, uses the convexity limit
`P(λ)/λ → P'(0) = 0`, and concludes `M(λ) ≤ exp(λ² L² / 2)`, which is
`LatticeProb.GaussianHerbstBound n`.  Together with `HerbstFromLSI` this reduces
the Gaussian Herbst exponential moment bound to the Gaussian log-Sobolev
inequality.

The argument is the classical one of Herbst (1975), as presented in Ledoux,
*The Concentration of Measure Phenomenon*, Section 5.1.
-/
import LatticeProb.Prob.HerbstFromLSI
import LatticeProb.Prob.ConvexOrder

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace LatticeProb

/-- **Differentiation of the moment generating function.**  For an `L`-Lipschitz
`f`, the moment generating function `t ↦ ∫ exp (t (f - ∫f))` of the centred
functional is differentiable, with derivative the corresponding first moment:
`(d/dt) ∫ exp (t (f - ∫f)) = ∫ (f - ∫f) exp (t (f - ∫f))`. -/
theorem hasDerivAt_mgf_centred_lipschitz (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf : LipschitzWith ⟨L, hL.le⟩ f) (lam : ℝ) :
    HasDerivAt (fun t => ∫ x, Real.exp (t * (f x - ∫ y, f y
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      (∫ x, (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        * Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) lam := by
  set g : (Fin n → ℝ) → ℝ := fun x => f x - ∫ y, f y
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) with hg
  have hgL : LipschitzWith ⟨L, hL.le⟩ g := lipschitzWith_sub_integral n f L hL.le hf
  have hgcont : Continuous g := hgL.continuous
  have hc0 : (0 : ℝ) ≤ |lam| + 1 := by positivity
  -- The dominating function `|g| exp ((|lam|+1) |g|)` is integrable.
  have hbound_int : Integrable (fun x => |g x| * Real.exp ((|lam| + 1) * |g x|))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
    have hpos : Integrable (fun x => |g x| * Real.exp ((|lam| + 1) * g x))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
      refine (integrable_mul_exp_sub_integral n f L (|lam| + 1) hL hf).norm.congr ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hneg : Integrable (fun x => |g x| * Real.exp (-(|lam| + 1) * g x))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
      refine (integrable_mul_exp_sub_integral n f L (-(|lam| + 1)) hL hf).norm.congr ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine (hpos.add hneg).mono' ?_ ?_
    · exact (hgcont.abs.mul (Real.continuous_exp.comp
        (continuous_const.mul hgcont.abs))).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]
      simp only [Pi.add_apply]
      rcases le_total 0 (g x) with hx | hx
      · rw [abs_of_nonneg hx]
        exact le_add_of_nonneg_right (mul_nonneg hx (Real.exp_pos _).le)
      · rw [abs_of_nonpos hx]
        rw [show (|lam| + 1) * -g x = -(|lam| + 1) * g x by ring]
        exact le_add_of_nonneg_left (mul_nonneg (neg_nonneg.mpr hx) (Real.exp_pos _).le)
  -- Measurability and integrability of the family.
  have hF_meas : ∀ᶠ t in 𝓝 lam,
      AEStronglyMeasurable (fun x => Real.exp (t * g x))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    Filter.Eventually.of_forall fun t =>
      (Real.continuous_exp.comp (continuous_const.mul hgcont)).aestronglyMeasurable
  have hF_int : Integrable (fun x => Real.exp (lam * g x))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    integrable_exp_sub_integral n f L lam hL hf
  have hF'_meas : AEStronglyMeasurable (fun x => g x * Real.exp (lam * g x))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    (hgcont.mul (Real.continuous_exp.comp (continuous_const.mul hgcont))).aestronglyMeasurable
  have h_diff : ∀ᵐ x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1),
      ∀ t ∈ Set.Ioo (lam - 1) (lam + 1),
        HasDerivAt (fun s => Real.exp (s * g x)) (g x * Real.exp (t * g x)) t := by
    filter_upwards with x
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s * g x) (1 * g x) t :=
      (hasDerivAt_id t).mul_const (g x)
    have h2 := h1.exp
    simpa only [one_mul, mul_comm] using h2
  have h_bound : ∀ᵐ x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1),
      ∀ t ∈ Set.Ioo (lam - 1) (lam + 1),
        ‖g x * Real.exp (t * g x)‖ ≤ |g x| * Real.exp ((|lam| + 1) * |g x|) := by
    filter_upwards with x
    intro t ht
    have htabs : |t| ≤ |lam| + 1 := by
      rw [abs_le]
      constructor
      · have h1 : -(|lam| + 1) ≤ lam - 1 := by
          have := neg_abs_le lam; linarith
        linarith [ht.1]
      · have h2 : lam + 1 ≤ |lam| + 1 := by linarith [le_abs_self lam]
        linarith [ht.2]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hle : t * g x ≤ (|lam| + 1) * |g x| := by
      calc t * g x ≤ |t * g x| := le_abs_self _
        _ = |t| * |g x| := by rw [abs_mul]
        _ ≤ (|lam| + 1) * |g x| := by
            exact mul_le_mul_of_nonneg_right htabs (abs_nonneg _)
    calc |g x| * Real.exp (t * g x) ≤ |g x| * Real.exp ((|lam| + 1) * |g x|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (abs_nonneg _)
      _ = |g x| * Real.exp ((|lam| + 1) * |g x|) := rfl
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.Ioo (lam - 1) (lam + 1))
    (Ioo_mem_nhds (by linarith) (by linarith)) hF_meas hF_int hF'_meas h_bound
    hbound_int h_diff).2



/-- The entropy of the tilted density, written through the moment generating
function: `∫ h_λ log h_λ = λ M'(λ)/M(λ) - log M(λ)` with `M` the moment
generating function of the centred functional. -/
theorem herbstTilt_entropy_eq (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L lam : ℝ) (hL : 0 < L)
    (hf : LipschitzWith ⟨L, hL.le⟩ f) :
    ∫ x, herbstTilt n f lam x * Real.log (herbstTilt n f lam x)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      = lam * ((∫ x, (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
          * Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        / (∫ x, Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
  set M : ℝ := ∫ x, Real.exp (lam * (f x - ∫ y, f y
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) with hM
  set A : ℝ := ∫ x, (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
    * Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) with hA
  have hMpos : 0 < M := mgf_centred_pos n f L lam hL hf
  have hE1 : Integrable (fun x => (f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      * Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    integrable_mul_exp_sub_integral n f L lam hL hf
  have hE2 : Integrable (fun x => Real.exp (lam * (f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    integrable_exp_sub_integral n f L lam hL hf
  have hpt : ∀ x, herbstTilt n f lam x * Real.log (herbstTilt n f lam x)
      = lam * ((f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
          * Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          / M)
        - Real.log M * (Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))) / M) := by
    intro x
    unfold herbstTilt
    rw [← hM, Real.log_div (Real.exp_ne_zero _) hMpos.ne', Real.log_exp]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have h1 : ∫ x, lam * ((f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      * Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      / M) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = lam * (A / M) := by
    rw [integral_const_mul, integral_div, ← hA]
  have h2 : ∫ x, Real.log M * (Real.exp (lam * (f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))) / M)
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = Real.log M := by
    rw [integral_const_mul, integral_div, ← hM, div_self hMpos.ne', mul_one]
  rw [integral_sub (hE1.div_const M |>.const_mul lam) (hE2.div_const M |>.const_mul _),
    h1, h2]

/-- **The differential form of the Herbst argument.**  With `M(λ) = ∫ exp (λ (f - ∫f))`
the moment generating function of the centred functional, the entropy bound
`herbstTilt_entropy_le` reads `λ M'(λ)/M(λ) - log M(λ) ≤ (λ L)² / 2`. -/
theorem herbst_log_deriv_le (n : ℕ) (h : GaussianLogSobolev n) (f : (Fin n → ℝ) → ℝ)
    (L lam : ℝ) (hL : 0 < L) (hf : LipschitzWith ⟨L, hL.le⟩ f) (hlam : 0 < lam) :
    lam * ((∫ x, (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        * Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      / (∫ x, Real.exp (lam * (f x - ∫ y, f y
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      ≤ lam ^ 2 * L ^ 2 / 2 := by
  have hent := herbstTilt_entropy_le n h f L lam hL hf hlam
  rw [herbstTilt_entropy_eq n f L lam hL hf] at hent
  simpa only [mul_pow] using hent

/-- **A function bounded by its derivative.**  If `Q` is continuous on `(0, ∞)`,
differentiable there with `Q' ≤ C`, and tends to `0` at `0⁺`, then
`Q x ≤ C x` for every `x > 0`.  This is the integration step of the Herbst
argument. -/
theorem le_mul_of_hasDerivAt_le {Q : ℝ → ℝ} {C : ℝ}
    (hcont : ContinuousOn Q (Set.Ioi 0))
    (hdiff : ∀ x, 0 < x → ∃ d : ℝ, d ≤ C ∧ HasDerivAt Q d x)
    (hlim : Tendsto Q (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ x, 0 < x → Q x ≤ C * x := by
  have hW : AntitoneOn (fun y => Q y - C * y) (Set.Ioi 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (D := Set.Ioi 0) (convex_Ioi 0)
      (f' := fun y => deriv (fun z => Q z - C * z) y)
      (hcont.sub (continuousOn_const.mul continuousOn_id)) ?_ ?_
    · intro x hx
      rw [interior_Ioi] at hx
      obtain ⟨d, hdC, hd⟩ := hdiff x hx
      have h2 : HasDerivAt (fun y : ℝ => C * y) (C * 1) x := (hasDerivAt_id x).const_mul C
      have h3 : HasDerivAt (fun y : ℝ => Q y - C * y) (d - C * 1) x := hd.sub h2
      rw [h3.deriv]
      exact h3.hasDerivWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      obtain ⟨d, hdC, hd⟩ := hdiff x hx
      have h2 : HasDerivAt (fun y : ℝ => C * y) (C * 1) x := (hasDerivAt_id x).const_mul C
      have h3 : HasDerivAt (fun y : ℝ => Q y - C * y) (d - C * 1) x := hd.sub h2
      rw [h3.deriv]
      linarith
  intro x hx
  have hWlim : Tendsto (fun y => Q y - C * y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => Q y) (𝓝[>] (0 : ℝ)) (𝓝 0) := hlim
    have h2 : Tendsto (fun y : ℝ => C * y) (𝓝[>] (0 : ℝ)) (𝓝 (C * 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds (tendsto_const_nhds.mul tendsto_id)
    simpa using h1.sub h2
  have hlt : ∀ᶠ eps in 𝓝[>] (0 : ℝ), eps < x := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hx] with eps heps _
    exact heps
  have hev : ∀ᶠ eps in 𝓝[>] (0 : ℝ),
      (fun y => Q y - C * y) x ≤ Q eps - C * eps := by
    filter_upwards [hlt, self_mem_nhdsWithin] with eps hepsx hepspos
    exact hW hepspos hx hepsx.le
  have hle : Q x - C * x ≤ 0 := ge_of_tendsto hWlim hev
  linarith

/-- **Herbst's exponential moment bound from an entropy bound for the tilt.**
If the tilted density `h_λ = exp(λ (f - ∫f)) / M(λ)` of an `L`-Lipschitz `f` has
entropy at most `(λ C)² / 2` for every `λ > 0`, then `M(λ) ≤ exp (λ² C² / 2)`.  The
constant `L` is used only to make the exponential moments integrable; the
constant `C` in the conclusion is read off the entropy bound, which is what the
`ℓ²` restatement of the Herbst argument needs. -/
theorem mgf_le_of_entropy_bound (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf : LipschitzWith ⟨L, hL.le⟩ f) (C : ℝ)
    (hent : ∀ lam : ℝ, 0 < lam →
      ∫ x, herbstTilt n f lam x * Real.log (herbstTilt n f lam x)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) ≤ (lam * C) ^ 2 / 2) :
    ∀ lam : ℝ, 0 < lam →
      ∫ x, Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) ≤ Real.exp (lam ^ 2 * C ^ 2 / 2) := by
  intro lam hlam
  set M : ℝ → ℝ := fun t => ∫ x, Real.exp (t * (f x - ∫ y, f y
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) with hM
  set A : ℝ → ℝ := fun t => ∫ x, (f x - ∫ y, f y
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
    * Real.exp (t * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) with hA
  set P : ℝ → ℝ := fun t => Real.log (M t) with hP
  set Q : ℝ → ℝ := fun t => P t / t with hQ
  have hMpos : ∀ t, 0 < M t := fun t => mgf_centred_pos n f L t hL hf
  have hMderiv : ∀ t, HasDerivAt M (A t) t := fun t =>
    hasDerivAt_mgf_centred_lipschitz n f L hL hf t
  have hMcont : Continuous M := continuous_iff_continuousAt.mpr fun t =>
    (hMderiv t).continuousAt
  have hPderiv : ∀ t, HasDerivAt P (A t / M t) t := fun t =>
    (hMderiv t).log (hMpos t).ne'
  have hM0 : M 0 = 1 := by
    have h : M 0 = ∫ x, (1 : ℝ) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
      simp only [hM]
      apply integral_congr_ae
      filter_upwards with x
      simp
    rw [h]
    simp
  have hP0 : P 0 = 0 := by
    simp only [hP, hM0, Real.log_one]
  have hA0 : A 0 = 0 := by
    have hexp_abs : Integrable (fun x : ℝ => Real.exp (1 * |x|)) (gaussianReal 0 1) := by
      have h1 : Integrable (fun x : ℝ => Real.exp (1 * x)) (gaussianReal 0 1) :=
        integrable_exp_mul_gaussianReal 1
      have h2 : Integrable (fun x : ℝ => Real.exp (-1 * x)) (gaussianReal 0 1) :=
        integrable_exp_mul_gaussianReal (-1)
      refine (h1.add h2).mono' ?_ ?_
      · exact (Real.measurable_exp.comp (measurable_id.abs.const_mul 1)).aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        rcases le_total 0 x with hx | hx
        · rw [abs_of_nonneg hx]
          exact le_add_of_nonneg_right (Real.exp_pos _).le
        · rw [abs_of_nonpos hx, show (1 : ℝ) * -x = -1 * x by ring]
          exact le_add_of_nonneg_left (Real.exp_pos _).le
    have hid : Integrable (id : (Fin n → ℝ) → (Fin n → ℝ))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
      ConvexOrder.integrable_id_pi (fun _ : Fin n => gaussianReal 0 1)
        (fun _ => ConvexOrder.integrable_id_of_exp_moment (by norm_num) hexp_abs)
    have hfint : Integrable f (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
      ConvexOrder.integrable_real_lipschitz hf hid
    have h : A 0 = ∫ x, (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
      simp only [hA]
      apply integral_congr_ae
      filter_upwards with x
      simp
    rw [h, integral_sub hfint (integrable_const _)]
    simp
  have hQlim : Tendsto Q (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hPderiv0 : HasDerivAt P 0 0 := by simpa [hA0, hM0] using hPderiv 0
    have hslope : Tendsto Q (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      refine (hPderiv0.tendsto_slope).congr' ?_
      filter_upwards with y
      simp only [hQ, slope_def_module, hP0, sub_zero, smul_eq_mul]
      ring
    exact hslope.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
  have hQcont : ContinuousOn Q (Set.Ioi 0) := by
    intro t ht
    have htne : t ≠ 0 := ne_of_gt ht
    exact (((Real.continuousAt_log (hMpos t).ne').comp hMcont.continuousAt).div
      continuousAt_id htne).continuousWithinAt
  have hdiff : ∀ t, 0 < t →
      ∃ d : ℝ, d ≤ C ^ 2 / 2 ∧ HasDerivAt Q d t := by
    intro t ht
    have htne : t ≠ 0 := ne_of_gt ht
    have hQd : HasDerivAt Q ((A t / M t * t - P t) / t ^ 2) t := by
      have h := (hPderiv t).div (hasDerivAt_id t) htne
      have h' : HasDerivAt (fun y : ℝ => P y / y) ((A t / M t * t - P t) / t ^ 2) t := by
        convert h using 1
        all_goals
          first
          | (ext y; rfl)
          | (simp only [id, mul_one])
      rwa [hQ]
    refine ⟨(A t / M t * t - P t) / t ^ 2, ?_, hQd⟩
    have he := hent t ht
    rw [herbstTilt_entropy_eq n f L t hL hf] at he
    have hEnt' : t * (A t / M t) - P t ≤ t ^ 2 * C ^ 2 / 2 := by
      simpa only [hA, hM, hP, mul_pow] using he
    have hmul : A t / M t * t - P t = t * (A t / M t) - P t := by ring
    rw [hmul, div_le_iff₀ (pow_pos ht 2)]
    nlinarith [hEnt']
  have hQle := le_mul_of_hasDerivAt_le (Q := Q) (C := C ^ 2 / 2) hQcont hdiff hQlim
  have hPle : P lam ≤ lam ^ 2 * C ^ 2 / 2 := by
    have h1 : Q lam ≤ C ^ 2 / 2 * lam := hQle lam hlam
    rw [hQ] at h1
    rw [div_le_iff₀ hlam] at h1
    nlinarith [h1]
  have hPle' : Real.log (M lam) ≤ lam ^ 2 * C ^ 2 / 2 := by simpa only [hP] using hPle
  have hMle : M lam ≤ Real.exp (lam ^ 2 * C ^ 2 / 2) :=
    (Real.log_le_iff_le_exp (hMpos lam)).mp hPle'
  simpa only [hM] using hMle

/-- **Herbst's exponential moment bound from the Gaussian log-Sobolev
inequality.**  If the Gaussian log-Sobolev inequality holds on `Fin n → ℝ`, then
an `L`-Lipschitz functional `f` of `n` independent standard Gaussians has
`∫ exp (λ (f - ∫f)) ≤ exp (λ² L² / 2)` for every `λ > 0`, which is
`LatticeProb.GaussianHerbstBound n`. -/
theorem gaussianHerbstBound_of_gaussianLogSobolev (n : ℕ)
    (h : GaussianLogSobolev n) : GaussianHerbstBound n := by
  intro f L hL hf lam hlam
  exact mgf_le_of_entropy_bound n f L hL hf L
    (fun lam hlam => herbstTilt_entropy_le n h f L lam hL hf hlam) lam hlam

end LatticeProb
