/-
The exponential family and its derivative under the integral sign.

Taken into the library from the parking model's support files, where they
were developed: the bounds on the increment of the exponential
(`abs_exp_sub_exp_le`, `mul_exp_le_exp_div`, `abs_exp_sub_exp_bound`) and
the differentiation of `s ↦ ∫ e^{s S} f` within `Set.Ici 0` are generic
analysis, with no parking content, and every model that differentiates an
exponential moment will want them.
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

namespace LatticeProb

open MeasureTheory Filter Topology Set


/-- **The increment of the exponential.**  `|e^a - e^b| ≤ |a - b| e^{a ∨ b}`. -/
theorem abs_exp_sub_exp_le (a b : ℝ) :
    |Real.exp a - Real.exp b| ≤ |a - b| * Real.exp (max a b) := by
  rcases le_total b a with h | h
  · rw [max_eq_left h]
    have h1 : Real.exp b ≤ Real.exp a := Real.exp_le_exp.mpr h
    have h2 : (b - a) + 1 ≤ Real.exp (b - a) := Real.add_one_le_exp (b - a)
    have h3 : Real.exp (b - a) * Real.exp a = Real.exp b := by
      rw [← Real.exp_add]; ring_nf
    have h4 : (0 : ℝ) < Real.exp a := Real.exp_pos a
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.exp a - Real.exp b),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)]
    nlinarith [h2, h3, h4]
  · rw [max_eq_right h]
    have h1 : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr h
    have h2 : (a - b) + 1 ≤ Real.exp (a - b) := Real.add_one_le_exp (a - b)
    have h3 : Real.exp (a - b) * Real.exp b = Real.exp a := by
      rw [← Real.exp_add]; ring_nf
    have h4 : (0 : ℝ) < Real.exp b := Real.exp_pos b
    rw [abs_of_nonpos (by linarith : Real.exp a - Real.exp b ≤ 0),
      abs_of_nonpos (by linarith : a - b ≤ 0)]
    nlinarith [h2, h3, h4]

/-- **A factor of `x` costs an arbitrarily small increase of the rate.** -/
theorem mul_exp_le_exp_div {x s t : ℝ} (hst : s < t) :
    x * Real.exp (s * x) ≤ Real.exp (t * x) / (t - s) := by
  have hts : (0 : ℝ) < t - s := by linarith
  have h1 : (t - s) * x + 1 ≤ Real.exp ((t - s) * x) := Real.add_one_le_exp ((t - s) * x)
  have h2 : Real.exp ((t - s) * x) * Real.exp (s * x) = Real.exp (t * x) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : (0 : ℝ) < Real.exp (s * x) := Real.exp_pos (s * x)
  rw [le_div_iff₀ hts]
  nlinarith [h1, h2, h3, Real.exp_pos ((t - s) * x)]

/-- **The dominating bound for the difference quotients of the tilt.**  For
`0 ≤ lam, s ≤ s₁ < θ` the increment of `s ↦ e^{sx}` is at most `|s - lam|`
times a function of `x` alone that is integrable whenever `e^{θ x}` and `|x|`
are. -/
theorem abs_exp_sub_exp_bound {θ s₁ lam s : ℝ} (h1 : s₁ < θ) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ s₁) (hs0 : 0 ≤ s) (hs1 : s ≤ s₁) (x : ℝ) :
    |Real.exp (s * x) - Real.exp (lam * x)|
      ≤ |s - lam| * (Real.exp (θ * x) / (θ - s₁) + |x|) := by
  have hbase := abs_exp_sub_exp_le (s * x) (lam * x)
  have hfac : |s * x - lam * x| = |s - lam| * |x| := by rw [← sub_mul, abs_mul]
  have habs : (0 : ℝ) ≤ |s - lam| := abs_nonneg _
  have hts : (0 : ℝ) < θ - s₁ := by linarith
  rcases le_or_gt 0 x with hx | hx
  · have hmax : max (s * x) (lam * x) ≤ s₁ * x :=
      max_le (mul_le_mul_of_nonneg_right hs1 hx) (mul_le_mul_of_nonneg_right hlam1 hx)
    have hexp : Real.exp (max (s * x) (lam * x)) ≤ Real.exp (s₁ * x) := Real.exp_le_exp.mpr hmax
    have hE2 : x * Real.exp (s₁ * x) ≤ Real.exp (θ * x) / (θ - s₁) := mul_exp_le_exp_div h1
    have hxabs : |x| = x := abs_of_nonneg hx
    have hstep : |s * x - lam * x| * Real.exp (max (s * x) (lam * x))
        ≤ |s - lam| * (x * Real.exp (s₁ * x)) := by
      rw [hfac, hxabs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hx) habs
    nlinarith [hbase, hstep, hE2, habs, abs_nonneg x]
  · have hs' : s * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0 (le_of_lt hx)
    have hl' : lam * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam0 (le_of_lt hx)
    have hexp : Real.exp (max (s * x) (lam * x)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (max_le hs' hl')
    have hpos : (0 : ℝ) ≤ Real.exp (θ * x) / (θ - s₁) :=
      div_nonneg (Real.exp_nonneg _) (le_of_lt hts)
    have hstep : |s * x - lam * x| * Real.exp (max (s * x) (lam * x)) ≤ |s - lam| * |x| := by
      rw [hfac]
      exact mul_le_of_le_one_right (mul_nonneg habs (abs_nonneg x)) hexp
    nlinarith [hbase, hstep, habs, hpos, abs_nonneg x]


variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}


variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **A bounded observable against the exponential weight is integrable.**
Below the threshold `θ` of the exponential moment the weight `e^{s S}` is
dominated by `1 + e^{θ S}`. -/
theorem integrable_exp_mul_bdd [IsFiniteMeasure P] {S : Ω → ℝ} (hSm : Measurable S) {θ : ℝ}
    (hexp : Integrable (fun ω => Real.exp (θ * S ω)) P)
    {f : Ω → ℝ} (hfm : Measurable f) (hfb : ∀ ω, |f ω| ≤ 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hsθ : s ≤ θ) :
    Integrable (fun ω => Real.exp (s * S ω) * f ω) P := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hexp)
    (((Real.measurable_exp.comp (measurable_const.mul hSm)).mul hfm)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have hpos : (0 : ℝ) < Real.exp (s * S ω) := Real.exp_pos _
  have hθ : (0 : ℝ) < Real.exp (θ * S ω) := Real.exp_pos _
  have hfb1 : |f ω| ≤ 1 := hfb ω
  have hmain : Real.exp (s * S ω) ≤ 1 + Real.exp (θ * S ω) := by
    rcases le_or_gt 0 (S ω) with hk | hk
    · have h1 : s * S ω ≤ θ * S ω := mul_le_mul_of_nonneg_right hsθ hk
      have h2 : Real.exp (s * S ω) ≤ Real.exp (θ * S ω) := Real.exp_le_exp.mpr h1
      linarith
    · have h1 : s * S ω ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0 (le_of_lt hk)
      have h2 : Real.exp (s * S ω) ≤ 1 := Real.exp_le_one_iff.mpr h1
      linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
  simp only [Pi.add_apply]
  nlinarith [hpos, hθ, hfb1, abs_nonneg (f ω)]

/-- **Differentiating the exponential family within `[0, ∞)`.**  For a bounded
observable `f` and a variable `S` with a right exponential moment of order `θ`
and an absolute first moment, the map `s ↦ ∫ e^{s S} f` has derivative
`∫ S e^{λ S} f` within `Set.Ici 0` at every `λ ∈ [0, θ)`. -/
theorem hasDerivWithinAt_integral_exp [IsFiniteMeasure P]
    {S : Ω → ℝ} (hSm : Measurable S) {θ : ℝ}
    (hexp : Integrable (fun ω => Real.exp (θ * S ω)) P)
    (hint : Integrable (fun ω => |S ω|) P)
    {f : Ω → ℝ} (hfm : Measurable f) (hfb : ∀ ω, |f ω| ≤ 1)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamθ : lam < θ) :
    HasDerivWithinAt (fun s => ∫ ω, Real.exp (s * S ω) * f ω ∂P)
      (∫ ω, S ω * Real.exp (lam * S ω) * f ω ∂P) (Set.Ici 0) lam := by
  classical
  set s₁ : ℝ := (lam + θ) / 2 with hs₁def
  have hlams₁ : lam < s₁ := by rw [hs₁def]; linarith
  have hs₁θ : s₁ < θ := by rw [hs₁def]; linarith
  have hs₁0 : 0 ≤ s₁ := by linarith
  set l : Filter ℝ := 𝓝[Set.Ici (0:ℝ) \ {lam}] lam with hldef
  set bnd : Ω → ℝ := fun ω => Real.exp (θ * S ω) / (θ - s₁) + |S ω| with hbnddef
  have hbndint : Integrable bnd P := (hexp.div_const _).add hint
  have hFmeas : ∀ s : ℝ, Measurable (fun ω => (s - lam)⁻¹ *
      (Real.exp (s * S ω) * f ω - Real.exp (lam * S ω) * f ω)) := by
    intro s
    exact measurable_const.mul
      ((((Real.measurable_exp.comp (measurable_const.mul hSm)).mul hfm)).sub
        (((Real.measurable_exp.comp (measurable_const.mul hSm)).mul hfm)))
  have hfilt : l ≤ 𝓝[≠] lam := by
    rw [hldef]
    exact nhdsWithin_mono _ (fun x hx => hx.2)
  have hev : ∀ᶠ s in l, 0 ≤ s ∧ s ≤ s₁ ∧ s ≠ lam := by
    have h1 : ∀ᶠ s in l, s ∈ Set.Ici (0:ℝ) \ {lam} := self_mem_nhdsWithin
    have h2 : ∀ᶠ s in l, s < s₁ :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hlams₁)
    filter_upwards [h1, h2] with s hs hlt
    exact ⟨hs.1, le_of_lt hlt, hs.2⟩
  have hslope : ∀ᶠ s in l, slope (fun s => ∫ ω, Real.exp (s * S ω) * f ω ∂P) lam s
      = ∫ ω, (s - lam)⁻¹ * (Real.exp (s * S ω) * f ω - Real.exp (lam * S ω) * f ω) ∂P := by
    filter_upwards [hev] with s hs
    have hI1 : Integrable (fun ω => Real.exp (s * S ω) * f ω) P :=
      integrable_exp_mul_bdd hSm hexp hfm hfb hs.1 (le_of_lt (lt_of_le_of_lt hs.2.1 hs₁θ))
    have hI2 : Integrable (fun ω => Real.exp (lam * S ω) * f ω) P :=
      integrable_exp_mul_bdd hSm hexp hfm hfb hlam0 (le_of_lt hlamθ)
    rw [integral_const_mul, integral_sub hI1 hI2]
    simp [slope_def_field, div_eq_inv_mul]
  have hlim : Tendsto (fun s => ∫ ω, (s - lam)⁻¹ *
      (Real.exp (s * S ω) * f ω - Real.exp (lam * S ω) * f ω) ∂P) l
      (𝓝 (∫ ω, S ω * Real.exp (lam * S ω) * f ω ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence bnd
      (Filter.Eventually.of_forall fun s => (hFmeas s).aestronglyMeasurable) ?_ hbndint ?_
    · filter_upwards [hev] with s hs
      refine Filter.Eventually.of_forall fun ω => ?_
      have hne : s - lam ≠ 0 := sub_ne_zero_of_ne hs.2.2
      have hkey := abs_exp_sub_exp_bound hs₁θ hlam0 (le_of_lt hlams₁) hs.1 hs.2.1 (S ω)
      have hfw : |f ω| ≤ 1 := hfb ω
      have hbpos : 0 ≤ bnd ω := by
        rw [hbnddef]
        exact add_nonneg (div_nonneg (Real.exp_nonneg _) (by linarith)) (abs_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_inv, ← sub_mul, abs_mul]
      have h1 : |Real.exp (s * S ω) - Real.exp (lam * S ω)| * |f ω|
          ≤ |s - lam| * bnd ω := by
        calc |Real.exp (s * S ω) - Real.exp (lam * S ω)| * |f ω|
            ≤ (|s - lam| * bnd ω) * 1 := by
              refine mul_le_mul hkey hfw (abs_nonneg _) ?_
              exact mul_nonneg (abs_nonneg _) hbpos
          _ = |s - lam| * bnd ω := by ring
      have habs : 0 < |s - lam| := abs_pos.mpr hne
      have hcancel : |s - lam|⁻¹ * (|s - lam| * bnd ω) = bnd ω := by field_simp
      rw [← hcancel]
      exact mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr habs))
    · refine Filter.Eventually.of_forall fun ω => ?_
      have hd : HasDerivAt (fun s : ℝ => Real.exp (s * S ω) * f ω)
          (S ω * Real.exp (lam * S ω) * f ω) lam := by
        have h1 : HasDerivAt (fun s : ℝ => s * S ω) (S ω) lam := by
          simpa using (hasDerivAt_id lam).mul_const (S ω)
        have h2 : HasDerivAt (fun s : ℝ => Real.exp (s * S ω))
            (Real.exp (lam * S ω) * S ω) lam := h1.exp
        have h3 := h2.mul_const (f ω)
        have heq : Real.exp (lam * S ω) * S ω * f ω = S ω * Real.exp (lam * S ω) * f ω := by
          ring
        rwa [heq] at h3
      have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left hfilt
      refine hs.congr fun s => ?_
      simp [slope_def_field, div_eq_inv_mul, mul_sub]
  rw [hasDerivWithinAt_iff_tendsto_slope]
  exact hlim.congr' (hslope.mono fun s hs => hs.symm)

end LatticeProb

end