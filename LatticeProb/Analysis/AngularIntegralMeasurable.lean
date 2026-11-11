import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import LatticeProb.Analysis.RadialLocalIntegrability

/-!
# Measurable circle averages of random radial families

For a random radial family `X s ω` (the value at radius `s` of a radial path) and a circle
`θ ↦ z + r e^{iθ}`, this file proves the following.

* `aemeasurable_circle_integral`: for fixed `z` and `r > 0`, the map
  `ω ↦ ∫_{[0,2π]} X |z + r e^{iθ}| ω dθ` is a.e. measurable. The hypotheses are the coordinate
  measurability `Measurable (X s)` for `s > 0` and almost sure continuity of `s ↦ X s ω` on `(0, ∞)`.
  No growth premise is needed for measurability, and circles through zero are included.
* `aemeasurable_circle_average`, `aemeasurable_realCircleAverage`: the normalized integral
  `(2π)⁻¹ ∫_{[0,2π]} ...`, and the same quantity written with Mathlib's `Real.circleAverage`.
* `ae_intervalIntegrable_circle_through_zero`: for a circle through zero (`‖z‖ = r`) and an almost sure
  logarithmic majorant `|X t ω| ≤ C (1 + |log t|)` on `(0, 2r]`, the angular integrand is a.s. interval
  integrable (`intervalIntegrable_radial_circle`), so the normalized integral is a finite average a.s.
* `aemeasurable_circle_radialPath`, `ae_intervalIntegrable_circle_radialPath`: the same for the radial
  path `X s ω = B (-log s) ω` (`t = -log|z|`) of a path `t ↦ B t ω` with a.s. continuous paths and
  sublinear growth.
* `intervalIntegrable_radial_circle` and its helpers: the angular integrability of a logarithmic
  radial singularity on a circle through zero.

Method. The exceptional angles, where the circle meets `0`, form a countable set
(`countable_circleZeroAngles`) and are removed explicitly. The radius is truncated at `1 / (n + 1)`, so
that off a measurable null set `N` of configurations every truncated family is continuous in the radius
for every `ω`. Carathéodory's lemma `measurable_uncurry_of_continuous_of_measurable` gives joint
measurability of each truncation; pointwise convergence gives joint measurability of the limit; and the
strong measurability of parametric integrals (`StronglyMeasurable.integral_prod_right'`) finishes the
proof. A Riemann sum in `θ` takes the value of the family at the singular angle whenever a grid point
hits that angle, so it is not used.

Names follow Armitage-Gardiner, *Classical Potential Theory* (Springer, 2001; spherical and circular means), for radial
means and circle averages, and Duplantier-Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
arXiv:0808.1560, Proposition 3.3, p. 18, for radial parts of the Liouville field.
-/

open MeasureTheory Set Filter Topology Complex

namespace LatticeProb.AngularIntegralMeasurable


/-- Standard circle parametrization through zero.  If `‖z‖ = r`, the circle `θ ↦ z + r e^{iθ}` has
`‖z + r e^{iθ}‖ = r · 2 |sin((θ - arg (-z))/2)|`, and it vanishes at `θ = arg (-z)`. -/
lemma norm_add_mul_exp_eq {z : ℂ} {r : ℝ} (hz : ‖z‖ = r) (θ : ℝ) :
    ‖z + (r : ℂ) * exp (I * θ)‖ = r * (2 * |Real.sin ((θ - arg (-z)) / 2)|) := by
  have ha : (r : ℂ) * exp (I * (arg (-z) : ℂ)) = -z := by
    have h := norm_mul_exp_arg_mul_I (-z)
    rw [norm_neg, hz, mul_comm ((arg (-z) : ℝ) : ℂ) I] at h
    exact h
  have hE : exp (I * (θ : ℂ)) =
      exp (I * (arg (-z) : ℂ)) * exp (I * ((θ - arg (-z) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have key : z + (r : ℂ) * exp (I * (θ : ℂ)) =
      -z * (exp (I * ((θ - arg (-z) : ℝ) : ℂ)) - 1) := by
    linear_combination (r : ℂ) * hE + exp (I * ((θ - arg (-z) : ℝ) : ℂ)) * ha
  rw [key, norm_mul, norm_neg, hz, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul, abs_two]

/-- Logarithmic singularity comparison on a circle through zero: for every `θ`,
`|log ‖z + r e^{iθ}‖| ≤ |log (2r)| + |log |sin((θ - arg (-z))/2)||`.  In Lean `log 0 = 0`, so the
zero of the circle is covered by the same inequality. -/
lemma abs_log_norm_add_mul_exp_le {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) (θ : ℝ) :
    |Real.log ‖z + (r : ℂ) * exp (I * θ)‖| ≤
      |Real.log (2 * r)| + |Real.log (|Real.sin ((θ - arg (-z)) / 2)|)| := by
  rw [norm_add_mul_exp_eq hz]
  by_cases hS : Real.sin ((θ - arg (-z)) / 2) = 0
  · simp [hS]
  · have hpos : 0 < |Real.sin ((θ - arg (-z)) / 2)| := abs_pos.2 hS
    have hfac : r * (2 * |Real.sin ((θ - arg (-z)) / 2)|) =
        2 * r * |Real.sin ((θ - arg (-z)) / 2)| := by ring
    have h2r : 2 * r ≠ 0 := ne_of_gt (by linarith)
    rw [hfac, Real.log_mul h2r hpos.ne']
    exact abs_add_le _ _

/-- For every shift `c`, `θ ↦ |log |sin((θ - c)/2)||` is interval integrable on `[0, 2π]`. -/
lemma intervalIntegrable_abs_log_abs_sin_shift (c : ℝ) :
    IntervalIntegrable (fun θ : ℝ => |Real.log (|Real.sin ((θ - c) / 2)|)|) volume 0
      (2 * Real.pi) := by
  have hF : IntervalIntegrable (fun x : ℝ => Real.log (Real.sin x)) volume (-c / 2)
      ((2 * Real.pi - c) / 2) := intervalIntegrable_log_sin
  have hG : IntervalIntegrable (fun x : ℝ => Real.log (Real.sin (1 / 2 * (x - c)))) volume
      ((-c / 2) / (1 / 2) + c) (((2 * Real.pi - c) / 2) / (1 / 2) + c) :=
    (hF.comp_mul_left (c := 1 / 2)).comp_sub_right c
  rw [show (-c / 2) / (1 / 2) + c = 0 by ring,
    show ((2 * Real.pi - c) / 2) / (1 / 2) + c = 2 * Real.pi by ring] at hG
  have hfun : (fun θ : ℝ => |Real.log (|Real.sin ((θ - c) / 2)|)|) =
      (fun θ : ℝ => |Real.log (Real.sin (1 / 2 * (θ - c)))|) := by
    funext θ
    have h2 : (θ - c) / 2 = 1 / 2 * (θ - c) := by ring
    rw [Real.log_abs, h2]
  rw [hfun]
  exact hG.abs

/-- Angular integrability of the absolute logarithmic singularity: for `r > 0` and `‖z‖ = r`,
`θ ↦ |log ‖z + r e^{iθ}‖|` is interval integrable on `[0, 2π]`. -/
lemma intervalIntegrable_abs_log_norm_add_mul_exp {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) :
    IntervalIntegrable (fun θ : ℝ => |Real.log ‖z + (r : ℂ) * exp (I * θ)‖|) volume 0
      (2 * Real.pi) := by
  have hcont : Continuous fun θ : ℝ => ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ := by fun_prop
  have hmeas : Measurable fun θ : ℝ => |Real.log ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖| :=
    continuous_abs.measurable.comp (Real.measurable_log.comp hcont.measurable)
  refine IntervalIntegrable.mono_fun' (g := fun θ : ℝ =>
      |Real.log (2 * r)| + |Real.log (|Real.sin ((θ - arg (-z)) / 2)|)|) ?_
    hmeas.aestronglyMeasurable ?_
  · exact intervalIntegrable_const.add (intervalIntegrable_abs_log_abs_sin_shift (arg (-z)))
  · refine ae_of_all _ fun θ => ?_
    dsimp only
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_log_norm_add_mul_exp_le hr hz θ

/-- Finiteness of the angular integral of a radial function with logarithmic majorant.  Let
`g` be continuous on `(0, ∞)` with `|g t| ≤ C (1 + |log t|)` for `0 < t ≤ δ`, and let the circle
`θ ↦ z + r e^{iθ}` pass through zero (`‖z‖ = r > 0`) with `2r ≤ δ`.  Then `θ ↦ g ‖z + r e^{iθ}‖`
is interval integrable on `[0, 2π]`.  The circle is Lebesgue-null, so the majorant is used along
the circle itself; the zeros of `θ ↦ sin((θ - arg(-z))/2)` form a countable set. -/
theorem intervalIntegrable_radial_circle {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0)) {C δ : ℝ}
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) (hδ : 2 * r ≤ δ)
    (hbound : ∀ t : ℝ, 0 < t → t ≤ δ → |g t| ≤ C * (1 + |Real.log t|)) :
    IntervalIntegrable (fun θ : ℝ => g ‖z + (r : ℂ) * exp (I * θ)‖) volume 0 (2 * Real.pi) := by
  classical
  have hZc : Set.Countable {θ : ℝ | Real.sin ((θ - arg (-z)) / 2) = 0} := by
    refine (Set.countable_range (fun n : ℤ => arg (-z) + 2 * Real.pi * n)).mono ?_
    intro θ hθ
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 (show Real.sin ((θ - arg (-z)) / 2) = 0 from hθ)
    exact ⟨n, by show arg (-z) + 2 * Real.pi * (n : ℝ) = θ; linear_combination 2 * hn⟩
  have hae : ∀ᵐ (θ : ℝ) ∂(volume : Measure ℝ), θ ∉ {θ : ℝ | Real.sin ((θ - arg (-z)) / 2) = 0} :=
    hZc.ae_notMem volume
  have hae' := ae_restrict_of_ae (s := Set.uIoc 0 (2 * Real.pi)) hae
  have hpos : ∀ θ : ℝ, Real.sin ((θ - arg (-z)) / 2) ≠ 0 → 0 < ‖z + (r : ℂ) * exp (I * θ)‖ := by
    intro θ hS
    rw [norm_add_mul_exp_eq hz]
    exact mul_pos hr (mul_pos two_pos (abs_pos.2 hS))
  have hle2 : ∀ θ : ℝ, ‖z + (r : ℂ) * exp (I * θ)‖ ≤ 2 * r := by
    intro θ
    rw [norm_add_mul_exp_eq hz]
    have hS1 : |Real.sin ((θ - arg (-z)) / 2)| ≤ 1 :=
      abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    nlinarith
  have hcont : Continuous fun θ : ℝ => ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ := by fun_prop
  have hGm : Measurable ((Ioi (0 : ℝ)).piecewise g (fun _ => (0 : ℝ))) :=
    ContinuousOn.measurable_piecewise hg continuousOn_const measurableSet_Ioi
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => g ‖z + (r : ℂ) * exp (I * θ)‖)
      (volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    refine (hGm.comp hcont.measurable).aestronglyMeasurable.congr ?_
    filter_upwards [hae'] with θ hθ
    exact Set.piecewise_eq_of_mem _ _ _ (Set.mem_Ioi.2 (hpos θ hθ))
  have hbd : ∀ᵐ (θ : ℝ) ∂(volume.restrict (Set.uIoc 0 (2 * Real.pi))),
      ‖g (‖z + (r : ℂ) * exp (I * θ)‖)‖ ≤ |C| * (1 + |Real.log (2 * r)|) +
        |C| * |Real.log (|Real.sin ((θ - arg (-z)) / 2)|)| := by
    filter_upwards [hae'] with θ hθ
    have hp := hpos θ hθ
    have hd : ‖z + (r : ℂ) * exp (I * θ)‖ ≤ δ := (hle2 θ).trans hδ
    have h1 := hbound _ hp hd
    have h2 := abs_log_norm_add_mul_exp_le hr hz θ
    rw [Real.norm_eq_abs]
    calc |g ‖z + (r : ℂ) * exp (I * θ)‖|
        ≤ C * (1 + |Real.log ‖z + (r : ℂ) * exp (I * θ)‖|) := h1
      _ ≤ |C| * (1 + |Real.log ‖z + (r : ℂ) * exp (I * θ)‖|) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (1 + (|Real.log (2 * r)| + |Real.log (|Real.sin ((θ - arg (-z)) / 2)|)|)) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
      _ = |C| * (1 + |Real.log (2 * r)|) + |C| * |Real.log (|Real.sin ((θ - arg (-z)) / 2)|)| := by
          ring
  have hint : IntervalIntegrable (fun θ : ℝ => |C| * (1 + |Real.log (2 * r)|) +
      |C| * |Real.log (|Real.sin ((θ - arg (-z)) / 2)|)|) volume 0 (2 * Real.pi) :=
    intervalIntegrable_const.add
      ((intervalIntegrable_abs_log_abs_sin_shift (arg (-z))).const_mul |C|)
  exact IntervalIntegrable.mono_fun' hint hmeas hbd


/-- The exceptional angles of the circle `θ ↦ z + r e^{iθ}`: the angles at which the circle passes
through `0`.  For `r > 0` this set is countable (`countable_circleZeroAngles`), hence null. -/
noncomputable def circleZeroAngles (z : ℂ) (r : ℝ) : Set ℝ :=
  {θ : ℝ | ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ = 0}

/-- For `r > 0` the exceptional angles are countable: two zeros of `θ ↦ z + r e^{iθ}` differ by an
integer multiple of `2π`. -/
lemma countable_circleZeroAngles {z : ℂ} {r : ℝ} (hr : 0 < r) :
    (circleZeroAngles z r).Countable := by
  by_cases hne : (circleZeroAngles z r).Nonempty
  · obtain ⟨θ₀, hθ₀⟩ := hne
    have h₀ : ‖z + (r : ℂ) * exp (I * (θ₀ : ℂ))‖ = 0 := hθ₀
    refine (Set.countable_range (fun n : ℤ => θ₀ + 2 * Real.pi * n)).mono ?_
    intro θ hθ
    have h₁ : ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ = 0 := hθ
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hexp : exp (I * (θ : ℂ)) = exp (I * (θ₀ : ℂ)) := by
      apply mul_left_cancel₀ hr0
      linear_combination (norm_eq_zero.1 h₁) - (norm_eq_zero.1 h₀)
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp
    have hI : I * (θ : ℂ) = I * ((θ₀ + 2 * Real.pi * n : ℝ) : ℂ) := by
      push_cast
      linear_combination hn
    have hθc : (θ : ℂ) = ((θ₀ + 2 * Real.pi * n : ℝ) : ℂ) :=
      mul_left_cancel₀ Complex.I_ne_zero hI
    exact ⟨n, (Complex.ofReal_injective hθc).symm⟩
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]
    exact Set.countable_empty

/-- The exceptional angles are Lebesgue-null when `r > 0`. -/
lemma volume_circleZeroAngles {z : ℂ} {r : ℝ} (hr : 0 < r) :
    volume (circleZeroAngles z r) = 0 :=
  (countable_circleZeroAngles hr).measure_zero volume

/-- The complement of the exceptional angles is measurable when `r > 0`. -/
lemma measurableSet_circleZeroAngles_compl {z : ℂ} {r : ℝ} (hr : 0 < r) :
    MeasurableSet (circleZeroAngles z r)ᶜ :=
  (countable_circleZeroAngles hr).measurableSet.compl

/-- Joint measurability of the truncated radial family `(s, ω) ↦ 1_{Nᶜ}(ω) X (max s a) ω`.  Here `N` is
a measurable set off which `s ↦ X s ω` is continuous on `(0, ∞)`, and `a > 0` is the truncation level.
The truncation keeps the radius in `[a, ∞) ⊆ (0, ∞)`, so each `ω`-slice is continuous on all of `ℝ`,
and Carathéodory's lemma applies.  Only the radii `max s a > 0` are evaluated. -/
lemma measurable_truncated_radial {Ω : Type*} [MeasurableSpace Ω] {X : ℝ → Ω → ℝ}
    (hXm : ∀ s : ℝ, 0 < s → Measurable fun ω => X s ω) {N : Set Ω} (hN : MeasurableSet N)
    (hNc : ∀ ω, ω ∉ N → ContinuousOn (fun s => X s ω) (Ioi 0)) {a : ℝ} (ha : 0 < a) :
    Measurable fun q : ℝ × Ω => Nᶜ.indicator (fun ω => X (max q.1 a) ω) q.2 := by
  have hcont : ∀ ω : Ω, Continuous fun s : ℝ => Nᶜ.indicator (fun ω' => X (max s a) ω') ω := by
    intro ω
    by_cases hω : ω ∈ N
    · have h0 : (fun s : ℝ => Nᶜ.indicator (fun ω' => X (max s a) ω') ω) = fun _ => 0 := by
        funext s
        exact Set.indicator_of_notMem (show ω ∉ Nᶜ by simpa using hω) _
      rw [h0]
      exact continuous_const
    · have h1 : (fun s : ℝ => Nᶜ.indicator (fun ω' => X (max s a) ω') ω) =
          fun s : ℝ => X (max s a) ω := by
        funext s
        exact Set.indicator_of_mem (show ω ∈ Nᶜ from hω) _
      rw [h1]
      exact (hNc ω hω).comp_continuous (by fun_prop) fun s => lt_of_lt_of_le ha (le_max_right s a)
  have hmeas : ∀ s : ℝ, Measurable fun ω => Nᶜ.indicator (fun ω' => X (max s a) ω') ω :=
    fun s => (hXm (max s a) (lt_of_lt_of_le ha (le_max_right s a))).indicator hN.compl
  exact measurable_uncurry_of_continuous_of_measurable
    (u := fun s ω => Nᶜ.indicator (fun ω' => X (max s a) ω') ω) hcont hmeas

/-- The truncated circle integrand on `Ω × ℝ` at level `n`: the value `1_{Nᶜ}(ω) X (max |z + r e^{iθ}|
(1/(n+1))) ω` at `(ω, θ)`, with the exceptional angles removed. -/
noncomputable def truncatedCircleIntegrand {Ω : Type*} (X : ℝ → Ω → ℝ) (N : Set Ω) (z : ℂ) (r : ℝ)
    (n : ℕ) : Ω × ℝ → ℝ :=
  (Prod.snd ⁻¹' (circleZeroAngles z r)ᶜ).indicator fun q : Ω × ℝ =>
    Nᶜ.indicator (fun ω => X (max ‖z + (r : ℂ) * exp (I * (q.2 : ℂ))‖ (1 / ((n : ℝ) + 1))) ω) q.1

/-- The circle integrand on `Ω × ℝ`: the value `1_{Nᶜ}(ω) X |z + r e^{iθ}| ω` at `(ω, θ)` for `θ` off the
exceptional angles, and `0` on them. -/
noncomputable def circleIntegrandLimit {Ω : Type*} (X : ℝ → Ω → ℝ) (N : Set Ω) (z : ℂ) (r : ℝ) :
    Ω × ℝ → ℝ :=
  (Prod.snd ⁻¹' (circleZeroAngles z r)ᶜ).indicator fun q : Ω × ℝ =>
    Nᶜ.indicator (fun ω => X ‖z + (r : ℂ) * exp (I * (q.2 : ℂ))‖ ω) q.1

/-- Each truncated circle integrand is jointly measurable on `Ω × ℝ`. -/
lemma measurable_truncatedCircleIntegrand {Ω : Type*} [MeasurableSpace Ω] {X : ℝ → Ω → ℝ}
    (hXm : ∀ s : ℝ, 0 < s → Measurable fun ω => X s ω) {N : Set Ω} (hN : MeasurableSet N)
    (hNc : ∀ ω, ω ∉ N → ContinuousOn (fun s => X s ω) (Ioi 0)) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (n : ℕ) : Measurable (truncatedCircleIntegrand X N z r n) := by
  have hT := measurable_truncated_radial hXm hN hNc (a := 1 / ((n : ℝ) + 1)) (by positivity)
  have hs : Measurable fun θ : ℝ => ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ := by fun_prop
  have hc : Measurable fun p : Ω × ℝ => (‖z + (r : ℂ) * exp (I * (p.2 : ℂ))‖, p.1) :=
    (hs.comp measurable_snd).prodMk measurable_fst
  have hI : Measurable fun p : Ω × ℝ =>
      Nᶜ.indicator (fun ω => X (max ‖z + (r : ℂ) * exp (I * (p.2 : ℂ))‖ (1 / ((n : ℝ) + 1))) ω) p.1 :=
    hT.comp hc
  exact hI.indicator (measurable_snd (measurableSet_circleZeroAngles_compl hr))

/-- **Fixed-circle measurability.**  Let `X s ω` be a radial family with measurable coordinates
`ω ↦ X s ω` for `s > 0` and almost surely continuous radius `s ↦ X s ω` on `(0, ∞)`.  For fixed `z` and
`r > 0` the circle integral `ω ↦ ∫_{[0,2π]} X |z + r e^{iθ}| ω dθ` is a.e. measurable.  Circles through
zero are included: the exceptional angles are countable and removed. -/
theorem aemeasurable_circle_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ → Ω → ℝ) (hXm : ∀ s : ℝ, 0 < s → Measurable fun ω => X s ω)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun s => X s ω) (Ioi 0)) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun ω => ∫ θ in Icc 0 (2 * Real.pi), X ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ ω) P := by
  obtain ⟨N, hNs, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hXc)
  have hNc : ∀ ω, ω ∉ N → ContinuousOn (fun s => X s ω) (Ioi 0) := fun ω hω => by
    by_contra h
    exact hω (hNs h)
  have hae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hN0
  -- pointwise convergence of the truncations, off the exceptional angles
  have hconv : ∀ p : Ω × ℝ, Tendsto (fun n : ℕ => truncatedCircleIntegrand X N z r n p) atTop
      (𝓝 (circleIntegrandLimit X N z r p)) := by
    intro p
    by_cases hp : p.2 ∈ circleZeroAngles z r
    · have hpE : p ∉ Prod.snd ⁻¹' (circleZeroAngles z r)ᶜ := fun h => h hp
      have h1 : ∀ n : ℕ, truncatedCircleIntegrand X N z r n p = 0 := fun n =>
        Set.indicator_of_notMem hpE _
      rw [show circleIntegrandLimit X N z r p = 0 from Set.indicator_of_notMem hpE _]
      simp only [h1]
      exact tendsto_const_nhds
    · have hpE : p ∈ Prod.snd ⁻¹' (circleZeroAngles z r)ᶜ := hp
      have hpos : 0 < ‖z + (r : ℂ) * exp (I * (p.2 : ℂ))‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hp)
      obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hpos
      have hev : ∀ n : ℕ, N₀ ≤ n → circleIntegrandLimit X N z r p =
          truncatedCircleIntegrand X N z r n p := by
        intro n hn
        have hcast : (N₀ : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
        have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N₀ : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        have hmax : max ‖z + (r : ℂ) * exp (I * (p.2 : ℂ))‖ (1 / ((n : ℝ) + 1)) =
            ‖z + (r : ℂ) * exp (I * (p.2 : ℂ))‖ := max_eq_left (by linarith)
        unfold truncatedCircleIntegrand circleIntegrandLimit
        simp only [Set.indicator_of_mem hpE, hmax]
      exact tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨N₀, fun n hn => hev n hn⟩)
  have hLm : Measurable (circleIntegrandLimit X N z r) :=
    measurable_of_tendsto_metrizable
      (fun n => measurable_truncatedCircleIntegrand (z := z) (r := r) hXm hNm hNc hr n)
      (tendsto_pi_nhds.2 hconv)
  have hF : StronglyMeasurable fun ω =>
      ∫ θ, circleIntegrandLimit X N z r (ω, θ) ∂(volume.restrict (Icc 0 (2 * Real.pi))) :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Icc 0 (2 * Real.pi)))
      hLm.stronglyMeasurable
  have hagree : (fun ω => ∫ θ in Icc 0 (2 * Real.pi), X ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ ω) =ᵐ[P]
      fun ω => ∫ θ, circleIntegrandLimit X N z r (ω, θ) ∂(volume.restrict (Icc 0 (2 * Real.pi))) := by
    filter_upwards [hae] with ω hω
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae ((countable_circleZeroAngles hr).ae_notMem volume)] with θ hθ
    have hθE : (ω, θ) ∈ Prod.snd ⁻¹' (circleZeroAngles z r)ᶜ := hθ
    have hωN : ω ∈ Nᶜ := hω
    show X ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ ω = circleIntegrandLimit X N z r (ω, θ)
    unfold circleIntegrandLimit
    simp only [Set.indicator_of_mem hθE, Set.indicator_of_mem hωN]
  exact AEMeasurable.congr hF.measurable.aemeasurable hagree.symm

/-- **Normalized circle average.**  The normalized integral `(2π)⁻¹ ∫_{[0,2π]} X |z + r e^{iθ}| ω dθ`,
the angular average of the radial family is a.e. measurable for
fixed `z` and `r > 0`. -/
theorem aemeasurable_circle_average {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ → Ω → ℝ) (hXm : ∀ s : ℝ, 0 < s → Measurable fun ω => X s ω)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun s => X s ω) (Ioi 0)) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun ω => (2 * Real.pi)⁻¹ *
      ∫ θ in Icc 0 (2 * Real.pi), X ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ ω) P :=
  (aemeasurable_circle_integral P X hXm hXc z hr).const_mul _

/-- Mathlib's circle average of a radial function, `Real.circleAverage (fun x ↦ f ‖x‖) z r =
(2π)⁻¹ ∫_0^{2π} f |circleMap z r θ|`, rewritten with the parametrization `z + r e^{iθ}` and the
integral over `[0, 2π]` (the interval and the closed interval differ by a null set). -/
lemma circleAverage_eq_normalized (f : ℝ → ℝ) (z : ℂ) (r : ℝ) :
    Real.circleAverage (fun x : ℂ => f ‖x‖) z r =
      (2 * Real.pi)⁻¹ * ∫ θ in Icc 0 (2 * Real.pi), f ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ := by
  have hfun : ∀ θ : ℝ, f ‖circleMap z r θ‖ = f ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ := fun θ => by
    rw [circleMap, mul_comm (θ : ℂ) Complex.I]
  rw [Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    integral_Icc_eq_integral_Ioc]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun θ => hfun θ)

/-- **Radial circle average.**  For a radial family with measurable coordinates on `(0, ∞)` and a.s.
continuity there, the circle average `ω ↦ Real.circleAverage (fun x ↦ X ‖x‖ ω) z r`
is a.e. measurable for `r > 0`. -/
theorem aemeasurable_realCircleAverage {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ → Ω → ℝ) (hXm : ∀ s : ℝ, 0 < s → Measurable fun ω => X s ω)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun s => X s ω) (Ioi 0)) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun ω => Real.circleAverage (fun x : ℂ => X ‖x‖ ω) z r) P := by
  have heq : (fun ω => Real.circleAverage (fun x : ℂ => X ‖x‖ ω) z r) =
      fun ω => (2 * Real.pi)⁻¹ * ∫ θ in Icc 0 (2 * Real.pi), X ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ ω := by
    funext ω
    exact circleAverage_eq_normalized (fun s => X s ω) z r
  rw [heq]
  exact aemeasurable_circle_average P X hXm hXc z hr

/-- **Circles through zero.**  If `‖z‖ = r` and the radial family has the logarithmic majorant
`|X t ω| ≤ C (1 + |log t|)` on `(0, 2r]` almost surely, then the angular integrand
`θ ↦ X |z + r e^{iθ}| ω` is a.s. interval integrable on `[0, 2π]`.  The logarithmic singularity at the
exceptional angle is integrable (`intervalIntegrable_radial_circle`), so the normalized integral is a
finite average almost surely.  Without this majorant the Bochner integral is only measurable by the
convention `∫ = 0` on non-integrable sections. -/
theorem ae_intervalIntegrable_circle_through_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ → Ω → ℝ) (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun s => X s ω) (Ioi 0)) {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hz : ‖z‖ = r)
    (hlog : ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 2 * r → |X t ω| ≤ C * (1 + |Real.log t|)) :
    ∀ᵐ ω ∂P, IntervalIntegrable (fun θ : ℝ => X ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ ω)
      volume 0 (2 * Real.pi) := by
  filter_upwards [hXc, hlog] with ω hωc hωl
  obtain ⟨C, hC⟩ := hωl
  exact intervalIntegrable_radial_circle hωc hr hz (le_refl (2 * r)) hC

/-- Radial path: the family `s ↦ B (-log s)` is a.s. continuous on `(0, ∞)` when `t ↦ B t ω` is
a.s. continuous (`t = -log|z|`). -/
lemma ae_continuousOn_log_radialPath {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ → Ω → ℝ} (hcont : ∀ᵐ ω ∂P, Continuous fun t : ℝ => B t ω) :
    ∀ᵐ ω ∂P, ContinuousOn (fun s : ℝ => B (-Real.log s) ω) (Ioi 0) := by
  have hlogc : ContinuousOn (fun s : ℝ => -Real.log s) (Ioi 0) :=
    (Real.continuousOn_log.mono fun s (hs : 0 < s) => Set.mem_compl_singleton_iff.2 hs.ne').neg
  filter_upwards [hcont] with ω hω
  exact hω.comp_continuousOn hlogc

/-- **Radial path, normalized circle average.**  For a radial path `B` with measurable coordinates
`ω ↦ B t ω` and a.s. continuous `t ↦ B t ω`, the normalized angular average
`(2π)⁻¹ ∫_{[0,2π]} B (-log |z + r e^{iθ}|) ω dθ` is a.e. measurable for fixed `z` and `r > 0`. -/
theorem aemeasurable_circle_radialPath {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ → Ω → ℝ) (hBm : ∀ t : ℝ, Measurable fun ω => B t ω)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t : ℝ => B t ω) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun ω => (2 * Real.pi)⁻¹ *
      ∫ θ in Icc 0 (2 * Real.pi), B (-Real.log ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖) ω) P :=
  aemeasurable_circle_average P (fun s ω => B (-Real.log s) ω) (fun s _ => hBm (-Real.log s))
    (ae_continuousOn_log_radialPath hcont) z hr

/-- Sublinear growth gives the logarithmic majorant on `(0, 2r]` for the radial path, when `2r ≤ 1`
(then `-log t ≥ 0` for `0 < t ≤ 2r`).  The growth is a sublinear bound `o(t)`,
as a premise `hsub`; the linear envelope is `exists_abs_le_mul_one_add_of_sublinear`. -/
lemma ae_log_majorant_radialPath {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ → Ω → ℝ} {r : ℝ} (hr2 : 2 * r ≤ 1) (hcont : ∀ᵐ ω ∂P, Continuous fun t : ℝ => B t ω)
    (hsub : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => B t ω / t) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 2 * r →
      |B (-Real.log t) ω| ≤ C * (1 + |Real.log t|) := by
  filter_upwards [hcont, hsub] with ω hωc hωs
  obtain ⟨C, -, hC⟩ := LatticeProb.RadialLocalIntegrability.exists_abs_le_mul_one_add_of_sublinear hωc hωs
  refine ⟨C, fun t ht0 ht1 => ?_⟩
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le (by linarith)
  rw [abs_of_nonpos hlog]
  exact hC (-Real.log t) (by linarith)

/-- **Radial path, circles through zero.**  For a radial path with a.s. continuous `t ↦ B t ω` and
sublinear growth `B t ω / t → 0`, and for a circle through zero (`‖z‖ = r`, `2r ≤ 1`), the angular
integrand `θ ↦ B (-log |z + r e^{iθ}|) ω` is a.s. interval integrable on `[0, 2π]`. -/
theorem ae_intervalIntegrable_circle_radialPath {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ → Ω → ℝ) (hcont : ∀ᵐ ω ∂P, Continuous fun t : ℝ => B t ω)
    (hsub : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => B t ω / t) atTop (𝓝 0)) {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hr2 : 2 * r ≤ 1) (hz : ‖z‖ = r) :
    ∀ᵐ ω ∂P, IntervalIntegrable
      (fun θ : ℝ => B (-Real.log ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖) ω) volume 0 (2 * Real.pi) :=
  ae_intervalIntegrable_circle_through_zero P (fun s ω => B (-Real.log s) ω)
    (ae_continuousOn_log_radialPath hcont) hr hz (ae_log_majorant_radialPath hr2 hcont hsub)


end LatticeProb.AngularIntegralMeasurable
