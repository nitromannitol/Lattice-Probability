/-
Karamata's theorem at the origin, and the reciprocal of an integrated tail.

The companion of `LatticeProb.Prob.Karamata`, which treats `∫_t^∞` of a function regularly
varying of index `-α` with `α > 1`.  Here the integral runs from the ORIGIN: for `F`
regularly varying of index `ρ > -1`,

  `∫_0^t F ∼ t F t / (ρ + 1)`.

The proof is the substitution `r = t u`, which turns `∫_0^t F` into `t ∫_0^1 F (t u) du`.  The
ratio `F (t u) / F t` converges to `u ^ ρ` for each fixed `u` by regular variation, and for a
MONOTONE INCREASING `F` the domination needed to pass to the limit is free: `0 ≤ F (t u) ≤ F t`
for `u ≤ 1`, so the integrand is bounded by the constant `1`, which is integrable on `(0, 1]`.
This is why no Potter bound is needed on this side, in contrast with the tail integral, where
the domination at `u → ∞` is exactly what Potter's bounds supply.  The hypothesis `ρ > -1` is
used only to evaluate `∫_0^1 u ^ ρ du = 1 / (ρ + 1)`.

The consumer of the file is the reciprocal of an integrated tail.  If the lower tail
`F t = P(X < -t)` of a law is regularly varying of index `-α` with `α > 1`, then the integrated
tail `I t = E (-X - t)_+` is regularly varying of index `1 - α` and antitone, so `1 / I` is
monotone increasing and regularly varying of index `α - 1 > -1`.  Karamata at the origin gives
`∫_0^t (1 / I) ∼ t / (α I t)`, and `I t ∼ t F t / (α - 1)` (Karamata for the tail integral, in
`LatticeProb.Prob.Karamata`) converts that into

  `P(X < -t) ∫_0^t dr / E (-X - r)_+ → 1 - 1 / α`.

The reference for the statement is Bingham, Goldie and Teugels, Theorem 1.5.11, or de Haan and
Ferreira, Theorem B.1.5.
-/
import Mathlib
import LatticeProb.Prob.RegularVariation
import LatticeProb.Prob.Karamata

open Filter Topology MeasureTheory Set

namespace LatticeProb

/-- A monotone increasing nonnegative function is integrable on every interval `(0, t]`: it is
bounded there by its value at the right end point. -/
theorem integrableOn_Ioc_of_monotone_nonneg {F : ℝ → ℝ} (hmono : Monotone F)
    (hnn : ∀ r, 0 ≤ F r) (t : ℝ) : IntegrableOn F (Ioc 0 t) := by
  have hmeas : Measurable F := hmono.measurable
  have hconst : IntegrableOn (fun _ : ℝ => F t) (Ioc 0 t) :=
    integrableOn_const measure_Ioc_lt_top.ne
  refine Integrable.mono' hconst hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun r hr => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn r)]
  exact hmono hr.2

/-- The substitution `r = t u` on the interval `(0, t]`. -/
theorem integral_Ioc_zero_scale (F : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ u in Ioc (0:ℝ) 1, F (t * u) = t⁻¹ * ∫ r in Ioc (0:ℝ) t, F r := by
  have h := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := (1:ℝ)) F (ne_of_gt ht)
  rw [mul_zero, mul_one, smul_eq_mul] at h
  rw [← intervalIntegral.integral_of_le (zero_le_one : (0:ℝ) ≤ 1),
    ← intervalIntegral.integral_of_le ht.le]
  exact h

/-- The limit integral of Karamata's theorem at the origin: `∫_0^1 u ^ ρ du = 1 / (ρ + 1)`,
which is where `ρ > -1` is used. -/
theorem integral_Ioc_zero_one_rpow {ρ : ℝ} (hρ : -1 < ρ) :
    ∫ u in Ioc (0:ℝ) 1, u ^ ρ = 1 / (ρ + 1) := by
  rw [← intervalIntegral.integral_of_le (zero_le_one : (0:ℝ) ≤ 1), integral_rpow (Or.inl hρ),
    Real.one_rpow, Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < ρ + 1))]
  ring

/-- The reciprocal of a regularly varying function is regularly varying with the opposite
index.  No positivity is needed: the ratio limit `lam ^ ρ` is never zero. -/
theorem regularlyVaryingAtTop_inv {f : ℝ → ℝ} {ρ : ℝ} (hf : RegularlyVaryingAtTop f ρ) :
    RegularlyVaryingAtTop (fun t => (f t)⁻¹) (-ρ) := by
  intro lam hlam
  have h := (hf lam hlam).inv₀ (ne_of_gt (Real.rpow_pos_of_pos hlam ρ))
  rw [← Real.rpow_neg hlam.le] at h
  refine h.congr fun r => ?_
  rw [inv_div, inv_div_inv]

/-- The heart of Karamata's theorem at the origin, after the substitution `r = t u`: the
average `∫_0^1 F (t u) / F t du` converges to `∫_0^1 u ^ ρ du`.  For a monotone increasing
nonnegative `F` the integrand lies in `[0, 1]`, so the constant `1` dominates it. -/
theorem karamata_origin_ratio {F : ℝ → ℝ} {ρ : ℝ} (hρ : -1 < ρ)
    (hmono : Monotone F) (hnn : ∀ r, 0 ≤ F r) (hF : RegularlyVaryingAtTop F ρ) :
    Tendsto (fun t : ℝ => ∫ u in Ioc (0:ℝ) 1, F (t * u) / F t) atTop (𝓝 (1 / (ρ + 1))) := by
  have hpos : ∀ᶠ r in atTop, 0 < F r := eventually_pos_of_regularlyVarying hF hnn
  have hbint : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioc (0:ℝ) 1) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hdct : Tendsto (fun t : ℝ => ∫ u in Ioc (0:ℝ) 1, F (t * u) / F t) atTop
      (𝓝 (∫ u in Ioc (0:ℝ) 1, u ^ ρ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (1:ℝ)) ?_ ?_ hbint ?_
    · exact Filter.Eventually.of_forall fun t =>
        ((hmono.measurable.comp (measurable_id.const_mul t)).div_const (F t)).aestronglyMeasurable
    · filter_upwards [hpos, eventually_gt_atTop (0:ℝ)] with t hFt ht0
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hnn _) (hnn t)), div_le_one hFt]
      exact hmono (mul_le_of_le_one_right ht0.le hu.2)
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
      exact (hF u hu.1).congr fun r => by rw [mul_comm u r]
  rwa [integral_Ioc_zero_one_rpow hρ] at hdct

/-- **Karamata's theorem at the origin**, for a monotone increasing nonnegative function:
`∫_0^t F ∼ t F t / (ρ + 1)` for `F` regularly varying of index `ρ > -1`. -/
theorem karamata_origin_integral_nonneg {F : ℝ → ℝ} {ρ : ℝ} (hρ : -1 < ρ)
    (hmono : Monotone F) (hnn : ∀ r, 0 ≤ F r) (hF : RegularlyVaryingAtTop F ρ) :
    Tendsto (fun t : ℝ => (∫ r in Ioc (0:ℝ) t, F r) / (t * F t)) atTop (𝓝 (1 / (ρ + 1))) := by
  have hpos : ∀ᶠ r in atTop, 0 < F r := eventually_pos_of_regularlyVarying hF hnn
  refine (karamata_origin_ratio hρ hmono hnn hF).congr' ?_
  filter_upwards [hpos, eventually_gt_atTop (0:ℝ)] with t hFt ht0
  rw [integral_div, integral_Ioc_zero_scale F ht0]
  field_simp

/-- Truncating a regularly varying function at zero changes nothing at infinity: on the half
line where the function is positive the truncation agrees with it. -/
theorem regularlyVaryingAtTop_max_zero {F : ℝ → ℝ} {ρ A : ℝ}
    (hFA : ∀ x, A ≤ x → 0 < F x) (hF : RegularlyVaryingAtTop F ρ) :
    RegularlyVaryingAtTop (fun r => max (F r) 0) ρ := by
  intro lam hlam
  refine (hF lam hlam).congr' ?_
  filter_upwards [eventually_ge_atTop A, eventually_ge_atTop (A / lam)] with r h1 h2
  have h3 : A ≤ lam * r := by
    have h4 := (div_le_iff₀ hlam).mp h2
    linarith [h4]
  rw [max_eq_left (hFA r h1).le, max_eq_left (hFA (lam * r) h3).le]

/-- The truncation changes the integral from the origin by a constant, fixed once the upper
limit passes the level beyond which the function is positive. -/
theorem integral_Ioc_max_zero_eq {F : ℝ → ℝ} {A : ℝ} (hA : 0 < A) (hmono : Monotone F)
    (hFA : ∀ x, A ≤ x → 0 < F x) (hint : ∀ t, IntegrableOn F (Ioc 0 t)) {t : ℝ} (hAt : A ≤ t) :
    ∫ r in Ioc (0:ℝ) t, max (F r) 0
      = (∫ r in Ioc (0:ℝ) A, max (F r) 0) - (∫ r in Ioc (0:ℝ) A, F r)
        + ∫ r in Ioc (0:ℝ) t, F r := by
  have hmono' : Monotone (fun r : ℝ => max (F r) 0) := fun a b hab => max_le_max (hmono hab) le_rfl
  have hnn' : ∀ r : ℝ, 0 ≤ max (F r) 0 := fun r => le_max_right _ _
  have hsub : Ioc (0:ℝ) A ⊆ Ioc (0:ℝ) t := Ioc_subset_Ioc_right hAt
  have hsub2 : Ioc A t ⊆ Ioc (0:ℝ) t := Ioc_subset_Ioc_left hA.le
  have hdisj : Disjoint (Ioc (0:ℝ) A) (Ioc A t) := Ioc_disjoint_Ioc_of_le le_rfl
  have hunion : Ioc (0:ℝ) A ∪ Ioc A t = Ioc (0:ℝ) t := Ioc_union_Ioc_eq_Ioc hA.le hAt
  have h1 : ∫ r in Ioc (0:ℝ) t, F r = (∫ r in Ioc (0:ℝ) A, F r) + ∫ r in Ioc A t, F r := by
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioc ((hint t).mono_set hsub)
      ((hint t).mono_set hsub2)]
  have h2 : ∫ r in Ioc (0:ℝ) t, max (F r) 0
      = (∫ r in Ioc (0:ℝ) A, max (F r) 0) + ∫ r in Ioc A t, max (F r) 0 := by
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioc
      ((integrableOn_Ioc_of_monotone_nonneg hmono' hnn' t).mono_set hsub)
      ((integrableOn_Ioc_of_monotone_nonneg hmono' hnn' t).mono_set hsub2)]
  have h3 : ∫ r in Ioc A t, max (F r) 0 = ∫ r in Ioc A t, F r :=
    setIntegral_congr_fun measurableSet_Ioc fun r hr => max_eq_left (hFA r hr.1.le).le
  rw [h1, h2, h3]
  ring

/-- A monotone increasing function that is eventually positive has `t F t → ∞`, which is what
makes the truncation constant negligible. -/
theorem tendsto_mul_self_atTop_of_pos {F : ℝ → ℝ} {A : ℝ} (hmono : Monotone F)
    (hFA : ∀ x, A ≤ x → 0 < F x) : Tendsto (fun t : ℝ => t * F t) atTop atTop := by
  have hFApos : 0 < F A := hFA A le_rfl
  have hlin : Tendsto (fun t : ℝ => t * F A) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hFApos
  refine tendsto_atTop_mono' atTop ?_ hlin
  filter_upwards [eventually_ge_atTop A, eventually_ge_atTop (0:ℝ)] with t h1 h2
  exact mul_le_mul_of_nonneg_left (hmono h1) h2

/-- **Karamata's theorem at the origin** (Bingham, Goldie and Teugels, Theorem 1.5.11): for a
monotone increasing function `F`, eventually positive, locally integrable and regularly varying
at infinity of index `ρ > -1`,

  `(∫_0^t F) / (t F t) → 1 / (ρ + 1)`.

Nonnegativity is not assumed: the function is truncated at zero, which changes the integral by
a constant that `t F t → ∞` absorbs. -/
theorem karamata_origin_integral {F : ℝ → ℝ} {ρ : ℝ} (hρ : -1 < ρ)
    (hmono : Monotone F) (hpos : ∀ᶠ t in atTop, 0 < F t)
    (hF : RegularlyVaryingAtTop F ρ) (hint : ∀ t, IntegrableOn F (Ioc 0 t)) :
    Tendsto (fun t : ℝ => (∫ r in Ioc (0:ℝ) t, F r) / (t * F t)) atTop (𝓝 (1 / (ρ + 1))) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpos
  set A : ℝ := max N 1 with hAdef
  have hA : 0 < A := lt_of_lt_of_le one_pos (le_max_right N 1)
  have hFA : ∀ x, A ≤ x → 0 < F x := fun x hx => hN x (le_trans (le_max_left N 1) hx)
  have hmono' : Monotone (fun r : ℝ => max (F r) 0) := fun a b hab => max_le_max (hmono hab) le_rfl
  have hnn' : ∀ r : ℝ, 0 ≤ max (F r) 0 := fun r => le_max_right _ _
  have hF' : RegularlyVaryingAtTop (fun r => max (F r) 0) ρ :=
    regularlyVaryingAtTop_max_zero hFA hF
  have hmain := karamata_origin_integral_nonneg hρ hmono' hnn' hF'
  set c : ℝ := (∫ r in Ioc (0:ℝ) A, max (F r) 0) - (∫ r in Ioc (0:ℝ) A, F r) with hcdef
  have hzero : Tendsto (fun t : ℝ => c / (t * F t)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds (tendsto_mul_self_atTop_of_pos hmono hFA)
  have hcomb := hmain.sub hzero
  rw [sub_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop A, eventually_gt_atTop (0:ℝ)] with t hAt ht0
  have hFt : 0 < F t := hFA t hAt
  rw [max_eq_left hFt.le, integral_Ioc_max_zero_eq hA hmono hFA hint hAt, ← hcdef, add_div,
    add_sub_cancel_left]

/-- **Karamata at the origin for the reciprocal of an integrated tail**, in the abstract form:
`I` is positive, antitone and regularly varying of index `1 - α`, and `I t ∼ t F t / (α - 1)`.
Then `F t ∫_0^t dr / I r → 1 - 1 / α`. -/
theorem karamata_origin_reciprocal {F I : ℝ → ℝ} {α : ℝ} (hα : 1 < α)
    (hIpos : ∀ t, 0 < I t) (hIanti : Antitone I) (hIRV : RegularlyVaryingAtTop I (1 - α))
    (hKar : Tendsto (fun t : ℝ => I t / (t * F t)) atTop (𝓝 (1 / (α - 1)))) :
    Tendsto (fun t : ℝ => F t * ∫ r in Ioc (0:ℝ) t, (I r)⁻¹) atTop (𝓝 (1 - 1 / α)) := by
  have hHmono : Monotone (fun t => (I t)⁻¹) := fun a b hab => inv_anti₀ (hIpos b) (hIanti hab)
  have hHnn : ∀ t, 0 ≤ (I t)⁻¹ := fun t => le_of_lt (inv_pos.mpr (hIpos t))
  have hHRV : RegularlyVaryingAtTop (fun t => (I t)⁻¹) (α - 1) := by
    have h := regularlyVaryingAtTop_inv hIRV
    rwa [show -(1 - α) = α - 1 by ring] at h
  have hnum := karamata_origin_integral_nonneg (show (-1:ℝ) < α - 1 by linarith) hHmono hHnn hHRV
  have hval : (1:ℝ) / (α - 1) ≠ 0 := by
    have : (0:ℝ) < α - 1 := by linarith
    positivity
  have hrec : Tendsto (fun t : ℝ => (t * F t) / I t) atTop (𝓝 (α - 1)) := by
    have h := hKar.inv₀ hval
    rw [one_div, inv_inv] at h
    refine h.congr fun t => ?_
    rw [inv_div]
  have hprod := hnum.mul hrec
  have hlim : (1 / ((α - 1) + 1)) * (α - 1) = 1 - 1 / α := by
    have hα0 : α ≠ 0 := by positivity
    rw [show α - 1 + 1 = α by ring]
    field_simp
  rw [hlim] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht0
  have ht : t ≠ 0 := ne_of_gt ht0
  have hI : I t ≠ 0 := ne_of_gt (hIpos t)
  field_simp

/-- **Karamata at the origin for the reciprocal integrated tail of a law.**  If the lower tail
of a law is regularly varying of index `-α` with `α > 1`, then

  `P(z < -t) ∫_0^t dr / E (-z - r)_+ → 1 - 1 / α`.

Every hypothesis is discharged inside: the integrated tail is positive, antitone and regularly
varying of index `1 - α`, and its asymptotic `E (-z - t)_+ ∼ t P(z < -t) / (α - 1)` is
Karamata's theorem for the tail integral. -/
theorem karamata_origin_reciprocal_integratedLowerTail {ν : Measure ℝ}
    [IsProbabilityMeasure ν] {α : ℝ} (hα : 1 < α)
    (htail : RegularlyVaryingAtTop (fun r => (ν (Set.Iio (-r))).toReal) (-α)) :
    Tendsto (fun t : ℝ => (ν (Set.Iio (-t))).toReal *
        ∫ r in Set.Ioc 0 t, (∫ z, max (-z - r) 0 ∂ν)⁻¹) atTop (𝓝 (1 - 1 / α)) := by
  have hInn : ∀ t : ℝ, 0 ≤ ∫ z, max (-z - t) 0 ∂ν := fun t =>
    integral_nonneg fun z => le_max_right _ _
  have hIRV : RegularlyVaryingAtTop (fun t => ∫ z, max (-z - t) 0 ∂ν) (1 - α) :=
    regularlyVaryingAtTop_integratedLowerTail hα htail
  have hIanti : Antitone fun t => ∫ z, max (-z - t) 0 ∂ν :=
    antitone_integratedLowerTail hα htail
  have hIpos : ∀ t : ℝ, 0 < ∫ z, max (-z - t) 0 ∂ν :=
    pos_of_antitone_of_eventually_pos hIanti (eventually_pos_of_regularlyVarying hIRV hInn)
  exact karamata_origin_reciprocal hα hIpos hIanti hIRV (karamata_integrated_tail hα htail)

end LatticeProb
