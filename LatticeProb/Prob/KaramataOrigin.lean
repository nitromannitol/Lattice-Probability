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

/-- A monotone increasing function is integrable on `(0, t]` with no sign condition: on that
interval it lies between `F 0` and `F t`.  This is what makes the local integrability
hypothesis of Karamata's theorem at the origin redundant for a monotone function. -/
theorem integrableOn_Ioc_of_monotone {F : ℝ → ℝ} (hmono : Monotone F) (t : ℝ) :
    IntegrableOn F (Ioc 0 t) := by
  have hmeas : Measurable F := hmono.measurable
  have hconst : IntegrableOn (fun _ : ℝ => max |F 0| |F t|) (Ioc 0 t) :=
    integrableOn_const measure_Ioc_lt_top.ne
  refine Integrable.mono' hconst hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun r hr => ?_)
  rw [Real.norm_eq_abs]
  exact abs_le_max_abs_abs (hmono hr.1.le) (hmono hr.2)

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

/-- **Karamata's theorem at the origin** with no integrability hypothesis: for a monotone
function the local integrability is automatic. -/
theorem karamata_origin_integral_of_monotone {F : ℝ → ℝ} {ρ : ℝ} (hρ : -1 < ρ)
    (hmono : Monotone F) (hpos : ∀ᶠ t in atTop, 0 < F t) (hF : RegularlyVaryingAtTop F ρ) :
    Tendsto (fun t : ℝ => (∫ r in Ioc (0:ℝ) t, F r) / (t * F t)) atTop (𝓝 (1 / (ρ + 1))) :=
  karamata_origin_integral hρ hmono hpos hF fun t => integrableOn_Ioc_of_monotone hmono t

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

/-- A monotone increasing nonnegative regularly varying function has index at least zero: the
ratio at `lam = 2` is at least one. -/
theorem index_nonneg_of_monotone {F : ℝ → ℝ} {ρ : ℝ} (hmono : Monotone F)
    (hnn : ∀ r, 0 ≤ F r) (hF : RegularlyVaryingAtTop F ρ) : 0 ≤ ρ := by
  have hpos := eventually_pos_of_regularlyVarying hF hnn
  have h2 := hF 2 two_pos
  have hge : ∀ᶠ r : ℝ in atTop, (1:ℝ) ≤ F (2 * r) / F r := by
    filter_upwards [hpos, eventually_ge_atTop (0:ℝ)] with r hFr hr
    rw [le_div_iff₀ hFr, one_mul]
    exact hmono (by linarith)
  have hbound : (1:ℝ) ≤ (2:ℝ) ^ ρ := ge_of_tendsto h2 hge
  by_contra hcon
  rw [not_le] at hcon
  have hlt : (2:ℝ) ^ ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hcon
  linarith

/-- An antitone nonnegative regularly varying function has index at most zero.  With
`index_nonneg_of_monotone` this says that a monotone function of index `ρ > -1` is increasing
when `ρ > 0` and decreasing when `ρ < 0`, so the two halves of Karamata's theorem at the origin
below cover every monotone function. -/
theorem index_nonpos_of_antitone {F : ℝ → ℝ} {ρ : ℝ} (hmono : Antitone F)
    (hnn : ∀ r, 0 ≤ F r) (hF : RegularlyVaryingAtTop F ρ) : ρ ≤ 0 := by
  have hpos := eventually_pos_of_regularlyVarying hF hnn
  have hFpos : ∀ x, 0 < F x := pos_of_antitone_of_eventually_pos hmono hpos
  have h2 := hF 2 two_pos
  have hle : ∀ᶠ r : ℝ in atTop, F (2 * r) / F r ≤ 1 := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
    rw [div_le_one (hFpos r)]
    exact hmono (by linarith)
  have hbound : (2:ℝ) ^ ρ ≤ 1 := le_of_tendsto h2 hle
  by_contra hcon
  rw [not_le] at hcon
  have hgt : (1:ℝ) < (2:ℝ) ^ ρ :=
    (Real.one_lt_rpow_iff_of_pos two_pos).mpr (Or.inl ⟨by norm_num, hcon⟩)
  linarith

/-- The domination needed at the origin for an ANTITONE function, where the trivial bound of
the increasing case is not available: Potter's bound covers `t u ≥ r₀`, and below that level
the function is bounded by `F 0` while `1 / F t` is bounded through Potter's bound at `r₀`,
which is again a multiple of `u ^ (ρ - δ)` because the exponent is negative. -/
theorem karamata_origin_antitone_bound {F : ℝ → ℝ} {ρ δ : ℝ} (hmono : Antitone F)
    (hnn : ∀ r, 0 ≤ F r) (hF : RegularlyVaryingAtTop F ρ) (hδ : 0 < δ) (hρδ : ρ - δ < 0) :
    ∃ C t₀ : ℝ, 0 < t₀ ∧ 0 ≤ C ∧ ∀ t u : ℝ, t₀ ≤ t → 0 < u → u ≤ 1 →
      F (t * u) / F t ≤ C * u ^ (ρ - δ) := by
  have hpos := eventually_pos_of_regularlyVarying hF hnn
  have hFpos : ∀ x, 0 < F x := pos_of_antitone_of_eventually_pos hmono hpos
  obtain ⟨r₀, hr₀pos, hpot⟩ := potter_lower hF hmono hpos hδ
  refine ⟨max (1 + δ) ((1 + δ) * (F 0 / F r₀)), r₀, hr₀pos, le_max_of_le_left (by linarith),
    fun t u ht hu0 hu1 => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le hr₀pos ht
  have hupow : (0:ℝ) < u ^ (ρ - δ) := Real.rpow_pos_of_pos hu0 _
  rcases le_or_gt r₀ (t * u) with hc | hc
  · have h1 := hpot t (t * u) hc (mul_le_of_le_one_right ht0.le hu1)
    rw [show t * u / t = u by field_simp] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) hupow.le)
  · have hur : u ≤ r₀ / t := by
      rw [le_div_iff₀ ht0]
      nlinarith [hc]
    have h3 : (r₀ / t) ^ (ρ - δ) ≤ u ^ (ρ - δ) := Real.rpow_le_rpow_of_nonpos hu0 hur hρδ.le
    have h1 := hpot t r₀ le_rfl ht
    have hFtu : F (t * u) ≤ F 0 := hmono (mul_nonneg ht0.le hu0.le)
    have h4 : F (t * u) / F t ≤ F 0 / F t := div_le_div_of_nonneg_right hFtu (hFpos t).le
    have hFt0 : F t ≠ 0 := ne_of_gt (hFpos t)
    have hFr0 : F r₀ ≠ 0 := ne_of_gt (hFpos r₀)
    have h5 : F 0 / F t = (F 0 / F r₀) * (F r₀ / F t) := by
      field_simp
    have h6 : (0:ℝ) ≤ F 0 / F r₀ := div_nonneg (hnn 0) (hFpos r₀).le
    have h7 : F 0 / F t ≤ (F 0 / F r₀) * ((1 + δ) * (r₀ / t) ^ (ρ - δ)) := by
      rw [h5]
      exact mul_le_mul_of_nonneg_left h1 h6
    have h8 : (F 0 / F r₀) * ((1 + δ) * (r₀ / t) ^ (ρ - δ))
        ≤ ((1 + δ) * (F 0 / F r₀)) * u ^ (ρ - δ) := by
      have hd : (0:ℝ) ≤ 1 + δ := by linarith
      calc (F 0 / F r₀) * ((1 + δ) * (r₀ / t) ^ (ρ - δ))
          = ((1 + δ) * (F 0 / F r₀)) * (r₀ / t) ^ (ρ - δ) := by ring
        _ ≤ ((1 + δ) * (F 0 / F r₀)) * u ^ (ρ - δ) :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg hd h6)
    have h9 : ((1 + δ) * (F 0 / F r₀)) * u ^ (ρ - δ)
        ≤ max (1 + δ) ((1 + δ) * (F 0 / F r₀)) * u ^ (ρ - δ) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hupow.le
    linarith [h4, h7, h8, h9]

/-- The heart of Karamata's theorem at the origin for an antitone function: the dominating
function is `C u ^ (ρ - δ)` with `δ = (ρ + 1) / 2`, integrable on `(0, 1]` because
`ρ - δ > -1`. -/
theorem karamata_origin_ratio_antitone {F : ℝ → ℝ} {ρ : ℝ} (hρ : -1 < ρ)
    (hmono : Antitone F) (hnn : ∀ r, 0 ≤ F r) (hF : RegularlyVaryingAtTop F ρ) :
    Tendsto (fun t : ℝ => ∫ u in Ioc (0:ℝ) 1, F (t * u) / F t) atTop (𝓝 (1 / (ρ + 1))) := by
  have hρ0 : ρ ≤ 0 := index_nonpos_of_antitone hmono hnn hF
  set δ : ℝ := (ρ + 1) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hρδ : ρ - δ < 0 := by rw [hδdef]; linarith
  have hexp : -1 < ρ - δ := by rw [hδdef]; linarith
  obtain ⟨C, t₀, ht₀, hC, hbnd⟩ := karamata_origin_antitone_bound hmono hnn hF hδ hρδ
  have hbint : IntegrableOn (fun u : ℝ => C * u ^ (ρ - δ)) (Ioc (0:ℝ) 1) :=
    ((intervalIntegral.intervalIntegrable_rpow' hexp).1).const_mul C
  have hdct : Tendsto (fun t : ℝ => ∫ u in Ioc (0:ℝ) 1, F (t * u) / F t) atTop
      (𝓝 (∫ u in Ioc (0:ℝ) 1, u ^ ρ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u : ℝ => C * u ^ (ρ - δ)) ?_ ?_ hbint ?_
    · exact Filter.Eventually.of_forall fun t =>
        ((hmono.measurable.comp (measurable_id.const_mul t)).div_const (F t)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop t₀] with t ht
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hnn _) (hnn t))]
      exact hbnd t u ht hu.1 hu.2
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
      exact (hF u hu.1).congr fun r => by rw [mul_comm u r]
  rwa [integral_Ioc_zero_one_rpow hρ] at hdct

/-- **Karamata's theorem at the origin for an antitone function**: `∫_0^t F ∼ t F t / (ρ + 1)`
for `F` antitone, nonnegative and regularly varying of index `ρ ∈ (-1, 0]`.  Together with
`karamata_origin_integral_nonneg` this covers every monotone regularly varying function of
index above `-1`. -/
theorem karamata_origin_integral_antitone {F : ℝ → ℝ} {ρ : ℝ} (hρ : -1 < ρ)
    (hmono : Antitone F) (hnn : ∀ r, 0 ≤ F r) (hF : RegularlyVaryingAtTop F ρ) :
    Tendsto (fun t : ℝ => (∫ r in Ioc (0:ℝ) t, F r) / (t * F t)) atTop (𝓝 (1 / (ρ + 1))) := by
  have hpos : ∀ᶠ r in atTop, 0 < F r := eventually_pos_of_regularlyVarying hF hnn
  refine (karamata_origin_ratio_antitone hρ hmono hnn hF).congr' ?_
  filter_upwards [hpos, eventually_gt_atTop (0:ℝ)] with t hFt ht0
  rw [integral_div, integral_Ioc_zero_scale F ht0]
  field_simp

/-- **The truncated mean of a law with a heavy lower tail.**  If the lower tail is regularly
varying of index `-α` with `α < 1`, then `∫_0^t P(z < -r) dr ∼ t P(z < -t) / (1 - α)`.  This is
the companion of `karamata_integrated_tail`, which needs `α > 1` for the tail to be integrable
at infinity; here the tail is not integrable and the integral from the origin is what
diverges. -/
theorem karamata_origin_lowerTail {ν : Measure ℝ} [IsFiniteMeasure ν] {α : ℝ} (hα : α < 1)
    (htail : RegularlyVaryingAtTop (fun r => (ν (Set.Iio (-r))).toReal) (-α)) :
    Tendsto (fun t : ℝ => (∫ r in Ioc (0:ℝ) t, (ν (Set.Iio (-r))).toReal)
      / (t * (ν (Set.Iio (-t))).toReal)) atTop (𝓝 (1 / (1 - α))) := by
  have h := karamata_origin_integral_antitone (show (-1:ℝ) < -α by linarith)
    (antitone_lowerTail ν) (lowerTail_nonneg ν) htail
  rw [show -α + 1 = 1 - α by ring] at h
  exact h

end LatticeProb
