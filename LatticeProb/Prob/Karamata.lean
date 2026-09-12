/-
Karamata's theorem for the integrated tail.

If the tail `F r = P(X < -r)` of a law is regularly varying of index `-α` with `α > 1`,
then its integral over `(t, ∞)` is asymptotic to `t F t / (α - 1)`.  Since
`E (-X - t)_+ = ∫_t^∞ F` by the layer cake formula, this is the statement that the
integrated lower tail is asymptotic to `t P(X < -t) / (α - 1)`.

The proof is the classical one: substituting `r = t u` turns the tail integral into
`t ∫_1^∞ F (t u) du`, the ratio `F (t u) / F t` converges to `u ^ (-α)` by regular
variation, and Potter's bound dominates it by the integrable `(1 + δ) u ^ (-α+δ)`
uniformly in `t`, so dominated convergence gives `∫_1^∞ u ^ (-α) du = 1 / (α - 1)`.
-/
import Mathlib
import LatticeProb.Prob.RegularVariation

open Filter Topology MeasureTheory Set

namespace LatticeProb

/-- The tail of a measure below `-r`, as a real number. -/
noncomputable def lowerTail (ν : Measure ℝ) (r : ℝ) : ℝ := (ν (Iio (-r))).toReal

theorem lowerTail_nonneg (ν : Measure ℝ) (r : ℝ) : 0 ≤ lowerTail ν r := ENNReal.toReal_nonneg

theorem antitone_lowerTail (ν : Measure ℝ) [IsFiniteMeasure ν] : Antitone (lowerTail ν) := by
  intro r r' hrr
  refine ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono ?_)
  intro z hz
  simp only [Set.mem_Iio] at hz ⊢
  linarith

/-- A nonnegative regularly varying function is eventually positive: the ratio at `λ = 1`
would otherwise be the junk value `0` instead of tending to `1`. -/
theorem eventually_pos_of_regularlyVarying {F : ℝ → ℝ} {ρ : ℝ} (hF : RegularlyVaryingAtTop F ρ)
    (hnn : ∀ r, 0 ≤ F r) : ∀ᶠ r in atTop, 0 < F r := by
  filter_upwards [hF.eventually_ne_zero] with r hr
  exact lt_of_le_of_ne (hnn r) (Ne.symm hr)

/-- Potter's bound in the scaled form the dominated convergence argument uses. -/
theorem potter_scaled {F : ℝ → ℝ} {α δ : ℝ} (hF : RegularlyVaryingAtTop F (-α))
    (hmono : Antitone F) (hnn : ∀ r, 0 ≤ F r) (hδ : 0 < δ) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t u : ℝ, t₀ ≤ t → 1 ≤ u →
      F (t * u) / F t ≤ (1 + δ) * u ^ (-α + δ) := by
  obtain ⟨r₀, hr₀pos, h⟩ :=
    potter_upper hF hmono (eventually_pos_of_regularlyVarying hF hnn) hδ
  refine ⟨r₀, hr₀pos, fun t u ht hu => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le hr₀pos ht
  have hts : t ≤ t * u := le_mul_of_one_le_right ht0.le hu
  have h1 := h t (t * u) ht hts
  have h2 : t * u / t = u := by field_simp
  rw [h2] at h1
  exact h1

/-- The integral of the dominating power over `(1, ∞)`. -/
theorem integral_Ioi_one_rpow {a : ℝ} (ha : a < -1) :
    ∫ u in Ioi (1 : ℝ), u ^ a = -1 / (a + 1) := by
  rw [integral_Ioi_rpow_of_lt ha one_pos, Real.one_rpow]

/-- A monotone regularly varying function of index `-α` with `α > 1` is integrable on every
half line far enough out. -/
theorem integrableOn_Ioi_of_regularlyVarying {F : ℝ → ℝ} {α : ℝ} (hα : 1 < α)
    (hmono : Antitone F) (hnn : ∀ r, 0 ≤ F r) (hF : RegularlyVaryingAtTop F (-α)) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t, t₀ ≤ t → IntegrableOn F (Ioi t) := by
  set δ : ℝ := (α - 1) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδα : δ < α - 1 := by rw [hδdef]; linarith
  have hFpos : ∀ x, 0 < F x :=
    pos_of_antitone_of_eventually_pos hmono (eventually_pos_of_regularlyVarying hF hnn)
  have hmeas : Measurable F := hmono.measurable
  obtain ⟨t₀, ht₀, hpot⟩ := potter_scaled hF hmono hnn hδ
  refine ⟨t₀, ht₀, fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le ht₀ ht
  have hbound : ∀ r ∈ Ioi t, ‖F r‖ ≤ ((1 + δ) * F t * t ^ (α - δ)) * r ^ (-α + δ) := by
    intro r hr
    have hr0 : 0 < r := lt_trans ht0 hr
    have hrt : 1 ≤ r / t := (one_le_div ht0).mpr (le_of_lt hr)
    have hEq : t * (r / t) = r := by field_simp
    have h1 := hpot t (r / t) ht hrt
    rw [hEq] at h1
    have h2 : F r ≤ (1 + δ) * (r / t) ^ (-α + δ) * F t := by
      have h4 := (div_le_iff₀ (hFpos t)).mp h1
      linarith
    have h3 : (r / t) ^ (-α + δ) = r ^ (-α + δ) * t ^ (α - δ) := by
      rw [Real.div_rpow hr0.le ht0.le, div_eq_mul_inv, ← Real.rpow_neg ht0.le]
      congr 1
      ring_nf
    rw [h3] at h2
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn r)]
    nlinarith [h2, Real.rpow_nonneg hr0.le (-α + δ), Real.rpow_nonneg ht0.le (α - δ)]
  have hbint : IntegrableOn (fun r : ℝ => ((1 + δ) * F t * t ^ (α - δ)) * r ^ (-α + δ))
      (Ioi t) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) ht0).const_mul _
  refine Integrable.mono' hbint hmeas.aestronglyMeasurable ?_
  exact (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hbound)

/-- **Karamata's theorem** for the tail integral of a monotone regularly varying function of
index `-α` with `α > 1`: `∫_t^∞ F ∼ t F t / (α - 1)`. -/
theorem karamata_tail_integral {F : ℝ → ℝ} {α : ℝ} (hα : 1 < α) (hmono : Antitone F)
    (hnn : ∀ r, 0 ≤ F r) (hF : RegularlyVaryingAtTop F (-α)) :
    Tendsto (fun t : ℝ => (∫ r in Ioi t, F r) / (t * F t)) atTop (𝓝 (1 / (α - 1))) := by
  set δ : ℝ := (α - 1) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδα : δ < α - 1 := by rw [hδdef]; linarith
  have hFpos : ∀ x, 0 < F x :=
    pos_of_antitone_of_eventually_pos hmono (eventually_pos_of_regularlyVarying hF hnn)
  obtain ⟨t₀, ht₀pos, hpot⟩ := potter_scaled hF hmono hnn hδ
  have hbint : IntegrableOn (fun u : ℝ => (1 + δ) * u ^ (-α + δ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  have hdct : Tendsto (fun t : ℝ => ∫ u in Ioi (1 : ℝ), F (t * u) / F t) atTop
      (𝓝 (∫ u in Ioi (1 : ℝ), u ^ (-α))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u : ℝ => (1 + δ) * u ^ (-α + δ)) ?_ ?_ hbint ?_
    · exact Filter.Eventually.of_forall fun t =>
        ((hmono.measurable.comp (measurable_id.const_mul t)).div_const (F t)).aestronglyMeasurable
    · refine eventually_atTop.mpr ⟨t₀, fun t ht => ?_⟩
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hnn _) (hnn t))]
      exact hpot t u ht (le_of_lt hu)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
      exact (hF u (lt_trans one_pos hu)).congr fun r => by rw [mul_comm u r]
  have hval : ∫ u in Ioi (1 : ℝ), u ^ (-α) = 1 / (α - 1) := by
    rw [integral_Ioi_one_rpow (show -α < -1 by linarith), show (-α + 1) = -(α - 1) by ring,
      neg_div_neg_eq]
  rw [hval] at hdct
  refine hdct.congr' (eventually_atTop.mpr ⟨max t₀ 1, fun t ht => ?_⟩)
  have ht0 : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right t₀ 1) ht)
  have hFt : F t ≠ 0 := (hFpos t).ne'
  have h1 : ∫ u in Ioi (1 : ℝ), F (t * u) / F t = (∫ u in Ioi (1 : ℝ), F (t * u)) / F t :=
    integral_div (F t) _
  have h2 : ∫ u in Ioi (1 : ℝ), F (t * u) = t⁻¹ * ∫ r in Ioi t, F r := by
    have h3 := integral_comp_mul_left_Ioi F 1 ht0
    rwa [mul_one, smul_eq_mul] at h3
  rw [h1, h2]
  field_simp


/-- The layer cake formula for the positive part, in `ℝ≥0∞`: no integrability is needed. -/
theorem lintegral_posPart_eq (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    ∫⁻ z, ENNReal.ofReal (max (-z - t) 0) ∂ν
      = ∫⁻ r in Ioi t, ENNReal.ofReal (lowerTail ν r) := by
  have hmeas : Measurable fun z : ℝ => max (-z - t) 0 :=
    (measurable_id.neg.sub_const t).max measurable_const
  have hnn : 0 ≤ᵐ[ν] fun z : ℝ => max (-z - t) 0 :=
    Filter.Eventually.of_forall fun z => le_max_right _ _
  rw [lintegral_eq_lintegral_meas_lt ν hnn hmeas.aemeasurable]
  have hset : EqOn (fun s : ℝ => ν {z : ℝ | s < max (-z - t) 0})
      (fun s : ℝ => ENNReal.ofReal (lowerTail ν (s + t))) (Ioi 0) := by
    intro s hs
    simp only [mem_Ioi] at hs
    have hEq : {z : ℝ | s < max (-z - t) 0} = Iio (-(s + t)) := by
      ext z
      simp only [mem_setOf_eq, mem_Iio, lt_max_iff]
      constructor
      · rintro (h | h)
        · linarith
        · linarith
      · intro h
        exact Or.inl (by linarith)
    simp only [hEq, lowerTail, ENNReal.ofReal_toReal (measure_ne_top ν _)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hset]
  have hmp := measurePreserving_add_right (volume : Measure ℝ) t
  have hemb := measurableEmbedding_addRight (G := ℝ) t
  have h := hmp.setLIntegral_comp_preimage_emb hemb
    (fun r : ℝ => ENNReal.ofReal (lowerTail ν r)) (Ioi t)
  rw [show (fun x : ℝ => x + t) ⁻¹' Ioi t = Ioi (0 : ℝ) by ext x; simp] at h
  exact h

/-- The positive part `(-z - t)_+` is integrable as soon as the tail is integrable past
`t`. -/
theorem integrable_posPart {ν : Measure ℝ} [IsFiniteMeasure ν] {t : ℝ}
    (hint : IntegrableOn (lowerTail ν) (Ioi t)) :
    Integrable (fun z => max (-z - t) 0) ν := by
  have hmeas : Measurable fun z : ℝ => max (-z - t) 0 :=
    (measurable_id.neg.sub_const t).max measurable_const
  have hnn : 0 ≤ᵐ[ν] fun z : ℝ => max (-z - t) 0 :=
    Filter.Eventually.of_forall fun z => le_max_right _ _
  refine ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).mpr ?_⟩
  rw [lintegral_posPart_eq ν t]
  exact hint.lintegral_lt_top

/-- **The integrated tail is the integral of the tail**: `E (-z - t)_+ = ∫_t^∞ P(z < -r) dr`. -/
theorem integral_posPart_eq {ν : Measure ℝ} [IsFiniteMeasure ν] {t : ℝ}
    (hint : IntegrableOn (lowerTail ν) (Ioi t)) :
    ∫ z, max (-z - t) 0 ∂ν = ∫ r in Ioi t, lowerTail ν r := by
  have hnn : 0 ≤ᵐ[ν] fun z : ℝ => max (-z - t) 0 :=
    Filter.Eventually.of_forall fun z => le_max_right _ _
  rw [(integrable_posPart hint).integral_eq_integral_meas_lt hnn]
  have hset : EqOn (fun s : ℝ => ν.real {z : ℝ | s < max (-z - t) 0})
      (fun s : ℝ => lowerTail ν (s + t)) (Ioi 0) := by
    intro s hs
    simp only [mem_Ioi] at hs
    have hEq : {z : ℝ | s < max (-z - t) 0} = Iio (-(s + t)) := by
      ext z
      simp only [mem_setOf_eq, mem_Iio, lt_max_iff]
      constructor
      · rintro (h | h)
        · linarith
        · linarith
      · intro h
        exact Or.inl (by linarith)
    simp only [hEq, lowerTail, measureReal_def]
  rw [setIntegral_congr_fun measurableSet_Ioi hset]
  have hmp := measurePreserving_add_right (volume : Measure ℝ) t
  have hemb := measurableEmbedding_addRight (G := ℝ) t
  have h := hmp.setIntegral_preimage_emb hemb (fun r : ℝ => lowerTail ν r) (Ioi t)
  rw [show (fun x : ℝ => x + t) ⁻¹' Ioi t = Ioi (0 : ℝ) by ext x; simp] at h
  exact h

/-- **Karamata's theorem for the integrated tail.**  If the lower tail of a law is regularly
varying of index `-α` with `α > 1`, then `E (-z - t)_+ ∼ t P(z < -t) / (α - 1)`. -/
theorem karamata_integrated_tail {ν : Measure ℝ} {α : ℝ} [IsProbabilityMeasure ν] (hα : 1 < α)
    (htail : RegularlyVaryingAtTop (fun r => (ν (Set.Iio (-r))).toReal) (-α)) :
    Tendsto (fun t : ℝ => (∫ z, max (-z - t) 0 ∂ν) / (t * (ν (Set.Iio (-t))).toReal))
      atTop (𝓝 (1 / (α - 1))) := by
  have hmono : Antitone (lowerTail ν) := antitone_lowerTail ν
  have hnn : ∀ r, 0 ≤ lowerTail ν r := lowerTail_nonneg ν
  have hF : RegularlyVaryingAtTop (lowerTail ν) (-α) := htail
  obtain ⟨t₀, ht₀pos, hint⟩ := integrableOn_Ioi_of_regularlyVarying hα hmono hnn hF
  refine (karamata_tail_integral hα hmono hnn hF).congr'
    (eventually_atTop.mpr ⟨t₀, fun t ht => ?_⟩)
  rw [← integral_posPart_eq (hint t ht)]
  rfl

end LatticeProb
