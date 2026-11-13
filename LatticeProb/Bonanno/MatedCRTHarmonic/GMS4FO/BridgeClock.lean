/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4FO.BridgeClock at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.Translate

/-!
# The swept-mass clock of an area-parametrized curve restricted to an open set

Source: [18], §4.2 and the proof of Lemma 4.3: `μ_h` on
`V` is determined by `h|_V`, so along the space-filling curve the area clock is determined, *inside `V`*, up to the
time spent outside `V`.

Hypotheses (`BridgeHyp μ c ψ V`): `c` is a continuous transient curve visiting every point, `c ∘ ψ` (`ψ : ℝ ≃o ℝ`)
is parametrized by `μ`-area, and `V` is open and bounded. With `ν = μ.restrict V` and a root time `σ`, the swept
mass `S = sweep ν c σ` satisfies:

* `sweep_sub`: `S u' − S u = μ(c([σ+u, σ+u']) ∩ V)` for `u ≤ u'` (images of consecutive intervals overlap in
  `μ`-null sets);
* `sweep_sub_of_subset`: if `c([σ+u, σ+u']) ⊆ V` the increment is the `μ`-area time `ψ⁻¹(σ+u') − ψ⁻¹(σ+u)`;
* `sweep_lt_of_mem`: `S` increases strictly across times spent in `V`; `sweep_continuous`;
* `exists_sweep_const_atTop/atBot`: `S` is constant near `±∞` (transience, `V` bounded), so the clamping values
  `sweepTop`, `sweepBot`, `sweepStart` of `relTime` are attained;
* `relTime_eq`: `relTime s` is the first relative time `u` with `S u = s`; `relTime_le_bot`, `relTime_top_le`:
  outside the swept range it is clamped to a time at which `c` is not in `V`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4FO

open MatedCRTHarmonic

/-- The hypotheses of the bridge between Lebesgue-time localized observables and the geometric ones. -/
structure BridgeHyp (μ : Measure ℂ) (c : ℝ → ℂ) (ψ : ℝ ≃o ℝ) (V : Set ℂ) : Prop where
  cont : Continuous c
  area : ∀ s t : ℝ, s ≤ t → μ ((c ∘ ψ) '' Icc s t) = ENNReal.ofReal (t - s)
  visits : HasFirstVisits c
  transient : Tendsto c (cocompact ℝ) (cocompact ℂ)
  isOpen : IsOpen V
  bounded : Bornology.IsBounded V

namespace BridgeHyp

variable {μ : Measure ℂ} {c : ℝ → ℂ} {ψ : ℝ ≃o ℝ} {V : Set ℂ} (H : BridgeHyp μ c ψ V)
include H

omit H in
theorem image_Icc_eq (a b : ℝ) : c '' Icc a b = (c ∘ ψ) '' Icc (ψ.symm a) (ψ.symm b) := by
  rw [image_comp, OrderIso.image_Icc, ψ.apply_symm_apply, ψ.apply_symm_apply]

/-- `μ(c([a, b])) = ψ⁻¹ b − ψ⁻¹ a`. -/
theorem measure_image_Icc {a b : ℝ} (hab : a ≤ b) :
    μ (c '' Icc a b) = ENNReal.ofReal (ψ.symm b - ψ.symm a) := by
  rw [image_Icc_eq]
  exact H.area _ _ (ψ.symm.monotone hab)

theorem measure_image_Icc_ne_top (a b : ℝ) : μ (c '' Icc a b) ≠ ⊤ := by
  rcases le_or_gt a b with hab | hab
  · rw [H.measure_image_Icc hab]
    exact ENNReal.ofReal_ne_top
  · rw [Icc_eq_empty_of_lt hab, image_empty, measure_empty]
    exact ENNReal.zero_ne_top

theorem isClosed_image_Icc (a b : ℝ) : IsClosed (c '' Icc a b) :=
  (isCompact_Icc.image H.cont).isClosed

theorem measure_singleton_image (a : ℝ) : μ {c a} = 0 := by
  have h := H.measure_image_Icc (le_refl a)
  rwa [Icc_self, image_singleton, sub_self, ENNReal.ofReal_zero] at h

/-- Images of consecutive intervals overlap in a `μ`-null set. -/
theorem measure_inter_null {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    μ (c '' Icc a b ∩ c '' Icc b d) = 0 := by
  have hU : c '' Icc a b ∪ c '' Icc b d = c '' Icc a d := by
    rw [← image_union, Icc_union_Icc_eq_Icc hab hbd]
  have h := measure_union_add_inter (μ := μ) (c '' Icc a b) (H.isClosed_image_Icc b d).measurableSet
  rw [hU, H.measure_image_Icc (hab.trans hbd), H.measure_image_Icc hab, H.measure_image_Icc hbd,
    ← ENNReal.ofReal_add (sub_nonneg.2 (ψ.symm.monotone hab)) (sub_nonneg.2 (ψ.symm.monotone hbd)),
    show ψ.symm b - ψ.symm a + (ψ.symm d - ψ.symm b) = ψ.symm d - ψ.symm a by ring] at h
  have h' : ENNReal.ofReal (ψ.symm d - ψ.symm a) + μ (c '' Icc a b ∩ c '' Icc b d) =
      ENNReal.ofReal (ψ.symm d - ψ.symm a) + 0 := by rw [h, add_zero]
  exact (ENNReal.add_right_inj ENNReal.ofReal_ne_top).1 h'

/-- Additivity of the `ν = μ|_V` mass of consecutive images. -/
theorem restrict_image_add {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    μ.restrict V (c '' Icc a d) = μ.restrict V (c '' Icc a b) + μ.restrict V (c '' Icc b d) := by
  have hV := H.isOpen.measurableSet
  rw [Measure.restrict_apply' hV, Measure.restrict_apply' hV, Measure.restrict_apply' hV]
  have hU : c '' Icc a d ∩ V = (c '' Icc a b ∩ V) ∪ (c '' Icc b d ∩ V) := by
    rw [← union_inter_distrib_right, ← image_union, Icc_union_Icc_eq_Icc hab hbd]
  have h := measure_union_add_inter (μ := μ) (c '' Icc a b ∩ V)
    ((H.isClosed_image_Icc b d).measurableSet.inter hV)
  have hnull : μ ((c '' Icc a b ∩ V) ∩ (c '' Icc b d ∩ V)) = 0 :=
    measure_mono_null (show (c '' Icc a b ∩ V) ∩ (c '' Icc b d ∩ V) ⊆ c '' Icc a b ∩ c '' Icc b d from
      fun x hx => ⟨hx.1.1, hx.2.1⟩) (H.measure_inter_null hab hbd)
  rw [hnull, add_zero] at h
  rw [hU, h]

theorem restrict_image_ne_top (a b : ℝ) : μ.restrict V (c '' Icc a b) ≠ ⊤ :=
  ne_top_of_le_ne_top (H.measure_image_Icc_ne_top a b) (Measure.restrict_apply_le _ _)

/-! ### The swept mass -/

variable (σ : ℝ)

/-- **Increments of the swept mass.** -/
theorem sweep_sub {u u' : ℝ} (huu' : u ≤ u') :
    sweep (μ.restrict V) c σ u' - sweep (μ.restrict V) c σ u =
      (μ.restrict V (c '' Icc (σ + u) (σ + u'))).toReal := by
  have hfin := H.restrict_image_ne_top (V := V)
  rcases le_or_gt 0 u with hu | hu
  · rw [sweep_of_nonneg _ _ _ (hu.trans huu'), sweep_of_nonneg _ _ _ hu,
      H.restrict_image_add (show σ ≤ σ + u by linarith) (show σ + u ≤ σ + u' by linarith),
      ENNReal.toReal_add (hfin _ _) (hfin _ _)]
    ring
  · rcases le_or_gt 0 u' with hu' | hu'
    · rw [sweep_of_nonneg _ _ _ hu', sweep_of_neg _ _ _ hu,
        H.restrict_image_add (show σ + u ≤ σ by linarith) (show σ ≤ σ + u' by linarith),
        ENNReal.toReal_add (hfin _ _) (hfin _ _)]
      ring
    · rw [sweep_of_neg _ _ _ hu', sweep_of_neg _ _ _ hu,
        H.restrict_image_add (show σ + u ≤ σ + u' by linarith) (show σ + u' ≤ σ by linarith),
        ENNReal.toReal_add (hfin _ _) (hfin _ _)]
      ring

theorem sweep_mono : Monotone (sweep (μ.restrict V) c σ) := by
  intro u u' huu'
  have h := H.sweep_sub σ huu'
  have : 0 ≤ (μ.restrict V (c '' Icc (σ + u) (σ + u'))).toReal := ENNReal.toReal_nonneg
  linarith

theorem sweep_zero : sweep (μ.restrict V) c σ 0 = 0 := by
  rw [sweep_of_nonneg _ _ _ le_rfl, add_zero, Icc_self, image_singleton]
  have : μ.restrict V {c σ} = 0 :=
    le_antisymm ((Measure.restrict_apply_le _ _).trans (H.measure_singleton_image σ).le) bot_le
  rw [this, ENNReal.toReal_zero]

/-- The increment is at most the `μ`-area time. -/
theorem sweep_sub_le {u u' : ℝ} (huu' : u ≤ u') :
    sweep (μ.restrict V) c σ u' - sweep (μ.restrict V) c σ u ≤
      ψ.symm (σ + u') - ψ.symm (σ + u) := by
  rw [H.sweep_sub σ huu']
  have hle : μ.restrict V (c '' Icc (σ + u) (σ + u')) ≤ μ (c '' Icc (σ + u) (σ + u')) :=
    Measure.restrict_apply_le _ _
  have h2 := H.measure_image_Icc (show σ + u ≤ σ + u' by linarith)
  calc (μ.restrict V (c '' Icc (σ + u) (σ + u'))).toReal
      ≤ (μ (c '' Icc (σ + u) (σ + u'))).toReal :=
        ENNReal.toReal_mono (H.measure_image_Icc_ne_top _ _) hle
    _ = ψ.symm (σ + u') - ψ.symm (σ + u) := by
        rw [h2, ENNReal.toReal_ofReal (sub_nonneg.2 (ψ.symm.monotone (by linarith)))]

/-- If the curve stays in `V`, the increment is the `μ`-area time. -/
theorem sweep_sub_of_subset {u u' : ℝ} (huu' : u ≤ u') (hsub : c '' Icc (σ + u) (σ + u') ⊆ V) :
    sweep (μ.restrict V) c σ u' - sweep (μ.restrict V) c σ u = ψ.symm (σ + u') - ψ.symm (σ + u) := by
  rw [H.sweep_sub σ huu', Measure.restrict_apply' H.isOpen.measurableSet, inter_eq_left.2 hsub,
    H.measure_image_Icc (show σ + u ≤ σ + u' by linarith),
    ENNReal.toReal_ofReal (sub_nonneg.2 (ψ.symm.monotone (by linarith)))]

theorem sweep_continuous : Continuous (sweep (μ.restrict V) c σ) := by
  have hg : Continuous fun u : ℝ => ψ.symm (σ + u) := ψ.symm.continuous.comp (continuous_const.add continuous_id)
  rw [Metric.continuous_iff]
  intro u₀ e he
  obtain ⟨δ, hδ, hδe⟩ := Metric.continuous_iff.1 hg u₀ e he
  refine ⟨δ, hδ, fun u hu => ?_⟩
  have hgu := hδe u hu
  rw [Real.dist_eq] at hgu ⊢
  rcases le_total u u₀ with h | h
  · have h1 := H.sweep_sub_le σ h
    have h2 := H.sweep_mono σ h
    rw [abs_sub_comm] at hgu ⊢
    rw [abs_of_nonneg (by linarith)]
    rw [abs_of_nonneg (sub_nonneg.2 (ψ.symm.monotone (by linarith : σ + u ≤ σ + u₀)))] at hgu
    linarith
  · have h1 := H.sweep_sub_le σ h
    have h2 := H.sweep_mono σ h
    rw [abs_of_nonneg (by linarith)]
    rw [abs_of_nonneg (sub_nonneg.2 (ψ.symm.monotone (by linarith : σ + u₀ ≤ σ + u)))] at hgu
    linarith

/-- Near a time spent in the open set `V`, the curve stays in `V`. -/
theorem exists_ball_subset {t : ℝ} (ht : c t ∈ V) :
    ∃ δ > 0, ∀ t' : ℝ, |t' - t| < δ → c t' ∈ V := by
  obtain ⟨e, he, heV⟩ := Metric.isOpen_iff.1 H.isOpen _ ht
  obtain ⟨δ, hδ, hδe⟩ := Metric.continuous_iff.1 H.cont t e he
  exact ⟨δ, hδ, fun t' ht' => heV (hδe t' (by rwa [Real.dist_eq]))⟩

/-- **Strict increase across a time spent in `V`.** -/
theorem sweep_lt_of_mem {u u' v : ℝ} (hv : v ∈ Ioo u u') (hcv : c (σ + v) ∈ V) :
    sweep (μ.restrict V) c σ u < sweep (μ.restrict V) c σ u' := by
  obtain ⟨δ, hδ, hδV⟩ := H.exists_ball_subset hcv
  set δ' := min δ (min (v - u) (u' - v)) / 2 with hδ'
  have hpos : 0 < min δ (min (v - u) (u' - v)) := lt_min hδ (lt_min (by linarith [hv.1]) (by linarith [hv.2]))
  have hδ'pos : 0 < δ' := by positivity
  have hδ'δ : δ' < δ := by
    have := min_le_left δ (min (v - u) (u' - v))
    linarith
  have hδ'1 : δ' < v - u := by
    have := (min_le_right δ (min (v - u) (u' - v))).trans (min_le_left _ _)
    linarith
  have hδ'2 : δ' < u' - v := by
    have := (min_le_right δ (min (v - u) (u' - v))).trans (min_le_right _ _)
    linarith
  have hsub : c '' Icc (σ + (v - δ')) (σ + (v + δ')) ⊆ V := by
    rintro _ ⟨t, ht, rfl⟩
    apply hδV
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have heq := H.sweep_sub_of_subset σ (show v - δ' ≤ v + δ' by linarith) hsub
  have hlt : ψ.symm (σ + (v - δ')) < ψ.symm (σ + (v + δ')) := ψ.symm.strictMono (by linarith)
  have h1 := H.sweep_mono σ (show u ≤ v - δ' by linarith)
  have h2 := H.sweep_mono σ (show v + δ' ≤ u' by linarith)
  linarith

/-- A flat stretch of the swept mass ends at a point outside `V`. -/
theorem not_mem_of_sweep_eq_right {u u' : ℝ} (huu' : u < u')
    (heq : sweep (μ.restrict V) c σ u = sweep (μ.restrict V) c σ u') : c (σ + u') ∉ V := by
  intro hc
  obtain ⟨δ, hδ, hδV⟩ := H.exists_ball_subset hc
  set v := max u (u' - δ / 2) + (u' - max u (u' - δ / 2)) / 2 with hv
  have hm : max u (u' - δ / 2) < u' := max_lt huu' (by linarith)
  have hv1 : max u (u' - δ / 2) < v := by rw [hv]; linarith
  have hv2 : v < u' := by rw [hv]; linarith
  have hvV : c (σ + v) ∈ V := by
    apply hδV
    rw [abs_lt]
    constructor <;> linarith [le_max_right u (u' - δ / 2)]
  have := H.sweep_lt_of_mem σ ⟨lt_of_le_of_lt (le_max_left _ _) hv1, hv2⟩ hvV
  linarith

/-- A flat stretch of the swept mass starts at a point outside `V`. -/
theorem not_mem_of_sweep_eq_left {u u' : ℝ} (huu' : u < u')
    (heq : sweep (μ.restrict V) c σ u = sweep (μ.restrict V) c σ u') : c (σ + u) ∉ V := by
  intro hc
  obtain ⟨δ, hδ, hδV⟩ := H.exists_ball_subset hc
  set v := u + (min u' (u + δ / 2) - u) / 2 with hv
  have hm : u < min u' (u + δ / 2) := lt_min huu' (by linarith)
  have hv1 : u < v := by rw [hv]; linarith
  have hv2 : v < min u' (u + δ / 2) := by rw [hv]; linarith
  have hvV : c (σ + v) ∈ V := by
    apply hδV
    rw [abs_lt]
    constructor <;> linarith [min_le_right u' (u + δ / 2)]
  have := H.sweep_lt_of_mem σ ⟨hv1, lt_of_lt_of_le hv2 (min_le_left _ _)⟩ hvV
  linarith

/-! ### Constancy near `±∞` -/

/-- The curve leaves the closure of `V` for good. -/
theorem exists_time_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, M < |t| → c t ∉ closure V := by
  have hK : IsCompact (closure V) := H.bounded.isCompact_closure
  have hmem : c ⁻¹' (closure V)ᶜ ∈ cocompact ℝ := H.transient hK.compl_mem_cocompact
  obtain ⟨K, hKc, hKs⟩ := mem_cocompact.1 hmem
  obtain ⟨M, hM⟩ := hKc.isBounded.subset_closedBall 0
  refine ⟨max M 0, le_max_right _ _, fun t ht hct => ?_⟩
  have htK : t ∈ K := by
    by_contra h
    exact hKs h hct
  have := hM htK
  rw [mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith [le_max_left M 0]

theorem exists_sweep_const_atTop :
    ∃ U₀ : ℝ, 0 ≤ U₀ ∧ ∀ u, U₀ ≤ u → sweep (μ.restrict V) c σ u = sweep (μ.restrict V) c σ U₀ := by
  obtain ⟨M, hM0, hM⟩ := H.exists_time_bound
  refine ⟨max 0 (M + 1 - σ), le_max_left _ _, fun u hu => ?_⟩
  have h := H.sweep_sub σ hu
  have hempty : μ.restrict V (c '' Icc (σ + max 0 (M + 1 - σ)) (σ + u)) = 0 := by
    rw [Measure.restrict_apply' H.isOpen.measurableSet]
    convert measure_empty (μ := μ)
    ext x
    simp only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false, not_and]
    rintro ⟨t, ht, rfl⟩ hV
    refine hM t ?_ (subset_closure hV)
    have : M + 1 - σ ≤ max 0 (M + 1 - σ) := le_max_right _ _
    rw [abs_of_pos (by linarith [ht.1])]
    linarith [ht.1]
  rw [hempty, ENNReal.toReal_zero] at h
  linarith

theorem exists_sweep_const_atBot :
    ∃ U₁ : ℝ, U₁ ≤ 0 ∧ ∀ u, u ≤ U₁ → sweep (μ.restrict V) c σ u = sweep (μ.restrict V) c σ U₁ := by
  obtain ⟨M, hM0, hM⟩ := H.exists_time_bound
  refine ⟨min 0 (-M - 1 - σ), min_le_left _ _, fun u hu => ?_⟩
  have h := H.sweep_sub σ hu
  have hempty : μ.restrict V (c '' Icc (σ + u) (σ + min 0 (-M - 1 - σ))) = 0 := by
    rw [Measure.restrict_apply' H.isOpen.measurableSet]
    convert measure_empty (μ := μ)
    ext x
    simp only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false, not_and]
    rintro ⟨t, ht, rfl⟩ hV
    refine hM t ?_ (subset_closure hV)
    have : min 0 (-M - 1 - σ) ≤ -M - 1 - σ := min_le_right _ _
    rw [abs_of_neg (by linarith [ht.2])]
    linarith [ht.2]
  rw [hempty, ENNReal.toReal_zero] at h
  linarith

end BridgeHyp

end MatedCRTHarmonic.GMS4FO
