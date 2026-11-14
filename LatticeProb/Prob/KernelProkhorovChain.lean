import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Topology.MetricSpace.Thickening

/-!
# One step of a Markov chain in the one-sided Prokhorov distance

Let `κ, κ'` be two Markov kernels on a metric space `E`, and `μ, ν` two probability measures.
We compare the one-step laws `μ.bind κ` and `ν.bind κ'` in the one-sided Prokhorov sense
`ProkhorovLE`, where the radius and the additive error are kept apart:
`ProkhorovLE μ ν r e` means `μ A ≤ ν (thickening r A) + e` for every measurable `A`.

The main result `prokhorovLE_bind` says: if `μ` is `(δ, e)`-close to `ν`, the kernels satisfy
`ProkhorovLE (κ y) (κ' y) ε ε` for every starting point `y`, and `κ'` is `η`-continuous in the
one-sided Prokhorov sense at the points of a set `G` of `ν`-mass at least `1 - ρ` (at scale `δ`),
then `μ.bind κ` is `(ε + η, ε + η + ρ + e)`-close to `ν.bind κ'`.  No continuity of `κ` is
needed, and `κ'` may be discontinuous on the complement of `G`.  Iterating gives the
`n`-step comparison of two chains whose kernels are uniformly close but only one of which is
continuous away from a small set, with errors adding up linearly in `n`.

The proof of the integral inequality `lintegral_le_add_of_prokhorovLE` integrates the level-set
inequality of `ProkhorovLE` along the layer-cake formula.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LatticeProb

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]

/-- One-sided Prokhorov relation with a radius `r` and an additive error `e`:
`μ A ≤ ν (thickening r A) + e` for every measurable set `A`. -/
def ProkhorovLE (μ ν : Measure E) (r e : ℝ) : Prop :=
  ∀ A : Set E, MeasurableSet A → μ A ≤ ν (thickening r A) + ENNReal.ofReal e

omit [OpensMeasurableSpace E] in
/-- Integral form of `ProkhorovLE μ ν δ e`: for a measurable `f ≤ 1`, a measurable `g ≤ 1`
and a set `G` with `ν Gᶜ ≤ ρ` such that `f y ≤ g b + η` whenever `b ∈ G` and `dist y b < δ`,
we get `∫ f dμ ≤ ∫ g dν + η + ρ + e`. -/
theorem lintegral_le_add_of_prokhorovLE {μ ν : Measure E} [IsProbabilityMeasure ν]
    {δ e η ρ : ℝ} (hη : 0 ≤ η) (hP : ProkhorovLE μ ν δ e)
    {f g : E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hf1 : ∀ y, f y ≤ 1)
    (hg1 : ∀ b, g b ≤ 1) {G : Set E} (hρ : ν Gᶜ ≤ ENNReal.ofReal ρ)
    (hH : ∀ b ∈ G, ∀ y, dist y b < δ → f y ≤ g b + ENNReal.ofReal η) :
    ∫⁻ y, f y ∂μ ≤ ∫⁻ b, g b ∂ν + ENNReal.ofReal η + ENNReal.ofReal ρ + ENNReal.ofReal e := by
  classical
  set F : E → ℝ := fun y => (f y).toReal with hF
  set H : E → ℝ := fun b => (g b).toReal + η with hHdef
  have hfin : ∀ y, f y ≠ ∞ := fun y => ne_top_of_le_ne_top ENNReal.one_ne_top (hf1 y)
  have hgfin : ∀ b, g b ≠ ∞ := fun b => ne_top_of_le_ne_top ENNReal.one_ne_top (hg1 b)
  have hFm : Measurable F := hf.ennreal_toReal
  have hHm : Measurable H := hg.ennreal_toReal.add_const η
  have hFnn : 0 ≤ᵐ[μ] F := Filter.Eventually.of_forall fun y => ENNReal.toReal_nonneg
  have hHnn : 0 ≤ᵐ[ν] H :=
    Filter.Eventually.of_forall fun b => add_nonneg ENNReal.toReal_nonneg hη
  have hF1 : ∀ y, F y ≤ 1 := fun y => by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hf1 y)
    simpa using this
  have h1 : ∫⁻ y, f y ∂μ = ∫⁻ t in Ioi (0 : ℝ), μ {a | t < F a} := by
    rw [← lintegral_eq_lintegral_meas_lt μ hFnn hFm.aemeasurable]
    exact lintegral_congr fun y => (ENNReal.ofReal_toReal (hfin y)).symm
  have h2 : ∫⁻ b, g b ∂ν + ENNReal.ofReal η = ∫⁻ t in Ioi (0 : ℝ), ν {a | t < H a} := by
    rw [← lintegral_eq_lintegral_meas_lt ν hHnn hHm.aemeasurable]
    have hgH : ∀ b, ENNReal.ofReal (H b) = g b + ENNReal.ofReal η := fun b => by
      simp only [hHdef]
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hη, ENNReal.ofReal_toReal (hgfin b)]
    simp_rw [hgH]
    rw [lintegral_add_right _ measurable_const]
    simp
  have h3 : ∀ t : ℝ, μ {a | t < F a} ≤
      ν {a | t < H a} + (ENNReal.ofReal ρ + ENNReal.ofReal e) := by
    intro t
    have hA : MeasurableSet {a | t < F a} := measurableSet_lt measurable_const hFm
    refine (hP _ hA).trans ?_
    have hsub : thickening δ {a | t < F a} ⊆ {a | t < H a} ∪ Gᶜ := by
      intro b hb
      by_cases hbG : b ∈ G
      · left
        obtain ⟨y, hy, hdist⟩ := Metric.mem_thickening_iff.1 hb
        have hle := hH b hbG y (by rwa [dist_comm])
        have hy' : t < F y := hy
        show t < H b
        have h4 : F y ≤ H b := by
          have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hgfin b, ENNReal.ofReal_ne_top⟩) hle
          rwa [ENNReal.toReal_add (hgfin b) ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal hη] at this
        exact lt_of_lt_of_le hy' h4
      · right
        exact hbG
    calc ν (thickening δ {a | t < F a}) + ENNReal.ofReal e
        ≤ ν ({a | t < H a} ∪ Gᶜ) + ENNReal.ofReal e := by gcongr
      _ ≤ (ν {a | t < H a} + ν Gᶜ) + ENNReal.ofReal e := by
          gcongr
          exact measure_union_le _ _
      _ ≤ (ν {a | t < H a} + ENNReal.ofReal ρ) + ENNReal.ofReal e := by gcongr
      _ = ν {a | t < H a} + (ENNReal.ofReal ρ + ENNReal.ofReal e) := by ring
  have h5 : ∀ t ∈ Ioi (0 : ℝ), μ {a | t < F a} ≤ ν {a | t < H a} +
      (Ioc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal ρ + ENNReal.ofReal e) t := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, ht1⟩)]
      exact h3 t
    · have hempty : {a | t < F a} = ∅ := by
        ext a
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (hF1 a).trans (not_le.1 ht1).le
      rw [hempty]
      simp
  have h6 : ∫⁻ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) 1).indicator
      (fun _ => ENNReal.ofReal ρ + ENNReal.ofReal e) t ≤
      ENNReal.ofReal ρ + ENNReal.ofReal e := by
    rw [lintegral_indicator_const measurableSet_Ioc,
      Measure.restrict_apply measurableSet_Ioc]
    calc (ENNReal.ofReal ρ + ENNReal.ofReal e) * volume (Ioc (0 : ℝ) 1 ∩ Ioi 0)
        ≤ (ENNReal.ofReal ρ + ENNReal.ofReal e) * volume (Ioc (0 : ℝ) 1) := by
          gcongr
          exact inter_subset_left
      _ = ENNReal.ofReal ρ + ENNReal.ofReal e := by simp
  calc ∫⁻ y, f y ∂μ = ∫⁻ t in Ioi (0 : ℝ), μ {a | t < F a} := h1
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), (ν {a | t < H a} +
        (Ioc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal ρ + ENNReal.ofReal e) t) :=
        setLIntegral_mono' measurableSet_Ioi h5
    _ = (∫⁻ t in Ioi (0 : ℝ), ν {a | t < H a}) + ∫⁻ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) 1).indicator
        (fun _ => ENNReal.ofReal ρ + ENNReal.ofReal e) t :=
        lintegral_add_right _ (measurable_const.indicator measurableSet_Ioc)
    _ ≤ (∫⁻ b, g b ∂ν + ENNReal.ofReal η) + (ENNReal.ofReal ρ + ENNReal.ofReal e) := by
        rw [h2]
        exact add_le_add le_rfl h6
    _ = ∫⁻ b, g b ∂ν + ENNReal.ofReal η + ENNReal.ofReal ρ + ENNReal.ofReal e := by ring

/-- One step of a chain, in the one-sided Prokhorov sense.  The kernels `κ, κ'` are uniformly
`ε`-close at every starting point, `κ'` is `η`-continuous at the points of `G` at scale `δ`,
`ν Gᶜ ≤ ρ` and `μ` is `(δ, e)`-close to `ν`; then `μ.bind κ` is `(ε + η, ε + η + ρ + e)`-close
to `ν.bind κ'`.  Neither the continuity of `κ` nor that of `κ'` on `Gᶜ` is used. -/
theorem prokhorovLE_bind {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {κ κ' : E → Measure E} (hκ : Measurable κ) (hκ' : Measurable κ')
    [∀ y, IsProbabilityMeasure (κ' y)] {ε δ η ρ e : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hρ0 : 0 ≤ ρ) (he : 0 ≤ e) (hP : ProkhorovLE μ ν δ e)
    (hK : ∀ y, ProkhorovLE (κ y) (κ' y) ε ε) {G : Set E} (hG : ν Gᶜ ≤ ENNReal.ofReal ρ)
    (hcont : ∀ b ∈ G, ∀ y, dist y b < δ → ∀ A : Set E, MeasurableSet A →
      κ' y A ≤ κ' b (thickening η A) + ENNReal.ofReal η) :
    ProkhorovLE (μ.bind κ) (ν.bind κ') (ε + η) (ε + η + ρ + e) := by
  intro A hA
  have hA' : MeasurableSet (thickening ε A) := isOpen_thickening.measurableSet
  have hA'' : MeasurableSet (thickening η (thickening ε A)) := isOpen_thickening.measurableSet
  have hAt : MeasurableSet (thickening (ε + η) A) := isOpen_thickening.measurableSet
  rw [Measure.bind_apply hA hκ.aemeasurable]
  set f : E → ℝ≥0∞ := fun y => κ' y (thickening ε A) with hf
  set g : E → ℝ≥0∞ := fun b => κ' b (thickening η (thickening ε A)) with hg
  have hfm : Measurable f := (Measure.measurable_coe hA').comp hκ'
  have hgm : Measurable g := (Measure.measurable_coe hA'').comp hκ'
  have step1 : ∫⁻ y, κ y A ∂μ ≤ ∫⁻ y, f y ∂μ + ENNReal.ofReal ε := by
    calc ∫⁻ y, κ y A ∂μ ≤ ∫⁻ y, (f y + ENNReal.ofReal ε) ∂μ :=
          lintegral_mono fun y => hK y A hA
      _ = ∫⁻ y, f y ∂μ + ENNReal.ofReal ε := by
          rw [lintegral_add_right _ measurable_const]
          simp
  have step2 : ∫⁻ y, f y ∂μ ≤
      ∫⁻ b, g b ∂ν + ENNReal.ofReal η + ENNReal.ofReal ρ + ENNReal.ofReal e :=
    lintegral_le_add_of_prokhorovLE hη hP hfm hgm (fun y => prob_le_one) (fun b => prob_le_one)
      hG (fun b hb y hy => hcont b hb y hy (thickening ε A) hA')
  have step3 : ∫⁻ b, g b ∂ν ≤ (ν.bind κ') (thickening (ε + η) A) := by
    rw [Measure.bind_apply hAt hκ'.aemeasurable]
    refine lintegral_mono fun b => measure_mono ?_
    exact (thickening_thickening_subset η ε A).trans (thickening_mono (le_of_eq (add_comm _ _)) A)
  have hsum : ENNReal.ofReal (ε + η + ρ + e) =
      ENNReal.ofReal ε + ENNReal.ofReal η + ENNReal.ofReal ρ + ENNReal.ofReal e := by
    rw [ENNReal.ofReal_add (by positivity) he, ENNReal.ofReal_add (by positivity) hρ0,
      ENNReal.ofReal_add hε hη]
  rw [hsum]
  calc ∫⁻ y, κ y A ∂μ ≤ ∫⁻ y, f y ∂μ + ENNReal.ofReal ε := step1
    _ ≤ (∫⁻ b, g b ∂ν + ENNReal.ofReal η + ENNReal.ofReal ρ + ENNReal.ofReal e) +
        ENNReal.ofReal ε := by gcongr
    _ ≤ ((ν.bind κ') (thickening (ε + η) A) + ENNReal.ofReal η + ENNReal.ofReal ρ +
        ENNReal.ofReal e) + ENNReal.ofReal ε := by gcongr
    _ = (ν.bind κ') (thickening (ε + η) A) +
        (ENNReal.ofReal ε + ENNReal.ofReal η + ENNReal.ofReal ρ + ENNReal.ofReal e) := by ring

/-- **One step of a chain with a support set and a decoupled continuity radius.**  As
`prokhorovLE_bind`, but the continuity hypothesis on `κ'` is only needed at the starting points
`y` of a measurable set `H` of full `μ`-measure, and its thickening radius `r_c` is independent of
the additive error `η` and of the scale `δ`; the conclusion has radius `ε + r_c` and error
`ε + η + ρ + e`.  This is the form that iterates when the continuity of the kernel `κ'` holds in
total variation (small `η`) at a fixed radius `r_c`. -/
theorem prokhorovLE_bind_split {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {κ κ' : E → Measure E} (hκ : Measurable κ) (hκ' : Measurable κ')
    [∀ y, IsProbabilityMeasure (κ' y)] {ε δ r_c η ρ e : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hρ0 : 0 ≤ ρ) (he : 0 ≤ e) (hP : ProkhorovLE μ ν δ e)
    (hK : ∀ y, ProkhorovLE (κ y) (κ' y) ε ε) {H G : Set E} (hH : MeasurableSet H)
    (hμH : μ Hᶜ = 0) (hG : ν Gᶜ ≤ ENNReal.ofReal ρ)
    (hcont : ∀ b ∈ G, ∀ y ∈ H, dist y b < δ → ∀ A : Set E, MeasurableSet A →
      κ' y A ≤ κ' b (thickening r_c A) + ENNReal.ofReal η) :
    ProkhorovLE (μ.bind κ) (ν.bind κ') (ε + r_c) (ε + η + ρ + e) := by
  intro A hA
  have hA' : MeasurableSet (thickening ε A) := isOpen_thickening.measurableSet
  have hA'' : MeasurableSet (thickening r_c (thickening ε A)) := isOpen_thickening.measurableSet
  have hAt : MeasurableSet (thickening (ε + r_c) A) := isOpen_thickening.measurableSet
  rw [Measure.bind_apply hA hκ.aemeasurable]
  set f : E → ℝ≥0∞ := fun y => κ' y (thickening ε A) with hf
  set g : E → ℝ≥0∞ := fun b => κ' b (thickening r_c (thickening ε A)) with hg
  have hfm : Measurable f := (Measure.measurable_coe hA').comp hκ'
  have hgm : Measurable g := (Measure.measurable_coe hA'').comp hκ'
  have hfHm : Measurable (H.indicator f) := hfm.indicator hH
  have hfH1 : ∀ y, H.indicator f y ≤ 1 := fun y =>
    (Set.indicator_le_self H f y).trans prob_le_one
  have hae : ∀ᵐ y ∂μ, y ∈ H := ae_iff.2 hμH
  have step1 : ∫⁻ y, κ y A ∂μ ≤ ∫⁻ y, H.indicator f y ∂μ + ENNReal.ofReal ε := by
    calc ∫⁻ y, κ y A ∂μ ≤ ∫⁻ y, (f y + ENNReal.ofReal ε) ∂μ :=
          lintegral_mono fun y => hK y A hA
      _ = ∫⁻ y, f y ∂μ + ENNReal.ofReal ε := by
          rw [lintegral_add_right _ measurable_const]
          simp
      _ = ∫⁻ y, H.indicator f y ∂μ + ENNReal.ofReal ε := by
          congr 1
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with y hy
          rw [Set.indicator_of_mem hy]
  have step2 : ∫⁻ y, H.indicator f y ∂μ ≤
      ∫⁻ b, g b ∂ν + ENNReal.ofReal η + ENNReal.ofReal ρ + ENNReal.ofReal e := by
    refine lintegral_le_add_of_prokhorovLE hη hP hfHm hgm hfH1 (fun b => prob_le_one) hG ?_
    intro b hb y hy
    by_cases hyH : y ∈ H
    · rw [Set.indicator_of_mem hyH]
      exact hcont b hb y hyH hy (thickening ε A) hA'
    · rw [Set.indicator_of_notMem hyH]
      exact zero_le
  have step3 : ∫⁻ b, g b ∂ν ≤ (ν.bind κ') (thickening (ε + r_c) A) := by
    rw [Measure.bind_apply hAt hκ'.aemeasurable]
    refine lintegral_mono fun b => measure_mono ?_
    exact (thickening_thickening_subset r_c ε A).trans
      (thickening_mono (le_of_eq (add_comm _ _)) A)
  have hsum : ENNReal.ofReal (ε + η + ρ + e) =
      ENNReal.ofReal ε + ENNReal.ofReal η + ENNReal.ofReal ρ + ENNReal.ofReal e := by
    rw [ENNReal.ofReal_add (by positivity) he, ENNReal.ofReal_add (by positivity) hρ0,
      ENNReal.ofReal_add hε hη]
  rw [hsum]
  calc ∫⁻ y, κ y A ∂μ ≤ ∫⁻ y, H.indicator f y ∂μ + ENNReal.ofReal ε := step1
    _ ≤ (∫⁻ b, g b ∂ν + ENNReal.ofReal η + ENNReal.ofReal ρ + ENNReal.ofReal e) +
        ENNReal.ofReal ε := by gcongr
    _ ≤ ((ν.bind κ') (thickening (ε + r_c) A) + ENNReal.ofReal η + ENNReal.ofReal ρ +
        ENNReal.ofReal e) + ENNReal.ofReal ε := by gcongr
    _ = (ν.bind κ') (thickening (ε + r_c) A) +
        (ENNReal.ofReal ε + ENNReal.ofReal η + ENNReal.ofReal ρ + ENNReal.ofReal e) := by ring

end LatticeProb
