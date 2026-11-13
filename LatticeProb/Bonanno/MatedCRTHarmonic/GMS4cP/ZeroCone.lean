/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.ZeroCone at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.Reconstruction
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TModel
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge

/-!
# The transferred Lemma 4.6 for the zero-quantum cone, from the configuration form of Lemma 4.3

Source: [18] Lemmas 4.3, 4.6 and (4.16) (`1968–2019`,
`2070–2116`).

`L43PZeroConeConfigInput D hγ ρ w` is the configuration form of measurable [18] Lemma 4.3 on the transfer's observation
disk `V = B_{(1−ρ)/4}(w)` and reconstruction disk `U = B_{(1−ρ)/8}(w)`: one Borel map of the observation
`(h|_V, h^IG|_V, U)` returning, almost surely, the actual local configuration `(μ|_U, h|_U, η_L` excursions`)`
both for the γ-cone translated by `z₀ = w + (1−ρ)/2` (field, area pushed forward, curve `η_L + z₀`) and for the
zero cone. Given it and the transfer's (4.16) comparison, `l43p_zeroCone_innerDegreeBoundPolylog` proves the
polylogarithmic Lemma 4.6 for the frozen zero-cone model. All model facts (excursion regularity of `η_L` and
of `η_L + z₀`, area parametrization of both quantum-time curves, finiteness of the local area, attained first
hitting times) are derived here from the frozen bundle.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b MatedCRTHarmonic.GMS4c MatedCRTHarmonic.MatedCRT

/-- A continuous curve translated in space. -/
def translateC (z₀ : ℂ) (c : C(ℝ, ℂ)) : C(ℝ, ℂ) := ⟨fun t => c t + z₀, by fun_prop⟩

theorem translateC_image (z₀ : ℂ) (c : C(ℝ, ℂ)) (s : Set ℝ) :
    translateC z₀ c '' s = (fun x => x + z₀) '' (c '' s) := by
  rw [image_image]
  rfl

/-- Excursion regularity is preserved by spatial translation, with the rational labels of the translated
region (the deterministic rational coverage). -/
theorem excursionRegular_translate {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {c : C(ℝ, ℂ)} (hsurj : Function.Surjective c)
    (htr : Tendsto c (cocompact ℝ) (cocompact ℂ))
    (hvol : ∀ s t : ℝ, s ≤ t → volume (c '' Icc s t) = ENNReal.ofReal (t - s))
    (hinter : ∀ a b : ℝ, a < b → (interior (c '' Icc a b)).Nonempty) (z₀ : ℂ) :
    ExcursionRegular U (translateC z₀ c) := by
  have hsurj' : Function.Surjective (translateC z₀ c) := by
    intro y
    obtain ⟨t, ht⟩ := hsurj (y - z₀)
    exact ⟨t, by simp [translateC, ht]⟩
  have htr' : Tendsto (translateC z₀ c) (cocompact ℝ) (cocompact ℂ) := by
    have : Tendsto (Homeomorph.addRight z₀) (cocompact ℂ) (cocompact ℂ) :=
      (Homeomorph.addRight z₀).map_cocompact.le
    exact this.comp htr
  have hvol' : ∀ s t : ℝ, s ≤ t →
      volume (translateC z₀ c '' Icc s t) = ENNReal.ofReal (t - s) := by
    intro s t hst
    rw [translateC_image, Set.image_add_right, measure_preimage_add_right, hvol s t hst]
  have hinter' : ∀ a b : ℝ, a < b → (interior (translateC z₀ c '' Icc a b)).Nonempty := by
    intro a b hab
    rw [translateC_image]
    have := (Homeomorph.addRight z₀).image_interior (c '' Icc a b)
    change (interior ((Homeomorph.addRight z₀) '' (c '' Icc a b))).Nonempty
    rw [← this]
    exact (hinter a b hab).image _
  refine ⟨hsurj', htr', ⟨volume, hvol'⟩, fun t ht => ?_⟩
  exact exists_ratPt_firstHit_excursion hU hUb hsurj' htr' hvol' hinter' ht

/-- The area of a bounded set under the frozen cone area is finite. -/
theorem lqgArea_bounded_lt_top (γ : ℝ) (h : LQGMetric.DistC) {A : Set ℂ}
    (hA : Bornology.IsBounded A) : CellScaling.lqgArea γ h A < ⊤ :=
  (measure_mono subset_closure).trans_lt
    (LQGCone.lqgArea_compact_lt_top γ h hA.isCompact_closure)

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The configuration form of measurable [18] Lemma 4.3** on the transfer's disks, for the translated γ-cone and the
zero cone of the frozen coupling. -/
def L43PZeroConeConfigInput
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ρ : ℝ) (w : ℂ) : Prop :=
  ∃ R₀ : L46TLocalFieldPhase (l46tObservation ρ w) → LocalConfiguration (l46tLocalRegion ρ w),
    Measurable R₀ ∧
    (∀ᵐ ω ∂P, R₀ (l46tLocalFieldPhase (l46tObservation ρ w)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) (MoTInput.cellModelOfCoupling D hγ).field)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) T ω) =
      localConfiguration (l46tLocalRegion ρ w)
        ((CellScaling.lqgArea γ ((MoTInput.cellModelOfCoupling D hγ).field ω)).map
          (fun x => x + (w + ((1 - ρ) / 2 : ℝ))))
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ))
          (MoTInput.cellModelOfCoupling D hγ).field ω)
        (translateC (w + ((1 - ρ) / 2 : ℝ)) (ηL ω))) ∧
    (∀ᵐ ω ∂P, R₀ (l46tLocalFieldPhase (l46tObservation ρ w)
        (l46tZeroConeCellModel D hγ).field hIG₀ T ω) =
      localConfiguration (l46tLocalRegion ρ w)
        (CellScaling.lqgArea γ ((l46tZeroConeCellModel D hγ).field ω))
        ((l46tZeroConeCellModel D hγ).field ω) (ηL ω))

/-- The zero-cone sample model, from the configuration identity. -/
theorem ae_zeroCone_sampleModel
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ρ : ℝ} {w : ℂ}
    {R₀ : L46TLocalFieldPhase (l46tObservation ρ w) → LocalConfiguration (l46tLocalRegion ρ w)}
    (hR : ∀ᵐ ω ∂P, R₀ (l46tLocalFieldPhase (l46tObservation ρ w)
        (l46tZeroConeCellModel D hγ).field hIG₀ T ω) =
      localConfiguration (l46tLocalRegion ρ w)
        (CellScaling.lqgArea γ ((l46tZeroConeCellModel D hγ).field ω))
        ((l46tZeroConeCellModel D hγ).field ω) (ηL ω)) :
    ∀ᵐ ω ∂P, L43PSampleModel R₀ (l46tLocalFieldPhase (l46tObservation ρ w)
        (l46tZeroConeCellModel D hγ).field hIG₀ T ω) (η₀ ω) := by
  have hUb : Bornology.IsBounded ((l46tLocalRegion ρ w : TopologicalSpace.Opens ℂ) : Set ℂ) :=
    isBounded_ball
  filter_upwards [hR, D.areaParam₀, ae_bundle_excursionRegular D (l46tLocalRegion ρ w) hUb,
    (l46tZeroConeCellModel D hγ).ae_area_curve] with ω hRω harea hreg hparam
  obtain ⟨φ, -, hcurve⟩ := harea.1
  exact ⟨_, _, ηL ω, φ, hRω, lqgArea_bounded_lt_top γ _ hUb, hreg, hcurve, hparam⟩

/-- The translated γ-cone sample model, from the configuration identity. -/
theorem ae_gammaTranslate_sampleModel
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ρ : ℝ} {w : ℂ}
    {R₀ : L46TLocalFieldPhase (l46tObservation ρ w) → LocalConfiguration (l46tLocalRegion ρ w)}
    (hR : ∀ᵐ ω ∂P, R₀ (l46tLocalFieldPhase (l46tObservation ρ w)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) (MoTInput.cellModelOfCoupling D hγ).field)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) T ω) =
      localConfiguration (l46tLocalRegion ρ w)
        ((CellScaling.lqgArea γ ((MoTInput.cellModelOfCoupling D hγ).field ω)).map
          (fun x => x + (w + ((1 - ρ) / 2 : ℝ))))
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ))
          (MoTInput.cellModelOfCoupling D hγ).field ω)
        (translateC (w + ((1 - ρ) / 2 : ℝ)) (ηL ω))) :
    ∀ᵐ ω ∂P, L43PSampleModel R₀ (l46tLocalFieldPhase (l46tObservation ρ w)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) (MoTInput.cellModelOfCoupling D hγ).field)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) T ω)
      (l46tTranslateCurve (w + ((1 - ρ) / 2 : ℝ)) (η ω)) := by
  set z₀ : ℂ := w + ((1 - ρ) / 2 : ℝ)
  have hUb : Bornology.IsBounded ((l46tLocalRegion ρ w : TopologicalSpace.Opens ℂ) : Set ℂ) :=
    isBounded_ball
  have hmeas : Measurable fun x : ℂ => x + z₀ := measurable_add_const z₀
  filter_upwards [hR, D.areaParam, D.spaceFilling, ae_ηL_intervals_have_interior D,
    (MoTInput.cellModelOfCoupling D hγ).ae_area_curve] with ω hRω harea hspace hinter hparam
  obtain ⟨φ, -, hcurve⟩ := harea.1
  have hreg := excursionRegular_translate (l46tLocalRegion ρ w).isOpen hUb hspace.1 hspace.2.1
    hspace.2.2.2 hinter z₀
  refine ⟨_, _, translateC z₀ (ηL ω), φ, hRω, ?_, hreg, ?_, ?_⟩
  · rw [Measure.map_apply hmeas (l46tLocalRegion ρ w).isOpen.measurableSet]
    have hsub : (fun x => x + z₀) ⁻¹' ((l46tLocalRegion ρ w : TopologicalSpace.Opens ℂ) : Set ℂ) ⊆
        ball (w - z₀) ((1 - ρ) / 8) := by
      intro x hx
      change dist (x + z₀) w < (1 - ρ) / 8 at hx
      rw [mem_ball, dist_eq_norm]
      rw [dist_eq_norm] at hx
      convert hx using 2
      ring
    exact lqgArea_bounded_lt_top γ _ (isBounded_ball.subset hsub)
  · intro t
    simp [l46tTranslateCurve, translateC, hcurve]
  · intro s t hst
    have himg : l46tTranslateCurve z₀ (η ω) '' Icc s t =
        (fun x => x + z₀) '' ((η ω : ℝ → ℂ) '' Icc s t) := by
      rw [image_image]
      rfl
    have hcpt : IsCompact ((fun x => x + z₀) '' ((η ω : ℝ → ℂ) '' Icc s t)) :=
      (isCompact_Icc.image (η ω).continuous).image (continuous_id.add continuous_const)
    rw [himg, Measure.map_apply hmeas hcpt.isClosed.measurableSet,
      preimage_image_eq _ (add_left_injective z₀)]
    exact hparam s t hst

end MatedCRTHarmonic.GMS4cP
