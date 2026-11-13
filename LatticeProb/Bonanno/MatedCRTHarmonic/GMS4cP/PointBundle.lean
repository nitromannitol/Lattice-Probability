/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.PointBundle at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.PointFactor
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.SampleBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.ZeroCone
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.BundleExcursions
import LatticeProb.Bonanno.MatedCRTHarmonic.Canon.ClockMeasurable
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108P2

/-!
# The local all-visit point factor of (4.22) for the zero cone

Source: [18] Lemma 4.3 and (4.22) (`2183–2208`).

For the frozen zero-cone model, a point `z`, mesh `ε ∈ (0,1)`, exponent `q` and an open `W` containing the
`ε^q/4`-thickening of `V₂ = B_{9ε^q/2}(z)`: given a Borel reader of the restricted LQG area `μ_{h₀}|_{V₂}` from
`h₀|_W` (the area half of Lemma 4.3), there is a **Borel** function of `(h₀|_W, h^IG|_W, U)` equal almost surely
to `truePointFactor η₀ z ε (ε^q) ζ`: the window test and degree cap of (4.22) at **every** visit times
`DA′(z)(deg′_in(z) + deg′_out(z))` (`l43p_zeroCone_pointFactor`). The two circle-average conditions of (4.22) at
radius `ε^{q−4ζ}` are not functions of the field near `z` and are kept as separate observables.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b MatedCRTHarmonic.GMS4c MatedCRTHarmonic.MatedCRT

attribute [local instance] Classical.propDecidable

/-- The segment data of an actual configuration. -/
theorem segments_of_cfg {U : TopologicalSpace.Opens ℂ} (hUb : Bornology.IsBounded (U : Set ℂ))
    {μ : Measure ℂ} {h : LQGMetric.DistC} {ηL : C(ℝ, ℂ)} {η : ℝ → ℂ} {φ : ℝ ≃o ℝ}
    (hfin : μ U < ⊤) (hreg : ExcursionRegular U ηL) (hcurve : ∀ t, η t = ηL (φ t))
    (hparam : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s)) :
    IsExcursionFamily η U (l43pLabels U)
        (fun q => φ.symm (entryBefore ηL U (ratPt q)))
        (fun q => φ.symm (exitAfter ηL U (ratPt q))) ∧
      ∀ q ∈ l43pLabels U, ⇑(l43pSegments U (localConfiguration U μ h ηL) q) =
        clampSeg η (φ.symm (entryBefore ηL U (ratPt q))) (φ.symm (exitAfter ηL U (ratPt q))) := by
  have hfin' : IsFiniteMeasure (localConfiguration U μ h ηL).1.1 := by
    change IsFiniteMeasure (μ.restrict U)
    exact isFiniteMeasure_restrict.mpr hfin.ne
  let ηc : C(ℝ, ℂ) := ⟨η, by
    have : η = fun t => ηL (φ t) := funext hcurve
    rw [this]
    exact ηL.continuous.comp φ.continuous⟩
  refine ⟨isExcursionFamily_of_regular U.isOpen hUb hreg hcurve, fun q hq => ?_⟩
  have hex := (isExcursion_entry_exit U.isOpen hUb hreg.surjective hreg.transient hq).1
  unfold l43pSegments
  rw [l43pFinite_of_finite hfin']
  exact localQuantumCurve_cfg (η := ηc) hfin' hcurve hparam hq hex

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The local all-visit point factor of (4.22) is an almost-sure Borel function of the local observation.** -/
theorem l43p_zeroCone_pointFactor
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε q : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (ζ : ℝ) (z : ℂ)
    (W : TopologicalSpace.Opens ℂ)
    (hW : thickening (ε ^ q / 4) (ball z (9 / 2 * ε ^ q)) ⊆ (W : Set ℂ))
    (hA : ∃ F : LQGMetric.DistOn W → Measure ℂ, Measurable F ∧ ∀ᵐ ω ∂P,
      F (LQGMetric.restrictTo W ((l46tZeroConeCellModel D hγ).field ω)) =
        (CellScaling.lqgArea γ ((l46tZeroConeCellModel D hγ).field ω)).restrict
          (ball z (9 / 2 * ε ^ q))) :
    ∃ factor : LQGMetric.DistOn W × (LQGMetric.DistOn W × ℝ) → ℝ, Measurable factor ∧
      ∀ᵐ ω ∂P, factor (LQGMetric.restrictTo W ((l46tZeroConeCellModel D hγ).field ω),
          (LQGMetric.restrictTo W (hIG₀ ω), T ω)) =
        truePointFactor (η₀ ω) z ε (ε ^ q) ζ := by
  have hP := D.isProbabilityMeasure
  obtain ⟨F, hF, hFae⟩ := hA
  set r₀ : ℝ := ε ^ q with hr₀def
  have hr₀ : 0 < r₀ := Real.rpow_pos_of_pos hε.1 q
  set V₂ : TopologicalSpace.Opens ℂ := ⟨ball z (9 / 2 * r₀), isOpen_ball⟩
  have hV₂b : Bornology.IsBounded (V₂ : Set ℂ) := isBounded_ball
  have hδ' : 0 < r₀ / 4 := by positivity
  set Wth : TopologicalSpace.Opens ℂ :=
    ⟨thickening (r₀ / 4) (V₂ : Set ℂ), isOpen_thickening⟩
  have hWthW : Wth ≤ W := hW
  have hV₂W : V₂ ≤ W := fun y hy => hW (self_subset_thickening hδ' _ hy)
  obtain ⟨g, hg, hgae⟩ := ae_bundle_excursions_from_localIG D V₂ hV₂b (r₀ / 4) hδ'
  -- the configuration reader
  let R : LQGMetric.DistOn W × (LQGMetric.DistOn W × ℝ) → LocalConfiguration V₂ := fun x =>
    ((F x.1, LQGMetric.CONF.resUW W V₂ x.1),
      fun q => if ratPt q ∈ V₂ then g (LQGMetric.CONF.resUW W Wth x.2.1, x.2.2) q else 0)
  have hR : Measurable R := by
    have h1 : Measurable fun x : LQGMetric.DistOn W × (LQGMetric.DistOn W × ℝ) =>
        (F x.1, LQGMetric.CONF.resUW W V₂ x.1) :=
      (hF.comp measurable_fst).prodMk ((LQGMetric.CONF.measurable_resUW W V₂).comp measurable_fst)
    have h2 : Measurable fun x : LQGMetric.DistOn W × (LQGMetric.DistOn W × ℝ) =>
        (fun q => if ratPt q ∈ V₂ then g (LQGMetric.CONF.resUW W Wth x.2.1, x.2.2) q else 0 :
          ℚ × ℚ → ℝ → ℂ) := by
      refine measurable_pi_iff.mpr fun q => ?_
      by_cases hq : ratPt q ∈ V₂
      · simp only [hq, ↓reduceIte]
        exact (measurable_pi_apply q).comp (hg.comp
          (((LQGMetric.CONF.measurable_resUW W Wth).comp (measurable_fst.comp measurable_snd)).prodMk
            (measurable_snd.comp measurable_snd)))
      · simp only [hq, ↓reduceIte]
        exact measurable_const
    exact h1.prodMk h2
  let obs : Ω → LQGMetric.DistOn W × (LQGMetric.DistOn W × ℝ) := fun ω =>
    (LQGMetric.restrictTo W ((l46tZeroConeCellModel D hγ).field ω),
      (LQGMetric.restrictTo W (hIG₀ ω), T ω))
  have hobs : AEMeasurable obs P := by
    have hU : AEMeasurable T P :=
      MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif
        (IGLaw.period_pos_of_uniform D.igField.2.1) D.igField.2.1
    have hfield : AEMeasurable (l46tZeroConeCellModel D hγ).field P :=
      Canon.aemeasurable_reference_field D hγ
    exact ((LQGMetric.measurable_restrictTo W).comp_aemeasurable hfield).prodMk
      (((LQGMetric.measurable_restrictTo W).comp D.igField.1.1.measurable).aemeasurable.prodMk hU)
  have hRae : ∀ᵐ ω ∂P, R (obs ω) = localConfiguration V₂
      (CellScaling.lqgArea γ ((l46tZeroConeCellModel D hγ).field ω))
      ((l46tZeroConeCellModel D hγ).field ω) (ηL ω) := by
    filter_upwards [hFae, hgae] with ω hFω hgω
    simp only [R, obs, localConfiguration]
    rw [hFω, LQGMetric.CONF.resUW_restrictTo hV₂W, LQGMetric.CONF.resUW_restrictTo hWthW]
    congr 1
    funext q
    by_cases hqV : ratPt q ∈ V₂
    · simp only [hqV, ↓reduceIte]
      exact (hgω q hqV).symm
    · simp [hqV]
  -- the local factor and its Borel modification
  let Y : LQGMetric.DistOn W × (LQGMetric.DistOn W × ℝ) → SegSpace := fun x =>
    l43pSegments V₂ (R x)
  have hY : Measurable Y := (measurable_l43pSegments V₂).comp hR
  let f : SegSpace → ℝ := locPointFactor (l43pLabels V₂) z ε r₀ ζ
  let ν : Measure SegSpace := P.map (fun ω => Y (obs ω))
  have hYobs : AEMeasurable (fun ω => Y (obs ω)) P := hY.comp_aemeasurable hobs
  have : IsFiniteMeasure ν := Measure.isFiniteMeasure_map P _
  have hfae : AEMeasurable f ν :=
    (nullMeasurable_locPointFactor (l43pLabels V₂) z ε r₀ ζ ν).aemeasurable
  refine ⟨fun x => hfae.mk f (Y x), hfae.measurable_mk.comp hY, ?_⟩
  have hmk : ∀ᵐ ω ∂P, f (Y (obs ω)) = hfae.mk f (Y (obs ω)) :=
    ae_of_ae_map hYobs hfae.ae_eq_mk
  have hz4 : closedBall z (4 * r₀) ⊆ (V₂ : Set ℂ) := closedBall_subset_ball (by linarith)
  filter_upwards [hmk, hRae, D.areaParam₀, ae_bundle_excursionRegular D V₂ hV₂b,
    (l46tZeroConeCellModel D hγ).ae_area_curve] with ω hmkω hRω harea hreg hparam
  obtain ⟨φ, -, hcurve⟩ := harea.1
  change hfae.mk f (Y (obs ω)) = _
  rw [← hmkω]
  simp only [f, Y]
  rw [hRω]
  obtain ⟨hD, hσ⟩ := segments_of_cfg hV₂b (lqgArea_bounded_lt_top γ _ hV₂b) hreg hcurve hparam
  exact locPointFactor_eq (η₀ ω).continuous hε.1.le hD hparam hσ hr₀.le hz4 ζ

end MatedCRTHarmonic.GMS4cP
