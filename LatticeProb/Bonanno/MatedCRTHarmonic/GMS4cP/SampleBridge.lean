/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.SampleBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalQuantumCurveBorel
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalQuantumInverse
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalClockMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ExcursionCoverage
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.LocalBorel

/-!
# From a stored local configuration to the quantum-time excursion segments

Source: the proof of [18] Lemma 4.3 : "`μ_h` is determined by
`h|_V` … From this, Lemma 2.4, and the definitions …". The local configuration `(μ|_U, h|_U, η_L` excursions`)`
of the reconstruction (`GMS4c.LocalConfiguration`) stores Lebesgue-time excursion segments of `η_L` and the restricted
area. the Borel rational-cut inverse of the mass clock turns each stored segment into a continuous
quantum-time curve `GMS4c.localQuantumCurve`. This file proves, for **any** area measure `μ` parametrizing the
quantum-time curve `η = η_L ∘ φ` (the reconstruction proved the case `μ = qAreaC γ h`), that these curves are exactly the
clamped quantum-time excursion segments `clampSeg η (φ⁻¹ T_q) (φ⁻¹ S_q)`, and that the transported entrance
and exit times form an `IsExcursionFamily` of `η`. Together with `GMS4cP/LocalEvents.lean` this reads the escape
and all-visit inner-degree events of `η` from the stored configuration, by one Borel map
`l43pSegments`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4c MatedCRTHarmonic.MatedCRT

attribute [local instance] Classical.propDecidable

/-! ## A measurable finite-area modification -/

/-- The configuration itself when its area coordinate is finite, and the zero configuration otherwise. -/
def l43pFinite (U : TopologicalSpace.Opens ℂ) (x : LocalConfiguration U) :
    FiniteLocalConfiguration U :=
  if h : IsFiniteMeasure x.1.1 then ⟨x, h⟩
  else ⟨((0, 0), 0), by change IsFiniteMeasure (0 : Measure ℂ); infer_instance⟩

theorem l43pFinite_of_finite {U : TopologicalSpace.Opens ℂ} {x : LocalConfiguration U}
    (h : IsFiniteMeasure x.1.1) : l43pFinite U x = ⟨x, h⟩ := by
  unfold l43pFinite
  rw [dite_eq_left h]

theorem measurable_l43pFinite (U : TopologicalSpace.Opens ℂ) : Measurable (l43pFinite U) := by
  have hfin : MeasurableSet {x : LocalConfiguration U | IsFiniteMeasure x.1.1} := by
    simp only [isFiniteMeasure_iff]
    exact measurableSet_lt
      ((Measure.measurable_coe MeasurableSet.univ).comp
        (measurable_fst.comp measurable_fst)) measurable_const
  let z : LocalConfiguration U := ((0, 0), 0)
  have hz : IsFiniteMeasure z.1.1 := by change IsFiniteMeasure (0 : Measure ℂ); infer_instance
  have hbase : Measurable fun x : LocalConfiguration U =>
      if IsFiniteMeasure x.1.1 then x else z :=
    Measurable.ite hfin measurable_id measurable_const
  have hprop (x : LocalConfiguration U) :
      IsFiniteMeasure (if IsFiniteMeasure x.1.1 then x else z).1.1 := by
    by_cases h : IsFiniteMeasure x.1.1
    · simp [h]
    · simpa [h] using hz
  have hsub : Measurable fun x : LocalConfiguration U =>
      (⟨if IsFiniteMeasure x.1.1 then x else z, hprop x⟩ : FiniteLocalConfiguration U) :=
    hbase.subtype_mk
  convert hsub using 1
  funext x
  by_cases h : IsFiniteMeasure x.1.1
  · simp [l43pFinite, h]
  · simp [l43pFinite, h, z]

/-- **The Borel segment reader**: every stored excursion, as a continuous quantum-time curve. -/
def l43pSegments (U : TopologicalSpace.Opens ℂ) (x : LocalConfiguration U) : SegSpace :=
  fun q => localQuantumCurve q (l43pFinite U x)

theorem measurable_l43pSegments (U : TopologicalSpace.Opens ℂ) :
    Measurable (l43pSegments U) :=
  measurable_pi_iff.mpr fun q =>
    (measurable_localQuantumCurve U q).comp (measurable_l43pFinite U)

/-! ## Clock inversion for a general area measure -/

section general

variable {U : TopologicalSpace.Opens ℂ} {μ : Measure ℂ} {h : LQGMetric.DistC}
  {ηL η : C(ℝ, ℂ)} {φ : ℝ ≃o ℝ}

theorem finiteLocalSegment_cfg (hfin : IsFiniteMeasure (localConfiguration U μ h ηL).1.1)
    {q : ℚ × ℚ} (hq : ratPt q ∈ U) :
    (finiteLocalSegment q ⟨localConfiguration U μ h ηL, hfin⟩ : ℝ → ℂ) =
      excursionSegment ηL U (ratPt q) := by
  have hc : Continuous (excursionSegment ηL U (ratPt q)) := by
    unfold excursionSegment
    fun_prop
  unfold finiteLocalSegment localConfiguration
  simp only [hq, ↓reduceIte, contVersion_coe hc]

theorem localSegmentMass_cfg (hfin : IsFiniteMeasure (localConfiguration U μ h ηL).1.1)
    {q : ℚ × ℚ} (hq : ratPt q ∈ U) (a b : ℝ) :
    localSegmentMass q a b ⟨localConfiguration U μ h ηL, hfin⟩ =
      (μ.restrict U) (excursionSegment ηL U (ratPt q) '' Icc a b) := by
  unfold localSegmentMass massClock
  rw [finiteLocalSegment_cfg hfin hq]
  rfl

theorem localQuantumElapsed_cfg (hfin : IsFiniteMeasure (localConfiguration U μ h ηL).1.1)
    (hcurve : ∀ t, η t = ηL (φ t))
    (hparam : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    {q : ℚ × ℚ} (hq : ratPt q ∈ U)
    (hex : IsExcursion ηL U (entryBefore ηL U (ratPt q)) (exitAfter ηL U (ratPt q)))
    {u : ℝ} (hu : 0 ≤ u) (hule : u ≤ exitAfter ηL U (ratPt q) - entryBefore ηL U (ratPt q)) :
    localQuantumElapsed q 0 u ⟨localConfiguration U μ h ηL, hfin⟩ =
      φ.symm (entryBefore ηL U (ratPt q) + u) - φ.symm (entryBefore ηL U (ratPt q)) := by
  unfold localQuantumElapsed
  rw [localSegmentMass_cfg hfin hq, restricted_excursion_mass_eq_quantum_elapsed_closed
    μ ηL η φ hcurve hparam U (ratPt q) u hex hu hule]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (φ.symm.monotone (by linarith)))

theorem localQuantumEval_cfg (hfin : IsFiniteMeasure (localConfiguration U μ h ηL).1.1)
    (hcurve : ∀ t, η t = ηL (φ t))
    (hparam : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    {q : ℚ × ℚ} (hq : ratPt q ∈ U)
    (hex : IsExcursion ηL U (entryBefore ηL U (ratPt q)) (exitAfter ηL U (ratPt q)))
    {t : ℝ} (ht : 0 < t)
    (htop : t ≤ φ.symm (exitAfter ηL U (ratPt q)) - φ.symm (entryBefore ηL U (ratPt q))) :
    localQuantumEval q ⟨localConfiguration U μ h ηL, hfin⟩ t =
      η (φ.symm (entryBefore ηL U (ratPt q)) + t) := by
  set a := entryBefore ηL U (ratPt q)
  set b := exitAfter ηL U (ratPt q)
  set u := φ (φ.symm a + t) - a
  have hu0 : 0 ≤ u := by
    have hmono := φ.strictMono (show φ.symm a < φ.symm a + t by linarith)
    rw [φ.apply_symm_apply] at hmono
    simp only [u]
    linarith
  have hub : u ≤ b - a := by
    have hmono := φ.monotone (show φ.symm a + t ≤ φ.symm b by linarith)
    rw [φ.apply_symm_apply] at hmono
    simp only [u]
    linarith
  have hinv : localQuantumInverse q ⟨localConfiguration U μ h ηL, hfin⟩ t = u := by
    apply localQuantumInverse_eq_orderIso q _ φ hex.lt ht htop
    intro r hr hrb
    exact localQuantumElapsed_cfg hfin hcurve hparam hq hex hr hrb
  unfold localQuantumEval
  rw [hinv, finiteLocalSegment_cfg hfin hq]
  change ηL (a + max 0 (min u (b - a))) = η (φ.symm a + t)
  rw [min_eq_left hub, max_eq_right hu0, hcurve]
  congr 1
  simp only [u]
  ring

theorem localQuantumTotal_cfg (hfin : IsFiniteMeasure (localConfiguration U μ h ηL).1.1)
    (hcurve : ∀ t, η t = ηL (φ t))
    (hparam : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    {q : ℚ × ℚ} (hq : ratPt q ∈ U)
    (hex : IsExcursion ηL U (entryBefore ηL U (ratPt q)) (exitAfter ηL U (ratPt q))) :
    localQuantumTotal q ⟨localConfiguration U μ h ηL, hfin⟩ =
      φ.symm (exitAfter ηL U (ratPt q)) - φ.symm (entryBefore ηL U (ratPt q)) := by
  set a := entryBefore ηL U (ratPt q)
  set b := exitAfter ηL U (ratPt q)
  set x : FiniteLocalConfiguration U := ⟨localConfiguration U μ h ηL, hfin⟩
  have hd : 0 ≤ b - a := sub_nonneg.mpr hex.lt.le
  have himg : ∀ n : ℝ, b - a ≤ n →
      excursionSegment ηL U (ratPt q) '' Icc 0 n =
        excursionSegment ηL U (ratPt q) '' Icc 0 (b - a) := by
    intro n hn
    have h1 := clampSeg_image_Icc_zero_of_ge (c := ηL) hex.lt.le hn
    have h2 := clampSeg_image_Icc_zero_of_ge (c := ηL) hex.lt.le (le_refl (b - a))
    change clampSeg ηL a b '' Icc 0 n = clampSeg ηL a b '' Icc 0 (b - a)
    rw [h1, h2]
  have hmass : localSegmentMass q 0 (b - a) x = ENNReal.ofReal (φ.symm b - φ.symm a) := by
    rw [localSegmentMass_cfg hfin hq, restricted_excursion_mass_eq_quantum_elapsed_closed
      μ ηL η φ hcurve hparam U (ratPt q) (b - a) hex hd le_rfl]
    have hab : entryBefore ηL U (ratPt q) + (b - a) = b := by simp only [a]; ring
    rw [hab]
  have hbound (n : ℕ) : localSegmentMass q 0 n x ≤ localSegmentMass q 0 (b - a) x := by
    rw [localSegmentMass_cfg hfin hq, localSegmentMass_cfg hfin hq]
    by_cases hn : (n : ℝ) ≤ b - a
    · exact measure_mono (image_mono (Icc_subset_Icc le_rfl hn))
    · rw [himg n (le_of_not_ge hn)]
  obtain ⟨n, hn⟩ := exists_nat_ge (b - a)
  have hlarge : localSegmentMass q 0 n x = localSegmentMass q 0 (b - a) x := by
    rw [localSegmentMass_cfg hfin hq, localSegmentMass_cfg hfin hq, himg n hn]
  have hsup : (⨆ n : ℕ, localSegmentMass q 0 n x) = localSegmentMass q 0 (b - a) x :=
    le_antisymm (iSup_le hbound) (le_iSup_of_le n hlarge.ge)
  unfold localQuantumTotal
  rw [hsup, hmass]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (φ.symm.monotone hex.lt.le))

/-- **The stored excursion, read in quantum time, is the clamped quantum-time excursion segment.** -/
theorem localQuantumCurve_cfg (hfin : IsFiniteMeasure (localConfiguration U μ h ηL).1.1)
    (hcurve : ∀ t, η t = ηL (φ t))
    (hparam : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    {q : ℚ × ℚ} (hq : ratPt q ∈ U)
    (hex : IsExcursion ηL U (entryBefore ηL U (ratPt q)) (exitAfter ηL U (ratPt q))) :
    (localQuantumCurve q ⟨localConfiguration U μ h ηL, hfin⟩ : ℝ → ℂ) =
      clampSeg η (φ.symm (entryBefore ηL U (ratPt q))) (φ.symm (exitAfter ηL U (ratPt q))) := by
  set a := entryBefore ηL U (ratPt q)
  set b := exitAfter ηL U (ratPt q)
  set x : FiniteLocalConfiguration U := ⟨localConfiguration U μ h ηL, hfin⟩
  set M := φ.symm b - φ.symm a
  have hM : 0 < M := sub_pos.mpr (φ.symm.strictMono hex.lt)
  have htotal : localQuantumTotal q x = M := localQuantumTotal_cfg hfin hcurve hparam hq hex
  have hclamp : ∀ t, localQuantumEvalClamped q x t = clampSeg η (φ.symm a) (φ.symm b) t := by
    intro t
    unfold localQuantumEvalClamped
    by_cases ht0 : t ≤ 0
    · rw [ite_eq_left ht0, clampSeg_of_nonpos ht0]
      have hs := finiteLocalSegment_cfg hfin hq
      change (finiteLocalSegment q x : ℝ → ℂ) 0 = _
      rw [hs]
      change ηL (a + max 0 (min 0 (b - a))) = η (φ.symm a)
      rw [min_eq_left (sub_nonneg.mpr hex.lt.le), max_self, add_zero, hcurve,
        φ.apply_symm_apply]
    · have ht0' : 0 < t := lt_of_not_ge ht0
      rw [ite_eq_right ht0, htotal]
      by_cases htM : M ≤ t
      · rw [ite_eq_left htM, localQuantumEval_cfg hfin hcurve hparam hq hex hM le_rfl,
          clampSeg_of_ge (φ.symm.monotone hex.lt.le) htM]
        congr 1
        simp only [M]
        ring
      · rw [ite_eq_right htM, localQuantumEval_cfg hfin hcurve hparam hq hex ht0'
          (le_of_lt (lt_of_not_ge htM)),
          clampSeg_of_mem ⟨ht0'.le, le_of_lt (lt_of_not_ge htM)⟩]
  have hcont : Continuous (clampSeg η (φ.symm a) (φ.symm b)) :=
    continuous_clampSeg η.continuous
  unfold localQuantumCurve
  rw [show (fun t => localQuantumEvalClamped q x t) = clampSeg η (φ.symm a) (φ.symm b) from
    funext hclamp, contVersion_coe hcont]

end general

/-! ## Excursion data of the quantum-time curve -/

/-- Rational labels of `U`. -/
def l43pLabels (U : Set ℂ) : Set (ℚ × ℚ) := {q | ratPt q ∈ U}

/-- The Lebesgue excursions of an excursion-regular curve, transported to the quantum-time curve
`η = η_L ∘ φ`, form an `IsExcursionFamily`. -/
theorem isExcursionFamily_of_regular {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {ηL : C(ℝ, ℂ)} (hreg : ExcursionRegular U ηL)
    {η : ℝ → ℂ} {φ : ℝ ≃o ℝ} (hcurve : ∀ t, η t = ηL (φ t)) :
    IsExcursionFamily η U (l43pLabels U)
      (fun q => φ.symm (entryBefore ηL U (ratPt q)))
      (fun q => φ.symm (exitAfter ηL U (ratPt q))) := by
  have hex : ∀ q ∈ l43pLabels U,
      IsExcursion ηL U (entryBefore ηL U (ratPt q)) (exitAfter ηL U (ratPt q)) := fun q hq =>
    (isExcursion_entry_exit hU hUb hreg.surjective hreg.transient hq).1
  refine ⟨fun q hq => φ.symm.strictMono (hex q hq).lt, fun q hq => ?_, fun q hq => ?_,
    fun q hq t ht => ?_, fun t ht => ?_⟩
  · rw [hcurve, φ.apply_symm_apply]
    exact (hex q hq).left
  · rw [hcurve, φ.apply_symm_apply]
    exact (hex q hq).right
  · rw [hcurve]
    apply (hex q hq).inside
    have h1 := φ.strictMono ht.1
    have h2 := φ.strictMono ht.2
    rw [φ.apply_symm_apply] at h1 h2
    exact ⟨h1, h2⟩
  · rw [hcurve] at ht
    obtain ⟨q, hq, h1, h2⟩ := hreg.exists_ratPt (φ t) ht
    refine ⟨q, hq, ?_, ?_⟩
    · have := φ.symm.strictMono h1
      rwa [φ.symm_apply_apply] at this
    · have := φ.symm.strictMono h2
      rwa [φ.symm_apply_apply] at this

/-- **One sample: the stored configuration determines the escape and all-visit inner events.** -/
theorem events_iff_of_cfg {U : TopologicalSpace.Opens ℂ} (hUb : Bornology.IsBounded (U : Set ℂ))
    {μ : Measure ℂ} {h : LQGMetric.DistC} {ηL : C(ℝ, ℂ)} {η : ℝ → ℂ} {φ : ℝ ≃o ℝ}
    (hfin : μ U < ⊤) (hreg : ExcursionRegular U ηL) (hcurve : ∀ t, η t = ηL (φ t))
    (hparam : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    {S : Set ℂ} (hSU : S ⊆ U) {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ) :
    (EscBad η S U ε ↔
        l43pSegments U (localConfiguration U μ h ηL) ∈ locEsc (l43pLabels U) S U ε) ∧
      (InnerAt η S ε N ∧ ¬ EscBad η S U ε ↔
        l43pSegments U (localConfiguration U μ h ηL) ∈ locInner (l43pLabels U) S U ε N) := by
  have hfin' : IsFiniteMeasure (localConfiguration U μ h ηL).1.1 := by
    change IsFiniteMeasure (μ.restrict U)
    exact isFiniteMeasure_restrict.mpr hfin.ne
  let ηc : C(ℝ, ℂ) := ⟨η, by
    have : η = fun t => ηL (φ t) := funext hcurve
    rw [this]
    exact ηL.continuous.comp φ.continuous⟩
  have hD := isExcursionFamily_of_regular U.isOpen hUb hreg hcurve
  have hσ : ∀ q ∈ l43pLabels U, ⇑(l43pSegments U (localConfiguration U μ h ηL) q) =
      clampSeg η (φ.symm (entryBefore ηL U (ratPt q)))
        (φ.symm (exitAfter ηL U (ratPt q))) := by
    intro q hq
    have hex := (isExcursion_entry_exit U.isOpen hUb hreg.surjective hreg.transient hq).1
    unfold l43pSegments
    rw [l43pFinite_of_finite hfin']
    exact localQuantumCurve_cfg (η := ηc) hfin' hcurve hparam hq hex
  exact ⟨escBad_iff_mem_locEsc ηc.continuous hε hSU hD hσ,
    innerAt_and_not_escBad_iff ηc.continuous hε hSU hD hparam hσ N⟩

end MatedCRTHarmonic.GMS4cP
