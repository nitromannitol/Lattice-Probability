/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.PrimeReconstructionAdapter at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.L46TPrime
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.ZeroCone
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108P2
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.VisitBoundQuantum

/-! Connect GMS4cP's cross-excursion Borel events to the exact
all-visit reconstruction interface. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4c

open MatedCRTHarmonic.GMS4b MatedCRTHarmonic.GMS4cP
open MatedCRTHarmonic.MatedCRT

/-- The finite-fiber primed failure is the all-time integer-threshold event
used by the cross-excursion Borel reconstruction. -/
theorem primeInnerBad_iff_innerAt
    {c : ℝ → ℂ} (hfinite : ∀ z, (c ⁻¹' {z}).Finite)
    (hsurj : Function.Surjective c) (S : Set ℂ) (ε : ℝ)
    (k : ℕ) (ζ : ℝ) :
    (∃ z ∈ S, ENNReal.ofReal
        (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)) <
          ((degreeInPrime ε c z : ℕ∞) : ℝ≥0∞)) ↔
      InnerAt c S ε (l43pThreshold ε k ζ) := by
  constructor
  · rintro ⟨z, hz, hdeg⟩
    rw [GMS4cP.ofReal_lt_coe_enat_iff] at hdeg
    obtain ⟨t, ht, hN⟩ :=
      (degreeInPrime_ge_iff_exists_visit (hfinite z)
        ⟨(hsurj z).choose, by simpa using (hsurj z).choose_spec⟩
        (l43pThreshold ε k ζ)).mp hdeg
    exact ⟨t, ht ▸ hz, hN⟩
  · rintro ⟨t, ht, hdeg⟩
    refine ⟨c t, ht, ?_⟩
    rw [GMS4cP.ofReal_lt_coe_enat_iff]
    exact (degreeInPrime_ge_iff_exists_visit (hfinite (c t))
      ⟨t, by simp⟩ (l43pThreshold ε k ζ)).mpr ⟨t, rfl, hdeg⟩

theorem surjective_of_l43pSampleModel
    {V U : TopologicalSpace.Opens ℂ}
    {R₀ : L46TLocalFieldPhase V → LocalConfiguration U}
    {obs : L46TLocalFieldPhase V} {c : ℝ → ℂ}
    (h : L43PSampleModel R₀ obs c) : Function.Surjective c := by
  obtain ⟨μ, hfield, ηL, φ, hR, hfin, hreg, hcurve, hparam⟩ := h
  intro z
  obtain ⟨s, hs⟩ := hreg.surjective z
  exact ⟨φ.symm s, by rw [hcurve, φ.apply_symm_apply, hs]⟩

/-- GMS4cP's cross-excursion Borel event gives exactly the primed
reconstruction once the two cone sample models and finite visit fibers are
available. -/
def bundle_primeReconstruction_of_sampleModels
    {Ωγ Ω₀ : Type*} [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    {V U : TopologicalSpace.Opens ℂ} {w : ℂ} {r R : ℝ}
    (hU : (U : Set ℂ) = ball w R) (hrR : r ≤ R)
    {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    {hγ hIGγ : Ωγ → LQGMetric.DistC} {uγ : Ωγ → ℝ}
    {h₀ hIG₀ : Ω₀ → LQGMetric.DistC} {u₀ : Ω₀ → ℝ}
    {cγ : Ωγ → ℝ → ℂ} {c₀ : Ω₀ → ℝ → ℂ}
    {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) (ζ : ℝ)
    (R₀ : L46TLocalFieldPhase V → LocalConfiguration U)
    (hR₀ : Measurable R₀)
    (hγcfg : ∀ᵐ ω ∂Pγ,
      L43PSampleModel R₀ (l46tLocalFieldPhase V hγ hIGγ uγ ω) (cγ ω))
    (h₀cfg : ∀ᵐ ω ∂P₀,
      L43PSampleModel R₀ (l46tLocalFieldPhase V h₀ hIG₀ u₀ ω) (c₀ ω))
    (hγfin : ∀ᵐ ω ∂Pγ, ∀ z, ((cγ ω) ⁻¹' {z}).Finite)
    (h₀fin : ∀ᵐ ω ∂P₀, ∀ z, ((c₀ ω) ⁻¹' {z}).Finite) :
    BundleSec4.L46TLocalReconstructionPrime V U Pγ P₀
      hγ hIGγ uγ h₀ hIG₀ u₀ cγ c₀ (ball w r) ε k ζ := by
  let S : Set ℂ := ball w r
  let N : ℕ := l43pThreshold ε k ζ
  let Besc : Set (LocalConfiguration U) :=
    l43pSegments U ⁻¹' locEsc (l43pLabels U) S U ε
  let Binner : Set (LocalConfiguration U) :=
    l43pSegments U ⁻¹' locInner (l43pLabels U) S U ε N
  have hE : MeasurableSet Besc := by
    change MeasurableSet (l43pSegments U ⁻¹' locEsc (l43pLabels U) S U ε)
    rw [hU]
    exact (measurableSet_locEsc _ w w r R ε).preimage
      (measurable_l43pSegments U)
  have hA : MeasurableSet Binner := by
    change MeasurableSet (l43pSegments U ⁻¹' locInner (l43pLabels U) S U ε N)
    rw [hU]
    exact (measurableSet_locInner _ w w r R ε N).preimage
      (measurable_l43pSegments U)
  have hUb : Bornology.IsBounded (U : Set ℂ) := hU ▸ isBounded_ball
  have hSU : S ⊆ U := hU ▸ ball_subset_ball hrR
  have key : ∀ (obs : L46TLocalFieldPhase V) (c : ℝ → ℂ),
      L43PSampleModel R₀ obs c →
      (EscBad c S U ε ↔ R₀ obs ∈ Besc) ∧
      (InnerAt c S ε N ∧ ¬ EscBad c S U ε ↔ R₀ obs ∈ Binner) := by
    rintro obs c ⟨μ, h, ηL, φ, hcfg, hfin, hreg, hcurve, hparam⟩
    simp only [Besc, Binner, mem_preimage, hcfg]
    exact events_iff_of_cfg hUb hfin hreg hcurve hparam hSU hε N
  refine ⟨R₀, hR₀, Besc, hE, Binner, hA, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hγcfg] with ω hω
    exact propext (key _ _ hω).1
  · filter_upwards [h₀cfg] with ω hω
    exact propext (key _ _ hω).1
  · filter_upwards [hγcfg, hγfin] with ω hω hf
    have hp := primeInnerBad_iff_innerAt hf
      (surjective_of_l43pSampleModel hω) S ε k ζ
    exact propext (by
      change (ω ∈ BundleSec4.l46tInnerBadPrime cγ S ε k ζ ∧
        ¬ EscBad (cγ ω) S U ε) ↔ R₀ (l46tLocalFieldPhase V hγ hIGγ uγ ω) ∈ Binner
      exact (and_congr hp Iff.rfl).trans (key _ _ hω).2)
  · filter_upwards [h₀cfg, h₀fin] with ω hω hf
    have hp := primeInnerBad_iff_innerAt hf
      (surjective_of_l43pSampleModel hω) S ε k ζ
    exact propext (by
      change (ω ∈ BundleSec4.l46tInnerBadPrime c₀ S ε k ζ ∧
        ¬ EscBad (c₀ ω) S U ε) ↔ R₀ (l46tLocalFieldPhase V h₀ hIG₀ u₀ ω) ∈ Binner
      exact (and_congr hp Iff.rfl).trans (key _ _ hω).2)

theorem ae_zero_bundle_finite_quantum_visits
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, ((η₀ ω) ⁻¹' {z}).Finite := by
  obtain ⟨k, hk⟩ := D.visitBound
  filter_upwards [D.areaParam₀, hk] with ω hparam hvisit z
  obtain ⟨φ, -, hφ⟩ := hparam.1
  exact finite_quantum_visits_of_reparam φ hφ
    (Set.finite_of_encard_le_coe (hvisit z))

theorem ae_gamma_translate_finite_quantum_visits
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (z₀ : ℂ) :
    ∀ᵐ ω ∂P, ∀ z : ℂ,
      ((l46tTranslateCurve z₀ (η ω)) ⁻¹' {z}).Finite := by
  filter_upwards [ae_bundle_finite_quantum_visits D] with ω hfin z
  have heq : (l46tTranslateCurve z₀ (η ω)) ⁻¹' {z} =
      (η ω) ⁻¹' {z - z₀} := by
    ext t
    simp only [mem_preimage, mem_singleton_iff, l46tTranslateCurve]
    constructor
    · intro h
      calc
        η ω t = (η ω t + z₀) - z₀ := (add_sub_cancel_right _ _).symm
        _ = z - z₀ := congrArg (· - z₀) h
    · intro h
      rw [h, sub_add_cancel]
  rw [heq]
  exact hfin (z - z₀)

/-- The exact the bundle construction primed structure from the two-cone configuration form of
Lemma 4.3. The Borel cross-excursion count is supplied by GMS4cP. -/
def bundle_primeReconstruction_of_configInput
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (w : ℂ) (hcfg : L43PZeroConeConfigInput D hγ ρ w)
    {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (k : ℕ) (ζ : ℝ) :
    BundleSec4.L46TLocalReconstructionPrime
      (l46tObservation ρ w) (l46tLocalRegion ρ w) P P
      (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ))
        (MoTInput.cellModelOfCoupling D hγ).field)
      (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) U
      (l46tZeroConeCellModel D hγ).field hIG₀ U
      (fun ω => l46tTranslateCurve (w + ((1 - ρ) / 2 : ℝ)) (η ω))
      (l46tZeroConeCellModel D hγ).curve
      (ball w ((1 - ρ) / 16)) ε k ζ := by
  let R₀ := hcfg.choose
  obtain ⟨hR₀, hRγ, hR₀cone⟩ := hcfg.choose_spec
  have hsub : (1 - ρ) / 16 ≤ (1 - ρ) / 8 := by linarith [hρ.2]
  exact bundle_primeReconstruction_of_sampleModels
    (hU := rfl) hsub hε.1.le k ζ R₀ hR₀
    (ae_gammaTranslate_sampleModel D hγ hRγ)
    (ae_zeroCone_sampleModel D hγ hR₀cone)
    (ae_gamma_translate_finite_quantum_visits D (w + ((1 - ρ) / 2 : ℝ)))
    (ae_zero_bundle_finite_quantum_visits D)

/-- The exact versioned reconstruction requested by the bundle construction, conditional only
on the two-cone configuration form of Lemma 4.3. -/
def bundle_primeReconstruction_versioned_of_configInput
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (w : ℂ) (_hw : w ∈ closedBall (0 : ℂ) ρ)
    (hcfg : L43PZeroConeConfigInput D hγ ρ w)
    {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (k : ℕ) (ζ : ℝ) :
    BundleSec4.L46TLocalReconstructionPrime
      (l46tObservation ρ w) (l46tLocalRegion ρ w) P P
      (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) (BundleSec4.coneFieldVersion D))
      (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) U
      (GMS4b.l46tZeroConeFieldVersion D) hIG₀ U
      (fun ω => l46tTranslateCurve (w + ((1 - ρ) / 2 : ℝ)) (η ω))
      (l46tZeroConeCellModel D hγ).curve
      (ball w ((1 - ρ) / 16)) ε k ζ := by
  let hraw := bundle_primeReconstruction_of_configInput D hγ hρ w hcfg hε k ζ
  apply BundleSec4.l46tPrimeReconstruction_congr hraw
  · filter_upwards [(BundleSec4.coneFieldVersion_ae_eq D hγ).symm] with ω heq
    simp only [l46tLocalFieldPhase, localFieldPair, l46tTranslatedField]
    rw [heq]
  · filter_upwards [(GMS4b.l46tZeroConeFieldVersion_ae_eq_raw D hγ).symm]
      with ω heq
    simp only [l46tLocalFieldPhase, localFieldPair]
    rw [heq]

end MatedCRTHarmonic.GMS4c

