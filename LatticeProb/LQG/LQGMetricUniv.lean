import Mathlib
import LatticeProb.Gauss.GFF
import LatticeProb.LQG.LengthMetric
import LatticeProb.LQG.LQGMetric

/-!
# Universe transport of the LQG metric axioms

`IsLQGMetric` (`LatticeProb/LQG/LQGMetric.lean`) quantifies its probability spaces over `Type` only. This file transports the
axioms I-IV to a sample space in an arbitrary universe `Type u`, with no hypothesis beyond `IsLQGMetric`:

* `LQGMetricSatisfiesAxiomsUnivLP`: LP form of `LQGMetricSatisfiesAxiomsUnivFrozen` (`FirstPass/Frozen/S11g.lean:31`),
  proved as `lqgMetricSatisfiesAxiomsUniv`.
* `LQGMetricLengthUnivLP`: LP form of `LQGMetricLengthUnivFrozen` (`FirstPass/Frozen/S11j.lean:133`), proved as
  `lqgMetricLengthUniv`.

Route (Duplantier-Sheffield circle process; Gwynne-Miller 2021, Section 1.2): a whole-plane GFF `hC` with a random
continuous shift `f` is pushed forward, after modifying the circle process off a measurable null set (`circleOn`), to a
Type-0 sample space `UnivSample = CircleSample × ContShift`. The pushed-forward law is a whole-plane GFF, the axioms of
`IsLQGMetric` apply there, and each clause is pulled back along the sample map by `ae_of_ae_map`. The sample field is
`addFunPairing (hC ω) (f ω)` exactly, so no pairing is changed.

Copied (mechanical LP ports, with the LP names of `LatticeProb/Gauss/GFF.lean`, `LatticeProb/LQG/LQGMetric.lean` and
`LatticeProb/LQG/LengthMetric.lean` reused, not redefined) from `FirstPass/S11aa.lean` (lines 28-107, 170-206, 252-258) and
`FirstPass/Phase2/AxiomsUnivDerived.lean` (lines 37-203) and `FirstPass/Phase2/LengthUnivDerived.lean` (lines 19-39).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
open LatticeProb.Gauss

universe u

namespace LatticeProb.LQG

/-! ### Pairing functionals and the Type-0 circle sample -/

/-- Pairing functionals `(ℂ → ℝ) → ℝ`, carrying the σ-algebra `distributionMeasurableSpace` of `LatticeProb/Gauss/GFF.lean`. A type
synonym, so that the σ-algebra is attached to this name. -/
def PairingFun : Type := (ℂ → ℝ) → ℝ

/-- The pairing functional viewed in `PairingFun`. -/
def toPairingFun (T : (ℂ → ℝ) → ℝ) : PairingFun := T

noncomputable instance : MeasurableSpace PairingFun := distributionMeasurableSpace

/-- Pairs (pairing functional, circle process) whose circle process is continuous on `(0, ∞) × ℂ`: a Type-0 space for the
transported whole-plane GFF (Duplantier-Sheffield, circle average process). -/
abbrev CircleSample : Type :=
  {p : PairingFun × (ℝ → ℂ → ℝ) // ContinuousOn (fun q : ℝ × ℂ => p.2 q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ))}

/-- Evaluation at a test function is measurable on the pairing functionals. -/
lemma measurable_evalPairing {φ : ℂ → ℝ} (hφ : IsTestFunction (univ : Set ℂ) φ) :
    Measurable fun T : PairingFun => T φ := by
  refine measurable_iff_comap_le.2 ?_
  exact le_iSup₂ (f := fun (ψ : ℂ → ℝ) (_ : IsTestFunction (univ : Set ℂ) ψ) =>
    MeasurableSpace.comap (fun T : PairingFun => T ψ) inferInstance) φ hφ

/-- A family of pairings with test functions, measurable in `ω`, is measurable as a map into `PairingFun`. -/
lemma measurable_toPairingFun {Ω : Type*} [MeasurableSpace Ω] {hC : Ω → (ℂ → ℝ) → ℝ}
    (h : ∀ φ, IsTestFunction (univ : Set ℂ) φ → Measurable fun ω => hC ω φ) :
    Measurable fun ω => toPairingFun (hC ω) := by
  refine measurable_iff_comap_le.2 ?_
  show MeasurableSpace.comap _ (⨆ (φ : ℂ → ℝ) (_ : IsTestFunction (univ : Set ℂ) φ),
    MeasurableSpace.comap (fun T : PairingFun => T φ) inferInstance) ≤ _
  simp only [MeasurableSpace.comap_iSup]
  refine iSup₂_le fun φ hφ => ?_
  rw [MeasurableSpace.comap_comp]
  exact (h φ hφ).comap_le

/-- Circle process with the radii `r ≤ 0` replaced by `0`. -/
noncomputable def posCircle {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) : ℝ → ℂ → ℝ :=
  fun r z => if 0 < r then hcirc ω r z else 0

lemma measurable_posCircle {Ω : Type*} [MeasurableSpace Ω] {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) :
    Measurable fun ω => posCircle hcirc ω := by
  refine measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun z => ?_
  by_cases hr : 0 < r
  · simpa [posCircle, hr] using h r z hr
  · simp [posCircle, hr]

lemma measurable_circleCoord (r : ℝ) (z : ℂ) : Measurable fun s : CircleSample => s.1.2 r z := by
  have h1 : Measurable fun g : ℝ → ℂ → ℝ => g r := measurable_pi_apply r
  have h2 : Measurable fun g : ℂ → ℝ => g z := measurable_pi_apply z
  exact (h2.comp h1).comp (measurable_snd.comp measurable_subtype_coe)

/-- Every admissible observable is a measurable function of the sample. -/
lemma measurable_evalObs (o : GFFObservable.Admissible) :
    Measurable fun s : CircleSample => o.1.eval s.1.1 s.1.2 := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ => exact (measurable_evalPairing ho).comp (measurable_fst.comp measurable_subtype_coe)
  | circle r z => exact measurable_circleCoord r z

/-- A measurable full-measure set on which the circle process is continuous on `(0, ∞) × ℂ`. -/
lemma exists_good_set {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : ∀ᵐ ω ∂P, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ))) :
    ∃ G0 : Set Ω, MeasurableSet G0 ∧ (∀ᵐ ω ∂P, ω ∈ G0) ∧
      ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) := by
  obtain ⟨t, hsub, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  refine ⟨tᶜ, htm.compl, ?_, fun ω hω => ?_⟩
  · refine ae_iff.2 ?_
    simpa using ht0
  · by_contra hc
    exact hω (hsub hc)

/-- The circle component: the positive-radius circle process on `G0`, and the zero process off `G0`. -/
noncomputable def circleOn {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ) (G0 : Set Ω) (ω : Ω) : ℝ → ℂ → ℝ :=
  by
    classical
    exact if ω ∈ G0 then posCircle hcirc ω else fun _ _ => 0

lemma circleOn_continuousOn {Ω : Type*} {hcirc : Ω → ℝ → ℂ → ℝ} {G0 : Set Ω}
    (hG0 : ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ))) (ω : Ω) :
    ContinuousOn (fun q : ℝ × ℂ => circleOn hcirc G0 ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) := by
  unfold circleOn
  by_cases hω : ω ∈ G0
  · simp only [hω, ite_true]
    refine (hG0 ω hω).congr fun q hq => ?_
    simp [posCircle, show (0 : ℝ) < q.1 from hq.1]
  · simp only [hω, ite_false]
    exact continuousOn_const

/-- The circle component of the sample is measurable. -/
lemma measurable_circleOn {Ω : Type*} [MeasurableSpace Ω] {hcirc : Ω → ℝ → ℂ → ℝ} {G0 : Set Ω}
    (hG0m : MeasurableSet G0) (hcirc_meas : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) :
    Measurable (circleOn hcirc G0) := by
  unfold circleOn
  classical
  exact Measurable.ite hG0m (measurable_posCircle hcirc_meas) measurable_const

/-- The `CircleSample` of `ω`: the exact pairing `hC ω` and the circle process `circleOn ω`. -/
noncomputable def circleSample {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (G0 : Set Ω)
    (hG0 : ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
    (ω : Ω) : CircleSample :=
  ⟨(toPairingFun (hC ω), circleOn hcirc G0 ω), circleOn_continuousOn hG0 ω⟩

lemma measurable_circleSample {Ω : Type*} [MeasurableSpace Ω] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {G0 : Set Ω} (hG0m : MeasurableSet G0)
    (hC_meas : ∀ φ, IsTestFunction (univ : Set ℂ) φ → Measurable fun ω => hC ω φ)
    (hcirc_meas : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hG0 : ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ))) :
    Measurable (circleSample hC hcirc G0 hG0) :=
  ((measurable_toPairingFun hC_meas).prodMk (measurable_circleOn hG0m hcirc_meas)).subtype_mk

/-- On `G0`, the circle component agrees with the positive-radius process, so every admissible observable agrees. -/
lemma eval_circleSample_eq {Ω : Type*} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {G0 : Set Ω} {ω : Ω}
    (hω : ω ∈ G0) (o : GFFObservable.Admissible) :
    o.1.eval (hC ω) (hcirc ω) = o.1.eval (hC ω) (circleOn hcirc G0 ω) := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ => simp [GFFObservable.eval]
  | circle r z =>
    have hr : 0 < r := ho
    simp [circleOn, hω, GFFObservable.eval, posCircle, hr]

/-! ### The Type-0 sample space `UnivSample` and the sample map -/

/-- Continuous shifts, as a Type-0 carrier. -/
abbrev ContShift : Type := {g : ℂ → ℝ // Continuous g}

/-- The Type-0 sample space of the transported model: pairing functional with circle process, and continuous shift. -/
abbrev UnivSample : Type := CircleSample × ContShift

/-- The sample map `Ω → UnivSample`, `ω ↦ (circleSample ω, f ω)`. -/
noncomputable def univSample {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (G0 : Set Ω)
    (hG0 : ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
    (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω)) (ω : Ω) : UnivSample :=
  (circleSample hC hcirc G0 hG0 ω, ⟨f ω, hf ω⟩)

lemma measurable_univSample {Ω : Type*} [MeasurableSpace Ω] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {G0 : Set Ω} (hG0m : MeasurableSet G0)
    (hC_meas : ∀ φ, IsTestFunction (univ : Set ℂ) φ → Measurable fun ω => hC ω φ)
    (hcirc_meas : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hG0 : ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
    {f : Ω → ℂ → ℝ} (hf : ∀ ω, Continuous (f ω)) (hfm : ∀ x, Measurable fun ω => f ω x) :
    Measurable (univSample hC hcirc G0 hG0 f hf) :=
  (measurable_circleSample hG0m hC_meas hcirc_meas hG0).prodMk
    (measurable_pi_iff.2 hfm).subtype_mk

lemma measurable_pairX : Measurable fun x : UnivSample => x.1.1.1 :=
  measurable_fst.comp (measurable_subtype_coe.comp measurable_fst)

lemma measurable_circX (r : ℝ) (z : ℂ) : Measurable fun x : UnivSample => x.1.1.2 r z :=
  (measurable_circleCoord r z).comp measurable_fst

lemma measurable_evalObsX (o : GFFObservable.Admissible) :
    Measurable fun x : UnivSample => o.1.eval x.1.1.1 x.1.1.2 :=
  (measurable_evalObs o).comp measurable_fst

lemma measurable_shiftX (z : ℂ) : Measurable fun x : UnivSample => x.2.1 z :=
  (measurable_pi_apply z).comp (measurable_subtype_coe.comp measurable_snd)

/-! ### Push-forward lemmas -/

/-- Integrals are preserved by a measurable push-forward. -/
lemma integral_map_of_measurable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {S : Ω → Ω'} (hS : Measurable S) {g : Ω' → ℝ} (hg : Measurable g) :
    ∫ s, g s ∂(P.map S) = ∫ ω, g (S ω) ∂P :=
  integral_map hS.aemeasurable hg.aestronglyMeasurable

/-- Covariances are preserved by a push-forward that agrees almost surely with the observables. -/
lemma covariance_map_of_ae {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {S : Ω → Ω'} (hS : Measurable S) {X' Y' : Ω' → ℝ} (hX' : Measurable X') (hY' : Measurable Y')
    {X Y : Ω → ℝ} (hX : ∀ᵐ ω ∂P, X' (S ω) = X ω) (hY : ∀ᵐ ω ∂P, Y' (S ω) = Y ω) :
    covariance X' Y' (P.map S) = covariance X Y P := by
  have hmX : ∫ s, X' s ∂(P.map S) = ∫ ω, X ω ∂P :=
    (integral_map_of_measurable hS hX').trans (integral_congr_ae hX)
  have hmY : ∫ s, Y' s ∂(P.map S) = ∫ ω, Y ω ∂P :=
    (integral_map_of_measurable hS hY').trans (integral_congr_ae hY)
  have key : ∀ c d : ℝ, ∫ s, (X' s - c) * (Y' s - d) ∂(P.map S) = ∫ ω, (X ω - c) * (Y ω - d) ∂P := by
    intro c d
    refine (integral_map_of_measurable hS ((hX'.sub measurable_const).mul (hY'.sub measurable_const))).trans
      (integral_congr_ae ?_)
    filter_upwards [hX, hY] with ω h1 h2
    show (X' (S ω) - c) * (Y' (S ω) - d) = (X ω - c) * (Y ω - d)
    rw [h1, h2]
  unfold covariance
  rw [hmX, hmY]
  exact key _ _

/-- Transport of Gaussian laws along a measurable map: `HasGaussianLaw (X ∘ S) P` gives `HasGaussianLaw X (P.map S)`. -/
lemma hasGaussianLaw_map_of_comp {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace E] [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] {P : Measure Ω}
    {S : Ω → Ω'} (hS : Measurable S) {X : Ω' → E} (hX : Measurable X)
    (h : HasGaussianLaw (fun ω => X (S ω)) P) : HasGaussianLaw X (P.map S) where
  aemeasurable := hX.aemeasurable
  isGaussian_map := by
    rw [Measure.map_map hX hS]
    exact h.isGaussian_map

/-- The transported whole-plane GFF: `P.map (univSample)` is a whole-plane GFF on `UnivSample`, with pairing
`x ↦ x.1.1.1` and circle process `x ↦ x.1.1.2`. -/
theorem isWholePlaneGFF_map_univSample {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) {G0 : Set Ω} (hG0m : MeasurableSet G0)
    (hG0 : ∀ᵐ ω ∂P, ω ∈ G0)
    (hG0c : ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
    {f : Ω → ℂ → ℝ} (hf : ∀ ω, Continuous (f ω)) (hfm : ∀ x, Measurable fun ω => f ω x) :
    IsWholePlaneGFF (P.map (univSample hC hcirc G0 hG0c f hf)) (fun x : UnivSample => x.1.1.1)
      (fun x : UnivSample => x.1.1.2) := by
  have hJm : Measurable (univSample hC hcirc G0 hG0c f hf) :=
    measurable_univSample hG0m hGFF.measurable_pairing hGFF.measurable_circle hG0c hf hfm
  refine
    { measurable_pairing := fun φ hφ => (measurable_evalPairing hφ).comp measurable_pairX
      measurable_circle := fun r z _ => measurable_circX r z
      isGaussianProcess := ⟨fun I => ?_⟩
      integral_eq_zero := fun o ho => ?_
      covariance_eq := fun o o' ho ho' => ?_
      ae_continuousOn_circle := Filter.Eventually.of_forall fun x => x.1.2 }
  · refine hasGaussianLaw_map_of_comp hJm ?_ ?_
    · refine Measurable.of_eval fun i => ?_
      exact measurable_evalObsX i.1
    · refine (hGFF.isGaussianProcess.hasGaussianLaw I).congr ?_
      filter_upwards [hG0] with ω hω
      funext i
      exact eval_circleSample_eq hω i.1
  · have hm : Measurable fun x : UnivSample => o.eval x.1.1.1 x.1.1.2 := measurable_evalObsX ⟨o, ho⟩
    have hae : (fun ω => o.eval (univSample hC hcirc G0 hG0c f hf ω).1.1.1
        (univSample hC hcirc G0 hG0c f hf ω).1.1.2) =ᵐ[P] fun ω => o.eval (hC ω) (hcirc ω) := by
      filter_upwards [hG0] with ω hω
      exact (eval_circleSample_eq hω ⟨o, ho⟩).symm
    exact ((integral_map_of_measurable hJm hm).trans (integral_congr_ae hae)).trans
      (hGFF.integral_eq_zero o ho)
  · have hm : Measurable fun x : UnivSample => o.eval x.1.1.1 x.1.1.2 := measurable_evalObsX ⟨o, ho⟩
    have hm' : Measurable fun x : UnivSample => o'.eval x.1.1.1 x.1.1.2 := measurable_evalObsX ⟨o', ho'⟩
    refine (covariance_map_of_ae hJm hm hm' ?_ ?_).trans (hGFF.covariance_eq o o' ho ho')
    · filter_upwards [hG0] with ω hω
      exact (eval_circleSample_eq hω ⟨o, ho⟩).symm
    · filter_upwards [hG0] with ω hω
      exact (eval_circleSample_eq hω ⟨o', ho'⟩).symm

/-- The sample map is measurable from the pairing σ-algebra of `addFunPairing (hC ω) (f ω)` over `U` into the pairing
σ-algebra of the sample field over `U`: the sample field is the sample pairing plus the sample shift, and its pairings
with test functions are the pairings of `addFunPairing (hC ω) (f ω)`, exactly. -/
lemma measurable_univSample_pairing {Ω : Type*} [MeasurableSpace Ω] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {G0 : Set Ω}
    (hG0c : ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
    {f : Ω → ℂ → ℝ} (hf : ∀ ω, Continuous (f ω)) (U : Set ℂ) :
    Measurable[pairingSigmaAlgebra (fun ω => addFunPairing (hC ω) (f ω)) U,
      pairingSigmaAlgebra (fun x : UnivSample => addFunPairing x.1.1.1 x.2.1) U]
      (univSample hC hcirc G0 hG0c f hf) := by
  refine measurable_iff_comap_le.2 ?_
  show MeasurableSpace.comap _ (pairingSigmaAlgebra (fun x : UnivSample => addFunPairing x.1.1.1 x.2.1) U) ≤ _
  unfold pairingSigmaAlgebra
  simp only [MeasurableSpace.comap_iSup]
  refine iSup₂_le fun φ hφ => ?_
  rw [MeasurableSpace.comap_comp]
  exact le_iSup₂ (f := fun (ψ : ℂ → ℝ) (_ : IsTestFunction U ψ) =>
    MeasurableSpace.comap (fun ω => addFunPairing (hC ω) (f ω) ψ) inferInstance) φ hφ

/-! ### The LP universe-transport statements -/

/-- **LP form of `LQGMetricSatisfiesAxiomsUnivFrozen`** (`FirstPass/Frozen/S11g.lean:31`): for every γ-LQG metric `𝔇` with
Weyl exponent `ξ` (`IsLQGMetric`), every whole-plane GFF `hC` on a probability space in `Type u` with a random continuous
shift `f`, the metric of `hC ω + f ω` satisfies the axioms I-IV (`SatisfiesLQGMetricAxioms`). -/
def LQGMetricSatisfiesAxiomsUnivLP : Prop :=
  ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), IsLQGMetric γ ξ 𝔇 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (f : Ω → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → (∀ ω, Continuous (f ω)) →
    (∀ x, Measurable fun ω => f ω x) →
    SatisfiesLQGMetricAxioms P γ ξ 𝔇 (fun ω => addFunPairing (hC ω) (f ω))

/-- **LP form of `LQGMetricLengthUnivFrozen`** (`FirstPass/Frozen/S11j.lean:133`): for every γ-LQG metric
`𝔇` with Weyl exponent `ξ` and every whole-plane GFF `hC` on a probability space in `Type u`, almost surely `𝔇 (hC ω)` is a
Euclidean length metric (`IsEuclideanLengthMetric`). -/
def LQGMetricLengthUnivLP : Prop :=
  ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω))

/-- Axioms I-IV of the LQG metric on a sample space in `Type u`, hypothesis-free beyond `IsLQGMetric`
(`LQGMetricSatisfiesAxiomsUnivLP`). Transport to `UnivSample`, where `IsLQGMetric.satisfiesLQGMetricAxioms` applies, and
pull-back of each clause along `univSample`; the sample field is `addFunPairing (hC ω) (f ω)` exactly. -/
theorem lqgMetricSatisfiesAxiomsUniv : LQGMetricSatisfiesAxiomsUnivLP.{u} := by
  intro γ ξ 𝔇 hLQG Ω _ P hC hcirc f hGFF hf hfm
  obtain ⟨G0, hG0m, hG0, hG0c⟩ := exists_good_set hGFF.ae_continuousOn_circle
  have hGFF' := isWholePlaneGFF_map_univSample hGFF hG0m hG0 hG0c hf hfm
  have hJm : Measurable (univSample hC hcirc G0 hG0c f hf) :=
    measurable_univSample hG0m hGFF.measurable_pairing hGFF.measurable_circle hG0c hf hfm
  have hS := hLQG.satisfiesLQGMetricAxioms UnivSample (P.map (univSample hC hcirc G0 hG0c f hf))
    (fun x : UnivSample => x.1.1.1) (fun x : UnivSample => x.1.1.2) (fun x : UnivSample => x.2.1) hGFF'
    (fun x => x.2.2) (fun z => measurable_shiftX z)
  refine
    { ae_isEuclideanLengthMetric := ?_
      locality := ?_
      ae_weylScaling := ?_
      coordChange := ?_ }
  · exact ae_of_ae_map hJm.aemeasurable hS.ae_isEuclideanLengthMetric
  · intro U hU
    obtain ⟨G, hGm, hGeq⟩ := hS.locality U hU
    refine ⟨fun ω => G (univSample hC hcirc G0 hG0c f hf ω), fun z w => ?_, ?_⟩
    · exact (hGm z w).comp (measurable_univSample_pairing hG0c hf U)
    · exact ae_of_ae_map hJm.aemeasurable hGeq
  · exact ae_of_ae_map hJm.aemeasurable hS.ae_weylScaling
  · intro r hr z
    exact ae_of_ae_map hJm.aemeasurable (hS.coordChange r hr z)

lemma addFunPairing_zero_fun (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => (0 : ℝ)) = T := by
  funext φ
  simp [addFunPairing]

/-- Axiom I of the LQG metric for a whole-plane GFF on a probability space in `Type u` (`LQGMetricLengthUnivLP`): specialize
`lqgMetricSatisfiesAxiomsUniv` to the zero shift, and pull axiom I back along `addFunPairing (hC ω) 0 = hC ω`. The bounds
`0 < γ < 2` are not used. -/
theorem lqgMetricLengthUniv : LQGMetricLengthUnivLP.{u} := by
  intro γ ξ 𝔇 _ _ hLQG Ω _ P hC hcirc hGFF
  have hS := lqgMetricSatisfiesAxiomsUniv.{u} γ ξ 𝔇 hLQG Ω P hC hcirc (fun _ _ => (0 : ℝ))
    hGFF (fun _ => continuous_const) (fun _ => measurable_const)
  filter_upwards [hS.ae_isEuclideanLengthMetric] with ω hω
  have h0 : addFunPairing (hC ω) (fun _ => (0 : ℝ)) = hC ω := addFunPairing_zero_fun (hC ω)
  have hω' : IsEuclideanLengthMetric (𝔇 (addFunPairing (hC ω) (fun _ => (0 : ℝ)))) := hω
  rwa [h0] at hω'

end LatticeProb.LQG
