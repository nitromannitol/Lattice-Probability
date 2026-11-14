/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.Smoothing at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.CanonicalH
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L2_2D




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale

open LQGMetric (DistC DistOn restrictTo addConst)

 
def localOne (U : TopologicalSpace.Opens ℂ) : DistOn U :=
  restrictTo U (addConst (0 : DistC) 1)

theorem localOne_apply (U : TopologicalSpace.Opens ℂ) (φ : LQGMetric.TestOn U) :
    localOne U φ = ∫ x, φ x := by
  rw [localOne, LQGMetric.DG.L22T.restrictTo_addConst]
  have hz : restrictTo U (0 : DistC) φ = 0 := by
    change (0 : DistC) ((TestFunction.monoCLM ℝ (Ω₁ := U) (Ω₂ := ⊤)) φ) = 0
    simp
  simp [hz]

 
def localShift (U : TopologicalSpace.Opens ℂ) (q : DistOn U) (t : ℝ) : DistOn U :=
  q + t • localOne U

theorem localShift_apply (U : TopologicalSpace.Opens ℂ) (q : DistOn U)
    (t : ℝ) (φ : LQGMetric.TestOn U) :
    localShift U q t φ = q φ + (∫ x, φ x) * t := by
  change q φ + t * localOne U φ = q φ + (∫ x, φ x) * t
  rw [localOne_apply]
  ring

theorem measurable_localShift (U : TopologicalSpace.Opens ℂ) :
    Measurable (fun p : DistOn U × ℝ => localShift U p.1 p.2) := by
  apply LQGMetric.measurable_distOn_iff.mpr
  intro φ
  simp only [localShift_apply]
  exact ((LQGMetric.measurable_distOn_apply φ).comp measurable_fst).add
    (measurable_const.mul measurable_snd)

theorem localShift_restrictTo (U : TopologicalSpace.Opens ℂ)
    (g : DistC) (t : ℝ) :
    localShift U (restrictTo U g) t = restrictTo U (addConst g t) := by
  apply DFunLike.ext
  intro φ
  rw [localShift_apply, LQGMetric.DG.L22T.restrictTo_addConst]

theorem gaussian_ae_untranslate {P : ℝ → Prop}
    (hP : MeasurableSet {t | P t}) (a : ℝ)
    (h : ∀ᵐ t ∂standardGaussian, P (t + a)) :
    ∀ᵐ t ∂standardGaussian, P t := by
  have hv : ∀ᵐ t ∂(volume : Measure ℝ), P (t + a) :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0)).ae_le h
  have hvmap : ∀ᵐ t ∂(volume : Measure ℝ).map (· + -a), P (t + a) := by
    rw [map_add_right_eq_self]
    exact hv
  have hv' : ∀ᵐ t ∂(volume : Measure ℝ), P ((t + -a) + a) :=
    (ae_map_iff (measurable_add_const (-a)).aemeasurable
      (hP.preimage (measurable_add_const a))).1 hvmap
  have hv'' : ∀ᵐ t ∂(volume : Measure ℝ), P t := by
    simpa only [add_assoc, neg_add_cancel, add_zero] using hv'
  exact (gaussianReal_absolutelyContinuous 0 (by norm_num : (1 : NNReal) ≠ 0)).ae_le hv''

 
def gaussianSmooth (U : TopologicalSpace.Opens ℂ) (S : Set (DistOn U))
    (q : DistOn U) : ℝ≥0∞ :=
  standardGaussian {t | localShift U q t ∈ S}

theorem measurable_gaussianSmooth (U : TopologicalSpace.Opens ℂ)
    {S : Set (DistOn U)} (hS : MeasurableSet S) :
    Measurable (gaussianSmooth U S) := by
  have hB : MeasurableSet {p : DistOn U × ℝ | localShift U p.1 p.2 ∈ S} :=
    hS.preimage (measurable_localShift U)
  exact measurable_measure_prodMk_left hB

theorem gaussian_smoothing_event
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : TopologicalSpace.Opens ℂ) (q : Ω → DistOn U) (a : Ω → ℝ)
    (E : Set Ω) (S : Set (DistOn U)) (hS : MeasurableSet S)
    (hAE : ∀ᵐ p ∂P.prod standardGaussian,
      (p.1 ∈ E ↔ localShift U (q p.1) (a p.1 + p.2) ∈ S)) :
    ∀ᵐ ω ∂P, (ω ∈ E ↔ gaussianSmooth U S (q ω) > 1 / 2) := by
  have hsections := Measure.ae_ae_of_ae_prod hAE
  filter_upwards [hsections] with ω hω
  have hB : MeasurableSet {t | localShift U (q ω) t ∈ S} :=
    hS.preimage ((measurable_localShift U).comp
      (measurable_const.prodMk measurable_id))
  have hP : MeasurableSet {t | ω ∈ E ↔ localShift U (q ω) t ∈ S} := by
    by_cases he : ω ∈ E
    · simpa [he] using hB
    · simpa only [he, false_iff, not_iff_not, Set.compl_setOf] using hB.compl
  have htrans : ∀ᵐ t ∂standardGaussian,
      (ω ∈ E ↔ localShift U (q ω) t ∈ S) := by
    apply gaussian_ae_untranslate hP (a ω)
    simpa only [add_comm] using hω
  by_cases he : ω ∈ E
  · have hmem : ∀ᵐ t ∂standardGaussian, t ∈ {t | localShift U (q ω) t ∈ S} :=
      htrans.mono (fun t ht => ht.mp he)
    have hzero : standardGaussian {t | localShift U (q ω) t ∈ S}ᶜ = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr
        (hmem.mono (fun t ht htc => htc ht))
    have hone := measure_add_measure_compl (μ := standardGaussian) hB
    rw [hzero, measure_univ] at hone
    have hF : gaussianSmooth U S (q ω) = 1 := by
      simpa [gaussianSmooth] using hone
    simp [he, hF]
  · have hnot : ∀ᵐ t ∂standardGaussian,
        t ∉ {t | localShift U (q ω) t ∈ S} :=
      htrans.mono (fun t ht hs => he (ht.mpr hs))
    have hzero : gaussianSmooth U S (q ω) = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr hnot
    simp [he, hzero]


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale
