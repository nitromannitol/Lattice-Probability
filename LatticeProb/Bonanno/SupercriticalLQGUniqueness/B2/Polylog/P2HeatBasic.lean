/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P2HeatBasic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.InputsPLA
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionMeasurable
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteMeasurable
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatCompactFieldTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatNormalizerAwayZero
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.EProjection
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf

 













set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open LQGMetric (DistC heatMollify)
open LQGMetric.DFGPS

namespace SupercriticalLQGUniqueness.B2.Polylog

 

theorem lfppMetric_eq_normalizedLFPPMetric (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) :
    Median.lfppMetric ξ a φ = PfeWeyl.normalizedLFPPMetric ξ a φ := by
  apply Subtype.ext
  funext p
  exact (Median.lfppMetric_apply ξ a φ p).trans
    (PfeWeyl.normalizedLFPPMetric_apply ξ a φ p).symm

 



theorem aemeasurable_lfppMetric_heat {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : ℝ) (a δ : Ioi (0 : ℝ)) (X : Ω → C(ℂ, ℝ)) (hX : IsHeatSmoothing P h δ X) :
    AEMeasurable (fun ω => Median.lfppMetric ξ a (X ω)) P := by
  have hXm := PfeAxioms.aemeasurable_heat_smoothing_version P h hh δ X hX
  have hG : Measurable (fun ω => PfeWeyl.normalizedLFPPMetric ξ a (hXm.mk X ω)) :=
    PfeAxioms.measurable_normalizedLFPPMetric_comp ξ a fun z =>
      (continuous_eval_const z).measurable.comp hXm.measurable_mk
  refine ⟨_, hG, ?_⟩
  filter_upwards [hXm.ae_eq_mk] with ω hω
  rw [lfppMetric_eq_normalizedLFPPMetric, hω]

 
theorem aemeasurable_acrossDist_lfppMetric_heat {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (ξ : ℝ) (a δ : Ioi (0 : ℝ)) (X : Ω → C(ℂ, ℝ))
    (hX : IsHeatSmoothing P h δ X) (A : EuclideanAnnulus) :
    AEMeasurable (fun ω => acrossDist (Median.lfppMetric ξ a (X ω)) A) P :=
  (Uniqueness.Toolkit.PathInfimum.measurable_acrossDist A).comp_aemeasurable
    (aemeasurable_lfppMetric_heat P h hh ξ a δ X hX)

 
theorem aemeasurable_aroundDist_lfppMetric_heat {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (ξ : ℝ) (a δ : Ioi (0 : ℝ)) (X : Ω → C(ℂ, ℝ))
    (hX : IsHeatSmoothing P h δ X) (A : EuclideanAnnulus) :
    AEMeasurable (fun ω => aroundDist (Median.lfppMetric ξ a (X ω)) A) P :=
  (Uniqueness.TwoScale.S36.measurable_aroundDist_fixed A).comp_aemeasurable
    (aemeasurable_lfppMetric_heat P h hh ξ a δ X hX)

 



theorem heat_compact_field_tail_Icc {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ)) (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (ε₁ R : ℝ) (hε₁ : 0 < ε₁) (K : Set ℂ) (hKR : K ⊆ closedBall (0 : ℂ) R)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ M : ℝ, 0 < M ∧ ∀ δ : Ioi (0 : ℝ), ε₁ ≤ (δ : ℝ) → (δ : ℝ) ≤ 1 →
      P {ω | ∃ x ∈ K, M < |X δ ω x|} ≤ ENNReal.ofReal ζ := by
  let F : Ω → ℝ := fun ω => farSup ε₁ R (h ω)
  have hFm : Measurable F := (measurable_farSup ε₁ R).comp hh.1.measurable
  obtain ⟨M, hM, htail⟩ := DG20Pt.dg20_real_random_tail P F hFm ζ hζ
  have hJ := lem2_1HeatJoint P h hh.1
  refine ⟨M, hM, ?_⟩
  intro δ hδ1 hδ2
  have hXe := DG20Pt.dg20_heat_smoothing_ae_heatMollify P h hh δ (X δ) (hX δ)
  have hJcont : ∀ᵐ ω ∂P,
      ContinuousOn (fun p : ℝ × ℂ => heatMollify p.1 (h ω) p.2) (Ioi 0 ×ˢ univ) :=
    hJ.mono (fun ω hω => hω.2)
  let E : Ω → Prop := fun ω =>
    (∀ x, X δ ω x = heatMollify δ (h ω) x) ∧
    ContinuousOn (fun p : ℝ × ℂ => heatMollify p.1 (h ω) p.2) (Ioi 0 ×ˢ univ)
  have hE : ∀ᵐ ω ∂P, E ω := hXe.and hJcont
  have hnull : P {ω | ¬ E ω} = 0 := ae_iff.mp hE
  have hsub : {ω | ∃ x ∈ K, M < |X δ ω x|} ⊆ {ω | M < |F ω|} ∪ {ω | ¬ E ω} := by
    intro ω ⟨x, hx, hlarge⟩
    by_cases he : E ω
    · have hp : ((δ : ℝ), x) ∈ farSet ε₁ R := ⟨⟨hδ1, hδ2⟩, hKR hx⟩
      have hxF : |heatMollify δ (h ω) x| ≤ F ω :=
        abs_heatMollify_le_farSup (ε₁ := ε₁) (R := R) (g := h ω) (p := (δ, x)) hε₁ he.2 hp
      left
      have hlow : 0 ≤ F ω := (abs_nonneg _).trans hxF
      change M < |F ω|
      rw [abs_of_nonneg hlow]
      exact lt_of_lt_of_le (by simpa only [he.1 x] using hlarge) hxF
    · exact Or.inr he
  calc
    _ ≤ P ({ω | M < |F ω|} ∪ {ω | ¬ E ω}) := measure_mono hsub
    _ ≤ P {ω | M < |F ω|} + P {ω | ¬ E ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal ζ := by rw [hnull, add_zero]; exact htail

 



theorem heat_normalizer_bounds_Icc (ξ : Ioi (0 : ℝ)) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε)) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ)) (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ δ : Ioi (0 : ℝ), ε₁ ≤ (δ : ℝ) → (δ : ℝ) ≤ 1 →
      c ≤ (m δ : ℝ) ∧ (m δ : ℝ) ≤ C := by
  obtain ⟨c, C, hc, hC, hb⟩ :=
    DG20Pt.dg20_heat_normalizer_bounds_away_zero ξ m hm P h hh X hX ε₁ hε₁
  have h1 : (0 : ℝ) < 1 := one_pos
  let one : Ioi (0 : ℝ) := ⟨1, h1⟩
  have hm1 : (0 : ℝ) < (m one : ℝ) := (m one).2
  refine ⟨min c (m one), max C (m one), lt_min hc hm1, lt_max_of_lt_left hC, ?_⟩
  intro δ hδ1 hδ2
  rcases hδ2.lt_or_eq with hlt | heq
  · have hb' := hb ⟨δ, δ.2, hlt⟩ hδ1
    exact ⟨(min_le_left _ _).trans hb'.1, hb'.2.trans (le_max_left _ _)⟩
  · have hδ : δ = one := Subtype.ext heq
    subst hδ
    exact ⟨min_le_right _ _, le_max_right _ _⟩

end SupercriticalLQGUniqueness.B2.Polylog
