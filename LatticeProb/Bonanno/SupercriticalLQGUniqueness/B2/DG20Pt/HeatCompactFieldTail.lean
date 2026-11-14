/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatCompactFieldTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.RealRandomTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatVersionPoint
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffFar
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1PolarJoint

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DFGPS

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_compact_field_tail_away_zero
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (ε₁ R : ℝ) (hε₁ : 0 < ε₁) (K : Set ℂ)
    (hKR : K ⊆ closedBall (0 : ℂ) R)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ M : ℝ, 0 < M ∧
      ∀ ε : Ioo (0 : ℝ) 1, ε₁ ≤ (ε : ℝ) →
        P {ω | ∃ x ∈ K, M < |X ⟨ε, ε.property.1⟩ ω x|} ≤
          ENNReal.ofReal ζ := by
  let F : Ω → ℝ := fun ω => farSup ε₁ R (h ω)
  have hFm : Measurable F :=
    (measurable_farSup ε₁ R).comp hh.1.measurable
  obtain ⟨M, hM, htail⟩ := dg20_real_random_tail P F hFm ζ hζ
  have hJ := lem2_1HeatJoint P h hh.1
  refine ⟨M, hM, ?_⟩
  intro ε hε
  have hXe := dg20_heat_smoothing_ae_heatMollify
    P h hh ⟨ε, ε.property.1⟩
    (X ⟨ε, ε.property.1⟩) (hX ⟨ε, ε.property.1⟩)
  have hJcont : ∀ᵐ ω ∂P,
      ContinuousOn (fun p : ℝ × ℂ => heatMollify p.1 (h ω) p.2)
        (Ioi 0 ×ˢ univ) := hJ.mono (fun ω hω => hω.2)
  let E : Ω → Prop := fun ω =>
    (∀ x, X ⟨ε, ε.property.1⟩ ω x = heatMollify ε (h ω) x) ∧
    ContinuousOn (fun p : ℝ × ℂ => heatMollify p.1 (h ω) p.2)
      (Ioi 0 ×ˢ univ)
  have hE : ∀ᵐ ω ∂P, E ω := hXe.and hJcont
  have hnull : P {ω | ¬ E ω} = 0 := ae_iff.mp hE
  have hsub : {ω | ∃ x ∈ K, M < |X ⟨ε, ε.property.1⟩ ω x|} ⊆
      {ω | M < |F ω|} ∪ {ω | ¬ E ω} := by
    intro ω ⟨x, hx, hlarge⟩
    by_cases he : E ω
    · have hp : ((ε : ℝ), x) ∈ farSet ε₁ R :=
        ⟨⟨hε, ε.property.2.le⟩, hKR hx⟩
      have hxF : |heatMollify ε (h ω) x| ≤ F ω :=
        abs_heatMollify_le_farSup
          (ε₁ := ε₁) (R := R) (g := h ω) (p := (ε, x))
          hε₁ he.2 hp
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

end SupercriticalLQGUniqueness.B2.DG20Pt
