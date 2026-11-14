/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.InputsPLA at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Median.LFPPMetric

 







set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalLQGUniqueness.B2.Polylog

 












def PLHeatAnnulusTight : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
    ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ δ, IsLFPPNormalizer ξ δ (m δ)) →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P →
      ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ δ, IsHeatSmoothing P h δ (X δ)) →
      ∀ A : EuclideanAnnulus,
        (∀ δ : Set.Ioi (0 : ℝ), (δ : ℝ) ≤ 1 →
          AEMeasurable (fun ω => acrossDist (Median.lfppMetric (ξ : ℝ) (m δ) (X δ ω)) A) P ∧
          AEMeasurable (fun ω => aroundDist (Median.lfppMetric (ξ : ℝ) (m δ) (X δ ω)) A) P) ∧
        ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧ ∀ δ : Set.Ioi (0 : ℝ), (δ : ℝ) ≤ 1 →
          P {ω | acrossDist (Median.lfppMetric (ξ : ℝ) (m δ) (X δ ω)) A <
              ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal η ∧
          P {ω | ENNReal.ofReal M <
              aroundDist (Median.lfppMetric (ξ : ℝ) (m δ) (X δ ω)) A} ≤ ENNReal.ofReal η

 





def PLRatioUniform : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
    ∀ D : DistC → LSCMetric, ∀ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      Iface.IsPfeWeakMetric ξ D c →
    ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
    ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ C : ℝ, 1 < C ∧ ∀ R : ℝ, 1 ≤ R → ∃ εs : ℝ, 0 < εs ∧
      ∀ ε r : Set.Ioi (0 : ℝ), (ε : ℝ) ≤ εs → 100 * (ε : ℝ) ^ (1 - ζ) ≤ r → (r : ℝ) ≤ R →
        C⁻¹ ≤ (r : ℝ) * (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp ε.2)
            (Set.mem_Ioi.mp r.2))⟩ : ℝ) / ((c r : ℝ) * (m ε : ℝ)) ∧
          (r : ℝ) * (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp ε.2)
            (Set.mem_Ioi.mp r.2))⟩ : ℝ) / ((c r : ℝ) * (m ε : ℝ)) ≤ C

end SupercriticalLQGUniqueness.B2.Polylog
