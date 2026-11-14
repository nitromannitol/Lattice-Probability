/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.InputsPLACompare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4Event

 







set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalLQGUniqueness.B2.Polylog

 
def plRadiusCount (ζ ε : ℝ) : ℕ := ⌊ζ / 2 * Real.logb 10 ε⁻¹⌋₊ - 10

 


def plRadiusSet (ζ : ℝ) (ε : Set.Ioi (0 : ℝ)) : Finset (Set.Ioi (0 : ℝ)) :=
  (Finset.range (plRadiusCount ζ ε)).image fun i : ℕ =>
    ⟨(10 : ℝ) ^ (-((i : ℝ) + 2)) * (ε : ℝ) ^ (1 - ζ),
      Set.mem_Ioi.mpr (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
        (Real.rpow_pos_of_pos (Set.mem_Ioi.mp ε.2) _))⟩

 
def ratioBC (m c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε r : Set.Ioi (0 : ℝ)) : ℝ :=
  lfppScaleFactor m ε r / (c r : ℝ)

 



def compareSubsetHolds (ξ : ℝ) (D : DistC → LSCMetric) (c m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (q ζ : ℝ) (U : Set ℂ) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (Rt : Finset (Set.Ioi (0 : ℝ)))
    (hne : Rt.Nonempty) (Csub : ℝ) (g : DistC) : Prop :=
  ∀ (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U),
    (plLocMetric ξ q m ε hε g).internalSetDist (thickening (ε ^ (1 - ζ)) U)
        {x | (x : ℂ) ∈ ball z (ε ^ (1 - ζ))} {x | (x : ℂ) ∈ ball w (ε ^ (1 - ζ))} ≤
      ENNReal.ofReal (Csub * Rt.sup' hne (ratioBC m c ⟨ε, hε.1⟩)) *
        (D g).internal U (⟨z, hz⟩, ⟨w, hw⟩) ∧
    (D g).internalSetDist (thickening (ε ^ (1 - ζ)) U)
        {x | (x : ℂ) ∈ ball z (ε ^ (1 - ζ))} {x | (x : ℂ) ∈ ball w (ε ^ (1 - ζ))} ≤
      ENNReal.ofReal (Csub * (Rt.inf' hne (ratioBC m c ⟨ε, hε.1⟩))⁻¹) *
        (plLocMetric ξ q m ε hε g).internal U (⟨z, hz⟩, ⟨w, hw⟩)

 





def PLCompareSubset : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
    ∀ D : DistC → LSCMetric, ∀ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      Iface.IsPfeWeakMetric ξ D c →
    ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
    ∀ q : ℝ, 0 < q → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
    ∃ Csub : ℝ, 0 < Csub ∧ ∀ U : Set ℂ, IsOpen U → IsConnected U → Bornology.IsBounded U →
      ∃ p₀ c₀ ε₀ : ℝ, 0 < p₀ ∧ 0 < c₀ ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
        ∀ (Rt : Finset (Set.Ioi (0 : ℝ))) (hne : Rt.Nonempty), Rt ⊆ plRadiusSet ζ ⟨ε, hε.1⟩ →
          (plRadiusCount ζ ε : ℝ) ≤ 100 * Rt.card →
          P {ω | ¬ compareSubsetHolds (ξ : ℝ) D c m q ζ U ε hε Rt hne Csub (h ω)} ≤
            ENNReal.ofReal (c₀ * ε ^ p₀)

end SupercriticalLQGUniqueness.B2.Polylog
