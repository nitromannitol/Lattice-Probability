/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatWholePlaneZBVersion at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovFinal
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinCmp
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffCV
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinSetup
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal
open LQGMetric LQGMetric.DFGPS LQGMetric.HeatSq LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_whole_plane_zero_boundary_heat_version
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∃ (Xh : BddOn ((sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ) → Ω → ℝ)
      (Y : ℝ → ℂ → Ω → ℝ),
      IsZBGFFProcessExt (sqOpens (-1) 3) Xh P ∧
      (∀ δ ∈ Ioo (0 : ℝ) 1,
        IsContVersion (fun z => Xh (heatBdd (sqOpens (-1) 3) (δ / 2) z)) (Y δ) P) ∧
      ∀ ζ : ℝ, 0 < ζ → ∃ M ε₁ : ℝ, 0 < ε₁ ∧
        ∀ ε : ℝ, 0 < ε → ε < ε₁ →
          P {ω | ∃ z ∈ closedUnitSquare,
            M < |heatMollify ε (h ω) z - Y (ε ^ 2) z ω|} ≤
            ENNReal.ofReal ζ := by
  have hVb : Bornology.IsBounded
      ((sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ) :=
    isBounded_sqOpen (-1) 3
  have hVd : Disjoint
      ((sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ)
      (sphere (0 : ℂ) 4) := disjoint_sqOpen_sphere
  obtain ⟨hhar, hz, Xh, hsum, hharm, -, hX, hlink⟩ :=
    markov_zb_coupling LQGMetric.MarkovFinal.lmLem2_1 P h hh.1
      (by norm_num : (0 : ℝ) < 4) 0 (sqOpens (-1) 3) hVb hVd
  obtain ⟨Y, hY⟩ := exists_heat_contVersion_sq
    (by norm_num : (0 : ℝ) < 3) hX
  exact ⟨Xh, Y, hX, hY, gff_zb_field_prob hh.1 hsum hharm hX hlink hY⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
