/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiSquareCrossing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiAnyVersion
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatCrossingAdapter
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffSq

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.DFGPS
  LQGMetric.WhiteNoise LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_phi_square_crossing_coupling
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (ξ : ℝ) (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ M ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : Ioi (0 : ℝ), (ε : ℝ) < ε₀ →
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω')
          (W : WNSpace → Ω' → ℝ) (φ : Ω' → C(ℂ, ℝ))
          (R : Measure (Ω × C(ℂ, ℝ))),
          IsProbabilityMeasure Q ∧ IsWhiteNoise Q W ∧
          (∀ ω z, φ ω z = phiVer W Q ε 1 z ω) ∧
          IsProbabilityMeasure R ∧ R.map Prod.fst = P ∧ R.map Prod.snd = Q.map φ ∧
          R {p | ¬ (
            lfppCrossingLength ξ (X ε p.1) ≤
              ENNReal.ofReal (Real.exp (|ξ| * M)) * lfppCrossingLength ξ p.2 ∧
            lfppCrossingLength ξ p.2 ≤
              ENNReal.ofReal (Real.exp (|ξ| * M)) *
                lfppCrossingLength ξ (X ε p.1))} ≤ ENNReal.ofReal ζ := by
  obtain ⟨M, ε₀, hε₀, hmain⟩ :=
    dg20_heat_version_phi_compact_sup_tight P h hh X hX
      closedUnitSquare isCompact_closedUnitSquare Subset.rfl ζ hζ
  refine ⟨M, ε₀, hε₀, ?_⟩
  intro ε hε
  obtain ⟨Ω', iΩ', Q, W, φ, R, hQ, hW, hφ, hR, hfst, hsnd, hsup⟩ :=
    hmain ε hε
  refine ⟨Ω', iΩ', Q, W, φ, R, hQ, hW, hφ, hR, hfst, hsnd, ?_⟩
  have hsub :
      {p : Ω × C(ℂ, ℝ) | ¬ (
        lfppCrossingLength ξ (X ε p.1) ≤
          ENNReal.ofReal (Real.exp (|ξ| * M)) * lfppCrossingLength ξ p.2 ∧
        lfppCrossingLength ξ p.2 ≤
          ENNReal.ofReal (Real.exp (|ξ| * M)) *
            lfppCrossingLength ξ (X ε p.1))} ⊆
      {p | ∃ z ∈ closedUnitSquare, M < |X ε p.1 z - p.2 z|} := by
    intro p hbad
    by_contra hno
    exact hbad (dg20_lfppCrossingLength_compare_of_square_sup ξ
      (X ε p.1) p.2 M (by
        intro z hz
        exact le_of_not_gt (fun hgt => hno ⟨z, hz, hgt⟩)))
  exact (measure_mono hsub).trans hsup

end SupercriticalLQGUniqueness.B2.DG20Pt
