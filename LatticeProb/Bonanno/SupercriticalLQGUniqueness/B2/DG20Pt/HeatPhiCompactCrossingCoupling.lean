/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiCompactCrossingCoupling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiAnyVersion
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiCrossingComparison

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.DFGPS
  LQGMetric.WhiteNoise LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_phi_compact_crossing_coupling
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (ξ : ℝ) (K U A B : Set ℂ) (hK : IsCompact K)
    (hKsq : K ⊆ closedUnitSquare) (hUK : U ⊆ K)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ M ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : Ioi (0 : ℝ), (ε : ℝ) < ε₀ →
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω')
          (W : WNSpace → Ω' → ℝ) (φ : Ω' → C(ℂ, ℝ))
          (R : Measure (Ω × C(ℂ, ℝ))),
          IsProbabilityMeasure Q ∧ IsWhiteNoise Q W ∧
          (∀ ω z, φ ω z = phiVer W Q ε 1 z ω) ∧
          IsProbabilityMeasure R ∧ R.map Prod.fst = P ∧ R.map Prod.snd = Q.map φ ∧
          R {p | ¬ (
            crossLenIn ξ (X ε p.1) U A B ≤
              ENNReal.ofReal (Real.exp (|ξ| * M)) *
                crossLenIn ξ p.2 U A B ∧
            crossLenIn ξ p.2 U A B ≤
              ENNReal.ofReal (Real.exp (|ξ| * M)) *
                crossLenIn ξ (X ε p.1) U A B)} ≤
            ENNReal.ofReal ζ := by
  obtain ⟨M, ε₀, hε₀, hmain⟩ :=
    dg20_heat_version_phi_compact_sup_tight P h hh X hX K hK hKsq ζ hζ
  refine ⟨M, ε₀, hε₀, ?_⟩
  intro ε hε
  obtain ⟨Ω', iΩ', Q, W, φ, R, hQ, hW, hφ, hR, hfst, hsnd, hsup⟩ :=
    hmain ε hε
  refine ⟨Ω', iΩ', Q, W, φ, R, hQ, hW, hφ, hR, hfst, hsnd, ?_⟩
  have hsub :
      {p : Ω × C(ℂ, ℝ) | ¬ (
        crossLenIn ξ (X ε p.1) U A B ≤
          ENNReal.ofReal (Real.exp (|ξ| * M)) * crossLenIn ξ p.2 U A B ∧
        crossLenIn ξ p.2 U A B ≤
          ENNReal.ofReal (Real.exp (|ξ| * M)) *
            crossLenIn ξ (X ε p.1) U A B)} ⊆
      {p | ∃ y ∈ K, M < |X ε p.1 y - p.2 y|} := by
    intro p hbad
    by_contra hno
    exact hbad (dg20_heat_phi_crossLen_compare_on_compact ξ
      (X ε p.1) p.2 K U A B M hUK
      (by intro y hy; exact le_of_not_gt (fun hgt => hno ⟨y, hy, hgt⟩)))
  exact (measure_mono hsub).trans hsup

end SupercriticalLQGUniqueness.B2.DG20Pt
