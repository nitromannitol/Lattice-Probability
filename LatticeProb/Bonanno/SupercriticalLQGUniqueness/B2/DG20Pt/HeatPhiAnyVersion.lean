/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiAnyVersion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatVersionPoint

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem dg20_heat_version_phi_compact_sup_tight
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (K : Set ℂ) (hK : IsCompact K) (hKsq : K ⊆ closedUnitSquare) :
    ∀ ζ : ℝ, 0 < ζ → ∃ M ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : Ioi (0 : ℝ), (ε : ℝ) < ε₀ →
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω')
          (W : WNSpace → Ω' → ℝ) (φ : Ω' → C(ℂ, ℝ))
          (R : Measure (Ω × C(ℂ, ℝ))),
          IsProbabilityMeasure Q ∧ IsWhiteNoise Q W ∧
          (∀ ω z, φ ω z = phiVer W Q ε 1 z ω) ∧
          IsProbabilityMeasure R ∧ R.map Prod.fst = P ∧ R.map Prod.snd = Q.map φ ∧
          R {p | ∃ z ∈ K,
            M < |X ε p.1 z - p.2 z|} ≤
            ENNReal.ofReal ζ := by
  intro ζ hζ
  obtain ⟨M, ε₀, hε₀, hmain⟩ :=
    dg20_whole_plane_heat_phi_compact_sup_tight_and_paths
      P h hh K hK hKsq ζ hζ
  refine ⟨M, ε₀, hε₀, ?_⟩
  intro ε hεε₀
  obtain ⟨Ω', iΩ', Q, W, φ, R, hQ, hW, hφ, hR, hfst, hsnd, hsup, _⟩ :=
    hmain ε ε.property hεε₀
  letI : MeasurableSpace Ω' := iΩ'
  letI : IsProbabilityMeasure Q := hQ
  letI : IsProbabilityMeasure R := hR
  have hae := dg20_heat_smoothing_ae_heatMollify
    P h hh ε (X ε) (hX ε)
  let E : Set Ω := {ω | ∃ z : ℂ, X ε ω z ≠ heatMollify ε (h ω) z}
  have hEzero : P E = 0 := by
    simpa only [E, ae_iff, not_forall] using hae
  have hREzero : R {p | p.1 ∈ E} = 0 := by
    apply le_antisymm
    · calc
        R {p | p.1 ∈ E} ≤ (R.map Prod.fst) E :=
          Measure.le_map_apply measurable_fst.aemeasurable E
        _ = 0 := by rw [hfst, hEzero]
    · exact bot_le
  have hsub :
      {p : Ω × C(ℂ, ℝ) | ∃ z ∈ K, M < |X ε p.1 z - p.2 z|} ⊆
        {p | ∃ z ∈ K, M < |heatMollify ε (h p.1) z - p.2 z|} ∪
        {p | p.1 ∈ E} := by
    rintro p ⟨z, hz, hb⟩
    by_cases he : p.1 ∈ E
    · exact Or.inr he
    · left
      refine ⟨z, hz, ?_⟩
      have heq : X ε p.1 z = heatMollify ε (h p.1) z := by
        by_contra hne
        exact he ⟨z, hne⟩
      simpa only [heq] using hb
  refine ⟨Ω', iΩ', Q, W, φ, R, hQ, hW, hφ, hR, hfst, hsnd, ?_⟩
  calc
    R {p : Ω × C(ℂ, ℝ) | ∃ z ∈ K,
        M < |X ε p.1 z - p.2 z|} ≤
      R ({p | ∃ z ∈ K, M < |heatMollify ε (h p.1) z - p.2 z|} ∪
        {p | p.1 ∈ E}) := measure_mono hsub
    _ ≤ R {p | ∃ z ∈ K, M < |heatMollify ε (h p.1) z - p.2 z|} +
        R {p | p.1 ∈ E} := measure_union_le _ _
    _ = R {p | ∃ z ∈ K, M < |heatMollify ε (h p.1) z - p.2 z|} := by
      rw [hREzero, add_zero]
    _ ≤ ENNReal.ofReal ζ := hsup

end SupercriticalLQGUniqueness.B2.DG20Pt
