/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatLocalEdgeUpper at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatLocalSquareGeometry
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointTranslatedSquareSmall
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.FieldComparison

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_local_edge_small_upper
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Qexp : ℝ) (hQ : IsLFPPExponent ξ Qexp)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (U : Set ℂ) (p q : ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (hρsmall : 4 * ρ ≤ (1 / 2 : ℝ))
    (hpq : dist p q < 2 * ρ)
    (hball : ball p (4 * ρ) ⊆ U)
    (η : ℝ) (hη : 0 < η) :
    ∃ T ε₀ : ℝ, 0 < T ∧ 0 < ε₀ ∧
      ∀ ε : Ioo (0 : ℝ) 1, (ε : ℝ) < ε₀ →
        P {ω | ENNReal.ofReal T <
          ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
            crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {p} {q}} ≤
          ENNReal.ofReal η := by
  let c : ℂ := Complex.mk (1 / 2) (1 / 2)
  let V : Set ℂ := ball c (4 * ρ)
  let a : ℂ := p - c
  have hgeom := dg20_local_edge_square_data hρ hρsmall hpq hball
  change IsOpen V ∧ IsConnected V ∧ V ⊆ closedUnitSquare ∧
    c ∈ V ∧ q - a ∈ V ∧ (· + a) '' V ⊆ U at hgeom
  obtain ⟨hVo, hVc, hVsq, hc, hq, hVU⟩ := hgeom
  by_cases hpqne : p = q
  · subst q
    have hpU : p ∈ U := hball (mem_ball_self (by positivity))
    have hself (ε : Ioo (0 : ℝ) 1) (ω : Ω) :
        crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {p} {p} = 0 := by
      rw [LQGMetric.DFGPS.crossLenIn_singleton]
      have hmono := crossLenIn_mono_domain (ξ : ℝ)
        (X ⟨ε, ε.property.1⟩ ω) (A := {p}) (B := {p}) hball
      simp only [LQGMetric.DFGPS.crossLenIn_singleton] at hmono
      rw [lfppDOn_self (ξ := (ξ : ℝ)) (φ := X ⟨ε, ε.property.1⟩ ω)
        (convex_ball p (4 * ρ)) (mem_ball_self (by positivity))] at hmono
      exact le_antisymm hmono zero_le
    refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro ε hε
    have hempty : {ω : Ω | ENNReal.ofReal (1 : ℝ) <
      ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
        crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {p} {p}} = ∅ := by
      ext ω
      simp [hself ε ω]
    rw [hempty, measure_empty]
    exact zero_le
  · have hcq : c ≠ q - a := by
      intro heq
      apply hpqne
      calc
        p = c + a := by dsimp [a]; abel
        _ = q := by rw [heq]; abel
    obtain ⟨T, ε₀, hT, hε₀, htail⟩ :=
      dg20_heat_point_translated_square_small_tails_of_inputs
        hPerc hExp hPos ξ Qexp hQ m hm P h hh X hX
        a V hVo hVc hVsq c (q - a) hc hq hcq η hη
    refine ⟨T, ε₀, hT, hε₀, ?_⟩
    intro ε hε
    have htail' := (htail ε hε).1
    have hsub : {ω | ENNReal.ofReal T <
        ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
          crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {p} {q}} ⊆
      {ω | ENNReal.ofReal T <
        ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
          crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
            ((· + a) '' V) {c + a} {(q - a) + a}} := by
      intro ω hω
      have hdom := crossLenIn_mono_domain (ξ : ℝ)
        (X ⟨ε, ε.property.1⟩ ω) (A := {p}) (B := {q}) hVU
      have hmul : ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
          crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) U {p} {q} ≤
          ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
            crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω) ((· + a) '' V) {p} {q} := by
        gcongr
      have hca : c + a = p := by dsimp [a]; abel
      have hqa : (q - a) + a = q := by abel
      change ENNReal.ofReal T <
        ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
          crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
            ((· + a) '' V) {c + a} {(q - a) + a}
      rw [hca, hqa]
      exact lt_of_lt_of_le hω hmul
    exact (measure_mono hsub).trans htail'

end SupercriticalLQGUniqueness.B2.DG20Pt
