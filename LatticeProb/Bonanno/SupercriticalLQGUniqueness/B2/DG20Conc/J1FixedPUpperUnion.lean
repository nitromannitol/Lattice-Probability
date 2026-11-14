/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPUpperUnion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SamePUpperUnion
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPUnitRate
 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_fixed_p_scaled_upper_union
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧ LaneA2HasUnitTails.{u} ξ p ∧
      ∀ (C : ℝ) (hC : 0 ≤ C), ∃ A CN cN CP cP : ℝ,
      0 < A ∧
      0 < CN ∧ 0 < cN ∧ 0 < CP ∧ 0 < cP ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : 64 ≤ K) (hKn : K ≤ n)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (i : Bool) (T : ℝ)
        (hT : Real.exp ((A + 5) * (C + 1) *
          Real.sqrt ((K : ℝ) + 1)) ≤ T),
        P {ω | ∃ b ∈ T20B.nearIdx K,
          crossLenIn ξ (fun z => phiMN W P K n z ω)
            (laneBBlockAnnulus i (T20.dyCenter K b) K)
            (j1BlockInner i (T20.dyCenter K b) K)
            (j1BlockOuter i (T20.dyCenter K b) K) <
            ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
              ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - K))} ≤
          ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CN * Real.exp (-cN * (Real.log T)^2)) ∧
        P {ω | ∃ b ∈ T20B.nearIdx K,
          ENNReal.ofReal (T * lambdaN ξ W P (n - K)) <
            (lfppContMetric ξ (fun z => phiMN W P K n
              (((2 : ℝ)⁻¹ ^ K : ℝ) * z +
                j1BlockAffineCenter (T20.dyCenter K b) K) ω)
              ((isPhiVersion_phiMN hW hKn).cont ω |>.comp
                (show Continuous (fun z : ℂ =>
                  (((2 : ℝ)⁻¹ ^ K : ℝ) * z +
                    j1BlockAffineCenter (T20.dyCenter K b) K)) by
                    fun_prop))).aroundDist
                (laneCUnitUaround i) (laneCUnitInner i)
                (laneCUnitOuter i)} ≤
          ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CP * Real.exp
              (-cP * (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨p, hp, hpHalf, hunit, hfixed⟩ := j1_fixed_p_unit_source_rates hξ
  refine ⟨p, hp, hpHalf, hunit, ?_⟩
  intro C hC
  obtain ⟨A, CN, cN, CP, cP, hA,
    hCN, hcN, hCP, hcP, htail⟩ := hfixed C hC
  refine ⟨A, CN, cN, CP, cP, hA,
    hCN, hcN, hCP, hcP, ?_⟩
  intro Ω _ P W hW K n hK hKn hH i T hT
  constructor
  · let E : ℤ × ℤ → Set Ω := fun b =>
      {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
        (laneBBlockAnnulus i (T20.dyCenter K b) K)
        (j1BlockInner i (T20.dyCenter K b) K)
        (j1BlockOuter i (T20.dyCenter K b) K) <
        ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - K))}
    have hblock : ∀ b ∈ T20B.nearIdx K,
        P (E b) ≤ ENNReal.ofReal
          (CN * Real.exp (-cN * (Real.log T)^2)) := by
      intro b hb
      change P {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
        (laneBBlockAnnulus i (T20.dyCenter K b) K)
        (j1BlockInner i (T20.dyCenter K b) K)
        (j1BlockOuter i (T20.dyCenter K b) K) <
        ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - K))} ≤ _
      rw [j1_block_cross_scale_law P W hW hKn ξ i (T20.dyCenter K b)]
      exact (htail P W hW K (n - K) hH i 0 T hT).1
    change P {ω | ∃ b ∈ T20B.nearIdx K, ω ∈ E b} ≤ _
    exact j1_block_union_of_pointwise P K (by omega) E _ hblock
  ·
    let E : ℤ × ℤ → Set Ω := fun b =>
      {ω | ENNReal.ofReal (T * lambdaN ξ W P (n - K)) <
        (lfppContMetric ξ (fun z => phiMN W P K n
          (((2 : ℝ)⁻¹ ^ K : ℝ) * z +
            j1BlockAffineCenter (T20.dyCenter K b) K) ω)
          ((isPhiVersion_phiMN hW hKn).cont ω |>.comp
            (show Continuous (fun z : ℂ =>
            (((2 : ℝ)⁻¹ ^ K : ℝ) * z +
              j1BlockAffineCenter (T20.dyCenter K b) K)) by
                fun_prop))).aroundDist
            (laneCUnitUaround i) (laneCUnitInner i)
            (laneCUnitOuter i)}
    have hblock : ∀ b ∈ T20B.nearIdx K,
        P (E b) ≤ ENNReal.ofReal (CP * Real.exp
          (-cP * (Real.log T)^2 / Real.log (Real.log T))) := by
      intro b hb
      have hh := (htail P W hW K (n - K) hH i
        (j1BlockAffineCenter (T20.dyCenter K b) K) T hT).2
      simpa only [Nat.add_sub_of_le hKn] using hh
    change P {ω | ∃ b ∈ T20B.nearIdx K, ω ∈ E b} ≤ _
    exact j1_block_union_of_pointwise P K (by omega) E _ hblock

end SupercriticalLQGUniqueness.B2.DG20Conc
