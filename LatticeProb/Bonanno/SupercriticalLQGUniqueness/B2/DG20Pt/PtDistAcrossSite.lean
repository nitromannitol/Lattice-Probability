/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAcrossSite at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAcrossGeometry
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistJointCrossLaw

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem pt_dist_across_site_upper_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ x : ℂ,
          ∀ T : ℝ, 3 < T →
          let r : ℝ := (2 : ℝ)⁻¹ ^ k
          P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)) *
              ENNReal.ofReal (T *
                ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n)) <
            crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
              ((fun z : ℂ => z + x) '' ball (0 : ℂ) (17 * r))
              ((fun z : ℂ => z + x) '' sphere (0 : ℂ) (r / 4))
              ((fun z : ℂ => z + x) '' sphere (0 : ℂ) (16 * r))} ≤
            ENNReal.ofReal (c₀ * Real.exp
              (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨hK₁, hK₂, hc₁, hc₂, hnt₁, hnt₂,
    hs₁, hs₂, hdisj, hconnU⟩ := ptAcross_data
  obtain ⟨c₀, c₁, hc₀, hc₁, htail⟩ :=
    perc_field_all_of_inputs hPerc hExp ξ Q hQ ζ hζ
      ptAcrossU (sphere 0 (1 / 4)) (sphere 0 16)
      hK₁ hK₂ hc₁ hc₂ hnt₁ hnt₂ hs₁ hs₂ hdisj hconnU
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n k hkn x T hT
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  have hr : 0 < r := by dsimp [r]; positivity
  have hbase := (htail P W hW n k hkn T hT).2
  dsimp at hbase ⊢
  let Uk : Opens ℂ := ⟨ball 0 (17 * r), isOpen_ball⟩
  have hU : (Uk : Set ℂ) = (fun z : ℂ => (r : ℂ) * z) '' ptAcrossU :=
    (ptAcross_scale_ball hr).symm
  have hA : sphere (0 : ℂ) (r / 4) =
      (fun z : ℂ => (r : ℂ) * z) '' sphere 0 (1 / 4) := by
    rw [ptAcross_scale_sphere hr]
    ring_nf
  have hB : sphere (0 : ℂ) (16 * r) =
      (fun z : ℂ => (r : ℂ) * z) '' sphere 0 16 := by
    rw [ptAcross_scale_sphere hr]
  have hcenter :
      P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
          ENNReal.ofReal (T *
            ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n)) <
        crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
          Uk (sphere (0 : ℂ) (r / 4)) (sphere (0 : ℂ) (16 * r))} ≤
      ENNReal.ofReal (c₀ * Real.exp
        (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
    simpa only [hU, hA, hB, Uk] using hbase
  have hlaw := measure_crossLenIn_phiMN_coarse_upper_motion hW n k hkn
    (ξ : ℝ)
    (T * ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n))
    Uk (sphere 0 (r / 4)) (sphere 0 (16 * r)) 0 (1 : Circle) x
  have htranslated :
      P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)) *
          ENNReal.ofReal (T *
            ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n)) <
        crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
          ((fun z : ℂ => z + x) '' ball (0 : ℂ) (17 * r))
          ((fun z : ℂ => z + x) '' sphere (0 : ℂ) (r / 4))
          ((fun z : ℂ => z + x) '' sphere (0 : ℂ) (16 * r))} =
      P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
          ENNReal.ofReal (T *
            ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n)) <
        crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
          Uk (sphere (0 : ℂ) (r / 4)) (sphere (0 : ℂ) (16 * r))} := by
    simpa [Uk] using hlaw
  rw [htranslated]
  exact hcenter

 

theorem pt_dist_across_site_upper_ball_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ x : ℂ,
          ∀ T : ℝ, 3 < T →
          let r : ℝ := (2 : ℝ)⁻¹ ^ k
          P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)) *
              ENNReal.ofReal (T *
                ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n)) <
            crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
              (ball x (17 * r)) (sphere x (r / 4)) (sphere x (16 * r))} ≤
            ENNReal.ofReal (c₀ * Real.exp
              (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨c₀, c₁, hc₀, hc₁, htail⟩ :=
    pt_dist_across_site_upper_of_inputs hPerc hExp ξ Q hQ ζ hζ
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n k hkn x T hT
  have h := htail P W hW n k hkn x T hT
  simpa only [ptAcross_translate_ball, ptAcross_translate_sphere] using h

end SupercriticalLQGUniqueness.B2.DG20Pt
