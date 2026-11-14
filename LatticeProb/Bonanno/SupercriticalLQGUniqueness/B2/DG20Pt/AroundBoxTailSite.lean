/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.AroundBoxTailSite at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.AroundPolarScale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistJointCrossLaw

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem around_cfg_box_tail_of_percEstimate
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (j : Fin 4) :
    ∃ c₀ c₁ d₀ d₁ : ℝ,
      0 < c₀ ∧ 0 < c₁ ∧ 0 < d₀ ∧ 0 < d₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ x : ℂ, ∀ T : ℝ, 9 < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        let A := Inputs.annulus48 x r (by dsimp [r]; positivity)
        P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)) *
            ENNReal.ofReal (T * r * lambdaN ξ W P (n - k)) <
          crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (Strong.cfgOpens A j) (Strong.cfgSet₁ A j) (Strong.cfgSet₂ A j)} ≤
          ENNReal.ofReal (d₀ * Real.exp (-d₁ * (Real.log T) ^ 2)) +
          ENNReal.ofReal (c₀ * Real.exp
            (-c₁ * (Real.log (Real.sqrt T)) ^ 2 /
              Real.log (Real.log (Real.sqrt T)))) := by
  let A₁ := Inputs.annulus48 0 1 one_pos
  obtain ⟨hU, hK₁, hK₂, hconn₁, hconn₂, hnt₁, hnt₂,
    hsub₁, hsub₂, hdisj, hconnU⟩ := around_polar_data A₁ j
  obtain ⟨c₀, c₁, d₀, d₁, hc₀, hc₁, hd₀, hd₁, htail⟩ :=
    around_box_tail_of_percEstimate hPerc ξ (Strong.cfgOpens A₁ j) hU
      (Strong.cfgSet₁ A₁ j) (Strong.cfgSet₂ A₁ j)
      hK₁ hK₂ hconn₁ hconn₂ hnt₁ hnt₂ hsub₁ hsub₂ hdisj hconnU
  refine ⟨c₀, c₁, d₀, d₁, hc₀, hc₁, hd₀, hd₁, ?_⟩
  intro Ω _ P _ W hW n k hkn x T hT
  dsimp
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  have hr : 0 < r := by dsimp [r]; positivity
  let A₀ := Inputs.annulus48 0 r hr
  let A := Inputs.annulus48 x r hr
  have hcenter := htail P W hW n k hkn T hT
  dsimp at hcenter
  have hcenter' :
      P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
          ENNReal.ofReal (T * r * lambdaN ξ W P (n - k)) <
        crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
          (Strong.cfgOpens A₀ j) (Strong.cfgSet₁ A₀ j) (Strong.cfgSet₂ A₀ j)} ≤
        ENNReal.ofReal (d₀ * Real.exp (-d₁ * (Real.log T) ^ 2)) +
        ENNReal.ofReal (c₀ * Real.exp
          (-c₁ * (Real.log (Real.sqrt T)) ^ 2 /
            Real.log (Real.log (Real.sqrt T)))) := by
    rw [around_cfgOpens_scale 0 hr j, around_cfgSet₁_scale 0 hr j,
      around_cfgSet₂_scale 0 hr j]
    simpa only [zero_add, A₁, r] using hcenter
  have hlaw := measure_crossLenIn_phiMN_coarse_upper_motion hW n k hkn
    (ξ : ℝ) (T * r * lambdaN ξ W P (n - k))
    (Strong.cfgOpens A₀ j) (Strong.cfgSet₁ A₀ j)
    (Strong.cfgSet₂ A₀ j) 0 (1 : Circle) x
  have htranslated :
      P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)) *
          ENNReal.ofReal (T * r * lambdaN ξ W P (n - k)) <
        crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
          (Strong.cfgOpens A j) (Strong.cfgSet₁ A j) (Strong.cfgSet₂ A j)} =
      P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
          ENNReal.ofReal (T * r * lambdaN ξ W P (n - k)) <
        crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
          (Strong.cfgOpens A₀ j) (Strong.cfgSet₁ A₀ j) (Strong.cfgSet₂ A₀ j)} := by
    simpa [around_cfgOpens_translate x hr j, around_cfgSet₁_translate x hr j,
      around_cfgSet₂_translate x hr j, A, A₀] using hlaw
  rw [htranslated]
  exact hcenter'

end SupercriticalLQGUniqueness.B2.DG20Pt
