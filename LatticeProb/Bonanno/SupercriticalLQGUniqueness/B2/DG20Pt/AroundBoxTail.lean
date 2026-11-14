/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.AroundBoxTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.AroundFourCrossing
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PercBandTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.CoarseOscLog
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.FieldTailSplit
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Mul

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

private theorem exp_half_log_eq_sqrt {T : ℝ} (hT : 0 < T) :
    Real.exp (Real.log T / 2) = Real.sqrt T := by
  have hsq : (Real.exp (Real.log T / 2)) ^ 2 = T := by
    rw [pow_two, ← Real.exp_add]
    have heq : Real.log T / 2 + Real.log T / 2 = Real.log T := by ring
    rw [heq, Real.exp_log hT]
  have hsqrt := Real.sq_sqrt hT.le
  nlinarith [Real.exp_pos (Real.log T / 2), Real.sqrt_nonneg T]

 

private theorem around_sqrt_threshold (ξ T r lam c : ℝ)
    (hξ : 0 < ξ) (hT : 0 < T) (hr : 0 ≤ r) (hlam : 0 ≤ lam) :
    ENNReal.ofReal (Real.exp (|ξ| * (Real.log T / (2 * ξ)))) *
      (ENNReal.ofReal (Real.exp c) *
        (ENNReal.ofReal r * ENNReal.ofReal (Real.sqrt T * lam))) =
      ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (T * r * lam) := by
  have he : Real.exp (|ξ| * (Real.log T / (2 * ξ))) = Real.sqrt T := by
    rw [abs_of_pos hξ]
    have hx : ξ * (Real.log T / (2 * ξ)) = Real.log T / 2 := by
      field_simp
    rw [hx, exp_half_log_eq_sqrt hT]
  rw [he]
  have hs : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hT' : T = Real.sqrt T * Real.sqrt T := by
    nlinarith [Real.sq_sqrt hT.le]
  conv_rhs => rw [hT']
  simp only [ENNReal.ofReal_mul hs, ENNReal.ofReal_mul hr]
  have hreorder : Real.sqrt T * Real.sqrt T * r * lam =
      Real.sqrt T * (r * (Real.sqrt T * lam)) := by ring
  rw [hreorder, ENNReal.ofReal_mul hs, ENNReal.ofReal_mul hr,
    ENNReal.ofReal_mul hs]
  ac_rfl

 



theorem around_box_tail_of_percEstimate
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (U : Opens ℂ) (hU : Bornology.IsBounded (U : Set ℂ))
    (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hconn₁ : IsConnected K₁) (hconn₂ : IsConnected K₂)
    (hnt₁ : K₁.Nontrivial) (hnt₂ : K₂.Nontrivial)
    (hsub₁ : K₁ ⊆ U) (hsub₂ : K₂ ⊆ U)
    (hdisj : Disjoint K₁ K₂) (hconnU : IsConnected (U : Set ℂ)) :
    ∃ c₀ c₁ d₀ d₁ : ℝ,
      0 < c₀ ∧ 0 < c₁ ∧ 0 < d₀ ∧ 0 < d₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ T : ℝ, 9 < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        let F : ℂ → ℂ := fun z => (r : ℂ) * z
        P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T * r * lambdaN ξ W P (n - k)) <
          crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (F '' U) (F '' K₁) (F '' K₂)} ≤
          ENNReal.ofReal (d₀ * Real.exp (-d₁ * (Real.log T) ^ 2)) +
          ENNReal.ofReal (c₀ * Real.exp
            (-c₁ * (Real.log (Real.sqrt T)) ^ 2 /
              Real.log (Real.log (Real.sqrt T)))) := by
  obtain ⟨c₀, c₁, hc₀, hc₁, hband⟩ :=
    hPerc ξ U K₁ K₂ hK₁ hK₂ hconn₁ hconn₂
      hnt₁ hnt₂ hsub₁ hsub₂ hdisj hconnU
  obtain ⟨d₀, d₁, hd₀, hd₁, hosc⟩ :=
    phiMN_center_osc_log_tail hU ξ ξ.property
  refine ⟨c₀, c₁, d₀, d₁, hc₀, hc₁, hd₀, hd₁, ?_⟩
  intro Ω _ P _ W hW n k hkn T hT
  dsimp
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  let F : ℂ → ℂ := fun z => (r : ℂ) * z
  let S : ℝ := Real.sqrt T
  let δ : ℝ := Real.log T / (2 * (ξ : ℝ))
  have hS : 3 < S := by
    dsimp [S]
    exact Real.lt_sqrt_of_sq_lt (by nlinarith)
  have hosc' : P {ω | ∃ z ∈ F '' U,
      δ < |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω|} ≤
      ENNReal.ofReal (d₀ * Real.exp (-d₁ * (Real.log T) ^ 2)) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (by simpa only [F, r, δ] using hosc P W hW k T (by linarith))
  have hband' : P {ω | ENNReal.ofReal (S * lambdaN ξ W P (n - k)) <
      crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 (n - k) z ω) U K₁ K₂} ≤
      ENNReal.ofReal (c₀ * Real.exp
        (-c₁ * (Real.log S) ^ 2 / Real.log (Real.log S))) := by
    exact (hband P W hW (n - k) S hS).2
  have hsplit := measure_full_crossing_gt_split P W hW (ξ : ℝ)
    U K₁ K₂ hkn δ (ENNReal.ofReal (S * lambdaN ξ W P (n - k)))
  dsimp at hsplit
  have hevent : {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
      ENNReal.ofReal (T * r * lambdaN ξ W P (n - k)) <
        crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
          (F '' U) (F '' K₁) (F '' K₂)} =
      {ω | ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * δ)) *
        (ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
          (ENNReal.ofReal r *
            ENNReal.ofReal (S * lambdaN ξ W P (n - k)))) <
        crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
          (F '' U) (F '' K₁) (F '' K₂)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [around_sqrt_threshold (ξ : ℝ) T r
      (lambdaN ξ W P (n - k)) ((ξ : ℝ) * phiMN W P 0 k 0 ω)
      ξ.property (by linarith) (by dsimp [r]; positivity)
      (lambdaN_pos hW (n - k)).le]
  rw [hevent]
  exact hsplit.trans (add_le_add hosc' hband')

end SupercriticalLQGUniqueness.B2.DG20Pt
