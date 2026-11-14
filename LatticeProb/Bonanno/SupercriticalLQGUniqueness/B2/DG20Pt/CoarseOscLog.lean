/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.CoarseOscLog at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.BoundedCoarseOsc

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 



theorem phiMN_center_osc_log_tail
    {U : Set ℂ} (hU : Bornology.IsBounded U)
    (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ k : ℕ, ∀ T : ℝ, 3 < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        P.real {ω | ∃ z ∈ (fun z : ℂ => (r : ℂ) * z) '' U,
          Real.log T / (2 * ξ) <
            |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω|} ≤
          c₀ * Real.exp (-c₁ * (Real.log T) ^ 2) := by
  obtain ⟨B, hB, htail⟩ := phiMN_center_osc_tail_bounded hU
  let A : ℝ := Real.sqrt (2 * (6 * (Real.sqrt 2 * (2 * B))) * Real.log 2) +
    ferniqueCF * Real.sqrt (3 * (Real.sqrt 2 * (2 * B)))
  have hA : 0 ≤ A := by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hCF : 0 < ferniqueCF := ferniqueCF_pos
    dsimp [A]
    positivity
  let d : ℝ := 2 * (6 * (Real.sqrt 2 * (2 * B)))
  have hd : 0 < d := by dsimp [d]; positivity
  let c₁ : ℝ := 1 / (64 * ξ ^ 2 * d)
  have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
  let c₀ : ℝ := Real.exp (c₁ * (8 * ξ * A) ^ 2)
  have hc₀ : 0 < c₀ := Real.exp_pos _
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW k T hT
  dsimp
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  by_cases hlarge : 8 * ξ * A ≤ Real.log T
  · let x : ℝ := Real.log T / (4 * ξ) - A
    have hxlow : Real.log T / (8 * ξ) ≤ x := by
      dsimp [x]
      have hAb : A ≤ Real.log T / (8 * ξ) := by
        apply (le_div_iff₀ (by positivity : 0 < 8 * ξ)).2
        nlinarith [hlarge]
      have heq : Real.log T / (4 * ξ) =
          2 * (Real.log T / (8 * ξ)) := by field_simp; ring
      rw [heq]
      linarith
    have hx : 0 ≤ x := le_trans (by positivity) hxlow
    have hbad : {ω | ∃ z ∈ (fun z : ℂ => (r : ℂ) * z) '' U,
          Real.log T / (2 * ξ) <
            |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω|} ⊆
        {ω | ∃ z ∈ (fun z : ℂ => (r : ℂ) * z) '' U,
          2 * (A + x) ≤
            |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω|} := by
      rintro ω ⟨z, hz, hbig⟩
      refine ⟨z, hz, ?_⟩
      have heq : 2 * (A + x) = Real.log T / (2 * ξ) := by
        dsimp [x]
        field_simp
        ring
      exact heq.le.trans hbig.le
    have htail' := htail P W hW k x hx
    have hprob : P.real {ω | ∃ z ∈ (fun z : ℂ => (r : ℂ) * z) '' U,
          Real.log T / (2 * ξ) <
            |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω|} ≤
        Real.exp (-x ^ 2 / d) := by
      exact (measureReal_mono hbad).trans (by simpa only [A, d, r] using htail')
    have hsq : (Real.log T / (8 * ξ)) ^ 2 ≤ x ^ 2 :=
      (sq_le_sq₀ (by positivity) hx).2 hxlow
    have hrate : c₁ * (Real.log T) ^ 2 ≤ x ^ 2 / d := by
      calc c₁ * (Real.log T) ^ 2 = (Real.log T / (8 * ξ)) ^ 2 / d := by
            dsimp [c₁]; field_simp; ring
        _ ≤ x ^ 2 / d := div_le_div_of_nonneg_right hsq hd.le
    calc
      _ ≤ Real.exp (-x ^ 2 / d) := hprob
      _ ≤ Real.exp (-c₁ * (Real.log T) ^ 2) :=
        Real.exp_le_exp.mpr (by
          calc
            -x ^ 2 / d = -(x ^ 2 / d) := by ring
            _ ≤ -(c₁ * (Real.log T) ^ 2) := neg_le_neg hrate
            _ = -c₁ * (Real.log T) ^ 2 := by ring)
      _ ≤ c₀ * Real.exp (-c₁ * (Real.log T) ^ 2) := by
        exact le_mul_of_one_le_left (Real.exp_nonneg _) (by
          dsimp [c₀]; exact Real.one_le_exp (by positivity))
  · have hsmall : Real.log T ≤ 8 * ξ * A := le_of_not_ge hlarge
    calc
      _ ≤ 1 := measureReal_le_one
      _ ≤ c₀ * Real.exp (-c₁ * (Real.log T) ^ 2) := by
        rw [show c₀ * Real.exp (-c₁ * (Real.log T) ^ 2) =
          Real.exp (c₁ * (8 * ξ * A) ^ 2 - c₁ * (Real.log T) ^ 2) by
            dsimp [c₀]; rw [← Real.exp_add]; ring]
        apply Real.one_le_exp
        have hsq : (Real.log T) ^ 2 ≤ (8 * ξ * A) ^ 2 :=
          (sq_le_sq₀ hlog.le (by positivity)).2 hsmall
        nlinarith [mul_nonneg hc₁.le (sub_nonneg.mpr hsq)]

end SupercriticalLQGUniqueness.B2.DG20Pt
