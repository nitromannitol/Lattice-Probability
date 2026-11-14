/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAllScalesInsideTail at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAllScalesInsideEvent
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateCompact

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem exists_pt_dist_all_scales_inside_tail_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (V : Set ℂ) (hV : Bornology.IsBounded V) (hconv : Convex ℝ V)
    (R : ℝ) (hR : 0 < R) :
    ∃ Cnet : ℕ, 0 < Cnet ∧ ∃ C c₀ c₁ : ℝ,
      0 < C ∧ 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, ∀ T : ℝ, 3 < T →
          ∃ F : ℕ → Finset ℂ,
            (∀ k ≤ n, (F k).card ≤ Cnet * 4 ^ k ∧
              (∀ x ∈ F k, x ∈ V) ∧
              ∀ z ∈ V, ∃ x ∈ F k,
                dist z x < ((2 : ℝ)⁻¹) ^ (k + 2)) ∧
            P (ptDistAllScalesGood P W ξ Q ζ C n F V R T
              (fun k => (Real.log T + ζ * (k : ℝ)) / (R * (ξ : ℝ))))ᶜ ≤
              ENNReal.ofReal (c₀ * Real.exp
                (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨Cnet, hCnet, C, a₀, a₁, b₀, b₁, D, σ2,
    hC, ha₀, ha₁, hb₀, hb₁, hD, hσ2, hevent⟩ :=
      exists_pt_dist_all_scales_inside_event_of_inputs
        hPerc hExp ξ Q hQ ζ hζ V hV hconv R hR
  obtain ⟨H, hH, hrate⟩ :=
    pt_dist_scale_rate_sum_large Cnet a₀ a₁ b₀ b₁ D σ2 ζ R (ξ : ℝ)
      ha₀.le ha₁ hb₀.le hb₁ hD.le hσ2 hζ hR ξ.2
  let A : ℝ := 2 * ((Cnet : ℝ) * a₀)
  let B : ℝ := 2 * ((Cnet : ℝ) * b₀)
  let D' : ℝ := 2 * D
  let g : ℝ := 1 / (2 * σ2 * (R * (ξ : ℝ)) ^ 2) / 2
  let c₁ : ℝ := min (a₁ / 2) (min (b₁ / 2) g)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD' : 0 ≤ D' := by dsimp [D']; positivity
  have hRξ : 0 < R * (ξ : ℝ) := mul_pos hR ξ.2
  have hg : 0 < g := by dsimp [g]; positivity
  have hc₁ : 0 < c₁ := by dsimp [c₁]; exact lt_min (by positivity) (lt_min (by positivity) hg)
  obtain ⟨Cpatch, hCpatch, hpatch⟩ := pt_dist_rate_compact_patch H c₁ hc₁
  let c₀ : ℝ := A + B + D' + Cpatch
  have hc₀ : 0 < c₀ := by dsimp [c₀]; linarith
  refine ⟨Cnet, hCnet, C, c₀, c₁, hC, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n T hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have ht (k : ℕ) (_hk : k ≤ n) :
      0 ≤ (Real.log T + ζ * (k : ℝ)) / (R * (ξ : ℝ)) :=
    div_nonneg (add_nonneg hlogT (mul_nonneg hζ.le (Nat.cast_nonneg k)))
      (mul_pos hR ξ.2).le
  obtain ⟨F, hcover, hbad⟩ := hevent P W hW n T hT
    (fun k => (Real.log T + ζ * (k : ℝ)) / (R * (ξ : ℝ))) ht
  refine ⟨F, hcover, ?_⟩
  by_cases hlarge : Real.exp H ≤ T
  · have hL : 3 ≤ Real.log T := by
      have h := (Real.le_log_iff_exp_le (by linarith : 0 < T)).2 hlarge
      linarith
    have hmerge := pt_dist_three_rate_merge A B D' (a₁ / 2) (b₁ / 2) g
      (Real.log T) hA hB hD' (by positivity) (by positivity) hg hL
    have hreal :
        A * Real.exp (-(a₁ / 2) * ((Real.log T) ^ 2 / Real.log (Real.log T))) +
        B * Real.exp (-(b₁ / 2) * ((Real.log T) ^ 2 / Real.log (Real.log T))) +
        D' * Real.exp (-g * (Real.log T) ^ 2) ≤
        c₀ * Real.exp (-c₁ * ((Real.log T) ^ 2 / Real.log (Real.log T))) := by
      have hm :
          A * Real.exp (-(a₁ / 2) * ((Real.log T) ^ 2 / Real.log (Real.log T))) +
          B * Real.exp (-(b₁ / 2) * ((Real.log T) ^ 2 / Real.log (Real.log T))) +
          D' * Real.exp (-g * (Real.log T) ^ 2) ≤
          (A + B + D') * Real.exp (-c₁ * ((Real.log T) ^ 2 / Real.log (Real.log T))) :=
        hmerge.2
      calc
        _ ≤ (A + B + D') * Real.exp
          (-c₁ * ((Real.log T) ^ 2 / Real.log (Real.log T))) := hm
        _ ≤ c₀ * Real.exp
          (-c₁ * ((Real.log T) ^ 2 / Real.log (Real.log T))) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          dsimp [c₀]
          linarith
    calc
      P (ptDistAllScalesGood P W ξ Q ζ C n F V R T
        (fun k => (Real.log T + ζ * (k : ℝ)) / (R * (ξ : ℝ))))ᶜ ≤
        ∑ k ∈ Finset.range (n + 1),
          ptDistScaleRate Cnet a₀ a₁ b₀ b₁ D σ2 ζ T k
            ((Real.log T + ζ * (k : ℝ)) / (R * (ξ : ℝ))) := hbad
      _ ≤ ENNReal.ofReal
          (A * Real.exp (-(a₁ / 2) * ((Real.log T) ^ 2 / Real.log (Real.log T))) +
           B * Real.exp (-(b₁ / 2) * ((Real.log T) ^ 2 / Real.log (Real.log T))) +
           D' * Real.exp (-g * (Real.log T) ^ 2)) := by
          simpa only [A, B, D', g] using hrate T hlarge (n + 1)
      _ ≤ _ := by
        convert ENNReal.ofReal_le_ofReal hreal using 1 <;> congr 1 <;> ring
  · have hsmall : T ≤ Real.exp H := le_of_lt (lt_of_not_ge hlarge)
    have hprob : P (ptDistAllScalesGood P W ξ Q ζ C n F V R T
        (fun k => (Real.log T + ζ * (k : ℝ)) / (R * (ξ : ℝ))))ᶜ ≤ 1 :=
      prob_le_one
    have hunit : (1 : ℝ≥0∞) ≤ ENNReal.ofReal
        (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have hh := hpatch T hT hsmall
      have hcc : Cpatch ≤ c₀ := by dsimp [c₀]; linarith
      exact hh.trans (mul_le_mul_of_nonneg_right hcc (Real.exp_nonneg _))
    exact hprob.trans hunit

end SupercriticalLQGUniqueness.B2.DG20Pt
