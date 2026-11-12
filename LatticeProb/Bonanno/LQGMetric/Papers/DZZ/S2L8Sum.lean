/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L8Sum at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L8

/-!
# DZZ Lemma 2.8, the sum over scales on `𝕍^ξ` (task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 603–609 ("following the derivation
as in Lemma 2.7"): `dzz_lemma28_sum` applies the probabilistic core `dzz_sum_sup_tail` to continuous
versions of `Δ_i = √π W(hatDeltaKernel i ·)` on `𝕍^ξ = [ξ, 1 − ξ]²` (`ferniqueBox ⟨ξ, ξ⟩ (1 − 2ξ)`),
with the bounds `sq_norm_hatDeltaKernel_le`, `sq_norm_hatDeltaKernel_sub_le` (the latter assumes
`BridgeShellBound`). `exists_continuous_hatDelta`: continuous versions exist.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail

lemma ball_subset_openSquare_of_mem {ξ : ℝ} (hξ : 0 < ξ) {v : ℂ}
    (hv : v ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ)) : Metric.ball v ξ ⊆ openSquare := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hv
  simp only at h1 h2 h3 h4
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have hre := (Complex.abs_re_le_norm (y - v)).trans_lt hy
  have him := (Complex.abs_im_le_norm (y - v)).trans_lt hy
  rw [Complex.sub_re, abs_lt] at hre
  rw [Complex.sub_im, abs_lt] at him
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

universe u

/-- **DZZ Lemma 2.8, the sum over scales** (l. 603–609), assuming `BridgeShellBound`. -/
theorem dzz_lemma28_sum {C₀ : ℝ} (hC0 : 0 ≤ C₀) (hC : BridgeShellBound C₀) {ξ : ℝ} (hξ : 0 < ξ)
    (hξ2 : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ Y : ℕ → ℂ → Ω → ℝ,
      (∀ i ω, Continuous fun x => Y i x ω) →
      (∀ i x, Y i x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (hatDeltaKernel i x) ω) →
      ∀ lam : ℝ, 0 ≤ lam →
        P.real {ω | ∃ v ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ), ∃ n : ℕ,
          lam ≤ ∑ i ∈ Finset.range n, |Y i v ω|} ≤ C * Real.exp (-lam ^ 2 / C) := by
  set K := max 4 (2 * Real.log 4 / rhoXi ξ)
  set K₂ := 2 * (Real.sqrt 2 + 4 * (13 + C₀))
  set K' := max K K₂
  have hK'0 : 0 < K' := lt_max_of_lt_left (lt_max_of_lt_left (by norm_num))
  obtain ⟨C, hCpos, hsum⟩ := dzz_sum_sup_tail (K := K') hK'0 (rhoXi_pos ξ) (rhoXi_lt_one hξ)
  refine ⟨C, hCpos, fun {Ω} _ {P} {W} hW Y hYc hY lam hlam => ?_⟩
  refine hsum Ω P ⟨ξ, ξ⟩ (1 - 2 * ξ) (by linarith) (by linarith) Y (fun i => ?_) (fun i v => ?_)
    (fun i ω => ?_) (fun i v hv => ?_) (fun i u _ v _ => ?_) lam hlam
  · exact (isGaussianProcess_sqrtPi hW (hatDeltaKernel i)).congr fun x => (hY i x).symm
  · rw [integral_congr_ae (hY i v)]; exact integral_sqrtPi hW _
  · exact (hYc i ω).continuousOn
  · rw [variance_congr (hY i v), variance_sqrtPi hW]
    exact (sq_norm_hatDeltaKernel_le hW hξ (ball_subset_openSquare_of_mem hξ hv) i).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (rhoXi_pos ξ).le _))
  · have hae : (fun ω => (Y i v ω - Y i u ω) ^ 2) =ᵐ[P] fun ω =>
        (Real.sqrt Real.pi * W (hatDeltaKernel i v) ω -
          Real.sqrt Real.pi * W (hatDeltaKernel i u) ω) ^ 2 := by
      filter_upwards [hY i u, hY i v] with ω h1 h2; rw [h1, h2]
    rw [integral_congr_ae hae, integral_sq_sqrtPi_sub hW]
    have h := sq_norm_hatDeltaKernel_sub_le hC0 hC hW i v u
    rw [norm_sub_rev v u] at h
    refine h.trans ?_
    gcongr
    exact le_max_right _ _

/-- Continuous versions of the `Δ_i` of Lemma 2.8 exist (assuming `BridgeShellBound`). -/
theorem exists_continuous_hatDelta {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} {C₀ : ℝ} (hC0 : 0 ≤ C₀) (hC : BridgeShellBound C₀)
    (hW : IsWhiteNoise P W) :
    ∃ Y : ℕ → ℂ → Ω → ℝ, (∀ i ω, Continuous fun x => Y i x ω) ∧ (∀ i x, Measurable (Y i x)) ∧
      ∀ i x, Y i x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (hatDeltaKernel i x) ω := by
  have hpi := Real.pi_pos
  have h : ∀ i : ℕ, ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧
      (∀ x, Measurable (Y x)) ∧ ∀ x, (fun ω => Y x ω) =ᵐ[P]
        fun ω => Real.sqrt Real.pi * W (hatDeltaKernel i x) ω := fun i =>
    exists_continuous_modification_of_kernel_half hW (hatDeltaKernel i)
      (K := 2 * (Real.sqrt 2 + 4 * (13 + C₀)) * 2 ^ i / Real.pi) (by positivity)
      (fun x x' => by
        have := sq_norm_hatDeltaKernel_sub_le hC0 hC hW i x x'
        rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
        linarith) _
  choose Y hYc hYm hYe using h
  exact ⟨Y, hYc, hYm, hYe⟩

end DZZ
end LQGMetric
