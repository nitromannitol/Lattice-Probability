/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_3Chain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_3Tau
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_3Aux

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 4.3, Step 3: the excursion count for a chain (task P2-DFA10)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Proposition 4.3,
Step 3 (T:2710–2741), for given excursion data `τ_k ≤ σ_k ≤ τ_{k+1}` (`k < K`), `C`-good balls
`B_k = B_{ρ_k}(y_k)` with `P(τ_k) ∈ B̄_{ρ_k}(y_k)`, `P(σ_k) ∉ B_{2ρ_k}(y_k)`, and points
`q_k ∈ ∂B_k` with `D(0, q_k) ≤ s`:
* `step_tau`: `τ_k ≤ s + C (σ_k − τ_k)` (`eqn-C-good-cross` + `eqn-tau-upper`);
* `sum_le_tau`: `∑_{j<k} (σ_j − τ_j) ≤ τ_k − τ_0` (disjoint intervals);
* `chain_count`: with the ratio bound (`eqn-holder-cont-bdy`), `(1 + C⁻¹)^{K−2} ≤ C ε^{-A}`.
-/

noncomputable section

open Set Metric Finset
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace P43

open Blueprint

variable {D : ContMetric} {P : ℝ → ℂ} {L : ℝ} {x : ℂ}

/-- `τ ≤ s + C (σ − τ)` for one excursion (`eqn-C-good-cross`, `eqn-tau-upper`) -/
theorem step_tau (hP : IsGeodesicL D P L 0 x) {τ σ s C ρ : ℝ} {y q : ℂ} (hs : 0 ≤ s)
    (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) (hσL : σ ≤ L)
    (hin : ‖P τ - y‖ ≤ ρ) (hout : 2 * ρ ≤ ‖P σ - y‖) (hgood : CGood D C ρ y)
    (hq : q ∈ sphere y ρ) (hqs : D.1 (0, q) ≤ s) : τ ≤ s + C * (σ - τ) := by
  obtain ⟨t₁, t₂, h1, h12, h2, hu, hv⟩ := exists_cross_times hP hτ hτσ hσL hρ hin hout
  have hT := tau_upper hP ⟨by linarith, by linarith⟩ hgood hu hq hqs
  have hsd : setDist D (sphere y ρ) (sphere y (2 * ρ)) ≤ ENNReal.ofReal (t₂ - t₁) := by
    rw [L32.setDist_eq_iInf']
    refine (biInf_le _ hu).trans ((biInf_le _ hv).trans_eq ?_)
    rw [hP.2.2.2 t₁ ⟨by linarith, by linarith⟩ t₂ ⟨by linarith, by linarith⟩,
      abs_of_nonneg (by linarith)]
  have h3 : ENNReal.ofReal t₁ ≤ ENNReal.ofReal (s + C * (t₂ - t₁)) := by
    refine hT.trans ?_
    rw [ENNReal.ofReal_add hs (by nlinarith), ENNReal.ofReal_mul hC]
    gcongr
  rw [ENNReal.ofReal_le_ofReal_iff (by nlinarith)] at h3
  nlinarith

/-- disjoint excursion intervals: `∑_{j<k} (σ_j − τ_j) ≤ τ_k − τ_0` -/
theorem sum_le_tau (τ σ : ℕ → ℝ) {K : ℕ} (h : ∀ j, j + 1 < K → σ j ≤ τ (j + 1)) :
    ∀ k, k < K → ∑ j ∈ range k, (σ j - τ j) ≤ τ k - τ 0 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [sum_range_succ]
    have := ih (by omega)
    have := h n hn
    linarith

/-- **the excursion count** (T:2710–2741) for a chain of `K ≥ 2` excursions -/
theorem chain_count (hP : IsGeodesicL D P L 0 x) {s C ε A R 𝕣 : ℝ} (hs : 0 ≤ s) (hC : 0 < C)
    (hε : 0 < ε) {K : ℕ} (hK : 2 ≤ K) (τ σ ρ : ℕ → ℝ) (y q : ℕ → ℂ)
    (hτ0 : s ≤ τ 0) (hτσ : ∀ k, k < K → τ k ≤ σ k) (hσL : ∀ k, k < K → σ k ≤ L)
    (hστ : ∀ j, j + 1 < K → σ j ≤ τ (j + 1)) (hρ : ∀ k, k < K → ε * 𝕣 ≤ ρ k)
    (hin : ∀ k, k < K → ‖P (τ k) - y k‖ ≤ ρ k / 2)
    (hout : ∀ k, k < K → 2 * ρ k ≤ ‖P (σ k) - y k‖) (hgood : ∀ k, k < K → CGood D C (ρ k) (y k))
    (hq : ∀ k, k < K → q k ∈ sphere (y k) (ρ k)) (hqs : ∀ k, k < K → D.1 (0, q k) ≤ s)
    (hball : ∀ k, k < K → P (τ k) ∈ ball (0 : ℂ) R ∧ P (σ k) ∈ ball (0 : ℂ) R)
    (hratio : ∀ z ∈ ball (0 : ℂ) R, ∀ w ∈ ball (0 : ℂ) R, ε * 𝕣 ≤ ‖z - w‖ →
      ENNReal.ofReal (ε ^ A) * supDist D (ball 0 R) ≤ ENNReal.ofReal (D.1 (z, w)))
    (h𝕣 : 0 < 𝕣) :
    (1 + C⁻¹) ^ (K - 2) ≤ C * ε ^ (-A) := by
  have hdist : ∀ k, k < K → D.1 (P (τ k), P (σ k)) = σ k - τ k := fun k hk => by
    have h0 : 0 ≤ τ k := hs.trans (hτ0.trans (by
      have := sum_le_tau τ σ hστ k hk
      have hnn : 0 ≤ ∑ j ∈ range k, (σ j - τ j) :=
        sum_nonneg fun j hj => by have := hτσ j (by simp at hj; omega); linarith
      linarith))
    rw [hP.2.2.2 (τ k) ⟨h0, (hτσ k hk).trans (hσL k hk)⟩ (σ k)
      ⟨h0.trans (hτσ k hk), hσL k hk⟩, abs_of_nonneg (by linarith [hτσ k hk])]
  set xk : ℕ → ℝ := fun k => σ k - τ k with hxk
  have hρpos : ∀ k, k < K → 0 < ρ k := fun k hk => lt_of_lt_of_le (by positivity) (hρ k hk)
  have hτnn : ∀ k, k < K → 0 ≤ τ k := fun k hk => by
    have := sum_le_tau τ σ hστ k hk
    have hnn : 0 ≤ ∑ j ∈ range k, (σ j - τ j) :=
      sum_nonneg fun j hj => by have := hτσ j (by simp at hj; omega); linarith
    linarith
  -- (`eqn-C-good-cross`, `eqn-tau-upper`) and disjointness
  have hgrow : ∀ k, k < K → ∑ j ∈ range k, xk j ≤ C * xk k := by
    intro k hk
    have h1 := sum_le_tau τ σ hστ k hk
    have h2 := step_tau hP hs hC.le (hρpos k hk).le (hτnn k hk) (hτσ k hk) (hσL k hk)
      ((hin k hk).trans (by linarith [hρpos k hk])) (hout k hk) (hgood k hk) (hq k hk) (hqs k hk)
    simp only [hxk]
    linarith
  -- the ratio bound
  have hfar : ε * 𝕣 ≤ ‖P (τ 0) - P (σ 0)‖ := by
    have h0 : (0 : ℕ) < K := by omega
    have a1 := hin 0 h0
    have a2 := hout 0 h0
    have a3 : ‖P (σ 0) - y 0‖ ≤ ‖P (τ 0) - P (σ 0)‖ + ‖P (τ 0) - y 0‖ := by
      calc ‖P (σ 0) - y 0‖ = ‖(P (τ 0) - y 0) - (P (τ 0) - P (σ 0))‖ := by ring_nf
        _ ≤ ‖P (τ 0) - y 0‖ + ‖P (τ 0) - P (σ 0)‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    have := hρ 0 h0
    linarith [mul_pos hε h𝕣]
  have hK1 : K - 1 < K := by omega
  have hr0 := hratio _ (hball 0 (by omega)).1 _ (hball 0 (by omega)).2 hfar
  have hsup : ENNReal.ofReal (D.1 (P (τ (K - 1)), P (σ (K - 1)))) ≤ supDist D (ball 0 R) :=
    le_iSup₂_of_le (P (τ (K - 1))) (hball _ hK1).1
      (le_iSup₂_of_le (P (σ (K - 1))) (hball _ hK1).2 le_rfl)
  have hrat : ε ^ A * xk (K - 1) ≤ xk 0 := by
    have h := (mul_le_mul_of_nonneg_left hsup bot_le).trans hr0
    rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hε A).le, hdist _ hK1, hdist 0 (by omega),
      ENNReal.ofReal_le_ofReal_iff (by linarith [hτσ 0 (by omega)])] at h
    exact h
  have hx0 : 0 < xk 0 := by
    have h0 : (0 : ℕ) < K := by omega
    have := hdist 0 h0
    have hne : P (τ 0) ≠ P (σ 0) := by
      intro he; rw [he, sub_self, norm_zero] at hfar; nlinarith
    have hpos : 0 < D.1 (P (τ 0), P (σ 0)) := by
      rcases (ContMetric.nonneg D (P (τ 0)) (P (σ 0))).lt_or_eq with h | h
      · exact h
      · exact absurd (D.2.eq_of_eq_zero _ _ h.symm) hne
    simp only [hxk]; linarith
  exact excursion_count hC hε xk hK hx0 hgrow hrat

end P43
end LQGMetric.DFGPS
