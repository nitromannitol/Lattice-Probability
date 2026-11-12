/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_3FData at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_3FTop
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_3Cover

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 4.3 for filled balls: chain length bounds (task P2-DFA10b)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Proposition 4.3,
Step 3 (T:2710–2741): the number of `4ε^{1−ζ}𝕣`-separated times (a chain, `P43.IsChain`) at
which the geodesic is near `∂𝓑^•_s` is at most `nB C ε A = ⌊log(C ε^{-A}) / log(1 + C⁻¹)⌋ + 3`,
separately for times `≥ s` (`chain_bound_fwd`, the paper's argument) and times `≤ s`
(`chain_bound_back`, its mirror image, D68). The data (good ball `B_{ρ_t}(y_t) ∋ P(t)` and boundary
points `q_t`, `q'_t`) is supplied as functions of the time `t`.
-/

noncomputable section

open Set Metric Finset
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace P43

open Blueprint

/-- the bound on the number of excursions (T:2741) -/
def nB (C ε A : ℝ) : ℕ := ⌊Real.log (C * ε ^ (-A)) / Real.log (1 + C⁻¹)⌋₊ + 3

lemma le_nB {C ε A : ℝ} (hC : 0 < C) (hε : 0 < ε) {n : ℕ} (hn : 3 ≤ n)
    (h : (1 + C⁻¹) ^ (n - 3) ≤ C * ε ^ (-A)) : n ≤ nB C ε A := by
  have hb : 0 < Real.log (1 + C⁻¹) := Real.log_pos (by have := inv_pos.2 hC; linarith)
  have hX : 0 < C * ε ^ (-A) := mul_pos hC (Real.rpow_pos_of_pos hε _)
  have h1 := Real.log_le_log (by positivity) h
  rw [Real.log_pow] at h1
  have h2 : ((n - 3 : ℕ) : ℝ) ≤ Real.log (C * ε ^ (-A)) / Real.log (1 + C⁻¹) := by
    rw [le_div_iff₀ hb]; exact h1
  have h3 := Nat.le_floor h2
  unfold nB; omega

variable {Dg : ContMetric} {G : ℝ → ℂ} {L : ℝ} {w : ℂ}

/-- the data at a time `t` near the boundary (forward direction) -/
def DataF (Dg : ContMetric) (G : ℝ → ℂ) (C ε 𝕣 ζ R s : ℝ) (t : ℝ) (y : ℂ) (ρ : ℝ) (q : ℂ) :
    Prop :=
  4 * ε * 𝕣 ≤ ρ ∧ ρ ≤ ε ^ (1 - ζ) * 𝕣 ∧ CGood Dg C ρ y ∧ ‖G t - y‖ < ρ / 2 ∧
    q ∈ sphere y ρ ∧ Dg.1 (0, q) ≤ s ∧ G t ∈ ball (0 : ℂ) R

/-- the data at a time `t` near the boundary (backward direction) -/
def DataB (Dg : ContMetric) (G : ℝ → ℂ) (C ε 𝕣 ζ R s : ℝ) (t : ℝ) (y : ℂ) (ρ : ℝ) (q : ℂ) :
    Prop :=
  4 * ε * 𝕣 ≤ ρ ∧ ρ ≤ ε ^ (1 - ζ) * 𝕣 ∧ CGood Dg C ρ y ∧ ‖G t - y‖ < ρ / 2 ∧
    q ∈ sphere y ρ ∧ s ≤ Dg.1 (0, q) ∧ G t ∈ ball (0 : ℂ) R

/-- separation of consecutive chain times pushes `P(τ_{k+1})` out of `2B_k` -/
lemma out_of_sep {a b y : ℂ} {ρ r : ℝ} (hρ : ρ ≤ r) (hsep : 4 * r ≤ ‖b - a‖)
    (hin : ‖a - y‖ < ρ / 2) (hρ0 : 0 ≤ ρ) : 2 * ρ ≤ ‖b - y‖ := by
  have : ‖b - a‖ ≤ ‖b - y‖ + ‖a - y‖ := by
    calc ‖b - a‖ = ‖(b - y) - (a - y)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  linarith

/-- **chain bound, times `≥ s`** (T:2710–2741) -/
theorem chain_bound_fwd (hG : IsGeodesicL Dg G L 0 w) {T : Set ℝ} (hT : T ⊆ Icc 0 L)
    {s C ε A 𝕣 ζ R : ℝ} (hs : 0 ≤ s) (hC : 0 < C) (hε : 0 < ε) (h𝕣 : 0 < 𝕣)
    (yf : ℝ → ℂ) (ρf : ℝ → ℝ) (qf : ℝ → ℂ)
    (hd : ∀ t ∈ T, DataF Dg G C ε 𝕣 ζ R s t (yf t) (ρf t) (qf t))
    (hratio : ∀ z ∈ ball (0 : ℂ) R, ∀ w ∈ ball (0 : ℂ) R, ε * 𝕣 ≤ ‖z - w‖ →
      ENNReal.ofReal (ε ^ A) * supDist Dg (ball 0 R) ≤ ENNReal.ofReal (Dg.1 (z, w)))
    {S : Finset ℝ} (hS : ↑S ⊆ T ∩ Ici s) (hch : IsChain G (4 * (ε ^ (1 - ζ) * 𝕣)) S) :
    S.card ≤ nB C ε A := by
  set n := S.card with hn
  by_cases h3 : n < 3
  · unfold nB; omega
  push Not at h3
  set τ : ℕ → ℝ := fun k => chainSeq S k
  have hmem : ∀ k, k < n → τ k ∈ T ∧ s ≤ τ k := fun k hk => hS (chainSeq_mem hk)
  have hD : ∀ k, k < n → DataF Dg G C ε 𝕣 ζ R s (τ k) (yf (τ k)) (ρf (τ k)) (qf (τ k)) :=
    fun k hk => hd _ (hmem k hk).1
  have hcc := chain_count hG hs hC hε (K := n - 1) (by omega) τ (fun k => τ (k + 1))
    (fun k => ρf (τ k)) (fun k => yf (τ k)) (fun k => qf (τ k)) (hmem 0 (by omega)).2
    (fun k hk => (chainSeq_lt (Nat.lt_succ_self k) (by omega)).le)
    (fun k hk => (hT (hmem (k + 1) (by omega)).1).2) (fun j _ => le_rfl)
    (fun k hk => by have := (hD k (by omega)).1; nlinarith)
    (fun k hk => (hD k (by omega)).2.2.2.1.le)
    (fun k hk => by
      have hk' := hD k (by omega)
      have hρ0 : 0 ≤ ρf (τ k) := by have := hk'.1; nlinarith
      exact out_of_sep hk'.2.1 (hch.seq_sep (by omega)) hk'.2.2.2.1 hρ0)
    (fun k hk => (hD k (by omega)).2.2.1) (fun k hk => (hD k (by omega)).2.2.2.2.1)
    (fun k hk => (hD k (by omega)).2.2.2.2.2.1)
    (fun k hk => ⟨(hD k (by omega)).2.2.2.2.2.2, (hD (k + 1) (by omega)).2.2.2.2.2.2⟩)
    hratio h𝕣
  exact le_nB hC hε h3 (by rw [show n - 3 = n - 1 - 2 by omega]; exact hcc)

/-- **chain bound, times `≤ s`** (mirror image, D68) -/
theorem chain_bound_back (hG : IsGeodesicL Dg G L 0 w) {T : Set ℝ} (hT : T ⊆ Icc 0 L)
    {s C ε A 𝕣 ζ R : ℝ} (hC : 0 < C) (hε : 0 < ε) (h𝕣 : 0 < 𝕣)
    (yf : ℝ → ℂ) (ρf : ℝ → ℝ) (qf : ℝ → ℂ)
    (hd : ∀ t ∈ T, DataB Dg G C ε 𝕣 ζ R s t (yf t) (ρf t) (qf t))
    (hratio : ∀ z ∈ ball (0 : ℂ) R, ∀ w ∈ ball (0 : ℂ) R, ε * 𝕣 ≤ ‖z - w‖ →
      ENNReal.ofReal (ε ^ A) * supDist Dg (ball 0 R) ≤ ENNReal.ofReal (Dg.1 (z, w)))
    {S : Finset ℝ} (hS : ↑S ⊆ T ∩ Iic s) (hch : IsChain G (4 * (ε ^ (1 - ζ) * 𝕣)) S) :
    S.card ≤ nB C ε A := by
  set n := S.card with hn
  by_cases h3 : n < 3
  · unfold nB; omega
  push Not at h3
  set v : ℕ → ℝ := fun k => chainSeq S (n - 1 - k)
  have hmem : ∀ k, k < n → v k ∈ T ∧ v k ≤ s := fun k hk => hS (chainSeq_mem (by omega))
  have hD : ∀ k, k < n → DataB Dg G C ε 𝕣 ζ R s (v k) (yf (v k)) (ρf (v k)) (qf (v k)) :=
    fun k hk => hd _ (hmem k hk).1
  have hcc := chain_count_back hG hC hε (K := n - 1) (by omega) v
    (fun k => ρf (v k)) (fun k => yf (v k)) (fun k => qf (v k)) (hmem 0 (by omega)).2
    (hT (hmem (n - 1) (by omega)).1).1 (hT (hmem 0 (by omega)).1).2
    (fun k hk => (chainSeq_lt (by omega) (by omega)).le)
    (fun k hk => by have := (hD k (by omega)).1; nlinarith)
    (fun k hk => by
      have hk' := hD k (by omega)
      have := hk'.1
      linarith [hk'.2.2.2.1, show 0 ≤ ρf (v k) by nlinarith])
    (fun k hk => by
      have hk' := hD k (by omega)
      have hρ0 : 0 ≤ ρf (v k) := by have := hk'.1; nlinarith
      have hsep := hch.seq_sep (k := n - 1 - (k + 1)) (by omega)
      rw [show n - 1 - (k + 1) + 1 = n - 1 - k by omega] at hsep
      rw [← norm_neg, neg_sub] at hsep
      have := out_of_sep hk'.2.1 (b := G (v (k + 1))) (by
        rw [norm_sub_rev]; simpa [v, norm_sub_rev] using hsep) hk'.2.2.2.1 hρ0
      exact this)
    (fun k hk => (hD k (by omega)).2.2.1) (fun k hk => (hD k (by omega)).2.2.2.2.1)
    (fun k hk => (hD k (by omega)).2.2.2.2.2.1)
    (fun k hk => (hD k (by omega)).2.2.2.2.2.2)
    hratio h𝕣
  exact le_nB hC hε h3 (by rw [show n - 3 = n - 1 - 2 by omega]; exact hcc)

end P43
end LQGMetric.DFGPS
