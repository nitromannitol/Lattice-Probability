/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39G2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412Step12

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 3.11, Step 1: the Hölder bound on `s_{k+1} − s_k`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`
C:1676–1689 (with (3.22), C:1609–1615): on `𝓔_𝕣(a)`, for `k ≤ K_{N₀} − 1`,
`R^{ε_k}_𝕣(𝓑^•_{s_k}) ≤ (ε_k + 6ε_k^{1/2})𝕣` (condition 4 of `𝓔_𝕣(a)`) and, by the Hölder
condition 3, `s_{k+1} = σ^{ε_k}_{s_k,𝕣} ≤ s_k + (ε_k + 6ε_k^{1/2})^χ 𝔠_𝕣e^{ξh_𝕣(0)}`.

We use the slightly larger radius `7ε^{1/2}𝕣 ≥ (ε + 6ε^{1/2})𝕣` (as GM l. 2142–2144 do in the
same argument; `GM.p412_confRK_le`, `GM.p412_enbhd_subset` are reused verbatim):

* `t39g_confRK_le`: condition 4 of `confReg` gives `R^ε_𝕣(K) ≤ 7ε^{1/2}𝕣` for dyadic `ε ≤ a`,
  `K ⊆ B_{3𝕣}(𝕫)`;
* `t39g_confSigma_le`: `σ^ε_{s,𝕣} ≤ s + (7ε^{1/2})^χ S` when `𝓑^•_s ⊆ B_{3𝕣}(𝕫)`,
  `7ε^{1/2} ≤ a ≤ 1`;
* `t39gExp n = ⌊log₂ n⌋/4`: `ε_k = 2^{−t39gExp n_k}` is CONF's smallest dyadic `≥ n_k^{−1/4}`
  ((3.19), C:1563), with `n^{−1/4} ≤ ε < 2n^{−1/4}` (`t39gExp_bounds`).
-/

noncomputable section

open MeasureTheory Set Metric
open LQGMetric.Blueprint LQGMetric.GM

namespace LQGMetric
namespace CONF

section Step1
variable {Ω : Type} [MeasurableSpace Ω] {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric}
  {P : Measure Ω} {h : Ω → DistC} {p : CONFParams} {χ : ℝ} {z₀ : ℂ} {R a : ℝ} {ω : Ω}

/-- **(3.22)** (C:1609–1615) from condition 4 of `confReg`: `R^ε_𝕣(K) ≤ 7ε^{1/2}𝕣` for a dyadic
`ε = 2^{−m} ≤ a` and `K ⊆ B_{3𝕣}(𝕫)` -/
theorem t39g_confRK_le (hω : ω ∈ confReg ξ cc D P h p χ z₀ R a) (hR : 0 < R) {m : ℕ}
    (hm : (2 : ℝ)⁻¹ ^ m ≤ a) {K : Set ℂ} (hK : K ⊆ ball z₀ (3 * R)) :
    confRK ξ cc D P h p R ((2 : ℝ)⁻¹ ^ m) K ω ≤
      ENNReal.ofReal (7 * ((2 : ℝ)⁻¹ ^ m) ^ (1 / 2 : ℝ) * R) := by
  set δ : ℝ := (2 : ℝ)⁻¹ ^ m with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hsq : δ ≤ δ ^ (1 / 2 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have hsup : (⨆ z ∈ gridPts (δ * R / 4) ∩ thickening (δ * R) K,
      confRho ξ cc D P h p (δ * R) z (confN p δ) ω) ≤
      ENNReal.ofReal (δ ^ (1 / 2 : ℝ) * R) := by
    refine iSup₂_le fun z hz => ?_
    refine hω.2.2.2 m hm z ⟨hz.1, ?_⟩
    obtain ⟨y, hy, hzy⟩ := mem_thickening_iff.1 hz.2
    have hy3 := mem_ball.1 (hK hy)
    rw [mem_ball]
    calc dist z z₀ ≤ dist z y + dist y z₀ := dist_triangle _ _ _
      _ < δ * R + 3 * R := add_lt_add hzy hy3
      _ ≤ 4 * R := by nlinarith
  have hpos : 0 ≤ δ ^ (1 / 2 : ℝ) * R := by positivity
  calc confRK ξ cc D P h p R δ K ω
      ≤ 6 * ENNReal.ofReal (δ ^ (1 / 2 : ℝ) * R) + ENNReal.ofReal (δ * R) := by
        unfold confRK; gcongr
    _ = ENNReal.ofReal (6 * (δ ^ (1 / 2 : ℝ) * R) + δ * R) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (7 * δ ^ (1 / 2 : ℝ) * R) := by
        apply ENNReal.ofReal_le_ofReal; nlinarith

/-- **CONF L3.11 Step 1** (C:1676–1689): on `𝓔_𝕣(a)`, if `𝓑^•_s ⊆ B_{3𝕣}(𝕫)` and `ε = 2^{−m}`
with `7ε^{1/2} ≤ a ≤ 1`, then `σ^ε_{s,𝕣} ≤ s + (7ε^{1/2})^χ 𝔠_𝕣e^{ξh_𝕣(𝕫)}` -/
theorem t39g_confSigma_le (hω : ω ∈ confReg ξ cc D P h p χ z₀ R a) (hR : 0 < R) (hχ : 0 < χ)
    (hS : 0 < scaleFac ξ cc (h ω) R z₀) {m : ℕ} (hm : 7 * ((2 : ℝ)⁻¹ ^ m) ^ (1 / 2 : ℝ) ≤ a)
    (ha1 : a ≤ 1) {s : ℝ} (hs : 0 ≤ s) (hK : filledBall (D (h ω)) z₀ s ⊆ ball z₀ (3 * R)) :
    confSigma ξ cc D P h p z₀ R ((2 : ℝ)⁻¹ ^ m) s ω ≤
      ENNReal.ofReal (s + (7 * ((2 : ℝ)⁻¹ ^ m) ^ (1 / 2 : ℝ)) ^ χ * scaleFac ξ cc (h ω) R z₀) := by
  set δ : ℝ := (2 : ℝ)⁻¹ ^ m with hδ
  set S := scaleFac ξ cc (h ω) R z₀
  set ρ := 7 * δ ^ (1 / 2 : ℝ) * R with hρ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hsq : δ ≤ δ ^ (1 / 2 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have hρR : ρ / R = 7 * δ ^ (1 / 2 : ℝ) := by rw [hρ]; field_simp
  have hρle : ρ ≤ R := by rw [hρ]; nlinarith
  have hbd : Bornology.IsBounded (ballM (D (h ω)) z₀ s) :=
    isBounded_ball.subset fun w hw => hK (by unfold filledBall; exact Or.inl (subset_closure hw))
  have hRK := t39g_confRK_le hω hR (hsq.trans (by linarith [Real.rpow_nonneg hδ0.le (1 / 2 : ℝ)]))
    hK
  have hB0 : 0 ≤ (ρ / R) ^ χ * S := by positivity
  have hHol : ∀ u ∈ frontier (filledBall (D (h ω)) z₀ s), ∀ x, x ∉ filledBall (D (h ω)) z₀ s →
      ‖u - x‖ < ρ → (D (h ω)).1 (u, x) ≤ (ρ / R) ^ χ * S := by
    intro u hu x _ hux
    have huK : u ∈ filledBall (D (h ω)) z₀ s := (jb_isClosed_filledBall hbd).frontier_subset hu
    have hu3 := mem_ball.1 (hK huK)
    have hx4 : x ∈ ball z₀ (4 * R) := by
      rw [mem_ball]
      calc dist x z₀ ≤ dist x u + dist u z₀ := dist_triangle _ _ _
        _ < ρ + 3 * R := by
          rw [dist_comm, dist_eq_norm]; exact add_lt_add hux hu3
        _ ≤ 4 * R := by linarith
    have hu4 : u ∈ ball z₀ (4 * R) := mem_ball.2 (hu3.trans (by linarith))
    have hlt : ‖u - x‖ / R ≤ ρ / R := div_le_div_of_nonneg_right hux.le hR.le
    have h3 := hω.2.2.1 u hu4 x hx4 (hlt.trans (by rw [hρR]; exact hm))
    have h4 : (‖u - x‖ / R) ^ χ ≤ (ρ / R) ^ χ :=
      Real.rpow_le_rpow (by positivity) hlt hχ.le
    have := (inv_mul_le_iff₀ hS).1 (h3.trans h4)
    linarith [mul_comm S ((ρ / R) ^ χ)]
  have hmain : ∀ s', s + (ρ / R) ^ χ * S < s' →
      confSigma ξ cc D P h p z₀ R δ s ω ≤ ENNReal.ofReal s' := by
    intro s' hs'
    have hsub := p412_enbhd_subset hbd hB0 hHol hs'
    unfold confSigma
    refine iInf_le_of_le s' (iInf_le_of_le (by linarith) (iInf_le_of_le ?_ le_rfl))
    exact fun x hx => hsub (show x ∈ enbhd _ _ from lt_of_lt_of_le hx hRK)
  rw [← hρR]
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have h1 := hmain (s + (ρ / R) ^ χ * S + η) (by have : (0 : ℝ) < η := hη; linarith)
  rwa [ENNReal.ofReal_add (by positivity) η.coe_nonneg, ENNReal.ofReal_coe_nnreal] at h1

end Step1

/-! ## The dyadic `ε_k` of (3.19) -/

/-- `⌊log₂ n⌋ / 4`: `2^{−t39gExp n}` is the smallest dyadic `≥ n^{−1/4}` (CONF (3.19), C:1563) -/
def t39gExp (n : ℕ) : ℕ := Nat.log 2 n / 4

/-- `2^{4m} ≤ n < 2^{4(m+1)}` for `m = t39gExp n`, `n ≥ 1` -/
theorem t39gExp_pow_bounds {n : ℕ} (hn : 1 ≤ n) :
    2 ^ (4 * t39gExp n) ≤ n ∧ n < 2 ^ (4 * (t39gExp n + 1)) := by
  have h1 : 2 ^ (Nat.log 2 n) ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  unfold t39gExp
  constructor
  · exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans h1
  · exact h2.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **(3.19)**: `n^{−1/4} ≤ ε < 2n^{−1/4}` for `ε = 2^{−t39gExp n}`, `n ≥ 1` -/
theorem t39gExp_bounds {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (2 : ℝ)⁻¹ ^ t39gExp n ∧
      (2 : ℝ)⁻¹ ^ t39gExp n ≤ 2 * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨h1, h2⟩ := t39gExp_pow_bounds hn
  set m := t39gExp n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- `x := 2^m`, `x^4 ≤ n < 16 x^4`
  have h1' : ((2 : ℝ) ^ m) ^ (4 : ℕ) ≤ n := by
    rw [← pow_mul, mul_comm]; exact_mod_cast h1
  have h2' : (n : ℝ) < 16 * ((2 : ℝ) ^ m) ^ (4 : ℕ) := by
    rw [← pow_mul, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_add]
    have : (n : ℝ) < (2 : ℝ) ^ (4 * (m + 1)) := by exact_mod_cast h2
    rwa [show 4 * (m + 1) = 4 + m * 4 by ring] at this
  have hx0 : (0 : ℝ) < 2 ^ m := by positivity
  have hq : (n : ℝ) ^ (-(1 / 4 : ℝ)) = ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹ := Real.rpow_neg hn0.le _
  have hinv : (2 : ℝ)⁻¹ ^ m = ((2 : ℝ) ^ m)⁻¹ := inv_pow _ _
  -- `n^{1/4}` versus `2^m`
  have hr : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hr0 : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hA : (2 : ℝ) ^ m ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    by_contra hc; push Not at hc
    have := pow_lt_pow_left₀ hc hr0.le (by norm_num : (4 : ℕ) ≠ 0)
    rw [hr] at this; linarith
  have hB : (n : ℝ) ^ (1 / 4 : ℝ) < 2 * 2 ^ m := by
    by_contra hc; push Not at hc
    have := pow_le_pow_left₀ (by positivity) hc 4
    rw [hr, mul_pow] at this; norm_num at this; linarith
  rw [hq, hinv]
  constructor
  · exact inv_anti₀ hx0 hA
  · rw [← div_eq_mul_inv, le_div_iff₀ hr0]
    calc ((2 : ℝ) ^ m)⁻¹ * (n : ℝ) ^ (1 / 4 : ℝ) ≤ ((2 : ℝ) ^ m)⁻¹ * (2 * 2 ^ m) :=
          mul_le_mul_of_nonneg_left hB.le (by positivity)
      _ = 2 := by field_simp

end CONF
end LQGMetric
