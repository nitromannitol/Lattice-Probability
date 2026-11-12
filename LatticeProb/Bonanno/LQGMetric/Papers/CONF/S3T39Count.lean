/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39Count at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9: deterministic counting in Lemmas 3.10 and 3.11

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`
C:1641–1647 and 1690–1716. For a non-increasing sequence of arc counts `n_k` such that every
step `k < K` which is not bad halves the count ((3.27)):

* `t39_level_card_le`: if no `M` consecutive bad steps occur at counts in `[b, 2b)` after the
  entry into `[0, 2b)`, then at most `M` indices `k < K` have `n_k ∈ [b, 2b)`;
* `t39_sum_le`: if each dyadic level holds at most `M` indices and `n_k ≥ N` for `k < K`, then
  `∑_{k<K} n_k^{−θ} ≤ M (N/2)^{−θ}/(1 − 2^{−θ})` (C:1690–1716, (3.28)–(3.31), by dyadic levels:
  DV-CONF-T39a).
-/

namespace LQGMetric
namespace CONF

open Finset

/-- **CONF Lemma 3.10, deterministic part** (C:1641–1647, (3.27)) -/
theorem t39_level_card_le (n : ℕ → ℕ) (bad : ℕ → Prop) (K b M : ℕ)
    (hmono : ∀ k, n (k + 1) ≤ n k) (hstep : ∀ k < K, ¬ bad k → 2 * n (k + 1) ≤ n k)
    (hno : ¬ ∃ k₀, (n k₀ < 2 * b ∧ ∀ j < k₀, 2 * b ≤ n j) ∧
      ∀ i < M, b ≤ n (k₀ + i) ∧ bad (k₀ + i)) :
    ((range K).filter (fun k => b ≤ n k ∧ n k < 2 * b)).card ≤ M := by
  classical
  have hanti : Antitone n := antitone_nat_of_succ_le hmono
  set S := (range K).filter (fun k => b ≤ n k ∧ n k < 2 * b)
  by_contra hlt
  rw [not_le] at hlt
  have hne : S.Nonempty := by
    rw [← Finset.card_pos]; omega
  have hex : ∃ k, n k < 2 * b := by
    obtain ⟨k, hk⟩ := hne
    exact ⟨k, (Finset.mem_filter.1 hk).2.2⟩
  set k₀ := Nat.find hex
  have hk₀ : n k₀ < 2 * b := Nat.find_spec hex
  have hmin : ∀ j < k₀, 2 * b ≤ n j := fun j hj => not_lt.1 (Nat.find_min hex hj)
  set kmax := S.max' hne
  have hkmax : kmax ∈ S := S.max'_mem hne
  have hkmaxK : kmax < K := Finset.mem_range.1 (Finset.mem_filter.1 hkmax).1
  have hkmaxb : b ≤ n kmax := (Finset.mem_filter.1 hkmax).2.1
  have hsub : S ⊆ Finset.Icc k₀ kmax := by
    intro k hk
    refine Finset.mem_Icc.2 ⟨Nat.find_min' hex (Finset.mem_filter.1 hk).2.2, S.le_max' k hk⟩
  have hcard := (Finset.card_le_card hsub).trans_eq (Nat.card_Icc k₀ kmax)
  have hM : k₀ + M ≤ kmax := by omega
  refine hno ⟨k₀, ⟨hk₀, hmin⟩, fun i hi => ⟨?_, ?_⟩⟩
  · exact hkmaxb.trans (hanti (by omega))
  · by_contra hb
    have h1 := hstep (k₀ + i) (by omega) hb
    have h2 : b ≤ n (k₀ + i + 1) := hkmaxb.trans (hanti (by omega))
    have h3 : n (k₀ + i) ≤ n k₀ := hanti (by omega)
    omega

/-- `∑_{ℓ ∈ S} r^ℓ ≤ r^{ℓ₀}/(1 − r)` for `S ⊆ [ℓ₀, ∞)`, `0 ≤ r < 1` -/
theorem t39_geom_sum_le (S : Finset ℕ) (ℓ₀ : ℕ) (hS : ∀ ℓ ∈ S, ℓ₀ ≤ ℓ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) : ∑ ℓ ∈ S, r ^ ℓ ≤ r ^ ℓ₀ / (1 - r) := by
  have hinj : Set.InjOn (fun ℓ => ℓ - ℓ₀) S := by
    intro x hx y hy hxy
    have := hS x hx; have := hS y hy; simp only at hxy; omega
  calc ∑ ℓ ∈ S, r ^ ℓ = ∑ ℓ ∈ S, r ^ ℓ₀ * r ^ (ℓ - ℓ₀) := by
        refine Finset.sum_congr rfl fun ℓ hℓ => ?_
        rw [← pow_add, Nat.add_sub_cancel' (hS ℓ hℓ)]
    _ = r ^ ℓ₀ * ∑ j ∈ S.image (fun ℓ => ℓ - ℓ₀), r ^ j := by
        rw [Finset.mul_sum, Finset.sum_image hinj]
    _ ≤ r ^ ℓ₀ * ∑' j : ℕ, r ^ j := by
        gcongr
        exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ fun j _ => pow_nonneg hr0 j
    _ = r ^ ℓ₀ / (1 - r) := by rw [tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

/-- **CONF Lemma 3.11, steps 2–3, deterministic part** (C:1690–1716): if `n_k ≥ N ≥ 1` for
`k < K` and each dyadic level `[2^ℓ, 2^{ℓ+1})` contains `n_k` for at most `M` indices `k < K`,
then `∑_{k<K} n_k^{−θ} ≤ M (N/2)^{−θ}/(1 − 2^{−θ})`. -/
theorem t39_sum_le (n : ℕ → ℕ) (K N M : ℕ) {θ : ℝ} (hθ : 0 < θ) (hN : 1 ≤ N)
    (hK : ∀ k < K, N ≤ n k)
    (hcard : ∀ ℓ, ((range K).filter (fun k => 2 ^ ℓ ≤ n k ∧ n k < 2 * 2 ^ ℓ)).card ≤ M) :
    ∑ k ∈ range K, ((n k : ℝ) ^ (-θ)) ≤ M * ((N : ℝ) / 2) ^ (-θ) / (1 - (2 : ℝ) ^ (-θ)) := by
  classical
  set g : ℕ → ℕ := fun k => Nat.log 2 (n k)
  set r : ℝ := (2 : ℝ) ^ (-θ)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set ℓ₀ := Nat.log 2 N
  have hNpos : 0 < N := hN
  -- each index of the level `ℓ = log₂ n_k` contributes at most `r^ℓ`
  have hterm : ∀ k < K, (n k : ℝ) ^ (-θ) ≤ r ^ g k := by
    intro k hk
    have hnk : n k ≠ 0 := by have := hK k hk; omega
    have h1 : ((2 : ℝ) ^ g k) ≤ n k := by exact_mod_cast Nat.pow_log_le_self 2 hnk
    calc (n k : ℝ) ^ (-θ) ≤ ((2 : ℝ) ^ g k) ^ (-θ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
      _ = r ^ g k := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
            Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hfib : ∀ ℓ, ((range K).filter (fun k => g k = ℓ)) ⊆
      (range K).filter (fun k => 2 ^ ℓ ≤ n k ∧ n k < 2 * 2 ^ ℓ) := by
    intro ℓ k hk
    obtain ⟨hkK, rfl⟩ := Finset.mem_filter.1 hk
    have hnk : n k ≠ 0 := by have := hK k (Finset.mem_range.1 hkK); omega
    refine Finset.mem_filter.2 ⟨hkK, Nat.pow_log_le_self 2 hnk, ?_⟩
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n k)
    rw [pow_succ] at this; simpa [g, mul_comm] using this
  have hℓ₀ : ∀ ℓ ∈ (range K).image g, ℓ₀ ≤ ℓ := by
    intro ℓ hℓ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hℓ
    exact Nat.log_mono_right (hK k (Finset.mem_range.1 hk))
  have hr₀ : r ^ ℓ₀ ≤ ((N : ℝ) / 2) ^ (-θ) := by
    have h2 : (N : ℝ) / 2 ≤ 2 ^ ℓ₀ := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
      rw [pow_succ] at this
      have : (N : ℝ) < 2 ^ ℓ₀ * 2 := by exact_mod_cast this
      linarith
    calc r ^ ℓ₀ = ((2 : ℝ) ^ ℓ₀) ^ (-θ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
            Real.rpow_mul (by norm_num), Real.rpow_natCast]
      _ ≤ ((N : ℝ) / 2) ^ (-θ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
  calc ∑ k ∈ range K, ((n k : ℝ) ^ (-θ))
      = ∑ ℓ ∈ (range K).image g, ∑ k ∈ (range K).filter (fun k => g k = ℓ), (n k : ℝ) ^ (-θ) :=
        (Finset.sum_fiberwise_of_maps_to (fun k hk => Finset.mem_image_of_mem g hk) _).symm
    _ ≤ ∑ ℓ ∈ (range K).image g, (M : ℝ) * r ^ ℓ := by
        refine Finset.sum_le_sum fun ℓ _ => ?_
        calc ∑ k ∈ (range K).filter (fun k => g k = ℓ), (n k : ℝ) ^ (-θ)
            ≤ ∑ k ∈ (range K).filter (fun k => g k = ℓ), r ^ ℓ := by
              refine Finset.sum_le_sum fun k hk => ?_
              obtain ⟨hkK, rfl⟩ := Finset.mem_filter.1 hk
              exact hterm k (Finset.mem_range.1 hkK)
          _ = ((range K).filter (fun k => g k = ℓ)).card * r ^ ℓ := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (M : ℝ) * r ^ ℓ := by
              gcongr
              exact_mod_cast (Finset.card_le_card (hfib ℓ)).trans (hcard ℓ)
    _ = M * ∑ ℓ ∈ (range K).image g, r ^ ℓ := by rw [Finset.mul_sum]
    _ ≤ M * (r ^ ℓ₀ / (1 - r)) := by
        gcongr; exact t39_geom_sum_le _ ℓ₀ hℓ₀ hr0 hr1
    _ ≤ M * (((N : ℝ) / 2) ^ (-θ) / (1 - r)) := by
        gcongr
    _ = M * ((N : ℝ) / 2) ^ (-θ) / (1 - (2 : ℝ) ^ (-θ)) := by ring

end CONF
end LQGMetric
