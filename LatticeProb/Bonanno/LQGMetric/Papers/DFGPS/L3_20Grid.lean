/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_20Grid at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_19
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordsAux1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proofs of Lemma 3.20 (T:2327–2330)
and Lemma 3.22 (T:2375–2377): "… applied … with `2^{-k}ε` for `k ∈ ℕ₀` in place of `ε`, together
with a union bound over all `z ∈ B_{ε𝕣}(K) ∩ (2^{-k-2}ε𝕣ℤ²)` and then over all `k ∈ ℕ₀`."

`grid_union_bound`: at scale `t_k = ερ^k` there are `≤ ((2R/κ + 1)/t_k)²` grid points of mesh
`κ t_k 𝕣` in `B̄_{R𝕣}(0)` (LQGDimension `card_gridBox_le`); if each bad event has probability
`≤ t_k^{β+2}`, the union has probability `≤ (2R/κ+1)² Σ_k t_k^β = (2R/κ+1)²ε^β/(1 − ρ^β)`.
(The general ratio `ρ` and mesh factor `κ` replace the paper's `2^{-k}` and `2^{-k-2}`, see
`L3_20.lean`.)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace L320

open LQGDimension.LFPPRecords

/-- the grid indices `a` with `‖gridPt m a‖ ≤ ρ` -/
def gridSel (m ρ : ℝ) : Set (ℤ × ℤ) := {a | ‖gridPt m a‖ ≤ ρ}

theorem grid_union_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {ρ κ R β ε 𝕣 : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hκ : 0 < κ) (hR : 0 ≤ R) (hβ : 0 < β) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (h𝕣 : 0 < 𝕣) (B : ℕ → ℤ × ℤ → Set Ω)
    (hB : ∀ k a, a ∈ gridSel (κ * (ε * ρ ^ k) * 𝕣) (R * 𝕣) →
      P (B k a) ≤ ENNReal.ofReal ((ε * ρ ^ k) ^ (β + 2))) :
    P (⋃ k, ⋃ a ∈ gridSel (κ * (ε * ρ ^ k) * 𝕣) (R * 𝕣), B k a) ≤
      ENNReal.ofReal ((2 * R / κ + 1) ^ 2 / (1 - ρ ^ β) * ε ^ β) := by
  classical
  set A := (2 * R / κ + 1) ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hρβ0 : 0 < ρ ^ β := Real.rpow_pos_of_pos hρ0 _
  have hρβ1 : ρ ^ β < 1 := Real.rpow_lt_one hρ0.le hρ1 hβ
  -- one scale
  have hk : ∀ k : ℕ, P (⋃ a ∈ gridSel (κ * (ε * ρ ^ k) * 𝕣) (R * 𝕣), B k a) ≤
      ENNReal.ofReal (A * ε ^ β) * ENNReal.ofReal (ρ ^ β) ^ k := by
    intro k
    set t := ε * ρ ^ k with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by
      have : ρ ^ k ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
      nlinarith
    set m := κ * t * 𝕣 with hm
    have hm0 : 0 < m := by positivity
    set G := (gridBox m 0 (R * 𝕣)).filter fun a => ‖gridPt m a‖ ≤ R * 𝕣
    have hsub : (⋃ a ∈ gridSel m (R * 𝕣), B k a) ⊆ ⋃ a ∈ G, B k a := by
      intro ω hω
      simp only [mem_iUnion] at hω
      obtain ⟨a, ha, hω⟩ := hω
      refine mem_biUnion (x := a) (Finset.mem_filter.2 ⟨mem_gridBox hm0 ?_, ha⟩) hω
      rw [sub_zero]; exact ha
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
    have hterm : ∀ a ∈ G, P (B k a) ≤ ENNReal.ofReal (t ^ (β + 2)) :=
      fun a ha => hB k a (Finset.mem_filter.1 ha).2
    refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_pow hρβ0.le, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcard : (G.card : ℝ) ≤ A / t ^ 2 := by
      refine (Nat.cast_le.2 (Finset.card_filter_le _ _)).trans
        ((card_gridBox_le hm0 (by positivity) 0).trans ?_)
      have h8 : 2 * (R * 𝕣) / m = 2 * R / κ / t := by
        rw [hm]; field_simp
      rw [h8, hA, ← div_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      rw [add_div]
      gcongr
      exact (one_le_div ht0).2 ht1
    have hpow : t ^ (β + 2) = t ^ β * t ^ 2 := by
      rw [Real.rpow_add ht0, Real.rpow_two]
    have htβ : t ^ β = ε ^ β * (ρ ^ β) ^ k := by
      rw [ht, Real.mul_rpow hε0.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hρ0.le,
        mul_comm (k : ℝ) β, Real.rpow_mul hρ0.le, Real.rpow_natCast]
    have htp : 0 ≤ t ^ (β + 2) := (Real.rpow_pos_of_pos ht0 _).le
    calc (G.card : ℝ) * t ^ (β + 2) ≤ A / t ^ 2 * t ^ (β + 2) :=
          mul_le_mul_of_nonneg_right hcard htp
      _ = A * ε ^ β * (ρ ^ β) ^ k := by
          rw [hpow, htβ]; field_simp
  refine (measure_iUnion_le _).trans ?_
  refine (ENNReal.tsum_le_tsum hk).trans ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have h1 : (1 : ℝ≥0∞) - ENNReal.ofReal (ρ ^ β) = ENNReal.ofReal (1 - ρ ^ β) := by
    rw [ENNReal.ofReal_sub _ hρβ0.le, ENNReal.ofReal_one]
  rw [h1, ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

end L320
end LQGMetric.DFGPS
