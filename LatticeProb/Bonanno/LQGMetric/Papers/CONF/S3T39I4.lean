/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39I4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39H3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39I2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9: `T39IterData'` from Lemma 3.7 (D119 S5)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1595–1617. Copy-and-adapt of `t39h_iterData_of` (S3T39H4) for the almost sure recursion of
`T39IterData'`: the recursion `s_{k+1} = σ^{ε_k}_{s_k,𝕣}` is assumed on events
`Cs k ∈ σ(𝓑^•_{s_{k+1}}, h| mod const)` of full measure (`hCs`, `hCsm`, `hCsae`; on `Cs k` the
trace lemma `t39h_inter_localSigma0` identifies the σ-algebras of `𝓑^•_{σ^{ε_k}}` and
`𝓑^•_{s_{k+1}}`), and (3.21′) almost surely. The kill event is `G₀ ∩ {ε_k < 1} ∩ Cs k ∩ M ∩ Ω₀`.
-/

noncomputable section

open MeasureTheory Set Metric
open LQGMetric.Blueprint LQGMetric.GM
open scoped ENNReal

namespace LQGMetric
namespace CONF

/-- **the choice of `N₀`** (C:1588, the input `hN₀` of `t39i_iterData_of`): for `a > 0` there is
`N₀` with `7ε(m)^{1/2} ≤ a` for all `m ≥ N₀`, `ε(m) = 2^{−t39gExp m}` -/
theorem t39i_hN₀ {a : ℝ} (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ m : ℕ, N₀ ≤ m → 7 * ((2 : ℝ)⁻¹ ^ t39gExp m) ^ (1 / 2 : ℝ) ≤ a := by
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (pow_pos (div_pos ha (by norm_num : (0 : ℝ) < 7)) 2)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨2 ^ (4 * j), fun m hm => ?_⟩
  have hm1 : 1 ≤ m := le_trans (Nat.one_le_two_pow) hm
  have hj' : j ≤ t39gExp m := by
    unfold t39gExp
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    rw [mul_comm]
    exact Nat.le_log_of_pow_le (by norm_num) hm
  have h1 : (2 : ℝ)⁻¹ ^ t39gExp m ≤ (2 : ℝ)⁻¹ ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hj'
  have h2 : ((2 : ℝ)⁻¹ ^ t39gExp m) ^ (1 / 2 : ℝ) ≤ (((a / 7) ^ 2 : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (h1.trans hj.le) (by norm_num)
  have h3 : (((a / 7) ^ 2 : ℝ)) ^ (1 / 2 : ℝ) = a / 7 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  rw [h3] at h2
  linarith

end CONF
end LQGMetric
