/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L10Exp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L9
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2BridgeLemmas
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L10Var

/-!
# DZZ Lemma 3.10, second statement (eq-oferberlin1) (P2-DZZ3C)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Lemma 3.10 (eq-oferberlin1),
l. 1257–1260: `|E min log D_{γ,δ} − E min log D_{γ,δ,η}| = O((log δ⁻¹)^{0.9})`. Proof (l. 1265–1269):
(ofer-morn1) (`dzz_lemma310`, here the hypothesis `hgood`) combined with (eq-very-crude) (l. 849–853,
`E (log D/log δ⁻¹)² = O(1)`, "and an analogous version for `D_η`"; here the hypotheses `hX`, `hY`,
which also carry the measurability DZZ leave implicit) and Cauchy–Schwarz (here in the AM–GM form
`|d| 1_S ≤ (ε d² + 1_S/ε)/2`).

* `logMinLGD μ δ A B = log min_{A×B} D_δ` (junk `log 0 = 0` if the minimum is infinite);
* `abs_log_toNat_sub_le`: on the event of (ofer-morn1), `|log min D − log min D_η| ≤ 10 (log δ⁻¹)^{0.9}`;
* **`dzz_lemma310_exp`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- `log min_{x ∈ A, y ∈ B} D_δ(x, y)` (junk `0` if the minimum is `∞`). -/
def logMinLGD (μ : Measure ℂ) (δ : ℝ) (A B : Set ℂ) : ℝ :=
  Real.log ((lgdMinSet μ δ A B).toNat : ℝ)

lemma abs_log_toNat_sub_le {m mη : ℕ∞} {X : ℝ} (hX : 0 ≤ X)
    (h1 : (mη : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-X)) ≤ m)
    (h2 : (m : ℝ≥0∞) ≤ mη * ENNReal.ofReal (Real.exp X)) :
    |Real.log (m.toNat : ℝ) - Real.log (mη.toNat : ℝ)| ≤ X := by
  have hpos : ∀ r : ℝ, ENNReal.ofReal (Real.exp r) ≠ 0 :=
    fun r => (ENNReal.ofReal_pos.mpr (Real.exp_pos r)).ne'
  induction m using ENat.recTopCoe with
  | top =>
    induction mη using ENat.recTopCoe with
    | top => simpa using hX
    | coe j =>
      exfalso
      have hlt : ((j : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (Real.exp X) < ⊤ :=
        ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
      rw [ENat.toENNReal_top] at h2
      exact hlt.ne (top_le_iff.mp h2)
  | coe k =>
    induction mη using ENat.recTopCoe with
    | top =>
      exfalso
      rw [ENat.toENNReal_top, ENNReal.top_mul (hpos _)] at h1
      exact absurd (top_le_iff.mp h1) (by simp)
    | coe j =>
      simp only [ENat.toNat_natCast, ENat.toENNReal_coe] at h1 h2 ⊢
      rw [← ENNReal.ofReal_natCast j, ← ENNReal.ofReal_mul (Nat.cast_nonneg j),
        ← ENNReal.ofReal_natCast k, ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg k)] at h1
      rw [← ENNReal.ofReal_natCast j, ← ENNReal.ofReal_mul (Nat.cast_nonneg j),
        ← ENNReal.ofReal_natCast k,
        ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg j) (Real.exp_pos _).le)] at h2
      have e1 := Real.exp_pos (-X)
      have e2 := Real.exp_pos X
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have : (j : ℝ) = 0 := by
          have := Nat.cast_nonneg (α := ℝ) j
          push_cast at h1
          nlinarith
        rw [this]
        simpa using hX
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · push_cast at h2
          have : (0 : ℝ) < k := by exact_mod_cast hk
          linarith
        · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
          have hj' : (0 : ℝ) < j := by exact_mod_cast hj
          have l1 : Real.log k ≤ Real.log j + X := by
            have := Real.log_le_log hk' h2
            rwa [Real.log_mul hj'.ne' e2.ne', Real.log_exp] at this
          have l2 : Real.log j - X ≤ Real.log k := by
            have := Real.log_le_log (by positivity) h1
            rwa [Real.log_mul hj'.ne' e1.ne', Real.log_exp, ← sub_eq_add_neg] at this
          rw [abs_le]
          constructor <;> linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

end DZZ
end LQGMetric
