/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54I3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54I2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54F1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117G3

/-!
# D117 P-54T (3): `DZZLem54SegQ` at every `u ∈ 𝕍̄` (P2-DZZ54C)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, (eq-point-to-segment) l. 2559 for every `u ∈ 𝕍̄` and
every boundary segment, from the configuration (`cfg_whp`, S5L54H3) by the isometric coupling
`DZZSimCoupleU` with `a = conj e_j`, `‖a‖ = 1` (lem-scaling-coupling l. 611–624 with the
translation invariance l. 2271; DEC-117 §2(a)(ii) last sentence, §4 P-54T), and P3.17 for the leg
(`DZZProp317Leg`, DZZ l. 2571–2578) to pass from "w.h.p." to the mean. The δ-shift of the
coupling is `δ' = δ e^{λ} = δ^{1−ε}` with `λ = ε log δ⁻¹`, `ε = min(1/4, ι/χ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma K₅₄_subset_dzzVXi {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 1 / 80) : K₅₄ ⊆ dzzVXi ξ := by
  intro z ⟨h1, h2⟩
  exact mem_dzzVXi_of_near (a := 1 / 20) (h1.trans_eq (by norm_num)) (h2.trans_eq (by norm_num))
    (by linarith) hξ0

lemma right_pt_mem_frontier (u : ℂ) :
    (⟨u.re + 1 / 20 / 2, u.im⟩ : ℂ) ∈ frontier (sqBox u (1 / 20)) := by
  rw [frontier_sqBox (by norm_num)]
  refine Or.inr (Complex.mem_reProdIm.2 ⟨rfl, ⟨by linarith [show (0 : ℝ) < 1 / 20 / 2 by norm_num],
    by linarith [show (0 : ℝ) < 1 / 20 / 2 by norm_num]⟩⟩)

lemma log_inv_rpow {δ e : ℝ} (hδ : 0 < δ) : Real.log (δ ^ e)⁻¹ = e * Real.log δ⁻¹ := by
  rw [Real.log_inv, Real.log_rpow hδ, Real.log_inv]; ring

/-- the comparison of the two `log min D` through the coupling -/
lemma log_toNat_mono_of_one_le {m n : ℕ∞} (h : m ≤ n) (hn : n < ⊤) (h1 : 1 ≤ m) :
    Real.log (m.toNat : ℝ) ≤ Real.log (n.toNat : ℝ) := by
  have hm : m < ⊤ := lt_of_le_of_lt h hn
  have h1' : (1 : ℝ) ≤ m.toNat := by
    obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp hm.ne
    simp only [ENat.toNat_coe]; exact_mod_cast h1
  refine Real.log_le_log (by linarith) ?_
  exact_mod_cast ENat.toNat_le_toNat h hn.ne

end DZZ
end LQGMetric
