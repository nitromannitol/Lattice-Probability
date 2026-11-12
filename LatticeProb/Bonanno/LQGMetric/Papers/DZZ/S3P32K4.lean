/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32K4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32K3

/-!
# Walled P3.2, K4: assembly (P2-DZZ317K)

DZZ (arXiv:1807.00422) Prop 3.2 (l. 807–812) for `(dzzWall K μ, approxLGDSetOn S)` (Remark 5.2,
D117 §3): the two halves of S3P32K3 combined as in `dzz_prop32U_of` (S3P32).

* **`dzz_prop32UOn_of`**: `L32BallCoverOn → L32UpperCrossOn → DZZLemma35UOn → DZZProp32UOn`;
* **`dzz_prop32UIn_dzzMuIn_of`**: at `dzzWall K μIn`, `S = cellsMeeting K`, with the proved
  `l32BallCoverIn_dzzMuIn`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

universe u

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Walled DZZ Proposition 3.2** (uniform form) from (eq-Euclidean-Ball-covering) and
(Eq.boundDprime) for `D`. -/
theorem dzz_prop32UOn_of {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {K : Set ℂ} {S : Set DyBox} {μ : Ω → Measure ℂ} {ξ ξd : ℝ}
    (hξ : 0 < ξ)
    (hξd : ξd < dzzCMc γ) (hcov : L32BallCoverOn P γ W S μ) (hX : L32UpperCrossOn P γ W K S μ ξ ξd)
    (h35U : ∀ ξd' : ℝ, ξd' < dzzCMc γ → DZZLemma35UOn P γ W K S ξ ξd') :
    DZZProp32UOn P γ W K S μ ξ ξd := by
  obtain ⟨c₁, hc₁, δ₁, hδ₁, h₁⟩ := dzz_prop32_lowerOn hW hγ hγ2 hcov hξ hξd h35U
  obtain ⟨c₂, hc₂, δ₂, hδ₂, h₂⟩ := dzz_prop32_upperOn hW hγ hγ2 hX hξ hξd
  set c := min c₁ c₂
  have hc : 0 < c := lt_min hc₁ hc₂
  refine ⟨c / 2, by positivity, min (min δ₁ δ₂) ((1 / 2) ^ (2 / c)), by positivity,
    fun δ hδ A B hAB => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδa : δ < δ₁ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδb : δ < δ₂ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδc : δ < (1 / 2) ^ (2 / c) := hδ.2.trans_le (min_le_right _ _)
  have hδ1 : δ < 1 := hδc.trans_le (Real.rpow_le_one (by norm_num) (by norm_num) (by positivity))
  rw [prop32EventOn_eq, compl_inter]
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (h₁ δ ⟨hδ0, hδa⟩ A B hAB) (h₂ δ ⟨hδ0, hδb⟩ A B hAB)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have m1 : δ ^ c₁ ≤ δ ^ c := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_left _ _)
  have m2 : δ ^ c₂ ≤ δ ^ c := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_right _ _)
  have hhalf : δ ^ (c / 2) ≤ 1 / 2 := by
    have := Real.rpow_le_rpow hδ0.le hδc.le (by positivity : 0 ≤ c / 2)
    rwa [← Real.rpow_mul (by norm_num), show 2 / c * (c / 2) = 1 by field_simp,
      Real.rpow_one] at this
  have hsplit : δ ^ c = δ ^ (c / 2) * δ ^ (c / 2) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  have : 0 ≤ δ ^ (c / 2) := by positivity
  nlinarith

end DZZ
end LQGMetric
