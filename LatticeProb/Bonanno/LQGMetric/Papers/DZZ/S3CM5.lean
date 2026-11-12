/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3CM5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CM4

/-!
# DZZ (eq-very-crude) at `μIn` for sets in `𝕍_{-ξ}` (P2-DZZCM)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 854–857), (eq-very-crude):
`E (log D_δ(u,v) / log δ⁻¹)² = O(1)`, here for `min_{A×B} D_δ` with `A ∋ u`, `B ∋ v`,
`u ≠ v ∈ 𝕍_{-ξ}` (DZZ l. 1521: "the general case follows by the same proof").

* `cm_log_min_le_of_good`: DZZ's segment covering (l. 744–745, as `log_tilde_le_of_good`) on the
  good event of DG L3.8 at scale `ε`: `log min_{A×B} D_δ ≤ log 6 + β log ε⁻¹`;
* `lintegral_sq_logMin_dzzMuIn_le`: the second moment, by the tail sum of
  `lintegral_sq_log_tilde_le` (S5L53B2) in the generic form `lintegral_sq_le_of_geom`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma cm_lineMap_mem_dzzVIn {r : ℝ} {u v : ℂ} (hu : u ∈ dzzVIn r) (hv : v ∈ dzzVIn r) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : AffineMap.lineMap u v t ∈ dzzVIn r := by
  have hre : (AffineMap.lineMap u v t : ℂ).re = u.re + t * (v.re - u.re) := by
    simp [AffineMap.lineMap_apply_module]; ring
  have him : (AffineMap.lineMap u v t : ℂ).im = u.im + t * (v.im - u.im) := by
    simp [AffineMap.lineMap_apply_module]; ring
  obtain ⟨a1, a2, a3, a4⟩ := hu
  obtain ⟨b1, b2, b3, b4⟩ := hv
  obtain ⟨t0, t1⟩ := ht
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hre, him] <;>
    nlinarith [mul_nonneg t0 (sub_nonneg.2 t1)]

lemma cm_dist_le_two {r : ℝ} (hr : 0 ≤ r) {u v : ℂ} (hu : u ∈ dzzVIn r) (hv : v ∈ dzzVIn r) :
    dist u v ≤ 2 := by
  rw [Complex.dist_eq]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  obtain ⟨a1, a2, a3, a4⟩ := hu
  obtain ⟨b1, b2, b3, b4⟩ := hv
  simp only [Complex.sub_re, Complex.sub_im]
  have e1 : |u.re - v.re| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have e2 : |u.im - v.im| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

/-- **the good event bounds `log min_{A×B} D_δ`** (DZZ's covering of `[u, v]`, l. 744–745) -/
lemma cm_log_min_le_of_good {γ b β ε δ ξ : ℝ} {ω : Ω} {A B : Set ℂ} {u v : ℂ} (hξ : 0 < ξ)
    (hu : u ∈ A) (hv : v ∈ B) (hu' : u ∈ dzzVIn ξ) (hv' : v ∈ dzzVIn ξ) (huv : u ≠ v)
    (hb : ∀ S : Set ℂ, MeasurableSet S → S ⊆ dzzVIn (ξ / 2) →
      wickQArea γ W ω S ≤ ENNReal.ofReal (Real.exp b) * DG.muHU W γ ω S)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 < β) (hεξ : ε ^ β ≤ ξ / 2)
    (hδ : ENNReal.ofReal (Real.exp b) * ENNReal.ofReal ε ≤ ENNReal.ofReal (δ ^ 2))
    (hgood : ∀ z ∈ dzzVIn ξ, DG.muHU W γ ω (ball z (ε ^ β)) ≤ ENNReal.ofReal ε) :
    logMinLGD (dzzMuIn γ W ω) δ A B ≤ Real.log 6 + β * Real.log ε⁻¹ := by
  have hεβ : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
  have hD := lgdDZZ_le_segment (ν := dzzMuIn γ W ω) (δ := δ) hεβ huv (fun t ht => by
    have hx := cm_lineMap_mem_dzzVIn hu' hv' ht
    have hsub := cm_ball_sub_dzzVIn hεξ hx
    have hsubV : ball (AffineMap.lineMap u v t) (ε ^ β) ⊆ dzzV :=
      hsub.trans (dzzVIn_sub_dzzV (by positivity))
    rw [dzzMuIn, dzzWall_apply_of_subset isClosed_dzzV.measurableSet hsubV]
    refine (hb _ isOpen_ball.measurableSet hsub).trans ?_
    refine le_trans ?_ hδ
    gcongr
    exact hgood _ hx)
  set N : ℕ := ⌈2 * dist u v / ε ^ β⌉₊ + 1 with hN
  have hNle : (N : ℝ) ≤ 6 * ε ^ (-β) := by
    have hinv : 1 ≤ ε ^ (-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)
    have e1 : ε ^ (-β) = (ε ^ β)⁻¹ := Real.rpow_neg hε.le β
    have hd := cm_dist_le_two (by positivity) hu' hv'
    have hq : 2 * dist u v / ε ^ β ≤ 4 * ε ^ (-β) := by
      rw [e1, div_eq_mul_inv]
      have : 0 ≤ (ε ^ β)⁻¹ := by positivity
      nlinarith
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * dist u v / ε ^ β by positivity)
    simp only [hN, Nat.cast_add, Nat.cast_one]
    linarith
  have hmin : lgdMinSet (dzzMuIn γ W ω) δ A B ≤ (N : ℕ∞) :=
    (iInf₂_le_of_le u hu (iInf₂_le_of_le v hv le_rfl)).trans hD
  have hT : (lgdMinSet (dzzMuIn γ W ω) δ A B).toNat ≤ N := ENat.toNat_le_of_le_natCast hmin
  have hN1 : (1 : ℝ) ≤ N := by simp only [hN]; exact_mod_cast Nat.le_add_left 1 _
  have hlogN : Real.log N ≤ Real.log 6 + β * Real.log ε⁻¹ := by
    calc Real.log N ≤ Real.log (6 * ε ^ (-β)) := Real.log_le_log (by linarith) hNle
      _ = Real.log 6 + β * Real.log ε⁻¹ := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hε _).ne', Real.log_rpow hε,
          Real.log_inv]; ring
  unfold logMinLGD
  rcases Nat.eq_zero_or_pos (lgdMinSet (dzzMuIn γ W ω) δ A B).toNat with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact (Real.log_nonneg hN1).trans hlogN
  · exact (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hT)).trans hlogN

end DZZ
end LQGMetric
