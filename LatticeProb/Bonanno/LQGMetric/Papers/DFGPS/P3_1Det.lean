/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_1Det at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_1Geom
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordsAux1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 3.1: the deterministic Steps 1 and 2 (task P2-DFA3)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Proposition 3.1,
T:1522–1568, on the event `F^ε_𝕣 ∩ {(3.10)}` (T:1532–1535), with `ν = 1`:

* `lower_det` (Step 1, (3.11), T:1537–1544): every path from `𝕣K₁` to `𝕣K₂` crosses from
  `∂B_r(w)` to `∂B_{2r}(w)` for a good `(w, r)`, so
  `D_h(𝕣K₁, 𝕣K₂; V) ≥ C⁻¹ Λ⁻¹ ε^{2Λ+ξq} 𝔠_𝕣 e^{ξ h_𝕣(0)}`.
* `upper_det` (Step 2, (3.12), T:1547–1556): the path of Lemma 3.5 lies in the union of at most
  `B ε^{-6}` good circles (the paper: `ε^{-4-o(1)}`; any polynomial bound suffices), each of
  `D_h(·,·; 𝕣U)`-diameter `≤ C Λ ε^{-(2Λ+ξq)} 𝔠_𝕣 e^{ξ h_𝕣(0)}`, and the triangle inequality
  (`P31.chain_bound`) gives the bound.
-/

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

namespace P31

lemma rpow_one_add_one (ε : ℝ) : ε ^ ((1 : ℝ) + 1) = ε ^ 2 := by
  rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two]

/-- the circle-average bound (3.10) at the dyadic radii, as a hypothesis on `g` -/
def TailOK (g : DistC) (q ε 𝕣 R : ℝ) : Prop :=
  ∀ w : ℂ, ‖w‖ < R * 𝕣 → w ∈ gridPts (ε ^ 2 * 𝕣 / 4) → ∀ k : ℕ, ε ^ 2 ≤ ((2 : ℝ) ^ k)⁻¹ →
    ((2 : ℝ) ^ k)⁻¹ ≤ ε →
    |circleAvg g (((2 : ℝ) ^ k)⁻¹ * 𝕣) w - circleAvg g 𝕣 0| ≤ q * Real.log ε⁻¹

/-- **Step 1** of the proof of Proposition 3.1 ((3.11), T:1537–1544). -/
theorem lower_det {D : DistC → ContMetric} {c : ℝ → ℝ} {g : DistC} {ξ Λ q ε 𝕣 C M R₀ d : ℝ}
    (hξ : 0 < ξ) (hΛ : 1 < Λ)
    (hc : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r →
      Λ⁻¹ * δ ^ Λ ≤ c (δ * r) / c r ∧ c (δ * r) / c r ≤ Λ * δ ^ (-Λ))
    (hcpos : ∀ r, 0 < r → 0 < c r) (hε0 : 0 < ε) (hε1 : ε < 1) (h𝕣 : 0 < 𝕣) (hC : 1 < C)
    (hM : 1 ≤ M) (hR₀ : 0 < R₀) (hεR : ε ≤ R₀⁻¹) (hεd : 3 * ε ≤ d) {K₁ K₂ V : Set ℂ}
    (hK₁ : K₁ ⊆ ball 0 R₀) (hd : ∀ x ∈ K₁, ∀ y ∈ K₂, d ≤ ‖x - y‖)
    (hcov : GoodCover (fun w r => g ∈ annEvent ξ D c C r w) 1 M ε 𝕣)
    (htail : TailOK g q ε 𝕣 (R₀ + 1)) :
    ENNReal.ofReal (C⁻¹ * (Λ⁻¹ * ε ^ (2 * Λ + ξ * q) * scaleFac ξ c g 𝕣 0)) ≤
      setDistIn (D g) (scaleSet 𝕣 0 K₁) (scaleSet 𝕣 0 K₂) V := by
  refine le_setDistIn_of_cross (D g) fun x hx => ?_
  have hxn := norm_of_mem_scaleSet h𝕣 hK₁ hx
  have hεM : R₀ ≤ ε ^ (-M) := by
    have h1 : R₀ ≤ ε⁻¹ := by rw [le_inv_comm₀ hR₀ hε0]; exact hεR
    refine h1.trans ?_
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
  have hxB : x ∈ ball (0 : ℂ) (𝕣 * ε ^ (-M)) := by
    rw [mem_ball_zero_iff]
    exact hxn.trans_le (mul_le_mul_of_nonneg_left hεM h𝕣.le)
  obtain ⟨w, ⟨_, hwg⟩, r, ⟨k, rfl⟩, hr1, hr2, hgood, hxw⟩ := hcov x hxB
  rw [rpow_one_add_one] at hr1 hwg hxw
  rw [mem_ball, dist_eq_norm] at hxw
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hδ1 : ε ^ 2 ≤ ((2 : ℝ) ^ k)⁻¹ := le_of_mul_le_mul_right hr1 h𝕣
  have hδ2 : ((2 : ℝ) ^ k)⁻¹ ≤ ε := le_of_mul_le_mul_right hr2 h𝕣
  have hwn : ‖w‖ < (R₀ + 1) * 𝕣 := by
    have : ‖w‖ ≤ ‖x‖ + ‖x - w‖ := by
      calc ‖w‖ = ‖x - (x - w)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - w‖ := norm_sub_le _ _
    nlinarith
  obtain ⟨hb1, -⟩ := scaleFac_bounds hξ hΛ hc hcpos hε0 hε1 h𝕣 hδ1 hδ2
    (htail w hwn hwg k hδ1 hδ2)
  refine ⟨w, ((2 : ℝ) ^ k)⁻¹ * 𝕣, by nlinarith, fun y hy => ?_, ?_⟩
  · have hxy := sep_scaleSet h𝕣 hd hx hy
    have : ‖x - y‖ ≤ ‖y - w‖ + ‖x - w‖ := by
      calc ‖x - y‖ = ‖(x - w) - (y - w)‖ := by congr 1; ring
        _ ≤ ‖x - w‖ + ‖y - w‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    nlinarith
  · refine le_trans ?_ hgood.2
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hb1 ?_)
    exact inv_nonneg.2 (by linarith)

end P31

end LQGMetric.DFGPS
