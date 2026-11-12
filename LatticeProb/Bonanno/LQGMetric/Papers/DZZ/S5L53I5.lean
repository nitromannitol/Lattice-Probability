/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53I5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53I4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53F4

/-!
# DZZ Lemma 5.3, part 1, node 1 with the margin of the walled L3.12 (P2-DZZ53I)

The adapter of `hreg` to S5L53F2/F4: copies of `l53_D1_prob` (S5L53F2), `l53_mem_desirable`,
`l53_hdes_of_D1` and `dzzLem53Exp_dzzMuIn_of_nodes` (S5L53F4) in which the cell chains of `𝒟₁`
and of the bad event of nodes 2–4 meet the closed `8 δ^{C_Mc}`-neighbourhood of `l53Region u v`
(`l53D1EventR`, `l53BadR` with a region parameter `R`; `l53D1Event = l53D1EventR … (l53Region u v)`).

* **`l53_hregN`**: the walled L3.12 at the nine boxes, proved (`dzz_lemma312Near`, S5L53I4);
* **`dzzLem53Exp_dzzMuIn_of_nodesN`**: `dzzLem53Exp_dzzMuIn_of_nodes` with `hreg` in the margin
  form and `hbad` for the thickened region;
* **`dzzLem53Exp_dzzMuIn_of_hd_hbadN`**: there is `α* > 0` (that of DZZ L3.12) such that
  `hd` and `hbad` (thickened region, this `α*`) give DZZ Lemma 5.3 at `μIn`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `𝒟₁` (S5L53F1 `l53D1Event`) with the region of the cell chain as a parameter. -/
def l53D1EventR (γ : ℝ) (W : WNSpace → Ω → ℝ) (αs δ : ℝ) (u v : ℂ) (R : Set ℂ) (T : ℝ) :
    Set Ω :=
  cellSizeEvent γ W δ ∩
    {ω | ∃ l : List DyBox, L53CellChain (approxLQG γ W ω) δ (epsStar αs δ) u v R T l}

lemma l53I_w_mem_dzzV {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) {i : ℕ} (hi : i ≤ 9) :
    l53W u v i ∈ dzzV := by
  have ht0 : (0 : ℝ) ≤ (i : ℝ) / 9 := by positivity
  have ht1 : (i : ℝ) / 9 ≤ 1 := by
    rw [div_le_one (by norm_num)]; exact_mod_cast hi
  have hre : (l53W u v i).re = u.re + (i : ℝ) / 9 * (v.re - u.re) := by
    simp [l53W, Complex.add_re, Complex.mul_re]
  have him : (l53W u v i).im = u.im + (i : ℝ) / 9 * (v.im - u.im) := by
    simp [l53W, Complex.add_im, Complex.mul_im]
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  simp only at hu1 hu2 hv1 hv2
  rw [abs_le] at hu1 hv1 hu2 hv2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]; nlinarith
  · rw [hre]; nlinarith
  · rw [him]; nlinarith
  · rw [him]; nlinarith

/-- **`hreg` in the margin form, proved** (walled DZZ L3.12 at the nine boxes, `dzz_lemma312Near`):
for the `α*` of DZZ L3.12. -/
theorem l53_hregN {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ αs : ℝ, 0 < αs ∧ HighProb P (fun δ => eventEDeltaAlpha γ W αs δ) ∧
      ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ i < 9,
        P (eventRegularNear (tildeBox (l53W u v i) (l53W u v (i + 1)))
          (8 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ) γ W αs ((2 : ℝ)⁻¹ ^ k)
          (l53W u v i) (l53W u v (i + 1)))ᶜ ≤
          ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (1 / 4 : ℝ))) := by
  obtain ⟨αs, hαs, hE, δ₀, hδ₀, h⟩ := dzz_lemma312Near hW hγ hγ2
  refine ⟨αs, hαs, hE, fun u hu v hv => ?_⟩
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one hδ₀ (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨k₀, fun k hk i hi => ?_⟩
  have hδ : (2 : ℝ)⁻¹ ^ k ∈ Ioo (0 : ℝ) δ₀ :=
    ⟨by positivity, (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk).trans_lt hk₀⟩
  have := h _ hδ (tildeBox (l53W u v i) (l53W u v (i + 1))) _
    (l53I_w_mem_dzzV hu hv (i := i) (by omega)) _ (l53I_w_mem_dzzV hu hv (i := i + 1) (by omega))
  rwa [log_inv_two_inv_pow] at this

end DZZ
end LQGMetric
