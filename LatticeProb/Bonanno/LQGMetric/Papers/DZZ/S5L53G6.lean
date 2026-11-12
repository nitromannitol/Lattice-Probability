/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53G6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53G5

/-!
# DZZ Lemma 5.3, part 1, node 2: the `(u,v)`-step of the far bound for small `δ̃` (P2-DZZ53G)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2490–2493 ("we combine the
preceding inequality with Corollary 3.9 and Proposition 3.17").

The regime `l log 2 ≥ L^{0.96}` (`δ̃ = 2^{−l}`, `L = log δ⁻¹`), complementing
`l53_uv_far_small` (S5L53G5):
* `l53_uv_conc2`: (eq-concentration-2) of the walled P3.17 at `𝕍̃_{u,v}` for `({u},{v})`.
* `l53_log_le_of_cor39`: the event of Cor 3.9 in logarithmic form.
* **`l53_uv_far_large`**: from the walled P3.17 and the walled Cor 3.9 at `𝕍̃_{u,v}` for the pair
  `({u},{v})` (the conclusion of `cor39_boundOn`, S5WallSim1, specialised; its inputs `h32`,
  `h35` at `𝕍̃_{u,v}` are the same as in node 1's `hd`):
  `P(log D̃_{δ̃e^{−L^{0.95}}}(u,v) > E log D̃_{δ̃}(u,v) + L^{0.97}) ≤ K⁻⁴`.
  Proof: on the intersection of the concentration events at `δ̃` and `δ' = δ̃e^{−L^{0.95}}`, the
  Cor 3.9 event and `{D̃_{δ̃} < ∞}` (positive probability), the means satisfy
  `E log D̃_{δ'} + (log δ'⁻¹)^{0.95} ≤ E log D̃_{δ̃} + 12 L^{0.95} ≤ E log D̃_{δ̃} + L^{0.97}`; then
  concentration at `δ'`. Own elementary argument (DZZ give the citation only).
* **`l53_uv_far`**: both regimes together, for all `l` with `l log 2 ≤ L`.
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

/-- (eq-concentration-2) at `𝕍̃_{u,v}` for `({u},{v})`, from the walled P3.17. -/
lemma l53_uv_conc2 {μ : Ω → Measure ℂ} {ξ : ℝ} (h317 : DZZProp317Walls P μ ξ dgWalls)
    (hξ4 : ξ ≤ 1 / 4) {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v)
    (h2ξ : 2 * ξ ≤ dist u v) (hξ : 0 < ξ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ' ∈ Ioo (0 : ℝ) δ₀,
      P (conc2Event (fun ω => dzzWall (tildeBox u v) (μ ω)) P δ' {u} {v})ᶜ ≤
        ENNReal.ofReal (Real.exp (-(Real.log δ'⁻¹ ^ (0.7 : ℝ)))) := by
  have hin := dzzProp317In_tildeBox_of_walls h317 hu hv huv
  have hVu : u ∈ dzzVXi ξ := by
    have h := tildeBox_subset_dzzVXi hu hv huv (mem_tildeBox_left u v)
    exact ⟨h.1, hξ4.trans h.2⟩
  have hVv : v ∈ dzzVXi ξ := by
    have h := tildeBox_subset_dzzVXi hu hv huv (mem_tildeBox_right u v)
    exact ⟨h.1, hξ4.trans h.2⟩
  have hAB := isXiAdmissible_const_singleton hVu hVv (by linarith)
  obtain ⟨c, hc, hall⟩ := hin
  exact (hall _ _ hAB (fun _ _ =>
    ⟨singleton_subset_iff.2 (mem_kXi_tildeBox_left huv h2ξ),
      singleton_subset_iff.2 (mem_kXi_tildeBox_right huv h2ξ)⟩)).2

lemma l53_log_two_pow (l : ℕ) : Real.log ((2 : ℝ)⁻¹ ^ l)⁻¹ = l * Real.log 2 := by
  rw [inv_pow, inv_inv, Real.log_pow]

end DZZ
end LQGMetric
