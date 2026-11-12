/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53E7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53E6
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53E4

/-!
# DZZ Lemma 5.3, part 1: (eq-z-open) from the per-pair far bound (P2-DZZ53E)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2495–2502, for one box boundary
`Bd = ∂𝖡` with `𝓛₁ = μH[1]`, `𝓛₁(∂𝖡) < ∞`, and the tilde distance `D̃_δ(z,z') = D^{𝕍̃_{z,z'}}_δ(z,z')`.

* **`l53_zopen`**: if every pair `z, z' ∈ ∂𝖡` is far (`¬ lgdLeExp δ T`) with probability `≤ p`,
  then outside an event `𝓑` with `a b P(𝓑) ≤ p 𝓛₁(∂𝖡)²` the box is open: every `Λ ⊆ ∂𝖡` with
  `𝓛₁(Λ) ≥ b` contains a `z` with `𝓛₁{z' ∈ ∂𝖡 : (z,z') far} ≤ a`. This is the form used by
  `l53_open_chain` (after `lgdLeExp_wall_mono`, for the pairs with `𝕍̃_{z,z'} ⊆ 𝕍̃_{u,v}`).
  With DZZ's `p = O(K⁻⁴)`, `a = b = K⁻¹𝓛₁(∂𝖡)`: `P(𝓑) = O(K⁻²)`.
  (Conditioning on `𝓕*` is not included: apply it to the conditional law.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal MeasureTheory

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A smaller wall gives a larger distance: a non-far pair for the tilde distance `D^{𝕍̃_{z,z'}}`
is related for `D^K` whenever `𝕍̃_{z,z'} ⊆ K` (DZZ: the pieces lie in `𝕍̃_{u,v}`, l. 2361). -/
lemma lgdLeExp_wall_mono {K K' : Set ℂ} (hKK : K' ⊆ K) (μ : Measure ℂ) {δ T : ℝ} {x y : ℂ}
    (h : lgdLeExp (dzzWall K' μ) δ T x y) : lgdLeExp (dzzWall K μ) δ T x y := by
  have hle : lgdDZZ (dzzWall K μ) δ x y ≤ lgdDZZ (dzzWall K' μ) δ x y :=
    lgdDZZ_mono_measure (dzzWall_anti hKK μ) δ x y
  refine ⟨ne_top_of_le_ne_top h.1 hle, le_trans ?_ h.2⟩
  exact_mod_cast ENat.toNat_le_toNat hle h.1

end DZZ
end LQGMetric
