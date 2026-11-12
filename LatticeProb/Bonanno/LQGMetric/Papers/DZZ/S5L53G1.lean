/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53G1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53E7

/-!
# DZZ Lemma 5.3, part 1, node 2: the bad event of (eq-z-open) as an explicit event (P2-DZZ53G)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2452–2502 (proof of Lemma 5.3,
(eq-z-open)). For one box boundary `Bd = ∂𝖡` with `𝓛₁ = μH[1]`:

* `l53Far ν δ T ω z z'`: the pair `(z, z')` is *far* at `ω`, i.e. not
  `D^{𝕍̃_{z,z'}}_δ[ν ω](z, z') ≤ e^T` (DZZ's `Λ_{z,far}`, l. 2494, with `T` the threshold
  `E log D̃_{δ̃}(u,v) + (log δ⁻¹)^{0.97}`).
* **`l53ZBad ν δ T Bd a b`**: the explicit bad event
  `{𝓛₁{z ∈ ∂𝖡 : 𝓛₁(Λ_{z,far}) ≥ a} ≥ b}` of l. 2497–2500. Its complement is DZZ's
  `𝓔_{𝖡,open}` (DZZ: `a = b = K⁻¹ 𝓛₁(∂𝖡)`).
* **`measurable_lgdTilde_q`**, **`measurableSet_l53Far_q`**: copies of `measurable_lgdTilde`,
  `measurableSet_l53Far` (S5L53E6) that only use the *rational* ball masses (needed for the
  a.e.-measurable `μIn`, S5L53G2, and for σ-algebras of local white noise, S5L53G3).
* **`measurableSet_l53ZBad`**: `l53ZBad` is measurable for *any* σ-algebra on `Ω` for which the
  rational ball masses of `ν` are measurable (this is the measurability half of DZZ's
  "measurable with respect to the field `η̌^𝖡`", l. 2452).
* **`l53ZBad_le`**: for any s-finite measure `μ` on `Ω` (the law, or the law restricted to an
  `𝓕*`-event, or `P[·|A]`): if `μ(far(z,z')) ≤ p` for `z, z' ∈ ∂𝖡` then
  `a b μ(l53ZBad) ≤ p 𝓛₁(∂𝖡)²` (l. 2495–2500; via `l53_far_count`, S5L53E3).
* **`l53_open_of_not_l53ZBad`**: off `l53ZBad`, every `Λ ⊆ ∂𝖡` with `𝓛₁(Λ) ≥ b` has a point `z`
  with `𝓛₁{z' ∈ ∂𝖡 : far} < a` (l. 2502, the form used by `l53_open_chain`, S5L53E4).
* `l53Far_mono`, **`l53ZBad_mono`**: a far-set inclusion on `∂𝖡` (e.g. from the domination
  (eq-M-A-upper-bound-bis), l. 2458, `M_γ ≤ δ²s_i^{-2} M^{η̌^𝖡} e^{(log δ⁻¹)^{0.91}}`) passes to
  the bad events: DZZ's `𝓔_{𝖡,open} ∩ 𝓔₄ ⊆ {𝖡 open}` (l. 2453).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*}

/-- The pair `(z, z')` is far at `ω`: not `D^{𝕍̃_{z,z'}}_δ[ν ω](z, z') ≤ e^T` (DZZ l. 2494). -/
def l53Far (ν : Ω → Measure ℂ) (δ T : ℝ) (ω : Ω) (z z' : ℂ) : Prop :=
  ¬ lgdLeExp (dzzWall (tildeBox z z') (ν ω)) δ T z z'

section Meas

variable [MeasurableSpace Ω]

end Meas

end DZZ
end LQGMetric
