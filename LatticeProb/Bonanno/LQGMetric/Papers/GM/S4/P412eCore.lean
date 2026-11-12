/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412eCore at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412bCore
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eFin2

/-!
# GM Proposition 4.12 on `ℰ_𝕣` with `hfin` discharged (DEC-86 (3))

`p412b_stab_of_ext` and `p412b_core` (P2-M2J2b) took `hfin` (avoid-geodesics have finite
`D_h`-length) as an open input. DEC-86 (3): on `ℰ_𝕣` it follows from GM's condition 3
(l. 1958–1962, `regC3`) via `p412e_hfin_regC3`, provided `∂B_r(z) ⊆ B_{4ℓ𝕣}(𝕣V)`.

* `p412e_sphere_mem_cthickening`: for `(z, r) ∈ 𝒵_k` with `r ≤ ε𝕣`, `∂B_r(z)` lies in the
  `4λ₄ε𝕣`-neighbourhood of `𝓑^•_{t_k}` (GM (4.10): `dist(z, ∂𝓑^•_{t_k}) ≤ 2λ₄ε𝕣`).
* `p412e_stab_of_ext`: `p412b_stab_of_ext` with `hfin` replaced by `∂B_r(z) ⊆ B_{4ℓ𝕣}(𝕣V)`.
* `p412e_core`: `p412b_core` with `hfin` removed; its regularity-region hypothesis is taken for
  the `4λ₄ε𝕣`- instead of the `2λ₄ε𝕣`-neighbourhood of `𝓑^•_{t_k}` (both follow from
  `t_k ≤ τ_{2ℓ𝕣}` and `ε` small; the proof is that of `p412b_core`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- `∂B_r(z) ⊆ cthickening (4λ₄ε𝕣) K` for `(z, r) ∈ 𝒵_k`, `r ≤ ε𝕣` -/
theorem p412e_sphere_mem_cthickening {K : Set ℂ} (hK : IsClosed K) {lam1 lam4 ε ν 𝕣 : ℝ}
    (hlam : 1 < lam4) (hε : 0 < ε) (h𝕣 : 0 < 𝕣) {Rads : Set ℝ} {z : ℂ} {r : ℝ}
    (hc : (z, r) ∈ candSet K lam1 lam4 ε ν 𝕣 Rads) (hr : r ≤ ε * 𝕣) {x : ℂ}
    (hx : x ∈ sphere z r) : x ∈ cthickening (4 * lam4 * ε * 𝕣) K := by
  obtain ⟨-, -, -, hd⟩ := hc
  simp only at hd
  have hpos : 0 < lam4 * ε * 𝕣 := by have := mul_pos hε h𝕣; nlinarith
  have hfne : (frontier K).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, infDist_empty] at hd; linarith [hd.1]
  obtain ⟨y, hy, hzy⟩ := (infDist_lt_iff hfne).1
    (show infDist z (frontier K) < 3 * lam4 * ε * 𝕣 by linarith [hd.2])
  refine mem_cthickening_of_dist_le x y _ K (hK.frontier_subset hy) ?_
  have h1 := dist_triangle x z y
  rw [mem_sphere.1 hx] at h1
  have : ε * 𝕣 ≤ lam4 * ε * 𝕣 := by have := mul_pos hε h𝕣; nlinarith
  linarith

end LQGMetric.GM
