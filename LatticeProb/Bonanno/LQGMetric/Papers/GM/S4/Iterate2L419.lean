/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate2L419 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL416b
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL422F
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47MeasG

/-!
# GM Lemma 4.19: the properties of `F_k` (deterministic part)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.19 (`lem-holder-balls`,
l. 2318–2327), proof l. 2593–2611: "if `F_k` occurs then … for each `(z,r) ∈ 𝒵_k` we have
`B_{λ₄r}(z) ⊂ 𝓑^•_{s_{k+1}}` and [every] `D_h(·,·;ℂ∖cl B_r(z))`-geodesic from `𝕫` to a point of
`∂B_r(z)` [is contained in] `𝓑^•_{s_{k+1}}`", where `F_k` is the event of Lemma 4.22 (4.39).

* `gm_ball_subset_filledBall_of_sphere`: "`𝓑^•_{s}` contains every point which it disconnects
  from `∞`": `∂B_ρ(z) ⊂ 𝓑_s` ⇒ `B_ρ(z) ⊂ 𝓑^•_s`.
* `gm_L4_19_of_439` (l. 2597–2611): from (4.39) with `t + B < s'`: `B_ρ(z) ⊂ 𝓑^•_{s'}`
  (`ρ = 2λ₄ε𝕣`) and every finite-length `D(·,·;ℂ∖cl B_r(z))`-geodesic `Q` from `𝕫` to `∂B_r(z)`
  (`r ≤ ε𝕣`) stays in `𝓑^•_{s'}` (by the last hit of `∂B_ρ(z)`, as GM).
* `gm_L4_19_props`: the same on `ℰ_𝕣` for every `k ≤ K` and `(z,r) ∈ 𝒵_k` with `r ≤ ε𝕣`, from
  `gm_L4_22` (GM Lemma 4.22), with `𝓑^•_{s_{k+1}} ⊂ B_{3ℓ𝕣}(𝕫)` (`s_{k+1} ≤ τ_{2ℓ𝕣}` in GM).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- `𝓑^•_s` contains every point it disconnects from `∞`: a ball whose circle lies in `𝓑_s` -/
theorem gm_ball_subset_filledBall_of_sphere (D : ContMetric) {𝕫 z : ℂ} {ρ s : ℝ}
    (hsph : sphere z ρ ⊆ ballM D 𝕫 s) : ball z ρ ⊆ filledBall D 𝕫 s := by
  intro y hy
  by_cases hyc : y ∈ closure (ballM D 𝕫 s)
  · exact Or.inl hyc
  refine Or.inr ⟨hyc, (isBounded_ball (x := z) (r := ρ)).subset ?_⟩
  have hsub : connectedComponentIn (closure (ballM D 𝕫 s))ᶜ y ⊆ ball z ρ ∪ (closedBall z ρ)ᶜ := by
    intro x hx
    have hx' : x ∉ closure (ballM D 𝕫 s) := connectedComponentIn_subset _ _ hx
    rcases lt_trichotomy (dist x z) ρ with h | h | h
    · exact Or.inl h
    · exact absurd (subset_closure (hsph (mem_sphere.2 h))) hx'
    · exact Or.inr (by simpa [mem_closedBall] using h)
  exact (isPreconnected_connectedComponentIn).subset_left_of_subset_union isOpen_ball
    isClosed_closedBall.isOpen_compl
    (disjoint_compl_right.mono_left ball_subset_closedBall) hsub
    ⟨y, mem_connectedComponentIn hyc, hy⟩

end LQGMetric.GM
