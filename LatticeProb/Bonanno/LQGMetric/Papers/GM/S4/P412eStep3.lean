/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412eStep3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412dL414
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412cStep3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanPunct
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanJ1bFinal

/-!
# GM L4.15 Step 3 for filled metric balls (l. 2157–2166, 2236–2244)

`p412c_step3` (P2-DEC86) takes the conclusion of `GML4_14'` and (LC) as inputs. For
`K = 𝓑^•_t` (`t > 0`, `D` a length metric with bounded balls) both are now proved:
`p412d_GML4_14` (GM L4.14′) and `p412c_filledBall_locConnAt` (LC). This file instantiates them.

* `p412e_GML4_14_filled`: GM L4.14′ for `K = 𝓑^•_t`.
* `p412eGoodZ`, `p412e_goodZ_exists`: GM L4.15 Step 3 (∗) (l. 2162–2165) for `K = 𝓑^•_t`,
  `y ∈ ∂K`: a point `z_y ∈ ∂K` and `r ≤ 8ε` such that every path `P` starting at
  `P(a) ∈ ∂K ∩ cl V` (`V` a witness component for `𝒞^ε_y`, GM (4.43)), running in `ℂ ∖ K` after
  `a` and ending outside any `F ⊇ cl B_{16ε}(K)` (`F = 𝓑^•_{s_{k+1}}`, GM l. 2240) meets
  `cl B_{2r}(z_y)` (`2r ≤ 16ε`; GM: `B_{16ε^κ𝕣}(z_y)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the Step 3 property (∗) of `z` for `y` (GM l. 2162–2165), with the radius `2r ≤ 16ε` -/
def p412eGoodZ (K : Set ℂ) (y z : ℂ) (ε : ℝ) : Prop :=
  ∃ r, 0 < r ∧ r ≤ 8 * ε ∧ ∀ F : Set ℂ, IsClosed F → Bornology.IsBounded F → IsConnected Fᶜ →
    cthickening (16 * ε) K ⊆ F →
    ∀ (X : Set ℂ) (v : ℂ) (P : ℝ → ℂ) (a b : ℝ), X ⊆ Kᶜ → IsConnected X →
      Metric.ediam X ≤ ENNReal.ofReal ε → v ∉ X ∪ K →
      Bornology.IsBounded (connectedComponentIn (X ∪ K)ᶜ v) →
      y ∈ closure (connectedComponentIn (X ∪ K)ᶜ v) →
      P a ∈ closure (connectedComponentIn (X ∪ K)ᶜ v) →
      P a ∈ frontier K → a < b → ContinuousOn P (Icc a b) →
      (∀ s ∈ Ioc a b, P s ∉ K) → P b ∉ F → ∃ s ∈ Icc a b, P s ∈ closedBall z (2 * r)

end LQGMetric.GM
