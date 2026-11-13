/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Probability.BMLocalMin.Main at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Probability.BMLocalMin.Prob

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Local extrema of Brownian motion (Mörters–Peres, Theorem 2.11)

Source: P. Mörters, Y. Peres, *Brownian Motion* (CUP 2010), Theorem 2.11 (draft
 lines 2400–2450). Used in DMS
(arXiv:1409.7055v4) §1.3, lines 699–700 (a.s. Brownian paths have countably many
local minima, with pairwise distinct values).

For `B` with `IsBrownianReal B P` and `path B ω t = B t.toNNReal ω`, almost surely, both on
`I = [0, T]` (`T > 0`) and on `I = [0, ∞)` (local extrema relative to `I`, so one-sided at the
endpoints):

* every local minimum is strict, distinct local minima have distinct values, and the set of
  local-minimum times is countable (`ae_locMinGood_Icc`, `ae_locMinGood_Ici`);
* the same for local maxima (`ae_locMaxGood_Icc`, `ae_locMaxGood_Ici`);
* for fixed `0 ≤ a < b`, the minimum and the maximum over `[a, b]` are attained at a unique time
  (`ae_isMinOn_unique`, `ae_isMaxOn_unique`; MP 2.11 (c) is `a = 0`, `b = T`).

The versions for `-B` are these theorems applied to `hB.neg` (mathlib `IsBrownianReal.neg`).
Density of local-minimum times (the rest of MP 2.11 (b)) is not formalized here (not needed by DMS).
-/

open MeasureTheory ProbabilityTheory NNReal Set

namespace MatedCRTHarmonic.MoTPort
namespace BMLocalMin

/-- Every local minimum of `f` on `I` is strict, distinct local minima have distinct values, and the
set of local-minimum times is countable. -/
def LocMinGood (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  (∀ t ∈ I, IsLocalMinOn f I t → ∃ ε > 0, ∀ u ∈ I, u ≠ t → |u - t| < ε → f t < f u) ∧
  (∀ t₁ ∈ I, ∀ t₂ ∈ I, IsLocalMinOn f I t₁ → IsLocalMinOn f I t₂ → t₁ ≠ t₂ → f t₁ ≠ f t₂) ∧
  {t ∈ I | IsLocalMinOn f I t}.Countable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- **MP Thm 2.11 (a), (b)** for local minima of Brownian motion on `[0, ∞)`. -/
theorem ae_locMinGood_Ici (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, LocMinGood (path B ω) (Ici 0) := by
  filter_upwards [hB.cont, ae_sep hB (countable_range ((↑) : ℚ → ℝ))] with ω hc hS
  exact localMin_props (continuous_path hc) hS (countable_range _)
    (fine_Ici fun u => mem_range_self u) subset_rfl

/-- **MP Thm 2.11 (c)**: for fixed `0 ≤ a < b`, a.s. the minimum of Brownian motion over `[a, b]`
is attained at a unique time. -/
theorem ae_isMinOn_unique (hB : IsBrownianReal B P) {a b : ℝ} (ha : 0 ≤ a) :
    ∀ᵐ ω ∂P, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, IsMinOn (path B ω) (Icc a b) x →
      IsMinOn (path B ω) (Icc a b) y → x = y := by
  have hD : (insert a (insert b (range ((↑) : ℚ → ℝ)))).Countable :=
    ((countable_range _).insert b).insert a
  filter_upwards [hB.cont, ae_sep hB hD] with ω hc hS x hx y hy hmx hmy
  exact isMinOn_unique (continuous_path hc) hS
    (fun u => mem_insert_of_mem _ (mem_insert_of_mem _ (mem_range_self u))) (mem_insert a _)
    (mem_insert_of_mem _ (mem_insert b _)) ha hx hy hmx hmy

end BMLocalMin
end MatedCRTHarmonic.MoTPort
