/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.JordanChord at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.Topology.Path
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoEilenberg
import Mathlib.Analysis.Complex.Convex

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# JORDAN-CHORD: the two sides of a simple chord are disjoint

* `chordSides_disjoint`: for a simple chord `η` from `0` to `∞` in `ℍ` (`IsSimpleChord`),
  `leftComponent η` and `rightComponent η` are disjoint.

**Source.** This is the separation of a domain by a cross-cut: M. H. A. Newman, *Elements of the
Topology of Plane Sets of Points* (2nd ed. 1964), Ch. V, Theorem 11.7 (printed p. 118, PDF
p. 63) (a cross-cut of a Jordan domain whose end-points separate the boundary separates the
domain); cf. Pommerenke, *Boundary Behaviour of Conformal Maps*, §1.3. The proof goes through
Eilenberg's criterion (R. B. Burckel, *Classical Analysis in the Complex Plane*, Exercise
4.37(i), printed p. 215; node T2 of this repository, `CA.Topo.hasLogOn_of_not_separates`), as in
the proof of Janiszewski's theorem there. The concrete computation below is an **own elementary
argument** (cost rule: short, standard).

**Proof.** Suppose `z` lies in both sides: paths `p` from `z` to `x < 0` and `q` from `z` to
`y > 0` run in `ℍ \ η` except at their ends. Let `Q = range p ∪ range q` (compact, connected,
`0 ∉ Q`), `m = min_Q ‖·‖ > 0`, `ε = m/2`, `S = [x, y] ⊆ ℝ`, `J = Q ∪ S`.
1. `a = iε` and `b = -iε` lie in the same component of `ℂ \ J`: `b` is in the lower half plane
   (unbounded, connected, off `J`), `a` is in `(ball 0 m ∩ ℍ) ∪ η((0,∞))` (unbounded since
   `‖η t‖ → ∞`, connected since `η t → 0`, off `J`); both lie in the unbounded component (T6).
2. By Eilenberg, `f z = (z - iε)/(z + iε)` has a continuous logarithm `G` on `J`.
3. On `Q`, `Re f > 0` (`‖z‖ > ε`), so `G - Log f` is constant on `Q`; on `S`,
   `f t = e^{-2i arg(t + iε)}`, so `G + 2i arg(· + iε)` is constant on `S`. At `y > 0`,
   `Log f y = -2i arg(y + iε)`; at `x < 0`, `Log f x = -2i arg(x + iε) + 2πi`. Comparing the two
   constants at `x` and `y` gives `2πi = 0`.
-/

noncomputable section

open Set Filter Topology Metric Complex Real

namespace QuantumZipper
namespace JordanChord

open QuantumZipper.CA.Topo

/-- Two continuous logarithms of the same function on a preconnected set differ by a constant. -/
theorem log_sub_eq_of_isPreconnected {S : Set ℂ} (hS : IsPreconnected S) {L₁ L₂ : ℂ → ℂ}
    (h₁ : ContinuousOn L₁ S) (h₂ : ContinuousOn L₂ S)
    (he : ∀ z ∈ S, exp (L₁ z) = exp (L₂ z)) {u v : ℂ} (hu : u ∈ S) (hv : v ∈ S) :
    L₁ u - L₂ u = L₁ v - L₂ v := by
  have h2 := two_pi_I_ne_zero'
  have hmaps : MapsTo (fun z => (L₁ z - L₂ z) / (2 * π * I)) S (range ((↑) : ℤ → ℂ)) := by
    intro z hz
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 (he z hz)
    exact ⟨n, by simp only [hn, add_sub_cancel_left, mul_div_cancel_right₀ _ h2]⟩
  have hc := hS.constant_of_mapsTo Complex.isClosedEmbedding_intCast.isInducing.isDiscrete_range
    ((h₁.sub h₂).div_const _) hmaps hu hv
  exact (div_left_inj' h2).1 hc

end JordanChord
end QuantumZipper
