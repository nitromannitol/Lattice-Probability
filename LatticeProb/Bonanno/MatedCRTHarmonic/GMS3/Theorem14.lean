/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS3.Theorem14 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Lemma34
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Recurrence
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph

/-!
# GMS [18] Theorem 1.4 (recurrence), conditional on the inputs of Proposition 2.10 and Lemma 2.7

Source: GMS [18] Theorem 1.4 and its proof. The corresponding recurrence statement for the mated-CRT map is recorded as the frozen declaration `matedCRT_recurrent`.

[18] proves recurrence of the unit-mesh map `G¹` from: (i) for each `k`, the scaled cells of `G¹`
(scaling `R_{2^k}`, the joint scaling of the cone and the curve) are the cells of the mesh
`2^{-k}` map, for which the bound (1.8) holds outside an event of probability `O(2^{-αk})`; (ii) Borel–Cantelli.
This file proves the deterministic part: if, for infinitely many `k`, the cells `H k` of the graph satisfy
The event of [18] **Lemma 2.7** and the conclusions of [18] **Proposition 2.10** for the three pairs used by
Lemma 3.4 at mesh `ε k → 0`, then the graph is recurrent. The probabilistic inputs (Proposition 2.10,
Lemma 2.7, the joint scaling) are hypotheses here and are proved elsewhere in this library; `ae_recurrent_of_summable`
packages the Borel–Cantelli step.

* `Theorem14Inputs H ε ρ ρ₁ q β β' α A`: the four inputs at mesh `ε` (`s = ε^β`, `δ = ε^q`, `w = ε^{β'}`,
  `η = ε^α`);
* `tendsto_lemma34Bound`: the error term of `lemma34` tends to `0` when `3β < q`, `2β < β'`, `2β < α`;
* `theorem14_recurrent` (**[18] Theorem 1.4, recurrence, conditional form**);
* `ae_recurrent_of_summable` (the Borel–Cantelli step: summable failure probabilities give a.s. recurrence);
* `matedCRT_adj_succ`, `matedCRT_connected` (the mated-CRT map of [18] (1.1) is connected; proved
  here, the frozen anchor `matedCRT_graph_connected` is not imported) and `theorem14_matedCRT_recurrent`
  (the conditional statement for the frozen `MatedCRT.graph ε ω h`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped ENNReal Topology

namespace MatedCRTHarmonic.GMS3

open LFMultigraph Harmonic

/-! ### Asymptotics of the Lemma 3.4 error term -/

section Asymptotics

variable {ε : ℕ → ℝ} (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
include hε hε0

end Asymptotics

/-- An algebraic form of `lemma34Bound` (`X = log(ρ/s)⁻¹`). -/
theorem lemma34Bound_eq {s ρ δ w A η : ℝ} (hs : 0 < s) (hℓ : Real.log (ρ / s) ≠ 0) :
    lemma34Bound s ρ δ w A η =
      3 * A * (2 * π) * (Real.log (ρ / s))⁻¹ + 3 * η +
      6 * ((Real.log (ρ / s))⁻¹) ^ 2 * (δ / s ^ 3) * (A * (π * ρ ^ 2) + η) +
      12 * ((Real.log (ρ / s))⁻¹) ^ 2 *
        (A * (8 * π) * (w / s + 4 * (w / s) ^ 2 + ρ * (w / s ^ 2)) + η / s ^ 2) +
      384 * ((Real.log (ρ / s))⁻¹) ^ 2 * (δ / s ^ 2) ^ 2 *
        ((A * (π * ρ ^ 2) + η) + (A * (8 * π * w * (s + 2 * w) + 8 * π * w * (ρ + 2 * w)) + η)) := by
  unfold lemma34Bound
  field_simp
  ring

/-! ### Theorem 1.4, conditional form -/

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

/-! ### The mated-CRT map -/

/-- Consecutive vertices of the mated-CRT map are adjacent ([18] (1.1): the edge `(x, x + 1)`). -/
theorem matedCRT_adj_succ (ε : ℝ) (ω : MatedCRT.Path2) (h : MatedCRT.IsLocallyFinite ε ω)
    (x : ℤ) : (MatedCRT.graph ε ω h).adj.Adj x (x + 1) := by
  refine adj_of_edge (MatedCRT.graph ε ω h) (e := ⟨(x, x + 1, false), lt_add_one x,
    Or.inl ⟨rfl, rfl⟩⟩) ?_
  show x ≠ x + 1
  omega

/-- **The mated-CRT map is connected** (proved here; the frozen anchor `matedCRT_graph_connected` is
not imported). -/
theorem matedCRT_connected (ε : ℝ) (ω : MatedCRT.Path2) (h : MatedCRT.IsLocallyFinite ε ω) :
    (MatedCRT.graph ε ω h).adj.Connected := by
  have hreach : ∀ n : ℤ, (MatedCRT.graph ε ω h).adj.Reachable 0 n := by
    intro n
    induction n using Int.induction_on with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ i ih => exact ih.trans (matedCRT_adj_succ ε ω h i).reachable
    | pred i ih =>
      refine ih.trans ?_
      have := (matedCRT_adj_succ ε ω h (-(i : ℤ) - 1)).reachable
      rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at this
      exact this.symm
  exact SimpleGraph.connected_iff_exists_forall_reachable _ |>.mpr ⟨0, hreach⟩

end MatedCRTHarmonic.GMS3
