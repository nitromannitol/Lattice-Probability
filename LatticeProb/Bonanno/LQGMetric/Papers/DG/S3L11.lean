/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Det
import LatticeProb.Bonanno.LQGMetric.Perc.Peierls
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# DG Lemma 3.11 for a truncated-type field: the Peierls step (P2-DG105g)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.11 (`lem-rectangle-perc`,
DG:1189–1278), the truncated bound (eqn-rectangle-perc-truncated) (DG:1222–1225), at scale `s`
and offset `b` (D105 item 1, DV-D105-3).

DG's proof: (eqn-perc-prob) each `E_S^ε` has probability `≥ 1 − p` (L3.12 + translation
invariance); `E_S^ε` and `E_{S̃}^ε` are independent when `S(2) ∩ S̃(2) = ∅` (DG:1267), i.e. when the
sites are at `ℓ^∞`-distance `> 9`; the Peierls argument (DG:1265–1278, `perc_peierls`) gives a
left–right crossing of good squares outside an event of probability `≤ 2n (8θ)^{n−2}`; the chain
argument (`dgLGDSet_rect_le_of_goodLR`) bounds the distance by `2n² M`; monotonicity in `ε`
(DG:1260) gives the bound for all `ε > 0` with `A = M(ε_*)`.

Parameters: DG's `p < 8^{-100}` (with `|P|/100` disjoint `S(2)`'s) is `p = 32^{-100}` here
(`θ = 1/32`, residue classes mod `10`, `(r+1)² = 100`, `perc_peierls`; D116, DG:1269–1276); `a₀ = 32`, `a₁ = log 2`.

The two probabilistic inputs (each `E_S^ε` likely; far `E_S^ε` independent) are hypotheses
`hgood`, `hind`: for `μ = μ_{ĥ^tr}` they are DG Lemma 3.12 transported to every grid square by
translation invariance in law (DG:1243), and the locality of `E_S^ε` (DG:1267) — see
handoff/P2-DG105g.md.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `2n (1/4)^{n−2} ≤ 32 · 2^{−n}` -/
lemma l311_num (m : ℕ) :
    (2 * ((m + 2 : ℕ) : ℝ)) * (1 / 4 : ℝ) ^ m ≤ 32 * (2 : ℝ)⁻¹ ^ (m + 2) := by
  have hm : (m : ℝ) + 2 ≤ 4 * 2 ^ m := by
    have := Nat.lt_two_pow_self (n := m)
    have h2 : m + 2 ≤ 4 * 2 ^ m := by
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
    exact_mod_cast h2
  have e1 : (1 / 4 : ℝ) ^ m = (2 : ℝ)⁻¹ ^ m * (2 : ℝ)⁻¹ ^ m := by
    rw [← mul_pow]; norm_num
  have e2 : (2 : ℝ)⁻¹ ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
  have hp : 0 < (2 : ℝ)⁻¹ ^ m := by positivity
  rw [e1, pow_add]
  push_cast
  have : (2 * ((m : ℝ) + 2)) * ((2 : ℝ)⁻¹ ^ m * (2 : ℝ)⁻¹ ^ m) ≤
      (2 * (4 * 2 ^ m)) * ((2 : ℝ)⁻¹ ^ m * (2 : ℝ)⁻¹ ^ m) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  calc _ ≤ (2 * (4 * 2 ^ m)) * ((2 : ℝ)⁻¹ ^ m * (2 : ℝ)⁻¹ ^ m) := this
    _ = 8 * ((2 : ℝ)⁻¹ ^ m * 2 ^ m) * (2 : ℝ)⁻¹ ^ m := by ring
    _ = 32 * ((2 : ℝ)⁻¹ ^ m * (2 : ℝ)⁻¹ ^ 2) := by rw [e2]; ring

end DG
end LQGMetric
