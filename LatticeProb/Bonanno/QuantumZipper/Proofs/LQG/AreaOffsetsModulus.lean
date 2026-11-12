/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.AreaOffsetsModulus at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsets
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceAS
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
At an interior point `z` with `2ε ≤ Im z`, folded circles are genuine circles and
`d°_{aε}(z) = d°_{2ε}(z) · H(a)` with `H(a) = (a/2)^{γ²/2} e^{γ Φ(a)}`,
`Φ(a) = Z_{aε}(z) − Z_{2ε}(z)` independent of `Z_{2ε}(z)`. This is the boundary computation with
`γ ↦ 2γ` and all variances halved; the dyadic chaining of `AllOffsetsModulus` is reused.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace AreaOffsets

open BdryExist GaussTK TwoRadius TwoRadiusC AreaExist AllOffsets

theorem tilt_moment_bound2 {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    6 * exp x - 4 * exp (3 * x) + exp (6 * x) - 3 ≤ 339776 * x ^ 2 := by
  obtain ⟨u, hu⟩ : ∃ u, u = exp x - 1 := ⟨_, rfl⟩
  have ex : exp x = 1 + u := by linarith
  have hu0 : 0 ≤ u := by linarith [add_one_le_exp x]
  have hexp2 : exp x ≤ 8 := by
    have h1 := Real.exp_one_lt_d9
    have : exp x ≤ exp 1 ^ 2 := by
      rw [← exp_nat_mul]; exact exp_le_exp.2 (by push_cast; linarith)
    nlinarith [exp_pos 1]
  have hux : u ≤ 8 * x := by
    have h := add_one_le_exp (-x)
    have hm : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
    have : exp x * (1 - x) ≤ 1 := by
      calc exp x * (1 - x) = exp x * (-x + 1) := by ring
        _ ≤ exp x * exp (-x) := mul_le_mul_of_nonneg_left h (exp_pos _).le
        _ = 1 := hm
    nlinarith
  have hu7 : u ≤ 7 := by linarith
  have e3 : exp (3 * x) = exp x ^ 3 := by rw [← exp_nat_mul]; norm_num
  have e6 : exp (6 * x) = exp x ^ 6 := by rw [← exp_nat_mul]; norm_num
  rw [e3, e6, ex]
  have hpoly : 6 * (1 + u) - 4 * (1 + u) ^ 3 + (1 + u) ^ 6 - 3 =
      u ^ 2 * (3 + 16 * u + 15 * u ^ 2 + 6 * u ^ 3 + u ^ 4) := by ring
  rw [hpoly]
  have p2 := pow_le_pow_left₀ hu0 hu7 2
  have p3 := pow_le_pow_left₀ hu0 hu7 3
  have p4 := pow_le_pow_left₀ hu0 hu7 4
  have hb : 3 + 16 * u + 15 * u ^ 2 + 6 * u ^ 3 + u ^ 4 ≤ 5309 := by
    norm_num at p2 p3 p4; linarith
  have hu2sq : u ^ 2 ≤ 64 * x ^ 2 := by nlinarith
  calc u ^ 2 * (3 + 16 * u + 15 * u ^ 2 + 6 * u ^ 3 + u ^ 4) ≤ u ^ 2 * 5309 :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg u)
    _ ≤ 64 * x ^ 2 * 5309 := by nlinarith
    _ = 339776 * x ^ 2 := by ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end AreaOffsets
end QuantumZipper
