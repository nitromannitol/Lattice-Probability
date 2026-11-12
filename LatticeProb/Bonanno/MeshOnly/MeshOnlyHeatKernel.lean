/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MeshOnly.MeshOnlyHeatKernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MeshOnly.MeshOnlyHeatPositivity
import LatticeProb.Bonanno.MeshOnly.MeshOnlyHeatUniformization
import LatticeProb.Bonanno.MeshOnly.MeshOnlyHeatMatrixBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! The genuine finite killed heat density with respect to vertex masses. -/

open Matrix
open scoped BigOperators Matrix Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [DecidableEq V] (N : FiniteConductanceNetwork V)

lemma hasDerivAt_killedHeatFlow_apply (m : V → ℝ) (S : Set V) (f : V → ℝ)
    (t : ℝ) (v : V) :
    HasDerivAt (fun s => N.killedHeatFlow m S f s v)
      (N.killedMassGenerator m S (N.killedHeatFlow m S f t) v) t := by
  exact (ContinuousLinearMap.proj v).hasFDerivAt.comp_hasDerivAt t
    (N.hasDerivAt_killedHeatFlow m S f t)

lemma killedHeatFlow_eq_zero_of_not_mem (m : V → ℝ) (S : Set V) (f : V → ℝ)
    (t : ℝ) {v : V} (hv : v ∉ S) : N.killedHeatFlow m S f t v = 0 := by
  have hd (s : ℝ) : HasDerivAt (fun r => N.killedHeatFlow m S f r v) 0 s := by
    simpa only [N.killedMassGenerator_eq_zero_of_not_mem m S _ hv] using
      N.hasDerivAt_killedHeatFlow_apply m S f s v
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa [hv] using hconst

lemma indicator_killedHeatFlow (m : V → ℝ) (S : Set V) (f : V → ℝ) (t : ℝ) :
    S.indicator (N.killedHeatFlow m S f t) = N.killedHeatFlow m S f t := by
  ext v
  by_cases hv : v ∈ S
  · simp [hv]
  · simp [hv, N.killedHeatFlow_eq_zero_of_not_mem m S f t hv]

/-- The density of the killed heat flow started at `x`, measured relative to
`m`. For `x ∈ S`, the initial weighted mass is exactly one. -/
noncomputable def killedHeatDensity (m : V → ℝ) (S : Set V) (x : V) (t : ℝ) : V → ℝ :=
  N.killedHeatFlow m S (Pi.single x (m x)⁻¹) t

lemma killedHeatDensity_apply (m : V → ℝ) (S : Set V) {x : V} (hx : x ∈ S)
    (t : ℝ) (y : V) :
    N.killedHeatDensity m S x t y = N.killedHeatMatrix m S t y x / m x := by
  have hi : S.indicator (Pi.single x (m x)⁻¹) = Pi.single x (m x)⁻¹ := by
    ext v
    by_cases hv : v = x
    · subst v; simp [hx]
    · simp [Pi.single_eq_of_ne hv, hv]
  simp [killedHeatDensity, killedHeatFlow, hi, Matrix.mulVec_single, div_eq_mul_inv]

lemma hasDerivAt_killedHeatDensity_weighted_sq (m : V → ℝ) (hm : ∀ v, m v ≠ 0)
    (S : Set V) (x : V) (t : ℝ) :
    HasDerivAt (fun s => ∑ v, m v * (N.killedHeatDensity m S x s v)^2)
      (-2 * N.energy (N.killedHeatDensity m S x t)) t := by
  have h := N.hasDerivAt_weighted_sq_of_killed_heat m hm S
    (N.killedHeatDensity m S x) t (fun v =>
      N.hasDerivAt_killedHeatFlow_apply m S (Pi.single x (m x)⁻¹) t v)
  simpa only [killedHeatDensity, N.indicator_killedHeatFlow] using h

lemma killedGeneratorMatrix_isMassReversible (m : V → ℝ) (hm : ∀ v, m v ≠ 0)
    (S : Set V) : MeshOnlyHeat.IsMassReversible m (N.killedGeneratorMatrix m S) := by
  intro v w
  have h := N.killedMassGenerator_symmetric m hm S (Pi.single w 1) (Pi.single v 1)
  simp only [← N.killedGeneratorMatrix_mulVec, Matrix.mulVec_single_one] at h
  simpa [Pi.single_apply, mul_ite, ite_mul, Matrix.col_apply] using h

lemma killedHeatMatrix_isMassReversible (m : V → ℝ) (hm : ∀ v, m v ≠ 0)
    (S : Set V) (t : ℝ) : MeshOnlyHeat.IsMassReversible m (N.killedHeatMatrix m S t) :=
  ((N.killedGeneratorMatrix_isMassReversible m hm S).smul t).exp

lemma killedHeatDensity_symmetric (m : V → ℝ) (hm : ∀ v, m v ≠ 0)
    (S : Set V) {x y : V} (hx : x ∈ S) (hy : y ∈ S) (t : ℝ) :
    N.killedHeatDensity m S x t y = N.killedHeatDensity m S y t x := by
  rw [N.killedHeatDensity_apply m S hx, N.killedHeatDensity_apply m S hy]
  apply (div_eq_div_iff (hm x) (hm y)).mpr
  have h := N.killedHeatMatrix_isMassReversible m hm S t y x
  nlinarith only [h]


lemma killedHeatDensity_eq_row (m : V → ℝ) (hm : ∀ v, m v ≠ 0)
    (S : Set V) {x : V} (hx : x ∈ S) (t : ℝ) (y : V) :
    N.killedHeatDensity m S x t y = N.killedHeatMatrix m S t x y / m y := by
  rw [N.killedHeatDensity_apply m S hx]
  apply (div_eq_div_iff (hm x) (hm y)).mpr
  have h := N.killedHeatMatrix_isMassReversible m hm S t y x
  nlinarith only [h]

lemma mass_mul_killedHeatDensity (m : V → ℝ) (hm : ∀ v, m v ≠ 0)
    (S : Set V) {x : V} (hx : x ∈ S) (t : ℝ) (y : V) :
    m y * N.killedHeatDensity m S x t y = N.killedHeatMatrix m S t x y := by
  rw [N.killedHeatDensity_eq_row m hm S hx]
  field_simp [hm y]

lemma killedHeatDensity_nonneg (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) {x : V} (hx : x ∈ S) {t : ℝ} (ht : 0 ≤ t) (y : V) :
    0 ≤ N.killedHeatDensity m S x t y := by
  rw [N.killedHeatDensity_apply m S hx]
  exact div_nonneg ((N.killedHeatMatrix_isSubstochastic m hm S ht).1 y x) (hm x).le

lemma killedHeatDensity_self_pos (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) {x : V} (hx : x ∈ S) {t : ℝ} (ht : 0 ≤ t) :
    0 < N.killedHeatDensity m S x t x := by
  rw [N.killedHeatDensity_apply m S hx]
  exact div_pos (N.killedHeatMatrix_diagonal_pos m hm S ht x) (hm x)

/-- The killed density has weighted L1 norm at most one. -/
lemma killedHeatDensity_weighted_L1_le_one (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) {x : V} (hx : x ∈ S) {t : ℝ} (ht : 0 ≤ t) :
    (∑ y, m y * |N.killedHeatDensity m S x t y|) ≤ 1 := by
  simp_rw [abs_of_nonneg (N.killedHeatDensity_nonneg m hm S hx ht _),
    N.mass_mul_killedHeatDensity m (fun v => (hm v).ne') S hx]
  exact (N.killedHeatMatrix_isSubstochastic m hm S ht).2 x

/-- Self-adjointness and the semigroup law identify the squared L2 norm with
exactly the diagonal density at twice the time. -/
lemma killedHeatDensity_weighted_sq_eq_double (m : V → ℝ) (hm : ∀ v, m v ≠ 0)
    (S : Set V) {x : V} (hx : x ∈ S) (t : ℝ) :
    (∑ y, m y * (N.killedHeatDensity m S x t y)^2) =
      N.killedHeatDensity m S x (2*t) x := by
  calc
    _ = ∑ y, N.killedHeatMatrix m S t x y * N.killedHeatMatrix m S t y x / m x := by
      apply Finset.sum_congr rfl
      intro y _
      rw [pow_two, ← mul_assoc, N.mass_mul_killedHeatDensity m hm S hx,
        N.killedHeatDensity_apply m S hx]
      ring
    _ = (N.killedHeatMatrix m S t * N.killedHeatMatrix m S t) x x / m x := by
      rw [Matrix.mul_apply, Finset.sum_div]
    _ = _ := by
      rw [N.killedHeatDensity_apply m S hx, show 2*t = t+t by ring,
        N.killedHeatMatrix_add]

lemma killedHeatDensity_weighted_sq_pos (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) {x : V} (hx : x ∈ S) {t : ℝ} (ht : 0 ≤ t) :
    0 < ∑ y, m y * (N.killedHeatDensity m S x t y)^2 := by
  rw [N.killedHeatDensity_weighted_sq_eq_double m (fun v => (hm v).ne') S hx]
  exact N.killedHeatDensity_self_pos m hm S hx (by linarith)

/-- Cauchy-Schwarz converts the on-diagonal bound to the survival bound, with
only the mass of the active set (not the ambient finite network). -/
lemma killedHeatDensity_survival_sq_le (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) {x : V} (hx : x ∈ S) (t : ℝ) :
    (∑ y, m y * N.killedHeatDensity m S x t y)^2 ≤
      (∑ y, S.indicator m y) * N.killedHeatDensity m S x (2*t) x := by
  have hout {y : V} (hy : y ∉ S) : N.killedHeatDensity m S x t y = 0 :=
    N.killedHeatFlow_eq_zero_of_not_mem m S _ t hy
  have hi (y : V) : S.indicator m y * N.killedHeatDensity m S x t y =
      m y * N.killedHeatDensity m S x t y := by
    by_cases hy : y ∈ S <;> simp [hy, hout]
  have hi2 (y : V) : S.indicator m y * (N.killedHeatDensity m S x t y)^2 =
      m y * (N.killedHeatDensity m S x t y)^2 := by
    by_cases hy : y ∈ S <;> simp [hy, hout]
  have h := MeshOnlyHeat.weighted_sum_sq_le (S.indicator m)
    (N.killedHeatDensity m S x t) (fun y => by
      by_cases hy : y ∈ S <;> simp [hy, (hm y).le])
  simpa only [hi, hi2, N.killedHeatDensity_weighted_sq_eq_double m (fun v => (hm v).ne') S hx]
    using h

end BouRabeeGwynne.FiniteConductanceNetwork
