/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: MeshOnly/MeshOnlyHeatKernel.lean.
-/
import LatticeProb.Network.HeatPositivity
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The killed heat density on a finite network

For a finite network with conductance `c` and vertex masses `m`, the killed heat flow of a datum
`f` on a vertex set `S` solves the killed heat equation. The killed heat density at `x` is the
killed heat flow with datum `δ_x / m x`. The file shows that the density is symmetric on `S` and
nonnegative, that `m y` times the density is the killed heat matrix entry, that the weighted `L¹`
norm of the density is at most one, and that its weighted `L²` norm is the diagonal density at
twice the time. It also shows that the weighted square norm has derivative `-2` times the
Dirichlet energy of the density.
-/

open Matrix
open scoped BigOperators Matrix Matrix.Norms.Operator

namespace LatticeProb.Network

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The killed heat flow is a matrix-vector product, so its time derivative is the killed generator
matrix applied to the flow. This holds for every `c`, because the killed generator matrix vanishes
off `S` by construction. -/
private theorem hasDerivAt_killedHeatFlow_generatorMatrix (c : V → V → ℝ) (m : V → ℝ)
    (S : Set V) (f : V → ℝ) (t : ℝ) :
    HasDerivAt (killedHeatFlow c m S f)
      (killedGeneratorMatrix c m S *ᵥ killedHeatFlow c m S f t) t := by
  have h := ((Matrix.mulVecBilin (R := ℝ) (S := ℝ)).flip (S.indicator f)).toContinuousLinearMap
    |>.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_killedHeatMatrix c m S t)
  change HasDerivAt (fun s => killedHeatMatrix c m S s *ᵥ S.indicator f)
    ((killedGeneratorMatrix c m S * killedHeatMatrix c m S t) *ᵥ S.indicator f) t at h
  rw [← Matrix.mulVec_mulVec] at h
  exact h

/-- The killed heat flow vanishes outside `S`: the killed generator matrix has zero rows off `S`,
so each of its coordinates is constant in time and starts at zero. -/
theorem killedHeatFlow_eq_zero_of_not_mem (c : V → V → ℝ) (m : V → ℝ) (S : Set V) (f : V → ℝ)
    (t : ℝ) {v : V} (hv : v ∉ S) : killedHeatFlow c m S f t v = 0 := by
  have hrow (u : V → ℝ) : (killedGeneratorMatrix c m S *ᵥ u) v = 0 := by
    simp only [killedGeneratorMatrix, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      killingProjection_mulVec, Set.indicator_of_notMem hv]
  have hd (s : ℝ) : HasDerivAt (fun r => killedHeatFlow c m S f r v) 0 s := by
    have h := (hasDerivAt_pi.1 (hasDerivAt_killedHeatFlow_generatorMatrix c m S f s)) v
    rwa [hrow] at h
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa [killedHeatFlow_zero, hv] using hconst

/-- The killed heat flow is unchanged by the projection onto `S`. -/
theorem indicator_killedHeatFlow (c : V → V → ℝ) (m : V → ℝ) (S : Set V) (f : V → ℝ) (t : ℝ) :
    S.indicator (killedHeatFlow c m S f t) = killedHeatFlow c m S f t := by
  ext v
  by_cases hv : v ∈ S
  · simp [hv]
  · simp [hv, killedHeatFlow_eq_zero_of_not_mem c m S f t hv]

/-- The killed heat density at `x` with respect to the masses `m`: the killed heat flow of the
datum `δ_x / m x`. Multiplying its value at `y` by `m y` gives the killed heat matrix entry
`killedHeatMatrix c m S t x y`, by `mass_mul_killedHeatDensity`. -/
noncomputable def killedHeatDensity (c : V → V → ℝ) (m : V → ℝ) (S : Set V) (x : V) (t : ℝ) :
    V → ℝ :=
  killedHeatFlow c m S (Pi.single x (m x)⁻¹) t

/-- For `x ∈ S`, the killed heat density at `y` is the killed heat matrix entry `(y, x)` divided by
the mass `m x`. -/
theorem killedHeatDensity_apply (c : V → V → ℝ) (m : V → ℝ) (S : Set V) {x : V} (hx : x ∈ S)
    (t : ℝ) (y : V) :
    killedHeatDensity c m S x t y = killedHeatMatrix c m S t y x / m x := by
  have hi : S.indicator (Pi.single x (m x)⁻¹) = Pi.single x (m x)⁻¹ := by
    ext v
    by_cases hv : v = x
    · subst v; simp [hx]
    · simp [hv]
  simp [killedHeatDensity, killedHeatFlow, hi, Matrix.mulVec_single, div_eq_mul_inv]

section Heat

variable (G : SimpleGraph V) [G.LocallyFinite]

/-- The `v`-coordinate of the killed heat flow solves the killed heat equation at `v`. -/
theorem hasDerivAt_killedHeatFlow_apply {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (S : Set V) (f : V → ℝ) (t : ℝ) (v : V) :
    HasDerivAt (fun s => killedHeatFlow c m S f s v)
      (killedMassGenerator G c m S (killedHeatFlow c m S f t) v) t :=
  hasDerivAt_pi.1 (hasDerivAt_killedHeatFlow G hc m S f t) v

/-- Along the killed heat density at `x`, the weighted square norm `∑ m v * u v ^ 2` has derivative
`-2` times the Dirichlet energy of the density. -/
theorem hasDerivAt_killedHeatDensity_weighted_sq {c : V → V → ℝ} (hc : IsCond G c)
    (m : V → ℝ) (hm : ∀ v, m v ≠ 0) (S : Set V) (x : V) (t : ℝ) :
    HasDerivAt (fun s => ∑ v, m v * (killedHeatDensity c m S x s v)^2)
      (-2 * dirichletEnergy c (killedHeatDensity c m S x t)) t := by
  have h := hasDerivAt_weighted_sq_of_killed_heat G hc m hm S
    (killedHeatDensity c m S x) t (fun v =>
      hasDerivAt_killedHeatFlow_apply G hc m S (Pi.single x (m x)⁻¹) t v)
  simpa only [killedHeatDensity, indicator_killedHeatFlow] using h

/-- The killed generator matrix is reversible with respect to the masses `m`. -/
theorem killedGeneratorMatrix_isMassReversible {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, m v ≠ 0) (S : Set V) :
    IsMassReversible m (killedGeneratorMatrix c m S) := by
  intro v w
  have h := killedMassGenerator_symmetric G hc m hm S (Pi.single w 1) (Pi.single v 1)
  simp only [← killedGeneratorMatrix_mulVec G hc, Matrix.mulVec_single_one] at h
  simpa [Pi.single_apply, mul_ite, ite_mul, Matrix.col_apply] using h

/-- The killed heat matrix at every time is reversible with respect to the masses `m`. -/
theorem killedHeatMatrix_isMassReversible {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, m v ≠ 0) (S : Set V) (t : ℝ) :
    IsMassReversible m (killedHeatMatrix c m S t) :=
  ((killedGeneratorMatrix_isMassReversible G hc m hm S).smul t).exp

/-- The killed heat density is symmetric on the active set `S`. -/
theorem killedHeatDensity_symmetric {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, m v ≠ 0) (S : Set V) {x y : V} (hx : x ∈ S) (hy : y ∈ S) (t : ℝ) :
    killedHeatDensity c m S x t y = killedHeatDensity c m S y t x := by
  rw [killedHeatDensity_apply c m S hx, killedHeatDensity_apply c m S hy]
  apply (div_eq_div_iff (hm x) (hm y)).mpr
  have h := killedHeatMatrix_isMassReversible G hc m hm S t y x
  nlinarith only [h]

/-- The killed heat density at `x` is the killed heat matrix row at `x`, divided by the mass at
`y`. -/
theorem killedHeatDensity_eq_row {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, m v ≠ 0) (S : Set V) {x : V} (hx : x ∈ S) (t : ℝ) (y : V) :
    killedHeatDensity c m S x t y = killedHeatMatrix c m S t x y / m y := by
  rw [killedHeatDensity_apply c m S hx]
  apply (div_eq_div_iff (hm x) (hm y)).mpr
  have h := killedHeatMatrix_isMassReversible G hc m hm S t y x
  nlinarith only [h]

/-- Multiplying the killed heat density by the mass gives the killed heat matrix entry. -/
theorem mass_mul_killedHeatDensity {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, m v ≠ 0) (S : Set V) {x : V} (hx : x ∈ S) (t : ℝ) (y : V) :
    m y * killedHeatDensity c m S x t y = killedHeatMatrix c m S t x y := by
  rw [killedHeatDensity_eq_row G hc m hm S hx]
  field_simp [hm y]

/-- The killed heat density is nonnegative for nonnegative time. -/
theorem killedHeatDensity_nonneg {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (S : Set V) {x : V} (hx : x ∈ S) {t : ℝ} (ht : 0 ≤ t) (y : V) :
    0 ≤ killedHeatDensity c m S x t y := by
  rw [killedHeatDensity_apply c m S hx]
  exact div_nonneg ((killedHeatMatrix_isSubstochastic G hc m hm S ht).1 y x) (hm x).le

/-- The killed heat density is strictly positive on the diagonal for nonnegative time. -/
theorem killedHeatDensity_self_pos {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (S : Set V) {x : V} (hx : x ∈ S) {t : ℝ} (ht : 0 ≤ t) :
    0 < killedHeatDensity c m S x t x := by
  rw [killedHeatDensity_apply c m S hx]
  exact div_pos (killedHeatMatrix_diagonal_pos G hc m hm S ht x) (hm x)

/-- The killed density has weighted L1 norm at most one. -/
theorem killedHeatDensity_weighted_L1_le_one {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (S : Set V) {x : V} (hx : x ∈ S) {t : ℝ} (ht : 0 ≤ t) :
    (∑ y, m y * |killedHeatDensity c m S x t y|) ≤ 1 := by
  simp_rw [abs_of_nonneg (killedHeatDensity_nonneg G hc m hm S hx ht _),
    mass_mul_killedHeatDensity G hc m (fun v => (hm v).ne') S hx]
  exact (killedHeatMatrix_isSubstochastic G hc m hm S ht).2 x

/-- Self-adjointness and the semigroup law identify the squared L2 norm with exactly the diagonal
density at twice the time. -/
theorem killedHeatDensity_weighted_sq_eq_double {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, m v ≠ 0) (S : Set V) {x : V} (hx : x ∈ S) (t : ℝ) :
    (∑ y, m y * (killedHeatDensity c m S x t y)^2) =
      killedHeatDensity c m S x (2*t) x := by
  calc
    _ = ∑ y, killedHeatMatrix c m S t x y * killedHeatMatrix c m S t y x / m x := by
      apply Finset.sum_congr rfl
      intro y _
      rw [pow_two, ← mul_assoc, mass_mul_killedHeatDensity G hc m hm S hx,
        killedHeatDensity_apply c m S hx]
      ring
    _ = (killedHeatMatrix c m S t * killedHeatMatrix c m S t) x x / m x := by
      rw [Matrix.mul_apply, Finset.sum_div]
    _ = _ := by
      rw [killedHeatDensity_apply c m S hx, show 2*t = t+t by ring,
        killedHeatMatrix_add]

/-- The weighted squared L2 norm of the killed heat density is strictly positive. -/
theorem killedHeatDensity_weighted_sq_pos {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (S : Set V) {x : V} (hx : x ∈ S) {t : ℝ} (ht : 0 ≤ t) :
    0 < ∑ y, m y * (killedHeatDensity c m S x t y)^2 := by
  rw [killedHeatDensity_weighted_sq_eq_double G hc m (fun v => (hm v).ne') S hx]
  exact killedHeatDensity_self_pos G hc m hm S hx (by linarith)

/-- Cauchy-Schwarz converts the on-diagonal bound to the survival bound, with only the mass of the
active set in the prefactor. -/
theorem killedHeatDensity_survival_sq_le {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (S : Set V) {x : V} (hx : x ∈ S) (t : ℝ) :
    (∑ y, m y * killedHeatDensity c m S x t y)^2 ≤
      (∑ y, S.indicator m y) * killedHeatDensity c m S x (2*t) x := by
  have hout {y : V} (hy : y ∉ S) : killedHeatDensity c m S x t y = 0 :=
    killedHeatFlow_eq_zero_of_not_mem c m S _ t hy
  have hi (y : V) : S.indicator m y * killedHeatDensity c m S x t y =
      m y * killedHeatDensity c m S x t y := by
    by_cases hy : y ∈ S <;> simp [hy, hout]
  have hi2 (y : V) : S.indicator m y * (killedHeatDensity c m S x t y)^2 =
      m y * (killedHeatDensity c m S x t y)^2 := by
    by_cases hy : y ∈ S <;> simp [hy, hout]
  have h := LatticeProb.weighted_sum_sq_le (S.indicator m)
    (killedHeatDensity c m S x t) (fun y => by
      by_cases hy : y ∈ S <;> simp [hy, (hm y).le])
  simpa only [hi, hi2, killedHeatDensity_weighted_sq_eq_double G hc m (fun v => (hm v).ne') S hx]
    using h

end Heat

namespace KilledHeatDensityExample

open SimpleGraph

attribute [local instance] HeatGeneratorExample.pathLocallyFinite

/-- On the path `0 – 1 – 2` with unit conductance, unit mass and `S = {0, 1}`, the killed heat
density at `0` is nonnegative, so the hypotheses of `killedHeatDensity_nonneg` are jointly
satisfiable. -/
example {t : ℝ} (ht : 0 ≤ t) (y : Fin 3) :
    0 ≤ killedHeatDensity (unitCond (pathGraph 3)) (fun _ => (1 : ℝ)) {0, 1} 0 t y :=
  killedHeatDensity_nonneg (pathGraph 3) isCond_unitCond (fun _ => (1 : ℝ)) (fun _ => one_pos)
    {0, 1} (by simp) ht y

/-- On the same path, the killed heat density at `0` is strictly positive on the diagonal, so the
hypotheses of `killedHeatDensity_self_pos` are jointly satisfiable. -/
example {t : ℝ} (ht : 0 ≤ t) :
    0 < killedHeatDensity (unitCond (pathGraph 3)) (fun _ => (1 : ℝ)) {0, 1} 0 t 0 :=
  killedHeatDensity_self_pos (pathGraph 3) isCond_unitCond (fun _ => (1 : ℝ)) (fun _ => one_pos)
    {0, 1} (by simp) ht

/-- On the same path, the killed density has weighted L1 norm at most one, so the hypotheses of
`killedHeatDensity_weighted_L1_le_one` are jointly satisfiable. -/
example {t : ℝ} (ht : 0 ≤ t) :
    (∑ y : Fin 3, (1 : ℝ) * |killedHeatDensity (unitCond (pathGraph 3)) (fun _ => (1 : ℝ))
      {0, 1} 0 t y|) ≤ 1 :=
  killedHeatDensity_weighted_L1_le_one (pathGraph 3) isCond_unitCond (fun _ => (1 : ℝ))
    (fun _ => one_pos) {0, 1} (by simp) ht

/-- On the same path, the weighted squared L2 norm of the killed density is strictly positive, so
the hypotheses of `killedHeatDensity_weighted_sq_pos` are jointly satisfiable. -/
example {t : ℝ} (ht : 0 ≤ t) :
    0 < ∑ y : Fin 3, (1 : ℝ) * (killedHeatDensity (unitCond (pathGraph 3))
      (fun _ => (1 : ℝ)) {0, 1} 0 t y)^2 :=
  killedHeatDensity_weighted_sq_pos (pathGraph 3) isCond_unitCond (fun _ => (1 : ℝ))
    (fun _ => one_pos) {0, 1} (by simp) ht

end KilledHeatDensityExample

end LatticeProb.Network
