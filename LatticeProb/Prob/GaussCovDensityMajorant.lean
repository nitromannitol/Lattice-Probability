/-
# Uniform Gaussian majorants of the density along the smart path

Li--Shao normal comparison, route item 3 (`scratch/pk/normalcompare-route.md`).  The orthant
probability `t ↦ ∫_{x ≤ b} covDensity (S_t) x dx` along the smart path
`S_t = (1 - t) • (v • 1) + t • S` (`LatticeProb.normalComparisonSmartPath`) is differentiated
under the integral sign by `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
which needs a dominating integrable function that is uniform in `t` near the base point.  This
file supplies it on `t ∈ [0, T]`, `T < 1` (the endpoint `t = 1` may be singular).

Write `q x = ∑ k, x k ^ 2`.  For `v > 0`, `S` positive semidefinite, `T ∈ [0, 1)`:

* `exists_precision_form_ge`: `x ⬝ᵥ (S_t⁻¹ *ᵥ x) ≥ c * q x` for all `t ∈ [0, T]`.  Route:
  Cauchy--Schwarz for the positive definite form `M = S_t`, in the form
  `(x ⬝ᵥ x)² ≤ (x ⬝ᵥ M⁻¹ x) (x ⬝ᵥ M x)` (`sq_dotProduct_self_le_precision_mul`; proved by the
  discriminant of `s ↦ (M⁻¹x + s x) ⬝ᵥ M (M⁻¹x + s x) ≥ 0`), together with the upper bound
  `x ⬝ᵥ S_t x ≤ (v + L) q x`, `L = ∑ i j, |S i j|`; so `c = 1 / (v + L)`.
* `exists_det_inv_bounds`: `D⁻¹ ≤ det S_t` and `|S_t⁻¹ i j| ≤ D` on `[0, T]`, by compactness of
  `[0, T]` and continuity of `t ↦ det S_t`, `t ↦ S_t⁻¹ i j = (det S_t)⁻¹ * adj S_t i j`.
* `exists_covDensity_path_majorant`: `covDensity S_t x ≤ C * exp (-(c * q x))`.
* `exists_partial2_path_majorant`: the second partials
  `((S_t⁻¹ x)_i (S_t⁻¹ x)_j - S_t⁻¹ i j) * covDensity S_t x` are bounded by
  `C * (1 + q x) * exp (-(c * q x))`, using `|(S_t⁻¹ x)_i| ≤ D ∑ |x_k|` and
  `(∑ |x_k|)² ≤ n q x`.
-/
import Mathlib
import LatticeProb.Prob.GaussCovDensity
import LatticeProb.Prob.NormalComparisonPath

open Matrix

namespace LatticeProb

/-! ### Cauchy--Schwarz for the precision form -/

/-- **Cauchy--Schwarz for a positive definite form.**  For `M` positive definite,
`x ⬝ᵥ M⁻¹ x ≥ 0` and `(x ⬝ᵥ x)² ≤ (x ⬝ᵥ M⁻¹ x) (x ⬝ᵥ M x)`. -/
theorem sq_dotProduct_self_le_precision_mul {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ (M⁻¹ *ᵥ x) ∧ (x ⬝ᵥ x) ^ 2 ≤ (x ⬝ᵥ (M⁻¹ *ᵥ x)) * (x ⬝ᵥ (M *ᵥ x)) := by
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.2 hM.det_pos.ne'
  have hMy : M *ᵥ (M⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hsymm : ∀ u w : Fin n → ℝ, u ⬝ᵥ (M *ᵥ w) = w ⬝ᵥ (M *ᵥ u) := by
    intro u w
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      ← Matrix.conjTranspose_eq_transpose_of_trivial, hM.1.eq, dotProduct_comm]
  have hpsd : ∀ z : Fin n → ℝ, 0 ≤ z ⬝ᵥ (M *ᵥ z) := fun z => by
    simpa using hM.posSemidef.dotProduct_mulVec_nonneg z
  generalize M⁻¹ *ᵥ x = y at hMy ⊢
  have hyy : y ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ y := by rw [hMy, dotProduct_comm]
  have hyx : y ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ x := by rw [hsymm, hMy]
  have hxy : x ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ x := by rw [hMy]
  refine ⟨by rw [← hyy]; exact hpsd y, ?_⟩
  have key : ∀ s : ℝ, 0 ≤ (x ⬝ᵥ (M *ᵥ x)) * (s * s) + (2 * (x ⬝ᵥ x)) * s + x ⬝ᵥ y := by
    intro s
    have h := hpsd (y + s • x)
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, hyy, hyx, hxy] at h
    nlinarith [h]
  have hd := discrim_le_zero key
  simp only [discrim] at hd
  nlinarith [hd]

/-! ### The quadratic form of the smart path -/

/-- `x ⬝ᵥ x` is the sum of squares `∑ k, x k ^ 2`. -/
theorem dotProduct_self_eq_sum_sq {n : ℕ} (x : Fin n → ℝ) : x ⬝ᵥ x = ∑ k, x k ^ 2 := by
  simp [dotProduct, sq]

/-- Crude upper bound for a quadratic form: for any real matrix `S`,
`x ⬝ᵥ S x ≤ (∑ i j, |S i j|) * ∑ k, x k ^ 2`. -/
theorem dotProduct_mulVec_le_sum_abs_mul {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    x ⬝ᵥ (S *ᵥ x) ≤ (∑ i, ∑ j, |S i j|) * ∑ k, x k ^ 2 := by
  have hq : ∀ k, x k ^ 2 ≤ ∑ k, x k ^ 2 := fun k =>
    Finset.single_le_sum (f := fun k => x k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ k)
  have hterm : ∀ i j, x i * (S i j * x j) ≤ |S i j| * ∑ k, x k ^ 2 := by
    intro i j
    have h1 : |x i * x j| ≤ ∑ k, x k ^ 2 := by
      have hi := hq i
      have hj := hq j
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (x i - x j), sq_nonneg (x i + x j)]
    calc x i * (S i j * x j) = S i j * (x i * x j) := by ring
      _ ≤ |S i j * (x i * x j)| := le_abs_self _
      _ = |S i j| * |x i * x j| := abs_mul _ _
      _ ≤ |S i j| * ∑ k, x k ^ 2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  calc x ⬝ᵥ (S *ᵥ x) = ∑ i, ∑ j, x i * (S i j * x j) := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, |S i j| * ∑ k, x k ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = (∑ i, ∑ j, |S i j|) * ∑ k, x k ^ 2 := by simp only [Finset.sum_mul]

/-- Upper bound for the quadratic form of the smart path, uniform in `t ∈ [0,1]`:
`x ⬝ᵥ S_t x ≤ (v + ∑ i j, |S i j|) * ∑ k, x k ^ 2`. -/
theorem smartPath_dotProduct_mulVec_le {n : ℕ} {v : ℝ} (hv : 0 < v)
    (S : Matrix (Fin n) (Fin n) ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Fin n → ℝ) :
    x ⬝ᵥ (normalComparisonSmartPath v S t *ᵥ x)
      ≤ (v + ∑ i, ∑ j, |S i j|) * ∑ k, x k ^ 2 := by
  have hL : 0 ≤ ∑ i, ∑ j, |S i j| := by positivity
  have hq : 0 ≤ ∑ k, x k ^ 2 := by positivity
  have h := dotProduct_mulVec_le_sum_abs_mul S x
  have heq : x ⬝ᵥ (normalComparisonSmartPath v S t *ᵥ x)
      = (1 - t) * v * ∑ k, x k ^ 2 + t * (x ⬝ᵥ (S *ᵥ x)) := by
    simp only [normalComparisonSmartPath, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul,
      dotProduct_self_eq_sum_sq]
    ring
  rw [heq]
  have h2 := mul_le_mul_of_nonneg_left h ht.1
  nlinarith [mul_nonneg ht.1 (mul_nonneg hv.le hq),
    mul_nonneg (sub_nonneg.2 ht.2) (mul_nonneg hL hq)]

/-! ### Target 1: uniform lower bound of the precision form -/

/-- Uniform quadratic lower bound for the precision form along the path:
`x ⬝ᵥ (S_t⁻¹ *ᵥ x) ≥ c * ∑ k, x k ^ 2` for all `t ∈ [0,T]`, `T < 1`. -/
theorem exists_precision_form_ge {n : ℕ} (v : ℝ) (hv : 0 < v) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosSemidef) {T : ℝ} (hT : T ∈ Set.Ico (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : Fin n → ℝ,
      c * ∑ k, x k ^ 2 ≤ x ⬝ᵥ ((normalComparisonSmartPath v S t)⁻¹ *ᵥ x) := by
  have hL : 0 ≤ ∑ i, ∑ j, |S i j| := by positivity
  have hΛ : 0 < v + ∑ i, ∑ j, |S i j| := by linarith
  refine ⟨(v + ∑ i, ∑ j, |S i j|)⁻¹, inv_pos.2 hΛ, fun t ht x => ?_⟩
  have htI : t ∈ Set.Ico (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_lt ht.2 hT.2⟩
  have hPD := normalComparisonSmartPath_posDef hS hv htI
  obtain ⟨hP, hCS⟩ := sq_dotProduct_self_le_precision_mul hPD x
  have hup := smartPath_dotProduct_mulVec_le hv S ⟨ht.1, htI.2.le⟩ x
  rw [dotProduct_self_eq_sum_sq] at hCS
  generalize x ⬝ᵥ ((normalComparisonSmartPath v S t)⁻¹ *ᵥ x) = P at hP hCS ⊢
  generalize v + ∑ i, ∑ j, |S i j| = Λ at hΛ hup ⊢
  have hq : 0 ≤ ∑ k, x k ^ 2 := by positivity
  generalize ∑ k, x k ^ 2 = q at hq hCS hup ⊢
  rcases hq.eq_or_lt with h0 | hpos
  · rw [← h0]; simpa using hP
  · have h1 : q ^ 2 ≤ P * (Λ * q) := hCS.trans (mul_le_mul_of_nonneg_left hup hP)
    have h2 : q * q ≤ (P * Λ) * q := by nlinarith
    have h3 : q ≤ P * Λ := le_of_mul_le_mul_right h2 hpos
    rw [inv_mul_le_iff₀ hΛ]
    linarith

/-! ### Target 2: uniform determinant lower bound and inverse-entry bound -/

/-- Uniform bound of the determinant factor and of the entries of the inverse along the path,
`t ∈ [0,T]`, `T < 1`: `D⁻¹ ≤ det S_t` and `|S_t⁻¹ i j| ≤ D`. -/
theorem exists_det_inv_bounds {n : ℕ} (v : ℝ) (hv : 0 < v) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosSemidef) {T : ℝ} (hT : T ∈ Set.Ico (0 : ℝ) 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
      D⁻¹ ≤ (normalComparisonSmartPath v S t).det ∧
      ∀ i j, |(normalComparisonSmartPath v S t)⁻¹ i j| ≤ D := by
  have hdetpos : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < (normalComparisonSmartPath v S t).det :=
    fun t ht =>
      (normalComparisonSmartPath_posDef hS hv ⟨ht.1, lt_of_le_of_lt ht.2 hT.2⟩).det_pos
  have hcm : Continuous (normalComparisonSmartPath v S) :=
    continuous_matrix (continuous_normalComparisonSmartPath_apply v S)
  have hdc : Continuous fun t => (normalComparisonSmartPath v S t).det := hcm.matrix_det
  obtain ⟨a, ha, ha'⟩ :=
    isCompact_Icc.exists_forall_le' (a := 0) hdc.continuousOn hdetpos
  have hinv : ContinuousOn
      (fun t => ∑ i, ∑ j, |(normalComparisonSmartPath v S t)⁻¹ i j|) (Set.Icc 0 T) := by
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    have hentry : ∀ t, (normalComparisonSmartPath v S t)⁻¹ i j
        = ((normalComparisonSmartPath v S t).det)⁻¹ *
          (normalComparisonSmartPath v S t).adjugate i j := by
      intro t
      rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    simp_rw [hentry]
    exact ((hdc.continuousOn.inv₀ fun t ht => (hdetpos t ht).ne').mul
      (hcm.matrix_adjugate.matrix_elem i j).continuousOn).abs
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hinv
  refine ⟨a⁻¹ + |B| + 1, by positivity, fun t ht => ⟨?_, fun i j => ?_⟩⟩
  · have h1 : (a⁻¹ + |B| + 1)⁻¹ ≤ a⁻¹⁻¹ :=
      inv_anti₀ (inv_pos.2 ha) (by linarith [abs_nonneg B])
    rw [inv_inv] at h1
    exact h1.trans (ha' t ht)
  · have h1 : |(normalComparisonSmartPath v S t)⁻¹ i j|
        ≤ ∑ j', |(normalComparisonSmartPath v S t)⁻¹ i j'| :=
      Finset.single_le_sum (f := fun j' => |(normalComparisonSmartPath v S t)⁻¹ i j'|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : ∑ j', |(normalComparisonSmartPath v S t)⁻¹ i j'|
        ≤ ∑ i', ∑ j', |(normalComparisonSmartPath v S t)⁻¹ i' j'| :=
      Finset.single_le_sum (f := fun i' => ∑ j', |(normalComparisonSmartPath v S t)⁻¹ i' j'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h3 := hB t ht
    rw [Real.norm_eq_abs] at h3
    have h4 := le_abs_self B
    have h5 := le_abs_self
      (∑ i', ∑ j', |(normalComparisonSmartPath v S t)⁻¹ i' j'|)
    have h6 : 0 < a⁻¹ := inv_pos.2 ha
    linarith

/-! ### Target 3: uniform Gaussian majorant of the density -/

/-- **Uniform Gaussian majorant of the density** along the smart path, `t ∈ [0,T]`, `T < 1`:
`covDensity S_t x ≤ C * exp (-(c * ∑ k, x k ^ 2))`. -/
theorem exists_covDensity_path_majorant {n : ℕ} (v : ℝ) (hv : 0 < v)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) {T : ℝ} (hT : T ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : Fin n → ℝ,
      covDensity (normalComparisonSmartPath v S t) x ≤ C * Real.exp (-(c * ∑ k, x k ^ 2)) := by
  obtain ⟨c, hc, hcx⟩ := exists_precision_form_ge v hv S hS hT
  obtain ⟨D, hD, hDb⟩ := exists_det_inv_bounds v hv S hS hT
  have h2pi : 0 < 2 * Real.pi := by positivity [Real.pi_pos]
  refine ⟨(2 * Real.pi) ^ (-(n : ℝ) / 2) * (D⁻¹) ^ (-(1 : ℝ) / 2), c / 2,
    mul_pos (Real.rpow_pos_of_pos h2pi _) (Real.rpow_pos_of_pos (inv_pos.2 hD) _),
    half_pos hc, fun t ht x => ?_⟩
  have hdet : (normalComparisonSmartPath v S t).det ^ (-(1 : ℝ) / 2) ≤ (D⁻¹) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos (inv_pos.2 hD) (hDb t ht).1 (by norm_num)
  have hexp : Real.exp (-(x ⬝ᵥ ((normalComparisonSmartPath v S t)⁻¹ *ᵥ x)) / 2)
      ≤ Real.exp (-(c / 2 * ∑ k, x k ^ 2)) := by
    apply Real.exp_le_exp.2
    linarith [hcx t ht x]
  unfold covDensity
  have hpos1 : 0 ≤ (2 * Real.pi) ^ (-(n : ℝ) / 2) := (Real.rpow_pos_of_pos h2pi _).le
  exact mul_le_mul (mul_le_mul_of_nonneg_left hdet hpos1) hexp (Real.exp_pos _).le
    (mul_nonneg hpos1 (Real.rpow_pos_of_pos (inv_pos.2 hD) _).le)

/-! ### Target 4: uniform majorant of the second partials -/

/-- If all entries of `K` are bounded by `D`, each coordinate of `K *ᵥ x` is bounded by
`D * ∑ k, |x k|`. -/
theorem abs_mulVec_le_mul_sum_abs {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {D : ℝ}
    (hK : ∀ i j, |K i j| ≤ D) (x : Fin n → ℝ) (i : Fin n) :
    |(K *ᵥ x) i| ≤ D * ∑ k, |x k| := by
  calc |(K *ᵥ x) i| = |∑ k, K i k * x k| := by simp only [Matrix.mulVec, dotProduct]
    _ ≤ ∑ k, |K i k * x k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |K i k| * |x k| := by simp only [abs_mul]
    _ ≤ ∑ k, D * |x k| :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hK i k) (abs_nonneg _)
    _ = D * ∑ k, |x k| := (Finset.mul_sum _ _ _).symm

/-- If all entries of `K` are bounded by `D`, any product of two coordinates of `K *ᵥ x` is
bounded by `D ^ 2 * n * ∑ k, x k ^ 2`. -/
theorem abs_mulVec_mul_mulVec_le {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {D : ℝ}
    (hK : ∀ i j, |K i j| ≤ D) (x : Fin n → ℝ) (i j : Fin n) :
    |(K *ᵥ x) i * (K *ᵥ x) j| ≤ D ^ 2 * n * ∑ k, x k ^ 2 := by
  have hD : 0 ≤ D := (abs_nonneg _).trans (hK i i)
  have hs : (∑ k, |x k|) ^ 2 ≤ n * ∑ k, x k ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => |x k|)
    simpa [sq_abs] using h
  have hsq : ∀ l, ((K *ᵥ x) l) ^ 2 ≤ D ^ 2 * n * ∑ k, x k ^ 2 := by
    intro l
    have h1 := abs_mulVec_le_mul_sum_abs hK x l
    have h2 : ((K *ᵥ x) l) ^ 2 ≤ (D * ∑ k, |x k|) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc ((K *ᵥ x) l) ^ 2 ≤ (D * ∑ k, |x k|) ^ 2 := h2
      _ = D ^ 2 * (∑ k, |x k|) ^ 2 := by ring
      _ ≤ D ^ 2 * (n * ∑ k, x k ^ 2) := mul_le_mul_of_nonneg_left hs (sq_nonneg D)
      _ = D ^ 2 * n * ∑ k, x k ^ 2 := by ring
  have hi := hsq i
  have hj := hsq j
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ((K *ᵥ x) i - (K *ᵥ x) j),
    sq_nonneg ((K *ᵥ x) i + (K *ᵥ x) j)]

/-- **Uniform majorant of the second partials** of the density along the smart path,
`t ∈ [0,T]`, `T < 1`:
`|((S_t⁻¹ x)_i (S_t⁻¹ x)_j - S_t⁻¹ i j) * covDensity S_t x|
  ≤ C * (1 + ∑ k, x k ^ 2) * exp (-(c * ∑ k, x k ^ 2))`. -/
theorem exists_partial2_path_majorant {n : ℕ} (v : ℝ) (hv : 0 < v)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) {T : ℝ} (hT : T ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : Fin n → ℝ, ∀ i j : Fin n,
      |(((normalComparisonSmartPath v S t)⁻¹ *ᵥ x) i
          * ((normalComparisonSmartPath v S t)⁻¹ *ᵥ x) j
          - (normalComparisonSmartPath v S t)⁻¹ i j)
          * covDensity (normalComparisonSmartPath v S t) x|
        ≤ C * (1 + ∑ k, x k ^ 2) * Real.exp (-(c * ∑ k, x k ^ 2)) := by
  obtain ⟨C₁, c, hC₁, hc, hmaj⟩ := exists_covDensity_path_majorant v hv S hS hT
  obtain ⟨D, hD, hDb⟩ := exists_det_inv_bounds v hv S hS hT
  refine ⟨(D ^ 2 * n + D) * C₁, c, by positivity, hc, fun t ht x i j => ?_⟩
  have hPD := normalComparisonSmartPath_posDef hS hv ⟨ht.1, lt_of_le_of_lt ht.2 hT.2⟩
  have hdens := covDensity_pos hPD x
  have hmajt := hmaj t ht x
  have hq : 0 ≤ ∑ k, x k ^ 2 := by positivity
  have hK := (hDb t ht).2
  have h1 := abs_mulVec_mul_mulVec_le hK x i j
  have hKij := hK i j
  generalize covDensity (normalComparisonSmartPath v S t) x = ρ at hdens hmajt ⊢
  generalize (normalComparisonSmartPath v S t)⁻¹ = K at h1 hKij ⊢
  generalize ∑ k, x k ^ 2 = q at hq h1 hmajt ⊢
  generalize (K *ᵥ x) i * (K *ᵥ x) j = A at h1 ⊢
  have h2 : |A - K i j| ≤ (D ^ 2 * n + D) * (1 + q) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc |A - K i j| ≤ |A| + |K i j| := abs_sub _ _
      _ ≤ D ^ 2 * n * q + D := add_le_add h1 hKij
      _ ≤ (D ^ 2 * n + D) * (1 + q) := by
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg D) hn) hq, mul_nonneg hD.le hq]
  rw [abs_mul, abs_of_pos hdens]
  calc |A - K i j| * ρ ≤ ((D ^ 2 * n + D) * (1 + q)) * (C₁ * Real.exp (-(c * q))) :=
        mul_le_mul h2 hmajt hdens.le (by positivity)
    _ = (D ^ 2 * n + D) * C₁ * (1 + q) * Real.exp (-(c * q)) := by ring

end LatticeProb
