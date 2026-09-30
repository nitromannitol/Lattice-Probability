/-
The smooth (log-sum-exp) maximum and minimum of a finite family of reals: their
order bounds, their uniform stability under a perturbation of the inputs, and
dimension-independent bounds on the sums of their first, second and third
coordinate derivatives.  These are analytic primitives, stated for a bare
`Fintype ι`, with no reference to any model.

Moved from Divisible-Sandpile-Percolation, `Sandpile/Support/SoftMaximum.lean`.
-/
import Mathlib

open scoped BigOperators

namespace LatticeProb

/-- The smooth maximum at inverse temperature `β`: `log(∑ exp(β xᵢ)) / β`. As
`β → ∞` this converges to `max_i x i`. -/
noncomputable def softMaximum {ι : Type*} [Fintype ι] (β : ℝ) (x : ι → ℝ) : ℝ :=
  Real.log (∑ i, Real.exp (β * x i)) / β

/-- The Gibbs (softmax) weight of coordinate `i` at inverse temperature `β`. -/
noncomputable def softWeight {ι : Type*} [Fintype ι] (β : ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (β * x i) / ∑ j, Real.exp (β * x j)

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The normalizing sum of exponentials is positive. -/
theorem sum_exp_pos (β : ℝ) (x : ι → ℝ) : 0 < ∑ i, Real.exp (β * x i) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- Every softmax weight is positive. -/
theorem softWeight_pos (β : ℝ) (x : ι → ℝ) (i : ι) : 0 < softWeight β x i :=
  div_pos (Real.exp_pos _) (sum_exp_pos β x)

/-- The softmax weights sum to `1`: they form a probability distribution on `ι`. -/
theorem sum_softWeight (β : ℝ) (x : ι → ℝ) : ∑ i, softWeight β x i = 1 := by
  simp only [softWeight, ← Finset.sum_div, div_self (sum_exp_pos β x).ne']

/-- Every coordinate is at most the smooth maximum, when `β > 0`. -/
theorem le_softMaximum {β : ℝ} (hβ : 0 < β) (x : ι → ℝ) (i : ι) :
    x i ≤ softMaximum β x := by
  rw [softMaximum, le_div_iff₀ hβ, mul_comm]
  apply (Real.le_log_iff_exp_le (sum_exp_pos β x)).2
  exact Finset.single_le_sum (fun j _ => (Real.exp_pos (β * x j)).le) (Finset.mem_univ i)

/-- The smooth maximum exceeds any common upper bound `M` on the coordinates
by at most `log(card ι) / β`. -/
theorem softMaximum_le {β : ℝ} (hβ : 0 < β) (x : ι → ℝ) (M : ℝ) (hM : ∀ i, x i ≤ M) :
    softMaximum β x ≤ M + Real.log (Fintype.card ι) / β := by
  have hc : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [softMaximum, div_le_iff₀ hβ]
  have hs : ∑ i, Real.exp (β * x i) ≤ (Fintype.card ι : ℝ) * Real.exp (β * M) := by
    calc
      _ ≤ ∑ _ : ι, Real.exp (β * M) := Finset.sum_le_sum fun i _ =>
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hM i) hβ.le)
      _ = _ := by simp
  have hl := Real.log_le_log (sum_exp_pos β x) hs
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  calc
    _ ≤ Real.log (Fintype.card ι) + β * M := hl
    _ = _ := by field_simp; ring

/-- The smooth maximum is monotone in the input, for `β > 0`. -/
theorem softMaximum_mono {β : ℝ} (hβ : 0 < β) {x y : ι → ℝ} (h : ∀ i, x i ≤ y i) :
    softMaximum β x ≤ softMaximum β y := by
  apply div_le_div_of_nonneg_right _ hβ.le
  apply Real.log_le_log (sum_exp_pos β x)
  exact Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (h i) hβ.le)

/-- The smooth maximum shifts by a common additive constant. -/
theorem softMaximum_add_const {β : ℝ} (hβ : β ≠ 0) (x : ι → ℝ) (c : ℝ) :
    softMaximum β (fun i => x i + c) = softMaximum β x + c := by
  simp only [softMaximum, mul_add, Real.exp_add, ← Finset.sum_mul]
  rw [Real.log_mul (sum_exp_pos β x).ne' (Real.exp_pos _).ne', Real.log_exp]
  field_simp

/-- The smooth maximum is `1`-Lipschitz for the sup norm: perturbing every
coordinate by at most `a` moves it by at most `a`. -/
theorem abs_softMaximum_sub_le {β : ℝ} (hβ : 0 < β) {x y : ι → ℝ} {a : ℝ}
    (h : ∀ i, |x i - y i| ≤ a) : |softMaximum β x - softMaximum β y| ≤ a := by
  have hu : softMaximum β x ≤ softMaximum β y + a := by
    rw [← softMaximum_add_const hβ.ne' y a]
    apply softMaximum_mono hβ
    intro i
    linarith [(abs_le.mp (h i)).2]
  have hl : softMaximum β y ≤ softMaximum β x + a := by
    rw [← softMaximum_add_const hβ.ne' x a]
    apply softMaximum_mono hβ
    intro i
    linarith [(abs_le.mp (h i)).1]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The smooth maximum is `C^∞` in the input, for any fixed `β`. -/
theorem contDiff_softMaximum (β : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (softMaximum (ι := ι) β) := by
  apply ContDiff.div_const
  apply ContDiff.log
  · exact ContDiff.sum fun i _ => (contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp
  · exact fun x => (sum_exp_pos β x).ne'

/-- The gradient of the smooth maximum is the vector of softmax weights. -/
theorem hasFDerivAt_softMaximum {β : ℝ} (hβ : β ≠ 0) (x : ι → ℝ) :
    HasFDerivAt (softMaximum β) (∑ i, softWeight β x i • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x := by
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((hasFDerivAt_apply i x).const_mul β).exp)
  convert (hs.log (sum_exp_pos β x).ne').const_mul β⁻¹ using 1 <;> try rfl
  · ext y; exact inv_mul_eq_div _ _ |>.symm
  ext y
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    softWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

/-- The softmax weight of `i` equals `exp(β (xᵢ - softMaximum β x))`: the
soft maximum is the natural centering constant for the Gibbs weights. -/
theorem softWeight_eq_exp {β : ℝ} (hβ : β ≠ 0) (x : ι → ℝ) (i : ι) :
    softWeight β x i = Real.exp (β * (x i - softMaximum β x)) := by
  have he : β * softMaximum β x = Real.log (∑ j, Real.exp (β * x j)) := by
    unfold softMaximum
    field_simp
  rw [mul_sub, he, Real.exp_sub, Real.exp_log (sum_exp_pos β x)]
  rfl

/-- The gradient of a single softmax weight, as a linear functional. -/
theorem hasFDerivAt_softWeight {β : ℝ} (hβ : β ≠ 0) (x : ι → ℝ) (i : ι) :
    HasFDerivAt (fun y => softWeight β y i)
      ((β * softWeight β x i) • ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) -
        ∑ j, softWeight β x j • ContinuousLinearMap.proj j)) x := by
  have h := (((hasFDerivAt_apply i x).sub (hasFDerivAt_softMaximum hβ x)).const_mul β).exp
  simpa only [Pi.sub_apply, ← softWeight_eq_exp hβ, smul_smul,
    mul_comm (softWeight β x i) β] using h

/-- The `i`-th coordinate partial derivative of the smooth maximum is the
`i`-th softmax weight. -/
theorem fderiv_softMaximum_single [DecidableEq ι] {β : ℝ} (hβ : β ≠ 0)
    (x : ι → ℝ) (i : ι) :
    fderiv ℝ (softMaximum β) x (Pi.single i 1) = softWeight β x i := by
  rw [(hasFDerivAt_softMaximum hβ x).fderiv]
  simp [sum_apply, smul_apply, Pi.single_apply]

/-- The `j`-th coordinate partial derivative of the `i`-th softmax weight. -/
theorem fderiv_softWeight_single [DecidableEq ι] {β : ℝ} (hβ : β ≠ 0)
    (x : ι → ℝ) (i j : ι) :
    fderiv ℝ (fun y => softWeight β y i) x (Pi.single j 1) =
      β * softWeight β x i * ((if i = j then 1 else 0) - softWeight β x j) := by
  rw [(hasFDerivAt_softWeight hβ x i).fderiv]
  simp [sum_apply, smul_apply, Pi.single_apply, eq_comm]

/-- The coordinate partial derivatives of the smooth maximum have absolute
values summing to exactly `1`. -/
theorem sum_abs_fderiv_softMaximum [DecidableEq ι] {β : ℝ} (hβ : β ≠ 0)
    (x : ι → ℝ) :
    ∑ i, |fderiv ℝ (softMaximum β) x (Pi.single i 1)| = 1 := by
  simp only [fderiv_softMaximum_single hβ,
    abs_of_pos (softWeight_pos β x _), sum_softWeight]

/-- The row sums of `|δᵢⱼ - softWeight β x j|` are bounded by `2`, uniformly in
`i` and in the input. -/
theorem sum_abs_delta_sub_softWeight [DecidableEq ι] (β : ℝ) (x : ι → ℝ) (i : ι) :
    ∑ j, |(if i = j then 1 else 0) - softWeight β x j| ≤ 2 := by
  calc
    _ ≤ ∑ j, (|(if i = j then 1 else 0 : ℝ)| + |softWeight β x j|) :=
      Finset.sum_le_sum fun j _ => abs_sub _ _
    _ = 2 := by
      simp [Finset.sum_add_distrib, abs_of_pos (softWeight_pos β x _), sum_softWeight,
        apply_ite abs]
      norm_num

/-- The full sum of absolute values of the softmax Hessian entries is at most
`2|β|`, uniformly in the input: the second derivative of the smooth maximum
does not grow with the number of coordinates. -/
theorem sum_abs_softHessian [DecidableEq ι] (β : ℝ) (x : ι → ℝ) :
    ∑ i, ∑ j, |β * softWeight β x i * ((if i = j then 1 else 0) - softWeight β x j)| ≤
      2 * |β| := by
  simp only [abs_mul, abs_of_pos (softWeight_pos β x _), ← Finset.mul_sum]
  calc
    _ ≤ ∑ i, |β| * softWeight β x i * 2 := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (sum_abs_delta_sub_softWeight β x i)
        (mul_nonneg (abs_nonneg β) (softWeight_pos β x i).le)
    _ = 2 * |β| := by rw [← Finset.sum_mul, ← Finset.mul_sum, sum_softWeight]; ring

/-- The second iterated Fréchet derivative of the smooth maximum, evaluated on
two coordinate directions, in closed form. -/
theorem iteratedFDeriv_two_softMaximum [DecidableEq ι] {β : ℝ} (hβ : β ≠ 0)
    (x : ι → ℝ) (z : Fin 2 → ι) :
    iteratedFDeriv ℝ 2 (softMaximum β) x (fun j => Pi.single (z j) 1) =
      β * softWeight β x (z 1) *
        ((if z 1 = z 0 then 1 else 0) - softWeight β x (z 0)) := by
  have hd := (contDiff_softMaximum (ι := ι) β).differentiable_iteratedFDeriv
    (m := 1) (by simp)
  rw [(hd x).iteratedFDeriv_succ_apply_left']
  simp only [iteratedFDeriv_one_apply, Fin.tail, Fin.succ_zero_eq_one,
    fderiv_softMaximum_single hβ, fderiv_softWeight_single hβ]

/-- The `k`-th coordinate partial derivative of the `(i,j)` entry of the
softmax Hessian, in closed form. -/
theorem fderiv_softHessian_single [DecidableEq ι] {β : ℝ} (hβ : β ≠ 0)
    (x : ι → ℝ) (i j k : ι) :
    fderiv ℝ (fun y => β * softWeight β y i *
      ((if i = j then 1 else 0) - softWeight β y j)) x (Pi.single k 1) =
      β ^ 2 * softWeight β x i *
        (((if i = j then 1 else 0) - softWeight β x j) *
          ((if i = k then 1 else 0) - softWeight β x k) -
          softWeight β x j * ((if j = k then 1 else 0) - softWeight β x k)) := by
  have hi := (hasFDerivAt_softWeight hβ x i).differentiableAt.hasFDerivAt
  have hj := (hasFDerivAt_softWeight hβ x j).differentiableAt.hasFDerivAt
  have h := (hi.const_mul β).fun_mul
    ((hasFDerivAt_const (if i = j then (1 : ℝ) else 0) x).sub hj)
  simp only [Pi.sub_apply] at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply, sub_apply, zero_apply, smul_eq_mul,
    fderiv_softWeight_single hβ]
  ring

/-- The third iterated Fréchet derivative of the smooth maximum, evaluated on
three coordinate directions, in closed form. -/
theorem iteratedFDeriv_three_softMaximum [DecidableEq ι] {β : ℝ} (hβ : β ≠ 0)
    (x : ι → ℝ) (z : Fin 3 → ι) :
    iteratedFDeriv ℝ 3 (softMaximum β) x (fun j => Pi.single (z j) 1) =
      β ^ 2 * softWeight β x (z 2) *
        (((if z 2 = z 1 then 1 else 0) - softWeight β x (z 1)) *
          ((if z 2 = z 0 then 1 else 0) - softWeight β x (z 0)) -
          softWeight β x (z 1) * ((if z 1 = z 0 then 1 else 0) - softWeight β x (z 0))) := by
  have hd := (contDiff_softMaximum (ι := ι) β).differentiable_iteratedFDeriv
    (m := 2) (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top 2))
  rw [(hd x).iteratedFDeriv_succ_apply_left']
  change fderiv ℝ (fun y => iteratedFDeriv ℝ 2 (softMaximum β) y
    (fun j => Pi.single ((Fin.tail z) j) 1)) x (Pi.single (z 0) 1) = _
  simp only [iteratedFDeriv_two_softMaximum hβ, Fin.tail]
  exact fderiv_softHessian_single hβ x (z 2) (z 1) (z 0)

/-- The full sum of absolute values of the third-order softmax derivative
tensor is at most `6β²`, uniformly in the input and in the number of
coordinates. -/
theorem sum_abs_softThird [DecidableEq ι] (β : ℝ) (x : ι → ℝ) :
    ∑ i, ∑ j, ∑ k, |β ^ 2 * softWeight β x i *
      (((if i = j then 1 else 0) - softWeight β x j) *
        ((if i = k then 1 else 0) - softWeight β x k) -
        softWeight β x j * ((if j = k then 1 else 0) - softWeight β x k))| ≤
      6 * β ^ 2 := by
  let a (i j : ι) := |(if i = j then 1 else 0 : ℝ) - softWeight β x j|
  have ha (i : ι) : ∑ j, a i j ≤ 2 := sum_abs_delta_sub_softWeight β x i
  have hs (i : ι) :
      ∑ j, ∑ k, (a i j * a i k + softWeight β x j * a j k) ≤ 6 := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    calc
      _ ≤ ∑ j, a i j * 2 + ∑ j, softWeight β x j * 2 := add_le_add
        (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ha i) (abs_nonneg _))
        (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (ha j) (softWeight_pos β x j).le)
      _ ≤ 2 * 2 + 1 * 2 := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, sum_softWeight]
        nlinarith [ha i]
      _ = 6 := by norm_num
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, β ^ 2 * softWeight β x i *
        (a i j * a i k + softWeight β x j * a j k) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg β), abs_of_pos (softWeight_pos β x i)]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg β) (softWeight_pos β x i).le)
      simpa only [abs_mul, abs_of_pos (softWeight_pos β x j)] using
        (abs_sub (((if i = j then 1 else 0) - softWeight β x j) *
          ((if i = k then 1 else 0) - softWeight β x k))
          (softWeight β x j * ((if j = k then 1 else 0) - softWeight β x k)))
    _ ≤ ∑ i, β ^ 2 * softWeight β x i * 6 := by
      simp only [← Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hs i) (mul_nonneg (sq_nonneg β) (softWeight_pos β x i).le)
    _ = 6 * β ^ 2 := by rw [← Finset.sum_mul, ← Finset.mul_sum, sum_softWeight]; ring

omit [Nonempty ι] in
/-- Reindexing a sum over `Fin 2 → ι` by the reversed pair of coordinates as a
double sum over `ι × ι`. -/
theorem sum_fin_two_reverse (f : ι → ι → ℝ) :
    ∑ z : Fin 2 → ι, f (z 1) (z 0) = ∑ i, ∑ j, f i j := by
  classical
  calc
    _ = ∑ p : ι × ι, f p.2 p.1 :=
      Fintype.sum_equiv (finTwoArrowEquiv ι) _ _ (fun _ => rfl)
    _ = ∑ j, ∑ i, f i j := Fintype.sum_prod_type _
    _ = _ := Finset.sum_comm

omit [Nonempty ι] in
/-- Reindexing a sum over `Fin 3 → ι` by the reversed triple of coordinates as
a triple sum over `ι × ι × ι`. -/
theorem sum_fin_three_reverse (f : ι → ι → ι → ℝ) :
    ∑ z : Fin 3 → ι, f (z 2) (z 1) (z 0) = ∑ i, ∑ j, ∑ k, f i j k := by
  classical
  let e : (Fin 3 → ι) ≃ ι × ι × ι := {
    toFun := fun z => (z 2, z 1, z 0)
    invFun := fun p => ![p.2.2, p.2.1, p.1]
    left_inv := fun z => by ext i; fin_cases i <;> rfl
    right_inv := fun p => rfl }
  calc
    _ = ∑ p : ι × ι × ι, f p.1 p.2.1 p.2.2 :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by simp only [Fintype.sum_prod_type]

/-- The second iterated derivative tensor of the smooth maximum, summed in
absolute value over all coordinate pairs, is at most `2|β|`. -/
theorem sum_abs_iteratedFDeriv_softMaximum_two [DecidableEq ι] {β : ℝ} (hβ : β ≠ 0)
    (x : ι → ℝ) :
    ∑ z : Fin 2 → ι,
      |iteratedFDeriv ℝ 2 (softMaximum β) x (fun j => Pi.single (z j) 1)| ≤ 2 * |β| := by
  simp only [iteratedFDeriv_two_softMaximum hβ]
  rw [sum_fin_two_reverse (fun i j =>
    |β * softWeight β x i * ((if i = j then 1 else 0) - softWeight β x j)|)]
  exact sum_abs_softHessian β x

/-- The third iterated derivative tensor of the smooth maximum, summed in
absolute value over all coordinate triples, is at most `6β²`. -/
theorem sum_abs_iteratedFDeriv_softMaximum_three [DecidableEq ι] {β : ℝ} (hβ : β ≠ 0)
    (x : ι → ℝ) :
    ∑ z : Fin 3 → ι,
      |iteratedFDeriv ℝ 3 (softMaximum β) x (fun j => Pi.single (z j) 1)| ≤ 6 * β ^ 2 := by
  simp only [iteratedFDeriv_three_softMaximum hβ]
  rw [sum_fin_three_reverse (fun i j k => |β ^ 2 * softWeight β x i *
    (((if i = j then 1 else 0) - softWeight β x j) *
      ((if i = k then 1 else 0) - softWeight β x k) -
      softWeight β x j * ((if j = k then 1 else 0) - softWeight β x k))|)]
  exact sum_abs_softThird β x

/-- The first iterated derivative tensor of the smooth maximum, summed in
absolute value over all coordinates, equals `1`. -/
theorem sum_abs_iteratedFDeriv_softMaximum_one [DecidableEq ι] {β : ℝ} (hβ : β ≠ 0)
    (x : ι → ℝ) :
    ∑ z : Fin 1 → ι,
      |iteratedFDeriv ℝ 1 (softMaximum β) x (fun j => Pi.single (z j) 1)| = 1 := by
  simp only [iteratedFDeriv_one_apply]
  calc
    _ = ∑ i, |fderiv ℝ (softMaximum β) x (Pi.single i 1)| :=
      Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ (fun _ => rfl)
    _ = 1 := sum_abs_fderiv_softMaximum hβ x

/-- The smooth minimum at inverse temperature `β`, defined as the smooth
maximum at `-β`. -/
noncomputable def softMinimum (β : ℝ) (x : ι → ℝ) : ℝ := softMaximum (-β) x

omit [Nonempty ι] in
/-- The smooth minimum of `x` is the negated smooth maximum of `-x`. -/
theorem softMinimum_eq_neg (β : ℝ) (x : ι → ℝ) :
    softMinimum β x = -softMaximum β (fun i => -x i) := by
  simp only [softMinimum, softMaximum, neg_mul, mul_neg, div_neg]

/-- The smooth minimum is at most every coordinate, when `β > 0`. -/
theorem softMinimum_le {β : ℝ} (hβ : 0 < β) (x : ι → ℝ) (i : ι) :
    softMinimum β x ≤ x i := by
  rw [softMinimum_eq_neg]
  linarith [le_softMaximum hβ (fun i => -x i) i]

/-- The smooth minimum is below any common lower bound `M` on the coordinates
by at most `log(card ι) / β`. -/
theorem le_softMinimum {β : ℝ} (hβ : 0 < β) (x : ι → ℝ) (M : ℝ) (hM : ∀ i, M ≤ x i) :
    M - Real.log (Fintype.card ι) / β ≤ softMinimum β x := by
  rw [softMinimum_eq_neg]
  have h := softMaximum_le hβ (fun i => -x i) (-M) (fun i => neg_le_neg (hM i))
  linarith

/-- The smooth minimum is `C^∞` in the input, for any fixed `β`. -/
theorem contDiff_softMinimum (β : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (softMinimum (ι := ι) β) :=
  contDiff_softMaximum (-β)

/-- The smooth minimum is `1`-Lipschitz for the sup norm. -/
theorem abs_softMinimum_sub_le {β : ℝ} (hβ : 0 < β) {x y : ι → ℝ} {a : ℝ}
    (h : ∀ i, |x i - y i| ≤ a) : |softMinimum β x - softMinimum β y| ≤ a := by
  simpa only [softMinimum_eq_neg, neg_sub_neg, abs_sub_comm] using
    (abs_softMaximum_sub_le hβ (x := fun i => -x i) (y := fun i => -y i)
      (fun i => by simpa only [neg_sub_neg, abs_sub_comm] using h i))

/-- For `1 ≤ k ≤ 3`, the sum of absolute values of the `k`-th iterated
derivative tensor of the smooth maximum is at most `6|β|^(k-1)`: a single
uniform bound covering the order-one, order-two and order-three cases. -/
theorem softMaximum_derivative_bound [DecidableEq ι] {β : ℝ} (hβ : β ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (x : ι → ℝ) :
    ∑ z : Fin k → ι,
      |iteratedFDeriv ℝ k (softMaximum β) x (fun j => Pi.single (z j) 1)| ≤
        6 * |β| ^ (k - 1) := by
  interval_cases k
  · rw [sum_abs_iteratedFDeriv_softMaximum_one hβ]
    norm_num
  · simpa only [Nat.reduceSub, pow_one] using
      (sum_abs_iteratedFDeriv_softMaximum_two hβ x).trans
        (mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ 6 by norm_num) (abs_nonneg β))
  · simpa only [Nat.reduceSub, sq_abs] using sum_abs_iteratedFDeriv_softMaximum_three hβ x

/-- The same uniform derivative bound as `softMaximum_derivative_bound`, for
the smooth minimum. -/
theorem softMinimum_derivative_bound [DecidableEq ι] {β : ℝ} (hβ : β ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (x : ι → ℝ) :
    ∑ z : Fin k → ι,
      |iteratedFDeriv ℝ k (softMinimum β) x (fun j => Pi.single (z j) 1)| ≤
        6 * |β| ^ (k - 1) := by
  change (∑ z : Fin k → ι,
    |iteratedFDeriv ℝ k (softMaximum (-β)) x (fun j => Pi.single (z j) 1)|) ≤ _
  simpa only [abs_neg] using
    softMaximum_derivative_bound (neg_ne_zero.mpr hβ) k hk hk' x

end LatticeProb
