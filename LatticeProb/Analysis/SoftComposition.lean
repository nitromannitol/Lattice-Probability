/-
Composition of smooth maxima and minima (`LatticeProb.Analysis.SoftMaximum`)
with dimension-independent coordinate derivative bounds: first-derivative sums
stay at most `1`, and second- and third-derivative sums grow at most linearly
and quadratically with the number of composition layers.

Moved from Divisible-Sandpile-Percolation, `Sandpile/Support/SoftComposition.lean`.
-/
import LatticeProb.Analysis.SoftMaximum

open scoped BigOperators

namespace LatticeProb

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `i`-th coordinate partial derivative of `f` at `x`. -/
noncomputable def coordPartial (f : (V → ℝ) → ℝ) (i : V) (x : V → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- A coordinate partial derivative of a `C^∞` function is again `C^∞`. -/
theorem contDiff_coordPartial {f : (V → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : V) :
    ContDiff ℝ (⊤ : ℕ∞) (coordPartial f i) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- Coordinate differentiation is additive. -/
theorem coordPartial_add {f g : (V → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (i : V) (x : V → ℝ) :
    coordPartial (fun y => f y + g y) i x = coordPartial f i x + coordPartial g i x := by
  simp only [coordPartial, fderiv_fun_add (hf x) (hg x), add_apply]

/-- The coordinate product rule. -/
theorem coordPartial_mul {f g : (V → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (i : V) (x : V → ℝ) :
    coordPartial (fun y => f y * g y) i x = f x * coordPartial g i x + g x * coordPartial f i x := by
  simp only [coordPartial, fderiv_fun_mul (hf x) (hg x), add_apply, smul_apply, smul_eq_mul]

/-- Coordinate differentiation commutes with a finite sum over an index type. -/
theorem coordPartial_sum {I : Type*} [Fintype I] {f : I → (V → ℝ) → ℝ}
    (hf : ∀ i, Differentiable ℝ (f i)) (j : V) (x : V → ℝ) :
    coordPartial (fun y => ∑ i, f i y) j x = ∑ i, coordPartial (f i) j x := by
  simp only [coordPartial, fderiv_fun_sum (fun i _ => hf i x), sum_apply]

/-- Coordinate differentiation is additive under subtraction. -/
theorem coordPartial_sub {f g : (V → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (i : V) (x : V → ℝ) :
    coordPartial (fun y => f y - g y) i x = coordPartial f i x - coordPartial g i x := by
  simp only [coordPartial, fderiv_fun_sub (hf x) (hg x), sub_apply]

/-- Coordinate differentiation pulls out a scalar multiple. -/
theorem coordPartial_const_mul (c : ℝ) {f : (V → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (i : V) (x : V → ℝ) :
    coordPartial (fun y => c * f y) i x = c * coordPartial f i x := by
  simp only [coordPartial, fderiv_const_mul (hf x), smul_apply, smul_eq_mul]

/-- The second iterated derivative of `f` is the coordinate partial of a
coordinate partial. -/
theorem iteratedFDeriv_two_coordPartial {f : (V → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : V → ℝ) (z : Fin 2 → V) :
    iteratedFDeriv ℝ 2 f x (fun j => Pi.single (z j) 1) =
      coordPartial (coordPartial f (z 1)) (z 0) x := by
  have hd := hf.differentiable_iteratedFDeriv (m := 1) (by simp)
  rw [(hd x).iteratedFDeriv_succ_apply_left']
  simp only [iteratedFDeriv_one_apply, Fin.tail, coordPartial, Fin.succ_zero_eq_one]
  rfl

/-- The third iterated derivative of `f` is an iterated coordinate partial. -/
theorem iteratedFDeriv_three_coordPartial {f : (V → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : V → ℝ) (z : Fin 3 → V) :
    iteratedFDeriv ℝ 3 f x (fun j => Pi.single (z j) 1) =
      coordPartial (coordPartial (coordPartial f (z 2)) (z 1)) (z 0) x := by
  have hd := hf.differentiable_iteratedFDeriv (m := 2)
    (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top 2))
  rw [(hd x).iteratedFDeriv_succ_apply_left']
  change fderiv ℝ (fun y => iteratedFDeriv ℝ 2 f y
    (fun j => Pi.single ((Fin.tail z) j) 1)) x (Pi.single (z 0) 1) = _
  simp only [iteratedFDeriv_two_coordPartial hf, Fin.tail]
  rfl

/-- The order-one iterated derivative tensor, summed in absolute value, equals
the sum of absolute coordinate partials. -/
theorem sum_abs_iteratedFDeriv_one_coordPartial (f : (V → ℝ) → ℝ) (x : V → ℝ) :
    ∑ z : Fin 1 → V, |iteratedFDeriv ℝ 1 f x (fun j => Pi.single (z j) 1)| =
      ∑ j, |coordPartial f j x| := by
  simp only [iteratedFDeriv_one_apply, coordPartial]
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) V) _ _ (fun _ => rfl)

/-- The order-two iterated derivative tensor, summed in absolute value, equals
the double sum of absolute iterated coordinate partials. -/
theorem sum_abs_iteratedFDeriv_two_coordPartial {f : (V → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : V → ℝ) :
    ∑ z : Fin 2 → V, |iteratedFDeriv ℝ 2 f x (fun j => Pi.single (z j) 1)| =
      ∑ j, ∑ k, |coordPartial (coordPartial f j) k x| := by
  simp only [iteratedFDeriv_two_coordPartial hf]
  exact sum_fin_two_reverse (fun j k => |coordPartial (coordPartial f j) k x|)

/-- The order-three iterated derivative tensor, summed in absolute value,
equals the triple sum of absolute iterated coordinate partials. -/
theorem sum_abs_iteratedFDeriv_three_coordPartial {f : (V → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : V → ℝ) :
    ∑ z : Fin 3 → V, |iteratedFDeriv ℝ 3 f x (fun j => Pi.single (z j) 1)| =
      ∑ j, ∑ k, ∑ l, |coordPartial (coordPartial (coordPartial f j) k) l x| := by
  simp only [iteratedFDeriv_three_coordPartial hf]
  exact sum_fin_three_reverse (fun j k l => |coordPartial (coordPartial (coordPartial f j) k) l x|)

/-- `f` is `C^∞` with coordinate derivative sums bounded uniformly through
order three by an affine/quadratic function of `n`, the number of smooth
maximum/minimum composition layers used to build it. -/
def SmoothBottleneckBound (β : ℝ) (n : ℕ) (f : (V → ℝ) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ ∀ x,
    (∑ j, |coordPartial f j x| ≤ 1) ∧
    (∑ j, ∑ k, |coordPartial (coordPartial f j) k x| ≤ 2 * |β| * n) ∧
    (∑ j, ∑ k, ∑ l, |coordPartial (coordPartial (coordPartial f j) k) l x| ≤ 6 * β ^ 2 * (n : ℝ) ^ 2)

/-- A coordinate projection satisfies the bottleneck bound at layer `0`: its
first derivative sum is `1` and its higher derivatives vanish. -/
theorem smoothBottleneckBound_coordinate (β : ℝ) (i : V) :
    SmoothBottleneckBound β 0 (fun x : V → ℝ => x i) := by
  have hpartial (j : V) (x : V → ℝ) :
      coordPartial (fun x : V → ℝ => x i) j x = if i = j then 1 else 0 := by
    simp only [coordPartial, (hasFDerivAt_apply i x).fderiv, ContinuousLinearMap.proj_apply]
    simp [Pi.single_apply]
  have hzero (j k : V) (x : V → ℝ) :
      coordPartial (coordPartial (fun x : V → ℝ => x i) j) k x = 0 := by
    have he : coordPartial (fun x : V → ℝ => x i) j = fun _ => if i = j then 1 else 0 :=
      funext (hpartial j)
    rw [he]
    simp [coordPartial]
  refine ⟨contDiff_apply ℝ ℝ i, fun x => ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [hpartial, apply_ite abs]
  · simp only [hzero, abs_zero, Finset.sum_const_zero, Nat.cast_zero, mul_zero, le_refl]
  · have he (j k : V) : coordPartial (coordPartial (fun x : V → ℝ => x i) j) k = fun _ => 0 :=
      funext (hzero j k)
    simp [he, coordPartial]

/-- The bottleneck bound implies the uniform derivative-tensor bound
`softMaximum_derivative_bound` mirrors, at orders one through three. -/
theorem SmoothBottleneckBound.iteratedFDeriv {β : ℝ} {n : ℕ} {f : (V → ℝ) → ℝ}
    (hf : SmoothBottleneckBound β n f) (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (x : V → ℝ) :
    ∑ z : Fin k → V, |iteratedFDeriv ℝ k f x (fun j => Pi.single (z j) 1)| ≤
      6 * |β| ^ (k - 1) * (n : ℝ) ^ (k - 1) := by
  interval_cases k
  · rw [sum_abs_iteratedFDeriv_one_coordPartial]
    simpa only [Nat.reduceSub, pow_zero, mul_one] using (hf.2 x).1.trans (by norm_num : (1 : ℝ) ≤ 6)
  · rw [sum_abs_iteratedFDeriv_two_coordPartial hf.1]
    simpa only [Nat.reduceSub, pow_one] using (hf.2 x).2.1.trans
      (by nlinarith [mul_nonneg (abs_nonneg β) (Nat.cast_nonneg n)] :
        2 * |β| * (n : ℝ) ≤ 6 * |β| * n)
  · rw [sum_abs_iteratedFDeriv_three_coordPartial hf.1]
    simpa only [Nat.reduceSub, sq_abs] using (hf.2 x).2.2

/-- The bottleneck bound at layer `n` also holds at any later layer `m ≥ n`. -/
theorem SmoothBottleneckBound.mono {β : ℝ} {n m : ℕ} {f : (V → ℝ) → ℝ}
    (hf : SmoothBottleneckBound β n f) (hnm : n ≤ m) : SmoothBottleneckBound β m f := by
  refine ⟨hf.1, fun x => ⟨(hf.2 x).1, ?_, ?_⟩⟩
  · exact (hf.2 x).2.1.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnm)
      (mul_nonneg (by norm_num) (abs_nonneg β)))
  · apply (hf.2 x).2.2.trans
    gcongr

variable {I : Type*} [Fintype I] [Nonempty I]

omit [DecidableEq V] in
/-- The smooth maximum of a family of `C^∞` functions is `C^∞`. -/
theorem contDiff_softComposition (β : ℝ) {f : I → (V → ℝ) → ℝ}
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => softMaximum β (fun i => f i x)) :=
  (contDiff_softMaximum β).comp (contDiff_pi.mpr hf)

/-- The chain rule for a coordinate partial of a smooth maximum of a family
`f`: it is the softmax-weighted average of the coordinate partials of the
`f i`. -/
theorem coordPartial_softComposition {β : ℝ} (hβ : β ≠ 0) {f : I → (V → ℝ) → ℝ}
    (hf : ∀ i, Differentiable ℝ (f i)) (j : V) (x : V → ℝ) :
    coordPartial (fun y => softMaximum β (fun i => f i y)) j x =
      ∑ i, softWeight β (fun i => f i x) i * coordPartial (f i) j x := by
  have hpi := hasFDerivAt_pi.mpr (fun i => (hf i x).hasFDerivAt)
  have h := (hasFDerivAt_softMaximum hβ (fun i => f i x)).comp x hpi
  simp only [Function.comp_def] at h
  unfold coordPartial
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.pi_apply, smul_eq_mul]

/-- If every `f i` has coordinate derivative sum at most `A`, so does their
smooth maximum: the weighted average of bounded quantities is bounded. -/
theorem sum_abs_coordPartial_softComposition {β : ℝ} (hβ : β ≠ 0)
    {f : I → (V → ℝ) → ℝ} (hf : ∀ i, Differentiable ℝ (f i))
    (x : V → ℝ) {A : ℝ} (hA : ∀ i, ∑ j, |coordPartial (f i) j x| ≤ A) :
    ∑ j, |coordPartial (fun y => softMaximum β (fun i => f i y)) j x| ≤ A := by
  simp only [coordPartial_softComposition hβ hf]
  calc
    _ ≤ ∑ j, ∑ i, softWeight β (fun i => f i x) i * |coordPartial (f i) j x| := by
      apply Finset.sum_le_sum
      intro j _
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
        simp only [abs_mul, abs_of_pos (softWeight_pos β _ _)])
    _ = ∑ i, softWeight β (fun i => f i x) i * ∑ j, |coordPartial (f i) j x| := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ i, softWeight β (fun i => f i x) i * A := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hA i) (softWeight_pos β _ i).le
    _ = A := by rw [← Finset.sum_mul, sum_softWeight, one_mul]

omit [DecidableEq V] in
/-- A softmax weight of a family of `C^∞` functions is `C^∞`. -/
theorem contDiff_softWeightComposition {β : ℝ} (hβ : β ≠ 0) {f : I → (V → ℝ) → ℝ}
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (i : I) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => softWeight β (fun i => f i x) i) := by
  simp_rw [softWeight_eq_exp hβ]
  exact (contDiff_const.mul ((hf i).sub (contDiff_softComposition β hf))).exp

/-- The chain rule for a coordinate partial of a composed softmax weight. -/
theorem coordPartial_softWeightComposition {β : ℝ} (hβ : β ≠ 0) {f : I → (V → ℝ) → ℝ}
    (hf : ∀ i, Differentiable ℝ (f i)) (i : I) (j : V) (x : V → ℝ) :
    coordPartial (fun y => softWeight β (fun i => f i y) i) j x =
      β * softWeight β (fun i => f i x) i *
        (coordPartial (f i) j x -
          coordPartial (fun y => softMaximum β (fun i => f i y)) j x) := by
  have hpi := hasFDerivAt_pi.mpr (fun i => (hf i x).hasFDerivAt)
  have h := (hasFDerivAt_softWeight hβ (fun i => f i x) i).comp x hpi
  simp only [Function.comp_def] at h
  rw [coordPartial_softComposition hβ hf]
  unfold coordPartial
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, sum_apply, smul_apply, sub_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.pi_apply, smul_eq_mul]

/-- The chain rule for a second coordinate partial of a smooth maximum of a
family `f`, in closed form as a softmax-weighted average. -/
theorem coordPartial_softComposition_two {β : ℝ} (hβ : β ≠ 0)
    {f : I → (V → ℝ) → ℝ} (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (j k : V) (x : V → ℝ) :
    coordPartial (coordPartial (fun y => softMaximum β (fun i => f i y)) j) k x =
      ∑ i, softWeight β (fun i => f i x) i *
        (coordPartial (coordPartial (f i) j) k x + β *
          (coordPartial (f i) k x -
            coordPartial (fun y => softMaximum β (fun i => f i y)) k x) *
          coordPartial (f i) j x) := by
  have hfd (i : I) := (hf i).differentiable (by simp)
  have hwp (i : I) := (contDiff_softWeightComposition hβ hf i).differentiable (by simp)
  have hfp (i : I) := (contDiff_coordPartial (hf i) j).differentiable (by simp)
  have he : coordPartial (fun y => softMaximum β (fun i => f i y)) j =
      fun y => ∑ i, softWeight β (fun i => f i y) i * coordPartial (f i) j y := by
    funext y
    exact coordPartial_softComposition hβ hfd j y
  rw [he, coordPartial_sum
    (f := fun i y => softWeight β (fun i => f i y) i * coordPartial (f i) j y)
    (fun i => (hwp i).mul (hfp i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordPartial_mul (hwp i) (hfp i), coordPartial_softWeightComposition hβ hfd]
  ring

/-- The coordinate partials of `f i` and of the composed smooth maximum
differ by at most `2` in total absolute value, uniformly, when each `f i` has
first-derivative sum at most `1`. -/
theorem sum_abs_centered_coordPartial {β : ℝ} (hβ : β ≠ 0)
    {f : I → (V → ℝ) → ℝ} (hf : ∀ i, Differentiable ℝ (f i))
    (x : V → ℝ) (hA : ∀ i, ∑ j, |coordPartial (f i) j x| ≤ 1) (i : I) :
    ∑ j, |coordPartial (f i) j x -
      coordPartial (fun y => softMaximum β (fun i => f i y)) j x| ≤ 2 := by
  calc
    _ ≤ ∑ j, (|coordPartial (f i) j x| +
        |coordPartial (fun y => softMaximum β (fun i => f i y)) j x|) :=
      Finset.sum_le_sum fun j _ => abs_sub _ _
    _ ≤ 1 + 1 := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (hA i) (sum_abs_coordPartial_softComposition hβ hf x hA)
    _ = 2 := by norm_num

/-- If every `f i` satisfies the bottleneck bound's first two moment
inequalities (with the same constant `1` on the first), so does their
smooth maximum's Hessian, up to the extra additive term `2|β|`. -/
theorem sum_abs_coordPartial_softComposition_two {β : ℝ} (hβ : β ≠ 0)
    {f : I → (V → ℝ) → ℝ} (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (x : V → ℝ) {A : ℝ}
    (h1 : ∀ i, ∑ j, |coordPartial (f i) j x| ≤ 1)
    (h2 : ∀ i, ∑ j, ∑ k, |coordPartial (coordPartial (f i) j) k x| ≤ A) :
    ∑ j, ∑ k, |coordPartial
      (coordPartial (fun y => softMaximum β (fun i => f i y)) j) k x| ≤ A + 2 * |β| := by
  let L (y : V → ℝ) := softMaximum β (fun i => f i y)
  let p (i : I) := softWeight β (fun i => f i x) i
  let d (i : I) (j : V) := coordPartial (f i) j x
  let H (i : I) (j k : V) := coordPartial (coordPartial (f i) j) k x
  let r (i : I) (j : V) := d i j - coordPartial L j x
  have hr (i : I) : ∑ j, |r i j| ≤ 2 :=
    sum_abs_centered_coordPartial hβ (fun i => (hf i).differentiable (by simp)) x h1 i
  have hrow (i : I) : ∑ j, ∑ k, |H i j k + β * r i k * d i j| ≤ A + 2 * |β| := by
    calc
      _ ≤ ∑ j, ∑ k, (|H i j k| + |β| * |r i k| * |d i j|) := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro k _
        simpa only [abs_mul] using abs_add_le (H i j k) (β * r i k * d i j)
      _ = (∑ j, ∑ k, |H i j k|) + |β| * (∑ k, |r i k|) * ∑ j, |d i j| := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ A + |β| * 2 * 1 := add_le_add (h2 i)
        (mul_le_mul (mul_le_mul_of_nonneg_left (hr i) (abs_nonneg β)) (h1 i)
          (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity))
      _ = _ := by ring
  simp only [coordPartial_softComposition_two hβ hf]
  change (∑ j, ∑ k, |∑ i, p i * (H i j k + β * r i k * d i j)|) ≤ _
  calc
    _ ≤ ∑ j, ∑ k, ∑ i, p i * |H i j k + β * r i k * d i j| := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
        simp only [p, abs_mul, abs_of_pos (softWeight_pos β _ _)])
    _ = ∑ i, p i * ∑ j, ∑ k, |H i j k + β * r i k * d i j| := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ j, ∑ i, ∑ k, p i * |H i j k + β * r i k * d i j| :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm
    _ ≤ ∑ i, p i * (A + 2 * |β|) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hrow i) (softWeight_pos β _ i).le
    _ = _ := by rw [← Finset.sum_mul, sum_softWeight, one_mul]

/-- The chain rule for a third coordinate partial of a smooth maximum of a
family `f`, in closed form as a softmax-weighted average. -/
theorem coordPartial_softComposition_three {β : ℝ} (hβ : β ≠ 0)
    {f : I → (V → ℝ) → ℝ} (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (j k l : V) (x : V → ℝ) :
    let L := fun y => softMaximum β (fun i => f i y)
    let r := fun i a y => coordPartial (f i) a y - coordPartial L a y
    coordPartial (coordPartial (coordPartial L j) k) l x =
      ∑ i, softWeight β (fun i => f i x) i *
        (coordPartial (coordPartial (coordPartial (f i) j) k) l x +
          β * r i l x * coordPartial (coordPartial (f i) j) k x +
          β * r i k x * coordPartial (coordPartial (f i) j) l x +
          β * (coordPartial (coordPartial (f i) k) l x -
            coordPartial (coordPartial L k) l x) * coordPartial (f i) j x +
          β ^ 2 * r i l x * r i k x * coordPartial (f i) j x) := by
  intro L r
  let w (i : I) (y : V → ℝ) := softWeight β (fun i => f i y) i
  let q (i : I) (y : V → ℝ) := coordPartial (coordPartial (f i) j) k y +
    β * r i k y * coordPartial (f i) j y
  have hL : ContDiff ℝ (⊤ : ℕ∞) L := contDiff_softComposition β hf
  have hw (i : I) : ContDiff ℝ (⊤ : ℕ∞) (w i) := contDiff_softWeightComposition hβ hf i
  have hr (i : I) (a : V) : ContDiff ℝ (⊤ : ℕ∞) (r i a) :=
    (contDiff_coordPartial (hf i) a).sub (contDiff_coordPartial hL a)
  have hp (i : I) (a : V) := contDiff_coordPartial (hf i) a
  have hpp (i : I) (a b : V) := contDiff_coordPartial (hp i a) b
  have hq (i : I) : ContDiff ℝ (⊤ : ℕ∞) (q i) :=
    (hpp i j k).add ((contDiff_const.mul (hr i k)).mul (hp i j))
  have he : coordPartial (coordPartial L j) k = fun y => ∑ i, w i y * q i y := by
    funext y
    exact coordPartial_softComposition_two hβ hf j k y
  rw [he, coordPartial_sum (f := fun i y => w i y * q i y)
    (fun i => ((hw i).differentiable (by simp)).mul ((hq i).differentiable (by simp)))]
  apply Finset.sum_congr rfl
  intro i _
  have hwi : coordPartial (w i) l x = β * w i x * r i l x :=
    coordPartial_softWeightComposition hβ (fun i => (hf i).differentiable (by simp)) i l x
  have hri : coordPartial (r i k) l x = coordPartial (coordPartial (f i) k) l x -
      coordPartial (coordPartial L k) l x :=
    coordPartial_sub ((hp i k).differentiable (by simp))
      ((contDiff_coordPartial hL k).differentiable (by simp)) l x
  have hqi : coordPartial (q i) l x =
      coordPartial (coordPartial (coordPartial (f i) j) k) l x +
        β * r i k x * coordPartial (coordPartial (f i) j) l x +
        coordPartial (f i) j x * β *
          (coordPartial (coordPartial (f i) k) l x - coordPartial (coordPartial L k) l x) := by
    unfold q
    rw [coordPartial_add (g := fun y => β * r i k y * coordPartial (f i) j y)
      ((hpp i j k).differentiable (by simp))
      ((((hr i k).differentiable (by simp)).const_mul β).mul ((hp i j).differentiable (by simp)))]
    rw [coordPartial_mul (((hr i k).differentiable (by simp)).const_mul β)
      ((hp i j).differentiable (by simp))]
    rw [coordPartial_const_mul β ((hr i k).differentiable (by simp)), hri]
    ring
  rw [coordPartial_mul ((hw i).differentiable (by simp)) ((hq i).differentiable (by simp)), hwi, hqi]
  dsimp only [q, w]
  ring

/-- If every `f i` satisfies the bottleneck bound's three moment
inequalities (with constants `1`, `A`, `B`), the third-order derivative sum
of the smooth maximum is at most `B + 6|β|A + 6β²`. -/
theorem sum_abs_coordPartial_softComposition_three {β : ℝ} (hβ : β ≠ 0)
    {f : I → (V → ℝ) → ℝ} (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (x : V → ℝ) {A B : ℝ}
    (h1 : ∀ i, ∑ j, |coordPartial (f i) j x| ≤ 1)
    (h2 : ∀ i, ∑ j, ∑ k, |coordPartial (coordPartial (f i) j) k x| ≤ A)
    (h3 : ∀ i, ∑ j, ∑ k, ∑ l, |coordPartial (coordPartial (coordPartial (f i) j) k) l x| ≤ B) :
    ∑ j, ∑ k, ∑ l, |coordPartial (coordPartial
      (coordPartial (fun y => softMaximum β (fun i => f i y)) j) k) l x| ≤
      B + 6 * |β| * A + 6 * β ^ 2 := by
  let L (y : V → ℝ) := softMaximum β (fun i => f i y)
  let p (i : I) := softWeight β (fun i => f i x) i
  let d (i : I) (j : V) := coordPartial (f i) j x
  let H (i : I) (j k : V) := coordPartial (coordPartial (f i) j) k x
  let T (i : I) (j k l : V) := coordPartial (coordPartial (coordPartial (f i) j) k) l x
  let HL (k l : V) := coordPartial (coordPartial L k) l x
  let r (i : I) (j : V) := d i j - coordPartial L j x
  let U (i : I) (j k l : V) := T i j k l + β * r i l * H i j k +
    β * r i k * H i j l + β * (H i k l - HL k l) * d i j +
    β ^ 2 * r i l * r i k * d i j
  have hr (i : I) : ∑ j, |r i j| ≤ 2 :=
    sum_abs_centered_coordPartial hβ (fun i => (hf i).differentiable (by simp)) x h1 i
  have hL2 : ∑ k, ∑ l, |HL k l| ≤ A + 2 * |β| :=
    sum_abs_coordPartial_softComposition_two hβ hf x h1 h2
  have hDiff (i : I) : ∑ k, ∑ l, |H i k l - HL k l| ≤ 2 * A + 2 * |β| := by
    calc
      _ ≤ ∑ k, ∑ l, (|H i k l| + |HL k l|) := Finset.sum_le_sum fun k _ =>
        Finset.sum_le_sum fun l _ => abs_sub _ _
      _ ≤ A + (A + 2 * |β|) := by
        simp only [Finset.sum_add_distrib]
        exact add_le_add (h2 i) hL2
      _ = _ := by ring
  have hA : 0 ≤ A := (Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => abs_nonneg _).trans (h2 (Classical.choice inferInstance))
  have hrow (i : I) : ∑ j, ∑ k, ∑ l, |U i j k l| ≤ B + 6 * |β| * A + 6 * β ^ 2 := by
    have hU (j k l : V) : |U i j k l| ≤ |T i j k l| +
        |β| * |r i l| * |H i j k| + |β| * |r i k| * |H i j l| +
        |β| * |H i k l - HL k l| * |d i j| + β ^ 2 * |r i l| * |r i k| * |d i j| := by
      dsimp only [U]
      calc
        _ ≤ |T i j k l| + |β * r i l * H i j k| + |β * r i k * H i j l| +
            |β * (H i k l - HL k l) * d i j| + |β ^ 2 * r i l * r i k * d i j| := by
          linarith only [abs_add_le (T i j k l) (β * r i l * H i j k),
            abs_add_le (T i j k l + β * r i l * H i j k) (β * r i k * H i j l),
            abs_add_le (T i j k l + β * r i l * H i j k + β * r i k * H i j l)
              (β * (H i k l - HL k l) * d i j),
            abs_add_le (T i j k l + β * r i l * H i j k + β * r i k * H i j l +
              β * (H i k l - HL k l) * d i j) (β ^ 2 * r i l * r i k * d i j)]
        _ = _ := by simp only [abs_mul, abs_pow, sq_abs]
    have hb2 : ∑ j, ∑ k, ∑ l, |β| * |r i l| * |H i j k| ≤ |β| * 2 * A := by
      calc
        _ = |β| * (∑ l, |r i l|) * ∑ j, ∑ k, |H i j k| := by
          simp only [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ _ := by gcongr; exact hr i; exact h2 i
    have hb3 : ∑ j, ∑ k, ∑ l, |β| * |r i k| * |H i j l| ≤ |β| * 2 * A := by
      calc
        _ = |β| * (∑ k, |r i k|) * ∑ j, ∑ l, |H i j l| := by
          simp only [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ _ := by gcongr; exact hr i; exact h2 i
    have hb4 : ∑ j, ∑ k, ∑ l, |β| * |H i k l - HL k l| * |d i j| ≤
        |β| * (2 * A + 2 * |β|) := by
      calc
        _ = |β| * (∑ k, ∑ l, |H i k l - HL k l|) * ∑ j, |d i j| := by
          simp only [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ |β| * (2 * A + 2 * |β|) * 1 := by gcongr; exact hDiff i; exact h1 i
        _ = _ := mul_one _
    have hb5 : ∑ j, ∑ k, ∑ l, β ^ 2 * |r i l| * |r i k| * |d i j| ≤ 4 * β ^ 2 := by
      calc
        _ = β ^ 2 * (∑ l, |r i l|) * (∑ k, |r i k|) * ∑ j, |d i j| := by
          simp only [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ β ^ 2 * 2 * 2 * 1 := by gcongr; exact hr i; exact hr i; exact h1 i
        _ = _ := by ring
    calc
      _ ≤ ∑ j, ∑ k, ∑ l, (|T i j k l| + |β| * |r i l| * |H i j k| +
          |β| * |r i k| * |H i j l| + |β| * |H i k l - HL k l| * |d i j| +
          β ^ 2 * |r i l| * |r i k| * |d i j|) := Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hU j k l
      _ ≤ B + |β| * 2 * A + |β| * 2 * A + |β| * (2 * A + 2 * |β|) + 4 * β ^ 2 := by
        simp only [Finset.sum_add_distrib]
        exact add_le_add (add_le_add (add_le_add (add_le_add (h3 i) hb2) hb3) hb4) hb5
      _ = _ := by nlinarith [sq_abs β]
  simp only [coordPartial_softComposition_three hβ hf]
  change (∑ j, ∑ k, ∑ l, |∑ i, p i * U i j k l|) ≤ _
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, ∑ i, p i * |U i j k l| := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
        simp only [p, abs_mul, abs_of_pos (softWeight_pos β _ _)])
    _ = ∑ i, p i * ∑ j, ∑ k, ∑ l, |U i j k l| := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ j, ∑ k, ∑ i, ∑ l, p i * |U i j k l| :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
        _ = ∑ j, ∑ i, ∑ k, ∑ l, p i * |U i j k l| :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm
    _ ≤ ∑ i, p i * (B + 6 * |β| * A + 6 * β ^ 2) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hrow i) (softWeight_pos β _ i).le
    _ = _ := by rw [← Finset.sum_mul, sum_softWeight, one_mul]

/-- The smooth maximum of a family, each satisfying the bottleneck bound at
layer `n`, satisfies the bottleneck bound at layer `n + 1`: composing one
more smooth maximum costs exactly one more layer. -/
theorem SmoothBottleneckBound.softMaximum {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f : I → (V → ℝ) → ℝ} (hf : ∀ i, SmoothBottleneckBound β n (f i)) :
    SmoothBottleneckBound β (n + 1) (fun y => softMaximum β (fun i => f i y)) := by
  refine ⟨contDiff_softComposition β (fun i => (hf i).1), fun x => ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact sum_abs_coordPartial_softComposition hβ
      (fun i => (hf i).1.differentiable (by simp)) x (fun i => ((hf i).2 x).1)
  · have h := sum_abs_coordPartial_softComposition_two hβ (fun i => (hf i).1) x
      (fun i => ((hf i).2 x).1) (fun i => ((hf i).2 x).2.1)
    convert h using 1
    push_cast
    ring
  · have h := sum_abs_coordPartial_softComposition_three hβ (fun i => (hf i).1) x
      (fun i => ((hf i).2 x).1) (fun i => ((hf i).2 x).2.1) (fun i => ((hf i).2 x).2.2)
    convert h using 1
    push_cast
    nlinarith [sq_abs β]

/-- The same one-layer-deeper bottleneck bound as `SmoothBottleneckBound.softMaximum`,
for the smooth minimum. -/
theorem SmoothBottleneckBound.softMinimum {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f : I → (V → ℝ) → ℝ} (hf : ∀ i, SmoothBottleneckBound β n (f i)) :
    SmoothBottleneckBound β (n + 1) (fun y => softMinimum β (fun i => f i y)) := by
  have hn (i : I) : SmoothBottleneckBound (-β) n (f i) := by
    simpa only [SmoothBottleneckBound, abs_neg, neg_sq] using hf i
  change SmoothBottleneckBound β (n + 1) (fun y => LatticeProb.softMaximum (-β) (fun i => f i y))
  simpa only [SmoothBottleneckBound, abs_neg, neg_sq] using
    SmoothBottleneckBound.softMaximum (neg_ne_zero.mpr hβ) hn

end LatticeProb
