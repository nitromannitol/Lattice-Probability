import LatticeProb.Analysis.Schauder.SineSeries

/-!
Ported from the Lattice-High-Contrast-Homogenization development, module `LatticeHC.Support.TwoScale.DirichletInverse`.

# The Dirichlet inverse of a test function

For a test function `f` of the unit cube and `D > 0`, `u = (−DΔ_Q)⁻¹ f` (the sine series
`Σ_k (Dλ_k)⁻¹⟨f, φ_k⟩φ_k`) is smooth on `ℝ^d`, solves
`−DΔu = f` in the cube, vanishes on its boundary, and `∫_Q f u = dirichletForm D f`: the derivatives
of the modes grow polynomially in `λ_k` while the coefficients decay faster than any power, so the
series can be differentiated termwise. The termwise differentiation is proved once for a general
sine series `sineSeries a` with rapidly decaying coefficients `a` (smoothness, iterated derivatives,
Laplacian, vanishing on the boundary); the Dirichlet inverse is the case `a_k = (Dλ_k)⁻¹⟨f, φ_k⟩`.
-/

open MeasureTheory LatticeProb

noncomputable section

namespace LatticeProb.Analysis.Schauder

variable {d : ℕ}

/-- The iterated derivatives of the one-variable factor of a sine mode. -/
theorem iteratedDeriv_sineFactor (a : ℝ) (m : ℕ) :
    iteratedDeriv m (sineFactor a) =
      fun t => Real.sqrt 2 * (a ^ m * Real.sin (a * t + m * (Real.pi / 2))) := by
  induction m with
  | zero => funext t; simp [sineFactor]
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h : HasDerivAt
        (fun t : ℝ => Real.sqrt 2 * (a ^ m * Real.sin (a * t + m * (Real.pi / 2))))
        (Real.sqrt 2 * (a ^ m * (Real.cos (a * t + m * (Real.pi / 2)) * a))) t := by
      have := (((hasDerivAt_id t).const_mul a).add_const (m * (Real.pi / 2))).sin
      exact ((this.const_mul (a ^ m)).const_mul _).congr_deriv (by simp)
    rw [h.deriv]
    push_cast
    have : a * t + (↑m + 1) * (Real.pi / 2) = (a * t + m * (Real.pi / 2)) + Real.pi / 2 := by ring
    rw [this, Real.sin_add_pi_div_two]
    ring

/-- The norm of the `m`-th derivative of the one-variable factor of a sine mode. -/
theorem norm_iteratedFDeriv_sineFactor_le {a : ℝ} (ha : 0 ≤ a) (m : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ m (sineFactor a) t‖ ≤ Real.sqrt 2 * a ^ m := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_sineFactor, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2), abs_mul, abs_of_nonneg (pow_nonneg ha m)]
  have := Real.abs_sin_le_one (a * t + m * (Real.pi / 2))
  have h2 := Real.sqrt_nonneg 2
  have h3 := pow_nonneg ha m
  nlinarith [mul_nonneg h2 h3]

/-- The coordinate projections are contractions. -/
theorem norm_proj_le_one (i : Fin d) : ‖(EuclideanSpace.proj (𝕜 := ℝ) i : Euc d →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using PiLp.norm_apply_le x i

/-- The norm of the `m`-th derivative of a one-variable sine factor of a coordinate. -/
theorem norm_iteratedFDeriv_sineFactor_proj_le {a : ℝ} (ha : 0 ≤ a) (i : Fin d) (m : ℕ)
    (x : Euc d) :
    ‖iteratedFDeriv ℝ m (fun z : Euc d => sineFactor a (z i)) x‖ ≤ Real.sqrt 2 * a ^ m := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).iteratedFDeriv_comp_right
    (contDiff_sineFactor a) x (i := m) (by exact_mod_cast le_top)
  have h1 : (fun z : Euc d => sineFactor a (z i)) =
      sineFactor a ∘ (EuclideanSpace.proj (𝕜 := ℝ) i) := rfl
  rw [h1, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _l : Fin m, ‖(EuclideanSpace.proj (𝕜 := ℝ) i : Euc d →L[ℝ] ℝ)‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => norm_proj_le_one i
  calc _ ≤ ‖iteratedFDeriv ℝ m (sineFactor a) ((EuclideanSpace.proj (𝕜 := ℝ) i) x)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ ≤ Real.sqrt 2 * a ^ m := by
        rw [mul_one]
        exact norm_iteratedFDeriv_sineFactor_le ha m _

/-- Derivative bound for a product of coordinate sine factors over a finite set of coordinates. -/
theorem norm_iteratedFDeriv_prod_sineFactor_le (a : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i)
    (s : Finset (Fin d)) (m : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ m (fun z : Euc d => ∏ i ∈ s, sineFactor (a i) (z i)) x‖ ≤
      Real.sqrt 2 ^ s.card * (∑ i ∈ s, a i) ^ m := by
  induction s using Finset.induction_on generalizing m with
  | empty =>
    cases m with
    | zero => simp
    | succ m =>
      simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero m)]
  | insert i s hi ih =>
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun z : Euc d => sineFactor (a i) (z i)) :=
      (contDiff_sineFactor _).comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
    have hG : ContDiff ℝ (⊤ : ℕ∞) (fun z : Euc d => ∏ j ∈ s, sineFactor (a j) (z j)) :=
      contDiff_prod fun j _ => (contDiff_sineFactor _).comp
        (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
    have hfun : (fun z : Euc d => ∏ j ∈ insert i s, sineFactor (a j) (z j)) =
        fun z => sineFactor (a i) (z i) * ∏ j ∈ s, sineFactor (a j) (z j) := by
      funext z
      rw [Finset.prod_insert hi]
    rw [hfun]
    refine (norm_iteratedFDeriv_mul_le hF hG x (by exact_mod_cast le_top)).trans ?_
    rw [Finset.card_insert_of_notMem hi, Finset.sum_insert hi, add_pow, pow_succ, mul_comm
      (Real.sqrt 2 ^ s.card), mul_assoc, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    have hl' : l ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have h1 := norm_iteratedFDeriv_sineFactor_proj_le (ha i) i l x
    have h2 := ih (m - l)
    have hc : (0 : ℝ) ≤ (m.choose l : ℝ) := Nat.cast_nonneg _
    calc (m.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun z : Euc d => sineFactor (a i) (z i)) x‖ *
          ‖iteratedFDeriv ℝ (m - l) (fun z : Euc d => ∏ j ∈ s, sineFactor (a j) (z j)) x‖
        ≤ (m.choose l : ℝ) * (Real.sqrt 2 * a i ^ l) *
          (Real.sqrt 2 ^ s.card * (∑ j ∈ s, a j) ^ (m - l)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (norm_nonneg _)
            (mul_nonneg hc (mul_nonneg (Real.sqrt_nonneg 2) (pow_nonneg (ha i) l)))
      _ = _ := by ring

/-- The frequency `π (k_i + 1)` of a sine mode is at most the eigenvalue. -/
theorem frequency_le_dirichletEigenvalue (k : Fin d → ℕ) (i : Fin d) :
    Real.pi * ((k i : ℝ) + 1) ≤ dirichletEigenvalue k := by
  have h1 : (1 : ℝ) ≤ Real.pi * ((k i : ℝ) + 1) := by
    have := Real.pi_gt_three
    have : (1 : ℝ) ≤ (k i : ℝ) + 1 := by linarith [(Nat.cast_nonneg (k i) : (0 : ℝ) ≤ k i)]
    nlinarith
  have h2 : (Real.pi * ((k i : ℝ) + 1)) ^ 2 ≤ dirichletEigenvalue k :=
    sineFreqSq_le_dirichletEigenvalue i k
  nlinarith

/-- **Derivative bound for a sine mode**: `‖D^m φ_k‖ ≤ (√2)^d (d λ_k)^m`. -/
theorem norm_iteratedFDeriv_sineMode_le (k : Fin d → ℕ) (m : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ m (sineMode k) x‖ ≤ Real.sqrt 2 ^ d * (d * dirichletEigenvalue k) ^ m := by
  have hfun : sineMode k =
      fun z : Euc d => ∏ i ∈ Finset.univ, sineFactor (Real.pi * ((k i : ℝ) + 1)) (z i) := rfl
  rw [hfun]
  refine (norm_iteratedFDeriv_prod_sineFactor_le (fun i => Real.pi * ((k i : ℝ) + 1))
    (fun i => by positivity) Finset.univ m x).trans ?_
  rw [Finset.card_univ, Fintype.card_fin]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => by positivity) ?_
    m) (by positivity)
  calc ∑ i, Real.pi * ((k i : ℝ) + 1) ≤ ∑ _i : Fin d, dirichletEigenvalue k :=
        Finset.sum_le_sum fun i _ => frequency_le_dirichletEigenvalue k i
    _ = d * dirichletEigenvalue k := by simp

/-- The eigenvalues are at least `1` in dimension at least one. -/
theorem one_le_dirichletEigenvalue (hd : 1 ≤ d) (k : Fin d → ℕ) : 1 ≤ dirichletEigenvalue k := by
  have h1 : (1 : ℝ) ≤ Real.pi * ((k ⟨0, hd⟩ : ℝ) + 1) := by
    have := Real.pi_gt_three
    have : (1 : ℝ) ≤ (k ⟨0, hd⟩ : ℝ) + 1 := by
      linarith [(Nat.cast_nonneg (k ⟨0, hd⟩) : (0 : ℝ) ≤ k ⟨0, hd⟩)]
    nlinarith
  exact h1.trans (frequency_le_dirichletEigenvalue k ⟨0, hd⟩)

/-- Every polynomial moment of the coefficients of the Dirichlet inverse is summable. -/
theorem summable_pow_mul_abs_inverseCoeff (hd : 1 ≤ d) {D : ℝ} (hD : 0 < D) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) (m : ℕ) :
    Summable fun k : Fin d → ℕ =>
      dirichletEigenvalue k ^ m * |(D * dirichletEigenvalue k)⁻¹ * sineCoeff f k| := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg
    (pow_nonneg (dirichletEigenvalue_pos hd k).le _) (abs_nonneg _)) (fun k => ?_)
    ((summable_pow_mul_abs_sineCoeff hd f hf m).mul_left D⁻¹)
  have h1 := one_le_dirichletEigenvalue hd k
  have hpos : 0 < dirichletEigenvalue k := dirichletEigenvalue_pos hd k
  have h2 : (D * dirichletEigenvalue k)⁻¹ ≤ D⁻¹ := by
    rw [mul_inv]
    exact mul_le_of_le_one_right (inv_nonneg.2 hD.le) (inv_le_one_of_one_le₀ h1)
  rw [abs_mul, abs_of_pos (inv_pos.2 (mul_pos hD hpos))]
  calc dirichletEigenvalue k ^ m * ((D * dirichletEigenvalue k)⁻¹ * |sineCoeff f k|)
      = (D * dirichletEigenvalue k)⁻¹ * (dirichletEigenvalue k ^ m * |sineCoeff f k|) := by ring
    _ ≤ D⁻¹ * (dirichletEigenvalue k ^ m * |sineCoeff f k|) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg (pow_nonneg hpos.le _) (abs_nonneg _))

/-- The `j`-th derivative of a term of the Dirichlet inverse series is bounded by a summable
sequence. -/
theorem norm_iteratedFDeriv_inverseTerm_le (a : ℝ) (k : Fin d → ℕ) (j : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (fun z => a * sineMode k z) x‖ ≤
      Real.sqrt 2 ^ d * d ^ j * (dirichletEigenvalue k ^ j * |a|) := by
  have h := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (i := j) (a := a) (f := sineMode k) (x := x)
    ((contDiff_sineMode k).of_le (by exact_mod_cast le_top)).contDiffAt
  simp only [smul_eq_mul] at h
  rw [h, norm_smul, Real.norm_eq_abs]
  calc |a| * ‖iteratedFDeriv ℝ j (sineMode k) x‖
      ≤ |a| * (Real.sqrt 2 ^ d * (d * dirichletEigenvalue k) ^ j) :=
        mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_sineMode_le k j x) (abs_nonneg a)
    _ = _ := by rw [mul_pow]; ring

/-- A sine series whose coefficients have every polynomial moment in the eigenvalue summable is
smooth: the termwise derivatives are summable. -/
theorem contDiff_sineSeries {a : (Fin d → ℕ) → ℝ}
    (hs : ∀ m : ℕ, Summable fun k : Fin d → ℕ => dirichletEigenvalue k ^ m * |a k|) :
    ContDiff ℝ (⊤ : ℕ∞) (sineSeries a) := by
  have hv : ∀ j : ℕ, Summable fun k : Fin d → ℕ => Real.sqrt 2 ^ d * d ^ j *
      (dirichletEigenvalue k ^ j * |a k|) := fun j => (hs j).mul_left _
  exact contDiff_tsum (N := (⊤ : ℕ∞)) (f := fun k z => a k * sineMode k z)
    (fun k => contDiff_const.mul ((contDiff_sineMode k).of_le (by exact_mod_cast le_top)))
    (fun j _ => hv j) (fun j k x _ => norm_iteratedFDeriv_inverseTerm_le _ k j x)

/-- A rapidly decaying sine series is `C^n` for every natural number `n`. -/
theorem contDiff_sineSeries_nat {a : (Fin d → ℕ) → ℝ}
    (hs : ∀ m : ℕ, Summable fun k : Fin d → ℕ => dirichletEigenvalue k ^ m * |a k|) (n : ℕ) :
    ContDiff ℝ n (sineSeries a) :=
  (contDiff_sineSeries hs).of_le (by exact_mod_cast le_top)

/-- The iterated derivatives of a rapidly decaying sine series are the sums of the iterated
derivatives of the terms. -/
theorem iteratedFDeriv_sineSeries {a : (Fin d → ℕ) → ℝ}
    (hs : ∀ m : ℕ, Summable fun k : Fin d → ℕ => dirichletEigenvalue k ^ m * |a k|) (j : ℕ)
    (x : Euc d) :
    iteratedFDeriv ℝ j (sineSeries a) x =
      ∑' k : Fin d → ℕ, iteratedFDeriv ℝ j (fun z => a k * sineMode k z) x := by
  have hv : ∀ j : ℕ, Summable fun k : Fin d → ℕ => Real.sqrt 2 ^ d * d ^ j *
      (dirichletEigenvalue k ^ j * |a k|) := fun j => (hs j).mul_left _
  exact iteratedFDeriv_tsum_apply (N := (⊤ : ℕ∞)) (f := fun k z => a k * sineMode k z)
    (fun k => contDiff_const.mul ((contDiff_sineMode k).of_le (by exact_mod_cast le_top)))
    (fun j _ => hv j) (fun j k x _ => norm_iteratedFDeriv_inverseTerm_le _ k j x) le_top x

/-- The Dirichlet inverse is the sine series with coefficients `(Dλ_k)⁻¹ ⟨f, φ_k⟩`. -/
theorem dirichletInverse_eq_sineSeries (D : ℝ) (f : Euc d → ℝ) :
    dirichletInverse D f = sineSeries fun k => (D * dirichletEigenvalue k)⁻¹ * sineCoeff f k :=
  rfl

/-- The Dirichlet inverse of a test function is smooth, and its iterated derivatives are the sums
of the iterated derivatives of the terms. -/
theorem iteratedFDeriv_dirichletInverse (hd : 1 ≤ d) {D : ℝ} (hD : 0 < D) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) (j : ℕ) (x : Euc d) :
    iteratedFDeriv ℝ j (dirichletInverse D f) x = ∑' k : Fin d → ℕ, iteratedFDeriv ℝ j
      (fun z => (D * dirichletEigenvalue k)⁻¹ * sineCoeff f k * sineMode k z) x := by
  rw [dirichletInverse_eq_sineSeries]
  exact iteratedFDeriv_sineSeries (summable_pow_mul_abs_inverseCoeff hd hD f hf) j x

/-- The Dirichlet inverse of a test function is smooth. -/
theorem contDiff_dirichletInverse (hd : 1 ≤ d) {D : ℝ} (hD : 0 < D) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) : ContDiff ℝ (⊤ : ℕ∞) (dirichletInverse D f) := by
  rw [dirichletInverse_eq_sineSeries]
  exact contDiff_sineSeries (summable_pow_mul_abs_inverseCoeff hd hD f hf)

/-- The Laplacian as a continuous linear functional of the second derivative. -/
def laplacianCLM (d : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Euc d) ℝ →L[ℝ] ℝ :=
  ∑ i : Fin d, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
    ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]

/-- The Laplacian of a function is the functional `laplacianCLM` of its second derivative. -/
theorem laplacianSum_eq_laplacianCLM (g : Euc d → ℝ) (z : Euc d) :
    laplacianSum g z = laplacianCLM d (iteratedFDeriv ℝ 2 g z) := by
  simp [laplacianSum, laplacianCLM]

/-- The Laplacian of a multiple of a sine mode. -/
theorem laplacianSum_const_mul_sineMode (a : ℝ) (k : Fin d → ℕ) (z : Euc d) :
    laplacianSum (fun w => a * sineMode k w) z =
      -(a * (dirichletEigenvalue k * sineMode k z)) := by
  have h := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (i := (2 : ℕ)) (a := a) (f := sineMode k)
    (x := z) (contDiff_sineMode_nat k 2).contDiffAt
  simp only [smul_eq_mul] at h
  rw [laplacianSum_eq_laplacianCLM, h, map_smul, ← laplacianSum_eq_laplacianCLM,
    laplacianSum_sineMode, smul_eq_mul]
  ring

/-- **Laplacian of a sine series**: `Δ Σ_k a_k φ_k = Σ_k −λ_k a_k φ_k`. -/
theorem laplacianSum_sineSeries {a : (Fin d → ℕ) → ℝ}
    (hs : ∀ m : ℕ, Summable fun k : Fin d → ℕ => dirichletEigenvalue k ^ m * |a k|)
    (z : Euc d) :
    laplacianSum (sineSeries a) z =
      ∑' k : Fin d → ℕ, -(a k * (dirichletEigenvalue k * sineMode k z)) := by
  have hsum : Summable fun k : Fin d → ℕ => iteratedFDeriv ℝ 2
      (fun w => a k * sineMode k w) z :=
    Summable.of_norm_bounded ((hs 2).mul_left (Real.sqrt 2 ^ d * d ^ 2)) fun k =>
      norm_iteratedFDeriv_inverseTerm_le _ k 2 z
  rw [laplacianSum_eq_laplacianCLM, iteratedFDeriv_sineSeries hs 2 z,
    (laplacianCLM d).map_tsum hsum]
  refine tsum_congr fun k => ?_
  rw [← laplacianSum_eq_laplacianCLM, laplacianSum_const_mul_sineMode]

/-- The Laplacian of the Dirichlet inverse is the sum of the Laplacians of the terms. -/
theorem laplacianSum_dirichletInverse (hd : 1 ≤ d) {D : ℝ} (hD : 0 < D) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) (z : Euc d) :
    laplacianSum (dirichletInverse D f) z = ∑' k : Fin d → ℕ,
      -((D * dirichletEigenvalue k)⁻¹ * sineCoeff f k *
        (dirichletEigenvalue k * sineMode k z)) := by
  rw [dirichletInverse_eq_sineSeries]
  exact laplacianSum_sineSeries (summable_pow_mul_abs_inverseCoeff hd hD f hf) z

/-- A sine mode vanishes on the boundary of the cube. -/
theorem sineMode_eq_zero_of_mem_closure_diff {z : Euc d}
    (hz : z ∈ closure (unitCube d) \ unitCube d) (k : Fin d → ℕ) : sineMode k z = 0 := by
  obtain ⟨hz1, hz2⟩ := hz
  have : ∃ i, ¬(0 < z i ∧ z i < 1) := by
    by_contra h
    push Not at h
    exact hz2 h
  obtain ⟨i, hi⟩ := this
  have hb := coord_mem_Icc_of_mem_closure_unitCube hz1 i
  have hi' : z i = 0 ∨ z i = 1 := by
    by_contra h
    push Not at h
    exact hi ⟨lt_of_le_of_ne hb.1 (Ne.symm h.1), lt_of_le_of_ne hb.2 h.2⟩
  unfold sineMode
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rcases hi' with h | h
  · simp [h]
  · have : Real.sin (Real.pi * ((k i : ℝ) + 1) * z i) = 0 := by
      rw [h, mul_one, mul_comm]
      have := Real.sin_nat_mul_pi (k i + 1)
      push_cast at this
      exact this
    rw [this, mul_zero]

/-- A sine series vanishes on the boundary of the cube. -/
theorem sineSeries_eq_zero_of_mem_closure_diff (a : (Fin d → ℕ) → ℝ) {z : Euc d}
    (hz : z ∈ closure (unitCube d) \ unitCube d) : sineSeries a z = 0 := by
  unfold sineSeries
  simp [sineMode_eq_zero_of_mem_closure_diff hz]

/-- **The form of the Dirichlet inverse as a series**: `∫_Q f u = Σ_k (Dλ_k)⁻¹ ⟨f, φ_k⟩²`. -/
theorem hasSum_integral_mul_dirichletInverse (hd : 1 ≤ d) {D : ℝ} (hD : 0 < D) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) :
    HasSum (fun k : Fin d → ℕ => (D * dirichletEigenvalue k)⁻¹ * sineCoeff f k ^ 2)
      (∫ z in unitCube d, f z * dirichletInverse D f z) := by
  have := isFiniteMeasure_restrict_unitCube (d := d)
  obtain ⟨B, hB⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2.1
  set F : (Fin d → ℕ) → Euc d → ℝ := fun k z =>
    f z * ((D * dirichletEigenvalue k)⁻¹ * sineCoeff f k * sineMode k z) with hF
  have hb : ∀ k z, ‖F k z‖ ≤ B * (|(D * dirichletEigenvalue k)⁻¹ * sineCoeff f k| *
      Real.sqrt 2 ^ d) := fun k z => by
    rw [hF, norm_mul, norm_mul, Real.norm_eq_abs (_ * _)]
    exact mul_le_mul (hB z) (mul_le_mul_of_nonneg_left (norm_sineMode_le k z) (abs_nonneg _))
      (by positivity) ((norm_nonneg _).trans (hB z))
  have hcont : ∀ k, Continuous (F k) := fun k =>
    hf.1.continuous.mul (continuous_const.mul (contDiff_sineMode k).continuous)
  have hint : ∀ k, Integrable (F k) (volume.restrict (unitCube d)) := fun k =>
    Integrable.of_bound (hcont k).aestronglyMeasurable _ (Filter.Eventually.of_forall (hb k))
  have hsum : Summable fun k => ∫ z, ‖F k z‖ ∂(volume.restrict (unitCube d)) := by
    have hs0 := (summable_pow_mul_abs_inverseCoeff hd hD f hf 0).mul_right
      (B * Real.sqrt 2 ^ d * (volume (unitCube d)).toReal)
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun z => norm_nonneg _)
      (fun k => ?_) hs0
    calc ∫ z, ‖F k z‖ ∂(volume.restrict (unitCube d))
        ≤ ‖∫ z, ‖F k z‖ ∂(volume.restrict (unitCube d))‖ := Real.le_norm_self _
      _ ≤ (B * (|(D * dirichletEigenvalue k)⁻¹ * sineCoeff f k| * Real.sqrt 2 ^ d)) *
          (volume.restrict (unitCube d)).real Set.univ :=
          norm_integral_le_of_norm_le_const
            (Filter.Eventually.of_forall fun z => by rw [norm_norm]; exact hb k z)
      _ = _ := by
          rw [Measure.real, Measure.restrict_apply_univ, pow_zero, one_mul]
          ring
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have h1 : ∀ k, ∫ z in unitCube d, F k z =
      (D * dirichletEigenvalue k)⁻¹ * sineCoeff f k ^ 2 := fun k => by
    have : ∀ z, F k z = ((D * dirichletEigenvalue k)⁻¹ * sineCoeff f k) * (f z * sineMode k z) :=
      fun z => by rw [hF]; ring
    simp_rw [this]
    rw [integral_const_mul]
    unfold sineCoeff
    ring
  have h2 : ∫ z in unitCube d, ∑' k, F k z = ∫ z in unitCube d, f z * dirichletInverse D f z := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show ∑' k, F k z = f z * ∑' k, _
    rw [tsum_mul_left]
  rw [← h2]
  simpa only [h1] using h

/-- **The Dirichlet inverse of a test function**: for `f ∈ C_c^∞((0,1)^d)` and `D > 0`,
`u = (−DΔ_Q)⁻¹ f = Σ_k (Dλ_k)⁻¹ ⟨f, φ_k⟩ φ_k` is smooth on `ℝ^d` (the termwise derivatives of
every order are summable since the coefficients decay faster than any power of `λ_k`), solves
`−DΔu = f` in `Q` (termwise
`Δφ_k = −λ_k φ_k` and the sine series of `f` converges to `f`), vanishes on `∂Q` (every sine mode
does), and `∫_Q f u = Σ_k (Dλ_k)⁻¹ ⟨f, φ_k⟩² = dirichletForm D f`. -/
theorem dirichletInverse_spec (hd : 1 ≤ d) (D : ℝ) (hD : 0 < D) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) :
    (∀ k : ℕ, ContDiff ℝ k (dirichletInverse D f)) ∧
      (∀ z ∈ unitCube d, -(D * laplacianSum (dirichletInverse D f) z) = f z) ∧
      (∀ z ∈ closure (unitCube d) \ unitCube d, dirichletInverse D f z = 0) ∧
      dirichletForm D f = ∫ z in unitCube d, f z * dirichletInverse D f z := by
  refine ⟨fun k => (contDiff_dirichletInverse hd hD f hf).of_le (by exact_mod_cast le_top),
    fun z hz => ?_, fun z hz => ?_, ?_⟩
  · rw [laplacianSum_dirichletInverse hd hD f hf z]
    have h1 : ∀ k : Fin d → ℕ, -((D * dirichletEigenvalue k)⁻¹ * sineCoeff f k *
        (dirichletEigenvalue k * sineMode k z)) = -(D⁻¹ * (sineCoeff f k * sineMode k z)) :=
      fun k => by
        have := (dirichletEigenvalue_pos hd k).ne'
        field_simp
    simp_rw [h1]
    rw [tsum_neg, tsum_mul_left, (hasSum_sineSeries hd f hf z hz).tsum_eq]
    field_simp
  · rw [dirichletInverse_eq_sineSeries]
    exact sineSeries_eq_zero_of_mem_closure_diff _ hz
  · have h := hasSum_integral_mul_dirichletInverse hd hD f hf
    have hnn : ∀ k : Fin d → ℕ, 0 ≤ (D * dirichletEigenvalue k)⁻¹ * sineCoeff f k ^ 2 :=
      fun k => by
        have := dirichletEigenvalue_pos hd k
        positivity
    unfold dirichletForm
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn h.summable,
      ENNReal.toReal_ofReal (tsum_nonneg hnn), h.tsum_eq]

end LatticeProb.Analysis.Schauder

end
