import LatticeProb.Analysis.Elliptic.Dirichlet

/-!
# Scalar ODE comparison on an interval

The maximum principle and a quadratic barrier bound scalar Dirichlet solutions.
The scalar equation and mean value theorem give derivative and Hölder increment bounds.
-/

namespace LatticeProb.Elliptic

open Set Filter
open scoped Topology ENNReal

noncomputable section

/-- At a local maximum, an existing scalar second derivative cannot be positive. -/
theorem deriv_deriv_nonpos_of_localMax {v : ℝ → ℝ} {x : ℝ}
    (hmax : IsLocalMax v x) (hv : ContinuousAt v x) :
    deriv (deriv v) x ≤ 0 := by
  by_contra! hpos
  have hmin := isLocalMin_of_deriv_deriv_pos hpos hmax.deriv_eq_zero hv
  have heq : v =ᶠ[𝓝 x] fun _ => v x := by
    filter_upwards [hmax, hmin] with y hymax hymin
    exact le_antisymm hymax hymin
  have hz := heq.deriv.deriv_eq
  simp only [deriv_const', deriv_const] at hz
  linarith

/-- A strict scalar elliptic subsolution with nonpositive endpoint values is nonpositive. -/
theorem le_zero_of_strict_ode {α β μ a : ℝ} {v : ℝ → ℝ}
    (hαβ : α < β) (hμ : 0 ≤ μ) (ha : 0 < a)
    (hv : ContinuousOn v (Icc α β)) (hα : v α ≤ 0) (hβ : v β ≤ 0)
    (hode : ∀ x ∈ Ioo α β, μ * v x - a * deriv (deriv v) x < 0) :
    ∀ x ∈ Icc α β, v x ≤ 0 := by
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨α, left_mem_Icc.mpr hαβ.le⟩ hv
  have hyv : v y ≤ 0 := by
    by_contra! hpos
    have hyα : α < y := lt_of_le_of_ne hy.1 (by
      intro heq
      subst y
      exact (not_lt_of_ge hα) hpos)
    have hyβ : y < β := lt_of_le_of_ne hy.2 (by
      intro heq
      subst y
      exact (not_lt_of_ge hβ) hpos)
    have hlocal := hmax.isLocalMax (Icc_mem_nhds hyα hyβ)
    have hsecond := deriv_deriv_nonpos_of_localMax hlocal
      ((hv y hy).continuousAt (Icc_mem_nhds hyα hyβ))
    have hmass := mul_nonneg hμ hpos.le
    have hdiff := mul_nonpos_of_nonneg_of_nonpos ha.le hsecond
    linarith [hode y ⟨hyα, hyβ⟩]
  exact fun x hx => (hmax hx).trans hyv

/-- A scalar elliptic subsolution with nonpositive endpoint data obeys the weak principle. -/
theorem le_zero_of_ode {α β μ a : ℝ} {v : ℝ → ℝ}
    (hαβ : α < β) (hμ : 0 ≤ μ) (ha : 0 < a)
    (hv : ContinuousOn v (Icc α β))
    (hd : ∀ x ∈ Ioo α β, DifferentiableAt ℝ v x)
    (hdd : ∀ x ∈ Ioo α β, DifferentiableAt ℝ (deriv v) x)
    (hα : v α ≤ 0) (hβ : v β ≤ 0)
    (hode : ∀ x ∈ Ioo α β, μ * v x - a * deriv (deriv v) x ≤ 0) :
    ∀ x ∈ Icc α β, v x ≤ 0 := by
  intro x hx
  let q : ℝ → ℝ := fun t => (t - α) * (t - β)
  have hq : ∀ t ∈ Icc α β, q t ≤ 0 := fun t ht =>
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.1) (sub_nonpos.mpr ht.2)
  have hpert (ε : ℝ) (hε : 0 < ε) : v x + ε * q x ≤ 0 := by
    let w : ℝ → ℝ := fun t => v t + ε * q t
    have hq' (t : ℝ) : HasDerivAt q (2 * t - α - β) t := by
      apply (((hasDerivAt_id t).sub_const α).mul
        ((hasDerivAt_id t).sub_const β)).congr_deriv
      dsimp
      ring
    have hw' (t : ℝ) (ht : t ∈ Ioo α β) :
        deriv w t = deriv v t + ε * (2 * t - α - β) :=
      ((hd t ht).hasDerivAt.add ((hq' t).const_mul ε)).deriv
    have hw'' (t : ℝ) (ht : t ∈ Ioo α β) :
        deriv (deriv w) t = deriv (deriv v) t + 2 * ε := by
      have heq : deriv w =ᶠ[𝓝 t] fun s => deriv v s + ε * (2 * s - α - β) := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
        exact hw' s hs
      rw [heq.deriv_eq]
      rw [deriv_fun_add (hdd t ht) (by fun_prop)]
      have hp : HasDerivAt (fun s : ℝ => ε * (2 * s - α - β)) (2 * ε) t := by
        apply (((((hasDerivAt_id t).const_mul 2).sub_const α).sub_const β).const_mul
          ε).congr_deriv
        ring
      rw [hp.deriv]
    apply le_zero_of_strict_ode hαβ hμ ha (v := w)
      (hv.add (by fun_prop)) (by simpa [w, q] using hα)
      (by simpa [w, q] using hβ) ?_ x hx
    intro t ht
    rw [hw'' t ht]
    have hqμ := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hμ hε.le)
      (hq t (Ioo_subset_Icc_self ht))
    have hstrict := mul_pos ha hε
    dsimp [w]
    nlinarith [hode t ht]
  by_contra! hvx
  let ε := v x / (2 * (|q x| + 1))
  have hε : 0 < ε := div_pos hvx (by positivity)
  have heq : ε * (2 * (|q x| + 1)) = v x := by
    dsimp [ε]
    exact div_mul_cancel₀ _ (by positivity)
  have hbound := neg_abs_le (q x)
  have hres := hpert ε hε
  nlinarith

/-- The quadratic interval barrier has the exact constant second derivative `-M / a`. -/
theorem interval_barrier_derivatives (α β M a t : ℝ) :
    HasDerivAt (fun s : ℝ => M / (2 * a) * (s - α) * (β - s))
      (M / (2 * a) * (α + β - 2 * t)) t ∧
    HasDerivAt (fun s : ℝ => M / (2 * a) * (α + β - 2 * s))
      (-M / a) t := by
  constructor
  · apply (((((hasDerivAt_id t).sub_const α).const_mul (M / (2 * a))).mul
      ((hasDerivAt_id t).const_sub β))).congr_deriv
    dsimp
    ring
  · apply ((((hasDerivAt_id t).const_mul 2).const_sub (α + β)).const_mul
      (M / (2 * a))).congr_deriv
    ring

/-- Subtracting a smooth barrier from a twice differentiable scalar function subtracts
its prescribed second derivative on the open interval. -/
theorem deriv_deriv_sub_on_interval {α β : ℝ} {v b b' : ℝ → ℝ}
    (hd : ∀ x ∈ Ioo α β, DifferentiableAt ℝ v x)
    (hdd : ∀ x ∈ Ioo α β, DifferentiableAt ℝ (deriv v) x)
    (hb : ∀ x, HasDerivAt b (b' x) x) {x : ℝ} (hx : x ∈ Ioo α β)
    {b'' : ℝ} (hb' : HasDerivAt b' b'' x) :
    deriv (deriv (fun t => v t - b t)) x = deriv (deriv v) x - b'' := by
  have heq : deriv (fun t => v t - b t) =ᶠ[𝓝 x] fun t => deriv v t - b' t := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact ((hd t ht).hasDerivAt.sub (hb t)).deriv
  rw [heq.deriv_eq]
  exact ((hdd x hx).hasDerivAt.sub hb').deriv

/-- Scalar interval comparison against the quadratic barrier gives the sharp pointwise bound. -/
theorem le_interval_barrier {α β μ a M : ℝ} {v : ℝ → ℝ}
    (hαβ : α < β) (hμ : 0 ≤ μ) (ha : 0 < a) (hM : 0 ≤ M)
    (hv : ContinuousOn v (Icc α β))
    (hd : ∀ x ∈ Ioo α β, DifferentiableAt ℝ v x)
    (hdd : ∀ x ∈ Ioo α β, DifferentiableAt ℝ (deriv v) x)
    (hα : v α ≤ 0) (hβ : v β ≤ 0)
    (hode : ∀ x ∈ Ioo α β, μ * v x - a * deriv (deriv v) x ≤ M) :
    ∀ x ∈ Icc α β, v x ≤ M / (2 * a) * (x - α) * (β - x) := by
  let b : ℝ → ℝ := fun t => M / (2 * a) * (t - α) * (β - t)
  let b' : ℝ → ℝ := fun t => M / (2 * a) * (α + β - 2 * t)
  have hb (t : ℝ) : HasDerivAt b (b' t) t :=
    (interval_barrier_derivatives α β M a t).1
  have hb' (t : ℝ) : HasDerivAt b' (-M / a) t :=
    (interval_barrier_derivatives α β M a t).2
  have hsecond (t : ℝ) (ht : t ∈ Ioo α β) :=
    deriv_deriv_sub_on_interval hd hdd hb ht (hb' t)
  have hdsub (t : ℝ) (ht : t ∈ Ioo α β) :
      DifferentiableAt ℝ (fun s => v s - b s) t :=
    (hd t ht).sub (hb t).differentiableAt
  have hddsub (t : ℝ) (ht : t ∈ Ioo α β) :
      DifferentiableAt ℝ (deriv (fun s => v s - b s)) t := by
    have heq : deriv (fun s => v s - b s) =ᶠ[𝓝 t] fun s => deriv v s - b' s := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact ((hd s hs).hasDerivAt.sub (hb s)).deriv
    exact ((hdd t ht).sub (hb' t).differentiableAt).congr_of_eventuallyEq heq
  have hcomp := le_zero_of_ode hαβ hμ ha (v := fun t => v t - b t)
    (hv.sub (by fun_prop)) hdsub hddsub (by simpa [b] using hα)
    (by simpa [b] using hβ) (fun t ht => by
      rw [hsecond t ht]
      have hbnonneg : 0 ≤ b t := by
        dsimp [b]
        exact mul_nonneg (mul_nonneg (div_nonneg hM (by positivity))
          (sub_nonneg.mpr ht.1.le)) (sub_nonneg.mpr ht.2.le)
      have hmass := mul_nonneg hμ hbnonneg
      have hcancel : a * (-M / a) = -M := mul_div_cancel₀ _ ha.ne'
      nlinarith [hode t ht])
  intro x hx
  exact sub_nonpos.mp (hcomp x hx)

/-- The interval barrier is bounded above by its value at the midpoint. -/
theorem interval_barrier_le (α β M a x : ℝ) (hM : 0 ≤ M) (ha : 0 < a) :
    M / (2 * a) * (x - α) * (β - x) ≤ (β - α) ^ 2 / (8 * a) * M := by
  have hsq : (x - α) * (β - x) ≤ (β - α) ^ 2 / 4 := by
    nlinarith [sq_nonneg (2 * x - α - β)]
  calc
    M / (2 * a) * (x - α) * (β - x) =
        M / (2 * a) * ((x - α) * (β - x)) := by ring
    _ ≤ M / (2 * a) * ((β - α) ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left hsq (div_nonneg hM (by positivity))
    _ = (β - α) ^ 2 / (8 * a) * M := by ring

/-- A twice differentiable scalar Dirichlet solution has the sharp interval supremum bound. -/
theorem abs_le_interval_barrier {α β μ a M : ℝ} {v : ℝ → ℝ}
    (hαβ : α < β) (hμ : 0 ≤ μ) (ha : 0 < a) (hM : 0 ≤ M)
    (hv : ContinuousOn v (Icc α β)) (hc : ContDiffOn ℝ 2 v (Ioo α β))
    (hα : v α = 0) (hβ : v β = 0)
    (hode : ∀ x ∈ Ioo α β, |μ * v x - a * deriv (deriv v) x| ≤ M) :
    ∀ x ∈ Icc α β, |v x| ≤ (β - α) ^ 2 / (8 * a) * M := by
  have hd (x : ℝ) (hx : x ∈ Ioo α β) :=
    (hc.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)
  have hcd : ContDiffOn ℝ 1 (deriv v) (Ioo α β) :=
    hc.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdd (x : ℝ) (hx : x ∈ Ioo α β) :=
    (hcd.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)
  have hupper := le_interval_barrier hαβ hμ ha hM hv hd hdd hα.le hβ.le
    (fun x hx => (le_abs_self _).trans (hode x hx))
  have hnegderiv : deriv (fun t => -v t) = fun t => -deriv v t := by
    ext t
    exact deriv.fun_neg
  have hdneg (x : ℝ) (hx : x ∈ Ioo α β) :
      DifferentiableAt ℝ (fun t => -v t) x := (hd x hx).neg
  have hddneg (x : ℝ) (hx : x ∈ Ioo α β) :
      DifferentiableAt ℝ (deriv (fun t => -v t)) x := by
    rw [hnegderiv]
    exact (hdd x hx).neg
  have hlower := le_interval_barrier hαβ hμ ha hM hv.neg hdneg hddneg
    (by simp [hα]) (by simp [hβ]) (fun x hx => by
      simp only [deriv.neg', deriv.fun_neg, Pi.neg_apply]
      have hh := (abs_le.mp (hode x hx)).1
      linarith)
  intro x hx
  apply abs_le.mpr
  have hb := interval_barrier_le α β M a x hM ha
  constructor
  · have hh : -v x ≤ M / (2 * a) * (x - α) * (β - x) := hlower x hx
    linarith
  · exact (hupper x hx).trans hb

/-- The scalar equation bounds the second derivative from bounds for the solution and datum. -/
theorem abs_second_deriv_le_of_ode {μ a B M : ℝ} {v f : ℝ → ℝ} {x : ℝ}
    (hμ : 0 ≤ μ) (ha : 0 < a) (hv : |v x| ≤ B) (hf : |f x| ≤ M)
    (hode : μ * v x - a * deriv (deriv v) x = f x) :
    |deriv (deriv v) x| ≤ (μ * B + M) / a := by
  apply (le_div_iff₀ ha).mpr
  have heq : a * deriv (deriv v) x = μ * v x - f x := by linarith
  calc
    |deriv (deriv v) x| * a = |a * deriv (deriv v) x| := by
      rw [abs_mul, abs_of_pos ha, mul_comm]
    _ = |μ * v x - f x| := congrArg abs heq
    _ ≤ |μ * v x| + |f x| := abs_sub _ _
    _ = μ * |v x| + |f x| := by rw [abs_mul, abs_of_nonneg hμ]
    _ ≤ μ * B + M := add_le_add (mul_le_mul_of_nonneg_left hv hμ) hf

/-- Rolle's theorem and the mean value theorem bound the first derivative by interval length
 times a uniform bound on the second derivative. -/
theorem abs_deriv_le_of_dirichlet {α β K : ℝ} {v : ℝ → ℝ}
    (hαβ : α < β) (hK : 0 ≤ K) (hv : ContinuousOn v (Icc α β))
    (hboundary : v α = v β)
    (hdd : ∀ x ∈ Ioo α β, DifferentiableAt ℝ (deriv v) x)
    (hsecond : ∀ x ∈ Ioo α β, |deriv (deriv v) x| ≤ K) :
    ∀ x ∈ Ioo α β, |deriv v x| ≤ (β - α) * K := by
  obtain ⟨c, hc, hzero⟩ := exists_deriv_eq_zero hαβ hv hboundary
  intro x hx
  have hmean := Convex.norm_image_sub_le_of_norm_deriv_le hdd
    (fun t ht => by simpa only [Real.norm_eq_abs] using hsecond t ht)
    (convex_Ioo α β) hc hx
  have hdist : |x - c| ≤ β - α := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hc.1, hc.2]
  simpa only [Real.norm_eq_abs, hzero, sub_zero, mul_comm K] using
    hmean.trans (mul_le_mul_of_nonneg_left (by
      simpa only [Real.norm_eq_abs] using hdist) hK)

/-- A derivative bound on the interval gives a quantitative Hölder increment bound. -/
theorem abs_sub_le_rpow_of_deriv_bound {α β σ D : ℝ} {v : ℝ → ℝ}
    (hαβ : α < β) (hσ : 0 < σ) (hσ1 : σ < 1) (hD : 0 ≤ D)
    (hd : ∀ x ∈ Ioo α β, DifferentiableAt ℝ v x)
    (hderiv : ∀ x ∈ Ioo α β, |deriv v x| ≤ D)
    {x y : ℝ} (hx : x ∈ Ioo α β) (hy : y ∈ Ioo α β) :
    |v x - v y| ≤ D * (β - α + 1) * |x - y| ^ σ := by
  have hmean := Convex.norm_image_sub_le_of_norm_deriv_le hd
    (fun t ht => by simpa only [Real.norm_eq_abs] using hderiv t ht)
    (convex_Ioo α β) hy hx
  have hlip : |v x - v y| ≤ D * |x - y| := by
    simpa only [Real.norm_eq_abs] using hmean
  have hdist : |x - y| ≤ β - α := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hscale : |x - y| ≤ (β - α + 1) * |x - y| ^ σ := by
    by_cases hsmall : |x - y| ≤ 1
    · have hp := Real.self_le_rpow_of_le_one (abs_nonneg (x - y)) hsmall hσ1.le
      have hpow := Real.rpow_nonneg (abs_nonneg (x - y)) σ
      exact hp.trans (le_mul_of_one_le_left hpow (by linarith))
    · have hp := Real.one_le_rpow (le_of_not_ge hsmall) hσ.le
      calc
        |x - y| ≤ β - α := hdist
        _ ≤ β - α + 1 := le_add_of_nonneg_right zero_le_one
        _ ≤ (β - α + 1) * |x - y| ^ σ :=
          le_mul_of_one_le_right (by linarith) hp
  calc
    |v x - v y| ≤ D * |x - y| := hlip
    _ ≤ D * ((β - α + 1) * |x - y| ^ σ) := mul_le_mul_of_nonneg_left hscale hD
    _ = D * (β - α + 1) * |x - y| ^ σ := by ring

/-- Subtracting the scalar equation at two points transfers Hölder increment bounds to
 the second derivative, with the diffusion and mass factors explicit. -/
theorem abs_sub_second_deriv_le_of_ode {μ a B M r x y : ℝ} {v f : ℝ → ℝ}
    (hμ : 0 ≤ μ) (ha : 0 < a) (hv : |v x - v y| ≤ B * r)
    (hf : |f x - f y| ≤ M * r)
    (hx : μ * v x - a * deriv (deriv v) x = f x)
    (hy : μ * v y - a * deriv (deriv v) y = f y) :
    |deriv (deriv v) x - deriv (deriv v) y| ≤ (μ * B + M) / a * r := by
  have heq : a * (deriv (deriv v) x - deriv (deriv v) y) =
      μ * (v x - v y) - (f x - f y) := by linarith
  have hbound : a * |deriv (deriv v) x - deriv (deriv v) y| ≤ (μ * B + M) * r := by
    calc
      a * |deriv (deriv v) x - deriv (deriv v) y| =
          |a * (deriv (deriv v) x - deriv (deriv v) y)| := by
        rw [abs_mul, abs_of_pos ha]
      _ = |μ * (v x - v y) - (f x - f y)| := congrArg abs heq
      _ ≤ |μ * (v x - v y)| + |f x - f y| := abs_sub _ _
      _ = μ * |v x - v y| + |f x - f y| := by
        rw [abs_mul, abs_of_nonneg hμ]
      _ ≤ μ * (B * r) + M * r :=
        add_le_add (mul_le_mul_of_nonneg_left hv hμ) hf
      _ = (μ * B + M) * r := by ring
  have hcancel : a * ((μ * B + M) / a * r) = (μ * B + M) * r := by
    rw [← mul_assoc, mul_div_cancel₀ _ ha.ne']
  exact (mul_le_mul_iff_right₀ ha).mp (hbound.trans_eq hcancel.symm)


end

end LatticeProb.Elliptic
