/-
Support lemmas for the Fourier representation of the simple random walk
heat kernel: the character shift identities, the product-to-sum identity,
and integrability of the Fourier integrand over the torus.
-/
import LatticeProb.Walk.Fourier

open MeasureTheory

noncomputable section

namespace LatticeProb

theorem dotSite_add_unit {d : ℕ} (θ : Fin d → ℝ) (z : Site d) (i : Fin d) :
    dotSite θ (z + unit i) = dotSite θ z + θ i := by
  unfold dotSite unit
  simp only [Pi.add_apply, Pi.single_apply, mul_add, Int.cast_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp [mul_ite]

theorem dotSite_sub_unit {d : ℕ} (θ : Fin d → ℝ) (z : Site d) (i : Fin d) :
    dotSite θ (z - unit i) = dotSite θ z - θ i := by
  unfold dotSite unit
  simp only [Pi.sub_apply, Pi.single_apply, mul_sub, Int.cast_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · simp [mul_ite]

theorem cos_mul_cos {d : ℕ} (θ : Fin d → ℝ) (z : Site d) (i : Fin d) :
    Real.cos (θ i) * Real.cos (dotSite θ z)
      = (Real.cos (dotSite θ (z + unit i)) + Real.cos (dotSite θ (z - unit i))) / 2 := by
  rw [dotSite_add_unit, dotSite_sub_unit]
  have h1 : Real.cos (dotSite θ z + θ i)
      = Real.cos (dotSite θ z) * Real.cos (θ i) - Real.sin (dotSite θ z) * Real.sin (θ i) :=
    Real.cos_add _ _
  have h2 : Real.cos (dotSite θ z - θ i)
      = Real.cos (dotSite θ z) * Real.cos (θ i) + Real.sin (dotSite θ z) * Real.sin (θ i) :=
    Real.cos_sub _ _
  rw [h1, h2]
  ring

theorem integrable_fourierHeat_integrand (d : ℕ) (j : ℕ) (w : Site d) :
    Integrable (fun θ : Fin d → ℝ => charFn d θ ^ j * Real.cos (dotSite θ w))
      (torusMeasure d) := by
  haveI : IsFiniteMeasure (torusMeasure d) := by
    unfold torusMeasure; infer_instance
  have hcont : Continuous (fun θ : Fin d → ℝ => charFn d θ ^ j * Real.cos (dotSite θ w)) := by
    by_cases hd : d = 0
    · subst hd
      have hz : ∀ θ : Fin 0 → ℝ, charFn 0 θ = 0 := by
        intro θ; unfold charFn; simp
      have hdot : ∀ θ : Fin 0 → ℝ, dotSite θ w = 0 := by
        intro θ; unfold dotSite; simp
      have hfun : (fun θ : Fin 0 → ℝ => charFn 0 θ ^ j * Real.cos (dotSite θ w))
          = fun _ => (0:ℝ) ^ j * (1:ℝ) := by
        funext θ
        rw [hz θ, hdot θ]; simp
      rw [hfun]
      exact continuous_const
    · have h1 : Continuous (fun θ : Fin d → ℝ => charFn d θ) := by
        unfold charFn
        have hdpos : (d:ℝ) ≠ 0 := by exact_mod_cast hd
        exact (continuous_finsetSum _ fun i _ =>
          Real.continuous_cos.comp (continuous_apply i)).div
          (continuous_const : Continuous (fun _ : Fin d → ℝ => (d:ℝ))) (fun _ => hdpos)
      have h2 : Continuous (fun θ : Fin d → ℝ => dotSite θ w) := by
        unfold dotSite
        exact continuous_finsetSum _ fun i _ =>
          (continuous_apply i).mul (continuous_const : Continuous (fun _ : Fin d → ℝ => (w i : ℝ)))
      exact (h1.pow j).mul (Real.continuous_cos.comp h2)
  have hpow : ∀ (c : ℝ), |c| ≤ 1 → ∀ k : ℕ, |c ^ k| ≤ 1 := by
    intro c hc k
    rw [abs_pow]
    induction k with
    | zero => simp
    | succ n ih =>
        rw [pow_succ']
        have h := mul_le_mul hc ih (pow_nonneg (abs_nonneg c) n) zero_le_one
        simpa using h
  refine Integrable.mono' (g := 1) (integrable_const (1:ℝ)) hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun θ => ?_
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : abs (Real.cos (dotSite θ w)) ≤ 1 := Real.abs_cos_le_one _
  have h2 : abs (charFn d θ ^ j) ≤ 1 := by
    have hle : abs (charFn d θ) ≤ 1 := by
      by_cases hd : d = 0
      · subst hd; unfold charFn; simp
      · unfold charFn
        have hdpos : (0:ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
        have hsum : abs (∑ i : Fin d, Real.cos (θ i)) ≤ (d:ℝ) := by
          refine le_trans (Finset.abs_sum_le_sum_abs (fun i => Real.cos (θ i)) Finset.univ) ?_
          have h1 : ∑ i : Fin d, abs (Real.cos (θ i)) ≤ ∑ i : Fin d, (1:ℝ) :=
            Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
          have h2 : ∑ i : Fin d, (1:ℝ) = (d:ℝ) := by simp
          exact le_trans h1 (by rw [h2])
        have habs : abs ((∑ i : Fin d, Real.cos (θ i)) / (d:ℝ))
            = abs (∑ i : Fin d, Real.cos (θ i)) / (d:ℝ) := by
          rw [abs_div, abs_of_nonneg hdpos.le]
        rw [habs, div_le_one hdpos]
        exact hsum
    exact hpow _ hle j
  have hfin := mul_le_mul h2 h1 (abs_nonneg (Real.cos (dotSite θ w))) zero_le_one
  simpa using hfin

/-- **The Fourier recursion**: the Fourier representation satisfies the same
one-step recursion as the heat kernel, `F_{j+1}(z)` is the average of
`F_j` over the `2d` neighbours of `z`. -/
theorem fourierHeat_succ (d : ℕ) (j : ℕ) (z : Site d) :
    fourierHeat d (j + 1) z
      = (∑ i, (fourierHeat d j (z + unit i) + fourierHeat d j (z - unit i))) / (2 * d) := by
  unfold fourierHeat
  simp only [pow_succ]
  have hident : ∀ θ : Fin d → ℝ,
      (charFn d θ ^ j * charFn d θ) * Real.cos (dotSite θ z)
        = (∑ i, (charFn d θ ^ j * Real.cos (dotSite θ (z + unit i))
              + charFn d θ ^ j * Real.cos (dotSite θ (z - unit i)))) / (2 * d) := by
    intro θ
    unfold charFn
    have h2 : ∀ i : Fin d, Real.cos (θ i) * Real.cos (dotSite θ z)
        = (Real.cos (dotSite θ (z + unit i)) + Real.cos (dotSite θ (z - unit i))) / 2 :=
      fun i => cos_mul_cos θ z i
    field_simp
    have h3 : ∑ x, (Real.cos (dotSite θ (z + unit x)) + Real.cos (dotSite θ (z - unit x)))
        = 2 * Real.cos (dotSite θ z) * ∑ i, Real.cos (θ i) := by
      have h4 : ∑ x, (Real.cos (dotSite θ (z + unit x)) + Real.cos (dotSite θ (z - unit x)))
          = ∑ x, (2 * Real.cos (θ x) * Real.cos (dotSite θ z)) :=
        Finset.sum_congr rfl fun x _ => by
          have hx := h2 x
          linear_combination (-2) * hx
      rw [h4, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [← Finset.mul_sum, h3]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall fun θ => hident θ)]
  rw [integral_div]
  have hint : ∀ i : Fin d, Integrable
      (fun θ : Fin d → ℝ => charFn d θ ^ j * Real.cos (dotSite θ (z + unit i))
        + charFn d θ ^ j * Real.cos (dotSite θ (z - unit i))) (torusMeasure d) :=
    fun i => (integrable_fourierHeat_integrand d j (z + unit i)).add
      (integrable_fourierHeat_integrand d j (z - unit i))
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => hint i)]
  have hkey : ∀ i : Fin d,
      (∫ (a : Fin d → ℝ), charFn d a ^ j * Real.cos (dotSite a (z + unit i))
        + charFn d a ^ j * Real.cos (dotSite a (z - unit i)) ∂torusMeasure d)
      = fourierHeat d j (z + unit i) + fourierHeat d j (z - unit i) :=
    fun i => integral_add (integrable_fourierHeat_integrand d j (z + unit i))
      (integrable_fourierHeat_integrand d j (z - unit i))
  have hsum : (∑ i : Fin d, (∫ (a : Fin d → ℝ), charFn d a ^ j * Real.cos (dotSite a (z + unit i))
        + charFn d a ^ j * Real.cos (dotSite a (z - unit i)) ∂torusMeasure d))
      = ∑ i : Fin d, (fourierHeat d j (z + unit i) + fourierHeat d j (z - unit i)) :=
    Finset.sum_congr rfl fun i _ => hkey i
  rw [hsum]
  rfl

/-- The character as a product: `cos(θ · z)` is the real part of the product
of the coordinate characters `exp(i θ_j z_j)`. -/
theorem cos_dotSite_eq_re_prod {d : ℕ} (θ : Fin d → ℝ) (z : Site d) :
    Real.cos (dotSite θ z)
      = (∏ i, Complex.exp (Complex.ofReal (θ i * (z i : ℝ)) * Complex.I)).re := by
  unfold dotSite
  rw [← Complex.exp_sum]
  have hS : ∑ i, Complex.ofReal (θ i * (z i : ℝ)) * Complex.I
      = Complex.ofReal (∑ i, θ i * (z i : ℝ)) * Complex.I := by
    rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  rw [hS, Complex.exp_mul_I, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.sin_ofReal_re, Complex.cos_ofReal_re]
  rw [Complex.sin_ofReal_im]
  simp

end LatticeProb

end
