/-
Two-smoothness of `L^p` for `p ≥ 2`, over a product of two probability measures.

This is the analytic step that part (a) of `lem:weighted-exp-conc` rests on.  The
pointwise second-order bound

  `|a + b|^p ≤ |a|^p + p |a|^{p-2} a b + C (|a|^{p-2} b^2 + |b|^p)`

is `exists_abs_add_rpow_bound`, and the algebra that turns the
resulting three terms into a single `p/2`-th power is
`exists_two_smooth_const`.  What is proved here is the integrated
statement between them: if `X` reads only the second coordinate of a product and
`Y` has mean zero in the first coordinate for every value of the second, then

  `‖X + Y‖_p^2 ≤ ‖X‖_p^2 + C ‖Y‖_p^2`.

The linear term integrates to zero coordinate by coordinate, and the cross term
is Hölder with the conjugate exponents `p/(p-2)` and `p/2`.  Every integrability
hypothesis beyond the two `p`-th moments is discharged by Young's inequality,
which dominates both the linear and the cross integrand by multiples of `|X|^p`
and `|Y|^p`.
-/
import Mathlib
import LatticeProb.Prob.PowerIneq
import LatticeProb.Prob.EfronStein

open MeasureTheory

namespace LatticeProb

/-! ### Two Young inequalities -/

/-- Young's inequality with exponents `p/(p-1)` and `p`, in the form the linear
term of the second-order expansion needs. -/
theorem young_rpow_mul_abs {p : ℝ} (hp : 2 ≤ p) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    a ^ (p - 1) * |b| ≤ (p - 1) / p * a ^ p + 1 / p * |b| ^ p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hconj : Real.HolderConjugate (p / (p - 1)) p := by
    refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hp1]; linarith
    · field_simp
      ring
  have hy := Real.young_inequality (a ^ (p - 1)) |b| hconj
  have h1 : |a ^ (p - 1)| = a ^ (p - 1) := abs_of_nonneg (Real.rpow_nonneg ha _)
  have h2 : (a ^ (p - 1)) ^ (p / (p - 1)) = a ^ p := by
    rw [← Real.rpow_mul ha]
    congr 1
    field_simp
  have h3 : |(|b|)| = |b| := abs_abs b
  rw [h1, h3] at hy
  rw [h2] at hy
  calc a ^ (p - 1) * |b| ≤ a ^ p / (p / (p - 1)) + |b| ^ p / p := hy
    _ = (p - 1) / p * a ^ p + 1 / p * |b| ^ p := by
        field_simp

/-- Young's inequality with exponents `p/(p-2)` and `p/2`, in the form the cross
term of the second-order expansion needs.  At `p = 2` it is an identity. -/
theorem young_rpow_mul_sq {p : ℝ} (hp : 2 ≤ p) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    a ^ (p - 2) * b ^ 2 ≤ (p - 2) / p * a ^ p + 2 / p * |b| ^ p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have habs2 : |b| ^ (2 : ℝ) = b ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rcases eq_or_lt_of_le hp with hp2 | hp2
  · rw [← hp2, show (2 : ℝ) - 2 = 0 by ring, Real.rpow_zero, one_mul]
    rw [habs2]
    norm_num
  · have hp2' : (0 : ℝ) < p - 2 := by linarith
    have hconj : Real.HolderConjugate (p / (p - 2)) (p / 2) := by
      refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
      · rw [lt_div_iff₀ hp2']; linarith
      · field_simp
        ring
    have hy := Real.young_inequality (a ^ (p - 2)) (b ^ 2) hconj
    have h1 : |a ^ (p - 2)| = a ^ (p - 2) := abs_of_nonneg (Real.rpow_nonneg ha _)
    have h3 : |b ^ 2| = b ^ 2 := abs_of_nonneg (sq_nonneg b)
    rw [h1, h3] at hy
    have h2 : (a ^ (p - 2)) ^ (p / (p - 2)) = a ^ p := by
      rw [← Real.rpow_mul ha]
      congr 1
      field_simp
    have h4 : (b ^ 2 : ℝ) ^ (p / 2) = |b| ^ p := by
      rw [← habs2, ← Real.rpow_mul (abs_nonneg b)]
      congr 1
      field_simp
    rw [h2, h4] at hy
    calc a ^ (p - 2) * b ^ 2 ≤ a ^ p / (p / (p - 2)) + |b| ^ p / (p / 2) := hy
      _ = (p - 2) / p * a ^ p + 2 / p * |b| ^ p := by field_simp

/-- `|x|^{p-2} |x| = |x|^{p-1}`, including at `x = 0`, where at `p = 2` the left
side reads `1 * 0`. -/
theorem abs_rpow_sub_two_mul {p : ℝ} (hp : 2 ≤ p) (x : ℝ) :
    |x| ^ (p - 2) * |x| = |x| ^ (p - 1) := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    have hp1 : (0 : ℝ) < p - 1 := by linarith
    simp [Real.zero_rpow (ne_of_gt hp1)]
  · have hpos : (0 : ℝ) < |x| := abs_pos.mpr hx
    have h := Real.rpow_add hpos (p - 2) 1
    rw [Real.rpow_one] at h
    rw [show p - 1 = p - 2 + 1 by ring, h]

/-! ### The two-smoothness inequality -/

/-- **Two-smoothness of `L^p` for `p ≥ 2`.**  On a product of two probability
measures, if `X` reads only the second coordinate and `Y` has mean zero in the
first coordinate for every value of the second, then the square of the `p`-norm
of `X + Y` exceeds that of `X` by at most a multiple of that of `Y`. -/
theorem exists_lp_two_smooth {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
        (κ : Measure α) (ρ : Measure β), IsProbabilityMeasure κ → IsProbabilityMeasure ρ →
        ∀ (X : β → ℝ) (Y : α → β → ℝ),
          Measurable X → Measurable (fun q : α × β => Y q.1 q.2) →
          Integrable (fun b => |X b| ^ p) ρ →
          Integrable (fun q : α × β => |Y q.1 q.2| ^ p) (κ.prod ρ) →
          (∀ b, ∫ a, Y a b ∂κ = 0) →
          (∫ q : α × β, |X q.2 + Y q.1 q.2| ^ p ∂(κ.prod ρ)) ^ (2 / p)
            ≤ (∫ b, |X b| ^ p ∂ρ) ^ (2 / p)
              + C * (∫ q : α × β, |Y q.1 q.2| ^ p ∂(κ.prod ρ)) ^ (2 / p) := by
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨C₀, hC₀1, hpt⟩ := exists_abs_add_rpow_bound hp
  obtain ⟨C, hCpos, halg⟩ := exists_two_smooth_const hp (C₁ := C₀) (by linarith)
  refine ⟨C, hCpos, ?_⟩
  intro α β _ _ κ ρ hκ hρ X Y hXm hYm hXp hYp hY0
  haveI := hκ
  haveI := hρ
  set A : ℝ := ∫ b, |X b| ^ p ∂ρ with hA
  set B : ℝ := ∫ q : α × β, |Y q.1 q.2| ^ p ∂(κ.prod ρ) with hB
  have hA0 : 0 ≤ A := integral_nonneg fun b => Real.rpow_nonneg (abs_nonneg _) _
  have hB0 : 0 ≤ B := integral_nonneg fun q => Real.rpow_nonneg (abs_nonneg _) _
  -- the two `p`-th powers, read on the product
  have hXpp : Integrable (fun q : α × β => |X q.2| ^ p) (κ.prod ρ) := hXp.comp_snd κ
  have hAeq : ∫ q : α × β, |X q.2| ^ p ∂(κ.prod ρ) = A := by
    rw [integral_prod_symm _ hXpp]
    simp only [integral_const, probReal_univ, one_smul]
    exact hA.symm
  -- the linear term
  have hXsnd : Measurable (fun q : α × β => X q.2) := hXm.comp measurable_snd
  have hXabs : Measurable (fun q : α × β => |X q.2| ^ (p - 2)) := by fun_prop
  have hlin_meas : Measurable
      (fun q : α × β => p * |X q.2| ^ (p - 2) * X q.2 * Y q.1 q.2) :=
    (((measurable_const.mul hXabs).mul hXsnd).mul hYm)
  have hlin_int : Integrable
      (fun q : α × β => p * |X q.2| ^ (p - 2) * X q.2 * Y q.1 q.2) (κ.prod ρ) := by
    refine Integrable.mono' ((hXpp.const_mul (p - 1)).add (hYp.const_mul 1))
      hlin_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
    have hy := young_rpow_mul_abs hp (abs_nonneg (X q.2)) (Y q.1 q.2)
    have hnorm : ‖p * |X q.2| ^ (p - 2) * X q.2 * Y q.1 q.2‖
        = p * (|X q.2| ^ (p - 1) * |Y q.1 q.2|) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hp0,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (X q.2)) (p - 2)),
        ← abs_rpow_sub_two_mul hp (X q.2)]
      ring
    have hmul := mul_le_mul_of_nonneg_left hy hp0.le
    have hfield : p * ((p - 1) / p * |X q.2| ^ p + 1 / p * |Y q.1 q.2| ^ p)
        = (p - 1) * |X q.2| ^ p + 1 * |Y q.1 q.2| ^ p := by field_simp
    rw [hfield] at hmul
    simp only [Pi.add_apply, hnorm]
    exact hmul
  -- the cross term
  have hcross_meas : Measurable
      (fun q : α × β => |X q.2| ^ (p - 2) * Y q.1 q.2 ^ 2) :=
    hXabs.mul (hYm.pow_const 2)
  have hcross_int : Integrable
      (fun q : α × β => |X q.2| ^ (p - 2) * Y q.1 q.2 ^ 2) (κ.prod ρ) := by
    refine Integrable.mono' ((hXpp.const_mul ((p - 2) / p)).add (hYp.const_mul (2 / p)))
      hcross_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
    have hy := young_rpow_mul_sq hp (abs_nonneg (X q.2)) (Y q.1 q.2)
    have hnorm : ‖|X q.2| ^ (p - 2) * Y q.1 q.2 ^ 2‖ = |X q.2| ^ (p - 2) * Y q.1 q.2 ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.rpow_nonneg (abs_nonneg (X q.2)) (p - 2)) (sq_nonneg _))]
    simp only [Pi.add_apply, hnorm]
    exact hy
  -- the second-order expansion is integrable
  have hDsum : Integrable
      (fun q : α × β => |X q.2| ^ p + p * |X q.2| ^ (p - 2) * X q.2 * Y q.1 q.2
        + C₀ * (|X q.2| ^ (p - 2) * Y q.1 q.2 ^ 2 + |Y q.1 q.2| ^ p)) (κ.prod ρ) :=
    (hXpp.add hlin_int).add ((hcross_int.add hYp).const_mul C₀)
  have htot_meas : Measurable (fun q : α × β => |X q.2 + Y q.1 q.2| ^ p) := by
    have : Measurable (fun q : α × β => X q.2 + Y q.1 q.2) := hXsnd.add hYm
    fun_prop
  have hptw : ∀ q : α × β, |X q.2 + Y q.1 q.2| ^ p
      ≤ |X q.2| ^ p + p * |X q.2| ^ (p - 2) * X q.2 * Y q.1 q.2
        + C₀ * (|X q.2| ^ (p - 2) * Y q.1 q.2 ^ 2 + |Y q.1 q.2| ^ p) := fun q =>
    hpt (X q.2) (Y q.1 q.2)
  have htot_int : Integrable (fun q : α × β => |X q.2 + Y q.1 q.2| ^ p) (κ.prod ρ) := by
    refine Integrable.mono' hDsum htot_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact hptw q
  -- the linear term integrates to zero
  have hlin_zero : ∫ q : α × β, p * |X q.2| ^ (p - 2) * X q.2 * Y q.1 q.2 ∂(κ.prod ρ) = 0 := by
    rw [integral_prod_symm _ hlin_int]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun b => ?_)
    show (∫ a : α, p * |X b| ^ (p - 2) * X b * Y a b ∂κ) = 0
    rw [integral_const_mul, hY0 b, mul_zero]
  -- the cross term, by Hölder with the conjugate exponents `p/(p-2)` and `p/2`
  have hfeq : ∀ q : α × β, (|X q.2| ^ (p - 2)) ^ (p / (p - 2)) = |X q.2| ^ p ∨ p = 2 := by
    intro q
    rcases eq_or_lt_of_le hp with hp2 | hp2
    · exact Or.inr hp2.symm
    · left
      rw [← Real.rpow_mul (abs_nonneg _)]
      congr 1
      field_simp
  have hcross_bound : ∫ q : α × β, |X q.2| ^ (p - 2) * Y q.1 q.2 ^ 2 ∂(κ.prod ρ)
      ≤ A ^ ((p - 2) / p) * B ^ (2 / p) := by
    rcases eq_or_lt_of_le hp with hp2 | hp2
    · have hz : p - 2 = 0 := by rw [← hp2]; ring
      have h1 : ∀ q : α × β, |X q.2| ^ (p - 2) * Y q.1 q.2 ^ 2 = |Y q.1 q.2| ^ p := by
        intro q
        rw [hz, Real.rpow_zero, one_mul, ← hp2,
          show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
      have h2 : A ^ ((p - 2) / p) = 1 := by rw [hz, zero_div, Real.rpow_zero]
      have h3 : (2 : ℝ) / p = 1 := by rw [← hp2]; norm_num
      have h4 : ∫ q : α × β, |X q.2| ^ (p - 2) * Y q.1 q.2 ^ 2 ∂(κ.prod ρ) = B := by
        rw [hB]
        exact integral_congr_ae (Filter.Eventually.of_forall h1)
      rw [h4, h2, h3, Real.rpow_one, one_mul]
    · have hp2' : (0 : ℝ) < p - 2 := by linarith
      have hrpos : (0 : ℝ) < p / (p - 2) := by positivity
      have hspos : (0 : ℝ) < p / 2 := by positivity
      have hconj : Real.HolderConjugate (p / (p - 2)) (p / 2) := by
        refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
        · rw [lt_div_iff₀ hp2']; linarith
        · field_simp
          ring
      have hfe : ∀ q : α × β, (|X q.2| ^ (p - 2)) ^ (p / (p - 2)) = |X q.2| ^ p := by
        intro q
        rw [← Real.rpow_mul (abs_nonneg _)]
        congr 1
        field_simp
      have hge : ∀ q : α × β, (Y q.1 q.2 ^ 2 : ℝ) ^ (p / 2) = |Y q.1 q.2| ^ p := by
        intro q
        rw [← sq_abs (Y q.1 q.2), show |Y q.1 q.2| ^ 2 = |Y q.1 q.2| ^ ((2 : ℕ) : ℝ) by
            rw [Real.rpow_natCast], ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        push_cast
        field_simp
      have hfL : MemLp (fun q : α × β => |X q.2| ^ (p - 2))
          (ENNReal.ofReal (p / (p - 2))) (κ.prod ρ) := by
        rw [← integrable_norm_rpow_iff hXabs.aestronglyMeasurable
          (by simp [ENNReal.ofReal_eq_zero]; linarith) (by simp),
          ENNReal.toReal_ofReal hrpos.le]
        refine hXpp.congr (Filter.Eventually.of_forall fun q => ?_)
        show |X q.2| ^ p = ‖|X q.2| ^ (p - 2)‖ ^ (p / (p - 2))
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), hfe q]
      have hgL : MemLp (fun q : α × β => Y q.1 q.2 ^ 2)
          (ENNReal.ofReal (p / 2)) (κ.prod ρ) := by
        rw [← integrable_norm_rpow_iff (hYm.pow_const 2).aestronglyMeasurable
          (by simp [ENNReal.ofReal_eq_zero]; linarith) (by simp),
          ENNReal.toReal_ofReal hspos.le]
        refine hYp.congr (Filter.Eventually.of_forall fun q => ?_)
        show |Y q.1 q.2| ^ p = ‖Y q.1 q.2 ^ 2‖ ^ (p / 2)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Y q.1 q.2)), hge q]
      have hf0 : 0 ≤ᵐ[κ.prod ρ] fun q : α × β => |X q.2| ^ (p - 2) :=
        Filter.Eventually.of_forall fun q => Real.rpow_nonneg (abs_nonneg _) _
      have hg0 : 0 ≤ᵐ[κ.prod ρ] fun q : α × β => Y q.1 q.2 ^ 2 :=
        Filter.Eventually.of_forall fun q => sq_nonneg _
      have hhold := integral_mul_le_Lp_mul_Lq_of_nonneg hconj hf0 hg0 hfL hgL
      have hA' : ∫ q : α × β, (|X q.2| ^ (p - 2)) ^ (p / (p - 2)) ∂(κ.prod ρ) = A := by
        rw [← hAeq]
        exact integral_congr_ae (Filter.Eventually.of_forall hfe)
      have hB' : ∫ q : α × β, (Y q.1 q.2 ^ 2 : ℝ) ^ (p / 2) ∂(κ.prod ρ) = B := by
        rw [hB]
        exact integral_congr_ae (Filter.Eventually.of_forall hge)
      rw [hA', hB'] at hhold
      have he1 : 1 / (p / (p - 2)) = (p - 2) / p := by field_simp
      have he2 : 1 / (p / 2) = 2 / p := by field_simp
      rw [he1, he2] at hhold
      exact hhold
  -- the second-order expansion, integrated
  have hmain : ∫ q : α × β, |X q.2 + Y q.1 q.2| ^ p ∂(κ.prod ρ)
      ≤ A + C₀ * (A ^ ((p - 2) / p) * B ^ (2 / p) + B) := by
    have h1 := integral_mono htot_int hDsum (fun q => hptw q)
    have h2 : ∫ q : α × β, (|X q.2| ^ p + p * |X q.2| ^ (p - 2) * X q.2 * Y q.1 q.2
          + C₀ * (|X q.2| ^ (p - 2) * Y q.1 q.2 ^ 2 + |Y q.1 q.2| ^ p)) ∂(κ.prod ρ)
        = A + 0 + C₀ * ((∫ q : α × β, |X q.2| ^ (p - 2) * Y q.1 q.2 ^ 2 ∂(κ.prod ρ)) + B) := by
      have e1 := integral_add (hXpp.add hlin_int) ((hcross_int.add hYp).const_mul C₀)
      have e2 := integral_add hXpp hlin_int
      have e3 := integral_add hcross_int hYp
      simp only [Pi.add_apply] at e1 e2 e3
      rw [e1, e2, integral_const_mul, e3, hAeq, hlin_zero, ← hB]
    rw [h2] at h1
    have hC₀0 : (0 : ℝ) ≤ C₀ := by linarith
    nlinarith [h1, hcross_bound, hC₀0]
  -- the algebraic step, and the `2/p`-th power
  have hApos : 0 ≤ A ^ (2 / p) := Real.rpow_nonneg hA0 _
  have hBpos : 0 ≤ B ^ (2 / p) := Real.rpow_nonneg hB0 _
  have hu : (A ^ (2 / p)) ^ (p / 2) = A := by
    rw [← Real.rpow_mul hA0, show 2 / p * (p / 2) = 1 by field_simp, Real.rpow_one]
  have hu2 : (A ^ (2 / p)) ^ ((p - 2) / 2) = A ^ ((p - 2) / p) := by
    rw [← Real.rpow_mul hA0]
    congr 1
    field_simp
  have hv : (B ^ (2 / p)) ^ (p / 2) = B := by
    rw [← Real.rpow_mul hB0, show 2 / p * (p / 2) = 1 by field_simp, Real.rpow_one]
  have halgA := halg (A ^ (2 / p)) (B ^ (2 / p)) hApos hBpos
  rw [hu, hu2, hv] at halgA
  have hbase : 0 ≤ A ^ (2 / p) + C * B ^ (2 / p) := by positivity
  have hnn : 0 ≤ ∫ q : α × β, |X q.2 + Y q.1 q.2| ^ p ∂(κ.prod ρ) :=
    integral_nonneg fun q => Real.rpow_nonneg (abs_nonneg _) _
  have hfin : ∫ q : α × β, |X q.2 + Y q.1 q.2| ^ p ∂(κ.prod ρ)
      ≤ (A ^ (2 / p) + C * B ^ (2 / p)) ^ (p / 2) := le_trans hmain halgA
  calc (∫ q : α × β, |X q.2 + Y q.1 q.2| ^ p ∂(κ.prod ρ)) ^ (2 / p)
      ≤ ((A ^ (2 / p) + C * B ^ (2 / p)) ^ (p / 2)) ^ (2 / p) :=
        Real.rpow_le_rpow hnn hfin (by positivity)
    _ = A ^ (2 / p) + C * B ^ (2 / p) := by
        rw [← Real.rpow_mul hbase, show p / 2 * (2 / p) = 1 by field_simp, Real.rpow_one]


/-! ### Jensen, and a sum raised to a power -/

/-- Jensen's inequality for `t ↦ t^p` against a probability measure, in the only
form used here.  It is Hölder against the constant function one. -/
theorem rpow_integral_le_integral_rpow {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 < p) (g : α → ℝ)
    (hgm : AEStronglyMeasurable g μ) (hg : 0 ≤ᵐ[μ] g)
    (hgp : Integrable (fun x => g x ^ p) μ) :
    (∫ x, g x ∂μ) ^ p ≤ ∫ x, g x ^ p ∂μ := by
  have hp0 : (0 : ℝ) < p := by linarith
  set q : ℝ := p.conjExponent with hqdef
  have hconj : Real.HolderConjugate p q := Real.HolderConjugate.conjExponent hp
  have hq0 : (0 : ℝ) < q := hconj.symm.pos
  have hgL : MemLp g (ENNReal.ofReal p) μ := by
    rw [← integrable_norm_rpow_iff hgm (by simp [ENNReal.ofReal_eq_zero]; linarith) (by simp),
      ENNReal.toReal_ofReal hp0.le]
    refine hgp.congr (Filter.Eventually.mono hg fun x hx => ?_)
    show g x ^ p = ‖g x‖ ^ p
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
  have h1L : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal q) μ := memLp_const 1
  have h10 : 0 ≤ᵐ[μ] fun _ : α => (1 : ℝ) := Filter.Eventually.of_forall fun _ => zero_le_one
  have hhold := integral_mul_le_Lp_mul_Lq_of_nonneg hconj hg h10 hgL h1L
  simp only [mul_one, Real.one_rpow, integral_const, probReal_univ, smul_eq_mul] at hhold
  have hInt0 : 0 ≤ ∫ x, g x ^ p ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.mono hg fun x hx => Real.rpow_nonneg hx _)
  have hgi0 : 0 ≤ ∫ x, g x ∂μ := integral_nonneg_of_ae hg
  calc (∫ x, g x ∂μ) ^ p ≤ ((∫ x, g x ^ p ∂μ) ^ (1 / p)) ^ p :=
        Real.rpow_le_rpow hgi0 hhold hp0.le
    _ = ∫ x, g x ^ p ∂μ := by
        rw [← Real.rpow_mul hInt0, one_div, inv_mul_cancel₀ (ne_of_gt hp0), Real.rpow_one]

/-- A finite sum of nonnegative terms raised to a power `p ≥ 1` is at most the
number of terms to the `p` times the sum of the powers. -/
theorem rpow_sum_le_card {ι : Type*} (s : Finset ι) (b : ι → ℝ) (hb : ∀ i ∈ s, 0 ≤ b i)
    {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, b i) ^ p ≤ (s.card : ℝ) ^ p * ∑ i ∈ s, b i ^ p := by
  have hp0 : (0 : ℝ) < p := by linarith
  set T : ℝ := ∑ i ∈ s, b i ^ p with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hb i hi) _
  have hpt : ∀ i ∈ s, b i ≤ T ^ (1 / p) := by
    intro i hi
    have h1 : b i ^ p ≤ T :=
      Finset.single_le_sum (f := fun j => b j ^ p)
        (fun j hj => Real.rpow_nonneg (hb j hj) _) hi
    have h2 : (b i ^ p) ^ (1 / p) = b i := by
      rw [← Real.rpow_mul (hb i hi), mul_one_div, div_self (ne_of_gt hp0), Real.rpow_one]
    calc b i = (b i ^ p) ^ (1 / p) := h2.symm
      _ ≤ T ^ (1 / p) := Real.rpow_le_rpow (Real.rpow_nonneg (hb i hi) _) h1 (by positivity)
  have hsum : ∑ i ∈ s, b i ≤ (s.card : ℝ) * T ^ (1 / p) := by
    calc ∑ i ∈ s, b i ≤ ∑ _i ∈ s, T ^ (1 / p) := Finset.sum_le_sum hpt
      _ = (s.card : ℝ) * T ^ (1 / p) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hs0 : 0 ≤ ∑ i ∈ s, b i := Finset.sum_nonneg hb
  calc (∑ i ∈ s, b i) ^ p ≤ ((s.card : ℝ) * T ^ (1 / p)) ^ p :=
        Real.rpow_le_rpow hs0 hsum hp0.le
    _ = (s.card : ℝ) ^ p * T := by
        rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hT0 _),
          ← Real.rpow_mul hT0, one_div, inv_mul_cancel₀ (ne_of_gt hp0), Real.rpow_one]

/-! ### The head-tail split for a family of one-site laws -/

variable {N : ℕ}

/-- The head-tail split of an integrable function on a product of `N + 1`
possibly different laws. -/
theorem integrable_prod_cons_fam (μ : Fin (N + 1) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (H : (Fin (N + 1) → ℝ) → ℝ) (hH : Integrable H (Measure.pi μ)) :
    Integrable (fun q : ℝ × (Fin N → ℝ) => H (Fin.cons q.1 q.2))
      ((μ 0).prod (Measure.pi fun j : Fin N => μ (Fin.succAbove 0 j))) := by
  classical
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0 with hedef
  have hmp : MeasurePreserving e (Measure.pi μ)
      ((μ 0).prod (Measure.pi fun j : Fin N => μ (Fin.succAbove 0 j))) :=
    measurePreserving_piFinSuccAbove μ 0
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  rw [← hmp.integrable_comp_emb hemb]
  refine hH.congr (Filter.Eventually.of_forall fun ξ => ?_)
  show H ξ = H (Fin.cons (ξ 0) fun j => ξ (Fin.succAbove 0 j))
  rw [cons_comp]

/-- The integral against a product of `N + 1` possibly different laws, read on
the product of the head law with the product of the others. -/
theorem integral_prod_cons_fam (μ : Fin (N + 1) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (H : (Fin (N + 1) → ℝ) → ℝ) :
    ∫ ξ, H ξ ∂(Measure.pi μ)
      = ∫ q : ℝ × (Fin N → ℝ), H (Fin.cons q.1 q.2)
          ∂((μ 0).prod (Measure.pi fun j : Fin N => μ (Fin.succAbove 0 j))) := by
  classical
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0 with hedef
  have hmp : MeasurePreserving e (Measure.pi μ)
      ((μ 0).prod (Measure.pi fun j : Fin N => μ (Fin.succAbove 0 j))) :=
    measurePreserving_piFinSuccAbove μ 0
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  rw [← hmp.integral_comp hemb (fun q => H (Fin.cons q.1 q.2))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show H ξ = H (Fin.cons (ξ 0) fun j => ξ (Fin.succAbove 0 j))
  rw [cons_comp]

/-- A single coordinate has the `p`-th moment of its own law. -/
theorem integrable_eval_rpow_fam (μ : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {p : ℝ} (i : Fin N) (h : Integrable (fun z => |z| ^ p) (μ i)) :
    Integrable (fun ξ : Fin N → ℝ => |ξ i| ^ p) (Measure.pi μ) := by
  classical
  have hprod : Integrable (fun ξ : Fin N → ℝ => ∏ j, (if j = i then |ξ j| ^ p else 1))
      (Measure.pi μ) := by
    refine Integrable.fintype_prod (f := fun j z => if j = i then |z| ^ p else 1) fun j => ?_
    by_cases hj : j = i
    · subst hj; simpa using h
    · simp only [if_neg hj]
      exact integrable_const (1 : ℝ)
  refine hprod.congr (Filter.Eventually.of_forall fun ξ => ?_)
  show (∏ j, if j = i then |ξ j| ^ p else 1) = |ξ i| ^ p
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj])
    (fun hi => absurd (Finset.mem_univ i) hi)]
  simp

/-- A coordinate-Lipschitz function has a `p`-th moment as soon as every
coordinate law does. -/
theorem integrable_rpow_of_lip_fam (μ : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {p : ℝ} (hp : 1 ≤ p) (hmom : ∀ i, Integrable (fun z => |z| ^ p) (μ i))
    (F : (Fin N → ℝ) → ℝ) (hFm : Measurable F) (ℓ : Fin N → ℝ) (hℓ : ∀ i, 0 ≤ ℓ i)
    (hLip : ∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
      |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) :
    Integrable (fun ξ => |F ξ| ^ p) (Measure.pi μ) := by
  classical
  have hp0 : (0 : ℝ) < p := by linarith
  -- the dominating function
  have hdom : Integrable
      (fun ξ : Fin N → ℝ => ((N : ℝ) + 1) ^ p *
        (|F 0| ^ p + ∑ i, ℓ i ^ p * |ξ i| ^ p)) (Measure.pi μ) := by
    refine Integrable.const_mul ?_ _
    refine (integrable_const (|F 0| ^ p)).add ?_
    refine integrable_finsetSum Finset.univ fun i _ => ?_
    exact (integrable_eval_rpow_fam μ i (hmom i)).const_mul (ℓ i ^ p)
  have hmeas : Measurable (fun ξ : Fin N → ℝ => |F ξ| ^ p) := by fun_prop
  refine Integrable.mono' hdom hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hlin : |F ξ| ≤ |F 0| + ∑ i, ℓ i * |ξ i| := by
    have h1 : |F ξ - F 0| ≤ ∑ i, ℓ i * |ξ i| := by
      refine le_trans (abs_sub_le_sum_lip F ℓ hLip ξ 0) (le_of_eq ?_)
      exact Finset.sum_congr rfl fun i _ => by simp
    have h2 : |F ξ| ≤ |F ξ - F 0| + |F 0| := by
      simpa using abs_add_le (F ξ - F 0) (F 0)
    linarith
  have hcnn : ∀ i : Fin (N + 1), i ∈ (Finset.univ : Finset (Fin (N + 1))) →
      0 ≤ (Fin.cons |F 0| (fun j : Fin N => ℓ j * |ξ j|) : Fin (N + 1) → ℝ) i := by
    intro i _
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j
      simpa using mul_nonneg (hℓ j) (abs_nonneg (ξ j))
  have hkey := rpow_sum_le_card (Finset.univ : Finset (Fin (N + 1)))
    (Fin.cons |F 0| (fun j : Fin N => ℓ j * |ξ j|)) hcnn hp
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.card_univ,
    Fintype.card_fin] at hkey
  have hmulr : ∀ j : Fin N, (ℓ j * |ξ j|) ^ p = ℓ j ^ p * |ξ j| ^ p := fun j =>
    Real.mul_rpow (hℓ j) (abs_nonneg _)
  simp only [hmulr] at hkey
  have hcast : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hkey
  calc |F ξ| ^ p ≤ (|F 0| + ∑ i, ℓ i * |ξ i|) ^ p :=
        Real.rpow_le_rpow (abs_nonneg _) hlin (by linarith)
    _ ≤ ((N : ℝ) + 1) ^ p * (|F 0| ^ p + ∑ i, ℓ i ^ p * |ξ i| ^ p) := hkey

/-! ### Elementary consequences of a `p`-th moment -/

/-- Two nonnegative numbers, their sum raised to `p ≥ 1`. -/
theorem rpow_add_le_two {p : ℝ} (hp : 1 ≤ p) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ p ≤ 2 ^ p * (a ^ p + b ^ p) := by
  classical
  have h := rpow_sum_le_card (Finset.univ : Finset (Fin 2)) ![a, b]
    (fun i _ => by fin_cases i <;> simpa) hp
  simpa [Fin.sum_univ_two] using h

/-- A `p`-th moment with `1 ≤ p` on a probability space gives a first moment. -/
theorem integrable_abs_of_rpow {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 ≤ p) (f : α → ℝ)
    (hfm : AEStronglyMeasurable f μ) (hfp : Integrable (fun x => |f x| ^ p) μ) :
    Integrable f μ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hfp) hfm
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  rcases le_or_gt |f x| 1 with h | h
  · have : (0 : ℝ) ≤ |f x| ^ p := Real.rpow_nonneg (abs_nonneg _) _
    simp only [Pi.add_apply]
    linarith
  · have : |f x| ≤ |f x| ^ p := by
      calc |f x| = |f x| ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ |f x| ^ p := Real.rpow_le_rpow_of_exponent_le h.le hp
    simp only [Pi.add_apply]
    linarith

/-- The `p`-th moment survives subtraction. -/
theorem integrable_rpow_sub {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {p : ℝ} (hp : 1 ≤ p) (f g : α → ℝ)
    (hm : AEStronglyMeasurable (fun x => |f x - g x| ^ p) μ)
    (hf : Integrable (fun x => |f x| ^ p) μ) (hg : Integrable (fun x => |g x| ^ p) μ) :
    Integrable (fun x => |f x - g x| ^ p) μ := by
  refine Integrable.mono' ((hf.add hg).const_mul (2 ^ p)) hm
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  calc |f x - g x| ^ p ≤ (|f x| + |g x|) ^ p :=
        Real.rpow_le_rpow (abs_nonneg _) (abs_sub _ _) (by linarith)
    _ ≤ 2 ^ p * (|f x| ^ p + |g x| ^ p) :=
        rpow_add_le_two hp (abs_nonneg _) (abs_nonneg _)

/-! ### The square-function bound on a product of one-site laws -/

/-- `E|ξ - ξ'|^p` for an independent pair with common law `μ`. -/
noncomputable def pairMoment (μ : Measure ℝ) (p : ℝ) : ℝ := ∫ y, ∫ z, |y - z| ^ p ∂μ ∂μ

theorem pairMoment_nonneg (μ : Measure ℝ) (p : ℝ) : 0 ≤ pairMoment μ p :=
  integral_nonneg fun _ => integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _

theorem measurable_abs_rpow {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f)
    (r : ℝ) : Measurable fun x => |f x| ^ r := by fun_prop

theorem integrable_pair_rpow (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 ≤ p)
    (hmom : Integrable (fun z => |z| ^ p) μ) :
    Integrable (fun q : ℝ × ℝ => |q.1 - q.2| ^ p) (μ.prod μ) :=
  integrable_rpow_sub _ hp (fun q : ℝ × ℝ => q.1) (fun q : ℝ × ℝ => q.2)
    (measurable_abs_rpow (measurable_fst.sub measurable_snd) p).aestronglyMeasurable
    (hmom.comp_fst μ) (hmom.comp_snd μ)

/-- **The square-function bound.**  For a coordinate-Lipschitz function of
independent coordinates with `p`-th moments, the `p`-norm of the fluctuation is
controlled by the weighted `ℓ²` norm of the Lipschitz constants against the pair
moments.  The constant depends only on `p`. -/
theorem exists_lp_square_pi {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (μ : Fin N → Measure ℝ), (∀ i, IsProbabilityMeasure (μ i)) →
        ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
        ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) →
          (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
            |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
          (∀ i, Integrable (fun z => |z| ^ p) (μ i)) →
          (∫ ξ, |F ξ - ∫ η, F η ∂(Measure.pi μ)| ^ p ∂(Measure.pi μ)) ^ (2 / p)
            ≤ C * ∑ i, ℓ i ^ 2 * pairMoment (μ i) p ^ (2 / p) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hp1' : (1 : ℝ) < p := by linarith
  obtain ⟨C, hCpos, hsmooth⟩ := exists_lp_two_smooth hp
  refine ⟨C, hCpos, ?_⟩
  intro N
  induction N with
  | zero =>
      intro μ hμ F hFm ℓ hℓ hLip hmom
      haveI := hμ
      have hsub : ∀ ξ : Fin 0 → ℝ, F ξ = F 0 := fun ξ => congrArg F (Subsingleton.elim _ _)
      have hm : ∫ η, F η ∂(Measure.pi μ) = F 0 := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hsub)]
        simp
      have hz : ∫ ξ, |F ξ - ∫ η, F η ∂(Measure.pi μ)| ^ p ∂(Measure.pi μ) = 0 := by
        rw [hm]
        have hzero : ∀ ξ : Fin 0 → ℝ, |F ξ - F 0| ^ p = (0 : ℝ) := fun ξ => by
          rw [hsub ξ, sub_self, abs_zero, Real.zero_rpow (ne_of_gt hp0)]
        rw [integral_congr_ae (Filter.Eventually.of_forall hzero)]
        simp
      rw [hz, Real.zero_rpow (by positivity : (2 : ℝ) / p ≠ 0)]
      simp
  | succ M ih =>
      intro μ hμ F hFm ℓ hℓ hLip hmom
      classical
      haveI := hμ
      set κ : Measure ℝ := μ 0 with hκdef
      set tμ : Fin M → Measure ℝ := fun j => μ (Fin.succAbove 0 j) with htμdef
      haveI htp : ∀ j, IsProbabilityMeasure (tμ j) := fun j => hμ _
      set ρ : Measure (Fin M → ℝ) := Measure.pi tμ with hρdef
      haveI : IsProbabilityMeasure ρ := by rw [hρdef]; infer_instance
      haveI hκp : IsProbabilityMeasure κ := hμ 0
      -- the Lipschitz property, split into the head and the tail
      have hLip0 : ∀ (x y : ℝ) (η : Fin M → ℝ),
          |F (Fin.cons x η) - F (Fin.cons y η)| ≤ ℓ 0 * |x - y| := by
        intro x y η
        have h := hLip (Fin.cons x η) 0 y
        rwa [cons_update_zero, Fin.cons_zero] at h
      have hLipS : ∀ (x : ℝ) (η : Fin M → ℝ) (j : Fin M) (z : ℝ),
          |F (Fin.cons x η) - F (Fin.cons x (Function.update η j z))| ≤ ℓ j.succ * |η j - z| := by
        intro x η j z
        have h := hLip (Fin.cons x η) j.succ z
        rw [Fin.cons_succ] at h
        rwa [cons_update_succ]
      -- first moments
      have hmomAbs : ∀ i, Integrable (fun z => |z|) (μ i) := fun i =>
        integrable_abs_of_rpow (μ i) hp1 (fun z => |z|) (by fun_prop) (by simpa using hmom i)
      have hconsHead : ∀ η : Fin M → ℝ,
          Measurable fun x : ℝ => (Fin.cons x η : Fin (M + 1) → ℝ) := fun η =>
        measurable_cons_pair.comp (measurable_id.prodMk measurable_const)
      have hslice : ∀ η : Fin M → ℝ, Integrable (fun x => F (Fin.cons x η)) κ := by
        intro η
        refine Integrable.mono' ((integrable_const |F (Fin.cons 0 η)|).add
          ((hmomAbs 0).const_mul (ℓ 0))) (hFm.comp (hconsHead η)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs]
        have h1 := hLip0 x 0 η
        rw [sub_zero] at h1
        have h2 : |F (Fin.cons x η)|
            ≤ |F (Fin.cons x η) - F (Fin.cons 0 η)| + |F (Fin.cons 0 η)| := by
          simpa using abs_add_le (F (Fin.cons x η) - F (Fin.cons 0 η)) (F (Fin.cons 0 η))
        simp only [Pi.add_apply]
        linarith
      have hslicepair : ∀ x : ℝ, Integrable (fun z => |x - z| ^ p) κ := fun x =>
        integrable_rpow_sub κ hp1 (fun _ => x) (fun z => z)
          (measurable_abs_rpow (measurable_const.sub measurable_id) p).aestronglyMeasurable
          (integrable_const _) (by simpa using hmom 0)
      -- the head average
      set Φ : (Fin M → ℝ) → ℝ := fun η => ∫ x, F (Fin.cons x η) ∂κ with hΦdef
      have hΦm : Measurable Φ := by
        have hg : StronglyMeasurable (fun q : (Fin M → ℝ) × ℝ => F (Fin.cons q.2 q.1)) :=
          (hFm.comp (measurable_cons_pair.comp (measurable_snd.prodMk measurable_fst))).stronglyMeasurable
        exact (hg.integral_prod_right').measurable
      have hΦLip : ∀ (η : Fin M → ℝ) (j : Fin M) (z : ℝ),
          |Φ η - Φ (Function.update η j z)| ≤ ℓ (Fin.succAbove 0 j) * |η j - z| := by
        intro η j z
        have hi1 := hslice η
        have hi2 := hslice (Function.update η j z)
        show |(∫ x, F (Fin.cons x η) ∂κ) - ∫ x, F (Fin.cons x (Function.update η j z)) ∂κ| ≤ _
        rw [← integral_sub hi1 hi2]
        calc |∫ x, (F (Fin.cons x η) - F (Fin.cons x (Function.update η j z))) ∂κ|
            ≤ ∫ x, |F (Fin.cons x η) - F (Fin.cons x (Function.update η j z))| ∂κ :=
              abs_integral_le_integral_abs
          _ ≤ ∫ _x : ℝ, ℓ (Fin.succAbove 0 j) * |η j - z| ∂κ := by
              refine integral_mono (hi1.sub hi2).abs (integrable_const _) fun x => ?_
              rw [Fin.zero_succAbove]
              exact hLipS x η j z
          _ = ℓ (Fin.succAbove 0 j) * |η j - z| := by simp
      -- the moments
      have hFmom : Integrable (fun ξ => |F ξ| ^ p) (Measure.pi μ) :=
        integrable_rpow_of_lip_fam μ hp1 hmom F hFm ℓ hℓ hLip
      have hFint : Integrable F (Measure.pi μ) :=
        integrable_abs_of_rpow _ hp1 F hFm.aestronglyMeasurable hFmom
      have hΦmom : Integrable (fun η => |Φ η| ^ p) ρ :=
        integrable_rpow_of_lip_fam tμ hp1 (fun j => hmom _) Φ hΦm
          (fun j => ℓ (Fin.succAbove 0 j)) (fun j => hℓ _) hΦLip
      set m : ℝ := ∫ ξ, F ξ ∂(Measure.pi μ) with hmdef
      have hmeq : m = ∫ η, Φ η ∂ρ := by
        rw [hmdef, integral_prod_cons_fam μ F,
          integral_prod_symm _ (integrable_prod_cons_fam μ F hFint)]
      have hXmom : Integrable (fun η => |Φ η - m| ^ p) ρ :=
        integrable_rpow_sub ρ hp1 Φ (fun _ => m)
          (measurable_abs_rpow (hΦm.sub measurable_const) p).aestronglyMeasurable
          hΦmom (integrable_const _)
      have hGm : Measurable (fun q : ℝ × (Fin M → ℝ) => F (Fin.cons q.1 q.2)) :=
        hFm.comp measurable_cons_pair
      have hYm : Measurable (fun q : ℝ × (Fin M → ℝ) => F (Fin.cons q.1 q.2) - Φ q.2) :=
        hGm.sub (hΦm.comp measurable_snd)
      have hYmom : Integrable
          (fun q : ℝ × (Fin M → ℝ) => |F (Fin.cons q.1 q.2) - Φ q.2| ^ p) (κ.prod ρ) :=
        integrable_rpow_sub _ hp1 _ _ (measurable_abs_rpow hYm p).aestronglyMeasurable
          (integrable_prod_cons_fam μ (fun ξ => |F ξ| ^ p) hFmom) (hΦmom.comp_snd κ)
      have hY0 : ∀ η : Fin M → ℝ, ∫ x, (F (Fin.cons x η) - Φ η) ∂κ = 0 := by
        intro η
        rw [integral_sub (hslice η) (integrable_const _)]
        simp [hΦdef]
      -- the head term
      have hYptw : ∀ q : ℝ × (Fin M → ℝ),
          |F (Fin.cons q.1 q.2) - Φ q.2| ^ p ≤ ℓ 0 ^ p * ∫ z, |q.1 - z| ^ p ∂κ := by
        intro q
        set g : ℝ → ℝ := fun z => |F (Fin.cons q.1 q.2) - F (Fin.cons z q.2)| with hgdef
        have hgm : Measurable g := by
          have : Measurable fun z : ℝ => F (Fin.cons z q.2) := hFm.comp (hconsHead q.2)
          exact (measurable_const.sub this).abs
        have hg3 : ∀ z, g z ^ p ≤ ℓ 0 ^ p * |q.1 - z| ^ p := by
          intro z
          have h := hLip0 q.1 z q.2
          calc g z ^ p ≤ (ℓ 0 * |q.1 - z|) ^ p :=
                Real.rpow_le_rpow (abs_nonneg _) h hp0.le
            _ = ℓ 0 ^ p * |q.1 - z| ^ p := Real.mul_rpow (hℓ 0) (abs_nonneg _)
        have hgpint : Integrable (fun z => g z ^ p) κ := by
          refine Integrable.mono' ((hslicepair q.1).const_mul (ℓ 0 ^ p))
            (measurable_abs_rpow (by
              have : Measurable fun z : ℝ => F (Fin.cons z q.2) := hFm.comp (hconsHead q.2)
              exact measurable_const.sub this) p).aestronglyMeasurable
            (Filter.Eventually.of_forall fun z => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
          exact hg3 z
        have hrep : F (Fin.cons q.1 q.2) - Φ q.2
            = ∫ z, (F (Fin.cons q.1 q.2) - F (Fin.cons z q.2)) ∂κ := by
          rw [integral_sub (integrable_const _) (hslice q.2)]
          simp [hΦdef]
        have h1 : |F (Fin.cons q.1 q.2) - Φ q.2| ≤ ∫ z, g z ∂κ := by
          rw [hrep]
          exact abs_integral_le_integral_abs
        have h2 : (∫ z, g z ∂κ) ^ p ≤ ∫ z, g z ^ p ∂κ :=
          rpow_integral_le_integral_rpow κ hp1' g hgm.aestronglyMeasurable
            (Filter.Eventually.of_forall fun z => abs_nonneg _) hgpint
        have h4 : ∫ z, g z ^ p ∂κ ≤ ℓ 0 ^ p * ∫ z, |q.1 - z| ^ p ∂κ := by
          rw [← integral_const_mul]
          exact integral_mono hgpint ((hslicepair q.1).const_mul _) hg3
        calc |F (Fin.cons q.1 q.2) - Φ q.2| ^ p ≤ (∫ z, g z ∂κ) ^ p :=
              Real.rpow_le_rpow (abs_nonneg _) h1 hp0.le
          _ ≤ ∫ z, g z ^ p ∂κ := h2
          _ ≤ ℓ 0 ^ p * ∫ z, |q.1 - z| ^ p ∂κ := h4
      have hpairInt : Integrable (fun q : ℝ × ℝ => |q.1 - q.2| ^ p) (κ.prod κ) :=
        integrable_pair_rpow κ hp1 (hmom 0)
      have hinner : Integrable (fun x => ∫ z, |x - z| ^ p ∂κ) κ := hpairInt.integral_prod_left
      have hYbound : ∫ q : ℝ × (Fin M → ℝ), |F (Fin.cons q.1 q.2) - Φ q.2| ^ p ∂(κ.prod ρ)
          ≤ ℓ 0 ^ p * pairMoment κ p := by
        have hdomint : Integrable
            (fun q : ℝ × (Fin M → ℝ) => ℓ 0 ^ p * ∫ z, |q.1 - z| ^ p ∂κ) (κ.prod ρ) :=
          (hinner.comp_fst ρ).const_mul _
        have hstep : ∫ q : ℝ × (Fin M → ℝ), ℓ 0 ^ p * (∫ z, |q.1 - z| ^ p ∂κ) ∂(κ.prod ρ)
            = ℓ 0 ^ p * pairMoment κ p := by
          rw [integral_const_mul, integral_prod _ (hinner.comp_fst ρ)]
          simp [pairMoment]
        calc ∫ q : ℝ × (Fin M → ℝ), |F (Fin.cons q.1 q.2) - Φ q.2| ^ p ∂(κ.prod ρ)
            ≤ ∫ q : ℝ × (Fin M → ℝ), ℓ 0 ^ p * (∫ z, |q.1 - z| ^ p ∂κ) ∂(κ.prod ρ) :=
              integral_mono hYmom hdomint hYptw
          _ = ℓ 0 ^ p * pairMoment κ p := hstep
      have hYnn : 0 ≤ ∫ q : ℝ × (Fin M → ℝ), |F (Fin.cons q.1 q.2) - Φ q.2| ^ p ∂(κ.prod ρ) :=
        integral_nonneg fun q => Real.rpow_nonneg (abs_nonneg _) _
      have hYfinal : (∫ q : ℝ × (Fin M → ℝ), |F (Fin.cons q.1 q.2) - Φ q.2| ^ p ∂(κ.prod ρ))
            ^ (2 / p) ≤ ℓ 0 ^ 2 * pairMoment κ p ^ (2 / p) := by
        have hcalc : (ℓ 0 ^ p * pairMoment κ p) ^ (2 / p)
            = ℓ 0 ^ 2 * pairMoment κ p ^ (2 / p) := by
          rw [Real.mul_rpow (Real.rpow_nonneg (hℓ 0) _) (pairMoment_nonneg _ _),
            ← Real.rpow_mul (hℓ 0), show p * (2 / p) = ((2 : ℕ) : ℝ) by push_cast; field_simp,
            Real.rpow_natCast]
        calc (∫ q : ℝ × (Fin M → ℝ), |F (Fin.cons q.1 q.2) - Φ q.2| ^ p ∂(κ.prod ρ)) ^ (2 / p)
            ≤ (ℓ 0 ^ p * pairMoment κ p) ^ (2 / p) :=
              Real.rpow_le_rpow hYnn hYbound (by positivity)
          _ = ℓ 0 ^ 2 * pairMoment κ p ^ (2 / p) := hcalc
      -- the tail term, by the inductive hypothesis
      have hIH := ih tμ htp Φ hΦm (fun j => ℓ (Fin.succAbove 0 j)) (fun j => hℓ _) hΦLip
        (fun j => hmom _)
      rw [← hρdef, ← hmeq] at hIH
      -- the two-smoothness step
      have hkey := hsmooth κ ρ hκp inferInstance (fun η => Φ η - m)
        (fun x η => F (Fin.cons x η) - Φ η) (hΦm.sub measurable_const) hYm hXmom hYmom hY0
      have hLHS : ∫ q : ℝ × (Fin M → ℝ),
            |(Φ q.2 - m) + (F (Fin.cons q.1 q.2) - Φ q.2)| ^ p ∂(κ.prod ρ)
          = ∫ ξ, |F ξ - m| ^ p ∂(Measure.pi μ) := by
        rw [integral_prod_cons_fam μ (fun ξ => |F ξ - m| ^ p)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
        show |(Φ q.2 - m) + (F (Fin.cons q.1 q.2) - Φ q.2)| ^ p = |F (Fin.cons q.1 q.2) - m| ^ p
        rw [show (Φ q.2 - m) + (F (Fin.cons q.1 q.2) - Φ q.2) = F (Fin.cons q.1 q.2) - m from by
          ring]
      rw [hLHS] at hkey
      -- put the two together
      have hsplit := Fin.sum_univ_succAbove
        (fun i : Fin (M + 1) => ℓ i ^ 2 * pairMoment (μ i) p ^ (2 / p)) 0
      rw [hsplit]
      have hCnn : (0 : ℝ) ≤ C := hCpos.le
      calc (∫ ξ, |F ξ - m| ^ p ∂(Measure.pi μ)) ^ (2 / p)
          ≤ (∫ η, |Φ η - m| ^ p ∂ρ) ^ (2 / p)
            + C * (∫ q : ℝ × (Fin M → ℝ), |F (Fin.cons q.1 q.2) - Φ q.2| ^ p ∂(κ.prod ρ))
              ^ (2 / p) := hkey
        _ ≤ C * (∑ j, ℓ (Fin.succAbove 0 j) ^ 2 * pairMoment (tμ j) p ^ (2 / p))
            + C * (ℓ 0 ^ 2 * pairMoment κ p ^ (2 / p)) := by
              exact add_le_add hIH (mul_le_mul_of_nonneg_left hYfinal hCnn)
        _ = C * (ℓ 0 ^ 2 * pairMoment (μ 0) p ^ (2 / p)
            + ∑ j, ℓ (Fin.succAbove 0 j) ^ 2 * pairMoment (μ (Fin.succAbove 0 j)) p ^ (2 / p)) := by
              rw [htμdef, hκdef]
              ring

end LatticeProb
