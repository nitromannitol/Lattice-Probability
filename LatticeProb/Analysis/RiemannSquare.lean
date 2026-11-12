import LatticeProb.Bonanno.LQGDimension.LFPP.SegCombLaw

/-!
# Riemann sums over a centred square of the plane

For a continuous `f : ℂ → ℝ` and `c > 0`, the averages of `f` over the uniform `N × N` grid of the
square `{w | |re w| ≤ c, |im w| ≤ c}` converge, as `N → ∞`, to the integral of `f` over the square
(with respect to Lebesgue measure), once multiplied by the area `(2c)²` of the square.

The proof reduces to the double Riemann sum over `[0,1]²` by an affine change of variables.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace LatticeProb

/-- The closed square `{w | |re w| ≤ c, |im w| ≤ c}` is the preimage of a product of intervals under
the measure-preserving identification `ℂ ≃ ℝ × ℝ`. -/
theorem centredSquare_eq_preimage (c : ℝ) :
    {w : ℂ | |w.re| ≤ c ∧ |w.im| ≤ c} =
      Complex.measurableEquivRealProd ⁻¹' (Icc (-c) c ×ˢ Icc (-c) c) := by
  ext w
  simp [abs_le]
  tauto

/-- The integral over the centred square of a continuous function, as an iterated interval integral
over `[0,1]²` after an affine change of variables. -/
theorem setIntegral_centredSquare_eq {c : ℝ} (hc : 0 < c) {f : ℂ → ℝ} (hf : Continuous f) :
    ∫ w in {w : ℂ | |w.re| ≤ c ∧ |w.im| ≤ c}, f w =
      (2 * c) ^ 2 * ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        f ⟨2 * c * s + -c, 2 * c * t + -c⟩ := by
  rw [centredSquare_eq_preimage]
  have hmp := Complex.volume_preserving_equiv_real_prod
  have h1 : ∫ w in Complex.measurableEquivRealProd ⁻¹' (Icc (-c) c ×ˢ Icc (-c) c), f w =
      ∫ p in Icc (-c) c ×ˢ Icc (-c) c, f (Complex.measurableEquivRealProd.symm p) := by
    rw [← hmp.setIntegral_preimage_emb Complex.measurableEquivRealProd.measurableEmbedding
      (fun p => f (Complex.measurableEquivRealProd.symm p))]
    simp
  rw [h1]
  have hcm : Continuous fun p : ℝ × ℝ => Complex.measurableEquivRealProd.symm p :=
    Complex.equivRealProdCLM.symm.continuous
  have hcont : Continuous fun p : ℝ × ℝ => f (Complex.measurableEquivRealProd.symm p) :=
    hf.comp hcm
  have hint : IntegrableOn (fun p : ℝ × ℝ => f (Complex.measurableEquivRealProd.symm p))
      (Icc (-c) c ×ˢ Icc (-c) c) volume :=
    hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod, setIntegral_prod _ (by simpa [Measure.volume_eq_prod] using hint)]
  have hle : -c ≤ c := by linarith
  have hc2 : (2 * c) ≠ 0 := by positivity
  have hi : ∀ x : ℝ, ∫ y in Icc (-c) c, f (Complex.measurableEquivRealProd.symm (x, y)) =
      (2 * c) * ∫ t in (0 : ℝ)..1, f ⟨x, 2 * c * t + -c⟩ := by
    intro x
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    have := intervalIntegral.integral_comp_mul_add
      (a := (0 : ℝ)) (b := 1) (fun y : ℝ => f ⟨x, y⟩) hc2 (-c)
    simp only [mul_zero, zero_add, mul_one] at this
    have e : 2 * c + -c = c := by ring
    rw [e] at this
    simp only [Complex.measurableEquivRealProd_symm_apply]
    rw [this, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc2, one_mul]
  simp_rw [hi]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_const_mul]
  have := intervalIntegral.integral_comp_mul_add
    (a := (0 : ℝ)) (b := 1) (fun x : ℝ => ∫ t in (0 : ℝ)..1, f ⟨x, 2 * c * t + -c⟩) hc2 (-c)
  simp only [mul_zero, zero_add, mul_one] at this
  have e : 2 * c + -c = c := by ring
  rw [e] at this
  rw [this, smul_eq_mul]
  field_simp

/-- **Riemann sums over a centred square.**  For `f : ℂ → ℝ` continuous and `c > 0`,
`((2c)² / N²) ∑_{k,l < N} f (grid point (k,l))` converges to `∫_{|re| ≤ c, |im| ≤ c} f`, where the
grid points are `(-c + 2c k/N) + i (-c + 2c l/N)`. -/
theorem tendsto_gridSum_centredSquare {c : ℝ} (hc : 0 < c) {f : ℂ → ℝ} (hf : Continuous f) :
    Tendsto (fun N : ℕ => ((2 * c) ^ 2 / (N : ℝ) ^ 2) * ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
        f ⟨2 * c * ((k : ℝ) / N) + -c, 2 * c * ((l : ℝ) / N) + -c⟩) atTop
      (𝓝 (∫ w in {w : ℂ | |w.re| ≤ c ∧ |w.im| ≤ c}, f w)) := by
  rw [setIntegral_centredSquare_eq hc hf]
  have hg : Continuous (Function.uncurry fun s t : ℝ => f ⟨2 * c * s + -c, 2 * c * t + -c⟩) := by
    have hcm : Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) :=
      Complex.equivRealProdCLM.symm.continuous
    have : Continuous fun p : ℝ × ℝ => (⟨2 * c * p.1 + -c, 2 * c * p.2 + -c⟩ : ℂ) :=
      hcm.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (2 * c * p.1 + -c, 2 * c * p.2 + -c))
    exact hf.comp this
  have h := (LQGDimension.SegLaw.tendsto_riemannSum2 hg).const_mul ((2 * c) ^ 2)
  refine h.congr fun N => ?_
  simp only [LQGDimension.SegLaw.riemannSum2]
  rw [← mul_assoc]
  congr 1
  ring

end LatticeProb
