import LatticeProb.Prob.CorrelatedBMForwardSubcritical

/-! # Forward wedge bounds from a positive axial starting point -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A positive axial starting point lies in the open symmetric wedge. -/
theorem normalizedWedgeStart_mem_open (a b q : ℝ) (ha : 0 < a) (hq : 0 < q) :
    let J : EuclideanSpace ℝ (Fin 2) → ℂ := Complex.orthonormalBasisOneI.repr.symm
    ((J (normalizedWedgeStart a q)).re, (J (normalizedWedgeStart a q)).im) ∈
      openSymmetricWedge a b := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  simp only [Complex.orthonormalBasisOneI_repr_symm_apply, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
    add_zero, openSymmetricWedge, mem_ofPred_eq, normalizedWedgeStart,
    Matrix.cons_val_zero, Matrix.cons_val_one, abs_zero]
  exact mul_pos ha (div_pos hq (mul_pos ha hs))

/-- The Euclidean norm of a positive axial starting point. -/
theorem norm_normalizedWedgeStart (a q : ℝ) (ha : 0 < a) (hq : 0 < q) :
    ‖normalizedWedgeStart a q‖ = q / (a * Real.sqrt 2) := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hx : 0 < q / (a * Real.sqrt 2) := div_pos hq (mul_pos ha hs)
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, normalizedWedgeStart,
    Real.sqrt_sq_eq_abs, abs_of_pos hx]

/-- The forward strict wedge bound for a positive axial offset. -/
theorem forward_wedge_barrier_subcritical_positive {θ p r : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (hr : 0 < r) (hrp : r < p)
    (hpθ : p * θ < Real.pi) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {μ : Measure Path2}, IsCorrelatedBM2 (Real.sqrt 2) μ →
        ∀ (q : ℝ) (T : ℝ≥0), 0 < q → 0 < (T : ℝ) →
        μ.real (openSymmetricWedgeBarrier (Real.sin (θ / 2))
          (Real.cos (θ / 2)) q T) ≤
          K * ((q / (Real.sin (θ / 2) * Real.sqrt 2)) / Real.sqrt (T : ℝ)) ^ r := by
  obtain ⟨K, hK, hbound⟩ := forward_wedge_barrier_subcritical hθ0 hθπ hr hrp hpθ
  refine ⟨K, hK, ?_⟩
  intro μ hμ q T hq hT
  have ha : 0 < Real.sin (θ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have hx := normalizedWedgeStart_mem_open (Real.sin (θ / 2)) (Real.cos (θ / 2)) q ha hq
  have hb := hbound hμ q T hT (subset_closure hx)
  simpa only [norm_normalizedWedgeStart _ _ ha hq] using hb

end LatticeProb.CorrelatedBM
