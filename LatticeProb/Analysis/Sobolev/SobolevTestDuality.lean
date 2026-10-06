/-
# The `H^s`–`H^{−s}` duality bound for smooth compactly supported test functions

`DualityAssembly` proves the duality bound under the four analytic inputs `Integrable f`,
`Integrable g`, `MemLp f 2 volume`, `MemLp g 2 volume`.  A finite pointwise-Fourier Sobolev norm
does not supply them, so this module produces them from genuine smooth compact support
(`IsTestFn`), for two test functions on *independent* domains, and for the translated,
reflected and differentiated mollifier kernels that occur in `∂^α (f ⋆ ρ)(x)`.

The convolution is `convReal f ρ x = ∫ t, f t * ρ (x - t)`, so the kernel seen by the pairing is
the reflected translate `t ↦ ρ (x - t)`, and for a directional derivative
`t ↦ fderiv ℝ ρ (x - t) v`.  The consumers at the end are instantiated at nonzero bump functions
`ContDiffBump`, centred at an arbitrary point.  The convolution-value pairing is positive;
the derivative consumer has a nonzero kernel and applies its pairing bound.
-/
import LatticeProb.Analysis.Sobolev.DualityAssembly

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

section Producers

variable {d : ℕ} {D : Set (Space d)} {φ : Space d → ℝ}

/-- A test function is integrable. -/
theorem IsTestFn.integrable (h : IsTestFn D φ) : Integrable φ :=
  h.1.continuous.integrable_of_hasCompactSupport h.2.1

/-- A test function lies in `L²`. -/
theorem IsTestFn.memLp_two (h : IsTestFn D φ) : MemLp φ 2 volume :=
  h.1.continuous.memLp_of_hasCompactSupport h.2.1

/-- The reflected translate `t ↦ φ (x - t)` of a test function is a test function, on the
reflected translate of its domain. -/
theorem IsTestFn.comp_sub_left (h : IsTestFn D φ) (x : Space d) :
    IsTestFn ((fun t => x - t) ⁻¹' D) (fun t => φ (x - t)) := by
  refine ⟨h.1.comp (contDiff_const.sub contDiff_id), ?_, ?_⟩
  · exact h.2.1.comp_homeomorph (Homeomorph.subLeft x)
  · have e : tsupport (fun t => φ (x - t)) = (fun t => x - t) ⁻¹' tsupport φ := by
      unfold tsupport
      have e0 : Function.support (fun t => φ (x - t))
          = (Homeomorph.subLeft x) ⁻¹' Function.support φ := rfl
      rw [e0, ← (Homeomorph.subLeft x).preimage_closure]
      rfl
    rw [e]
    exact Set.preimage_mono h.2.2

/-- A directional derivative of a test function is a test function on the same domain. -/
theorem IsTestFn.fderiv_apply (h : IsTestFn D φ) (v : Space d) :
    IsTestFn D (fun t => fderiv ℝ φ t v) := by
  refine ⟨?_, h.2.1.fderiv_apply ℝ v, (tsupport_fderiv_apply_subset ℝ v).trans h.2.2⟩
  exact (h.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

end Producers

section Wrapper

variable {d : ℕ} {D₁ D₂ : Set (Space d)} {f g : Space d → ℝ}

/-- **The `H^s`–`H^{−s}` duality bound for test functions.**  The two test functions live on
independent domains `D₁`, `D₂`; no finiteness of the Sobolev norms is needed, since the bound is
in `ℝ≥0∞`. -/
theorem sobolevDualityBound_of_isTestFn (s : ℝ) (hf : IsTestFn D₁ f) (hg : IsTestFn D₂ g) :
    ENNReal.ofReal (|∫ x, f x * g x| ^ 2) ≤ sobolevNormSq d s f * sobolevNormSq d (-s) g :=
  sobolevDualityBound_of_memLp s hf.memLp_two hg.memLp_two hf.integrable hg.integrable

/-- The real form of the test-function duality bound, with finite Sobolev norms. -/
theorem sq_abs_integral_mul_le_integral_weight_of_isTestFn (s : ℝ) (hf : IsTestFn D₁ f)
    (hg : IsTestFn D₂ g) (hfin : sobolevNormSq d s f < ⊤) (hgfin : sobolevNormSq d (-s) g < ⊤) :
    |∫ x, f x * g x| ^ 2
      ≤ (∫ ξ, sobolevWeight s ξ * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2)
        * ∫ ξ, sobolevWeight (-s) ξ * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2 :=
  sq_abs_integral_mul_le_integral_weight s hf.memLp_two hg.memLp_two hf.integrable
    hg.integrable hfin hgfin

/-- **Mollified value bound.**  `|(f ⋆ ρ)(x)|² ≤ ‖f‖²_{H^s} ‖ρ(x - ·)‖²_{H^{−s}}` for test
functions `f` and `ρ` on independent domains. -/
theorem sobolevDualityBound_convReal (s : ℝ) (hf : IsTestFn D₁ f) {ρ : Space d → ℝ}
    (hρ : IsTestFn D₂ ρ) (x : Space d) :
    ENNReal.ofReal (|convReal f ρ x| ^ 2)
      ≤ sobolevNormSq d s f * sobolevNormSq d (-s) (fun t => ρ (x - t)) := by
  have h := sobolevDualityBound_of_isTestFn s hf (hρ.comp_sub_left x)
  simpa [convReal, convolution_def] using h

/-- **Derivative-kernel pairing bound.**  The squared absolute value of
`∫ t, f t * fderiv ℝ ρ (x - t) v` is bounded by
`‖f‖²_{H^s} ‖fderiv ρ (x - ·) v‖²_{H^{−s}}`. -/
theorem sobolevDualityBound_fderiv (s : ℝ) (hf : IsTestFn D₁ f) {ρ : Space d → ℝ}
    (hρ : IsTestFn D₂ ρ) (x v : Space d) :
    ENNReal.ofReal (|∫ t, f t * fderiv ℝ ρ (x - t) v| ^ 2)
      ≤ sobolevNormSq d s f * sobolevNormSq d (-s) (fun t => fderiv ℝ ρ (x - t) v) :=
  sobolevDualityBound_of_isTestFn s hf ((hρ.fderiv_apply v).comp_sub_left x)

end Wrapper

section Consumers

variable {d : ℕ}

/-- A bump function is a test function on its outer closed ball. -/
theorem isTestFn_contDiffBump {c : Space d} (φ : ContDiffBump c) :
    IsTestFn (Metric.closedBall c φ.rOut) φ :=
  ⟨φ.contDiff, φ.hasCompactSupport, φ.tsupport_eq.subset⟩

/-- **Nonzero consumer, mollified value.**  For the standard bump `φ₀` at the origin and the
standard bump `φ_c` at an arbitrary centre `c` (an asymmetric kernel when `c ≠ 0`), the pairing
at `x = c` is positive, hence both `H^s` and `H^{−s}` norms are nonzero (not the junk zero). -/
theorem sobolevNormSq_mul_pos_bump (s : ℝ) (c : Space d) :
    0 < sobolevNormSq d s (default : ContDiffBump (0 : Space d))
      * sobolevNormSq d (-s) (fun t => (default : ContDiffBump c) (c - t)) := by
  set φ₀ : ContDiffBump (0 : Space d) := default with hφ₀
  set φc : ContDiffBump c := default with hφc
  have hf := isTestFn_contDiffBump φ₀
  have hρ := isTestFn_contDiffBump φc
  have hb := sobolevDualityBound_convReal s hf hρ c
  have hpos : 0 < convReal φ₀ φc c := by
    have hc : convReal φ₀ φc c = ∫ t, φ₀ t * φc (c - t) := by
      simp [convReal, convolution_def]
    rw [hc]
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) ?_ ?_ ?_ ?_
    · exact hf.1.continuous.mul ((hρ.comp_sub_left c).1.continuous)
    · exact hf.2.1.mul_right
    · intro t
      exact mul_nonneg φ₀.nonneg (φc.nonneg)
    · have h1 : φ₀ 0 = 1 :=
        φ₀.one_of_mem_closedBall (by simpa [Metric.mem_closedBall] using φ₀.rIn_pos.le)
      have h2 : φc (c - 0) = 1 :=
        φc.one_of_mem_closedBall (by simpa [Metric.mem_closedBall] using φc.rIn_pos.le)
      show φ₀ 0 * φc (c - 0) ≠ 0
      rw [h1, h2]
      norm_num
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by positivity)) hb

/-- A nonconstant bump has a nonzero directional derivative somewhere (dimension `≥ 1`). -/
theorem exists_fderiv_contDiffBump_ne_zero (hd : 0 < d) {c : Space d} (φ : ContDiffBump c) :
    ∃ t v, fderiv ℝ φ t v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ t, fderiv ℝ φ t = 0 := fun t => ContinuousLinearMap.ext (hcon t)
  have hdiff : Differentiable ℝ φ := (φ.contDiff (n := 1)).differentiable (by simp)
  have hc : ∀ t, φ t = φ c := fun t => is_const_of_fderiv_eq_zero hdiff hzero t c
  let t₀ : Space d := c + EuclideanSpace.single (⟨0, hd⟩ : Fin d) φ.rOut
  have h0 : φ t₀ = 0 := by
    refine φ.zero_of_le_dist ?_
    simp [t₀, dist_eq_norm, abs_of_pos φ.rOut_pos]
  have h1 : φ c = 1 := φ.one_of_mem_closedBall (by simpa using φ.rIn_pos.le)
  have := hc t₀
  rw [h0, h1] at this
  exact zero_ne_one this

/-- **Nonzero consumer, mollified derivative.**  For the standard bumps in dimension `≥ 1`, the
reflected translated derivative kernel `t ↦ fderiv ℝ φ_c (x - t) v` is a nonzero test function
(it is nonzero at `t = 0` for a suitable `x`, `v`), and the derivative duality bound holds
for it. -/
theorem sobolevDualityBound_fderiv_bump (hd : 0 < d) (s : ℝ) (c : Space d) :
    ∃ x v : Space d, fderiv ℝ (default : ContDiffBump c) (x - 0) v ≠ 0 ∧
      ENNReal.ofReal
          (|∫ t, (default : ContDiffBump (0 : Space d)) t
              * fderiv ℝ (default : ContDiffBump c) (x - t) v| ^ 2)
        ≤ sobolevNormSq d s (default : ContDiffBump (0 : Space d))
          * sobolevNormSq d (-s)
              (fun t => fderiv ℝ (default : ContDiffBump c) (x - t) v) := by
  obtain ⟨x, v, hx⟩ := exists_fderiv_contDiffBump_ne_zero hd (default : ContDiffBump c)
  exact ⟨x, v, by simpa using hx, sobolevDualityBound_fderiv s
    (isTestFn_contDiffBump (default : ContDiffBump (0 : Space d)))
    (isTestFn_contDiffBump (default : ContDiffBump c)) x v⟩

end Consumers

end LatticeProb.Sobolev
