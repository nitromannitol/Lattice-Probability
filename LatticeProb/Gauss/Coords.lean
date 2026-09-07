/-
An independent sequence of standard Gaussians, and the law of a finite linear
combination of its coordinates.

The construction of every Gaussian process here starts from one object: the
product of countably many standard Gaussians on `ℕ → ℝ`.  What is needed of it
is the law of `∑_{k<N} c_k ω_k`, and that is computed here directly from the
head-tail decomposition of the product measure rather than through the
independence API: the characteristic function satisfies the recursion
`φ_{N+1}(t) = e^{-c_0^2t^2/2} φ_N(t)` because splitting off the first
coordinate is exactly what the product measure does.
-/
import Mathlib
import LatticeProb.Prob.InfinitePiSplit
import LatticeProb.Gauss.Limit

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory Complex

open scoped ENNReal NNReal Topology

/-- The law of an independent sequence of standard Gaussians. -/
def gaussLaw : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1

instance isProbabilityMeasure_gaussLaw : IsProbabilityMeasure gaussLaw := by
  unfold gaussLaw
  infer_instance

/-- A bounded complex exponential is integrable on a finite measure. -/
theorem integrable_cexp_mul_I {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {g : Ω → ℝ} (hg : Measurable g) (t : ℝ) :
    Integrable (fun ω => Complex.exp ((t : ℂ) * (g ω : ℂ) * Complex.I)) P := by
  have hm : Measurable (fun ω => Complex.exp ((t : ℂ) * (g ω : ℂ) * Complex.I)) :=
    Complex.measurable_exp.comp
      (((Complex.measurable_ofReal.comp hg).const_mul _).mul_const _)
  refine Integrable.mono' (integrable_const 1) hm.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [show (t : ℂ) * (g ω : ℂ) * Complex.I = ((t * g ω : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)

/-- The partial sum `∑_{k<N} c_k ω_k`. -/
def gaussSum (c : ℕ → ℝ) (N : ℕ) (ω : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range N, c k * ω k

theorem measurable_gaussSum (c : ℕ → ℝ) (N : ℕ) : Measurable (gaussSum c N) := by
  unfold gaussSum
  exact Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).const_mul _

theorem gaussSum_consNat (c : ℕ → ℝ) (N : ℕ) (u : ℝ) (η : ℕ → ℝ) :
    gaussSum c (N + 1) (consNat u η) = c 0 * u + gaussSum (fun k => c (k + 1)) N η := by
  unfold gaussSum
  rw [Finset.sum_range_succ']
  simp [consNat]
  ring

/-- **The characteristic function of a finite linear combination of independent
standard Gaussians.** -/
theorem charFun_gaussSum (c : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    ∫ ω, Complex.exp ((t : ℂ) * (gaussSum c N ω : ℂ) * Complex.I) ∂gaussLaw
      = Complex.exp (-((∑ k ∈ Finset.range N, c k ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
  induction N generalizing c with
  | zero =>
      simp [gaussSum]
  | succ N ih =>
      have hint : Integrable
          (fun ω => Complex.exp ((t : ℂ) * (gaussSum c (N + 1) ω : ℂ) * Complex.I)) gaussLaw :=
        integrable_cexp_mul_I _ (measurable_gaussSum c (N + 1)) t
      rw [gaussLaw] at hint ⊢
      rw [integral_infinitePi_nat_head_tail (gaussianReal 0 1) _ hint]
      have hsplit : ∀ (u : ℝ) (η : ℕ → ℝ),
          Complex.exp ((t : ℂ) * (gaussSum c (N + 1) (consNat u η) : ℂ) * Complex.I)
            = Complex.exp ((t : ℂ) * ((c 0 * u : ℝ) : ℂ) * Complex.I) *
                Complex.exp ((t : ℂ) * (gaussSum (fun k => c (k + 1)) N η : ℂ) * Complex.I) := by
        intro u η
        rw [← Complex.exp_add, gaussSum_consNat]
        congr 1
        push_cast
        ring
      have hinner : ∀ u : ℝ,
          ∫ η, Complex.exp ((t : ℂ) * (gaussSum c (N + 1) (consNat u η) : ℂ) * Complex.I)
              ∂(Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
            = Complex.exp ((t : ℂ) * ((c 0 * u : ℝ) : ℂ) * Complex.I) *
                Complex.exp (-((∑ k ∈ Finset.range N, c (k + 1) ^ 2 : ℝ) : ℂ) *
                  (t : ℂ) ^ 2 / 2) := by
        intro u
        rw [integral_congr_ae (Filter.Eventually.of_forall fun η => hsplit u η),
          integral_const_mul]
        congr 1
        have := ih (c := fun k => c (k + 1))
        rw [gaussLaw] at this
        exact this
      rw [integral_congr_ae (Filter.Eventually.of_forall hinner), integral_mul_const]
      have houter : ∫ u, Complex.exp ((t : ℂ) * ((c 0 * u : ℝ) : ℂ) * Complex.I)
            ∂(gaussianReal 0 1)
          = Complex.exp (-((c 0 ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
        have h2 : (fun u : ℝ => Complex.exp ((t : ℂ) * ((c 0 * u : ℝ) : ℂ) * Complex.I))
            = fun u : ℝ => Complex.exp (((t * c 0 : ℝ) : ℂ) * (u : ℂ) * Complex.I) := by
          funext u
          congr 1
          push_cast
          ring
        rw [h2, ← charFun_apply_real, charFun_gaussianReal]
        push_cast
        ring_nf
      rw [houter, ← Complex.exp_add]
      congr 1
      rw [Finset.sum_range_succ']
      push_cast
      ring

/-- **The law of a finite linear combination of independent standard
Gaussians.** -/
theorem map_gaussSum (c : ℕ → ℝ) (N : ℕ) :
    gaussLaw.map (gaussSum c N)
      = gaussianReal 0 (∑ k ∈ Finset.range N, c k ^ 2).toNNReal := by
  haveI : IsProbabilityMeasure (gaussLaw.map (gaussSum c N)) :=
    Measure.isProbabilityMeasure_map (measurable_gaussSum c N).aemeasurable
  refine Measure.ext_of_charFun ?_
  funext t
  have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range N, c k ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hcast : (((∑ k ∈ Finset.range N, c k ^ 2).toNNReal : ℝ≥0) : ℝ)
      = ∑ k ∈ Finset.range N, c k ^ 2 := Real.coe_toNNReal _ hnn
  have hfm : AEStronglyMeasurable
      (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
      (gaussLaw.map (gaussSum c N)) :=
    (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  rw [charFun_apply_real, integral_map (measurable_gaussSum c N).aemeasurable hfm,
    charFun_gaussSum c N t, charFun_gaussianReal, hcast]
  push_cast
  ring_nf

end LatticeProb

end
