/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatKernelSquareGreen6 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen5
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
On `U = (a, a+L)²` let `g_p = gradFeat U φ_p ∈ GradSpace U` (`φ_p = HeatSq.sqMode a L p`, i.e.
`(2π)^{-1/2} ∇φ_p`). Then:

* `HeatSq.inner_gradFeat_sqMode_test` (G1): for `f ∈ C_c^∞(U)`,
  `⟪g_p, ∇f⟫ = (2π)⁻¹ λ_p ∫ φ_p f` with `λ_p = 2 sqRate L p = π²(j²+k²)/L²` (weak eigen-equation
  `HeatSq.integral_gradInner_sqMode`);
* `HeatSq.inner_gradFeat_sqMode` (G2): `⟪g_p, g_q⟫ = (2π)⁻¹ λ_p (L/2)² δ_{pq}` (`q.1, q.2 ≥ 1`):
  `∂_xφ_p = (πj/L) cos·sin`, `∂_yφ_p = (πk/L) sin·cos` and the 1-D orthogonality relations.

Standard computations with the Dirichlet eigenfunctions of the square (e.g. Evans, *PDE*, §6.5);
own elementary proofs.
-/

noncomputable section

open Real MeasureTheory Set Filter Topology QuantumZipper QuantumZipper.K3
open scoped RealInnerProductSpace

namespace LQGMetric
namespace HeatSq

lemma isOpen_sqOpen (a L : ℝ) : IsOpen (sqOpen a L) := by
  have e : sqOpen a L = {z : ℂ | a < z.re} ∩ {z | z.re < a + L} ∩ {z | a < z.im} ∩
      {z | z.im < a + L} := by
    ext z; simp [sqOpen, and_assoc]
  rw [e]
  exact (((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)).inter
    (isOpen_lt continuous_const Complex.continuous_im)).inter
    (isOpen_lt Complex.continuous_im continuous_const)

/-- the open square as an element of `Opens ℂ` -/
def sqOpens (a L : ℝ) : TopologicalSpace.Opens ℂ := ⟨sqOpen a L, isOpen_sqOpen a L⟩

lemma isBounded_sqOpen (a L : ℝ) : Bornology.IsBounded (sqOpen a L) := by
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2 * (|a| + |a + L|))).subset
    fun z hz => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have hre : |z.re| ≤ |a| + |a + L| := by
    rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases (a + L) <;> linarith
  have him : |z.im| ≤ |a| + |a + L| := by
    rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases (a + L) <;> linarith
  linarith [Complex.norm_le_abs_re_add_abs_im z]

lemma integrableOn_sqOpen_of_continuous {a L : ℝ} {F : ℂ → ℝ} (hF : Continuous F) :
    IntegrableOn F (sqOpen a L) := by
  obtain ⟨R, hR⟩ := (isBounded_sqOpen a L).subset_closedBall 0
  exact (hF.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set hR

lemma hasDerivAt_sinMode (a L : ℝ) (k : ℕ) (u : ℝ) :
    HasDerivAt (sinMode a L k) (π * k / L * cosMode a L k u) u := by
  have h := hasDerivAt_sinShift (π * k / L) a u
  have e1 : sinMode a L k = fun u => Real.sin (π * k / L * (u - a)) := funext (sinMode_eq a L k)
  have e2 : cosMode a L k u = Real.cos (π * k / L * (u - a)) := by
    unfold cosMode; congr 1; ring
  rw [e1, e2]; exact h

lemma contDiff_sinMode (a L : ℝ) (k : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sinMode a L k) := by
  unfold sinMode; fun_prop

lemma contDiff_sqMode (a L : ℝ) (p : ℕ × ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sqMode a L p) := by
  unfold sqMode
  exact ((contDiff_sinMode a L p.1).comp Complex.reCLM.contDiff).mul
    ((contDiff_sinMode a L p.2).comp Complex.imCLM.contDiff)

lemma continuous_cosMode (a L : ℝ) (k : ℕ) : Continuous (cosMode a L k) := by
  unfold cosMode; fun_prop

lemma continuous_sinMode (a L : ℝ) (k : ℕ) : Continuous (sinMode a L k) := by
  unfold sinMode; fun_prop

lemma fderiv_sqMode_one (a L : ℝ) (p : ℕ × ℕ) (z : ℂ) :
    fderiv ℝ (sqMode a L p) z 1 = sinMode a L p.2 z.im * (π * p.1 / L * cosMode a L p.1 z.re) := by
  have h := hasFDerivAt_sep (hasDerivAt_sinMode a L p.1) (hasDerivAt_sinMode a L p.2) z
  have e : sqMode a L p = fun w : ℂ => sinMode a L p.1 w.re * sinMode a L p.2 w.im := rfl
  rw [e, h.fderiv]; simp

lemma fderiv_sqMode_I (a L : ℝ) (p : ℕ × ℕ) (z : ℂ) :
    fderiv ℝ (sqMode a L p) z Complex.I =
      sinMode a L p.1 z.re * (π * p.2 / L * cosMode a L p.2 z.im) := by
  have h := hasFDerivAt_sep (hasDerivAt_sinMode a L p.1) (hasDerivAt_sinMode a L p.2) z
  have e : sqMode a L p = fun w : ℂ => sinMode a L p.1 w.re * sinMode a L p.2 w.im := rfl
  rw [e, h.fderiv]; simp

lemma continuous_fderiv_sqMode (a L : ℝ) (p : ℕ × ℕ) : Continuous (fderiv ℝ (sqMode a L p)) :=
  (contDiff_sqMode a L p).continuous_fderiv (by simp)

lemma memLp_gradVal_sqMode (a L : ℝ) (p : ℕ × ℕ) :
    MemLp (gradVal (sqMode a L p)) 2 (gradMeasure (sqOpen a L)) :=
  memLp_gradVal ((contDiff_sqMode a L p).of_le (by simp))
    (integrableOn_sqOpen_of_continuous ((continuous_fderiv_sqMode a L p).norm.pow 2))

lemma sum_gradVal_mul (f g : ℂ → ℝ) (z : ℂ) :
    ∑ i : Fin 2, gradVal f (z, i) * gradVal g (z, i) = (2 * π)⁻¹ * gradInner f g z := by
  have hc : (Real.sqrt (2 * π))⁻¹ * (Real.sqrt (2 * π))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  rw [Fin.sum_univ_two]
  simp only [gradVal, gradVec, gradInner]
  simp only [Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, one_ne_zero]
  rw [← hc]
  ring

/-- the Dirichlet inner product of two gradient features -/
theorem inner_gradFeat_eq {D : Set ℂ} {f g : ℂ → ℝ} (hf : MemLp (gradVal f) 2 (gradMeasure D))
    (hg : MemLp (gradVal g) 2 (gradMeasure D)) :
    ⟪gradFeat D f, gradFeat D g⟫ = (2 * π)⁻¹ * ∫ z in D, gradInner f g z := by
  have e1 : gradFeat D f = hf.toLp _ := by simp [gradFeat, hf]
  have e2 : gradFeat D g = hg.toLp _ := by simp [gradFeat, hg]
  rw [e1, e2, L2.inner_def]
  have h1 : ∫ p, ⟪hf.toLp (gradVal f) p, hg.toLp (gradVal g) p⟫ ∂(gradMeasure D) =
      ∫ p, gradVal f p * gradVal g p ∂(gradMeasure D) := by
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with p h1 h2
    rw [h1, h2, RCLike.inner_apply, conj_trivial, mul_comm]
  have hint : Integrable (fun p => gradVal f p * gradVal g p) (gradMeasure D) :=
    hf.integrable_mul hg
  rw [h1, integral_prod _ hint]
  simp only [integral_count, sum_gradVal_mul]
  rw [integral_const_mul]

/-- **G1.** `⟪g_p, ∇f⟫ = (2π)⁻¹ λ_p ∫ φ_p f` for `f ∈ C_c^∞(U)`. -/
theorem inner_gradFeat_sqMode_test {a L : ℝ} (p : ℕ × ℕ) {f : ℂ → ℝ}
    (hf : f ∈ zeroSpace (sqOpen a L)) :
    ⟪gradFeat (sqOpen a L) (sqMode a L p), gradFeat (sqOpen a L) f⟫ =
      (2 * π)⁻¹ * (2 * sqRate L p * ∫ z, sqMode a L p z * f z) := by
  have hf1 : ContDiff ℝ 1 f := hf.1.of_le (by simp)
  have hfL : MemLp (gradVal f) 2 (gradMeasure (sqOpen a L)) :=
    memLp_gradVal hf1 (integrableOn_sqOpen_of_continuous
      ((hf1.continuous_fderiv one_ne_zero).norm.pow 2))
  rw [inner_gradFeat_eq (memLp_gradVal_sqMode a L p) hfL,
    ← integral_gradInner_sqMode p hf1 hf.2.1]
  congr 1
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
  have h0 : fderiv ℝ f z = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := f) fun h => hz (hf.2.2 h)
  simp [gradInner, h0]

/-- **G2.** Orthogonality and norms of the gradient features of the modes. -/
theorem inner_gradFeat_sqMode {a L : ℝ} (hL : 0 < L) (p q : ℕ × ℕ) (hq1 : q.1 ≠ 0)
    (hq2 : q.2 ≠ 0) :
    ⟪gradFeat (sqOpen a L) (sqMode a L p), gradFeat (sqOpen a L) (sqMode a L q)⟫ =
      if p = q then (2 * π)⁻¹ * (2 * sqRate L p * (L / 2) ^ 2) else 0 := by
  rw [inner_gradFeat_eq (memLp_gradVal_sqMode a L p) (memLp_gradVal_sqMode a L q)]
  have e : ∀ z : ℂ, gradInner (sqMode a L p) (sqMode a L q) z =
      (π * p.1 / L * (π * q.1 / L)) * ((cosMode a L p.1 z.re * cosMode a L q.1 z.re) *
        (sinMode a L p.2 z.im * sinMode a L q.2 z.im)) +
      (π * p.2 / L * (π * q.2 / L)) * ((sinMode a L p.1 z.re * sinMode a L q.1 z.re) *
        (cosMode a L p.2 z.im * cosMode a L q.2 z.im)) := fun z => by
    rw [gradInner, fderiv_sqMode_one, fderiv_sqMode_one, fderiv_sqMode_I, fderiv_sqMode_I]; ring
  simp_rw [e]
  have c1 : Continuous fun z : ℂ => (cosMode a L p.1 z.re * cosMode a L q.1 z.re) *
      (sinMode a L p.2 z.im * sinMode a L q.2 z.im) := by
    have := continuous_cosMode a L; have := continuous_sinMode a L; fun_prop
  have c2 : Continuous fun z : ℂ => (sinMode a L p.1 z.re * sinMode a L q.1 z.re) *
      (cosMode a L p.2 z.im * cosMode a L q.2 z.im) := by
    have := continuous_cosMode a L; have := continuous_sinMode a L; fun_prop
  rw [integral_add ((integrableOn_sqOpen_of_continuous c1).const_mul _)
      ((integrableOn_sqOpen_of_continuous c2).const_mul _), integral_const_mul,
    integral_const_mul,
    integral_sqOpen_re_mul_im a L (fun t => cosMode a L p.1 t * cosMode a L q.1 t)
      (fun t => sinMode a L p.2 t * sinMode a L q.2 t),
    integral_sqOpen_re_mul_im a L (fun t => sinMode a L p.1 t * sinMode a L q.1 t)
      (fun t => cosMode a L p.2 t * cosMode a L q.2 t),
    integral_cosMode_mul_cosMode hL hq1, integral_sinMode_mul_sinMode hL hq2,
    integral_sinMode_mul_sinMode hL hq1, integral_cosMode_mul_cosMode hL hq2]
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk.injEq]
  by_cases h1 : p1 = q1 <;> by_cases h2 : p2 = q2 <;> simp only [h1, h2, ite_true, ite_false,
    and_true, and_false, mul_zero, zero_mul, add_zero]
  subst h1; subst h2
  unfold sqRate
  field_simp

end HeatSq
end LQGMetric
