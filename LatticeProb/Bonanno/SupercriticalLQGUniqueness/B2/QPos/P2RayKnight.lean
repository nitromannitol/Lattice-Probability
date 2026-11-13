/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2RayKnight at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2LocalTime
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2GaussQuad

 












set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Complex Matrix
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos

namespace WiredConductances

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WiredConductances V)

 
theorem precisionShift_mulVec_one (θ : V → ℝ) (i : V) :
    (G.precisionShift θ *ᵥ fun _ => (1 : ℂ)) i = (G.boundary i : ℂ) - θ i * I := by
  rw [G.precisionShift_mulVec]
  simp only [mul_one, totalRate]
  push_cast
  ring

theorem precisionShift_transpose (θ : V → ℝ) :
    (G.precisionShift θ)ᵀ = G.precisionShift θ := by
  unfold precisionShift
  rw [Matrix.transpose_sub, Matrix.diagonal_transpose, ← Matrix.transpose_map]
  have h := G.precision_isHermitian.eq
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [h]

 
theorem rayKnight_exponent (hK : G.precision.PosDef) (θ : V → ℝ) :
    let Y := G.shiftResolvent θ
    let p : V → ℂ := fun v => I * (1 - Y v)
    (G.precisionShift θ *ᵥ p = fun v => (θ v : ℂ)) ∧
      (∑ v, (θ v : ℂ) * p v - I * ∑ v, (θ v : ℂ)) =
        (G.boundaryTotal : ℂ) - ∑ i, (G.boundary i : ℂ) * Y i := by
  intro Y p
  have hBY := G.precisionShift_mulVec_shiftResolvent hK θ
  have hB1 := G.precisionShift_mulVec_one θ
  constructor
  · have : p = I • ((fun _ => (1 : ℂ)) - Y) := by
      funext v; simp [p]
    rw [this, Matrix.mulVec_smul, Matrix.mulVec_sub, hBY]
    funext v
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hB1]
    ring_nf
    rw [Complex.I_sq]
    ring
  · have hθ : ∀ v, (θ v : ℂ) = I * ((G.precisionShift θ *ᵥ fun _ => (1 : ℂ)) v -
        (G.boundary v : ℂ)) := by
      intro v
      rw [hB1]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hsym : (G.precisionShift θ *ᵥ fun _ => (1 : ℂ)) ⬝ᵥ Y =
        ∑ i, (G.boundary i : ℂ) := by
      rw [dotProduct_mulVec_symm _ (G.precisionShift_transpose θ), hBY]
      simp [dotProduct]
    have hθY : ∑ v, (θ v : ℂ) * Y v = I * ((G.boundaryTotal : ℂ) -
        ∑ i, (G.boundary i : ℂ) * Y i) := by
      simp_rw [hθ]
      have : ∑ v, I * ((G.precisionShift θ *ᵥ fun _ => (1 : ℂ)) v - (G.boundary v : ℂ)) * Y v =
          I * ((G.precisionShift θ *ᵥ fun _ => (1 : ℂ)) ⬝ᵥ Y - ∑ v, (G.boundary v : ℂ) * Y v) := by
        rw [mul_sub, dotProduct, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro v _
        ring
      rw [this, hsym, boundaryTotal]
      push_cast
      rfl
    have hp : ∑ v, (θ v : ℂ) * p v = I * ∑ v, (θ v : ℂ) - I * ∑ v, (θ v : ℂ) * Y v := by
      simp only [p, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v _
      ring
    rw [hp, hθY]
    ring_nf
    rw [Complex.I_sq]
    ring

 
def localTimeLawE (t : ℝ) : Measure (EuclideanSpace ℝ V) :=
  (G.localTimeLaw t).map (WithLp.toLp 2)

theorem isProbabilityMeasure_localTimeLawE (hK : G.precision.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    IsProbabilityMeasure (G.localTimeLawE t) := by
  have := G.isProbabilityMeasure_localTimeLaw hK ht
  unfold localTimeLawE
  infer_instance

 
abbrev gff : Measure (EuclideanSpace ℝ V) := multivariateGaussian 0 G.precision⁻¹

 
def shiftSqHalf (w : ℝ) (φ : EuclideanSpace ℝ V) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 fun v => (φ v + w) ^ 2 / 2

theorem continuous_shiftSqHalf (w : ℝ) : Continuous (shiftSqHalf (V := V) w) := by
  unfold shiftSqHalf
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun v => ?_)
  exact (((PiLp.continuous_apply 2 _ v).add continuous_const).pow 2).div_const _

theorem charFun_map_shiftSqHalf (w : ℝ) (θ : EuclideanSpace ℝ V) :
    charFun (G.gff.map (shiftSqHalf w)) θ =
      ∫ φ, cexp (((∑ v, θ v * (φ v + w) ^ 2 / 2 : ℝ) : ℂ) * I) ∂G.gff := by
  rw [charFun_apply, integral_map (continuous_shiftSqHalf w).measurable.aemeasurable
    (by fun_prop)]
  congr 1
  funext φ
  congr 3
  simp only [shiftSqHalf, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  try (apply Finset.sum_congr rfl; intro v _; ring)

theorem charFun_localTimeLawE (hK : G.precision.PosDef) {t : ℝ} (ht : 0 ≤ t)
    (θ : EuclideanSpace ℝ V) :
    charFun (G.localTimeLawE t) θ =
      Complex.exp (-(t * G.boundaryTotal)) *
        Complex.exp (t * ∑ i, (G.boundary i : ℂ) * G.shiftResolvent (fun v => θ v) i) := by
  rw [charFun_apply, localTimeLawE, integral_map (by fun_prop) (by fun_prop)]
  rw [← G.integral_cexp_localTimeLaw hK ht (fun v => θ v)]
  congr 1

 

theorem rayKnight (hK : G.precision.PosDef) (u : ℝ) :
    ((G.localTimeLawE (u ^ 2 / 2)).prod G.gff).map (fun q => q.1 + shiftSqHalf 0 q.2) =
      G.gff.map (shiftSqHalf u) := by
  have ht : (0 : ℝ) ≤ u ^ 2 / 2 := by positivity
  have := G.isProbabilityMeasure_localTimeLawE hK ht
  have hmap : ((G.localTimeLawE (u ^ 2 / 2)).prod G.gff).map (fun q => q.1 + shiftSqHalf 0 q.2) =
      ((G.localTimeLawE (u ^ 2 / 2)).prod (G.gff.map (shiftSqHalf 0))).map
        (fun q => q.1 + q.2) := by
    conv_rhs => rw [show G.localTimeLawE (u ^ 2 / 2) = (G.localTimeLawE (u ^ 2 / 2)).map id
      from Measure.map_id.symm]
    rw [Measure.map_prod_map _ _ measurable_id (continuous_shiftSqHalf 0).measurable,
      Measure.map_map (by fun_prop)
        (measurable_id.prodMap (continuous_shiftSqHalf 0).measurable)]
    rfl
  apply Measure.ext_of_charFun
  funext θ
  rw [hmap, charFun_map_add_prod_eq_mul, Pi.mul_apply, G.charFun_localTimeLawE hK ht,
    G.charFun_map_shiftSqHalf, G.charFun_map_shiftSqHalf]
  obtain ⟨hp, hexp⟩ := G.rayKnight_exponent hK (fun v => θ v)
  have hq := integral_cexp_shift_sq G.precision hK (fun v => θ v) u _ hp
  simp only [add_zero] at hq ⊢
  rw [hq, hexp]
  rw [mul_comm]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

 
def sqrtTwice (x : EuclideanSpace ℝ V) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 fun v => Real.sqrt (2 * x v)

theorem continuous_sqrtTwice : Continuous (sqrtTwice (V := V)) := by
  unfold sqrtTwice
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun v => ?_)
  exact Real.continuous_sqrt.comp (continuous_const.mul (PiLp.continuous_apply 2 _ v))

 
theorem rayKnight_abs (hK : G.precision.PosDef) (u : ℝ) :
    ((G.localTimeLawE (u ^ 2 / 2)).prod G.gff).map
        (fun q => WithLp.toLp 2 fun v => Real.sqrt (2 * q.1 v + q.2 v ^ 2)) =
      G.gff.map (fun φ => WithLp.toLp 2 fun v => |φ v + u|) := by
  have h := congrArg (fun μ => μ.map sqrtTwice) (G.rayKnight hK u)
  rw [Measure.map_map continuous_sqrtTwice.measurable (by
      exact (measurable_fst.add ((continuous_shiftSqHalf 0).measurable.comp
        measurable_snd))),
    Measure.map_map continuous_sqrtTwice.measurable (continuous_shiftSqHalf u).measurable] at h
  convert h using 2
  · funext q
    simp only [Function.comp, sqrtTwice, shiftSqHalf, add_zero]
    congr 1
    funext v
    simp only [PiLp.add_apply]
    congr 1
    ring
  · funext φ
    simp only [Function.comp, sqrtTwice, shiftSqHalf]
    congr 1
    funext v
    rw [show 2 * ((φ v + u) ^ 2 / 2) = (φ v + u) ^ 2 by ring, Real.sqrt_sq_eq_abs]

end WiredConductances

end SupercriticalLQGUniqueness.B2.QPos
