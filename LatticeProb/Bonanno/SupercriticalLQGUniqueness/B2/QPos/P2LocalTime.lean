/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2LocalTime at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2PathSum
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2Soup
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2Holding

 








set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology Matrix
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos

 
def Excursion.visitCount {V : Type*} [DecidableEq V] (γ : Excursion V) (v : V) : ℕ :=
  (Finset.univ.filter fun j => γ.2 j = v).card

 
def soupVisitCount {V : Type*} [DecidableEq V] (s : Soup (Excursion V)) (v : V) : ℕ :=
  ∑ i, (s.2 i).visitCount v
theorem visitProduct_eq_prod_pow {V R : Type*} [Fintype V] [DecidableEq V] [CommMonoid R]
    (m : V → R) (γ : Excursion V) :
    visitProduct m γ = ∏ v, m v ^ γ.visitCount v := by
  unfold visitProduct Excursion.visitCount
  rw [← Finset.prod_fiberwise Finset.univ γ.2 (fun j => m (γ.2 j))]
  apply Finset.prod_congr rfl
  intro v _
  rw [Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]),
    Finset.prod_const]

theorem prod_visitProduct_eq_prod_pow {V R : Type*} [Fintype V] [DecidableEq V] [CommMonoid R]
    (m : V → R) (s : Soup (Excursion V)) :
    ∏ i, visitProduct m (s.2 i) = ∏ v, m v ^ soupVisitCount s v := by
  simp_rw [visitProduct_eq_prod_pow, soupVisitCount]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro v _
  rw [Finset.prod_pow_eq_pow_sum]

namespace WiredConductances

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WiredConductances V)

 
def boundaryTotal : ℝ := ∑ i, G.boundary i

 
def soupMassAt (t : ℝ) : Soup (Excursion V) → ℝ :=
  soupMass G.excursionWeight G.boundaryTotal t

theorem soupMassAt_nonneg {t : ℝ} (ht : 0 ≤ t) (s : Soup (Excursion V)) :
    0 ≤ G.soupMassAt t s :=
  soupMass_nonneg G.excursionWeight_nonneg _ ht s

theorem hasSum_soupMassAt (hK : G.precision.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (G.soupMassAt t) 1 :=
  hasSum_soupMass G.excursionWeight_nonneg (G.hasSum_excursionWeight hK) ht

 
def holdingLaw (s : Soup (Excursion V)) : Measure (V → ℝ) :=
  Measure.pi fun v => expConvPow (G.totalRate v) (soupVisitCount s v)

theorem isProbabilityMeasure_holdingLaw (hK : G.precision.PosDef) (s : Soup (Excursion V)) :
    IsProbabilityMeasure (G.holdingLaw s) := by
  have := fun v => isProbabilityMeasure_expConvPow (G.totalRate_pos hK v) (soupVisitCount s v)
  unfold holdingLaw
  infer_instance

 
def localTimeLaw (t : ℝ) : Measure (V → ℝ) :=
  Measure.sum fun s : Soup (Excursion V) => ENNReal.ofReal (G.soupMassAt t s) • G.holdingLaw s

theorem isProbabilityMeasure_localTimeLaw (hK : G.precision.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    IsProbabilityMeasure (G.localTimeLaw t) := by
  constructor
  rw [localTimeLaw, Measure.sum_apply _ MeasurableSet.univ]
  have := G.isProbabilityMeasure_holdingLaw hK
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (G.soupMassAt_nonneg ht)
    (G.hasSum_soupMassAt hK ht).summable, (G.hasSum_soupMassAt hK ht).tsum_eq,
    ENNReal.ofReal_one]

 
theorem integral_localTimeLaw (hK : G.precision.PosDef) {t : ℝ} (ht : 0 ≤ t)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : (V → ℝ) → E) (hf : Integrable f (G.localTimeLaw t)) :
    ∫ L, f L ∂(G.localTimeLaw t) = ∑' s, G.soupMassAt t s • ∫ L, f L ∂(G.holdingLaw s) := by
  rw [localTimeLaw, integral_sum_measure hf]
  congr 1
  funext s
  rw [integral_smul_measure, ENNReal.toReal_ofReal (G.soupMassAt_nonneg ht s)]

def precisionShift (θ : V → ℝ) : Matrix V V ℂ :=
  G.precision.map (fun x => (x : ℂ)) - Matrix.diagonal fun v => (θ v : ℂ) * I

theorem precisionShift_mulVec (θ : V → ℝ) (Y : V → ℂ) (i : V) :
    (G.precisionShift θ *ᵥ Y) i =
      ((G.totalRate i : ℂ) - θ i * I) * Y i - ∑ j, (G.edge i j : ℂ) * Y j := by
  simp only [precisionShift, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
  have hK : (G.precision.map (fun x => (x : ℂ)) *ᵥ Y) i =
      (G.totalRate i : ℂ) * Y i - ∑ j, (G.edge i j : ℂ) * Y j := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase Finset.univ (fun j => (G.edge i j : ℂ) * Y j) (Finset.mem_univ i)]
    rw [G.precision_diag, G.edge_self, Complex.ofReal_zero, zero_mul, zero_add]
    have : ∑ x ∈ Finset.univ.erase i, (G.precision i x : ℂ) * Y x =
        -∑ x ∈ Finset.univ.erase i, (G.edge i x : ℂ) * Y x := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hji : i ≠ j := (Finset.mem_erase.mp hj).1.symm
      simp [precision, hji]
    rw [this]
    ring
  rw [hK]
  ring

 
theorem precisionShift_mulVec_eq_zero (hK : G.precision.PosDef) (θ : V → ℝ) (z : V → ℂ)
    (hz : G.precisionShift θ *ᵥ z = 0) : z = 0 := by
  set x : V → ℝ := fun v => (z v).re
  set y : V → ℝ := fun v => (z v).im
  have hre : ∀ i, (G.precision *ᵥ x) i + θ i * y i = 0 := by
    intro i
    have h := congrArg Complex.re (congrFun hz i)
    simp only [precisionShift, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal,
      Pi.zero_apply, Complex.sub_re, Complex.zero_re] at h
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.re_sum,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub] at h
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_mul, add_zero] at h
    simp only [Matrix.mulVec, dotProduct, x, y]
    linarith
  have him : ∀ i, (G.precision *ᵥ y) i - θ i * x i = 0 := by
    intro i
    have h := congrArg Complex.im (congrFun hz i)
    simp only [precisionShift, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal,
      Pi.zero_apply, Complex.sub_im, Complex.zero_im] at h
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.im_sum,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.I_re, Complex.I_im, mul_zero, mul_one] at h
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, add_zero, sub_zero] at h
    simp only [Matrix.mulVec, dotProduct, x, y]
    linarith
  have hsum : x ⬝ᵥ (G.precision *ᵥ x) + y ⬝ᵥ (G.precision *ᵥ y) = 0 := by
    have h1 : x ⬝ᵥ (G.precision *ᵥ x) = -∑ i, x i * (θ i * y i) := by
      simp only [dotProduct, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have := hre i
      rw [show (G.precision *ᵥ x) i = -(θ i * y i) by linarith]
      ring
    have h2 : y ⬝ᵥ (G.precision *ᵥ y) = ∑ i, x i * (θ i * y i) := by
      simp only [dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      have := him i
      rw [show (G.precision *ᵥ y) i = θ i * x i by linarith]
      ring
    rw [h1, h2]
    ring
  have hx0 : x = 0 := by
    by_contra hx
    have hpos := hK.dotProduct_mulVec_pos hx
    have hnn := hK.posSemidef.dotProduct_mulVec_nonneg y
    simp only [star_trivial] at hpos hnn
    linarith
  have hy0 : y = 0 := by
    by_contra hy
    have hpos := hK.dotProduct_mulVec_pos hy
    have hnn := hK.posSemidef.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at hpos hnn
    linarith
  funext v
  apply Complex.ext
  · exact congrFun hx0 v
  · exact congrFun hy0 v

theorem isUnit_precisionShift_det (hK : G.precision.PosDef) (θ : V → ℝ) :
    IsUnit (G.precisionShift θ).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hz0 (G.precisionShift_mulVec_eq_zero hK θ z hz)

 
def shiftResolvent (θ : V → ℝ) : V → ℂ :=
  (G.precisionShift θ)⁻¹ *ᵥ fun i => (G.boundary i : ℂ)

theorem precisionShift_mulVec_shiftResolvent (hK : G.precision.PosDef) (θ : V → ℝ) :
    G.precisionShift θ *ᵥ G.shiftResolvent θ = fun i => (G.boundary i : ℂ) := by
  rw [shiftResolvent, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    (G.isUnit_precisionShift_det hK θ), Matrix.one_mulVec]

 
def holdingMultiplier (θ : V → ℝ) (v : V) : ℂ :=
  (G.totalRate v : ℂ) / ((G.totalRate v : ℂ) - θ v * I)

theorem holdingMultiplier_norm_le (hK : G.precision.PosDef) (θ : V → ℝ) (v : V) :
    ‖G.holdingMultiplier θ v‖ ≤ 1 := by
  have hr := G.totalRate_pos hK v
  unfold holdingMultiplier
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hden : G.totalRate v ≤ ‖(G.totalRate v : ℂ) - θ v * I‖ := by
    have : ((G.totalRate v : ℂ) - θ v * I).re = G.totalRate v := by simp
    calc G.totalRate v = |((G.totalRate v : ℂ) - θ v * I).re| := by rw [this, abs_of_pos hr]
      _ ≤ ‖(G.totalRate v : ℂ) - θ v * I‖ := Complex.abs_re_le_norm _
  exact div_le_one_of_le₀ hden (norm_nonneg _)

 
theorem shiftResolvent_fixedPoint (hK : G.precision.PosDef) (θ : V → ℝ) (i : V) :
    G.shiftResolvent θ i = G.holdingMultiplier θ i *
      (((G.boundary i / G.totalRate i : ℝ) : ℂ) +
        ∑ j, (G.killedTransition i j : ℂ) * G.shiftResolvent θ j) := by
  have h := congrFun (G.precisionShift_mulVec_shiftResolvent hK θ) i
  rw [G.precisionShift_mulVec] at h
  have hr : (G.totalRate i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (G.totalRate_pos hK i).ne'
  have hd : (G.totalRate i : ℂ) - θ i * I ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    exact (G.totalRate_pos hK i).ne' this
  unfold holdingMultiplier killedTransition
  push_cast
  simp_rw [div_eq_mul_inv]
  rw [show ∑ j, (G.edge i j : ℂ) * (G.totalRate i : ℂ)⁻¹ * G.shiftResolvent θ j =
      (G.totalRate i : ℂ)⁻¹ * ∑ j, (G.edge i j : ℂ) * G.shiftResolvent θ j by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring]
  field_simp
  linear_combination h

 

theorem integral_cexp_localTimeLaw (hK : G.precision.PosDef) {t : ℝ} (ht : 0 ≤ t)
    (θ : V → ℝ) :
    ∫ L, Complex.exp ((∑ v, θ v * L v : ℝ) * I) ∂(G.localTimeLaw t) =
      Complex.exp (-(t * G.boundaryTotal)) *
        Complex.exp (t * ∑ i, (G.boundary i : ℂ) * G.shiftResolvent θ i) := by
  have hprob := G.isProbabilityMeasure_localTimeLaw hK ht
  have hint : Integrable (fun L : V → ℝ => Complex.exp ((∑ v, θ v * L v : ℝ) * I))
      (G.localTimeLaw t) := by
    have hc : Continuous (fun L : V → ℝ => Complex.exp ((∑ v, θ v * L v : ℝ) * I)) :=
      Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_finsetSum _ fun v _ => continuous_const.mul (continuous_apply v))).mul
          continuous_const)
    refine Integrable.of_bound hc.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun L => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [G.integral_localTimeLaw hK ht _ hint]
  have hhold : ∀ s : Soup (Excursion V),
      ∫ L, Complex.exp ((∑ v, θ v * L v : ℝ) * I) ∂(G.holdingLaw s) =
        ∏ i, visitProduct (G.holdingMultiplier θ) (s.2 i) := by
    intro s
    rw [prod_visitProduct_eq_prod_pow]
    have hsplit : (fun L : V → ℝ => Complex.exp ((∑ v, θ v * L v : ℝ) * I)) =
        fun L => ∏ v, Complex.exp (θ v * L v * I) := by
      funext L
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      rw [Finset.sum_mul]
    have hp : ∀ v, IsProbabilityMeasure (expConvPow (G.totalRate v) (soupVisitCount s v)) :=
      fun v => isProbabilityMeasure_expConvPow (G.totalRate_pos hK v) _
    rw [hsplit, holdingLaw, integral_fintype_prod_eq_prod
      (f := fun v (x : ℝ) => Complex.exp (↑(θ v) * ↑x * I))]
    apply Finset.prod_congr rfl
    intro v _
    have := charFun_expConvPow (G.totalRate_pos hK v) (θ v) (soupVisitCount s v)
    rw [charFun_apply_real] at this
    rw [this]
    rfl
  simp_rw [hhold]
  have hsum := hasSum_soupMass_mul_prod G.excursionWeight_nonneg
    (G.hasSum_excursionWeight hK) ht (visitProduct (G.holdingMultiplier θ)) (by
      intro γ
      unfold visitProduct
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
        (fun j _ => G.holdingMultiplier_norm_le hK θ _))
  have hF := G.hasSum_excursion_visitProduct hK (G.holdingMultiplier θ)
    (G.holdingMultiplier_norm_le hK θ) (G.shiftResolvent θ) (G.shiftResolvent_fixedPoint hK θ)
  rw [hF.tsum_eq] at hsum
  unfold boundaryTotal
  rw [← hsum.tsum_eq]
  congr 1

end WiredConductances

end SupercriticalLQGUniqueness.B2.QPos
