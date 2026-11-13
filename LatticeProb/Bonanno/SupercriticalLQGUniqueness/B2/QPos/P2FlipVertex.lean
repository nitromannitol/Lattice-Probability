/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2FlipVertex at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2Avoid
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2RayKnight

 










set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.B2.QPos

 
theorem integral_exp_neg_mul_sq_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    ∫ x, Real.exp (-s * x ^ 2) ∂(gaussianReal 0 v) = (Real.sqrt (1 + 2 * s * v))⁻¹ := by
  have hv0 : (0 : ℝ) < v := lt_of_le_of_ne v.2 (Ne.symm (by exact_mod_cast hv))
  rw [integral_gaussianReal_eq_integral_smul hv]
  have h : ∀ x : ℝ, gaussianPDFReal 0 v x • Real.exp (-s * x ^ 2) =
      (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(s + 1 / (2 * v)) * x ^ 2) := by
    intro x
    rw [gaussianPDFReal_def, smul_eq_mul, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian]
  have hb : 0 < s + 1 / (2 * (v : ℝ)) := by positivity
  rw [← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_mul (inv_nonneg.mpr (by positivity))]
  congr 1
  field_simp
  ring

namespace WiredConductances

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WiredConductances V)

theorem integral_gff_exp_neg_sq (hK : G.precision.PosDef) (p : V) {s : ℝ} (hs : 0 ≤ s) :
    ∫ φ, Real.exp (-s * (φ p) ^ 2) ∂G.gff = (Real.sqrt (1 + 2 * s * G.green p p))⁻¹ := by
  have hmp := measurePreserving_eval_multivariateGaussian (μ := 0) hK.inv.posSemidef (i := p)
  simp only [WithLp.ofLp_zero, Pi.zero_apply] at hmp
  have hint : ∫ φ, Real.exp (-s * (φ p) ^ 2) ∂G.gff =
      ∫ x, Real.exp (-s * x ^ 2) ∂(gaussianReal 0 ((G.precision⁻¹ p p).toNNReal)) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by fun_prop)]
  rw [hint]
  have hG := G.green_diag_pos hK p
  have hne : (G.precision⁻¹ p p).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hG
  rw [integral_exp_neg_mul_sq_gaussianReal hne hs,
    Real.coe_toNNReal (G.precision⁻¹ p p) hG.le]
  rfl

theorem integral_holdingLaw_exp_neg (hK : G.precision.PosDef) (s : Soup (Excursion V)) (p : V)
    {c : ℝ} (hc : 0 ≤ c) :
    ∫ L, Real.exp (-c * L p) ∂(G.holdingLaw s) =
      (G.totalRate p / (G.totalRate p + c)) ^ soupVisitCount s p := by
  have hp := fun v => isProbabilityMeasure_expConvPow (G.totalRate_pos hK v) (soupVisitCount s v)
  have hmp := measurePreserving_eval (fun v => expConvPow (G.totalRate v) (soupVisitCount s v)) p
  have hint : ∫ L, Real.exp (-c * L p) ∂(G.holdingLaw s) =
      ∫ x, Real.exp (-c * x) ∂(expConvPow (G.totalRate p) (soupVisitCount s p)) := by
    unfold holdingLaw
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by fun_prop)]
  rw [hint, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x =>
    (Real.exp_pos _).le) (by fun_prop)]
  have hl := lintegral_exp_neg_expConvPow (G.totalRate_pos hK p) hc (soupVisitCount s p)
  simp_rw [neg_mul] at hl ⊢
  rw [hl, ENNReal.toReal_ofReal (pow_nonneg (div_nonneg (G.totalRate_pos hK p).le
    (by linarith [G.totalRate_pos hK p])) _)]

 
theorem integral_flip_vertex (hK : G.precision.PosDef) (s : Soup (Excursion V)) (p : V)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ∫ L, ∫ φ, Real.exp (-2 * κ * (2 * L p + (φ p) ^ 2)) ∂G.gff ∂(G.holdingLaw s) =
      (G.totalRate p / (G.totalRate p + 4 * κ)) ^ soupVisitCount s p *
        (Real.sqrt (1 + 4 * κ * G.green p p))⁻¹ := by
  have hsplit : ∀ L : V → ℝ, ∀ φ : EuclideanSpace ℝ V,
      Real.exp (-2 * κ * (2 * L p + (φ p) ^ 2)) =
        Real.exp (-(4 * κ) * L p) * Real.exp (-(2 * κ) * (φ p) ^ 2) := by
    intro L φ
    rw [← Real.exp_add]; congr 1; ring
  simp_rw [hsplit]
  simp_rw [integral_const_mul]
  rw [G.integral_gff_exp_neg_sq hK p (by positivity), integral_mul_const,
    G.integral_holdingLaw_exp_neg hK s p (by positivity)]
  congr 3
  ring

 
theorem hasSum_soupMass_visit_pos (hK : G.precision.PosDef) {t : ℝ} (ht : 0 ≤ t) (p : V)
    {κ : ℝ} (hκ : 0 < κ) :
    HasSum (fun s => G.soupMassAt t s *
        (if soupVisitCount s p = 0 then 0 else
          (G.totalRate p / (G.totalRate p + 4 * κ)) ^ soupVisitCount s p))
      (Real.exp (-(t * (4 * κ / (1 + 4 * κ * G.green p p)))) -
        Real.exp (-(t / G.green p p))) := by
  have hr := G.totalRate_pos hK p
  have hr0 : 0 < G.totalRate p / (G.totalRate p + 4 * κ) := by positivity
  have hr1 : G.totalRate p / (G.totalRate p + 4 * κ) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have h1 := G.hasSum_soupMass_pow_visit hK ht p hr0 hr1
  have hα : G.totalRate p * (1 - G.totalRate p / (G.totalRate p + 4 * κ)) /
      (G.totalRate p / (G.totalRate p + 4 * κ)) = 4 * κ := by
    field_simp
    ring
  rw [hα] at h1
  have h0 := G.hasSum_soupMass_visit_zero hK ht p
  have := h1.sub h0
  have hfun : (fun s => G.soupMassAt t s *
      (if soupVisitCount s p = 0 then 0 else
        (G.totalRate p / (G.totalRate p + 4 * κ)) ^ soupVisitCount s p)) =
      fun s => G.soupMassAt t s * (G.totalRate p / (G.totalRate p + 4 * κ)) ^ soupVisitCount s p -
        (if soupVisitCount s p = 0 then G.soupMassAt t s else 0) := by
    funext s
    by_cases hs : soupVisitCount s p = 0
    · rw [if_pos hs, if_pos hs, hs, pow_zero]; ring
    · rw [if_neg hs, if_neg hs, sub_zero]
  rw [hfun]
  exact this

 
theorem exp_neg_sub_exp_neg_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.exp (-x) - Real.exp (-y) ≤ y - x := by
  have h1 : Real.exp (-x) - Real.exp (-y) = Real.exp (-x) * (1 - Real.exp (-(y - x))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
  rw [h1]
  have h2 : 1 - Real.exp (-(y - x)) ≤ y - x := by
    have := Real.add_one_le_exp (-(y - x)); linarith
  have h3 : 0 ≤ 1 - Real.exp (-(y - x)) := by
    have : Real.exp (-(y - x)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  calc Real.exp (-x) * (1 - Real.exp (-(y - x))) ≤ 1 * (1 - Real.exp (-(y - x))) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by linarith)) h3
    _ ≤ y - x := by linarith

 
def flipBound (A S : ℝ) : ℝ := (Real.exp (-(A / (1 + S))) - Real.exp (-(A / S))) *
  (Real.sqrt (1 + S))⁻¹

theorem flipBound_le_poly' {A S : ℝ} (hA : 0 ≤ A) (hS : 0 < S) :
    flipBound A S ≤ A / (S * (1 + S)) * (Real.sqrt (1 + S))⁻¹ := by
  unfold flipBound
  have hd : Real.exp (-(A / (1 + S))) - Real.exp (-(A / S)) ≤ A / S - A / (1 + S) :=
    exp_neg_sub_exp_neg_le (by positivity) (div_le_div_of_nonneg_left hA hS (by linarith))
  have heq : A / S - A / (1 + S) = A / (S * (1 + S)) := by field_simp; ring
  rw [← heq]
  exact mul_le_mul_of_nonneg_right hd (inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem flipBound_le_exp {A S : ℝ} (hS : 0 ≤ S) :
    flipBound A S ≤ Real.exp (-(A / (1 + S))) := by
  unfold flipBound
  have hsq : (Real.sqrt (1 + S))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
    rw [Real.one_le_sqrt]; linarith)
  have hle : Real.exp (-(A / (1 + S))) - Real.exp (-(A / S)) ≤ Real.exp (-(A / (1 + S))) := by
    linarith [Real.exp_pos (-(A / S))]
  rcases le_or_gt (Real.exp (-(A / (1 + S))) - Real.exp (-(A / S))) 0 with h | h
  · calc (Real.exp (-(A / (1 + S))) - Real.exp (-(A / S))) * (Real.sqrt (1 + S))⁻¹ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h (inv_nonneg.mpr (Real.sqrt_nonneg _))
      _ ≤ Real.exp (-(A / (1 + S))) := (Real.exp_pos _).le
  · calc (Real.exp (-(A / (1 + S))) - Real.exp (-(A / S))) * (Real.sqrt (1 + S))⁻¹
        ≤ (Real.exp (-(A / (1 + S))) - Real.exp (-(A / S))) * 1 :=
          mul_le_mul_of_nonneg_left hsq h.le
      _ ≤ Real.exp (-(A / (1 + S))) := by rw [mul_one]; exact hle

theorem flipBound_nonneg {A S : ℝ} (hA : 0 ≤ A) (hS : 0 < S) : 0 ≤ flipBound A S := by
  unfold flipBound
  refine mul_nonneg ?_ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  rw [sub_nonneg, Real.exp_le_exp, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left hA hS (by linarith)

 

theorem hasSum_flip_vertex (hK : G.precision.PosDef) {t : ℝ} (ht : 0 ≤ t) (p : V)
    {κ : ℝ} (hκ : 0 < κ) :
    HasSum (fun s => G.soupMassAt t s *
        ∫ L, ∫ φ, (if soupVisitCount s p = 0 then 0 else
          Real.exp (-2 * κ * (2 * L p + (φ p) ^ 2))) ∂G.gff ∂(G.holdingLaw s))
      (flipBound (4 * κ * t) (4 * κ * G.green p p)) := by
  have hG := G.green_diag_pos hK p
  have h := (G.hasSum_soupMass_visit_pos hK ht p hκ).mul_right
    (Real.sqrt (1 + 4 * κ * G.green p p))⁻¹
  have hval : (Real.exp (-(t * (4 * κ / (1 + 4 * κ * G.green p p)))) -
      Real.exp (-(t / G.green p p))) * (Real.sqrt (1 + 4 * κ * G.green p p))⁻¹ =
      flipBound (4 * κ * t) (4 * κ * G.green p p) := by
    unfold flipBound
    congr 3
    · congr 1; field_simp
    · congr 1; field_simp
  rw [hval] at h
  have hfun : (fun s => G.soupMassAt t s *
      ∫ L, ∫ φ, (if soupVisitCount s p = 0 then 0 else
        Real.exp (-2 * κ * (2 * L p + (φ p) ^ 2))) ∂G.gff ∂(G.holdingLaw s)) =
      fun s => G.soupMassAt t s * (if soupVisitCount s p = 0 then 0 else
        (G.totalRate p / (G.totalRate p + 4 * κ)) ^ soupVisitCount s p) *
          (Real.sqrt (1 + 4 * κ * G.green p p))⁻¹ := by
    funext s
    by_cases hs : soupVisitCount s p = 0
    · simp [hs]
    · simp only [hs, if_false]
      rw [G.integral_flip_vertex hK s p hκ.le]
      ring
  rw [hfun]
  exact h

end WiredConductances

end SupercriticalLQGUniqueness.B2.QPos
