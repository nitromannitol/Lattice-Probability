/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5Nested at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4HarmonicMax
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFMarkovLaw

 












set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.QPos.P5

open P4

theorem mem_interiorSites_iff_sqBox (N : ℕ) (c : ℤ × ℤ) :
    c ∈ interiorSites N ↔ c ∈ sqBox 0 (2 ^ N) := by
  rw [interiorSites_eq_sqBox]

theorem mem_interiorSites_shift {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k)
    (c : DGFFSite (n - k)) : c.1 + z ∈ interiorSites n := by
  apply hk.2
  have hc : c.1 ∈ interiorSites (n - k) := c.2
  rw [mem_interiorSites_iff_sqBox, mem_sqBox] at hc
  rw [mem_sqBox]
  simpa using hc

 
def shiftSite {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k) (c : DGFFSite (n - k)) :
    DGFFSite n := ⟨c.1 + z, mem_interiorSites_shift hk c⟩

theorem shiftSite_val {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k)
    (c : DGFFSite (n - k)) : (shiftSite hk c).1 = c.1 + z := rfl

theorem shiftSite_mem {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k)
    (c : DGFFSite (n - k)) : shiftSite hk c ∈ scaleSites n z k := by
  unfold scaleSites boxSites siteFilter
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hc : c.1 ∈ interiorSites (n - k) := c.2
  rw [mem_interiorSites_iff_sqBox, mem_sqBox] at hc
  rw [shiftSite_val, mem_sqBox]
  simpa using hc

theorem unshift_mem {n : ℕ} {z : ℤ × ℤ} {k : ℕ} {d : DGFFSite n}
    (hd : d ∈ scaleSites n z k) : d.1 - z ∈ interiorSites (n - k) := by
  unfold scaleSites boxSites siteFilter at hd
  rw [Finset.mem_filter, mem_sqBox] at hd
  rw [mem_interiorSites_iff_sqBox, mem_sqBox]
  simpa using hd.2

 

def scaleEquiv {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k) :
    {d : DGFFSite n // d ∈ scaleSites n z k} ≃ DGFFSite (n - k) where
  toFun d := ⟨d.1.1 - z, unshift_mem d.2⟩
  invFun c := ⟨shiftSite hk c, shiftSite_mem hk c⟩
  left_inv d := by
    apply Subtype.ext; apply Subtype.ext
    simp [shiftSite_val]
  right_inv c := by
    apply Subtype.ext
    simp [shiftSite_val]

 
def tresCLM {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k) :
    EuclideanSpace ℝ (DGFFSite n) →L[ℝ] EuclideanSpace ℝ (DGFFSite (n - k)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (scaleEquiv hk)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (boxResidualInnerCLM n (boxInnerOuterEquiv n (scaleSites n z k)))

theorem tresCLM_apply {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k)
    (h : EuclideanSpace ℝ (DGFFSite n)) (c : DGFFSite (n - k)) :
    tresCLM hk h c = resid n (scaleSites n z k) h (shiftSite hk c) := by
  unfold tresCLM resid
  rw [dif_pos (shiftSite_mem hk c)]
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
    boxResidualInnerCLM_apply]
  rfl

 
theorem tres_law {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k) :
    (boxDGFF n).map (tresCLM hk) = boxDGFF (n - k) := by
  have hbase : IsGaussian (boxDGFF n) := by
    unfold boxDGFF WiredConductances.gaussianOfPrecision
    infer_instance
  have hbase' : IsGaussian (boxDGFF (n - k)) := by
    unfold boxDGFF WiredConductances.gaussianOfPrecision
    infer_instance
  letI := hbase
  letI := hbase'
  apply IsGaussian.ext
  · simp only [id]
    rw [(tresCLM hk).integral_id_map IsGaussian.integrable_id, boxDGFF_mean, boxDGFF_mean,
      map_zero]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis
    (EuclideanSpace.basisFun (DGFFSite (n - k)) ℝ).toBasis fun a b => ?_
  rw [ContinuousLinearMap.toBilinForm_apply,
    ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covarianceBilin_apply_eq_cov]
  · have hcoord (c : DGFFSite (n - k)) :
        (fun g : EuclideanSpace ℝ (DGFFSite (n - k)) =>
          inner ℝ ((EuclideanSpace.basisFun (DGFFSite (n - k)) ℝ).toBasis c) g) =
        (fun g => g c) := by
      ext g
      simp [PiLp.inner_apply]
    rw [hcoord a, hcoord b]
    rw [covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)]
    
    have hL : cov[fun h : EuclideanSpace ℝ (DGFFSite n) => tresCLM hk h a,
        fun h => tresCLM hk h b; boxDGFF n] =
        (Real.pi / 2) * green (interiorSites (n - k)) a.1 b.1 := by
      have e : ∀ c : DGFFSite (n - k), (fun h : EuclideanSpace ℝ (DGFFSite n) => tresCLM hk h c) =
          fun h => (boxResidualField n (boxInnerOuterEquiv n (scaleSites n z k)) h).1
            ⟨shiftSite hk c, shiftSite_mem hk c⟩ := by
        intro c; funext h; rw [tresCLM_apply]; unfold resid; rw [dif_pos (shiftSite_mem hk c)]
      rw [e a, e b, boxResidualField_inner_covariance, innerBlock_inv_eq_green]
      congr 1
      have hS : innerSet n (scaleSites n z k) = sqBox z (2 ^ (n - k)) :=
        innerSet_siteFilter hk.2
      rw [hS]
      have hsh := green_shift (interiorSites (n - k)) z a.1 b.1
      have hset : shiftSet (interiorSites (n - k)) z = sqBox z (2 ^ (n - k)) := by
        rw [interiorSites_eq_sqBox, shiftSet_sqBox, zero_add]
      rw [hset] at hsh
      exact hsh
    rw [hL]
    rw [boxDGFF_covariance, WiredConductances.algebraicGreen, precision_inv_eq_green]
    field_simp
  all_goals exact IsGaussian.memLp_two_id

 

theorem tres_prob {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k)
    {B : Set (EuclideanSpace ℝ (DGFFSite (n - k)))} (hB : MeasurableSet B) :
    boxDGFF n (tresCLM hk ⁻¹' B) = boxDGFF (n - k) B := by
  rw [← tres_law hk, Measure.map_apply (tresCLM hk).continuous.measurable hB]

 
theorem boxDGFF_map_neg (m : ℕ) : (boxDGFF m).map (fun g => -g) = boxDGFF m := by
  have hbase : IsGaussian (boxDGFF m) := by
    unfold boxDGFF WiredConductances.gaussianOfPrecision
    infer_instance
  letI := hbase
  set L : EuclideanSpace ℝ (DGFFSite m) →L[ℝ] EuclideanSpace ℝ (DGFFSite m) :=
    -(ContinuousLinearMap.id ℝ _)
  have hL : (fun g : EuclideanSpace ℝ (DGFFSite m) => -g) = ⇑L := by
    funext g; simp [L]
  rw [hL]
  apply IsGaussian.ext
  · simp only [id]
    rw [L.integral_id_map IsGaussian.integrable_id, boxDGFF_mean, map_zero]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis
    (EuclideanSpace.basisFun (DGFFSite m) ℝ).toBasis fun a b => ?_
  rw [ContinuousLinearMap.toBilinForm_apply,
    ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covarianceBilin_apply_eq_cov]
  · have hcoord (c : DGFFSite m) :
        (fun g : EuclideanSpace ℝ (DGFFSite m) =>
          inner ℝ ((EuclideanSpace.basisFun (DGFFSite m) ℝ).toBasis c) g) =
        (fun g => g c) := by
      ext g
      simp [PiLp.inner_apply]
    rw [hcoord a, hcoord b]
    rw [covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)]
    simp only [L, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, PiLp.neg_apply]
    rw [covariance_fun_neg_left, covariance_fun_neg_right, neg_neg]
  all_goals exact IsGaussian.memLp_two_id

 
theorem tres_prob_neg {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k)
    {B : Set (EuclideanSpace ℝ (DGFFSite (n - k)))} (hB : MeasurableSet B) :
    boxDGFF n ((fun h => -tresCLM hk h) ⁻¹' B) = boxDGFF (n - k) B := by
  have hmeas : Measurable fun g : EuclideanSpace ℝ (DGFFSite (n - k)) => -g := measurable_neg
  have hpre : (fun h => -tresCLM hk h) ⁻¹' B = tresCLM hk ⁻¹' ((fun g => -g) ⁻¹' B) := rfl
  rw [hpre, tres_prob hk (hmeas hB)]
  
  rw [← Measure.map_apply hmeas hB, boxDGFF_map_neg]

end SupercriticalLQGUniqueness.B2.QPos.P5
