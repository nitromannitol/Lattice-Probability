/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127A1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSqStop
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Dynkin
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMMoments
import Mathlib.Analysis.InnerProductSpace.Laplacian

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 N1, part 1: the one-step Taylor estimate for planar Brownian motion (packet P-127A)

For a planar Brownian motion `B`, a bounded functional `ξ = F((B_{r_i})_i)` of the path at times
`r_i ≤ a`, and `g ∈ C³` with bounded `Dg`, `D²g` and Lipschitz `D²g`,

  `|E[ξ g(z + B_{a+h})] − E[ξ g(z + B_a)] − (h/2) E[ξ Δg(z + B_a)]| ≤ 8 C c₃ h^{3/2}`

(`HeatA.step_bound`), where `C` bounds the derivatives and `c₃ = E|N(0,1)|³`.

This is the planar version of the one-step estimate `QuantumZipper.Dynkin.step_expect` of QZ's
Dynkin formula (QZ `Proofs/ItoLite/Dynkin.lean`, which is for one real Brownian motion): the proof
copies its scheme (second-order Taylor expansion `QuantumZipper.Dynkin.taylor2_bound`,
independence of the increment `B_{a+h} − B_a` from the past (`KilledHeatSq.indepFun_past_inc`),
Gaussian moments `QuantumZipper.integral_abs_pow_le`). Used for Berestycki–Powell, *Gaussian
free field and Liouville quantum gravity* (arXiv:2404.16642), §1.5, Prop. 1.18
(`Δ G_D(x, ·) = −δ_x` for `G_D = π ∫ p_D`), in its probabilistic (Dynkin) form; see DEC-127 N1.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Laplacian
open scoped NNReal ENNReal

namespace LQGMetric
namespace CONF
namespace ZBM
namespace HeatA

open KilledHeat KilledHeatSq

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℂ} {P : Measure Ω}

/-! ### Gaussian moments of the increment -/

lemma integrable_abs_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) (gaussianReal 0 v) := by
  have hmem : MemLp (fun x : ℝ => x) (n : ℝ≥0) (gaussianReal 0 v) := memLp_id_gaussianReal n
  have hint : Integrable (fun x : ℝ => ‖x‖ ^ n) (gaussianReal 0 v) := hmem.integrable_norm_pow'
  simpa [Real.norm_eq_abs] using hint

/-- `E|V|ⁿ ≤ c_n v^{n/2}` for `V ∼ N(0, v)` (QZ `integral_abs_pow_le` through the law). -/
lemma integral_abs_pow_le_of_hasLaw {V : Ω → ℝ} {v : ℝ≥0} (hV : HasLaw V (gaussianReal 0 v) P)
    (n : ℕ) :
    ∫ ω, |V ω| ^ n ∂P ≤ QuantumZipper.gaussianAbsMoment n * (v : ℝ) ^ ((n : ℝ) / 2) := by
  have h1 : ∫ ω, |V ω| ^ n ∂P = ∫ x, |x| ^ n ∂(gaussianReal 0 v) := by
    have := hV.integral_comp (f := fun x : ℝ => |x| ^ n) (by fun_prop)
    simpa [Function.comp_def] using this
  have hW := QuantumZipper.hasLaw_gaussianReal isBrownianReal_stdBM.toIsPreBrownianReal v
  have h2 : ∫ ω, |stdBM v ω| ^ n ∂LQGDimension.ExistAsm.stdP = ∫ x, |x| ^ n ∂(gaussianReal 0 v) := by
    have := hW.integral_comp (f := fun x : ℝ => |x| ^ n) (by fun_prop)
    simpa [Function.comp_def] using this
  rw [h1, ← h2]
  exact QuantumZipper.integral_abs_pow_le isBrownianReal_stdBM.toIsPreBrownianReal v n

lemma integrable_abs_pow_of_hasLaw {V : Ω → ℝ} {v : ℝ≥0} (hV : HasLaw V (gaussianReal 0 v) P)
    (n : ℕ) : Integrable (fun ω => |V ω| ^ n) P := by
  have h := hV.integrable_comp (f := fun x : ℝ => |x| ^ n) (integrable_abs_pow_gaussianReal v n)
  simpa [Function.comp_def] using h

lemma hasLaw_incr (hB : IsPlanarBM B P) (a h : ℝ≥0) (b : Bool) :
    HasLaw (fun ω ↦ incVec B a (a + h) ω b) (gaussianReal 0 h) P := by
  have := hasLaw_inc hB ((le_self_add : a ≤ a + h)) b
  rwa [add_tsub_cancel_left] at this

lemma memLp_incr (hB : IsPlanarBM B P) (a h : ℝ≥0) (b : Bool) :
    MemLp (fun ω ↦ incVec B a (a + h) ω b) 2 P := by
  have hG0 := isGaussianProcess_past_inc hB (fun _ : Unit ↦ a) a (a + h)
  exact (hG0.hasGaussianLaw_eval (Sum.inr b)).memLp_two

lemma integral_incr (hB : IsPlanarBM B P) (a h : ℝ≥0) (b : Bool) :
    ∫ ω, incVec B a (a + h) ω b ∂P = 0 := by
  have := (hasLaw_incr hB a h b).integral_comp (f := fun x : ℝ => x) (by fun_prop)
  simp only [Function.comp_def] at this
  rw [this, integral_id_gaussianReal]

lemma integral_incr_mul (hB : IsPlanarBM B P) (a h : ℝ≥0) (b b' : Bool) :
    ∫ ω, incVec B a (a + h) ω b * incVec B a (a + h) ω b' ∂P = if b = b' then (h : ℝ) else 0 := by
  have hc := cov_inc_inc hB ((le_self_add : a ≤ a + h)) b b'
  rw [NNReal.coe_add, add_sub_cancel_left] at hc
  rw [← hc, covariance]
  simp only [integral_incr hB a h, sub_zero]

/-! ### Factorization against the past -/

variable {ι : Type*} [Countable ι]

lemma integral_past_mul_incr (hB : IsPlanarBM B P) {r : ι → ℝ≥0} {a : ℝ≥0} (hr : ∀ i, r i ≤ a)
    (h : ℝ≥0) {G : (Bool × ι → ℝ) → ℝ} (hG : Measurable G) (b : Bool) :
    ∫ ω, G (pastVec B r ω) * incVec B a (a + h) ω b ∂P = 0 := by
  rw [integral_past_mul_inc hB hr ((le_self_add : a ≤ a + h)) hG
    (H := fun d : Bool → ℝ ↦ d b) (measurable_pi_apply b), integral_incr hB a h b, mul_zero]

lemma integral_past_mul_incr_mul (hB : IsPlanarBM B P) {r : ι → ℝ≥0} {a : ℝ≥0}
    (hr : ∀ i, r i ≤ a) (h : ℝ≥0) {G : (Bool × ι → ℝ) → ℝ} (hG : Measurable G) (b b' : Bool) :
    ∫ ω, G (pastVec B r ω) * (incVec B a (a + h) ω b * incVec B a (a + h) ω b') ∂P =
      (∫ ω, G (pastVec B r ω) ∂P) * (if b = b' then (h : ℝ) else 0) := by
  rw [integral_past_mul_inc hB hr ((le_self_add : a ≤ a + h)) hG
    (H := fun d : Bool → ℝ ↦ d b * d b')
    ((measurable_pi_apply b).mul (measurable_pi_apply b')), integral_incr_mul hB a h b b']

/-! ### The one-step estimate -/

lemma toC_eq_smul (d : Bool → ℝ) : toC d = d false • (1 : ℂ) + d true • Complex.I := by
  simp [toC, Complex.real_smul]

lemma norm_toC_le (d : Bool → ℝ) : ‖toC d‖ ≤ |d false| + |d true| := by
  unfold toC
  refine (norm_add_le _ _).trans ?_
  simp [Complex.norm_real]

omit [Countable ι] in
lemma add_incr (B : ℝ≥0 → Ω → ℂ) (a h : ℝ≥0) (ω : Ω) :
    B (a + h) ω = B a ω + toC (incVec B a (a + h) ω) := by
  rw [← toC_coordProc B (a + h) ω, ← toC_coordProc B a ω]
  simp only [toC, incVec]
  push_cast
  ring

lemma cube_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg hx hy) (sq_nonneg (x - y))]

/-- **One-step estimate** (planar copy of `QuantumZipper.Dynkin.step_expect`). -/
theorem step_bound (hB : IsPlanarBM B P) {r : ι → ℝ≥0} {a : ℝ≥0} (hr : ∀ i, r i ≤ a) (h : ℝ≥0)
    {F : (Bool × ι → ℝ) → ℝ} (hF : Measurable F) (hFb : ∀ y, |F y| ≤ 1)
    {g : ℂ → ℝ} (hg : ContDiff ℝ 3 g) {C : ℝ} (hC : 0 ≤ C)
    (hg0 : ∀ x, |g x| ≤ C) (hD1 : ∀ x, ‖fderiv ℝ g x‖ ≤ C)
    (hD2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C)
    (hLip2 : ∀ x y, ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤ C * ‖x - y‖) (z : ℂ) :
    |∫ ω, F (pastVec B r ω) * g (z + B (a + h) ω) ∂P -
        ∫ ω, F (pastVec B r ω) * g (z + B a ω) ∂P -
        (h : ℝ) / 2 * ∫ ω, F (pastVec B r ω) * Δ g (z + B a ω) ∂P|
      ≤ 8 * C * QuantumZipper.gaussianAbsMoment 3 * ((h : ℝ) * Real.sqrt h) := by
  have := hB.gauss.isProbabilityMeasure
  classical
  set r' : Option ι → ℝ≥0 := fun o ↦ o.elim a r with hr'def
  have hr' : ∀ o, r' o ≤ a := fun o ↦ by cases o <;> simp [r', hr]
  set X : Ω → (Bool × Option ι → ℝ) := pastVec B r' with hX
  set Fp : (Bool × Option ι → ℝ) → ℝ := fun y ↦ F (fun p ↦ y (p.1, some p.2)) with hFp
  set Yp : (Bool × Option ι → ℝ) → ℂ := fun y ↦ z + toC (fun b ↦ y (b, none)) with hYp
  have hFpm : Measurable Fp := hF.comp (measurable_pi_iff.mpr fun p ↦ measurable_pi_apply _)
  have hYpm : Measurable Yp := measurable_const.add
    (measurable_toC.comp (measurable_pi_iff.mpr fun b ↦ measurable_pi_apply _))
  have hFX : ∀ ω, Fp (X ω) = F (pastVec B r ω) := fun ω ↦ rfl
  have hYX : ∀ ω, Yp (X ω) = z + B a ω := fun ω ↦ by
    simp only [Yp, X, pastVec, r', Option.elim]
    rw [toC_coordProc]
  set D : Ω → (Bool → ℝ) := incVec B a (a + h) with hDdef
  have hBD : ∀ ω, z + B (a + h) ω = Yp (X ω) + toC (D ω) := by
    intro ω; rw [hYX, add_incr B a h ω, add_assoc]
  have hXm : AEMeasurable X P := aemeasurable_pastVec hB r'
  have hDm : AEMeasurable D P := aemeasurable_incVec hB a (a + h)
  have hFb' : ∀ y, |Fp y| ≤ 1 := fun y ↦ hFb _
  -- derivatives
  set A := fderiv ℝ (fderiv ℝ g) with hAdef
  have hg1 : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hAc : Continuous A := (hg.fderiv_right (m := 2) (by norm_num)).continuous_fderiv
    (by norm_num)
  have hgm : Measurable g := hg.continuous.measurable
  have hg1m : ∀ v : ℂ, Measurable fun x ↦ fderiv ℝ g x v := fun v ↦
    (hg1.clm_apply continuous_const).measurable
  have hAm : ∀ v w : ℂ, Measurable fun x ↦ A x v w := fun v w ↦
    ((hAc.clm_apply continuous_const).clm_apply continuous_const).measurable
  have hg1b : ∀ x v, |fderiv ℝ g x v| ≤ C * ‖v‖ := fun x v ↦ by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ g x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hD1 x) (norm_nonneg _))
  have hAb : ∀ x v w, |A x v w| ≤ C * ‖v‖ * ‖w‖ := fun x v w ↦ by
    rw [← Real.norm_eq_abs]
    refine (QuantumZipper.Dynkin.norm_fderiv_fderiv_apply_le g x v w).trans ?_
    gcongr
    exact hD2 x
  -- integrability tools
  have hDi : ∀ b, Integrable (fun ω ↦ D ω b) P := fun b ↦ (memLp_incr hB a h b).integrable one_le_two
  have hDDi : ∀ b b', Integrable (fun ω ↦ D ω b * D ω b') P := fun b b' ↦
    (memLp_incr hB a h b).integrable_mul (memLp_incr hB a h b')
  have hint1 : ∀ (G : (Bool × Option ι → ℝ) → ℝ), Measurable G → ∀ c, (∀ y, |G y| ≤ c) →
      ∀ b, Integrable (fun ω ↦ G (X ω) * D ω b) P := fun G hG c hc b ↦
    (hDi b).bdd_mul (hG.comp_aemeasurable hXm).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hc _)
  have hint2 : ∀ (G : (Bool × Option ι → ℝ) → ℝ), Measurable G → ∀ c, (∀ y, |G y| ≤ c) →
      ∀ b b', Integrable (fun ω ↦ G (X ω) * (D ω b * D ω b')) P := fun G hG c hc b b' ↦
    (hDDi b b').bdd_mul (hG.comp_aemeasurable hXm).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hc _)
  have hFg : ∀ v, ∀ y, |Fp y * fderiv ℝ g (Yp y) v| ≤ C * ‖v‖ := fun v y ↦ by
    rw [abs_mul]
    calc |Fp y| * |fderiv ℝ g (Yp y) v| ≤ 1 * (C * ‖v‖) :=
          mul_le_mul (hFb' y) (hg1b _ v) (abs_nonneg _) zero_le_one
      _ = C * ‖v‖ := one_mul _
  have hFA : ∀ v w, ∀ y, |Fp y * A (Yp y) v w| ≤ C * ‖v‖ * ‖w‖ := fun v w y ↦ by
    rw [abs_mul]
    calc |Fp y| * |A (Yp y) v w| ≤ 1 * (C * ‖v‖ * ‖w‖) :=
          mul_le_mul (hFb' y) (hAb _ v w) (abs_nonneg _) zero_le_one
      _ = C * ‖v‖ * ‖w‖ := one_mul _
  have hFgm : ∀ v, Measurable fun y ↦ Fp y * fderiv ℝ g (Yp y) v := fun v ↦
    hFpm.mul ((hg1m v).comp hYpm)
  have hFAm : ∀ v w, Measurable fun y ↦ Fp y * A (Yp y) v w := fun v w ↦
    hFpm.mul ((hAm v w).comp hYpm)
  -- first order term vanishes
  have hT1 : ∫ ω, Fp (X ω) * fderiv ℝ g (Yp (X ω)) (toC (D ω)) ∂P = 0 := by
    have e : ∀ ω, Fp (X ω) * fderiv ℝ g (Yp (X ω)) (toC (D ω)) =
        (Fp (X ω) * fderiv ℝ g (Yp (X ω)) 1) * D ω false +
          (Fp (X ω) * fderiv ℝ g (Yp (X ω)) Complex.I) * D ω true := by
      intro ω
      rw [toC_eq_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      ring
    simp_rw [e]
    refine (integral_add (hint1 _ (hFgm 1) _ (hFg 1) false)
      (hint1 _ (hFgm Complex.I) _ (hFg _) true)).trans ?_
    rw [integral_past_mul_incr hB hr' h (hFgm 1) false,
      integral_past_mul_incr hB hr' h (hFgm _) true, add_zero]
  -- second order term
  have hT2 : ∫ ω, Fp (X ω) * A (Yp (X ω)) (toC (D ω)) (toC (D ω)) ∂P =
      (h : ℝ) * ∫ ω, Fp (X ω) * Δ g (Yp (X ω)) ∂P := by
    have e : ∀ ω, Fp (X ω) * A (Yp (X ω)) (toC (D ω)) (toC (D ω)) =
        (Fp (X ω) * A (Yp (X ω)) 1 1) * (D ω false * D ω false) +
        (Fp (X ω) * A (Yp (X ω)) 1 Complex.I) * (D ω false * D ω true) +
        (Fp (X ω) * A (Yp (X ω)) Complex.I 1) * (D ω true * D ω false) +
        (Fp (X ω) * A (Yp (X ω)) Complex.I Complex.I) * (D ω true * D ω true) := by
      intro ω
      rw [toC_eq_smul]
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    simp_rw [e]
    have i1 := hint2 _ (hFAm 1 1) _ (hFA 1 1) false false
    have i2 := hint2 _ (hFAm 1 Complex.I) _ (hFA 1 Complex.I) false true
    have i3 := hint2 _ (hFAm Complex.I 1) _ (hFA Complex.I 1) true false
    have i4 := hint2 _ (hFAm Complex.I Complex.I) _ (hFA Complex.I Complex.I) true true
    have k3 := integral_add ((i1.add i2).add i3) i4
    have k2 := integral_add (i1.add i2) i3
    have k1 := integral_add i1 i2
    simp only [Pi.add_apply] at k1 k2 k3
    rw [k3, k2, k1,
      integral_past_mul_incr_mul hB hr' h (hFAm 1 1),
      integral_past_mul_incr_mul hB hr' h (hFAm _ _),
      integral_past_mul_incr_mul hB hr' h (hFAm _ _),
      integral_past_mul_incr_mul hB hr' h (hFAm _ _)]
    simp only [ite_true, Bool.false_eq_true, ite_false, Bool.true_eq_false, mul_zero, add_zero]
    have hlap : ∀ x, Δ g x = A x 1 1 + A x Complex.I Complex.I := fun x ↦ by
      simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
        QuantumZipper.Dynkin.iteratedFDeriv_two_vec, hAdef]
    have j : ∀ v w : ℂ, Integrable (fun ω ↦ Fp (X ω) * A (Yp (X ω)) v w) P := fun v w ↦
      (integrable_const (C * ‖v‖ * ‖w‖)).mono' ((hFAm v w).comp_aemeasurable hXm).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hFA v w (X ω))
    simp_rw [hlap, mul_add]
    rw [integral_add (j 1 1) (j Complex.I Complex.I)]
    ring
  -- integrability of the two Taylor terms
  have iT1 : Integrable (fun ω ↦ Fp (X ω) * fderiv ℝ g (Yp (X ω)) (toC (D ω))) P := by
    refine ((hint1 _ (hFgm 1) _ (hFg 1) false).add
      (hint1 _ (hFgm Complex.I) _ (hFg _) true)).congr (ae_of_all _ fun ω ↦ ?_)
    simp only [Pi.add_apply]
    rw [toC_eq_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have iT2 : Integrable (fun ω ↦ Fp (X ω) * A (Yp (X ω)) (toC (D ω)) (toC (D ω))) P := by
    refine ((((hint2 _ (hFAm 1 1) _ (hFA 1 1) false false).add
      (hint2 _ (hFAm 1 Complex.I) _ (hFA 1 Complex.I) false true)).add
      (hint2 _ (hFAm Complex.I 1) _ (hFA Complex.I 1) true false)).add
      (hint2 _ (hFAm Complex.I Complex.I) _ (hFA Complex.I Complex.I) true true)).congr
      (ae_of_all _ fun ω ↦ ?_)
    simp only [Pi.add_apply]
    rw [toC_eq_smul]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  -- remainder
  set R : Ω → ℝ := fun ω ↦ g (Yp (X ω) + toC (D ω)) - g (Yp (X ω)) -
      fderiv ℝ g (Yp (X ω)) (toC (D ω)) - 1 / 2 * A (Yp (X ω)) (toC (D ω)) (toC (D ω)) with hR
  have hRb : ∀ ω, |R ω| ≤ C * (4 * (|D ω false| ^ 3 + |D ω true| ^ 3)) := by
    intro ω
    have ht := QuantumZipper.Dynkin.taylor2_bound hg hC hLip2 (Yp (X ω)) (toC (D ω))
    rw [QuantumZipper.Dynkin.iteratedFDeriv_two_vec] at ht
    refine ht.trans (mul_le_mul_of_nonneg_left ?_ hC)
    calc ‖toC (D ω)‖ ^ 3 ≤ (|D ω false| + |D ω true|) ^ 3 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_toC_le _) 3
      _ ≤ _ := cube_add_le (abs_nonneg _) (abs_nonneg _)
  have hcube : ∀ b, Integrable (fun ω ↦ |D ω b| ^ 3) P := fun b ↦
    integrable_abs_pow_of_hasLaw (hasLaw_incr hB a h b) 3
  have hdom : Integrable (fun ω ↦ C * (4 * (|D ω false| ^ 3 + |D ω true| ^ 3))) P :=
    (((hcube false).add (hcube true)).const_mul 4).const_mul C
  have hYm : AEMeasurable (fun ω ↦ Yp (X ω)) P := hYpm.comp_aemeasurable hXm
  have hTm : AEMeasurable (fun ω ↦ toC (D ω)) P := measurable_toC.comp_aemeasurable hDm
  have hRm : AEStronglyMeasurable R P := by
    have c1 : Continuous fun p : ℂ × ℂ ↦ fderiv ℝ g p.1 p.2 :=
      (hg1.comp continuous_fst).clm_apply continuous_snd
    have c2 : Continuous fun p : ℂ × ℂ ↦ A p.1 p.2 p.2 :=
      ((hAc.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
    refine (((((hgm.comp_aemeasurable (hYm.add hTm)).sub (hgm.comp_aemeasurable hYm)).sub
      (c1.measurable.comp_aemeasurable (hYm.prodMk hTm))).sub
      ((c2.measurable.comp_aemeasurable (hYm.prodMk hTm)).const_mul _))).aestronglyMeasurable
  have hFXm : AEStronglyMeasurable (fun ω ↦ Fp (X ω)) P :=
    (hFpm.comp_aemeasurable hXm).aestronglyMeasurable
  have iR : Integrable (fun ω ↦ Fp (X ω) * R ω) P := by
    refine hdom.mono' (hFXm.mul hRm) (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |Fp (X ω)| * |R ω| ≤ 1 * |R ω| :=
          mul_le_mul_of_nonneg_right (hFb' _) (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hRb ω
  have ibdd : ∀ Y : Ω → ℂ, AEMeasurable Y P →
      Integrable (fun ω ↦ Fp (X ω) * g (Y ω)) P := fun Y hY ↦ by
    refine (integrable_const C).mono' (hFXm.mul (hgm.comp_aemeasurable hY).aestronglyMeasurable)
      (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |Fp (X ω)| * |g (Y ω)| ≤ 1 * C := mul_le_mul (hFb' _) (hg0 _) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have eI1 : ∫ ω, F (pastVec B r ω) * g (z + B (a + h) ω) ∂P =
      ∫ ω, Fp (X ω) * g (Yp (X ω) + toC (D ω)) ∂P :=
    integral_congr_ae (ae_of_all _ fun ω ↦ by simp only [hBD]; rfl)
  have eI0 : ∫ ω, F (pastVec B r ω) * g (z + B a ω) ∂P = ∫ ω, Fp (X ω) * g (Yp (X ω)) ∂P :=
    integral_congr_ae (ae_of_all _ fun ω ↦ by simp only [hYX]; rfl)
  have eJ : ∫ ω, F (pastVec B r ω) * Δ g (z + B a ω) ∂P =
      ∫ ω, Fp (X ω) * Δ g (Yp (X ω)) ∂P :=
    integral_congr_ae (ae_of_all _ fun ω ↦ by simp only [hYX]; rfl)
  have hsplit : ∫ ω, Fp (X ω) * g (Yp (X ω) + toC (D ω)) ∂P - ∫ ω, Fp (X ω) * g (Yp (X ω)) ∂P =
      ∫ ω, Fp (X ω) * fderiv ℝ g (Yp (X ω)) (toC (D ω)) ∂P +
        1 / 2 * ∫ ω, Fp (X ω) * A (Yp (X ω)) (toC (D ω)) (toC (D ω)) ∂P +
        ∫ ω, Fp (X ω) * R ω ∂P := by
    have i1 : Integrable (fun ω ↦ Fp (X ω) * g (Yp (X ω) + toC (D ω))) P := ibdd _ (hYm.add hTm)
    have i0 : Integrable (fun ω ↦ Fp (X ω) * g (Yp (X ω))) P := ibdd _ hYm
    have i12 : Integrable (fun ω ↦ Fp (X ω) * fderiv ℝ g (Yp (X ω)) (toC (D ω)) +
        1 / 2 * (Fp (X ω) * A (Yp (X ω)) (toC (D ω)) (toC (D ω)))) P := iT1.add (iT2.const_mul _)
    rw [← integral_sub i1 i0, ← integral_const_mul,
      ← integral_add iT1 (iT2.const_mul _), ← integral_add i12 iR]
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    simp only [hR]
    ring
  rw [eI1, eI0, eJ, hsplit, hT1, hT2]
  have hfin : |∫ ω, Fp (X ω) * R ω ∂P| ≤
      8 * C * QuantumZipper.gaussianAbsMoment 3 * ((h : ℝ) * Real.sqrt h) := by
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono iR.abs hdom fun ω ↦ ?_).trans ?_
    · rw [abs_mul]
      calc |Fp (X ω)| * |R ω| ≤ 1 * |R ω| :=
            mul_le_mul_of_nonneg_right (hFb' _) (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hRb ω
    · rw [integral_const_mul, integral_const_mul, integral_add (hcube false) (hcube true)]
      have h3 : ∀ b, ∫ ω, |D ω b| ^ 3 ∂P ≤
          QuantumZipper.gaussianAbsMoment 3 * ((h : ℝ) * Real.sqrt h) := fun b ↦ by
        have := integral_abs_pow_le_of_hasLaw (hasLaw_incr hB a h b) 3
        rwa [QuantumZipper.Dynkin.rpow_three_halves_eq (NNReal.coe_nonneg h)] at this
      have := add_le_add (h3 false) (h3 true)
      nlinarith
  have e0 : (0 : ℝ) + 1 / 2 * ((h : ℝ) * ∫ ω, Fp (X ω) * Δ g (Yp (X ω)) ∂P) +
      ∫ ω, Fp (X ω) * R ω ∂P - (h : ℝ) / 2 * ∫ ω, Fp (X ω) * Δ g (Yp (X ω)) ∂P =
      ∫ ω, Fp (X ω) * R ω ∂P := by ring
  rw [e0]
  exact hfin

end HeatA
end ZBM
end CONF
end LQGMetric
