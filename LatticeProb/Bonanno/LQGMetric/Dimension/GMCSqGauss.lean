/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCSqGauss at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqCov
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-!
# Independence of circle-average increments of the square GFF (P2-GMC, WP-24)

For `hX : IsZeroBoundaryGFFOn openSquare X P`, `U_t = h_r(t)`, `Δ_t = h_{r/2}(t) − h_r(t)`:

* `indepFun_incr_same` : `Δ_t ⟂ U_t`;
* `indepFun_incr_far` : `Δ_t ⟂ (U_t, U_u, Δ_u)` when `‖t − u‖ ≥ 2r`;
* `variance_incr` : `Var Δ_t = log 2`.

These are the Gaussian hypotheses of QZ's planar two-radius lemma (`TwoRadiusC.TRLHypC`), the
square analogue of QZ `AreaExist.indepFun_incr_bullet1_int`; they follow from the circle
covariances `circleCov_same`, `circleCov_far` (Duplantier–Sheffield arXiv:0808.1560 §3.1: the
circle-average process has independent increments in the radius) and mathlib's
`IsGaussianProcess.indepFun_of_covariance_eq_zero`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric QuantumZipper
open scoped ENNReal

namespace LQGMetric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- linear combinations `V (a s) − c s · V (b s)` of a Gaussian process form a Gaussian process -/
lemma isGaussianProcess_lincomb {T S : Type*} {V : T → Ω → ℝ} (hV : IsGaussianProcess V P)
    (a b : S → T) (c : S → ℝ) :
    IsGaussianProcess (fun s ω => V (a s) ω - c s * V (b s) ω) P := by
  classical
  refine hV.of_isGaussianProcess fun s => ⟨{a s, b s}, ?_, ?_⟩
  · exact ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({a s, b s} : Finset T) => ℝ)
        ⟨a s, by simp⟩ - c s • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : ({a s, b s} : Finset T) => ℝ) ⟨b s, by simp⟩
  · intro ω; simp [Finset.restrict]

/-- the admissible circle `∂B(t, r) ⊆ 𝕍` as an index of the GFF -/
def admC {t : ℂ} {r : ℝ} (hr : 0 < r) (hB : closedBall t r ⊆ openSquare) :
    {μ : Measure ℂ // IsAdmissibleDual openSquare (zeroSpace openSquare) μ} :=
  ⟨foldedCircle t r, isAdmissibleDual_openSquare_foldedCircle (inSq_of_closedBall hr hB) hr⟩

variable {X : Ω → Measure ℂ → ℝ}

lemma memLp_fc (hX : IsZeroBoundaryGFFOn openSquare X P) {t : ℂ} {r : ℝ} (hr : 0 < r)
    (hB : closedBall t r ⊆ openSquare) : MemLp (fun ω => X ω (foldedCircle t r)) 2 P :=
  (hX.gaussian.hasGaussianLaw_eval (admC hr hB)).memLp_two

/-- a circle with closed disc of radius `2r` around `t` inside `𝕍`: the data of one point -/
structure CircPt (t : ℂ) (r : ℝ) : Prop where
  pos : 0 < r
  ball : closedBall t r ⊆ openSquare

lemma CircPt.half {t : ℂ} {r : ℝ} (h : CircPt t r) : CircPt t (r / 2) :=
  ⟨by linarith [h.pos], (closedBall_subset_closedBall (by linarith [h.pos])).trans h.ball⟩

/-- the two-element family `[U_t, U_u, Δ_u]` and `Δ_t` as linear combinations -/
theorem indepFun_incr_far (hX : IsZeroBoundaryGFFOn openSquare X P) {t u : ℂ} {r : ℝ}
    (ht : CircPt t r) (hu : CircPt u r) (htu : 2 * r ≤ ‖t - u‖) :
    IndepFun (fun ω => X ω (foldedCircle t (r / 2)) - X ω (foldedCircle t r))
      (fun ω => (X ω (foldedCircle t r), X ω (foldedCircle u r),
        X ω (foldedCircle u (r / 2)) - X ω (foldedCircle u r))) P := by
  have hP := (hX.gaussian.hasGaussianLaw_eval (admC ht.pos ht.ball)).isProbabilityMeasure
  have hr := ht.pos
  set ct := admC ht.pos ht.ball
  set ct2 := admC ht.half.pos ht.half.ball
  set cu := admC hu.pos hu.ball
  set cu2 := admC hu.half.pos hu.half.ball
  let a : Unit ⊕ Fin 3 → _ := Sum.elim (fun _ => ct2) ![ct, cu, cu2]
  let b : Unit ⊕ Fin 3 → _ := Sum.elim (fun _ => ct) ![ct, cu, cu]
  let c : Unit ⊕ Fin 3 → ℝ := Sum.elim (fun _ => 1) ![0, 0, 1]
  have hG := isGaussianProcess_lincomb hX.gaussian a b c
  set V : Unit ⊕ Fin 3 → Ω → ℝ :=
    fun s ω => X ω (a s).1 - c s * X ω (b s).1
  have hG' : IsGaussianProcess (Sum.elim (fun (_ : Unit) => V (Sum.inl ()))
      (fun i => V (Sum.inr i))) P := by
    have e : Sum.elim (fun (_ : Unit) => V (Sum.inl ())) (fun i => V (Sum.inr i)) = V := by
      funext s; cases s <;> rfl
    rw [e]; exact hG
  have hmem : ∀ s, MemLp (V s) 2 P := fun s =>
    (hX.gaussian.hasGaussianLaw_eval (a s)).memLp_two.sub
      ((hX.gaussian.hasGaussianLaw_eval (b s)).memLp_two.const_mul _)
  have hmemX : ∀ p : {μ : Measure ℂ // IsAdmissibleDual openSquare (zeroSpace openSquare) μ},
      MemLp (fun ω => X ω p.1) 2 P := fun p => (hX.gaussian.hasGaussianLaw_eval p).memLp_two
  -- the covariance of `V s` and `V s'` in terms of the four circle covariances
  have hcov : ∀ s s', cov[V s, V s'; P] = cov[fun ω => X ω (a s).1, fun ω => X ω (a s').1; P]
      - c s' * cov[fun ω => X ω (a s).1, fun ω => X ω (b s').1; P]
      - c s * cov[fun ω => X ω (b s).1, fun ω => X ω (a s').1; P]
      + c s * c s' * cov[fun ω => X ω (b s).1, fun ω => X ω (b s').1; P] := by
    intro s s'
    simp only [V]
    rw [covariance_fun_sub_left (hmemX _) ((hmemX _).const_mul _) (hmem s'),
      covariance_const_mul_left, covariance_fun_sub_right (hmemX _) (hmemX _)
      ((hmemX _).const_mul _), covariance_fun_sub_right (hmemX _) (hmemX _)
      ((hmemX _).const_mul _), covariance_const_mul_right, covariance_const_mul_right]
    ring
  have hr2 : 0 < r / 2 := ht.half.pos
  have hfar : ∀ {ρ σ : ℝ}, 0 < ρ → ρ ≤ r → 0 < σ → σ ≤ r →
      cov[fun ω => X ω (foldedCircle t ρ), fun ω => X ω (foldedCircle u σ); P] =
        -Real.log ‖t - u‖ + hS t u := fun hρ hρr hσ hσr =>
    circleCov_far hX hρ hσ ((closedBall_subset_closedBall hρr).trans ht.ball)
      ((closedBall_subset_closedBall hσr).trans hu.ball) (by linarith)
  have hsame : ∀ {ρ σ : ℝ}, 0 < ρ → ρ ≤ r → 0 < σ → σ ≤ r →
      cov[fun ω => X ω (foldedCircle t ρ), fun ω => X ω (foldedCircle t σ); P] =
        -Real.log (max ρ σ) + hS t t := fun hρ hρr hσ hσr =>
    circleCov_same hX hρ hσ ((closedBall_subset_closedBall hρr).trans ht.ball)
      ((closedBall_subset_closedBall hσr).trans ht.ball)
  have hzero : ∀ (s : Unit) (i : Fin 3), cov[V (Sum.inl s), V (Sum.inr i); P] = 0 := by
    intro s i
    rw [hcov]
    have hh : r / 2 ≤ r := by linarith
    fin_cases i <;> simp only [a, b, c, ct, ct2, cu, cu2, admC, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.isValue, Fin.reduceFinMk]
    · rw [hsame hr2 hh hr le_rfl, hsame hr le_rfl hr le_rfl, max_eq_right hh, max_self]; ring
    · rw [hfar hr2 hh hr le_rfl, hfar hr le_rfl hr le_rfl]; ring
    · rw [hfar hr2 hh hr2 hh, hfar hr2 hh hr le_rfl, hfar hr le_rfl hr2 hh,
        hfar hr le_rfl hr le_rfl]; ring
  have hI := hG'.indepFun_of_covariance_eq_zero (fun _ => (hmem _).aemeasurable)
    (fun _ => (hmem _).aemeasurable) hzero
  have hφ : Measurable (fun v : Fin 3 → ℝ => (v 0, v 1, v 2)) :=
    (measurable_pi_apply 0).prodMk ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2))
  have hI2 := hI.comp (measurable_pi_apply ()) hφ
  refine hI2.congr (Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
  · simp [V, a, b, c, ct, ct2, admC]
  · simp [V, a, b, c, ct, cu, cu2, admC]

/-- `Δ_t ⟂ U_t` -/
theorem indepFun_incr_same (hX : IsZeroBoundaryGFFOn openSquare X P) {t : ℂ} {r : ℝ}
    (ht : CircPt t r) :
    IndepFun (fun ω => X ω (foldedCircle t (r / 2)) - X ω (foldedCircle t r))
      (fun ω => X ω (foldedCircle t r)) P := by
  have hP := (hX.gaussian.hasGaussianLaw_eval (admC ht.pos ht.ball)).isProbabilityMeasure
  have hr := ht.pos
  have hr2 : 0 < r / 2 := ht.half.pos
  set ct := admC ht.pos ht.ball
  set ct2 := admC ht.half.pos ht.half.ball
  let a : Unit ⊕ Unit → _ := Sum.elim (fun _ => ct2) (fun _ => ct)
  let c : Unit ⊕ Unit → ℝ := Sum.elim (fun _ => 1) (fun _ => 0)
  have hG := isGaussianProcess_lincomb hX.gaussian a (fun _ => ct) c
  set V : Unit ⊕ Unit → Ω → ℝ := fun s ω => X ω (a s).1 - c s * X ω ct.1
  have hG' : IsGaussianProcess (Sum.elim (fun (_ : Unit) => V (Sum.inl ()))
      (fun (_ : Unit) => V (Sum.inr ()))) P := by
    have e : Sum.elim (fun (_ : Unit) => V (Sum.inl ())) (fun (_ : Unit) => V (Sum.inr ())) = V := by
      funext s; cases s <;> rfl
    rw [e]; exact hG
  have hmemX : ∀ p : {μ : Measure ℂ // IsAdmissibleDual openSquare (zeroSpace openSquare) μ},
      MemLp (fun ω => X ω p.1) 2 P := fun p => (hX.gaussian.hasGaussianLaw_eval p).memLp_two
  have hmem : ∀ s, MemLp (V s) 2 P := fun s => (hmemX _).sub ((hmemX _).const_mul _)
  have hzero : ∀ (s s' : Unit), cov[V (Sum.inl s), V (Sum.inr s'); P] = 0 := by
    intro s s'
    simp only [V, a, c, Sum.elim_inl, Sum.elim_inr, one_mul, zero_mul, sub_zero]
    rw [covariance_fun_sub_left (hmemX _) (hmemX _) (hmemX _)]
    simp only [ct, ct2, admC]
    rw [circleCov_same hX hr2 hr ht.half.ball ht.ball, circleCov_same hX hr hr ht.ball ht.ball,
      max_eq_right (by linarith), max_self]
    ring
  have hI := hG'.indepFun_of_covariance_eq_zero (fun _ => (hmem _).aemeasurable)
    (fun _ => (hmem _).aemeasurable) hzero
  have hI2 := hI.comp (measurable_pi_apply ()) (measurable_pi_apply ())
  refine hI2.congr (Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
  · simp [V, a, c, ct, ct2, admC]
  · simp [V, a, c, ct, admC]

/-- `Var Δ_t = log 2` -/
theorem variance_incr (hX : IsZeroBoundaryGFFOn openSquare X P) {t : ℂ} {r : ℝ}
    (ht : CircPt t r) :
    Var[fun ω => X ω (foldedCircle t (r / 2)) - X ω (foldedCircle t r); P] = Real.log 2 := by
  have hP := (hX.gaussian.hasGaussianLaw_eval (admC ht.pos ht.ball)).isProbabilityMeasure
  have hr := ht.pos
  have hr2 : 0 < r / 2 := ht.half.pos
  rw [variance_fun_sub (memLp_fc hX hr2 ht.half.ball) (memLp_fc hX hr ht.ball),
    ← covariance_self (memLp_fc hX hr2 ht.half.ball).aemeasurable,
    ← covariance_self (memLp_fc hX hr ht.ball).aemeasurable,
    circleCov_same hX hr2 hr2 ht.half.ball ht.half.ball, circleCov_same hX hr hr ht.ball ht.ball,
    circleCov_same hX hr2 hr ht.half.ball ht.ball, max_self, max_self,
    max_eq_right (by linarith), Real.log_div hr.ne' two_ne_zero]
  ring

end LQGMetric
