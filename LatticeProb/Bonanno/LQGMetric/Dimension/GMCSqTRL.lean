/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCSqTRL at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqReg
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqGauss
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMoment
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistence

/-!
# The planar two-radius lemma for the zero-boundary GFF on the unit square (P2-GMC, WP-24)

Instantiation of QZ's `TwoRadiusC.TRLHypC` (QZ `Proofs/LQG/AreaExistenceTRL.lean`) for the
square field: `U_t = h_{2^{-k}}(t)` (QZ's regularized `avgReg`), `Δ_t = h_{2^{-k-1}}(t) − U_t`,
on regions `S ⊆ sqIn s` with `4 · 2^{-k} ≤ s` (`trlHypC_sq`), and the resulting bound on
`E|∫ f dμ_k − ∫ f dμ_{k+1}|` (`integral_abs_areaApprox_step_le_sq`). This is the square
analogue of QZ `AreaExist.trlHypC_field` / `integral_abs_areaApprox_step_le` (template, same
proof); the Gaussian inputs are `GMCSqGauss.lean`, `GMCSqReg.lean`.

Mathematical source of the two-radius argument: QZ blueprint M4-A1 (the area analogue of the
boundary-measure two-radius lemma); the GMC existence it gives is DS Prop. 1.1
(arXiv:0808.1560, a.s. weak limit along dyadic radii) for the zero-boundary GFF on `𝕍`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric QuantumZipper Real
open scoped ENNReal NNReal

namespace LQGMetric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

/-- coarse coordinate `U_t = h_{2^{-k}}(t)` -/
def sU (X : Ω → Measure ℂ → ℝ) (k : ℕ) (t : ℂ) (ω : Ω) : ℝ := avgReg (X ω) k t

/-- increment `Δ_t = h_{2^{-k-1}}(t) − h_{2^{-k}}(t)` -/
def sΔ (X : Ω → Measure ℂ → ℝ) (k : ℕ) (t : ℂ) (ω : Ω) : ℝ := sU X (k + 1) t ω - sU X k t ω

/-- the variance of `U_t` -/
def sV (k : ℕ) (t : ℂ) : ℝ≥0 :=
  ((dualNormSq openSquare (zeroSpace openSquare) (foldedCircle t (radius k))).toReal).toNNReal

lemma closedBall_subset_of_sqIn {s ρ : ℝ} {t : ℂ} (ht : t ∈ sqIn s) (hρ : ρ < s) :
    closedBall t ρ ⊆ openSquare := by
  intro x hx
  rw [mem_closedBall, Complex.dist_eq] at hx
  have h1 := (Complex.abs_re_le_norm (x - t)).trans hx
  have h2 := (Complex.abs_im_le_norm (x - t)).trans hx
  rw [Complex.sub_re] at h1; rw [Complex.sub_im] at h2
  obtain ⟨a, b, c, d⟩ := ht
  have := abs_le.mp h1; have := abs_le.mp h2
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma measurable_sU (hX : IsZeroBoundaryGFFOn openSquare X P) (k : ℕ) :
    Measurable fun p : ℂ × Ω => sU X k p.1 p.2 :=
  (measurable_avgReg k).comp (((measurable_field hX).comp measurable_snd).prodMk measurable_fst)

/-- the law of a circle average -/
lemma hasLaw_fc (hX : IsZeroBoundaryGFFOn openSquare X P) {t : ℂ} {r : ℝ} (hr : 0 < r)
    (hB : closedBall t r ⊆ openSquare) :
    HasLaw (fun ω => X ω (foldedCircle t r)) (gaussianReal 0
      ((dualNormSq openSquare (zeroSpace openSquare) (foldedCircle t r)).toReal).toNNReal) P := by
  have hadm := isAdmissibleDual_openSquare_foldedCircle (inSq_of_closedBall hr hB) hr
  have hG : HasGaussianLaw (fun ω => X ω (foldedCircle t r)) P :=
    hX.gaussian.hasGaussianLaw_eval ⟨_, hadm⟩
  have hm : AEMeasurable (fun ω => X ω (foldedCircle t r)) P :=
    (hX.measurable_coord _).aemeasurable
  refine ⟨hm, ?_⟩
  rw [hG.map_eq_gaussianReal, ← covariance_self hm, hX.covariance_eq _ _ hadm hadm,
    dualCov_self_eq]
  congr 1
  exact hX.centered _ hadm

lemma radius_succ' (k : ℕ) : radius (k + 1) = radius k / 2 := AreaExist.aradius_succ k

/-- **Instantiation of `TRLHypC`** for the square field -/
theorem trlHypC_sq (hX : IsZeroBoundaryGFFOn openSquare X P) {s : ℝ} {S : Set ℂ}
    (hS : S ⊆ sqIn s) {k : ℕ} (hk : 4 * radius k ≤ s) :
    TwoRadiusC.TRLHypC P S (2 * radius k) (Real.log 3) (Real.log 2)
      (fun _ => 1 / 2 * Real.log (1 / radius k)) (sV k) (fun _ => (Real.log 2).toNNReal)
      (sU X k) (sΔ X k) := by
  set r := radius k
  have hr : 0 < r := radius_pos k
  have hr1 : r ≤ 1 := radius_le_one k
  have hball : ∀ t ∈ S, closedBall t (2 * r) ⊆ openSquare := fun t ht =>
    closedBall_subset_of_sqIn (hS ht) (by linarith)
  have hball1 : ∀ t ∈ S, closedBall t r ⊆ openSquare := fun t ht =>
    (closedBall_subset_closedBall (by linarith)).trans (hball t ht)
  have hcp : ∀ t ∈ S, CircPt t r := fun t ht => ⟨hr, hball1 t ht⟩
  have hUe : ∀ t ∈ S, sU X k t =ᵐ[P] fun ω => X ω (foldedCircle t r) := fun t ht =>
    avgReg_ae_eq hX (hball t ht)
  have hUe1 : ∀ t ∈ S, sU X (k + 1) t =ᵐ[P] fun ω => X ω (foldedCircle t (r / 2)) := by
    intro t ht
    have h := avgReg_ae_eq (k := k + 1) hX ((closedBall_subset_closedBall (by
      rw [radius_succ']; linarith)).trans (hball t ht))
    rwa [radius_succ'] at h
  have hΔe : ∀ t ∈ S, sΔ X k t =ᵐ[P]
      fun ω => X ω (foldedCircle t (r / 2)) - X ω (foldedCircle t r) := by
    intro t ht
    filter_upwards [hUe1 t ht, hUe t ht] with ω h1 h2
    simp only [sΔ, h1, h2]
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  refine
    { measU := measurable_sU hX k
      measΔ := (measurable_sU hX (k + 1)).sub (measurable_sU hX k)
      measL := measurable_const
      measw := measurable_const
      lawU := fun t ht => (hasLaw_fc hX hr (hball1 t ht)).congr (hUe t ht)
      lawΔ := ?_, varU := ?_, varΔ := ?_, indep := ?_, decor := ?_ }
  · intro t ht
    have hc := hcp t ht
    have hadm1 := isAdmissibleDual_openSquare_foldedCircle (inSq_of_closedBall hc.half.pos
      hc.half.ball) hc.half.pos
    have hadm := isAdmissibleDual_openSquare_foldedCircle (inSq_of_closedBall hr hc.ball) hr
    have hG : HasGaussianLaw
        (fun ω => X ω (foldedCircle t (r / 2)) - X ω (foldedCircle t r)) P :=
      hX.gaussian.hasGaussianLaw_fun_sub (s := ⟨_, hadm1⟩) (t := ⟨_, hadm⟩)
    have hm : AEMeasurable
        (fun ω => X ω (foldedCircle t (r / 2)) - X ω (foldedCircle t r)) P :=
      ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
    have hP := hG.isProbabilityMeasure
    have hmean : P[fun ω => X ω (foldedCircle t (r / 2)) - X ω (foldedCircle t r)] = 0 := by
      show ∫ ω, (X ω (foldedCircle t (r / 2)) - X ω (foldedCircle t r)) ∂P = 0
      rw [integral_sub ((memLp_fc hX hc.half.pos hc.half.ball).integrable one_le_two)
        ((memLp_fc hX hr hc.ball).integrable one_le_two), hX.centered _ hadm1,
        hX.centered _ hadm, sub_zero]
    refine HasLaw.congr ⟨hm, ?_⟩ (hΔe t ht)
    rw [hG.map_eq_gaussianReal, hmean, ← covariance_self hm, covariance_self hm,
      variance_incr hX hc]
  · intro t ht
    have hc := hcp t ht
    show ((sV k t : ℝ)) ≤ 2 * (1 / 2 * Real.log (1 / r)) + Real.log 3
    have h := dualNormSq_openSquare_foldedCircle_le (inSq_of_closedBall hr hc.ball) hr
    have h3r : 0 ≤ Real.log (3 / r) := Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
    have := ENNReal.toReal_le_of_le_ofReal h3r h
    rw [sV, Real.coe_toNNReal _ ENNReal.toReal_nonneg]
    rw [Real.log_div (by norm_num) hr.ne'] at this
    have e : (dualNormSq openSquare (zeroSpace openSquare) (foldedCircle t (radius k))).toReal ≤
        Real.log 3 - Real.log r := this
    have e2 : Real.log (1 / r) = -Real.log r := by rw [one_div, Real.log_inv]
    rw [e2]
    linarith
  · intro t _
    exact (Real.coe_toNNReal _ hlog2).le
  · intro t ht
    exact (indepFun_incr_same hX (hcp t ht)).congr (hΔe t ht).symm (hUe t ht).symm
  · intro t ht u hu htu
    refine (indepFun_incr_far hX (hcp t ht) (hcp u hu) htu).congr (hΔe t ht).symm ?_
    filter_upwards [hUe t ht, hUe u hu, hΔe u hu] with ω h1 h2 h3
    simp [h1, h2, h3]

end LQGMetric
