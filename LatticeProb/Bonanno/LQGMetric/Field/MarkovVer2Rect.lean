/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovVer2Rect at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovVer2Riesz
import LatticeProb.Bonanno.LQGMetric.Field.ExistKolm
import LatticeProb.Bonanno.LQGMetric.Field.ExistRect

/-!
# The antiderivative field of the zero-boundary part and its continuous version (task P2-MKV)

For `V` open with `V ∩ ∂𝔻 = ∅` and the zero-boundary part `h̊` of a whole-plane GFF on `V`
(extended by zero, `MarkovExt.extVec`), the rectangle field
`F(x) = ⟨h̊, 1_V 1_{[0,x]}⟩` (`rectVec`, signed rectangle indicators `GFFExist.rectInd`) has
centred Gaussian increments with `Var(F(x) − F(x')) ≤ C_A ‖x − x'‖` on boxes
(`MarkovVer2.norm_rieszFun_sq_le` and `GFFExist.integral_abs_rectInd_sub_le`), so it has a
continuous modification (`exists_continuous_rectVec`, Kolmogorov–Čentsov
`GFFExist.exists_continuous_modification_of_gauss`).

Same construction as the whole-plane field of `ExistField`/`ExistGFF` (own elementary route,
see the P2-EXIST entry of `DEVIATIONS.md`); the published existence proofs of the GFF as a
random distribution (Sheffield math/0312099 §2; Berestycki–Powell arXiv:2404.16642 §1) use
Hilbert-space/Sobolev arguments instead.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric TopologicalSpace
open scoped ENNReal RealInnerProductSpace

namespace LQGMetric
namespace MarkovVer2

open MarkovGauss MarkovZB MarkovGerm MarkovExt GFFExist QuantumZipper QuantumZipper.K3

/-- `1_V 1_{[0,x]}` (signed rectangle) -/
def rectDens (V : Opens ℂ) (x : ℂ) : ℂ → ℝ := (V : Set ℂ).indicator (rectInd x)

lemma isBddDensOn_rectDens (V : Opens ℂ) {x : ℂ} {A : ℝ} (hA : |x.re| + |x.im| < A) :
    IsBddDensOn V A (rectDens V x) where
  meas := (measurable_rectInd x).indicator V.isOpen.measurableSet
  bdd := ⟨1, fun z => by
    unfold rectDens
    by_cases hz : z ∈ (V : Set ℂ)
    · rw [indicator_of_mem hz]; exact (rectInd_bddSupp x).bdd z
    · rw [indicator_of_notMem hz, abs_zero]; exact zero_le_one⟩
  ball z hz := by
    unfold rectDens
    have : |x.re| + |x.im| < ‖z‖ := hA.trans_le (by rwa [mem_ball, dist_zero_right, not_lt] at hz)
    by_cases hzV : z ∈ (V : Set ℂ)
    · rw [indicator_of_mem hzV]; exact (rectInd_bddSupp x).supp z this
    · exact indicator_of_notMem hzV _
  zero z hz := indicator_of_notMem hz _

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- `F(x) = [⟨h̊, 1_V 1_{[0,x]}⟩] ∈ L²(P)` -/
def rectVec (hh : IsWholePlaneGFF h P) (V : Opens ℂ) (x : ℂ) : Lp ℝ 2 P := extVec hh V (rectDens V x)

/-- a measurable representative of `rectVec` -/
def rectProc (hh : IsWholePlaneGFF h P) (V : Opens ℂ) (x : ℂ) : Ω → ℝ :=
  (Lp.aestronglyMeasurable (rectVec hh V x)).aemeasurable.mk _

lemma measurable_rectProc (hh : IsWholePlaneGFF h P) (V : Opens ℂ) (x : ℂ) :
    Measurable (rectProc hh V x) :=
  (Lp.aestronglyMeasurable _).aemeasurable.measurable_mk

lemma rectProc_ae (hh : IsWholePlaneGFF h P) (V : Opens ℂ) (x : ℂ) :
    rectProc hh V x =ᵐ[P] rectVec hh V x :=
  ((Lp.aestronglyMeasurable _).aemeasurable.ae_eq_mk).symm

/-- a centred Gaussian in `L²` has law `N(0, ‖u‖²)` -/
lemma map_eq_gaussianReal_norm {u : Lp ℝ 2 P} (hu : IsCGauss P u) :
    P.map (u : Ω → ℝ) = gaussianReal 0 (‖u‖ ^ 2).toNNReal := by
  obtain ⟨v, hv⟩ := hu.map_eq
  have hm : AEMeasurable (u : Ω → ℝ) P := (Lp.aestronglyMeasurable u).aemeasurable
  have h1 : Var[(u : Ω → ℝ); P] = v := by
    have := variance_map (X := id) (μ := P) (Y := (u : Ω → ℝ)) aemeasurable_id hm
    rw [hv, variance_id_gaussianReal] at this
    exact this.symm
  have h2 : Var[(u : Ω → ℝ); P] = ‖u‖ ^ 2 := by
    rw [← covariance_self hm, covariance_eq_inner u (Lp.memLp u) hu.2, Lp.toLp_coeFn,
      real_inner_self_eq_norm_sq]
  rw [hv]
  congr 1
  ext
  rw [Real.coe_toNNReal _ (sq_nonneg _), ← h2, h1]

lemma rectVec_sub (hh : IsWholePlaneGFF h P) {V : Opens ℂ} (hV : Disjoint (V : Set ℂ) (sphere 0 1))
    {x x' : ℂ} {A : ℝ} (hx : |x.re| + |x.im| < A) (hx' : |x'.re| + |x'.im| < A) :
    ‖rectVec hh V x - rectVec hh V x'‖ = ‖rieszFun V (rectDens V x - rectDens V x')‖ := by
  rw [rieszFun_sub hV (isBddDensOn_rectDens V hx) (isBddDensOn_rectDens V hx'), rectVec,
    rectVec, extVec, extVec, ← map_sub, LinearIsometry.norm_map]
  rfl

/-- `Var(F(x) − F(x')) ≤ 16π (2A+1)³ A ‖x − x'‖` on the box `[−A, A]²` -/
lemma sq_norm_rectVec_sub_le (hh : IsWholePlaneGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) {x x' : ℂ} {A : ℝ} (h0 : |x.re| ≤ A)
    (h1 : |x.im| ≤ A) (h2 : |x'.re| ≤ A) (h3 : |x'.im| ≤ A) :
    ‖rectVec hh V x - rectVec hh V x'‖ ^ 2 ≤
      2 * Real.pi * (2 * A + 1) ^ 3 * (2 * (4 * A * ‖x - x'‖)) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans h0
  have hx : |x.re| + |x.im| < 2 * A + 1 := by linarith
  have hx' : |x'.re| + |x'.im| < 2 * A + 1 := by linarith
  rw [rectVec_sub hh hV hx hx']
  refine (norm_rieszFun_sq_le hV (by linarith) ((isBddDensOn_rectDens V hx).sub
    (isBddDensOn_rectDens V hx'))).trans ?_
  have hint : Integrable fun u => |rectInd x u - rectInd x' u| :=
    (((rectInd_bddSupp x).integrable.sub (rectInd_bddSupp x').integrable)).abs
  have hpt : ∀ u, (rectDens V x - rectDens V x') u ^ 2 ≤ 2 * |rectInd x u - rectInd x' u| := by
    intro u
    have hb : |rectInd x u - rectInd x' u| ≤ 2 := (abs_sub _ _).trans (by
      linarith [(rectInd_bddSupp x).bdd u, (rectInd_bddSupp x').bdd u])
    simp only [Pi.sub_apply, rectDens]
    by_cases hu : u ∈ (V : Set ℂ)
    · rw [indicator_of_mem hu, indicator_of_mem hu, ← sq_abs]
      nlinarith [abs_nonneg (rectInd x u - rectInd x' u)]
    · rw [indicator_of_notMem hu, indicator_of_notMem hu]
      simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
  have hm : Measurable fun u => (rectDens V x - rectDens V x') u ^ 2 :=
    (((isBddDensOn_rectDens V hx).meas.sub (isBddDensOn_rectDens V hx').meas)).pow_const 2
  have hi2 : Integrable fun u => (rectDens V x - rectDens V x') u ^ 2 :=
    (hint.const_mul 2).mono' hm.aestronglyMeasurable (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt u)
  have hle : ∫ u, (rectDens V x - rectDens V x') u ^ 2 ≤ 2 * (4 * A * ‖x - x'‖) := by
    calc _ ≤ ∫ u, 2 * |rectInd x u - rectInd x' u| := integral_mono hi2 (hint.const_mul 2) hpt
      _ = 2 * ∫ u, |rectInd x u - rectInd x' u| := integral_const_mul _ _
      _ ≤ _ := by gcongr; exact integral_abs_rectInd_sub_le h1 h2
  have : 0 ≤ 2 * Real.pi * (2 * A + 1) ^ 3 := by positivity
  exact mul_le_mul_of_nonneg_left hle this

lemma hasLaw_rectProc_sub (hh : IsWholePlaneGFF h P) (V : Opens ℂ) (x x' : ℂ) :
    HasLaw (fun ω => rectProc hh V x ω - rectProc hh V x' ω)
      (gaussianReal 0 (‖rectVec hh V x - rectVec hh V x'‖ ^ 2).toNNReal) P := by
  set u := rectVec hh V x - rectVec hh V x'
  have hmem : u ∈ gaussSpace (pairProc h) (memLp_pair hh) :=
    sub_mem (extVec_mem_gaussSpace hh V _) (extVec_mem_gaussSpace hh V _)
  have hG := isCGauss_of_mem_gaussSpace (gaussian_pairProc hh) (centered_pairProc hh)
    (memLp_pair hh) hmem
  have hL : HasLaw (u : Ω → ℝ) (gaussianReal 0 (‖u‖ ^ 2).toNNReal) P :=
    ⟨(Lp.aestronglyMeasurable u).aemeasurable, map_eq_gaussianReal_norm hG⟩
  refine hL.congr ?_
  filter_upwards [rectProc_ae hh V x, rectProc_ae hh V x', Lp.coeFn_sub (rectVec hh V x)
    (rectVec hh V x')] with ω e1 e2 e3
  rw [e3, Pi.sub_apply, e1, e2]

/-- **Continuous version of the rectangle field of the zero-boundary part.** -/
theorem exists_continuous_rectVec (hh : IsWholePlaneGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ x, (fun ω => Y x ω) =ᵐ[P] rectVec hh V x := by
  have hv : ∀ A : ℝ, ∃ C, 0 ≤ C ∧ ∀ x x' : ℂ, |x.re| ≤ A → |x.im| ≤ A → |x'.re| ≤ A →
      |x'.im| ≤ A → ((‖rectVec hh V x - rectVec hh V x'‖ ^ 2).toNNReal : ℝ) ≤ C * ‖x - x'‖ := by
    intro A
    refine ⟨2 * Real.pi * (2 * |A| + 1) ^ 3 * (2 * (4 * |A|)), by positivity,
      fun x x' h0 h1 h2 h3 => ?_⟩
    have hA : 0 ≤ A := (abs_nonneg _).trans h0
    rw [Real.coe_toNNReal', max_le_iff]
    refine ⟨?_, by positivity⟩
    rw [abs_of_nonneg hA]
    calc _ ≤ 2 * Real.pi * (2 * A + 1) ^ 3 * (2 * (4 * A * ‖x - x'‖)) :=
          sq_norm_rectVec_sub_le hh hV h0 h1 h2 h3
      _ = _ := by ring
  obtain ⟨Y, hc, hm, hY⟩ := exists_continuous_modification_of_gauss
    (measurable_rectProc hh V) (fun x x' => (‖rectVec hh V x - rectVec hh V x'‖ ^ 2).toNNReal)
    (hasLaw_rectProc_sub hh V) hv
  exact ⟨Y, hc, hm, fun x => (hY x).trans (rectProc_ae hh V x)⟩

end MarkovVer2
end LQGMetric
