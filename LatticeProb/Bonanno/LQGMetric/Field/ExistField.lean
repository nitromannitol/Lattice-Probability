/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ExistField at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ExistRect
import LatticeProb.Bonanno.LQGMetric.Field.ExistKolm

/-!
# The antiderivative field `F(x) = W(kerFun 1_{[0,x]})` and its continuous version (P2-EXIST)

* `kerFun_sub`: linearity of `g ↦ kerFun g`;
* `integral_sq_kerFun_rect_sub_le`: `‖kerFun 1_{[0,x]} − kerFun 1_{[0,x']}‖² ≤ C_A ‖x − x'‖`;
* `rectL2 x ∈ L²(ℝ × ℂ)`, `rectField W x = W(rectL2 x)`;
* `exists_continuous_rectField`: a modification `Y` of `rectField W` continuous for every `ω`
  (Kolmogorov–Čentsov, `exists_continuous_modification_of_gauss`).

Own elementary proofs (the published constructions of the GFF as a random distribution —
Sheffield math/0312099 §2, Berestycki–Powell arXiv:2404.16642 ch. 1 — use Hilbert-space /
Bochner–Minlos arguments instead; see the P2-EXIST report and DEVIATIONS).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace

namespace LQGMetric
namespace GFFExist

open WhiteNoise

variable {g g' : ℂ → ℝ} {M M' R R' : ℝ}

lemma BddSupp.sub (hg : BddSupp g M R) (hg' : BddSupp g' M' R') :
    BddSupp (fun u => g u - g' u) (M + M') (max R R') where
  meas := hg.meas.sub hg'.meas
  bdd u := (abs_sub _ _).trans (add_le_add (hg.bdd u) (hg'.bdd u))
  supp u hu := by
    rw [hg.supp u ((le_max_left _ _).trans_lt hu), hg'.supp u ((le_max_right _ _).trans_lt hu),
      sub_zero]

lemma BddSupp.integrable_mul_heat_sub (hg : BddSupp g M R) {s : ℝ} (hs : 0 < s) (y : ℂ)
    (K : ℝ) : Integrable fun u => g u * (heatKernel s u y - K) := by
  have := hg.integrable_mul_bdd (f := fun u => heatKernel s u y - K)
    (by unfold heatKernel; fun_prop) (K := (2 * Real.pi * s)⁻¹ + |K|) (fun u _ => by
      refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
      rw [abs_of_nonneg (heatKernel_nonneg _ hs.le _ _)]; exact heatKernel_le s hs u y)
  exact this.congr (Eventually.of_forall fun u => mul_comm _ _)

lemma kerFun_sub (hg : BddSupp g M R) (hg' : BddSupp g' M' R') (q : ℝ × ℂ) :
    kerFun (fun u => g u - g' u) q = kerFun g q - kerFun g' q := by
  unfold kerFun
  by_cases ht : q.1 ∈ Ioi (0 : ℝ)
  · simp only [indicator_of_mem ht]
    rw [← mul_sub]; congr 1
    unfold kerInner
    have hs : 0 < q.1 / 2 := by have : 0 < q.1 := ht; linarith
    rw [← integral_sub (hg.integrable_mul_heat_sub hs _ _) (hg'.integrable_mul_heat_sub hs _ _)]
    congr 1; funext u; ring
  · simp [indicator_of_notMem ht]

/-- **Increment bound** for the rectangle kernels. -/
theorem integral_sq_kerFun_rect_sub_le {x x' : ℂ} {A : ℝ} (h0 : |x.re| ≤ A) (h1 : |x.im| ≤ A)
    (h2 : |x'.re| ≤ A) (h3 : |x'.im| ≤ A) :
    ∫ q, kerFun (fun u => rectInd x u - rectInd x' u) q ^ 2 ≤
      (2 * Real.pi + 32 * A ^ 4) * (4 * A * ‖x - x'‖) := by
  have hA : 0 ≤ A := (abs_nonneg _).trans h0
  set g : ℂ → ℝ := fun u => rectInd x u - rectInd x' u with hgdef
  have hg := (rectInd_bddSupp x).sub (rectInd_bddSupp x')
  have hb := hg.memLp_kerFun.2
  set I := ∫ u, |g u| with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => abs_nonneg _
  have hI1 : I ≤ 4 * A * ‖x - x'‖ := integral_abs_rectInd_sub_le h1 h2
  have hnx : ‖x‖ ≤ 2 * A := (Complex.norm_le_abs_re_add_abs_im x).trans (by linarith)
  have hnx' : ‖x'‖ ≤ 2 * A := (Complex.norm_le_abs_re_add_abs_im x').trans (by linarith)
  have hd : ‖x - x'‖ ≤ 4 * A := (norm_sub_le _ _).trans (by linarith)
  have hI2 : I ≤ 16 * A ^ 2 := hI1.trans (by nlinarith)
  have hgi := hg.integrable
  have hgb : ∀ u, |g u| ≤ 2 := fun u => by have := hg.bdd u; norm_num at this; linarith
  have hg2 : Integrable fun u => g u ^ 2 := by
    have := hg.integrable_mul_bdd hg.meas (K := 1 + 1) (fun u _ => hg.bdd u)
    simpa [sq] using this
  have hsq : ∫ u, g u ^ 2 ≤ 2 * I := by
    rw [hI, ← integral_const_mul]
    refine integral_mono hg2 (hgi.abs.const_mul _) fun u => ?_
    have := hgb u
    rw [← sq_abs]; nlinarith [abs_nonneg (g u)]
  have hR0 : max (|x.re| + |x.im|) (|x'.re| + |x'.im|) ≤ 2 * A := max_le (by linarith) (by linarith)
  have hgn : Integrable fun u => |g u| * ‖u‖ ^ 2 := by
    have := hg.integrable_mul_bdd (f := fun u => ‖u‖ ^ 2) (by fun_prop)
      (K := (max (|x.re| + |x.im|) (|x'.re| + |x'.im|)) ^ 2) (fun u hu => by
        rw [abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) hu 2)
    refine this.abs.congr (Eventually.of_forall fun u => ?_)
    simp only [abs_mul, abs_pow, abs_norm]; ring
  have hnorm : ∫ u, |g u| * ‖u‖ ^ 2 ≤ 4 * A ^ 2 * I := by
    rw [hI, ← integral_const_mul]
    refine integral_mono hgn (hgi.abs.const_mul _) fun u => ?_
    by_cases hu : ‖u‖ ≤ max (|x.re| + |x.im|) (|x'.re| + |x'.im|)
    · have : ‖u‖ ^ 2 ≤ 4 * A ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg u) (hu.trans hR0) 2; nlinarith
      simp only
      nlinarith [abs_nonneg (g u)]
    · have h0 : g u = 0 := hg.supp u (not_le.mp hu)
      rw [h0]; simp
  have hS0 : 0 ≤ ∫ u, |g u| * ‖u‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hpi := Real.pi_pos
  calc ∫ q, kerFun g q ^ 2
      ≤ Real.pi * (∫ u, g u ^ 2) + I * (∫ u, |g u| * ‖u‖ ^ 2) / 2 := hb
    _ ≤ Real.pi * (2 * I) + I * (4 * A ^ 2 * I) / 2 := by gcongr
    _ = (2 * Real.pi + 2 * A ^ 2 * I) * I := by ring
    _ ≤ (2 * Real.pi + 32 * A ^ 4) * (4 * A * ‖x - x'‖) := by
        apply mul_le_mul _ hI1 hI0 (by positivity)
        nlinarith

/-- the `L²` class of `kerFun 1_{[0,x]}` -/
def rectL2 (x : ℂ) : WNSpace := ((rectInd_bddSupp x).memLp_kerFun.1).toLp _

lemma coeFn_rectL2 (x : ℂ) : (rectL2 x : ℝ × ℂ → ℝ) =ᵐ[volume] kerFun (rectInd x) :=
  MemLp.coeFn_toLp _

lemma sq_norm_rectL2_sub (x x' : ℂ) :
    ‖rectL2 x - rectL2 x'‖ ^ 2 = ∫ q, kerFun (fun u => rectInd x u - rectInd x' u) q ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (rectL2 x) (rectL2 x'), coeFn_rectL2 x, coeFn_rectL2 x']
    with q h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3, ← kerFun_sub (rectInd_bddSupp x) (rectInd_bddSupp x'),
    real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the antiderivative field `F(x) = W(kerFun 1_{[0,x]})` -/
def rectField (W : WNSpace → Ω → ℝ) (x : ℂ) (ω : Ω) : ℝ := W (rectL2 x) ω

lemma hasLaw_rectField_sub (hW : IsWhiteNoise P W) (x x' : ℂ) :
    HasLaw (fun ω => rectField W x ω - rectField W x' ω)
      (gaussianReal 0 (‖rectL2 x - rectL2 x'‖ ^ 2).toNNReal) P := by
  have h := hW.hasLaw ![rectL2 x, rectL2 x'] ![1, -1]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul,
    ← sub_eq_add_neg] at h
  refine h.congr ?_
  exact Eventually.of_forall fun ω => by simp only [rectField]; ring

/-- **Continuous version of the antiderivative field.** -/
theorem exists_continuous_rectField (hW : IsWhiteNoise P W) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ x, (fun ω => Y x ω) =ᵐ[P] rectField W x := by
  refine exists_continuous_modification_of_gauss (fun x => hW.measurable _)
    (fun x x' => (‖rectL2 x - rectL2 x'‖ ^ 2).toNNReal) (hasLaw_rectField_sub hW)
    (fun A => ⟨(2 * Real.pi + 32 * A ^ 4) * (4 * |A|), by positivity,
      fun x x' h0 h1 h2 h3 => ?_⟩)
  have hA : 0 ≤ A := (abs_nonneg _).trans h0
  rw [Real.coe_toNNReal', max_le_iff]
  refine ⟨?_, by positivity⟩
  rw [sq_norm_rectL2_sub, abs_of_nonneg hA, mul_assoc]
  exact integral_sq_kerFun_rect_sub_le h0 h1 h2 h3

end GFFExist
end LQGMetric
