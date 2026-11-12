/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoisePsi at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseL4
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# DDDF's truncated white-noise field `ψ` (task P2-DDDFPSI; blueprint DDDF.D2.psi)

DDDF (arXiv:1904.08021, `tightness.tex` l. 350–358): fix a smooth radial bump `Φ` with
`0 ≤ Φ ≤ 1`, `Φ = 1` on `B(0,1)`, `Φ = 0` off `B(0,2)`, small constants `r₀, ε₀ > 0`, and set
`σ_t = r₀ √t |log t|^{ε₀}`, `p^{Tr}_{t/2} := p_{t/2} Φ(·/σ_t)`,
`ψ_δ(x) := ∫_{δ²}^1 ∫ p^{Tr}_{t/2}(x − y) W(dy, dt)` (same white noise `W` as `φ`).

Deviations (blueprint DDDF.md, proposed D-DDDF-1, D-DDDF-3):
* D-DDDF-1: `ψ` carries the factor `√π` of `φ` (l. 355 omits it; (2.23) needs the same
  normalization).
* D-DDDF-3: `σ_t := r₀ √t (1 + |log t|)^{ε₀}` (the printed `|log t|^{ε₀}` vanishes at `t = 1`,
  and the claim `sup_t √t/σ_t < ∞` of l. 417 is false for it).

Here the kernel is `psiKernel a b x = phiKernel a b x · Φ(σ_t⁻¹(x − y))`, pointwise dominated by
`phiKernel`, hence in `L²` (`psiKernelL2`), and `psi W a b x = √π W(psiKernelL2 a b x)`.
The cutoff and the constants are bundled in `PsiParams`; `exists_psiCutoff` shows a cutoff with
all of DDDF's properties exists (mathlib's `ContDiffBumpBase.ofInnerProductSpace`).
Also: the generic variance identity `Var(√π W f − √π W g) = π ‖f − g‖²` and a Fubini lemma
for time-weighted kernels used in Lemma 4 and (2.23).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace WhiteNoise

/-- DDDF's cutoff `Φ` (l. 352): smooth, radial, `0 ≤ Φ ≤ 1`, `Φ = 1` on the unit ball (closed
ball; equivalent by continuity), `Φ = 0` off the open ball of radius `2`. -/
structure PsiCutoff where
  Φ : ℂ → ℝ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
  radial : ∀ x y : ℂ, ‖x‖ = ‖y‖ → Φ x = Φ y
  nonneg : ∀ x, 0 ≤ Φ x
  le_one : ∀ x, Φ x ≤ 1
  eq_one : ∀ x, ‖x‖ ≤ 1 → Φ x = 1
  eq_zero : ∀ x, 2 ≤ ‖x‖ → Φ x = 0

/-- DDDF's data for `ψ`: the cutoff `Φ` and the constants `r₀, ε₀ > 0` (l. 352). -/
structure PsiParams where
  cut : PsiCutoff
  r₀ : ℝ
  ε₀ : ℝ
  r₀_pos : 0 < r₀
  ε₀_pos : 0 < ε₀

/-- A cutoff with DDDF's properties exists: `x ↦ smoothTransition (2 − ‖x‖)`. -/
theorem exists_psiCutoff : Nonempty PsiCutoff := by
  let B := ContDiffBumpBase.ofInnerProductSpace ℂ
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B.toFun 2) := by
    have h := B.smooth
    rw [contDiff_iff_contDiffAt]
    intro x
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry B.toFun) (2, x) :=
      h.contDiffAt (prod_mem_nhds (Ioi_mem_nhds (by norm_num)) Filter.univ_mem)
    exact h1.comp x (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨⟨B.toFun 2, hsm, fun x y hxy => ?_, fun x => (B.mem_Icc 2 x).1,
    fun x => (B.mem_Icc 2 x).2, fun x hx => B.eq_one 2 (by norm_num) x hx, fun x hx => ?_⟩⟩
  · show Real.smoothTransition ((2 - ‖x‖) / (2 - 1)) = Real.smoothTransition ((2 - ‖y‖) / (2 - 1))
    rw [hxy]
  · have hs := B.support 2 (by norm_num)
    by_contra hne
    have : x ∈ Function.support (B.toFun 2) := hne
    rw [hs, Metric.mem_ball, dist_zero_right] at this
    linarith

namespace PsiCutoff

variable (C : PsiCutoff)

lemma continuous : Continuous C.Φ := C.smooth.continuous

lemma measurable : Measurable C.Φ := C.continuous.measurable

lemma hasCompactSupport : HasCompactSupport C.Φ := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2) fun x hx => C.eq_zero x ?_
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  exact hx.le

/-- `Φ` is Lipschitz (smooth with compact support; DDDF l. 414 uses `‖∇Φ‖_∞ < ∞`). -/
lemma exists_lipschitz : ∃ L : NNReal, LipschitzWith L C.Φ :=
  ContDiff.lipschitzWith_of_hasCompactSupport C.hasCompactSupport C.smooth (by simp)

end PsiCutoff

namespace PsiParams

variable (Q : PsiParams)

/-- `σ_t = r₀ √t (1 + |log t|)^{ε₀}` (DDDF (2.19) = `Def:sigma`, with D-DDDF-3). -/
def sigma (t : ℝ) : ℝ := Q.r₀ * Real.sqrt t * (1 + |Real.log t|) ^ Q.ε₀

lemma sigma_pos {t : ℝ} (ht : 0 < t) : 0 < Q.sigma t := by
  unfold sigma
  have := Q.r₀_pos
  have : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  positivity

/-- `σ_t ≥ r₀ √t` (replaces DDDF's `sup_t √t/σ_t < ∞`, l. 417). -/
lemma r₀_mul_sqrt_le_sigma (t : ℝ) : Q.r₀ * Real.sqrt t ≤ Q.sigma t := by
  unfold sigma
  have h1 : 1 ≤ (1 + |Real.log t|) ^ Q.ε₀ :=
    Real.one_le_rpow (by linarith [abs_nonneg (Real.log t)]) Q.ε₀_pos.le
  have : 0 ≤ Q.r₀ * Real.sqrt t := mul_nonneg Q.r₀_pos.le (Real.sqrt_nonneg _)
  nlinarith

lemma measurable_sigma : Measurable Q.sigma := by
  unfold sigma
  fun_prop

/-- The truncation factor `Φ_{σ_t}(x − y) = Φ(σ_t⁻¹ (x − y))` at `p = (t, y)`. -/
def trunc (x : ℂ) (p : ℝ × ℂ) : ℝ := Q.cut.Φ ((Q.sigma p.1)⁻¹ • (x - p.2))

lemma measurable_trunc (x : ℂ) : Measurable (Q.trunc x) := by
  unfold trunc
  exact Q.cut.measurable.comp (((Q.measurable_sigma.comp measurable_fst).inv).smul
    (measurable_const.sub measurable_snd))

lemma trunc_nonneg (x : ℂ) (p : ℝ × ℂ) : 0 ≤ Q.trunc x p := Q.cut.nonneg _

lemma trunc_le_one (x : ℂ) (p : ℝ × ℂ) : Q.trunc x p ≤ 1 := Q.cut.le_one _

/-- DDDF's truncated kernel `1_{[a²,b²]}(t) p^{Tr}_{t/2}(x − y)` (l. 355). -/
def psiKernel (a b : ℝ) (x : ℂ) (p : ℝ × ℂ) : ℝ := phiKernel a b x p * Q.trunc x p

lemma measurable_psiKernel (a b : ℝ) (x : ℂ) : Measurable (Q.psiKernel a b x) :=
  (measurable_phiKernel a b x).mul (Q.measurable_trunc x)

lemma abs_psiKernel_le (a b : ℝ) (x : ℂ) (p : ℝ × ℂ) :
    |Q.psiKernel a b x p| ≤ |phiKernel a b x p| := by
  unfold psiKernel
  rw [abs_mul]
  have h0 := Q.trunc_nonneg x p
  have h1 := Q.trunc_le_one x p
  rw [abs_of_nonneg h0]
  exact mul_le_of_le_one_right (abs_nonneg _) h1

lemma memLp_psiKernel (a b : ℝ) (ha : 0 < a) (x : ℂ) :
    MemLp (Q.psiKernel a b x) 2 (volume : Measure (ℝ × ℂ)) :=
  (memLp_phiKernel a b ha x).of_le (Q.measurable_psiKernel a b x).aestronglyMeasurable
    (Eventually.of_forall fun p => by
      simpa [Real.norm_eq_abs] using Q.abs_psiKernel_le a b x p)

/-- The `L²` class of the truncated kernel (junk `0` for `a ≤ 0`, as WN-3). -/
def psiKernelL2 (a b : ℝ) (x : ℂ) : WNSpace :=
  if h : 0 < a then (Q.memLp_psiKernel a b h x).toLp _ else 0

lemma coeFn_psiKernelL2 (a b : ℝ) (ha : 0 < a) (x : ℂ) :
    (Q.psiKernelL2 a b x : ℝ × ℂ → ℝ) =ᵐ[volume] Q.psiKernel a b x := by
  rw [psiKernelL2, dite_eq_left_of_eq_true (eq_true ha)]
  exact MemLp.coeFn_toLp _

end PsiParams

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- DDDF's field `ψ_{a,b}(x) = √π ∫_{a²}^{b²} ∫ p^{Tr}_{t/2}(x − y) W(dy, dt)` (l. 355, with
the factor `√π` of D-DDDF-1); `ψ_δ = ψ_{δ,1}`, `ψ_{m,n} = ψ_{2^{-n},2^{-m}}`. -/
def psi (Q : PsiParams) (W : WNSpace → Ω → ℝ) (a b : ℝ) (x : ℂ) (ω : Ω) : ℝ :=
  Real.sqrt Real.pi * W (Q.psiKernelL2 a b x) ω

lemma measurable_psi (hW : IsWhiteNoise P W) (Q : PsiParams) (a b : ℝ) (x : ℂ) :
    Measurable (psi Q W a b x) :=
  (hW.measurable _).const_mul _

/-- `Var(√π W f − √π W g) = π ‖f − g‖²`. -/
theorem variance_sqrtPi_sub (hW : IsWhiteNoise P W) (f g : WNSpace) :
    Var[fun ω => Real.sqrt Real.pi * W f ω - Real.sqrt Real.pi * W g ω; P] =
      Real.pi * ‖f - g‖ ^ 2 := by
  have h := hW.hasLaw ![f, g] ![Real.sqrt Real.pi, -Real.sqrt Real.pi]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have h' : HasLaw (fun ω => Real.sqrt Real.pi * W f ω - Real.sqrt Real.pi * W g ω)
      (gaussianReal 0 (‖Real.sqrt Real.pi • f + (-Real.sqrt Real.pi) • g‖ ^ 2).toNNReal) P :=
    h.congr (Eventually.of_forall fun ω => by simp only; ring)
  rw [h'.variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ (by positivity),
    neg_smul, ← sub_eq_add_neg, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt Real.pi_pos.le]

/-- `‖f − g‖²` for `L²` classes of square-integrable functions. -/
lemma sq_norm_toLp_sub {f g : ℝ × ℂ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ p, (f p - g p) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with p h h1 h2
  rw [h, Pi.sub_apply, h1, h2, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [sq]

/-- Fubini for time-weighted kernels: for `G ≥ 0` with `∫ G(t, ·) = g(t)` on `[a², b²]` and a
nonnegative weight `w`, `∫ 1_{[a²,b²]}(t) w(t) G(t, y) = ∫_{[a²,b²]} w g`. -/
lemma integral_timeWeight {a b : ℝ} {w g : ℝ → ℝ} {G : ℝ × ℂ → ℝ}
    (hw : ContinuousOn w (Icc (a ^ 2) (b ^ 2))) (hw0 : ∀ t ∈ Icc (a ^ 2) (b ^ 2), 0 ≤ w t)
    (hwm : Measurable w)
    (hg : ContinuousOn g (Icc (a ^ 2) (b ^ 2))) (hGm : Measurable G)
    (hG0 : ∀ p : ℝ × ℂ, p.1 ∈ Icc (a ^ 2) (b ^ 2) → 0 ≤ G p)
    (hGi : ∀ t ∈ Icc (a ^ 2) (b ^ 2), Integrable fun y => G (t, y))
    (hGg : ∀ t ∈ Icc (a ^ 2) (b ^ 2), ∫ y, G (t, y) = g t) :
    Integrable ((Icc (a ^ 2) (b ^ 2) ×ˢ univ).indicator fun p => w p.1 * G p) ∧
      ∫ p, (Icc (a ^ 2) (b ^ 2) ×ˢ univ).indicator (fun p => w p.1 * G p) p =
        ∫ t in Icc (a ^ 2) (b ^ 2), w t * g t := by
  set F : ℝ × ℂ → ℝ := (Icc (a ^ 2) (b ^ 2) ×ˢ univ).indicator fun p => w p.1 * G p with hF
  have hsec : ∀ t, (fun y => F (t, y)) =
      fun y => (Icc (a ^ 2) (b ^ 2)).indicator (fun t => w t) t * G (t, y) := by
    intro t; funext y
    by_cases ht : t ∈ Icc (a ^ 2) (b ^ 2) <;> simp [hF, ht]
  have hinner : ∀ t, ∫ y, F (t, y) = (Icc (a ^ 2) (b ^ 2)).indicator (fun t => w t * g t) t := by
    intro t
    rw [hsec t]
    by_cases ht : t ∈ Icc (a ^ 2) (b ^ 2)
    · simp only [ht, indicator_of_mem]
      rw [integral_const_mul, hGg t ht]
    · simp [ht]
  have hFm : Measurable F :=
    ((hwm.comp measurable_fst).mul hGm).indicator (measurableSet_Icc.prod MeasurableSet.univ)
  have hnn : ∀ p, 0 ≤ F p := fun p => by
    simp only [hF]
    exact indicator_nonneg (fun q hq => mul_nonneg (hw0 _ (mem_prod.mp hq).1) (hG0 q (mem_prod.mp hq).1)) p
  have hI : IntegrableOn (fun t => w t * g t) (Icc (a ^ 2) (b ^ 2)) :=
    (hw.mul hg).integrableOn_compact isCompact_Icc
  have hint : Integrable F := by
    rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl,
      integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun t => ?_, ?_⟩
    · rw [hsec t]
      by_cases ht : t ∈ Icc (a ^ 2) (b ^ 2)
      · simp only [ht, indicator_of_mem]
        exact (hGi t ht).const_mul (w t)
      · simp [ht]
    · have : (fun t => ∫ y, ‖F (t, y)‖) =
          (Icc (a ^ 2) (b ^ 2)).indicator (fun t => w t * g t) := by
        funext t
        rw [← hinner t]
        congr 1; funext y
        exact Real.norm_of_nonneg (hnn _)
      rw [this, integrable_indicator_iff measurableSet_Icc]
      exact hI
  refine ⟨hint, ?_⟩
  rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl, integral_prod F hint]
  simp_rw [hinner]
  rw [integral_indicator measurableSet_Icc]

end WhiteNoise
end LQGMetric
