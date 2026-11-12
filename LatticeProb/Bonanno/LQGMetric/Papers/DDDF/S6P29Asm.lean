/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P29Asm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29Ker
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29Sq
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6FinalTail
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiField

/-!
# DDDF Proposition 29 on `(−1,2)²`: assembly of the coupling (R4)

DDDF arXiv:1904.08021, `tightness.tex`, proof of Proposition 29 (DD:1508–1601). With one white
noise `W` (`WhiteNoise.exists_isWhiteNoise`):
* `h := zbX W` is the zero-boundary GFF on `D = (−1,2)²` (DD:1514–1525, `isZBGFFProcessExt_zbX`);
* `φ_t := φ_{√t, 1}` of the shifted noise `W ∘ T_t` (DD:1527–1532, `isWhiteNoise_shift`);
* `φ_t − p_{t/2} * h` is, at each `x`, `a.s.` the Gaussian `W(√π p29Ker t x)` with
  `p29Ker t x = T_t k_{√t,1,x} − zbKer(p_{t/2}(x − ·) 1_D)` (DD:1533–1536);
* Kolmogorov + Fernique (DD:1598–1601): `DDDF.exists_version_tail` on `K = cthickening r (cl U)`
  gives the uniform Gaussian tail, once `E(Δ_v − Δ_u)² ≤ A |u − v|` and `Var Δ_v ≤ σ²`
  uniformly in `t ∈ (0, 1/2)` (the kernel estimates of DD:1562–1596, `P29KerBounds`).

`dddfProp29Sq_of_kerBounds : P29KerBounds → DDDFProp29Sq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real Metric Filter
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace P29WN

open HeatSq WhiteNoise Blueprint SupTail

/-- the white-noise kernel of `φ_t − p_{t/2} * h` at `x` (without the factor `√π`;
DD:1533–1536) -/
def p29Ker (t : ℝ) (x : ℂ) : WNSpace :=
  shiftL2 t (phiKernelL2 (Real.sqrt t) 1 x) -
    zbKerL2 (-1) 3 (by norm_num) (heatBdd (sqOpen (-1) 3) (t / 2) x)

/-- **The kernel estimates of DDDF Proposition 29** (DD:1562–1596, first, second and third
terms): on every compact `K ⊆ (−1,2)²`, uniformly in `t ∈ (0,1/2)`,
`‖p29Ker t v − p29Ker t u‖² ≤ A |u − v|` and `‖p29Ker t v‖² ≤ σ²`. -/
def P29KerBounds : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ sqOpen (-1) 3 → ∃ A σ : ℝ, 0 < A ∧ 0 < σ ∧
    ∀ t ∈ Ioo (0 : ℝ) (1 / 2), ∀ u ∈ K, ∀ v ∈ K,
      ‖p29Ker t v - p29Ker t u‖ ^ 2 ≤ A * ‖u - v‖ ∧ ‖p29Ker t v‖ ^ 2 ≤ σ ^ 2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma W_sub_ae (hW : IsWhiteNoise P W) (f g : WNSpace) :
    W (f - g) =ᵐ[P] fun ω => W f ω - W g ω := by
  have e : f - g = f + (-1 : ℝ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e]
  filter_upwards [hW.add_ae f ((-1 : ℝ) • g), hW.smul_ae (-1) g] with ω h1 h2
  rw [h1, h2]; ring

lemma cthickening_subset_sq {K : Set ℂ} (hK : IsCompact K) {d : ℝ} (hd : 0 < d)
    (hdK : ∀ y ∈ K, y.re ∈ Icc (-1 + d) (-1 + 3 - d) ∧ y.im ∈ Icc (-1 + d) (-1 + 3 - d)) :
    cthickening (d / 2) K ⊆ sqOpen (-1) 3 := by
  rw [hK.cthickening_eq_biUnion_closedBall (by positivity)]
  intro z hz
  obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 hz
  rw [mem_closedBall, dist_eq_norm] at hzy
  have e1 := (Complex.abs_re_le_norm (z - y)).trans hzy
  have e2 := (Complex.abs_im_le_norm (z - y)).trans hzy
  rw [Complex.sub_re, abs_le] at e1
  rw [Complex.sub_im, abs_le] at e2
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hdK y hy
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [e1.1, e1.2, e2.1, e2.2]

/-- **DDDF Proposition 29 on `(−1,2)²`** from the kernel estimates. -/
theorem dddfProp29Sq_of_kerBounds (hB : P29KerBounds) : DDDFProp29Sq := by
  intro U hU hUc hUD
  obtain ⟨d, hd, hdK⟩ := exists_margin (a := -1) (L := 3) hUc hUD
  set K := closure U with hKdef
  have hr : 0 < d / 2 := half_pos hd
  have hKr := cthickening_subset_sq hUc hd hdK
  obtain ⟨A, σ, hA, hσ, hb⟩ := hB _ hUc.cthickening hKr
  obtain ⟨W, hW⟩ := exists_isWhiteNoise
  haveI := hW.isProbabilityMeasure
  obtain ⟨C, c, hC, hc, hT⟩ := exists_version_tail (P := LQGDimension.ExistAsm.stdP) hUc hr
    (A := π * A) (σ := Real.sqrt π * σ) (by positivity) (by positivity)
  refine ⟨C, c, hC, hc, fun t ht => ?_⟩
  have ht1 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  have hWn := isWhiteNoise_shift hW t
  have hX := isZBGFFProcessExt_zbX (P := LQGDimension.ExistAsm.stdP) hW
  obtain ⟨Y0, hY0⟩ := DFGPS.exists_heat_contVersion_sq (by norm_num : (0 : ℝ) < 3) hX
  have hYt := hY0 t ht1
  set G : ℂ → (ℕ → ℝ) → ℝ := fun v => W (Real.sqrt π • p29Ker t v) with hGdef
  have hG : IsGaussianProcess G LQGDimension.ExistAsm.stdP := hW.isGaussianProcess_comp _
  have h0 : ∀ v, ∫ ω, G v ω ∂LQGDimension.ExistAsm.stdP = 0 := fun v => integral_W hW _
  have hinc : ∀ u ∈ cthickening (d / 2) K, ∀ v ∈ cthickening (d / 2) K,
      ∫ ω, (G v ω - G u ω) ^ 2 ∂LQGDimension.ExistAsm.stdP ≤ π * A * ‖u - v‖ := by
    intro u hu v hv
    have e : ∫ ω, (G v ω - G u ω) ^ 2 ∂LQGDimension.ExistAsm.stdP =
        ‖Real.sqrt π • p29Ker t v - Real.sqrt π • p29Ker t u‖ ^ 2 := by
      rw [← integral_sq_W hW]
      refine integral_congr_ae ?_
      filter_upwards [W_sub_ae hW (Real.sqrt π • p29Ker t v) (Real.sqrt π • p29Ker t u)]
        with ω hω
      rw [hω]
    rw [e, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt Real.pi_pos.le, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb t ht u hu v hv).1 Real.pi_pos.le
  have hvar : ∀ v ∈ cthickening (d / 2) K,
      Var[G v; LQGDimension.ExistAsm.stdP] ≤ (Real.sqrt π * σ) ^ 2 := by
    intro v hv
    rw [variance_eq_integral (hW.measurable _).aemeasurable, h0 v]
    simp only [sub_zero]
    rw [integral_sq_W hW, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_left (hb t ht v hv v hv).2 (sq_nonneg _)
  obtain ⟨Yk, hYk, hYkc, hYkt⟩ := hT G hG h0 hinc hvar
  have hsq : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1.2.le
  have hφ := isPhiVersion_phiVer hWn (Real.sqrt_pos.2 ht.1) hsq
  set Z : ℂ → (ℕ → ℝ) → ℝ := fun z ω =>
    phiVer (fun f => W (shiftL2 t f)) LQGDimension.ExistAsm.stdP (Real.sqrt t) 1 z ω - Y0 t z ω
  have hZc : ∀ ω, Continuous fun z => Z z ω := fun ω => (hφ.cont ω).sub (hYt.1 ω)
  have hZG : ∀ v, (fun ω => Z v ω) =ᵐ[LQGDimension.ExistAsm.stdP] G v := by
    intro v
    filter_upwards [hφ.ae_eq v, hYt.2.2 v,
      W_sub_ae hW (Real.sqrt π • shiftL2 t (phiKernelL2 (Real.sqrt t) 1 v))
        (Real.sqrt π • zbKerL2 (-1) 3 (by norm_num) (heatBdd (sqOpen (-1) 3) (t / 2) v)),
      hW.smul_ae (Real.sqrt π) (shiftL2 t (phiKernelL2 (Real.sqrt t) 1 v))] with ω h1 h2 h3 h4
    simp only [Z, hGdef, p29Ker, smul_sub]
    rw [h1, h2, h3, h4]
    rfl
  have hEq : ∀ᵐ ω ∂LQGDimension.ExistAsm.stdP, ∀ x ∈ K, Z x ω = Yk x ω := by
    obtain ⟨D, hDc, hDs, hDd⟩ := TopologicalSpace.exists_countable_dense_subset K
    have hD : ∀ᵐ ω ∂LQGDimension.ExistAsm.stdP, ∀ q ∈ D, Z q ω = Yk q ω := by
      rw [ae_ball_iff hDc]
      intro q hq
      filter_upwards [hZG q, hYk q (hDs hq)] with ω h1 h2
      rw [h1, h2]
    filter_upwards [hD] with ω hω
    exact Set.EqOn.of_subset_closure hω (hZc ω).continuousOn (hYkc ω) hDs hDd
  refine ⟨ℕ → ℝ, inferInstance, LQGDimension.ExistAsm.stdP, zbX W, fun f => W (shiftL2 t f),
    Y0 t, inferInstance, hX, hWn, hYt, fun x hx => ?_⟩
  refine (measure_mono_ae ?_).trans (hYkt x hx)
  filter_upwards [hEq] with ω hω hxω
  refine le_trans hxω (iSup₂_le fun z hz => ?_)
  have hzK : z ∈ K := subset_closure hz
  have e : |phiVer (fun f => W (shiftL2 t f)) LQGDimension.ExistAsm.stdP (Real.sqrt t) 1 z ω -
      Y0 t z ω| = |Yk z ω| := by rw [← hω z hzK]
  rw [e]
  exact le_iSup₂ (f := fun z (_ : z ∈ K) => ENNReal.ofReal |Yk z ω|) z hzK

end P29WN
end DDDF
end LQGMetric
