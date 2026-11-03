/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_4M2 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4N4
import LatticeProb.Bonanno.LQGMetric.Complex.HarmonicComp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LM Lemma 3.1, canonical nesting: the increments and the telescoping identity (task P2-LM34c)

Source: MQ arXiv:1812.03913 `lqg_geodesics.tex`, proof of Prop 4.3 (l. 693–700): with
`𝔥^{r}` the harmonic part of `h` in `B_r`, `𝔥^{r_k} = ∑_{j ≤ k} (𝔥^{r_j} − 𝔥^{r_{j−1}})` on
`B_{r_k}`. In the normalized coordinates of `lmScaled h (r_j)` (harmonic part `G_j` on `B_1`):
`D_0 = G_0`, `D_{j+1} = G_{j+1} − G_j(ρ ·) + λ_j` with `ρ = r_{j+1}/r_j` and a random constant
`λ_j` (constants cancel in the identity; `λ_j` is fixed in `L3_4M3` so that `D_{j+1}` is the
harmonic part of the zero-boundary field).

* `nestIncr` (the distributions `D_j`), `nestIncr_succ_apply`, `measurable_nestIncr`;
* `restrictTo_affineComp_rep`: `G` represented by `g` on `B_1` ⇒ `G(ρ ·)` represented by
  `g(ρ ·)` (`0 < ρ ≤ 1`); `harmonicOnNhd_comp_smul`;
* `nestFun`, `sum_nestFun`: the telescoping identity (pure algebra).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Finset Metric InnerProductSpace Topology

namespace LQGMetric.LM

open Blueprint

/-- the increments `D_0 = G_0`, `D_{j+1} = G_{j+1} − G_j((r_{j+1}/r_j) ·) + λ_j` -/
def nestIncr {Ω : Type} (r : ℕ → ℝ) (G : ℕ → Ω → DistC) (lam : ℕ → Ω → ℝ) : ℕ → Ω → DistC
  | 0 => G 0
  | j + 1 => fun ω => addConst (G (j + 1) ω - affineComp (r (j + 1) / r j) 0 (G j ω)) (lam j ω)

lemma nestIncr_succ_apply {Ω : Type} (r : ℕ → ℝ) (G : ℕ → Ω → DistC) (lam : ℕ → Ω → ℝ)
    (j : ℕ) (ω : Ω) (φ : TestC) :
    nestIncr r G lam (j + 1) ω φ = G (j + 1) ω φ -
      ((r (j + 1) / r j) ^ 2)⁻¹ * G j ω (testAffinePull (r (j + 1) / r j) 0 φ) +
      (∫ x, φ x) * lam j ω := by
  simp only [nestIncr]
  rw [GFFInv.addConst_apply, ← GFFInv.affineComp_apply]
  rfl

lemma measurable_nestIncr {Ω : Type} [MeasurableSpace Ω] (r : ℕ → ℝ) {G : ℕ → Ω → DistC}
    {lam : ℕ → Ω → ℝ} (hG : ∀ j, Measurable (G j)) (hl : ∀ j, Measurable (lam j)) (j : ℕ) :
    Measurable (nestIncr r G lam j) := by
  cases j with
  | zero => exact hG 0
  | succ j =>
    refine GFFInv.measurable_distC_iff.2 fun φ => ?_
    simp only [nestIncr_succ_apply]
    exact ((GFFInv.measurable_distC_iff.1 (hG (j + 1)) φ).sub
      ((GFFInv.measurable_distC_iff.1 (hG j) _).const_mul _)).add ((hl j).const_mul _)

lemma restrictTo_apply_eq (T : DistC) (φ : TestOn (ballO (0 : ℂ) 1)) :
    restrictTo (ballO 0 1) T φ = T (TestFunction.monoCLM ℝ φ) := rfl

lemma monoCLM_apply_eq (φ : TestOn (ballO (0 : ℂ) 1)) (x : ℂ) :
    (TestFunction.monoCLM ℝ φ : TestC) x = φ x := by
  simp [TestFunction.monoCLM_apply]

/-- `G` represented by `g` on `B_1` ⇒ `G(ρ ·)` represented by `g(ρ ·)` on `B_1` (`0 < ρ ≤ 1`) -/
lemma restrictTo_affineComp_rep {T : DistC} {g : ℂ → ℝ}
    (hg : ∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) T φ = ∫ x, g x * φ x) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (φ : TestOn (ballO 0 1)) :
    restrictTo (ballO 0 1) (affineComp ρ 0 T) φ = ∫ x, g (ρ • x) * φ x := by
  set ψ : TestC := testAffinePull ρ 0 (TestFunction.monoCLM ℝ φ) with hψ
  have hψx : ∀ x, ψ x = φ (ρ⁻¹ • x) := fun x => by
    rw [hψ, testAffinePull_apply ρ 0 hρ0.ne', monoCLM_apply_eq, sub_zero]
    congr 1
    rw [Complex.real_smul, div_eq_inv_mul]; push_cast; rfl
  have hsupp : tsupport (ψ : ℂ → ℝ) ⊆ ball (0 : ℂ) 1 := by
    have e : (ψ : ℂ → ℝ) = fun x => φ (ρ⁻¹ • x) := funext hψx
    rw [e]
    refine (tsupport_comp_subset_preimage (φ : ℂ → ℝ) (continuous_const_smul ρ⁻¹)).trans ?_
    intro x hx
    have h1 : ρ⁻¹ • x ∈ ball (0 : ℂ) 1 := φ.tsupport_subset hx
    simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hρ0] at h1 ⊢
    rw [inv_mul_lt_iff₀ hρ0, mul_one] at h1
    linarith
  rw [restrictTo_apply_eq, GFFInv.affineComp_apply, ← hψ, ← restrictTo_testOn1 T ψ hsupp,
    hg]
  have hcv := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure ℂ))
    (fun x => g x * (testOn1 ψ hsupp) x) ρ
  simp only [Complex.finrank_real_complex] at hcv
  have e2 : ∀ x : ℂ, g (ρ • x) * (testOn1 ψ hsupp) (ρ • x) = g (ρ • x) * φ x := fun x => by
    change g (ρ • x) * ψ (ρ • x) = _
    rw [hψx, smul_smul, inv_mul_cancel₀ hρ0.ne', one_smul]
  simp only [e2] at hcv
  rw [hcv, abs_inv, abs_of_pos (pow_pos hρ0 2), smul_eq_mul]

lemma harmonicOnNhd_comp_smul {g : ℂ → ℝ} (hg : HarmonicOnNhd g (ball (0 : ℂ) 1)) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) : HarmonicOnNhd (fun y => g (ρ • y)) (ball (0 : ℂ) 1) := by
  have e : (fun y : ℂ => g (ρ • y)) = g ∘ fun y : ℂ => (ρ : ℂ) * y := by
    funext y; simp [Complex.real_smul]
  rw [e]
  refine harmonicOnNhd_comp_holo isOpen_ball isOpen_ball hg
    ((differentiable_id.const_mul _).differentiableOn) fun y hy => ?_
  simp only [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hρ0] at hy ⊢
  nlinarith [norm_nonneg y]

/-- the harmonic increments `d_0 = g_0`, `d_{j+1}(y) = g_{j+1}(y) − g_j((r_{j+1}/r_j) y) + λ_j` -/
def nestFun (r : ℕ → ℝ) (g : ℕ → ℂ → ℝ) (lam : ℕ → ℝ) : ℕ → ℂ → ℝ
  | 0 => g 0
  | j + 1 => fun y => g (j + 1) y - g j ((r (j + 1) / r j) • y) + lam j

/-- **The telescoping identity** `g_k(u) − g_k(0) = ∑_{j ≤ k} (d_j((r_k/r_j) u) − d_j(0))`
(MQ l. 693–700). -/
theorem sum_nestFun {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (g : ℕ → ℂ → ℝ) (lam : ℕ → ℝ) (k : ℕ) :
    ∀ u : ℂ, g k u - g k 0 =
      ∑ j ∈ range (k + 1), (nestFun r g lam j ((r k / r j : ℝ) • u) - nestFun r g lam j 0) := by
  induction k with
  | zero =>
    intro u
    simp only [zero_add, sum_range_one, nestFun, div_self (hr 0).ne', one_smul]
  | succ k ih =>
    intro u
    rw [sum_range_succ]
    have hs : ∀ j ∈ range (k + 1), nestFun r g lam j ((r (k + 1) / r j : ℝ) • u) =
        nestFun r g lam j ((r k / r j : ℝ) • ((r (k + 1) / r k : ℝ) • u)) := fun j _ => by
      rw [smul_smul]; congr 2; field_simp [(hr j).ne', (hr k).ne']
    rw [sum_congr rfl fun j hj => by rw [hs j hj], ← ih]
    simp only [nestFun, div_self (hr (k + 1)).ne', one_smul, smul_zero]
    ring

end LQGMetric.LM
