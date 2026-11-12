/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcG at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcF
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32G6
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P317B
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117C

/-!
# The Lipschitz inputs in terms of the coarse field (P2-DZZCONC)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 1572–1594 (for (eq-concentration-approximate)) and
l. 1631–1645 (for (eq-concentration-approximate-2)). With the concrete coarse field
`𝒳_δ = coarseField W (dzzCmc γ) δ` (S3ConcF):

* `coarse_gauss`: `𝒳_δ` (D124: `η` at boxes, `h̃` at coarse points) is a centered Gaussian
  process with variance `≤ (C_mc + 4 + b₁) log δ⁻¹` (DZZ l. 1600: "maximal individual variance
  … is `O_{C_mc}(log δ⁻¹)`"; `etaVar_le`, `etaVar_anti`, `tildeVar_sub_etaVar_le`).
* `DZZGoodSet P γ W δ A B ℓ τ ε`: a set `𝒜 ⊆ 𝒜_δ` of coarse paths with `P(𝒳_δ ∉ 𝒜) ≤ ε`,
  (eq-distance-Lip) `‖x − x'‖_∞ ≤ ℓ ⇒ |log D'_x − log D'_{x'}| ≤ τ` on `𝒜`, and a finite `1`-net.
* OPEN: `DZZDistLip1C` (`ℓ = aι log δ⁻¹`, `τ = ι log δ⁻¹`, `ε = δ^{aι}`) and `DZZDistLip2C`
  (`ℓ = (log δ⁻¹)^{0.9}`, `τ = (log δ⁻¹)^{0.93}`, `ε = δ^a`).
* **`dzzDistLip1_of_C`**, **`dzzDistLip2_of_C`**, **`dzzConcApprox_of_C`**, and
  **`dzzProp317_dzzMuIn_of_C`** (DZZ Proposition 3.17 at `μIn` from the good sets and the crude
  moments).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `Var η_ε(v) ≤ (κ + 4) log δ⁻¹` for `ε ≥ δ^κ`, `0 < δ < 1`, `log δ⁻¹ ≥ 1`. -/
lemma etaVar_le_coarse {κ δ ε : ℝ} (hκ : 0 ≤ κ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hL : 1 ≤ Real.log δ⁻¹) (hε : δ ^ κ ≤ ε) (v : ℂ) :
    etaVar ε v ≤ (κ + 4) * Real.log δ⁻¹ := by
  have hδκ : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ0 κ
  have hδκ1 : δ ^ κ ≤ 1 := Real.rpow_le_one hδ0.le hδ1.le hκ
  set ε' := min ε 1
  have hε' : 0 < ε' := lt_min (hδκ.trans_le hε) one_pos
  have h1 : etaVar ε v ≤ etaVar ε' v := etaVar_anti hε' (min_le_left _ _) v
  have h2 : etaVar ε' v ≤ Real.log ε'⁻¹ + 4 := etaVar_le hε' (min_le_right _ _) v
  have h3 : Real.log ε'⁻¹ ≤ κ * Real.log δ⁻¹ := by
    rw [Real.log_inv, Real.log_inv]
    have := Real.log_le_log hδκ (le_min hε hδκ1)
    rw [Real.log_rpow hδ0] at this
    linarith
  nlinarith

/-- The constant `b₁` of `tildeVar_sub_etaVar_le` (`Var h̃_ε(v) − Var η_ε(v) ≤ b₁`). -/
def coarseB1 : ℝ := Classical.choose tildeVar_sub_etaVar_le

lemma coarseB1_nonneg : 0 ≤ coarseB1 := (Classical.choose_spec tildeVar_sub_etaVar_le).1

/-- `Var h̃_ε(v) ≤ (κ + 4 + b₁) log δ⁻¹` for `ε ≥ δ^κ`, `0 < δ < 1`, `log δ⁻¹ ≥ 1`. -/
lemma tildeVar_le_coarse {κ δ ε : ℝ} (hκ : 0 ≤ κ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hL : 1 ≤ Real.log δ⁻¹) (hε : δ ^ κ ≤ ε) (v : ℂ) :
    tildeVar ε v ≤ (κ + 4 + coarseB1) * Real.log δ⁻¹ := by
  have hε0 : 0 < ε := (Real.rpow_pos_of_pos hδ0 κ).trans_le hε
  have h1 := ((Classical.choose_spec tildeVar_sub_etaVar_le).2 ε hε0 v).2
  have h2 := etaVar_le_coarse hκ hδ0 hδ1 hL hε v
  have h3 := coarseB1_nonneg
  change tildeVar ε v - etaVar ε v ≤ coarseB1 at h1
  nlinarith

/-- The `L²` kernels of the coordinates of `𝒳_δ` (`coarseField = √π W(coarseKernel ·)`). -/
def coarseKernel (κ δ : ℝ) : CoarseIdx κ δ → WNSpace
  | Sum.inl b => etaKernelL2 (Ioi (b.1.side ^ 2)) b.1.center
  | Sum.inr q => wndKernelL2 openSquare (Ioi (q.1.2 ^ 2)) q.1.1

lemma coarseField_eq_sqrtPi (W : WNSpace → Ω → ℝ) (κ δ : ℝ) :
    coarseField W κ δ = fun t ω => Real.sqrt Real.pi * W (coarseKernel κ δ t) ω := by
  funext t ω
  rcases t with b | q <;> rfl

lemma le_of_isCoarseScale {κ δ ε : ℝ} (h : IsCoarseScale κ δ ε) : δ ^ κ ≤ ε := by
  rcases h with h | ⟨n, -, h⟩
  · exact h.ge
  · exact h

/-- **`𝒳_δ` is a centered Gaussian process with variance `O(log δ⁻¹)`** (DZZ l. 1600; the
`η`-coordinates by `etaVar_le`, the `h̃`-coordinates by `tildeVar_sub_etaVar_le`). -/
theorem coarse_gauss (hW : IsWhiteNoise P W) {κ δ : ℝ} (hκ : 0 ≤ κ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hL : 1 ≤ Real.log δ⁻¹) :
    IsGaussianProcess (coarseField W κ δ) P ∧ (∀ t, ∫ ω, coarseField W κ δ t ω ∂P = 0) ∧
      ∀ t, Var[coarseField W κ δ t; P] ≤ (κ + 4 + coarseB1) * Real.log δ⁻¹ := by
  rw [coarseField_eq_sqrtPi]
  refine ⟨isGaussianProcess_sqrtPi hW (coarseKernel κ δ), fun t => integral_sqrtPi hW _,
    fun t => ?_⟩
  rw [variance_sqrtPi hW]
  rcases t with b | q
  · have := etaVar_le_coarse hκ hδ0 hδ1 hL b.2 b.1.center
    have := coarseB1_nonneg
    change etaVar b.1.side b.1.center ≤ _
    nlinarith
  · exact tildeVar_le_coarse hκ hδ0 hδ1 hL (le_of_isCoarseScale q.2.2.2) q.1.1

/-- DZZ's good set `𝒜 ⊆ 𝒜_δ` with (eq-distance-Lip) (see the module docstring). -/
def DZZGoodSet (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (A B : Set ℂ)
    (ℓ τ ε : ℝ) : Prop :=
  ∃ 𝒜 : Set (CoarseIdx (dzzCmc γ) δ → ℝ), 𝒜 ⊆ CoarseGood γ (dzzCmc γ) δ ∧
    P.real {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ 𝒜} ≤ ε ∧
    (∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, (∀ s, |x s - x' s| ≤ ℓ) →
      |coarseLogD γ (dzzCmc γ) δ A B x - coarseLogD γ (dzzCmc γ) δ A B x'| ≤ τ) ∧
    ∃ (n : ℕ) (t : Fin n → CoarseIdx (dzzCmc γ) δ),
      ∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, ∀ s, ∃ i, |x s - x' s| ≤ |x (t i) - x' (t i)| + 1

theorem lipData_of_goodSet (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hL : 1 ≤ Real.log δ⁻¹) {A B : Set ℂ} {ℓ τ ε : ℝ}
    (h : DZZGoodSet P γ W δ A B ℓ τ ε) :
    DZZLipData P γ W δ A B (√((dzzCmc γ + 4 + coarseB1) * Real.log δ⁻¹)) ℓ τ ε := by
  have hκ := dzzCmc_nonneg hγ hγ2
  obtain ⟨hX, h0, hvar⟩ := coarse_gauss hW hκ hδ0 hδ1 hL
  obtain ⟨𝒜, hsub, hε, hlip, n, t, hnet⟩ := h
  refine ⟨CoarseIdx (dzzCmc γ) δ, coarseField W (dzzCmc γ) δ, hX, h0, fun s => ?_, 𝒜,
    coarseLogD γ (dzzCmc γ) δ A B, Eventually.of_forall fun ω hω =>
      logApproxLGD_eq_coarseLogD hδ0.ne' W A B ω (hsub hω), hε, hlip, n, t, hnet⟩
  have := coarseB1_nonneg
  rw [Real.sq_sqrt (by positivity)]
  exact hvar s

/-- **DZZ l. 1572–1594** in terms of `𝒳_δ` (OPEN). -/
def DZZDistLip1C (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (ξ : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B →
    ∀ ι ∈ Ioo (0 : ℝ) 1, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      DZZGoodSet P γ W δ (A δ) (B δ) (a * ι * Real.log δ⁻¹) (ι * Real.log δ⁻¹) (δ ^ (a * ι))

/-- **DZZ l. 1631–1645** in terms of `𝒳_δ` (OPEN). -/
def DZZDistLip2C (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (ξ : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      DZZGoodSet P γ W δ (A δ) (B δ) (Real.log δ⁻¹ ^ (0.9 : ℝ)) (Real.log δ⁻¹ ^ (0.93 : ℝ))
        (δ ^ a)

lemma small_delta {δ₀ δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) (min δ₀ (Real.exp (-1)))) :
    δ ∈ Ioo (0 : ℝ) δ₀ ∧ δ < 1 ∧ 1 ≤ Real.log δ⁻¹ := by
  have h1 : δ < Real.exp (-1) := hδ.2.trans_le (min_le_right _ _)
  have h2 : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  refine ⟨⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩, h1.trans h2, ?_⟩
  have := Real.log_lt_log hδ.1 h1
  rw [Real.log_exp] at this
  rw [Real.log_inv]; linarith

theorem dzzDistLip1_of_C (hW : IsWhiteNoise P W) {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : DZZDistLip1C P γ W ξ) : DZZDistLip1 P γ W ξ := by
  obtain ⟨a, ha, h⟩ := h
  have hκ := dzzCmc_nonneg hγ hγ2
  have hb := coarseB1_nonneg
  refine ⟨a, dzzCmc γ + 4 + coarseB1, ha, by linarith, fun A B hAB ι hι => ?_⟩
  obtain ⟨δ₀, hδ₀, hD⟩ := h A B hAB ι hι
  refine ⟨min δ₀ (Real.exp (-1)), lt_min hδ₀ (Real.exp_pos _), fun δ hδ => ?_⟩
  obtain ⟨hδa, hδ1, hL⟩ := small_delta hδ
  exact lipData_of_goodSet hW hγ hγ2 hδ.1 hδ1 hL (hD δ hδa)

theorem dzzDistLip2_of_C (hW : IsWhiteNoise P W) {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : DZZDistLip2C P γ W ξ) : DZZDistLip2 P γ W ξ := by
  obtain ⟨a, ha, h⟩ := h
  have hκ := dzzCmc_nonneg hγ hγ2
  have hb := coarseB1_nonneg
  refine ⟨a, dzzCmc γ + 4 + coarseB1, ha, by linarith, fun A B hAB => ?_⟩
  obtain ⟨δ₀, hδ₀, hD⟩ := h A B hAB
  refine ⟨min δ₀ (Real.exp (-1)), lt_min hδ₀ (Real.exp_pos _), fun δ hδ => ?_⟩
  obtain ⟨hδa, hδ1, hL⟩ := small_delta hδ
  exact lipData_of_goodSet hW hγ hγ2 hδ.1 hδ1 hL (hD δ hδa)

end DZZ
end LQGMetric
