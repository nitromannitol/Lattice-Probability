/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcW4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcW3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcK

/-!
# Walled Lipschitz data: `DZZDistLip{1,2}In` at a dyadic wall (P2-DZZCONCW)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`), proof of Prop 3.17, l. 1555–1594 and 1631–1645,
for `D'_S`, `S = cellsInside B` (Remark 5.2; D117, D123).

* `DZZLipDataOn`, `DZZDistLip1In`, `DZZDistLip2In`: `DZZLipData`, `DZZDistLip{1,2}` (S3ConcC)
  with `logApproxLGDOn S` (S3P317E) and the pairs inside `B̄^ξ`;
* `DZZGoodSetOn`, `lipDataOn_of_goodSetOn`: copies of `DZZGoodSet`, `lipData_of_goodSet`
  (S3ConcG) with `coarseLogDOn S` and `logApproxLGDOn_eq_coarseLogDOn` (S3ConcI0);
* `goodSetOn_of_core_net`: copy of `goodSet_of_core_net` (S3ConcH);
* **`dzzDistLip1In_of_core`**, **`dzzDistLip2In_of_core`**: copies of `dzzDistLip{1,2}C_of_core`
  (S3ConcH) composed with `dzzDistLip{1,2}_of_C` (S3ConcG); the regularity `DZZCoarseReg`
  (S3ConcH, proved as `dzzCoarseReg`, S3ConcK) is wall-independent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `DZZLipData` (S3ConcC) for `D'_S`. -/
def DZZLipDataOn (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (S : Set DyBox) (δ : ℝ)
    (A B : Set ℂ) (σ ℓ τ ε : ℝ) : Prop :=
  ∃ (T : Type) (X : T → Ω → ℝ), IsGaussianProcess X P ∧ (∀ t, ∫ ω, X t ω ∂P = 0) ∧
    (∀ t, Var[X t; P] ≤ σ ^ 2) ∧ ∃ (𝒜 : Set (T → ℝ)) (F : (T → ℝ) → ℝ),
      (∀ᵐ ω ∂P, (fun s => X s ω) ∈ 𝒜 → logApproxLGDOn S γ W δ A B ω = F (fun s => X s ω)) ∧
      P.real {ω | (fun s => X s ω) ∉ 𝒜} ≤ ε ∧
      (∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, (∀ s, |x s - x' s| ≤ ℓ) → |F x - F x'| ≤ τ) ∧
      ∃ (n : ℕ) (t : Fin n → T),
        ∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, ∀ s, ∃ i, |x s - x' s| ≤ |x (t i) - x' (t i)| + 1

/-- **DZZ l. 1555–1594, walled at `B̄`** (`DZZDistLip1`, S3ConcC). -/
def DZZDistLip1In (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (Bw : DyBox) (ξ : ℝ) : Prop :=
  ∃ a K : ℝ, 0 < a ∧ 0 < K ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B → InsideXi Bw ξ A B →
    ∀ ι ∈ Ioo (0 : ℝ) 1, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      DZZLipDataOn P γ W (cellsInside Bw) δ (A δ) (B δ) (√(K * Real.log δ⁻¹))
        (a * ι * Real.log δ⁻¹) (ι * Real.log δ⁻¹) (δ ^ (a * ι))

/-- **DZZ l. 1631–1645, walled at `B̄`** (`DZZDistLip2`, S3ConcC). -/
def DZZDistLip2In (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (Bw : DyBox) (ξ : ℝ) : Prop :=
  ∃ a K : ℝ, 0 < a ∧ 0 < K ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B → InsideXi Bw ξ A B →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      DZZLipDataOn P γ W (cellsInside Bw) δ (A δ) (B δ) (√(K * Real.log δ⁻¹))
        (Real.log δ⁻¹ ^ (0.9 : ℝ)) (Real.log δ⁻¹ ^ (0.93 : ℝ)) (δ ^ a)

/-- `DZZGoodSet` (S3ConcG) for `D'_S`. -/
def DZZGoodSetOn (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (S : Set DyBox) (δ : ℝ)
    (A B : Set ℂ) (ℓ τ ε : ℝ) : Prop :=
  ∃ 𝒜 : Set (CoarseIdx (dzzCmc γ) δ → ℝ), 𝒜 ⊆ CoarseGood γ (dzzCmc γ) δ ∧
    P.real {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ 𝒜} ≤ ε ∧
    (∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, (∀ s, |x s - x' s| ≤ ℓ) →
      |coarseLogDOn S γ (dzzCmc γ) δ A B x - coarseLogDOn S γ (dzzCmc γ) δ A B x'| ≤ τ) ∧
    ∃ (n : ℕ) (t : Fin n → CoarseIdx (dzzCmc γ) δ),
      ∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, ∀ s, ∃ i, |x s - x' s| ≤ |x (t i) - x' (t i)| + 1

/-- Copy of `lipData_of_goodSet` (S3ConcG) for `D'_S`. -/
theorem lipDataOn_of_goodSetOn (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {S : Set DyBox} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hL : 1 ≤ Real.log δ⁻¹) {A B : Set ℂ}
    {ℓ τ ε : ℝ} (h : DZZGoodSetOn P γ W S δ A B ℓ τ ε) :
    DZZLipDataOn P γ W S δ A B (√((dzzCmc γ + 4 + coarseB1) * Real.log δ⁻¹)) ℓ τ ε := by
  have hκ := dzzCmc_nonneg hγ hγ2
  obtain ⟨hX, h0, hvar⟩ := coarse_gauss hW hκ hδ0 hδ1 hL
  obtain ⟨𝒜, hsub, hε, hlip, n, t, hnet⟩ := h
  refine ⟨CoarseIdx (dzzCmc γ) δ, coarseField W (dzzCmc γ) δ, hX, h0, fun s => ?_, 𝒜,
    coarseLogDOn S γ (dzzCmc γ) δ A B, Eventually.of_forall fun ω hω =>
      logApproxLGDOn_eq_coarseLogDOn S hδ0.ne' W A B ω (hsub hω), hε, hlip, n, t, hnet⟩
  have := coarseB1_nonneg
  rw [Real.sq_sqrt (by positivity)]
  exact hvar s

/-- Copy of `goodSet_of_core_net` (S3ConcH) for `D'_S`. -/
theorem goodSetOn_of_core_net [IsFiniteMeasure P] {γ δ : ℝ} {S : Set DyBox} {A B : Set ℂ}
    {ℓ ℓ' τ ε₁ ε₂ ε : ℝ} (hc : DZZGoodCoreOn P γ W S δ A B ℓ τ ε₁) (hr : CoarseNet P γ W δ ε₂)
    (hℓ : ℓ' ≤ ℓ) (hε : ε₁ + ε₂ ≤ ε) : DZZGoodSetOn P γ W S δ A B ℓ' τ ε := by
  obtain ⟨𝒜, hsub, h𝒜, hlip⟩ := hc
  obtain ⟨ℛ, hℛ, n, t, hnet⟩ := hr
  refine ⟨𝒜 ∩ ℛ, fun x hx => hsub hx.1, ?_, fun x hx x' hx' hxx =>
    hlip x hx.1 x' hx'.1 fun s => (hxx s).trans hℓ, n, t, fun x hx x' hx' => hnet x hx.2 x' hx'.2⟩
  have h1 := measureReal_mono (μ := P)
    (s₁ := {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ 𝒜 ∩ ℛ})
    (s₂ := {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ 𝒜} ∪
      {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ ℛ})
    (fun ω hω => by
      simp only [mem_setOf_eq, mem_inter_iff, not_and_or] at hω
      exact hω) (measure_ne_top P _)
  have h2 := measureReal_union_le (μ := P)
    {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ 𝒜}
    {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ ℛ}
  linarith

/-- **`DZZDistLip1In`** from the walled good sets and the regularity of `𝒳_δ` (copies of
`dzzDistLip1C_of_core`, S3ConcH, and `dzzDistLip1_of_C`, S3ConcG). -/
theorem dzzDistLip1In_of_core (hW : IsWhiteNoise P W) {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Bw : DyBox} (hreg : DZZCoarseReg P γ W) (h : DZZDistLip1CoreIn P γ W Bw ξ) :
    DZZDistLip1In P γ W Bw ξ := by
  have := hW.isProbabilityMeasure
  obtain ⟨a, ha, h⟩ := h
  have hκ := dzzCmc_nonneg hγ hγ2
  have hb := coarseB1_nonneg
  refine ⟨a / 2, dzzCmc γ + 4 + coarseB1, by positivity, by linarith, fun A B hAB hin ι hι => ?_⟩
  obtain ⟨δ₀, hδ₀, hD⟩ := h A B hAB hin ι hι
  obtain ⟨δ₂, hδ₂, h2⟩ := two_rpow_le (x := a * ι) (mul_pos ha hι.1)
  refine ⟨min (min δ₀ δ₂) (Real.exp (-1)), lt_min (lt_min hδ₀ hδ₂) (Real.exp_pos _),
    fun δ hδ => ?_⟩
  obtain ⟨hδa', hδ1, hL⟩ := small_delta hδ
  have hδa : δ < δ₀ := hδa'.2.trans_le (min_le_left _ _)
  have hδb : δ < δ₂ := hδa'.2.trans_le (min_le_right _ _)
  have hL0 : 0 ≤ Real.log δ⁻¹ := by linarith
  refine lipDataOn_of_goodSetOn hW hγ hγ2 hδ.1 hδ1 hL (goodSetOn_of_core_net (hD δ ⟨hδ.1, hδa⟩)
    (hreg δ ⟨hδ.1, hδ1⟩ (δ ^ (a * ι)) (Real.rpow_pos_of_pos hδ.1 _)) ?_ ?_)
  · have : a / 2 * ι ≤ a * ι := by nlinarith [hι.1]
    exact mul_le_mul_of_nonneg_right this hL0
  · have e : a / 2 * ι = a * ι / 2 := by ring
    rw [e]; exact h2 δ ⟨hδ.1, hδb⟩

/-- **`DZZDistLip2In`** from the walled good sets and the regularity of `𝒳_δ` (copies of
`dzzDistLip2C_of_core`, S3ConcH, and `dzzDistLip2_of_C`, S3ConcG). -/
theorem dzzDistLip2In_of_core (hW : IsWhiteNoise P W) {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Bw : DyBox} (hreg : DZZCoarseReg P γ W) (h : DZZDistLip2CoreIn P γ W Bw ξ) :
    DZZDistLip2In P γ W Bw ξ := by
  have := hW.isProbabilityMeasure
  obtain ⟨a, ha, h⟩ := h
  have hκ := dzzCmc_nonneg hγ hγ2
  have hb := coarseB1_nonneg
  refine ⟨a / 2, dzzCmc γ + 4 + coarseB1, by positivity, by linarith, fun A B hAB hin => ?_⟩
  obtain ⟨δ₀, hδ₀, hD⟩ := h A B hAB hin
  obtain ⟨δ₂, hδ₂, h2⟩ := two_rpow_le ha
  refine ⟨min (min δ₀ δ₂) (Real.exp (-1)), lt_min (lt_min hδ₀ hδ₂) (Real.exp_pos _),
    fun δ hδ => ?_⟩
  obtain ⟨hδa', hδ1, hL⟩ := small_delta hδ
  have hδa : δ < δ₀ := hδa'.2.trans_le (min_le_left _ _)
  have hδb : δ < δ₂ := hδa'.2.trans_le (min_le_right _ _)
  exact lipDataOn_of_goodSetOn hW hγ hγ2 hδ.1 hδ1 hL (goodSetOn_of_core_net (hD δ ⟨hδ.1, hδa⟩)
    (hreg δ ⟨hδ.1, hδ1⟩ (δ ^ a) (Real.rpow_pos_of_pos hδ.1 _)) le_rfl (h2 δ ⟨hδ.1, hδb⟩))

end DZZ
end LQGMetric
