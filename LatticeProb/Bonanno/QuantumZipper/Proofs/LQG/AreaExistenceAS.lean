/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.AreaExistenceAS at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceVague
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn

/-!
# M4-A1, part 2: almost sure existence of the area measure of the free field

Blueprint node M4-A1 (`blueprint/M4_BLUEPRINT.md`).

* `ae_tendsto_of_L1_rate`: summable `L¹` increments give almost sure convergence.
* `ae_tendsto_areaApprox_aZ`: for each test function `f` supported in `ℍ ∩ B(0,R-1)`,
  `∫ f d(areaApprox γ Z k)` converges a.s. (`Z = X − X(fc(0,R))`).
* `ae_areaApprox_aZ_eq`: a.s., `areaApprox γ Z k = e^{-γ X(fc(0,R))} • areaApprox γ X k`.
* `ae_exists_isVagueLimitOn_areaApprox`: **a.s. `areaApprox γ X` has a vague limit on `ℍ`**, and
  `ae_isVagueLimitOn_qAreaMeasure`: a.s. it is `qAreaMeasure γ X`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace AreaExist

open VagueH

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- Summable `L¹` increments (geometric rate from `k₀` on) give a.s. convergence. -/
theorem ae_tendsto_of_L1_rate {G : ℕ → Ω → ℝ} {k₀ : ℕ} {C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hint : ∀ k, k₀ ≤ k → Integrable (G k) P)
    (hstep : ∀ k, k₀ ≤ k → ∫ ω, |G (k + 1) ω - G k ω| ∂P ≤ C * q ^ k) :
    ∀ᵐ ω ∂P, ∃ l, Tendsto (fun k => G k ω) atTop (𝓝 l) := by
  set F : ℕ → Ω → ℝ := fun k ω => |G (k + k₀ + 1) ω - G (k + k₀) ω| with hF
  have hFi : ∀ k, Integrable (F k) P := fun k =>
    ((hint _ (by omega)).sub (hint _ (by omega))).abs
  have hFb : ∀ k, ∫ ω, F k ω ∂P ≤ C * q ^ (k + k₀) := fun k => hstep _ (by omega)
  have hsum : Summable fun k : ℕ => C * q ^ (k + k₀) := by
    have := (summable_geometric_of_lt_one hq0 hq1).mul_left (C * q ^ k₀)
    refine this.congr fun k => ?_
    rw [pow_add]; ring
  have hlin : ∫⁻ ω, ∑' k, ENNReal.ofReal (F k ω) ∂P ≠ ∞ := by
    rw [lintegral_tsum fun k => (hFi k).aemeasurable.ennreal_ofReal]
    have e : ∀ k, ∫⁻ ω, ENNReal.ofReal (F k ω) ∂P = ENNReal.ofReal (∫ ω, F k ω ∂P) := fun k =>
      (ofReal_integral_eq_lintegral_ofReal (hFi k) (ae_of_all _ fun ω => abs_nonneg _)).symm
    simp_rw [e]
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' k : ℕ, C * q ^ (k + k₀))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => ?_) hsum]
    · exact ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (hFb k)
    · exact (integral_nonneg fun ω => abs_nonneg _).trans (hFb k)
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum fun k => (hFi k).aemeasurable.ennreal_ofReal)
    hlin
  filter_upwards [hae] with ω hω
  have hs : Summable fun k => F k ω := by
    have := ENNReal.summable_toReal hω.ne
    refine this.congr fun k => ?_
    exact ENNReal.toReal_ofReal (abs_nonneg _)
  have hc : CauchySeq fun k => G (k + k₀) ω := by
    refine cauchySeq_of_summable_dist (hs.congr fun k => ?_)
    rw [Real.dist_eq, abs_sub_comm]
    simp only [hF, Nat.succ_eq_add_one]
    ring_nf
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨l, (tendsto_add_atTop_iff_nat k₀).1 hl⟩

variable [IsProbabilityMeasure P]

/-- For each test function supported in `ℍ ∩ {‖z‖ + 1 ≤ R}`, `∫ f dμ_k(Z)` converges a.s. -/
theorem ae_tendsto_areaApprox_aZ (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {R : ℝ} {f : ℂ → ℝ} (hf : IsTestH f)
    (hfR : ∀ z ∈ tsupport f, ‖z‖ + 1 ≤ R) :
    ∀ᵐ ω ∂P, ∃ l, Tendsto (fun k => ∫ z, f z ∂(areaApprox γ (aZ X R ω) k)) atTop (𝓝 l) := by
  obtain ⟨C, -, k₀, hint, hC⟩ := areaApprox_L1_rate hX hγ hγ2 hf.1 hf.2.1 hf.2.2 hfR
  set q := exp (-areaRate γ * log 2) with hq
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (mul_neg_of_neg_of_pos
    (neg_neg_of_pos (areaRate_pos hγ hγ2)) (log_pos one_lt_two))
  refine ae_tendsto_of_L1_rate (C := C) (exp_pos _).le hq1 hint fun k hk => ?_
  have := hC k (k + 1) hk (Nat.le_succ k)
  convert this using 1
  rw [← exp_nat_mul]; congr 2; ring

omit [IsProbabilityMeasure P] in
/-- The additive constant: a.s., `areaApprox γ Z k = e^{-γ X(fc(0,R))} • areaApprox γ X k`
for every `k`. -/
theorem ae_areaApprox_aZ_eq (hX : IsFreeGFFModConstH X P) (γ R : ℝ) :
    ∀ᵐ ω ∂P, ∀ k, areaApprox γ (aZ X R ω) k =
      ENNReal.ofReal (exp (-(γ * X ω (foldedCircle 0 R)))) • areaApprox γ (X ω) k := by
  filter_upwards [ae_all_iff.2 fun k => ae_avgReg_aZ hX R k] with ω hω k
  unfold areaApprox
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem isOpen_H.measurableSet] with z hz
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hω k z (H_subset_Hbar hz), ← ENNReal.ofReal_mul (exp_pos _).le]
  congr 1
  rw [mul_sub, sub_eq_add_neg, exp_add]
  ring

/-- Height used on `K_n`. -/
def dK (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 1))

theorem dK_spec (n : ℕ) : 0 < dK n ∧ 2 * dK n ≤ 1 ∧ ∀ z ∈ Kset n, dK n ≤ z.im := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  refine ⟨by unfold dK; positivity, ?_, fun z hz => le_trans ?_ hz.2⟩
  · unfold dK
    rw [show 2 * (1 / (2 * ((n : ℝ) + 1))) = 1 / ((n : ℝ) + 1) by field_simp]
    exact (div_le_one (by positivity)).2 h1
  · unfold dK
    apply one_div_le_one_div_of_le (by positivity); linarith

theorem Kset_R (n : ℕ) : ∀ z ∈ Kset n, ‖z‖ + 1 ≤ (n : ℝ) + 1 := fun z hz => by
  linarith [hz.1]

/-- A.s. `areaApprox γ Z k` is finite on `K_n` (for `R = n + 1` and `2^{-k} ≤ d_n`). -/
theorem ae_areaApprox_aZ_Kset_lt_top (hX : IsFreeGFFModConstH X P) (γ : ℝ) (n : ℕ) {k : ℕ}
    (hk : radius k ≤ dK n) :
    ∀ᵐ ω ∂P, areaApprox γ (aZ X ((n : ℝ) + 1) ω) k (Kset n) < ∞ := by
  obtain ⟨-, hd1, hSd⟩ := dK_spec n
  have hS : MeasurableSet (Kset n) := (isCompact_Kset n).isClosed.measurableSet
  have hint := integrable_fDensA (P := P) hX hS (isCompact_Kset n).measure_lt_top hd1 (Kset_R n)
    hSd γ (f := (Kset n).indicator 1) (measurable_one.indicator hS) (M := 1)
    (fun z => by
      by_cases hz : z ∈ Kset n
      · simp [indicator_of_mem hz]
      · simp [indicator_of_notMem hz]) hk
  filter_upwards [hint.prod_right_ae] with ω hω
  have e : areaApprox γ (aZ X ((n : ℝ) + 1) ω) k (Kset n) =
      ∫⁻ z in Kset n, ENNReal.ofReal ((Kset n).indicator 1 z *
        aDens γ X ((n : ℝ) + 1) k z ω) := by
    unfold areaApprox
    rw [withDensity_apply _ hS, Measure.restrict_restrict hS,
      inter_eq_left.2 (Kset_subset_H n)]
    refine setLIntegral_congr_fun hS fun z hz => ?_
    rw [indicator_of_mem hz, Pi.one_apply, one_mul]
    rfl
  rw [e]
  exact hω.lintegral_lt_top

/-- **M4-A1 (2): almost surely the approximating area measures of the free field converge
vaguely on `ℍ`.** -/
theorem ae_exists_isVagueLimitOn_areaApprox (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∃ μ, IsVagueLimitOn H (areaApprox γ (X ω)) μ := by
  obtain ⟨F, hFc, hF⟩ := exists_denseTestFamily
  have hscale := ae_all_iff.2 fun n : ℕ => ae_areaApprox_aZ_eq (P := P) hX γ ((n : ℝ) + 1)
  have hfinZ : ∀ᵐ ω ∂P, ∀ n k : ℕ, radius k ≤ dK n →
      areaApprox γ (aZ X ((n : ℝ) + 1) ω) k (Kset n) < ∞ := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro k
    by_cases hk : radius k ≤ dK n
    · filter_upwards [ae_areaApprox_aZ_Kset_lt_top hX γ n hk] with ω h _ using h
    · exact ae_of_all _ fun ω h => absurd h hk
  have hconv : ∀ᵐ ω ∂P, ∀ f ∈ F,
      ∃ l, Tendsto (fun k => ∫ z, f z ∂(areaApprox γ (X ω) k)) atTop (𝓝 l) := by
    rw [ae_ball_iff hFc]
    intro f hfF
    have hf := hF.1 f hfF
    obtain ⟨n, hn⟩ := exists_Kset hf.2.1 hf.2.2
    filter_upwards [ae_tendsto_areaApprox_aZ hX hγ hγ2 hf (R := (n : ℝ) + 1)
      (fun z hz => Kset_R n z (hn hz)), hscale] with ω ⟨l, hl⟩ hsc
    set e := exp (-(γ * X ω (foldedCircle 0 ((n : ℝ) + 1)))) with he
    have he0 : 0 < e := exp_pos _
    refine ⟨e⁻¹ * l, ?_⟩
    refine (hl.const_mul e⁻¹).congr fun k => ?_
    rw [hsc n k, integral_smul_measure, ENNReal.toReal_ofReal he0.le, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ he0.ne', one_mul]
  have hfin : ∀ᵐ ω ∂P, ∀ K, IsCompact K → K ⊆ H →
      ∀ᶠ k in atTop, areaApprox γ (X ω) k K < ∞ := by
    filter_upwards [hfinZ, hscale] with ω hω hsc K hK hKH
    obtain ⟨n, hn⟩ := exists_Kset hK hKH
    obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one (dK_spec n).1 (show (2 : ℝ)⁻¹ < 1 by norm_num)
    refine eventually_atTop.2 ⟨k₀, fun k hk => ?_⟩
    have h1 := hω n k ((aradius_anti hk).trans hk₀.le)
    rw [hsc n k, Measure.smul_apply, smul_eq_mul] at h1
    have hc0 : ENNReal.ofReal (exp (-(γ * X ω (foldedCircle 0 ((n : ℝ) + 1))))) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (exp_pos _)).ne'
    have h2 : areaApprox γ (X ω) k (Kset n) < ∞ := by
      rcases ENNReal.mul_lt_top_iff.1 h1 with h | h | h
      · exact h.2
      · exact absurd h hc0
      · rw [h]; exact ENNReal.zero_lt_top
    exact (measure_mono hn).trans_lt h2
  filter_upwards [hconv, hfin] with ω h1 h2
  exact exists_isVagueLimitOn_of_family h2 hF h1

/-- **M4-A1 (2), with the chosen limit:** almost surely `qAreaMeasure γ X` is a vague limit of
`areaApprox γ X` on `ℍ` (in particular it is the unique such limit). -/
theorem ae_isVagueLimitOn_qAreaMeasure (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, IsVagueLimitOn H (areaApprox γ (X ω)) (qAreaMeasure γ (X ω)) := by
  filter_upwards [ae_exists_isVagueLimitOn_areaApprox hX hγ hγ2] with ω ⟨μ, hμ⟩
  rwa [qAreaMeasure_eq hμ]

/-- The same for the normalized field `Z = X − X(fc(0,R))`, for any `R`. -/
theorem ae_isVagueLimitOn_qAreaMeasure_aZ (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (R : ℝ) :
    ∀ᵐ ω ∂P, IsVagueLimitOn H (areaApprox γ (aZ X R ω)) (qAreaMeasure γ (aZ X R ω)) := by
  filter_upwards [ae_exists_isVagueLimitOn_areaApprox hX hγ hγ2,
    ae_areaApprox_aZ_eq (P := P) hX γ R] with ω ⟨μ, h0, hK, ht⟩ hsc
  set c := ENNReal.ofReal (exp (-(γ * X ω (foldedCircle 0 R)))) with hc
  have hμ : IsVagueLimitOn H (areaApprox γ (aZ X R ω)) (c • μ) := by
    refine ⟨by rw [Measure.smul_apply, h0, smul_zero], fun K hKc hKH => ?_,
      fun f hf hfc hfH => ?_⟩
    · rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hK K hKc hKH)
    · simp_rw [hsc, integral_smul_measure]
      exact (ht f hf hfc hfH).const_smul _
  rwa [qAreaMeasure_eq hμ]

omit [IsProbabilityMeasure P] in
/-- Fatou step: an `L¹` Cauchy bound passes to the a.s. limit. -/
theorem integral_abs_sub_lim_le {G : ℕ → Ω → ℝ} {L : Ω → ℝ} {k₀ : ℕ} {B : ℕ → ℝ}
    (hint : ∀ k, k₀ ≤ k → Integrable (G k) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (L ω)))
    (hB : ∀ k k', k₀ ≤ k → k ≤ k' → ∫ ω, |G k' ω - G k ω| ∂P ≤ B k) {k : ℕ} (hk : k₀ ≤ k) :
    Integrable (fun ω => G k ω - L ω) P ∧ ∫ ω, |G k ω - L ω| ∂P ≤ B k := by
  have hB0 : 0 ≤ B k := (integral_nonneg fun _ => abs_nonneg _).trans (hB k k hk le_rfl)
  have hlim' : ∀ᵐ ω ∂P, Tendsto (fun i => G (i + k) ω) atTop (𝓝 (L ω)) := by
    filter_upwards [hlim] with ω hω using (tendsto_add_atTop_iff_nat k).2 hω
  have hL : AEStronglyMeasurable L P :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun i => (hint (i + k) (by omega)).aestronglyMeasurable) hlim'
  have hmeas : AEStronglyMeasurable (fun ω => G k ω - L ω) P :=
    (hint k hk).aestronglyMeasurable.sub hL
  have hfi : ∀ i, Integrable (fun ω => |G (i + k) ω - G k ω|) P := fun i =>
    ((hint (i + k) (by omega)).sub (hint k hk)).abs
  have hlin : ∫⁻ ω, ENNReal.ofReal |G k ω - L ω| ∂P ≤ ENNReal.ofReal (B k) := by
    calc ∫⁻ ω, ENNReal.ofReal |G k ω - L ω| ∂P
        = ∫⁻ ω, liminf (fun i => ENNReal.ofReal |G (i + k) ω - G k ω|) atTop ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlim'] with ω hω
          have ht : Tendsto (fun i => ENNReal.ofReal |G (i + k) ω - G k ω|) atTop
              (𝓝 (ENNReal.ofReal |L ω - G k ω|)) :=
            (ENNReal.continuous_ofReal.tendsto _).comp
              ((continuous_abs.tendsto _).comp (hω.sub_const _))
          rw [ht.liminf_eq, abs_sub_comm]
      _ ≤ liminf (fun i => ∫⁻ ω, ENNReal.ofReal |G (i + k) ω - G k ω| ∂P) atTop :=
          lintegral_liminf_le' fun i => (hfi i).aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal (B k) := by
          refine liminf_le_of_frequently_le' (Eventually.frequently
            (Eventually.of_forall fun i => ?_))
          rw [← ofReal_integral_eq_lintegral_ofReal (hfi i)
            (ae_of_all _ fun _ => abs_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hB k (i + k) hk (by omega))
  have hfin : HasFiniteIntegral (fun ω => G k ω - L ω) P := by
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨⟨hmeas, hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => abs_nonneg _)
    (continuous_abs.comp_aestronglyMeasurable hmeas)]
  exact ENNReal.toReal_le_of_le_ofReal hB0 hlin

/-- **M4-A1 (2), `L¹` rate to the limit:** for `f` a test function supported in
`ℍ ∩ {‖z‖ + 1 ≤ R}`, `E|∫ f d(areaApprox γ Z k) − ∫ f d(qAreaMeasure γ Z)| ≤ C e^{-β k log 2}`
for `k ≥ k₀`, `Z = X − X(fc(0,R))`, `β = areaRate γ`. -/
theorem areaApprox_L1_rate_limit (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {R : ℝ} {f : ℂ → ℝ} (hf : IsTestH f)
    (hfR : ∀ z ∈ tsupport f, ‖z‖ + 1 ≤ R) :
    ∃ C, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∫ ω, |∫ z, f z ∂(areaApprox γ (aZ X R ω) k) -
        ∫ z, f z ∂(qAreaMeasure γ (aZ X R ω))| ∂P ≤ C * exp (-areaRate γ * (k * log 2)) := by
  obtain ⟨C, hC0, k₀, hint, hC⟩ := areaApprox_L1_rate hX hγ hγ2 hf.1 hf.2.1 hf.2.2 hfR
  refine ⟨C, hC0, k₀, fun k hk => (integral_abs_sub_lim_le hint ?_ hC hk).2⟩
  filter_upwards [ae_isVagueLimitOn_qAreaMeasure_aZ hX hγ hγ2 R] with ω hω
  exact hω.2.2 f hf.1 hf.2.1 hf.2.2

end AreaExist
end QuantumZipper
