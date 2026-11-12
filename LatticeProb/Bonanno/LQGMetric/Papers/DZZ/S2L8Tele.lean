/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L8Tele at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L8Sum
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Tele

/-!
# DZZ Lemma 2.8 (`lem-hat-h-eta`; task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 594–609:
`P(max_{v ∈ 𝕍^ξ} max_{j ≥ 0} |ĥ^1_{2^{-j}}(v) − η_{2^{-j}}(v)| ≥ λ) ≤ C e^{−λ²/C}`, `C = C(ξ)`.
`hat_telescope`: `ĥ^1_{2^{-j}} − η_{2^{-j}} = Σ_{i ≤ j} Δ_i` a.s. (bands of `ĥ` by `phi_add_ae`, of `η` by
`etaKernelL2_split`); `dzz_lemma28`: the lemma for continuous versions, modulo `BridgeShellBound`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma phiKernelL2_one_one (x : ℂ) : phiKernelL2 1 1 x = 0 := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff, ← real_inner_self_eq_norm_sq,
    inner_phiKernelL2 1 1 one_pos x x, integral_Icc_eq_integral_Ioc]
  simp

/-- `ĥ^1_{2^{-j}}(x) − η_{2^{-j}}(x) = Σ_{i ≤ j} Δ_i(x)` a.s. (DZZ l. 604, as l. 573–574). -/
theorem hat_telescope (hW : IsWhiteNoise P W) (j : ℕ) (x : ℂ) :
    (fun ω => phi W ((1 / 2 : ℝ) ^ j) 1 x ω - etaInf W ((1 / 2 : ℝ) ^ j) x ω) =ᵐ[P]
      fun ω => ∑ i ∈ Finset.range (j + 1), Real.sqrt Real.pi * W (hatDeltaKernel i x) ω := by
  induction j with
  | zero =>
    have hk0 : hatDeltaKernel 0 x = (-1 : ℝ) • etaKernelL2 (Ioi ((1 : ℝ) ^ 2)) x := by
      simp [hatDeltaKernel, bandSet]
    have h0 := hW.smul_ae 0 (0 : WNSpace)
    have h1 := hW.smul_ae (-1) (etaKernelL2 (Ioi ((1 : ℝ) ^ 2)) x)
    filter_upwards [h0, h1] with ω e0 e1
    have e0' : W 0 ω = 0 := by rw [smul_zero] at e0; linarith
    simp only [pow_zero, zero_add, Finset.range_one, Finset.sum_singleton]
    rw [hk0, e1]
    simp only [phi, phiKernelL2_one_one, e0', etaInf, etaField, one_pow]
    ring
  | succ j ih =>
    have ha : (0 : ℝ) < (1 / 2) ^ (j + 1) := by positivity
    have hab : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2) ^ j :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ j)
    have hb1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have ha' : (0 : ℝ) < ((1 / 2 : ℝ) ^ (j + 1)) ^ 2 := by positivity
    have hle : ((1 / 2 : ℝ) ^ (j + 1)) ^ 2 ≤ ((1 / 2 : ℝ) ^ j) ^ 2 :=
      pow_le_pow_left₀ ha.le hab 2
    have e1 := phi_add_ae hW ha hab hb1 x
    have e2 := hW.add_ae (etaKernelL2 (Ioi (((1 / 2 : ℝ) ^ j) ^ 2)) x)
      (etaKernelL2 (Ioo (((1 / 2 : ℝ) ^ (j + 1)) ^ 2) (((1 / 2 : ℝ) ^ j) ^ 2)) x)
    have e3 := hW.add_ae (phiKernelL2 ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j) x)
      (-etaKernelL2 (bandSet (j + 1)) x)
    have e4 := hW.smul_ae (-1) (etaKernelL2 (bandSet (j + 1)) x)
    filter_upwards [ih, e1, e2, e3, e4] with ω h0 h1 h2 h3 h4
    rw [Finset.sum_range_succ, ← h0, h1]
    have hk : hatDeltaKernel (j + 1) x = phiKernelL2 ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j) x +
        -etaKernelL2 (bandSet (j + 1)) x := by
      simp [hatDeltaKernel, sub_eq_add_neg]
    rw [hk, h3, ← neg_one_smul ℝ (etaKernelL2 (bandSet (j + 1)) x), h4]
    have hbs : bandSet (j + 1) = Ioo (((1 / 2 : ℝ) ^ (j + 1)) ^ 2) (((1 / 2 : ℝ) ^ j) ^ 2) := by
      simp [bandSet]
    simp only [etaInf, etaField, phi]
    rw [etaKernelL2_split ha' hle, h2, hbs]
    ring

universe u

/-- **DZZ Lemma 2.8** (`lem-hat-h-eta`, l. 594–609), assuming `BridgeShellBound`: for
`ξ ∈ (0, 1/2)` and continuous versions `Z_j` of `ĥ^1_{2^{-j}} − η_{2^{-j}}`,
`P(max_{v ∈ 𝕍^ξ} max_j |Z_j(v)| ≥ λ) ≤ C e^{−λ²/C}`, `C = C(ξ)`. -/
theorem dzz_lemma28 {C₀ : ℝ} (hC0 : 0 ≤ C₀) (hC : BridgeShellBound C₀) {ξ : ℝ} (hξ : 0 < ξ)
    (hξ2 : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ Z : ℕ → ℂ → Ω → ℝ,
      (∀ j ω, Continuous fun x => Z j x ω) →
      (∀ j x, Z j x =ᵐ[P] fun ω => phi W ((1 / 2 : ℝ) ^ j) 1 x ω -
        etaInf W ((1 / 2 : ℝ) ^ j) x ω) →
      ∀ lam : ℝ, 0 ≤ lam →
        P.real {ω | ∃ v ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ), ∃ j : ℕ, lam ≤ |Z j v ω|} ≤
          C * Real.exp (-lam ^ 2 / C) := by
  obtain ⟨C, hCpos, hsum⟩ := dzz_lemma28_sum.{u} hC0 hC hξ hξ2
  refine ⟨C, hCpos, fun {Ω} _ {P} {W} hW Z hZc hZ lam hlam => ?_⟩
  have := hW.isProbabilityMeasure
  obtain ⟨Y, hYc, -, hY⟩ := exists_continuous_hatDelta hC0 hC hW
  have hpt : ∀ j x, Z j x =ᵐ[P] fun ω => ∑ i ∈ Finset.range (j + 1), Y i x ω := by
    intro j x
    have hs : (fun ω => ∑ i ∈ Finset.range (j + 1), Y i x ω) =ᵐ[P]
        fun ω => ∑ i ∈ Finset.range (j + 1), Real.sqrt Real.pi * W (hatDeltaKernel i x) ω := by
      have : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (j + 1),
          Y i x ω = Real.sqrt Real.pi * W (hatDeltaKernel i x) ω :=
        (Finset.eventually_all _).2 fun i _ => hY i x
      filter_upwards [this] with ω hω
      exact Finset.sum_congr rfl hω
    exact (hZ j x).trans ((hat_telescope hW j x).trans hs.symm)
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ q : ℚ × ℚ,
      Z j (ratPt q) ω = ∑ i ∈ Finset.range (j + 1), Y i (ratPt q) ω := by
    rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro q; exact hpt j (ratPt q)
  have hall' : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ x : ℂ,
      Z j x ω = ∑ i ∈ Finset.range (j + 1), Y i x ω := by
    filter_upwards [hall] with ω hω j
    have hS : Continuous fun x => ∑ i ∈ Finset.range (j + 1), Y i x ω :=
      continuous_finset_sum _ fun i _ => hYc i ω
    have := denseRange_ratPt'.equalizer (hZc j ω) hS (funext fun q => hω j q)
    exact fun x => congrFun this x
  have hsub : {ω | ∃ v ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ), ∃ j : ℕ, lam ≤ |Z j v ω|} ≤ᵐ[P]
      {ω | ∃ v ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ), ∃ n : ℕ,
        lam ≤ ∑ i ∈ Finset.range n, |Y i v ω|} := by
    filter_upwards [hall'] with ω hω hE
    obtain ⟨v, hv, j, hj⟩ := hE
    refine ⟨v, hv, j + 1, hj.trans ?_⟩
    rw [hω j v]
    exact Finset.abs_sum_le_sum_abs _ _
  refine (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)).trans ?_
  exact hsum hW Y hYc hY lam hlam

end DZZ
end LQGMetric
