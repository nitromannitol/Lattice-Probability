/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L8Scaled at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L9Band
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2BridgeLemmas

/-!
# DZZ Lemma 2.8 along the scales `a 2^{-j}` (task P2-DZZPRE4)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 628–641 (proof of Lemma 2.9):
(eq-coupling-hat-h-eta-2) is Lemma 2.8 (`lem-hat-h-eta`, l. 594–609) along the scales `a 2^{-j}`,
`a ∈ (0, 1]`, which DZZ obtain by "the same derivation". We follow the derivation of Lemma 2.8
(l. 603–609, as l. 571–594): with `2^{-k-1} < a ≤ 2^{-k}`,
`ĥ^1_{a2^{-j}} − η_{a2^{-j}} = (ĥ^1_{2^{-(j+k)}} − η_{2^{-(j+k)}}) + Δ'_j` a.s., where `Δ'_j` is the
sub-band `[a2^{-j}, 2^{-(j+k)}]` of `ĥ − η` (inside one dyadic band). The dyadic part is
`Σ_{i ≤ j+k} Δ_i` (`hat_telescope`); the sub-bands obey (eq-variance-truncation) and (eq-feb25)
(`pi_sq_norm_phi_sub_eta_subband_le`, `pi_sq_norm_subband_sub_le`), so the probabilistic core
`dzz_sum_sup_tail` applies to both families.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail

/-- The sub-band kernel `k^ĥ_{α,β,x} − K^η_{(α², β²),x}`. -/
def subbandKernel (α β : ℝ) (x : ℂ) : WNSpace :=
  phiKernelL2 α β x - etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x

section decomp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `ĥ^1_α − η_α = (ĥ^1_β − η_β) + √π W(subbandKernel α β x)` a.s. for `0 < α ≤ β ≤ 1`. -/
theorem hat_sub_eta_decomp (hW : IsWhiteNoise P W) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hβ : β ≤ 1) (x : ℂ) :
    (fun ω => phi W α 1 x ω - etaInf W α x ω) =ᵐ[P] fun ω =>
      (phi W β 1 x ω - etaInf W β x ω) +
        Real.sqrt Real.pi * W (subbandKernel α β x) ω := by
  have e1 := phi_add_ae hW hα hαβ hβ x
  have e2 := hW.add_ae (etaKernelL2 (Ioi (β ^ 2)) x) (etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x)
  have e3 := hW.add_ae (phiKernelL2 α β x) (-etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x)
  have e4 := hW.smul_ae (-1) (etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x)
  filter_upwards [e1, e2, e3, e4] with ω h1 h2 h3 h4
  have hk : subbandKernel α β x = phiKernelL2 α β x + -etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x := by
    simp [subbandKernel, sub_eq_add_neg]
  rw [h1, hk, h3, ← neg_one_smul ℝ (etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x), h4]
  simp only [etaInf, etaField, phi]
  rw [etaKernelL2_split (by positivity) (pow_le_pow_left₀ hα.le hαβ 2), h2]
  ring

end decomp

universe u

/-- **DZZ Lemma 2.8 along the scales `a 2^{-j}`** (used in the proof of Lemma 2.9, l. 638–641,
(eq-coupling-hat-h-eta-2)): for `ξ ∈ (0, 1/2)`, `a ∈ (0, 1]` and continuous versions `Z_j` of
`ĥ^1_{a2^{-j}} − η_{a2^{-j}}`, `P(max_{v ∈ 𝕍^ξ} max_j |Z_j(v)| ≥ λ) ≤ C e^{−λ²/C}`, `C = C(ξ, a)`. -/
theorem dzz_lemma28_scaled {ξ a : ℝ} (hξ : 0 < ξ) (hξ2 : ξ < 1 / 2) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ Z : ℕ → ℂ → Ω → ℝ,
      (∀ j ω, Continuous fun x => Z j x ω) →
      (∀ j x, Z j x =ᵐ[P] fun ω => phi W (a * (1 / 2 : ℝ) ^ j) 1 x ω -
        etaInf W (a * (1 / 2 : ℝ) ^ j) x ω) →
      ∀ lam : ℝ, 0 ≤ lam →
        P.real {ω | ∃ v ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ), ∃ j : ℕ, lam ≤ |Z j v ω|} ≤
          C * Real.exp (-lam ^ 2 / C) := by
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one ha ha1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  obtain ⟨C1, hC1, hsum1⟩ := dzz_lemma28_sum.{u} (by norm_num) bridgeShellBound_256 hξ hξ2
  set L := 2 * (Real.sqrt 2 + 4 * (13 + 256)) / a with hL
  have hL0 : 0 < L := by positivity
  set K2 := max (2 * Real.log 4) L with hK2
  have hK20 : 0 < K2 := lt_max_of_lt_right hL0
  obtain ⟨C2, hC2, hsum2⟩ := dzz_sum_sup_tail.{u} (K := K2) hK20 (rhoXi_pos ξ) (rhoXi_lt_one hξ)
  set M := max C1 C2 with hM
  have hM0 : 0 < M := lt_max_of_lt_left hC1
  refine ⟨4 * M, by positivity, fun {Ω} _ {P} {W} hW Z hZc hZ lam hlam => ?_⟩
  have := hW.isProbabilityMeasure
  have hpi := Real.pi_pos
  -- scales
  set α : ℕ → ℝ := fun j => a * (1 / 2 : ℝ) ^ j with hα
  set β : ℕ → ℝ := fun j => (1 / 2 : ℝ) ^ (j + k) with hβ
  have hα0 : ∀ j, 0 < α j := fun j => by positivity
  have hαβ : ∀ j, α j ≤ β j := fun j => by
    simp only [hα, hβ, pow_add]
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left hk2 (by positivity)
  have hαlow : ∀ j, (1 / 2 : ℝ) ^ (j + k + 1) ≤ α j := fun j => by
    simp only [hα]
    rw [show j + k + 1 = j + (k + 1) by ring, pow_add, mul_comm]
    exact mul_le_mul_of_nonneg_right hk1.le (by positivity)
  have hβ1 : ∀ j, β j ≤ 1 := fun j => pow_le_one₀ (by norm_num) (by norm_num)
  -- continuous versions of the dyadic bands and of the sub-bands
  obtain ⟨Y, hYc, -, hY⟩ := exists_continuous_hatDelta (by norm_num) bridgeShellBound_256 hW
  have hsub_inc : ∀ j x x', Real.pi * ‖subbandKernel (α j) (β j) x -
      subbandKernel (α j) (β j) x'‖ ^ 2 ≤ L * 2 ^ j * ‖x - x'‖ := by
    intro j x x'
    refine (pi_sq_norm_subband_sub_le hW (hα0 j) x x').trans (le_of_eq ?_)
    simp only [hL, hα]
    field_simp
    rw [mul_assoc, ← mul_pow]; norm_num
  have h' : ∀ j : ℕ, ∃ Y' : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y' x ω) ∧
      (∀ x, Measurable (Y' x)) ∧ ∀ x, (fun ω => Y' x ω) =ᵐ[P]
        fun ω => Real.sqrt Real.pi * W (subbandKernel (α j) (β j) x) ω := fun j =>
    exists_continuous_modification_of_kernel_half hW (fun x => subbandKernel (α j) (β j) x)
      (K := L * 2 ^ j / Real.pi) (by positivity)
      (fun x x' => by
        have := hsub_inc j x x'
        rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
        linarith) _
  choose Y' hY'c hY'm hY' using h'
  -- the decomposition, a.s. at each point
  have hpt : ∀ j x, Z j x =ᵐ[P] fun ω =>
      ∑ i ∈ Finset.range (j + k + 1), Y i x ω + Y' j x ω := by
    intro j x
    have hs : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (j + k + 1),
        Y i x ω = Real.sqrt Real.pi * W (hatDeltaKernel i x) ω :=
      (Finset.eventually_all _).2 fun i _ => hY i x
    have ht := hat_telescope hW (j + k) x
    have hd := hat_sub_eta_decomp hW (hα0 j) (hαβ j) (hβ1 j) x
    filter_upwards [hZ j x, hs, ht, hd, hY' j x] with ω h1 h2 h3 h4 h5
    rw [h1]
    change phi W (α j) 1 x ω - etaInf W (α j) x ω = _
    rw [h4, h5, Finset.sum_congr rfl h2]
    simp only [hβ] at h3 ⊢
    rw [h3]
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ q : ℚ × ℚ,
      Z j (ratPt q) ω = ∑ i ∈ Finset.range (j + k + 1), Y i (ratPt q) ω + Y' j (ratPt q) ω := by
    rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro q; exact hpt j (ratPt q)
  have hall' : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ x : ℂ,
      Z j x ω = ∑ i ∈ Finset.range (j + k + 1), Y i x ω + Y' j x ω := by
    filter_upwards [hall] with ω hω j
    have hS : Continuous fun x => ∑ i ∈ Finset.range (j + k + 1), Y i x ω + Y' j x ω :=
      (continuous_finsetSum _ fun i _ => hYc i ω).add (hY'c j ω)
    have := denseRange_ratPt'.equalizer (hZc j ω) hS (funext fun q => hω j q)
    exact fun x => congrFun this x
  set box := ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ)
  set A := {ω | ∃ v ∈ box, ∃ n : ℕ, lam / 2 ≤ ∑ i ∈ Finset.range n, |Y i v ω|}
  set B := {ω | ∃ v ∈ box, ∃ n : ℕ, lam / 2 ≤ ∑ i ∈ Finset.range n, |Y' i v ω|}
  have hsub : {ω | ∃ v ∈ box, ∃ j : ℕ, lam ≤ |Z j v ω|} ≤ᵐ[P] A ∪ B := by
    filter_upwards [hall'] with ω hω hE
    obtain ⟨v, hv, j, hj⟩ := hE
    rw [hω j v] at hj
    have h1 := Finset.abs_sum_le_sum_abs (fun i => Y i v ω) (Finset.range (j + k + 1))
    have h2 : |Y' j v ω| ≤ ∑ i ∈ Finset.range (j + 1), |Y' i v ω| := by
      rw [Finset.sum_range_succ]
      linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range j) => abs_nonneg (Y' i v ω)]
    have h3 := abs_add_le (∑ i ∈ Finset.range (j + k + 1), Y i v ω) (Y' j v ω)
    by_cases hc : lam / 2 ≤ ∑ i ∈ Finset.range (j + k + 1), |Y i v ω|
    · exact Or.inl ⟨v, hv, _, hc⟩
    · exact Or.inr ⟨v, hv, j + 1, by linarith⟩
  have hPA : P.real A ≤ C1 * Real.exp (-(lam / 2) ^ 2 / C1) :=
    hsum1 hW Y hYc hY (lam / 2) (by linarith)
  have hPB : P.real B ≤ C2 * Real.exp (-(lam / 2) ^ 2 / C2) := by
    refine hsum2 Ω P ⟨ξ, ξ⟩ (1 - 2 * ξ) (by linarith) (by linarith) Y' (fun i => ?_)
      (fun i v => ?_) (fun i ω => (hY'c i ω).continuousOn) (fun i v hv => ?_)
      (fun i u _ v _ => ?_) (lam / 2) (by linarith)
    · exact (isGaussianProcess_sqrtPi hW (fun x => subbandKernel (α i) (β i) x)).congr
        fun x => (hY' i x).symm
    · rw [integral_congr_ae (hY' i v)]; exact integral_sqrtPi hW _
    · rw [variance_congr (hY' i v), variance_sqrtPi hW]
      have hb := pi_sq_norm_phi_sub_eta_subband_le hξ (ball_subset_openSquare_of_mem hξ hv)
        (i + k) (hαlow i) (hαβ i) le_rfl
      refine hb.trans ?_
      have hc : 0 ≤ 2 / 9 * min (ξ ^ 2) kappaBand :=
        mul_nonneg (by norm_num) (le_min (by positivity) kappaBand_pos.le)
      have he : Real.exp (-(2 / 9 * min (ξ ^ 2) kappaBand * ((i + k : ℕ) : ℝ))) ≤ rhoXi ξ ^ i := by
        rw [rhoXi, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.2
        push_cast
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      calc 2 * Real.exp (-(2 / 9 * min (ξ ^ 2) kappaBand * ((i + k : ℕ) : ℝ))) * Real.log 4
          ≤ 2 * rhoXi ξ ^ i * Real.log 4 := by gcongr
        _ = (2 * Real.log 4) * rhoXi ξ ^ i := by ring
        _ ≤ K2 * rhoXi ξ ^ i :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (rhoXi_pos ξ).le _)
    · have hae : (fun ω => (Y' i v ω - Y' i u ω) ^ 2) =ᵐ[P] fun ω =>
          (Real.sqrt Real.pi * W (subbandKernel (α i) (β i) v) ω -
            Real.sqrt Real.pi * W (subbandKernel (α i) (β i) u) ω) ^ 2 := by
        filter_upwards [hY' i u, hY' i v] with ω h1 h2; rw [h1, h2]
      rw [integral_congr_ae hae, integral_sq_sqrtPi_sub hW]
      have h := hsub_inc i v u
      rw [norm_sub_rev v u] at h
      refine h.trans ?_
      gcongr
      exact le_max_right _ _
  have hE : P.real {ω | ∃ v ∈ box, ∃ j : ℕ, lam ≤ |Z j v ω|} ≤ P.real A + P.real B :=
    (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)).trans
      (measureReal_union_le A B)
  have hexp : ∀ c : ℝ, 0 < c → c ≤ M →
      c * Real.exp (-(lam / 2) ^ 2 / c) ≤ M * Real.exp (-lam ^ 2 / (4 * M)) := by
    intro c hc hcM
    refine mul_le_mul hcM (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hM0.le
    rw [div_pow, neg_div, neg_div, neg_le_neg_iff, div_div, div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith [sq_nonneg lam]
  have e1 := hexp C1 hC1 (le_max_left _ _)
  have e2 := hexp C2 hC2 (le_max_right _ _)
  have hpos : 0 ≤ M * Real.exp (-lam ^ 2 / (4 * M)) := by positivity
  linarith

end DZZ
end LQGMetric
