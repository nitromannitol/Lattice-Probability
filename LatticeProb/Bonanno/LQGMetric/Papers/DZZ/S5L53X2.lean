/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53X2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117G1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L8Scaled

/-!
# P-131S (2): DZZ Lemmas 2.7 and 2.8 along `c 2^{-j}`, with constants uniform in `c ∈ (0, 1]`
(P2-DZZ53X)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) Lemma 2.7 (`lem-tilde-h-eta`, l. 548–576) and Lemma
2.8 (l. 593–610) along the scales `c 2^{-j}`, with the sub-band step of l. 638–641.

Near misses adapted: `dzzLemma27Along_of` (S5D117G1) and `dzz_lemma28_scaled` (S2L8Scaled), whose
constant is `C(c)`; proofs copied with one change making it independent of `c`: the sub-band
processes `Y'_j` (scale `c 2^{-j} ∈ [2^{-(j+k+1)}, 2^{-(j+k)}]`) are fed to `dzz_sum_sup_tail`
with the index shifted by `k` (`Δ_i = Y'_{i-k}`, `i ≥ k`; the zero field `√π W(0)` for `i < k`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail

/-- `2D ≤ 4D 2^{j+k} α` when `2^{-(j+k+1)} ≤ α` -/
lemma two_mul_le_of_pow_le {D α : ℝ} (hD : 0 ≤ D) {n : ℕ} (h : (1 / 2 : ℝ) ^ (n + 1) ≤ α) :
    2 * D ≤ 4 * D * 2 ^ n * α := by
  have e : (2 : ℝ) ^ n * (1 / 2) ^ (n + 1) = 1 / 2 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num
  have h2 : (2 : ℝ) ^ n * (1 / 2) ^ (n + 1) ≤ 2 ^ n * α :=
    mul_le_mul_of_nonneg_left h (by positivity)
  rw [e] at h2
  nlinarith

/-- **DZZ Lemma 2.7 along `c 2^{-j}`, constant uniform in `c ∈ (0, 1]`** (proof of
`dzzLemma27Along_of`, S5D117G1, copied; index shift in the sub-band sum). -/
theorem dzzLemma27Along_unif :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ Z : ℕ → ℂ → Ω → ℝ,
      (∀ j ω, Continuous fun x => Z j x ω) →
      (∀ j x, Z j x =ᵐ[P] fun ω => tildeHInf W (c * (1 / 2 : ℝ) ^ j) x ω -
        etaInf W (c * (1 / 2 : ℝ) ^ j) x ω) →
      ∀ lam : ℝ, 0 ≤ lam →
        P.real {ω | ∃ v ∈ ferniqueBox 0 1, ∃ j : ℕ, lam ≤ |Z j v ω|} ≤
          C * Real.exp (-lam ^ 2 / C) := by
  obtain ⟨C1, hC1, hsum1⟩ := dzz_lemma27_sum.{0} (by norm_num) bridgeShellBound_256
  set ρ := Real.exp (-(2 / 9 * kappaBand)) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.mpr (by have := kappaBand_pos; linarith)
  set L := 4 * (28 + 4 * (13 + 256) : ℝ) with hL
  have hL0 : 0 < L := by positivity
  set K2 := max (2 * Real.log 4) L with hK2
  have hK20 : 0 < K2 := lt_max_of_lt_right hL0
  obtain ⟨C2, hC2, hsum2⟩ := dzz_sum_sup_tail.{0} (K := K2) hK20 hρ0 hρ1
  set M := max C1 C2 with hM
  have hM0 : 0 < M := lt_max_of_lt_left hC1
  refine ⟨4 * M, by positivity, fun c hc hc1 {Ω} _ {P} {W} hW Z hZc hZ lam hlam => ?_⟩
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hc hc1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have := hW.isProbabilityMeasure
  have hpi := Real.pi_pos
  -- scales
  set α : ℕ → ℝ := fun j => c * (1 / 2 : ℝ) ^ j with hα
  set β : ℕ → ℝ := fun j => (1 / 2 : ℝ) ^ (j + k) with hβ
  have hα0 : ∀ j, 0 < α j := fun j => by positivity
  have hαβ : ∀ j, α j ≤ β j := fun j => by
    simp only [hα, hβ, pow_add]
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left hk2 (by positivity)
  have hαlow : ∀ j, (1 / 2 : ℝ) ^ (j + k + 1) ≤ α j := fun j => by
    simp only [hα]
    rw [show j + k + 1 = j + (k + 1) by ring, pow_add, mul_comm]
    exact mul_le_mul_of_nonneg_right hk1.le (by positivity)
  -- continuous versions of the dyadic bands and of the sub-bands
  obtain ⟨Y, hYc, -, hY⟩ := exists_continuous_dzzDelta (by norm_num) bridgeShellBound_256 hW
  have hsub_inc : ∀ j x x', Real.pi * ‖tsubKernel (α j) (β j) x -
      tsubKernel (α j) (β j) x'‖ ^ 2 ≤ L * 2 ^ (j + k) * ‖x - x'‖ := by
    intro j x x'
    refine (pi_sq_norm_tsubKernel_sub_le hW (hα0 j) _ x x').trans
      (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [div_le_iff₀ (hα0 j)]
    exact two_mul_le_of_pow_le (by norm_num) (hαlow j)
  have h' : ∀ j : ℕ, ∃ Y' : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y' x ω) ∧
      (∀ x, Measurable (Y' x)) ∧ ∀ x, (fun ω => Y' x ω) =ᵐ[P]
        fun ω => Real.sqrt Real.pi * W (tsubKernel (α j) (β j) x) ω := fun j =>
    exists_continuous_modification_of_kernel_half hW (fun x => tsubKernel (α j) (β j) x)
      (K := L * 2 ^ (j + k) / Real.pi) (by positivity)
      (fun x x' => by
        have := hsub_inc j x x'
        rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
        linarith) _
  choose Y' hY'c hY'm hY' using h'
  -- the decomposition, a.s. at each point
  have hpt : ∀ j x, Z j x =ᵐ[P] fun ω =>
      ∑ i ∈ Finset.range (j + k + 1), Y i x ω + Y' j x ω := by
    intro j x
    have hs : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (j + k + 1), Y i x ω = dzzDelta W i x ω :=
      (Finset.eventually_all _).2 fun i _ => hY i x
    have ht := dzz_telescope hW (j + k) x
    have hd := tilde_sub_eta_decomp hW (hα0 j) (hαβ j) x
    filter_upwards [hZ j x, hs, ht, hd, hY' j x] with ω h1 h2 h3 h4 h5
    rw [h1]
    change tildeHInf W (α j) x ω - etaInf W (α j) x ω = _
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
  set box := ferniqueBox 0 1
  -- the shifted sub-band family
  set Δ : ℕ → ℂ → Ω → ℝ := fun i x ω =>
    if k ≤ i then Y' (i - k) x ω else Real.sqrt Real.pi * W 0 ω with hΔ
  set A := {ω | ∃ v ∈ box, ∃ n : ℕ, lam / 2 ≤ ∑ i ∈ Finset.range n, |Y i v ω|}
  set B := {ω | ∃ v ∈ box, ∃ n : ℕ, lam / 2 ≤ ∑ i ∈ Finset.range n, |Δ i v ω|}
  have hshift : ∀ v ω n, ∑ i ∈ Finset.range n, |Y' i v ω| ≤
      ∑ i ∈ Finset.range (k + n), |Δ i v ω| := by
    intro v ω n
    rw [Finset.sum_range_add]
    have e : ∀ i ∈ Finset.range n, |Δ (k + i) v ω| = |Y' i v ω| := fun i _ => by
      simp only [hΔ, Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [Finset.sum_congr rfl e]
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range k) => abs_nonneg (Δ i v ω)]
  have hsub : {ω | ∃ v ∈ box, ∃ j : ℕ, lam ≤ |Z j v ω|} ≤ᵐ[P] A ∪ B := by
    filter_upwards [hall'] with ω hω hE
    obtain ⟨v, hv, j, hj⟩ := hE
    rw [hω j v] at hj
    have h1 := Finset.abs_sum_le_sum_abs (fun i => Y i v ω) (Finset.range (j + k + 1))
    have h2 : |Y' j v ω| ≤ ∑ i ∈ Finset.range (j + 1), |Y' i v ω| := by
      rw [Finset.sum_range_succ]
      linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range j) => abs_nonneg (Y' i v ω)]
    have h3 := abs_add_le (∑ i ∈ Finset.range (j + k + 1), Y i v ω) (Y' j v ω)
    have h4 := hshift v ω (j + 1)
    by_cases hc : lam / 2 ≤ ∑ i ∈ Finset.range (j + k + 1), |Y i v ω|
    · exact Or.inl ⟨v, hv, _, hc⟩
    · exact Or.inr ⟨v, hv, k + (j + 1), by linarith⟩
  have hPA : P.real A ≤ C1 * Real.exp (-(lam / 2) ^ 2 / C1) :=
    hsum1 hW Y hYc hY (lam / 2) (by linarith)
  have hPB : P.real B ≤ C2 * Real.exp (-(lam / 2) ^ 2 / C2) := by
    refine hsum2 Ω P 0 1 one_pos le_rfl Δ (fun i => ?_)
      (fun i v => ?_) (fun i ω => ?_) (fun i v _ => ?_)
      (fun i u _ v _ => ?_) (lam / 2) (by linarith)
    · by_cases hk : k ≤ i
      · simp only [hΔ, hk, ↓reduceIte]
        exact (isGaussianProcess_sqrtPi hW (fun x => tsubKernel (α (i - k)) (β (i - k)) x)).congr
          fun x => (hY' (i - k) x).symm
      · simp only [hΔ, hk, ↓reduceIte]
        exact isGaussianProcess_sqrtPi hW (fun _ : ℂ => (0 : WNSpace))
    · by_cases hk : k ≤ i
      · simp only [hΔ, hk, ↓reduceIte]
        rw [integral_congr_ae (hY' (i - k) v)]; exact integral_sqrtPi hW _
      · simp only [hΔ, hk, ↓reduceIte]
        exact integral_sqrtPi hW _
    · by_cases hk : k ≤ i
      · simp only [hΔ, hk, ↓reduceIte]; exact (hY'c (i - k) ω).continuousOn
      · simp only [hΔ, hk, ↓reduceIte]; exact continuousOn_const
    · by_cases hk : k ≤ i
      · simp only [hΔ, hk, ↓reduceIte]
        rw [variance_congr (hY' (i - k) v), variance_sqrtPi hW]
        have hb := pi_sq_norm_tsubKernel_le hW (i - k + k) (hαlow (i - k)) (hαβ (i - k)) v
        rw [Nat.sub_add_cancel hk] at hb
        have hβi : β (i - k) = (1 / 2 : ℝ) ^ i := by simp only [hβ, Nat.sub_add_cancel hk]
        rw [hβi]
        refine hb.trans ?_
        have he : Real.exp (-(2 / 9 * kappaBand * (i : ℝ))) ≤ ρ ^ i := by
          rw [hρ, ← Real.exp_nat_mul]
          apply Real.exp_le_exp.2
          linarith
        have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        calc 2 * Real.exp (-(2 / 9 * kappaBand * (i : ℝ))) * Real.log 4
            ≤ 2 * ρ ^ i * Real.log 4 := by gcongr
          _ = (2 * Real.log 4) * ρ ^ i := by ring
          _ ≤ K2 * ρ ^ i :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hρ0.le _)
      · simp only [hΔ, hk, ↓reduceIte]
        rw [variance_sqrtPi hW]
        simp only [norm_zero]
        have : 0 ≤ K2 * ρ ^ i := by positivity
        simpa using this
    · by_cases hk : k ≤ i
      · simp only [hΔ, hk, ↓reduceIte]
        have hae : (fun ω => (Y' (i - k) v ω - Y' (i - k) u ω) ^ 2) =ᵐ[P] fun ω =>
            (Real.sqrt Real.pi * W (tsubKernel (α (i - k)) (β (i - k)) v) ω -
              Real.sqrt Real.pi * W (tsubKernel (α (i - k)) (β (i - k)) u) ω) ^ 2 := by
          filter_upwards [hY' (i - k) u, hY' (i - k) v] with ω h1 h2; rw [h1, h2]
        rw [integral_congr_ae hae, integral_sq_sqrtPi_sub hW]
        have h := hsub_inc (i - k) v u
        rw [norm_sub_rev v u, Nat.sub_add_cancel hk] at h
        refine h.trans ?_
        gcongr
        exact le_max_right _ _
      · simp only [hΔ, hk, ↓reduceIte, sub_self]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
        positivity
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

/-- **DZZ Lemma 2.8 along `a 2^{-j}`, constant uniform in `a ∈ (0, 1]`** (proof of
`dzz_lemma28_scaled`, S2L8Scaled, copied; index shift in the sub-band sum). -/
theorem dzz_lemma28_unif {ξ : ℝ} (hξ : 0 < ξ) (hξ2 : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ Z : ℕ → ℂ → Ω → ℝ,
      (∀ j ω, Continuous fun x => Z j x ω) →
      (∀ j x, Z j x =ᵐ[P] fun ω => phi W (a * (1 / 2 : ℝ) ^ j) 1 x ω -
        etaInf W (a * (1 / 2 : ℝ) ^ j) x ω) →
      ∀ lam : ℝ, 0 ≤ lam →
        P.real {ω | ∃ v ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ), ∃ j : ℕ, lam ≤ |Z j v ω|} ≤
          C * Real.exp (-lam ^ 2 / C) := by
  obtain ⟨C1, hC1, hsum1⟩ := dzz_lemma28_sum.{0} (by norm_num) bridgeShellBound_256 hξ hξ2
  set L := 4 * (Real.sqrt 2 + 4 * (13 + 256)) with hL
  have hL0 : 0 < L := by positivity
  set K2 := max (2 * Real.log 4) L with hK2
  have hK20 : 0 < K2 := lt_max_of_lt_right hL0
  obtain ⟨C2, hC2, hsum2⟩ := dzz_sum_sup_tail.{0} (K := K2) hK20 (rhoXi_pos ξ) (rhoXi_lt_one hξ)
  set M := max C1 C2 with hM
  have hM0 : 0 < M := lt_max_of_lt_left hC1
  refine ⟨4 * M, by positivity, fun a ha ha1 {Ω} _ {P} {W} hW Z hZc hZ lam hlam => ?_⟩
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one ha ha1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
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
      subbandKernel (α j) (β j) x'‖ ^ 2 ≤ L * 2 ^ (j + k) * ‖x - x'‖ := by
    intro j x x'
    refine (pi_sq_norm_subband_sub_le hW (hα0 j) x x').trans ?_
    rw [div_le_iff₀ (hα0 j)]
    have h := mul_le_mul_of_nonneg_right
      (two_mul_le_of_pow_le (D := Real.sqrt 2 + 4 * (13 + 256)) (by positivity) (hαlow j))
      (norm_nonneg (x - x'))
    exact h.trans_eq (by rw [hL]; ring)
  have h' : ∀ j : ℕ, ∃ Y' : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y' x ω) ∧
      (∀ x, Measurable (Y' x)) ∧ ∀ x, (fun ω => Y' x ω) =ᵐ[P]
        fun ω => Real.sqrt Real.pi * W (subbandKernel (α j) (β j) x) ω := fun j =>
    exists_continuous_modification_of_kernel_half hW (fun x => subbandKernel (α j) (β j) x)
      (K := L * 2 ^ (j + k) / Real.pi) (by positivity)
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
  set Δ : ℕ → ℂ → Ω → ℝ := fun i x ω =>
    if k ≤ i then Y' (i - k) x ω else Real.sqrt Real.pi * W 0 ω with hΔ
  set A := {ω | ∃ v ∈ box, ∃ n : ℕ, lam / 2 ≤ ∑ i ∈ Finset.range n, |Y i v ω|}
  set B := {ω | ∃ v ∈ box, ∃ n : ℕ, lam / 2 ≤ ∑ i ∈ Finset.range n, |Δ i v ω|}
  have hshift : ∀ v ω n, ∑ i ∈ Finset.range n, |Y' i v ω| ≤
      ∑ i ∈ Finset.range (k + n), |Δ i v ω| := by
    intro v ω n
    rw [Finset.sum_range_add]
    have e : ∀ i ∈ Finset.range n, |Δ (k + i) v ω| = |Y' i v ω| := fun i _ => by
      simp only [hΔ, Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [Finset.sum_congr rfl e]
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range k) => abs_nonneg (Δ i v ω)]
  have hsub : {ω | ∃ v ∈ box, ∃ j : ℕ, lam ≤ |Z j v ω|} ≤ᵐ[P] A ∪ B := by
    filter_upwards [hall'] with ω hω hE
    obtain ⟨v, hv, j, hj⟩ := hE
    rw [hω j v] at hj
    have h1 := Finset.abs_sum_le_sum_abs (fun i => Y i v ω) (Finset.range (j + k + 1))
    have h2 : |Y' j v ω| ≤ ∑ i ∈ Finset.range (j + 1), |Y' i v ω| := by
      rw [Finset.sum_range_succ]
      linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range j) => abs_nonneg (Y' i v ω)]
    have h3 := abs_add_le (∑ i ∈ Finset.range (j + k + 1), Y i v ω) (Y' j v ω)
    have h4 := hshift v ω (j + 1)
    by_cases hc : lam / 2 ≤ ∑ i ∈ Finset.range (j + k + 1), |Y i v ω|
    · exact Or.inl ⟨v, hv, _, hc⟩
    · exact Or.inr ⟨v, hv, k + (j + 1), by linarith⟩
  have hPA : P.real A ≤ C1 * Real.exp (-(lam / 2) ^ 2 / C1) :=
    hsum1 hW Y hYc hY (lam / 2) (by linarith)
  have hPB : P.real B ≤ C2 * Real.exp (-(lam / 2) ^ 2 / C2) := by
    refine hsum2 Ω P ⟨ξ, ξ⟩ (1 - 2 * ξ) (by linarith) (by linarith) Δ (fun i => ?_)
      (fun i v => ?_) (fun i ω => ?_) (fun i v hv => ?_)
      (fun i u _ v _ => ?_) (lam / 2) (by linarith)
    · by_cases hk : k ≤ i
      · simp only [hΔ, hk, ↓reduceIte]
        exact (isGaussianProcess_sqrtPi hW
          (fun x => subbandKernel (α (i - k)) (β (i - k)) x)).congr fun x => (hY' (i - k) x).symm
      · simp only [hΔ, hk, ↓reduceIte]
        exact isGaussianProcess_sqrtPi hW (fun _ : ℂ => (0 : WNSpace))
    · by_cases hk : k ≤ i
      · simp only [hΔ, hk, ↓reduceIte]
        rw [integral_congr_ae (hY' (i - k) v)]; exact integral_sqrtPi hW _
      · simp only [hΔ, hk, ↓reduceIte]
        exact integral_sqrtPi hW _
    · by_cases hk : k ≤ i
      · simp only [hΔ, hk, ↓reduceIte]; exact (hY'c (i - k) ω).continuousOn
      · simp only [hΔ, hk, ↓reduceIte]; exact continuousOn_const
    · by_cases hk : k ≤ i
      · simp only [hΔ, hk, ↓reduceIte]
        rw [variance_congr (hY' (i - k) v), variance_sqrtPi hW]
        have hb := pi_sq_norm_phi_sub_eta_subband_le hξ (ball_subset_openSquare_of_mem hξ hv)
          (i - k + k) (hαlow (i - k)) (hαβ (i - k)) le_rfl
        refine hb.trans ?_
        have he : Real.exp (-(2 / 9 * min (ξ ^ 2) kappaBand * ((i - k + k : ℕ) : ℝ))) ≤
            rhoXi ξ ^ i := by
          rw [Nat.sub_add_cancel hk, rhoXi, ← Real.exp_nat_mul]
          apply Real.exp_le_exp.2
          nlinarith
        have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        calc 2 * Real.exp (-(2 / 9 * min (ξ ^ 2) kappaBand * ((i - k + k : ℕ) : ℝ))) *
              Real.log 4
            ≤ 2 * rhoXi ξ ^ i * Real.log 4 := by gcongr
          _ = (2 * Real.log 4) * rhoXi ξ ^ i := by ring
          _ ≤ K2 * rhoXi ξ ^ i :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (rhoXi_pos ξ).le _)
      · simp only [hΔ, hk, ↓reduceIte]
        rw [variance_sqrtPi hW]
        simp only [norm_zero]
        have : 0 ≤ K2 * rhoXi ξ ^ i := mul_nonneg hK20.le (pow_nonneg (rhoXi_pos ξ).le _)
        simpa using this
    · by_cases hk : k ≤ i
      · simp only [hΔ, hk, ↓reduceIte]
        have hae : (fun ω => (Y' (i - k) v ω - Y' (i - k) u ω) ^ 2) =ᵐ[P] fun ω =>
            (Real.sqrt Real.pi * W (subbandKernel (α (i - k)) (β (i - k)) v) ω -
              Real.sqrt Real.pi * W (subbandKernel (α (i - k)) (β (i - k)) u) ω) ^ 2 := by
          filter_upwards [hY' (i - k) u, hY' (i - k) v] with ω h1 h2; rw [h1, h2]
        rw [integral_congr_ae hae, integral_sq_sqrtPi_sub hW]
        have h := hsub_inc (i - k) v u
        rw [norm_sub_rev v u, Nat.sub_add_cancel hk] at h
        refine h.trans ?_
        gcongr
        exact le_max_right _ _
      · simp only [hΔ, hk, ↓reduceIte, sub_self]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
        positivity
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
