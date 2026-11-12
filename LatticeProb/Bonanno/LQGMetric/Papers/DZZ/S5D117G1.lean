/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D117G1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117C2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2BridgeLemmas
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Tele

/-!
# D117 packet P-SIM: DZZ Lemma 2.7 along the scales `c 2^{-j}` (P2-DZZSIM2)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Lemma 2.7 (`lem-tilde-h-eta`,
l. 548–576) along the scales `c 2^{-j}`, `c ∈ (0, 1]` (used at l. 611–624 for
lem-scaling-coupling). We follow the proof of Lemma 2.7 exactly as DZZ do for Lemma 2.8 along
`a 2^{-j}` (l. 638–641; formalized as `dzz_lemma28_scaled`): with `2^{-k-1} < c ≤ 2^{-k}`,
`h̃_{c2^{-j}} − η_{c2^{-j}} = (h̃_{2^{-(j+k)}} − η_{2^{-(j+k)}}) + Δ'_j` a.s., where `Δ'_j` is the
sub-band `(c²4^{-j}, 4^{-(j+k)})` of `h̃ − η`, inside the dyadic band `j + k`.
* The dyadic part is `Σ_{i ≤ j+k} Δ_i` (`dzz_telescope`), bounded by `dzz_lemma27_sum`.
* The sub-bands obey (eq-variance-truncation) (`pi_sq_norm_tsubKernel_le`, from
  `pi_integral_trunc_le` on the sub-band) and (eq-feb25) (`pi_sq_norm_tsubKernel_sub_le`, from
  Lemma 2.5 for `h̃` and `η` on the sub-band), so `dzz_sum_sup_tail` applies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail

/-- The sub-band kernel `K^{h̃}_{(α², β²),x} − K^η_{(α², β²),x}`. -/
def tsubKernel (α β : ℝ) (x : ℂ) : WNSpace :=
  wndKernelL2 openSquare (Ioo (α ^ 2) (β ^ 2)) x - etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x

section bounds

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `h̃_α − η_α = (h̃_β − η_β) + √π W(tsubKernel α β x)` a.s. for `0 < α ≤ β`. -/
theorem tilde_sub_eta_decomp (hW : IsWhiteNoise P W) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (x : ℂ) :
    (fun ω => tildeHInf W α x ω - etaInf W α x ω) =ᵐ[P] fun ω =>
      (tildeHInf W β x ω - etaInf W β x ω) + Real.sqrt Real.pi * W (tsubKernel α β x) ω := by
  have hα2 : 0 < α ^ 2 := by positivity
  have hle : α ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ hα.le hαβ 2
  have e1 := hW.add_ae (wndKernelL2 openSquare (Ioi (β ^ 2)) x)
    (wndKernelL2 openSquare (Ioo (α ^ 2) (β ^ 2)) x)
  have e2 := hW.add_ae (etaKernelL2 (Ioi (β ^ 2)) x) (etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x)
  have e3 := hW.add_ae (wndKernelL2 openSquare (Ioo (α ^ 2) (β ^ 2)) x)
    (-etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x)
  have e4 := hW.smul_ae (-1) (etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x)
  filter_upwards [e1, e2, e3, e4] with ω h1 h2 h3 h4
  have hk : tsubKernel α β x = wndKernelL2 openSquare (Ioo (α ^ 2) (β ^ 2)) x +
      -etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x := by
    simp [tsubKernel, sub_eq_add_neg]
  have h5 : W (-etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x) ω =
      -W (etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x) ω := by
    rw [← neg_one_smul ℝ (etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x), h4]; ring
  simp only [tildeHInf, etaInf, wnField, etaField]
  rw [wndKernelL2_split hα2 hle, etaKernelL2_split hα2 hle, h1, h2, hk, h3, h5]
  ring

/-- (eq-variance-truncation) on the sub-band: for `2^{-(j+k+1)} ≤ α ≤ 2^{-(j+k)}`,
`π ‖tsubKernel α 2^{-(j+k)} x‖² ≤ 2 e^{−2κ(j+k)/9} log 4`. -/
theorem pi_sq_norm_tsubKernel_le (hW : IsWhiteNoise P W) (n : ℕ) {α : ℝ}
    (hα1 : (1 / 2 : ℝ) ^ (n + 1) ≤ α) (hα2 : α ≤ (1 / 2 : ℝ) ^ n) (x : ℂ) :
    Real.pi * ‖tsubKernel α ((1 / 2 : ℝ) ^ n) x‖ ^ 2 ≤
      2 * Real.exp (-(2 / 9 * kappaBand * n)) * Real.log 4 := by
  have hα0 : 0 < α := lt_of_lt_of_le (by positivity) hα1
  have ha : 0 < α ^ 2 := by positivity
  have hab : α ^ 2 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 := pow_le_pow_left₀ hα0.le hα2 2
  have hlo : (1 / 4 : ℝ) ^ (n + 1) ≤ α ^ 2 := by
    have e : (1 / 4 : ℝ) ^ (n + 1) = ((1 / 2 : ℝ) ^ (n + 1)) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e]; exact pow_le_pow_left₀ (by positivity) hα1 2
  have hhi : ((1 / 2 : ℝ) ^ n) ^ 2 = (1 / 4) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hband : ∀ s ∈ Ioo (α ^ 2) (((1 / 2 : ℝ) ^ n) ^ 2),
      s ∈ Ioo ((1 / 4 : ℝ) ^ (n + 1)) ((1 / 4 : ℝ) ^ n) := fun s hs =>
    ⟨hlo.trans_lt hs.1, hhi ▸ hs.2⟩
  have hv := variance_wnField_sub_etaField_le hW (measurableSet_Ioo (a := α ^ 2)
    (b := ((1 / 2 : ℝ) ^ n) ^ 2)) ha Ioo_subset_Ioi_self x
  simp only [wnField, etaField] at hv
  rw [variance_sqrtPi_sub hW] at hv
  refine (show Real.pi * ‖tsubKernel α ((1 / 2 : ℝ) ^ n) x‖ ^ 2 = _ from rfl).le.trans
    (hv.trans ?_)
  refine (pi_integral_trunc_le (m := 2 / 9 * kappaBand * n) ha hab (fun s hs => (etaRad_band n (hband s hs)).1)
    (fun s hs => ?_) x).trans ?_
  · have h := (etaRad_band n (hband s hs)).2
    have e2 : 2 * (etaRad s / 3) ^ 2 / s = 2 / 9 * (etaRad s ^ 2 / s) := by ring
    rw [e2]
    nlinarith
  · have hq : ((1 / 2 : ℝ) ^ n) ^ 2 / α ^ 2 ≤ 4 := by
      rw [div_le_iff₀ ha, hhi]
      have : (1 / 4 : ℝ) ^ n = 4 * (1 / 4) ^ (n + 1) := by rw [pow_succ]; ring
      linarith
    have hl : Real.log (((1 / 2 : ℝ) ^ n) ^ 2 / α ^ 2) ≤ Real.log 4 :=
      Real.log_le_log (by positivity) hq
    exact mul_le_mul_of_nonneg_left hl (by positivity)

/-- (eq-feb25), increment half, on the sub-band:
`π ‖tsubKernel α β x − tsubKernel α β x'‖² ≤ 2 (28 + 4 (13 + 256)) |x − x'| / α`. -/
theorem pi_sq_norm_tsubKernel_sub_le (hW : IsWhiteNoise P W) {α : ℝ} (hα : 0 < α) (β : ℝ)
    (x x' : ℂ) :
    Real.pi * ‖tsubKernel α β x - tsubKernel α β x'‖ ^ 2 ≤
      2 * (28 + 4 * (13 + 256)) / α * ‖x - x'‖ := by
  have h1 := dzz_lemma25_wnField (P := P) hW hα (measurableSet_Ioo (a := α ^ 2) (b := β ^ 2))
    Ioo_subset_Ioi_self x x'
  have h2 := dzz_lemma25_etaField (by norm_num) bridgeShellBound_256 hW hα
    (measurableSet_Ioo (a := α ^ 2) (b := β ^ 2)) Ioo_subset_Ioi_self x x'
  simp only [wnField, etaField] at h1 h2
  rw [variance_sqrtPi_sub hW] at h1 h2
  have h3 := sq_norm_sub_sub_le (wndKernelL2 openSquare (Ioo (α ^ 2) (β ^ 2)) x)
    (etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x) (wndKernelL2 openSquare (Ioo (α ^ 2) (β ^ 2)) x')
    (etaKernelL2 (Ioo (α ^ 2) (β ^ 2)) x')
  have hpi := Real.pi_pos
  have e : 2 * (28 + 4 * (13 + 256)) / α * ‖x - x'‖ =
      2 * (28 * ‖x - x'‖ / α) + 2 * (4 * (13 + 256) * ‖x - x'‖ / α) := by ring
  rw [e]
  unfold tsubKernel
  nlinarith

end bounds

/-- **DZZ Lemma 2.7 along the scales `c 2^{-j}`** for `c ∈ (0, 1]` (`lem-tilde-h-eta`,
l. 548–576, with the sub-band step of l. 638–641). -/
theorem dzzLemma27Along_of {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) : DZZLemma27Along c := by
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hc hc1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  obtain ⟨C1, hC1, hsum1⟩ := dzz_lemma27_sum.{0} (by norm_num) bridgeShellBound_256
  set ρ := Real.exp (-(2 / 9 * kappaBand)) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.mpr (by have := kappaBand_pos; linarith)
  set L := 2 * (28 + 4 * (13 + 256)) / c with hL
  have hL0 : 0 < L := by positivity
  set K2 := max (2 * Real.log 4) L with hK2
  have hK20 : 0 < K2 := lt_max_of_lt_right hL0
  obtain ⟨C2, hC2, hsum2⟩ := dzz_sum_sup_tail.{0} (K := K2) hK20 hρ0 hρ1
  set M := max C1 C2 with hM
  have hM0 : 0 < M := lt_max_of_lt_left hC1
  refine ⟨4 * M, by positivity, fun {Ω} _ {P} {W} hW Z hZc hZ lam hlam => ?_⟩
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
      tsubKernel (α j) (β j) x'‖ ^ 2 ≤ L * 2 ^ j * ‖x - x'‖ := by
    intro j x x'
    refine (pi_sq_norm_tsubKernel_sub_le hW (hα0 j) _ x x').trans (le_of_eq ?_)
    simp only [hL, hα]
    field_simp
    rw [mul_right_comm, ← mul_pow]; norm_num
  have h' : ∀ j : ℕ, ∃ Y' : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y' x ω) ∧
      (∀ x, Measurable (Y' x)) ∧ ∀ x, (fun ω => Y' x ω) =ᵐ[P]
        fun ω => Real.sqrt Real.pi * W (tsubKernel (α j) (β j) x) ω := fun j =>
    exists_continuous_modification_of_kernel_half hW (fun x => tsubKernel (α j) (β j) x)
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
    refine hsum2 Ω P 0 1 one_pos le_rfl Y' (fun i => ?_)
      (fun i v => ?_) (fun i ω => (hY'c i ω).continuousOn) (fun i v _ => ?_)
      (fun i u _ v _ => ?_) (lam / 2) (by linarith)
    · exact (isGaussianProcess_sqrtPi hW (fun x => tsubKernel (α i) (β i) x)).congr
        fun x => (hY' i x).symm
    · rw [integral_congr_ae (hY' i v)]; exact integral_sqrtPi hW _
    · rw [variance_congr (hY' i v), variance_sqrtPi hW]
      have hb := pi_sq_norm_tsubKernel_le hW (i + k) (hαlow i) (hαβ i) v
      refine hb.trans ?_
      have he : Real.exp (-(2 / 9 * kappaBand * ((i + k : ℕ) : ℝ))) ≤ ρ ^ i := by
        rw [hρ, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.2
        have := kappaBand_pos
        push_cast
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      calc 2 * Real.exp (-(2 / 9 * kappaBand * ((i + k : ℕ) : ℝ))) * Real.log 4
          ≤ 2 * ρ ^ i * Real.log 4 := by gcongr
        _ = (2 * Real.log 4) * ρ ^ i := by ring
        _ ≤ K2 * ρ ^ i :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hρ0.le _)
    · have hae : (fun ω => (Y' i v ω - Y' i u ω) ^ 2) =ᵐ[P] fun ω =>
          (Real.sqrt Real.pi * W (tsubKernel (α i) (β i) v) ω -
            Real.sqrt Real.pi * W (tsubKernel (α i) (β i) u) ω) ^ 2 := by
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
