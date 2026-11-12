/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127C2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127C1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 N4a, part 2: `P^x(τ_U > h) → 0` as `x → Uᶜ` under an exterior corkscrew condition
(packet P-127C)

Exterior corkscrew condition (`ExtCorkscrew U L`): for every `p ∉ U` and every scale
`0 < ρ ≤ L` there is a ball `B(c, ρ/4) ⊆ Uᶜ` with `|c − p| ≤ ρ` (the exterior cone/disc
condition of D127 N4(a), in the form needed for the proof). Main result
`exists_killedSurv_le_of_corkscrew`: for every `h > 0`, `ε > 0` there is `η > 0` such that
`P^x(τ_U > h) ≤ ε` whenever `|x − p| < η` for some `p ∉ U`.

Proof (multi-scale iteration of the Markov property at fixed times; own elementary argument
replacing the Blumenthal 0-1 law proof of the Poincaré cone condition, DV-P127C-1): with scales
`R_j = r₀ Λʲ` and times `T_k = Σ_{j ≤ k} R_{j+1}²`, one Markov step (`killedSurv_add_le_of_near`)
and the corkscrew step (`killedSurv_le_of_ball`) give
`P^x(τ > T_{k+1}) ≤ (1 − γ₀) P^x(τ > T_k) + 2 e^{-Λ²/(16(k+1))}` (Gaussian tail
`lintegral_far_heatKernel_le`), hence `P^x(τ > T_n) ≤ (1 − γ₀)^{n+1} + 2n e^{-Λ²/(16(n+1))}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Finset
open scoped NNReal ENNReal

namespace LQGMetric
namespace CONF
namespace ZBM

open KilledHeat

/-- The **exterior corkscrew condition** at scales `≤ L`. -/
def ExtCorkscrew (U : Set ℂ) (L : ℝ) : Prop :=
  ∀ p ∉ U, ∀ ρ : ℝ, 0 < ρ → ρ ≤ L → ∃ c, dist c p ≤ ρ ∧ ball c (ρ / 4) ⊆ Uᶜ

/-- `M_{k+1} ≤ a M_k + e`, `M_0 ≤ a`, `a ≤ 1` give `M_k ≤ a^{k+1} + k e`. -/
lemma killedSurv_iter_le {M : ℕ → ℝ≥0∞} {a e : ℝ≥0∞} {n : ℕ} (ha : a ≤ 1) (h0 : M 0 ≤ a)
    (hs : ∀ k < n, M (k + 1) ≤ a * M k + e) : ∀ k ≤ n, M k ≤ a ^ (k + 1) + k * e
  | 0, _ => by simpa using h0
  | k + 1, hk => by
    have ih := killedSurv_iter_le ha h0 hs k (by omega)
    calc M (k + 1) ≤ a * M k + e := hs k (by omega)
      _ ≤ a * (a ^ (k + 1) + k * e) + e := by gcongr
      _ = a ^ (k + 1 + 1) + a * (k * e) + e := by rw [mul_add, pow_succ' a (k + 1)]
      _ ≤ a ^ (k + 1 + 1) + k * e + e :=
        add_le_add (add_le_add le_rfl (mul_le_of_le_one_left zero_le ha)) le_rfl
      _ = a ^ (k + 1 + 1) + ((k + 1 : ℕ) : ℝ≥0∞) * e := by push_cast; ring

/-- **Decay of the survival probability near `Uᶜ`** under the exterior corkscrew condition. -/
theorem exists_killedSurv_le_of_corkscrew {U : Set ℂ} (hU : IsOpen U) {L : ℝ} (hL : 0 < L)
    (hcork : ExtCorkscrew U L) {ε : ℝ} (hε : 0 < ε) {h : ℝ≥0} (hh : h ≠ 0) :
    ∃ η > 0, ∀ x p : ℂ, p ∉ U → dist x p < η → killedSurv U h x ≤ ENNReal.ofReal ε := by
  set a : ℝ≥0∞ := 1 - ENNReal.ofReal survGam0 with ha_def
  have ha1 : a ≤ 1 := tsub_le_self
  have ha : a < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
    (ENNReal.ofReal_pos.mpr survGam0_pos).ne'
  -- the number of scales
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a ^ (n + 1) ≤ ENNReal.ofReal (ε / 2) := by
    have ht := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ha
    have hev := ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hε)))
    obtain ⟨N, hN⟩ := hev.exists_forall_of_atTop
    exact ⟨N, (hN (N + 1) (Nat.le_succ N)).le⟩
  -- the tail level `Y` with `2 n e^{-Y} ≤ ε/2`
  obtain ⟨Y, hY0, hY⟩ : ∃ Y : ℝ, 0 ≤ Y ∧ (n : ℝ) * (2 * Real.exp (-Y)) ≤ ε / 2 := by
    have ht : Filter.Tendsto (fun y : ℝ ↦ (n : ℝ) * (2 * Real.exp (-y))) Filter.atTop
        (nhds ((n : ℝ) * (2 * 0))) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul 2).const_mul _
    rw [mul_zero, mul_zero] at ht
    obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds (half_pos hε))).exists_forall_of_atTop
    exact ⟨max N 0, le_max_right _ _, (hN _ (le_max_left _ _)).le⟩
  -- the scale ratio `Λ`
  obtain ⟨Λ, hΛ2, hΛY⟩ : ∃ Λ : ℝ≥0, (2 : ℝ) ≤ Λ ∧ 16 * ((n : ℝ) + 1) * Y ≤ (Λ : ℝ) ^ 2 := by
    refine ⟨(max 2 (Real.sqrt (16 * ((n : ℝ) + 1) * Y))).toNNReal, ?_, ?_⟩
    · rw [Real.coe_toNNReal _ (le_max_of_le_left zero_le_two)]; exact le_max_left _ _
    · rw [Real.coe_toNNReal _ (le_max_of_le_left zero_le_two)]
      calc 16 * ((n : ℝ) + 1) * Y = Real.sqrt (16 * ((n : ℝ) + 1) * Y) ^ 2 :=
            (Real.sq_sqrt (by positivity)).symm
        _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  -- the smallest scale `r₀`
  obtain ⟨r0, hr0, hr0L, hr0h⟩ : ∃ r0 : ℝ≥0, (0 : ℝ) < r0 ∧ (r0 : ℝ) * Λ ^ (n + 1) ≤ L ∧
      ((n : ℝ) + 1) * ((r0 : ℝ) * Λ ^ (n + 1)) ^ 2 ≤ h := by
    have hP : (0 : ℝ) < (Λ : ℝ) ^ (n + 1) := by positivity
    have hh' : (0 : ℝ) < h := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hh)
    set m := min L (Real.sqrt (h / ((n : ℝ) + 1))) with hm
    have hm0 : 0 < m := lt_min hL (Real.sqrt_pos.mpr (by positivity))
    refine ⟨(m / (Λ : ℝ) ^ (n + 1)).toNNReal, ?_, ?_, ?_⟩ <;>
      rw [Real.coe_toNNReal _ (by positivity)]
    · positivity
    · rw [div_mul_cancel₀ _ hP.ne']; exact min_le_left _ _
    · rw [div_mul_cancel₀ _ hP.ne']
      calc ((n : ℝ) + 1) * m ^ 2 ≤ ((n : ℝ) + 1) * Real.sqrt (h / ((n : ℝ) + 1)) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0.le (min_le_right _ _) 2)
              (by positivity)
          _ = (h : ℝ) := by
            rw [Real.sq_sqrt (by positivity)]; exact mul_div_cancel₀ _ (by positivity)
  refine ⟨r0, hr0, fun x p hp hxp ↦ ?_⟩
  -- scales and times
  set R : ℕ → ℝ≥0 := fun j ↦ r0 * Λ ^ j with hR_def
  set T : ℕ → ℝ≥0 := fun k ↦ ∑ j ∈ range (k + 1), R (j + 1) ^ 2 with hT_def
  have hRpos : ∀ j, (0 : ℝ) < R j := fun j ↦ by simp only [hR_def]; push_cast; positivity
  have hRne : ∀ j, R j ≠ 0 := fun j ↦ by
    have := hRpos j; intro h0; rw [h0] at this; simp at this
  have hRmono : ∀ i j, i ≤ j → (R i : ℝ) ≤ R j := fun i j hij ↦ by
    simp only [hR_def]; push_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΛ1 hij) hr0.le
  have hRL : ∀ j ≤ n + 1, (R j : ℝ) ≤ L := fun j hj ↦ by
    refine le_trans ?_ hr0L
    simp only [hR_def]; push_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΛ1 hj) hr0.le
  have hTsucc : ∀ k, T (k + 1) = T k + R (k + 2) ^ 2 := fun k ↦ by
    simp only [hT_def]; rw [sum_range_succ]
  have hTne : ∀ k, T k ≠ 0 := fun k ↦ by
    simp only [hT_def]
    exact (sum_pos (fun j _ ↦ pow_pos (pos_iff_ne_zero.mpr (hRne _)) 2)
      nonempty_range_add_one).ne'
  have hTle : ∀ k, (T k : ℝ) ≤ ((k : ℝ) + 1) * (R (k + 1) : ℝ) ^ 2 := fun k ↦ by
    simp only [hT_def]; push_cast
    calc ∑ j ∈ range (k + 1), ((R (j + 1) : ℝ)) ^ 2 ≤ ∑ _j ∈ range (k + 1), (R (k + 1) : ℝ) ^ 2 :=
          sum_le_sum fun j hj ↦ pow_le_pow_left₀ (hRpos _).le
            (hRmono _ _ (by simp at hj; omega)) 2
      _ = _ := by simp
  -- the corkscrew step at scale `R j`
  have hstep : ∀ j ≤ n + 1, ∀ w, dist w p ≤ R j → killedSurv U (R j ^ 2) w ≤ a := by
    intro j hj w hw
    obtain ⟨c, hcp, hball⟩ := hcork p hp (R j) (hRpos j) (hRL j hj)
    exact killedSurv_le_of_ball hU (hRne j) hcp hball hw
  have hxp' : dist x p ≤ r0 := hxp.le
  have hr0R : ∀ j, 1 ≤ j → (r0 : ℝ) ≤ R j / 2 := fun j hj ↦ by
    simp only [hR_def]; push_cast
    have : (2 : ℝ) ≤ (Λ : ℝ) ^ j := hΛ2.trans (le_self_pow₀ hΛ1 (by omega))
    nlinarith
  set e : ℝ≥0∞ := ENNReal.ofReal (2 * Real.exp (-Y)) with he
  have hiter := killedSurv_iter_le (M := fun k ↦ killedSurv U (T k) x) (e := e) (n := n) ha1
    (by
      show killedSurv U (T 0) x ≤ a
      have : T 0 = R 1 ^ 2 := by simp [hT_def]
      rw [this]
      exact hstep 1 (by omega) x (hxp'.trans (by
        have := hr0R 1 le_rfl; have := hRpos 1; linarith)))
    (by
      intro k hk
      show killedSurv U (T (k + 1)) x ≤ a * killedSurv U (T k) x + e
      rw [hTsucc]
      refine (killedSurv_add_le_of_near hU (hTne k) (pow_ne_zero 2 (hRne _)) x p
        (hstep (k + 2) (by omega))).trans (add_le_add le_rfl ?_)
      have hTk : (0 : ℝ) < T k := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (hTne k))
      refine (lintegral_far_heatKernel_le hTk (δ := (R (k + 2) : ℝ) / 2)
        (by have := hRpos (k + 2); positivity) x _ fun w hw ↦ ?_).trans
        (ENNReal.ofReal_le_ofReal ?_)
      · simp only [Set.mem_ofPred_eq] at hw ⊢
        have h1 := dist_triangle w x p
        have h2 := hr0R (k + 2) (by omega)
        linarith
      · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) zero_le_two
        have hR2 : (R (k + 2) : ℝ) = Λ * R (k + 1) := by
          simp only [hR_def]; push_cast; ring
        have hRk := hRpos (k + 1)
        have hTk' := hTle k
        have hkn : ((k : ℝ) + 1) ≤ (n : ℝ) + 1 := by
          have : (k : ℝ) ≤ n := by exact_mod_cast hk.le
          linarith
        rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity), hR2]
        calc Y * (4 * (T k : ℝ)) ≤ Y * (4 * (((n : ℝ) + 1) * (R (k + 1) : ℝ) ^ 2)) := by
              gcongr
              exact hTk'.trans (mul_le_mul_of_nonneg_right hkn (by positivity))
          _ = (16 * ((n : ℝ) + 1) * Y) * (R (k + 1) : ℝ) ^ 2 / 4 := by ring
          _ ≤ (Λ : ℝ) ^ 2 * (R (k + 1) : ℝ) ^ 2 / 4 := by gcongr
          _ = _ := by ring) n le_rfl
  -- conclusion
  have hTn : T n ≤ h := by
    have := hTle n
    have hRn : (R (n + 1) : ℝ) = r0 * Λ ^ (n + 1) := by simp [hR_def]
    rw [hRn] at this
    exact_mod_cast this.trans hr0h
  calc killedSurv U h x ≤ killedSurv U (T n) x := killedSurv_anti hU (hTne n) hTn x
    _ ≤ a ^ (n + 1) + n * e := hiter
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
        refine add_le_add hn ?_
        rw [he, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        exact ENNReal.ofReal_le_ofReal hY
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

end ZBM
end CONF
end LQGMetric
