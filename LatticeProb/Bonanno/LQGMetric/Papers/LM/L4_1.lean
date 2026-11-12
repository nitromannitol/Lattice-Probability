/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L4_1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L4_Meas
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L4_2
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_6Thm

/-!
# LM Lemma 4.1 from LM Lemma 3.1 (`N = 2`), and LM Theorem 1.6 (task P2-LM42)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Lemma 4.1 (`lem-good-radius-tail`, l. 803–816) and its proof
(l. 811–816): `E_r(z)` is determined by the rescaled internal metrics on `𝔸_{r/2,2r}(z)`
(`lmGoodE_aeEventIn`), locality is preserved under translation (`lm_S4_0`), and Lemma 3.1 is
applied to the translated field with `a = q log 2` (`q = 5`, as used in Lemma 4.2, l. 827).

Departure from LM's proof (LM S4.1a, blueprint/LocalMetrics.md): LM apply Lemma 3.1 with
`r_k = 2^{-k} r`, but Lemma 3.1 needs annuli `𝔸_{s₁R_k, s₂R_k}(0)` with `s₂ < 1` and
`R_{k+1}/R_k ≤ s₁`, while `E_t` lives on `𝔸_{t/2,2t}`. We take `R_k = 4·8^{-k} r`, `s₁ = 1/8`,
`s₂ = 1/2` (so `𝔸_{s₁R_k, s₂R_k} = 𝔸_{t/2,2t}` for `t = 8^{-k} r`) and only use the scales
`8^{-k} r` (instead of splitting `k` into residue classes): one good scale suffices for
`ρ_r(z) ≥ εr`. Accordingly `a = q log 8` and `K = ⌊log_8 ε^{-1}⌋`.

* `lmLem4_1Tail_of`: `LMLem3_1aN2 → ∃ p ∈ (0,1), LMLem4_1Tail p`.
* `lmLem4_2_of_N2`: `LMLem3_1aN2 → ∃ p ∈ (0,1), LMLem4_2 p`.
* `lmThm1_6_of_N2`: `LMLem3_1aN2 → Blueprint.LMThm1_6`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

lemma exp_neg_log8 (M : ℕ) : Real.exp (-(5 * Real.log 8) * M) = (8 : ℝ)⁻¹ ^ (5 * M) := by
  have e : -(5 * Real.log 8) * M = ((5 * M : ℕ) : ℝ) * Real.log (8 : ℝ)⁻¹ := by
    rw [Real.log_inv]; push_cast; ring
  rw [e, Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- **LM Lemma 4.1** (l. 803–816) with `q = 5`, from LM Lemma 3.1 (1) with `N = 2`. -/
theorem lmLem4_1Tail_of (h31 : LMLem3_1aN2) : ∃ p : ℝ, 0 < p ∧ p < 1 ∧ LMLem4_1Tail p := by
  have ha : 0 < 5 * Real.log 8 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 8); positivity
  obtain ⟨p, c, hp0, hp1, hc, H⟩ := h31 (1 / 8) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (5 * Real.log 8) ha (1 / 2) (by norm_num) (by norm_num)
  refine ⟨p, hp0, hp1, max c 1, by positivity, ?_⟩
  intro ξ Ω _ P _ h D D' hh hxi C hC w r hr hp M
  obtain ⟨hnN, hnX⟩ := lm_S4_0 hh hxi w
  set ρ : ℕ → ℝ := fun k => (8 : ℝ)⁻¹ ^ k * r with hρ
  have hρ0 : ∀ k, 0 < ρ k := fun k => by positivity
  choose E hEm hEae using fun k => lmGoodE_aeEventIn hxi C w (hρ0 k)
  set R : ℕ → ℝ := fun k => 4 * ρ k with hR
  have hAI : AnnulusIterHypN2 ξ (transField h w) (transMetric ξ h w D) (transMetric ξ h w D')
      (1 / 8) (1 / 2) R E := by
    refine ⟨fun k => by positivity, fun i j hij => ?_, fun k => ?_, fun k => ?_⟩
    · have h8 : (8 : ℝ)⁻¹ ^ j ≤ 8⁻¹ ^ i := pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
      show 4 * ((8 : ℝ)⁻¹ ^ j * r) ≤ 4 * ((8 : ℝ)⁻¹ ^ i * r)
      nlinarith
    · show 4 * ((8 : ℝ)⁻¹ ^ (k + 1) * r) / (4 * ((8 : ℝ)⁻¹ ^ k * r)) ≤ 1 / 8
      have e : 4 * ((8 : ℝ)⁻¹ ^ (k + 1) * r) = 1 / 8 * (4 * ((8 : ℝ)⁻¹ ^ k * r)) := by
        rw [pow_succ]; ring
      rw [e, mul_div_assoc, div_self (ne_of_gt (by positivity)), mul_one]
    · exact MeasurableSpace.le_def.1 (sup_le (le_sup_right.trans le_sup_left) le_sup_right) _
        (hEm k)
  have hPE : ∀ k, ENNReal.ofReal p ≤ P (E k) := fun k => by
    rw [measure_congr (hEae k)]; exact hp k
  have HB := H ξ P (transField h w) (transMetric ξ h w D) (transMetric ξ h w D') hnN hnX R E hAI
    hPE M
  have hae : ∀ᵐ ω ∂P, ∀ k, (ω ∈ E k ↔ lmGoodE (D ω) (D' ω) C w (ρ k)) := by
    rw [ae_all_iff]; intro k
    filter_upwards [hEae k] with ω hω
    exact Iff.of_eq hω
  rcases Nat.eq_zero_or_pos M with hM0 | hM0
  · subst hM0
    calc P _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (max c 1 * (8 : ℝ)⁻¹ ^ (5 * 0)) := by simp
  calc P {ω | ∀ m ∈ Finset.Icc 1 M, ¬ lmGoodE (D ω) (D' ω) C w ((8 : ℝ)⁻¹ ^ m * r)}
        ≤ P {ω | (countOcc E M ω : ℝ) < 1 / 2 * M} := by
        refine measure_mono_ae ?_
        filter_upwards [hae] with ω hω hbad
        have h0 : countOcc E M ω = 0 := by
          classical
          unfold countOcc
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro k hk hkE
          exact hbad k hk ((hω k).1 hkE)
        show (countOcc E M ω : ℝ) < 1 / 2 * M
        rw [h0]
        have : (0 : ℝ) < M := by exact_mod_cast hM0
        push_cast; linarith
    _ ≤ ENNReal.ofReal (c * Real.exp (-(5 * Real.log 8) * M)) := HB
    _ ≤ ENNReal.ofReal (max c 1 * (8 : ℝ)⁻¹ ^ (5 * M)) := by
        rw [exp_neg_log8]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (by positivity))

/-- **LM Lemma 4.2** (l. 820–829) from LM Lemma 3.1 (1) with `N = 2`. -/
theorem lmLem4_2_of_N2 (h31 : LMLem3_1aN2) : ∃ p : ℝ, 0 < p ∧ p < 1 ∧ LMLem4_2 p := by
  obtain ⟨p, hp0, hp1, H⟩ := lmLem4_1Tail_of h31
  exact ⟨p, hp0, hp1, lmLem4_2_of_tail H⟩

/-- **LM Theorem 1.6** (`thm-bilip`, `U = ℂ`) from LM Lemma 3.1 (1) with `N = 2`. -/
theorem lmThm1_6_of_N2 (h31 : LMLem3_1aN2) : LMThm1_6 := by
  obtain ⟨p, hp0, hp1, H⟩ := lmLem4_2_of_N2 h31
  exact lmThm1_6_of hp0 hp1 H

end LQGMetric.LM
