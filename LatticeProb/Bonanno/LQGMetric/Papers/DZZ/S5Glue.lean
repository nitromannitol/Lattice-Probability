/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5Glue at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32

/-!
# DZZ Proposition 3.17 + an exponent of `E log D` ⇒ "with probability tending to 1" (P2-DZZ56)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`; Ding–Gwynne, arXiv:1807.01072,
`metric-comparison-final.tex`.

DG use DZZ only in the form "Proposition 3.17 and Lemma 5.3" (DG:1206, proof of DG Lemma 3.12) and
"Proposition 3.17 and Lemma 6.1" (DG:1627, proof of DG Lemma 3.20), both "with probability tending
to 1 as `ε → 0`" (decision D105, `decisions/DEC-105.md` §1 item 7, §3 N9). DZZ Lemmas 5.3/6.1 give
`E log min D_δ(A,B) / log δ⁻¹ → χ`; Proposition 3.17 (eq-concentration-1) gives
`|log min D_δ(A,B) − E log min D_δ(A,B)| ≤ ι log δ⁻¹` with probability `≥ 1 − δ^{cι²}`. Combining
the two (DZZ use this combination themselves, e.g. DZZ:2318–2325, (Eq.boundfortildeD)) gives:

* **`tendsto_prob_gt_of_conc`**, **`tendsto_prob_lt_of_conc`**: the abstract step for real
  random variables `X_δ`.
* **`dzz_lgd_upper_whp`**: `P[min D_δ(A_δ,B_δ) > δ^{−χ−ι}] → 0` (DG Lemma 3.12's input,
  `ε = δ²`, `χ = 2/d_γ`), given that the minimum is a.s. finite.
* **`dzz_lgd_lower_whp`**: `P[min D_δ(A_δ,B_δ) < δ^{−χ+ι}] → 0` (DG Lemma 3.20's input).

The concentration hypothesis is the project's statement `DZZProp317` (S3P32) for the measure in
question (DZZ Remark 5.2, l. 2287–2290: Proposition 3.17 holds verbatim for the restricted
distances `D̃`, `D̄`; a restriction is encoded as the walled measure `dzzWall`, D97).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω]

lemma tendsto_ofReal_rpow_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ a)) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun δ : ℝ => δ ^ a) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow ha.ne'] using (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
  simpa using ENNReal.tendsto_ofReal (tendsto_nhdsWithin_of_tendsto_nhds h)

lemma eventually_Ioo_nhdsGT {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo (0 : ℝ) (min δ₀ 1) :=
  Ioo_mem_nhdsGT (lt_min hδ₀ one_pos)

lemma log_inv_pos_of_mem {δ δ₀ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) (min δ₀ 1)) : 0 < Real.log δ⁻¹ :=
  Real.log_pos ((one_lt_inv₀ hδ.1).mpr (hδ.2.trans_le (min_le_right _ _)))

/-- Abstract upper step, one-sided form: concentration at all `ι ∈ (0,1)` with rate `δ^{cι²}`
and `limsup E X_δ / log δ⁻¹ ≤ χ` give `P[X_δ > (χ+ι) log δ⁻¹] → 0`. -/
theorem tendsto_prob_gt_of_conc' {P : Measure Ω} {X : ℝ → Ω → ℝ} {χ c : ℝ} (hc : 0 < c)
    (hconc : ∀ ι ∈ Ioo (0 : ℝ) 1, AlphaHighProb P (c * ι ^ 2)
      fun δ => {ω | |X δ ω - ∫ ω', X δ ω' ∂P| ≤ ι * Real.log δ⁻¹})
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ δ in 𝓝[>] (0 : ℝ), (∫ ω, X δ ω ∂P) / Real.log δ⁻¹ < χ + ε)
    {ι : ℝ} (hι : 0 < ι) :
    Tendsto (fun δ => P {ω | (χ + ι) * Real.log δ⁻¹ < X δ ω}) (𝓝[>] 0) (𝓝 0) := by
  set ι' := min (ι / 2) (1 / 2)
  have hι' : ι' ∈ Ioo (0 : ℝ) 1 := ⟨lt_min (by linarith) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num)⟩
  obtain ⟨δ₀, hδ₀, hP⟩ := hconc ι' hι'
  have hE : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (∫ ω, X δ ω ∂P) / Real.log δ⁻¹ < χ + ι / 2 :=
    hup (ι / 2) (by linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_ofReal_rpow_zero (a := c * ι' ^ 2) (by have := hι'.1; positivity))
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_Ioo_nhdsGT hδ₀, hE] with δ hδ hEδ
  have hL := log_inv_pos_of_mem hδ
  refine le_trans (measure_mono fun ω hω => ?_) (hP δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩)
  simp only [mem_setOf_eq, mem_compl_iff, not_le] at hω ⊢
  rw [div_lt_iff₀ hL] at hEδ
  have : ι' * Real.log δ⁻¹ ≤ ι / 2 * Real.log δ⁻¹ :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hL.le
  exact lt_of_lt_of_le (by nlinarith) (le_abs_self _)

/-- Abstract lower step, one-sided form (`liminf E X_δ / log δ⁻¹ ≥ χ`):
`P[X_δ < (χ−ι) log δ⁻¹] → 0`. -/
theorem tendsto_prob_lt_of_conc' {P : Measure Ω} {X : ℝ → Ω → ℝ} {χ c : ℝ} (hc : 0 < c)
    (hconc : ∀ ι ∈ Ioo (0 : ℝ) 1, AlphaHighProb P (c * ι ^ 2)
      fun δ => {ω | |X δ ω - ∫ ω', X δ ω' ∂P| ≤ ι * Real.log δ⁻¹})
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ δ in 𝓝[>] (0 : ℝ), χ - ε < (∫ ω, X δ ω ∂P) / Real.log δ⁻¹)
    {ι : ℝ} (hι : 0 < ι) :
    Tendsto (fun δ => P {ω | X δ ω < (χ - ι) * Real.log δ⁻¹}) (𝓝[>] 0) (𝓝 0) := by
  set ι' := min (ι / 2) (1 / 2)
  have hι' : ι' ∈ Ioo (0 : ℝ) 1 := ⟨lt_min (by linarith) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num)⟩
  obtain ⟨δ₀, hδ₀, hP⟩ := hconc ι' hι'
  have hE : ∀ᶠ δ in 𝓝[>] (0 : ℝ), χ - ι / 2 < (∫ ω, X δ ω ∂P) / Real.log δ⁻¹ :=
    hlow (ι / 2) (by linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_ofReal_rpow_zero (a := c * ι' ^ 2) (by have := hι'.1; positivity))
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_Ioo_nhdsGT hδ₀, hE] with δ hδ hEδ
  have hL := log_inv_pos_of_mem hδ
  refine le_trans (measure_mono fun ω hω => ?_) (hP δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩)
  simp only [mem_setOf_eq, mem_compl_iff, not_le] at hω ⊢
  rw [lt_div_iff₀ hL] at hEδ
  have : ι' * Real.log δ⁻¹ ≤ ι / 2 * Real.log δ⁻¹ :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hL.le
  rw [abs_sub_comm]
  exact lt_of_lt_of_le (by nlinarith) (le_abs_self _)

lemma one_le_lgdMinSet (μ : Measure ℂ) (δ : ℝ) (A B : Set ℂ) : 1 ≤ lgdMinSet μ δ A B :=
  le_iInf₂ fun _ _ => le_iInf₂ fun _ _ => one_le_lgdDZZ μ δ _ _

lemma exp_mul_log_inv {δ a : ℝ} (hδ : 0 < δ) : Real.exp (a * Real.log δ⁻¹) = δ ^ (-a) := by
  rw [Real.rpow_neg hδ.le, ← Real.inv_rpow hδ.le, Real.rpow_def_of_pos (inv_pos.mpr hδ),
    mul_comm]

/-- **Lower bound w.p. → 1** from DZZ Proposition 3.17 and the exponent of the mean (DZZ Lemma
6.1 in DG's use, DG:1627): `P[min D_δ(A_δ,B_δ) < δ^{−χ+ι}] → 0`. -/
theorem dzz_lgd_lower_whp' {P : Measure Ω} {μ : Ω → Measure ℂ} {ξ χ : ℝ}
    (h317 : DZZProp317 P μ ξ) {A B : ℝ → Set ℂ} (hAB : IsXiAdmissible ξ A B)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      χ - ε < (∫ ω, logMinLGD (μ ω) δ (A δ) (B δ) ∂P) / Real.log δ⁻¹)
    {ι : ℝ} (hι : 0 < ι) :
    Tendsto (fun δ => P {ω | ¬ ENNReal.ofReal (δ ^ (-(χ - ι))) ≤
      ((lgdMinSet (μ ω) δ (A δ) (B δ) : ℕ∞) : ℝ≥0∞)}) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨c, hc, h⟩ := h317
  have hX := tendsto_prob_lt_of_conc' hc (fun ι hι => (h A B hAB).1 ι hι) hlow hι
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hX
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  refine measure_mono (fun ω hω => ?_)
  simp only [mem_setOf_eq, not_le] at hω ⊢
  have htop : lgdMinSet (μ ω) δ (A δ) (B δ) ≠ ⊤ := by
    intro h; rw [h] at hω; simp at hω
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  have h1 := one_le_lgdMinSet (μ ω) δ (A δ) (B δ)
  rw [← hn] at h1 hω
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
  rw [show (((n : ℕ∞) : ℝ≥0∞)) = ENNReal.ofReal n by simp,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)] at hω
  unfold logMinLGD; rw [← hn]
  simp only [ENat.toNat_natCast]
  rw [← exp_mul_log_inv (mem_Ioi.mp hδ)] at hω
  calc Real.log n < Real.log (Real.exp ((χ - ι) * Real.log δ⁻¹)) :=
        Real.log_lt_log (by linarith) hω
    _ = (χ - ι) * Real.log δ⁻¹ := Real.log_exp _

end DZZ
end LQGMetric
