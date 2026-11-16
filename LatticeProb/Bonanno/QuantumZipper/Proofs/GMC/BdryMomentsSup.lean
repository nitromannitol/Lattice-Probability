import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Supremum moments from higher moments and increment bounds

Minkowski and interpolation give a finite moment bound for the supremum of a
sequence from a uniform higher-moment bound and geometric first-moment bounds
on its increments.

Copied from Leonardo Bonanno's `QuantumZipper/Proofs/GMC/BdryMomentsSup.lean`,
https://github.com/leobon12/lean-formalizations, commit
`fdb5cad17d11550228cf8dbaf6216e69fc3d2d82`. The module documentation was
revised; the Mathlib import for `AEMeasurable.tsum` was added and the deprecated
name `AEMeasurable.ennreal_tsum` was replaced by `AEMeasurable.tsum`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace GMCMoments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Minkowski's inequality for finite sums and series of `ℝ≥0∞`-valued functions -/

/-- Minkowski for the partial sums `Σ_{i<n} f_i`. -/
theorem lintegral_sum_range_rpow_le {p : ℝ} (hp : 1 ≤ p) {f : ℕ → Ω → ℝ≥0∞}
    (hf : ∀ i, AEMeasurable (f i) μ) (n : ℕ) :
    (∫⁻ ω, (∑ i ∈ Finset.range n, f i ω) ^ p ∂μ) ^ (1 / p) ≤
      ∑ i ∈ Finset.range n, (∫⁻ ω, f i ω ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  induction n with
  | zero =>
    simp [ENNReal.zero_rpow_of_pos hp0, hp0]
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    have hS : AEMeasurable (fun ω => ∑ i ∈ Finset.range n, f i ω) μ :=
      Finset.aemeasurable_fun_sum _ fun i _ => hf i
    calc (∫⁻ ω, (∑ i ∈ Finset.range n, f i ω + f n ω) ^ p ∂μ) ^ (1 / p)
        ≤ (∫⁻ ω, (∑ i ∈ Finset.range n, f i ω) ^ p ∂μ) ^ (1 / p) +
            (∫⁻ ω, f n ω ^ p ∂μ) ^ (1 / p) :=
          ENNReal.lintegral_Lp_add_le hS (hf n) hp
      _ ≤ _ := by gcongr

/-- **Minkowski for series**: `‖Σ' f_i‖_p ≤ Σ' ‖f_i‖_p` (`1 ≤ p`). -/
theorem lintegral_tsum_rpow_le {p : ℝ} (hp : 1 ≤ p) {f : ℕ → Ω → ℝ≥0∞}
    (hf : ∀ i, AEMeasurable (f i) μ) :
    (∫⁻ ω, (∑' i, f i ω) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, (∫⁻ ω, f i ω ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hpt : ∀ ω, (∑' i, f i ω) ^ p = ⨆ n, (∑ i ∈ Finset.range n, f i ω) ^ p := by
    intro ω
    rw [ENNReal.tsum_eq_iSup_nat]
    exact (ENNReal.orderIsoRpow p hp0).map_iSup _
  simp_rw [hpt]
  rw [lintegral_iSup' (fun n => (Finset.aemeasurable_fun_sum _ fun i _ => hf i).pow_const p)
    (ae_of_all _ fun ω n m hnm => ENNReal.rpow_le_rpow
      (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hnm)) hp0.le)]
  have h1 := (ENNReal.orderIsoRpow (1 / p) (one_div_pos.2 hp0)).map_iSup
    (fun n => ∫⁻ ω, (∑ i ∈ Finset.range n, f i ω) ^ p ∂μ)
  simp only [ENNReal.orderIsoRpow_apply] at h1
  rw [h1]
  exact iSup_le fun n => (lintegral_sum_range_rpow_le hp hf n).trans (ENNReal.sum_le_tsum _)

/-! ## Interpolation between `L¹` and `L^q` -/

/-- **Lyapunov interpolation**: for `1 ≤ p ≤ q`, `1 < q`,
`E[g^p] ≤ E[g]^θ E[g^q]^{1−θ}` with `θ = (q − p)/(q − 1)`. -/
theorem lintegral_rpow_le_interp {g : Ω → ℝ≥0∞} (hg : AEMeasurable g μ) {p q : ℝ} (hp : 1 ≤ p)
    (hpq : p ≤ q) (hq : 1 < q) :
    ∫⁻ ω, g ω ^ p ∂μ ≤
      (∫⁻ ω, g ω ∂μ) ^ ((q - p) / (q - 1)) * (∫⁻ ω, g ω ^ q ∂μ) ^ ((p - 1) / (q - 1)) := by
  have hq1 : 0 < q - 1 := by linarith
  have hθ0 : 0 ≤ (q - p) / (q - 1) := div_nonneg (by linarith) hq1.le
  have hθ1 : 0 ≤ (p - 1) / (q - 1) := div_nonneg (by linarith) hq1.le
  have hsum : (q - p) / (q - 1) + (p - 1) / (q - 1) = 1 := by
    field_simp; ring
  have hpt : ∀ ω, g ω ^ p = g ω ^ ((q - p) / (q - 1)) * (g ω ^ q) ^ ((p - 1) / (q - 1)) := by
    intro ω
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add_of_nonneg _ _ hθ0
      (mul_nonneg (by linarith) hθ1)]
    congr 1
    field_simp; ring
  simp_rw [hpt]
  exact ENNReal.lintegral_mul_norm_pow_le hg (hg.pow_const q) hθ0 hθ1 hsum

/-! ## The supremum over levels -/

/-- Telescoping: `a_K ≤ a_0 + Σ_{k<K} |a_{k+1} − a_k|` for finite `a`. -/
theorem le_add_sum_incr (a : ℕ → ℝ≥0∞) (ha : ∀ k, a k ≠ ⊤) (K : ℕ) :
    a K ≤ a 0 + ∑ k ∈ Finset.range K, ENNReal.ofReal |(a (k + 1)).toReal - (a k).toReal| := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← add_assoc]
    calc a (K + 1)
        = ENNReal.ofReal ((a K).toReal + ((a (K + 1)).toReal - (a K).toReal)) := by
          rw [show (a K).toReal + ((a (K + 1)).toReal - (a K).toReal) = (a (K + 1)).toReal by
            ring, ENNReal.ofReal_toReal (ha _)]
      _ ≤ ENNReal.ofReal (a K).toReal +
            ENNReal.ofReal |(a (K + 1)).toReal - (a K).toReal| :=
          (ENNReal.ofReal_le_ofReal (by gcongr; exact le_abs_self _)).trans
            ENNReal.ofReal_add_le
      _ ≤ _ := by rw [ENNReal.ofReal_toReal (ha _)]; gcongr

/-- `sup_k a_k ≤ a_0 + Σ'_k |a_{k+1} − a_k|` for finite `a`. -/
theorem iSup_le_add_tsum_incr (a : ℕ → ℝ≥0∞) (ha : ∀ k, a k ≠ ⊤) :
    ⨆ k, a k ≤ a 0 + ∑' k, ENNReal.ofReal |(a (k + 1)).toReal - (a k).toReal| :=
  iSup_le fun K => (le_add_sum_incr a ha K).trans (by gcongr; exact ENNReal.sum_le_tsum _)

/-- The increment `|M_{k+1} − M_k|` as an `ℝ≥0∞`-valued function. -/
def incr (M : ℕ → Ω → ℝ≥0∞) (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal |(M (k + 1) ω).toReal - (M k ω).toReal|

theorem aemeasurable_incr {M : ℕ → Ω → ℝ≥0∞} (hM : ∀ k, AEMeasurable (M k) μ) (k : ℕ) :
    AEMeasurable (incr M k) μ :=
  ENNReal.measurable_ofReal.comp_aemeasurable (continuous_abs.measurable.comp_aemeasurable
    ((hM (k + 1)).ennreal_toReal.sub (hM k).ennreal_toReal))

omit [MeasurableSpace Ω] in
theorem incr_le (M : ℕ → Ω → ℝ≥0∞) (k : ℕ) (ω : Ω) (h1 : M (k + 1) ω ≠ ⊤) (h0 : M k ω ≠ ⊤) :
    incr M k ω ≤ M (k + 1) ω + M k ω := by
  unfold incr
  have ha := ENNReal.toReal_nonneg (a := M (k + 1) ω)
  have hb := ENNReal.toReal_nonneg (a := M k ω)
  calc ENNReal.ofReal |(M (k + 1) ω).toReal - (M k ω).toReal|
      ≤ ENNReal.ofReal ((M (k + 1) ω).toReal + (M k ω).toReal) :=
        ENNReal.ofReal_le_ofReal (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩)
    _ = M (k + 1) ω + M k ω := by
        rw [ENNReal.ofReal_add ha hb, ENNReal.ofReal_toReal h1, ENNReal.ofReal_toReal h0]

/-- A uniform `q`-th moment bound makes every `M_k` a.e. finite. -/
theorem ae_ne_top_of_lintegral_rpow {M : ℕ → Ω → ℝ≥0∞} (hM : ∀ k, AEMeasurable (M k) μ)
    {q : ℝ} {A' : ℝ≥0∞} (hq : 0 < q) (hA : A' ≠ ⊤) (hqA : ∀ k, ∫⁻ ω, M k ω ^ q ∂μ ≤ A') :
    ∀ᵐ ω ∂μ, ∀ k, M k ω ≠ ⊤ := by
  rw [ae_all_iff]
  intro k
  filter_upwards [ae_lt_top' ((hM k).pow_const q) (ne_top_of_le_ne_top hA (hqA k))] with ω hω
  intro h
  rw [h, ENNReal.top_rpow_of_pos hq] at hω
  exact lt_irrefl _ hω

/-- **The supremum over levels (explicit form).** Let `1 ≤ p < q`, `E[M_k^q] ≤ A < ∞` for all
`k`, and `E|M_{k+1} − M_k| ≤ B ρ^k`. Then, with `θ = (q − p)/(q − 1)`,
`‖sup_k M_k‖_p ≤ ‖M_0‖_p + Σ_k ((B ρ^k)^θ (2^q A)^{1−θ})^{1/p}`. -/
theorem lintegral_iSup_rpow_le_of_incr {M : ℕ → Ω → ℝ≥0∞} (hM : ∀ k, AEMeasurable (M k) μ)
    {p q : ℝ} (hp : 1 ≤ p) (hpq : p < q) {A B ρ : ℝ≥0∞} (hA : A ≠ ⊤)
    (hqA : ∀ k, ∫⁻ ω, M k ω ^ q ∂μ ≤ A)
    (hinc : ∀ k, ∫⁻ ω, incr M k ω ∂μ ≤ B * ρ ^ k) :
    (∫⁻ ω, (⨆ k, M k ω) ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ ω, M 0 ω ^ p ∂μ) ^ (1 / p) +
        ∑' k, ((B * ρ ^ k) ^ ((q - p) / (q - 1)) *
          (2 ^ q * A) ^ ((p - 1) / (q - 1))) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hq1 : 1 < q := by linarith
  have hq0 : 0 < q := by linarith
  have hfin := ae_ne_top_of_lintegral_rpow hM hq0 hA hqA
  have hD := aemeasurable_incr hM
  -- pointwise domination of the supremum
  have hle : ∫⁻ ω, (⨆ k, M k ω) ^ p ∂μ ≤ ∫⁻ ω, (M 0 ω + ∑' k, incr M k ω) ^ p ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hfin] with ω hω
    exact ENNReal.rpow_le_rpow (iSup_le_add_tsum_incr (fun k => M k ω) hω) hp0.le
  -- `q`-th moments of the increments
  have hDq : ∀ k, ∫⁻ ω, incr M k ω ^ q ∂μ ≤ 2 ^ q * A := by
    intro k
    calc ∫⁻ ω, incr M k ω ^ q ∂μ
        ≤ ∫⁻ ω, 2 ^ (q - 1) * (M (k + 1) ω ^ q + M k ω ^ q) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hfin] with ω hω
          exact (ENNReal.rpow_le_rpow (incr_le M k ω (hω _) (hω _)) hq0.le).trans
            (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq1.le)
      _ = 2 ^ (q - 1) * (∫⁻ ω, M (k + 1) ω ^ q ∂μ + ∫⁻ ω, M k ω ^ q ∂μ) := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
            ENNReal.ofNat_ne_top), lintegral_add_left' ((hM (k + 1)).pow_const q)]
      _ ≤ 2 ^ (q - 1) * (A + A) := by gcongr <;> exact hqA _
      _ = 2 ^ q * A := by
          rw [← two_mul, ← mul_assoc]
          congr 1
          conv_rhs => rw [show q = (q - 1) + 1 by ring]
          rw [ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, ENNReal.rpow_one]
  -- `L^p` norm of each increment
  have hDp : ∀ k, (∫⁻ ω, incr M k ω ^ p ∂μ) ^ (1 / p) ≤
      ((B * ρ ^ k) ^ ((q - p) / (q - 1)) * (2 ^ q * A) ^ ((p - 1) / (q - 1))) ^ (1 / p) := by
    intro k
    have hθ0 : 0 ≤ (q - p) / (q - 1) := div_nonneg (by linarith) (by linarith)
    have hθ1 : 0 ≤ (p - 1) / (q - 1) := div_nonneg (by linarith) (by linarith)
    refine ENNReal.rpow_le_rpow ((lintegral_rpow_le_interp (hD k) hp hpq.le hq1).trans ?_)
      (one_div_pos.2 hp0).le
    exact mul_le_mul' (ENNReal.rpow_le_rpow (hinc k) hθ0) (ENNReal.rpow_le_rpow (hDq k) hθ1)
  calc (∫⁻ ω, (⨆ k, M k ω) ^ p ∂μ) ^ (1 / p)
      ≤ (∫⁻ ω, (M 0 ω + ∑' k, incr M k ω) ^ p ∂μ) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hle (one_div_pos.2 hp0).le
    _ ≤ (∫⁻ ω, M 0 ω ^ p ∂μ) ^ (1 / p) + (∫⁻ ω, (∑' k, incr M k ω) ^ p ∂μ) ^ (1 / p) :=
        ENNReal.lintegral_Lp_add_le (hM 0) (AEMeasurable.tsum hD) hp
    _ ≤ _ := by
        gcongr
        exact (lintegral_tsum_rpow_le hp hD).trans (ENNReal.tsum_le_tsum hDp)

/-- On a probability space, a `q`-th moment bound gives the `p`-th moment for `p ≤ q`. -/
theorem lintegral_rpow_le_one_add [IsProbabilityMeasure μ] {g : Ω → ℝ≥0∞} {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) : ∫⁻ ω, g ω ^ p ∂μ ≤ 1 + ∫⁻ ω, g ω ^ q ∂μ := by
  calc ∫⁻ ω, g ω ^ p ∂μ ≤ ∫⁻ ω, (1 + g ω ^ q) ∂μ := by
        refine lintegral_mono fun ω => ?_
        rcases le_total (g ω) 1 with h | h
        · exact (ENNReal.rpow_le_one h hp).trans le_self_add
        · exact (ENNReal.rpow_le_rpow_of_exponent_le h hpq).trans le_add_self
    _ = 1 + ∫⁻ ω, g ω ^ q ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

/-- The geometric series of the increment bounds is finite. -/
theorem tsum_incrBound_ne_top {p q : ℝ} (hp : 1 ≤ p) (hpq : p < q) {A B ρ : ℝ≥0∞}
    (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hρ : ρ < 1) :
    ∑' k : ℕ, ((B * ρ ^ k) ^ ((q - p) / (q - 1)) *
      (2 ^ q * A) ^ ((p - 1) / (q - 1))) ^ (1 / p) ≠ ⊤ := by
  have hp0 : 0 < p := by linarith
  have hq1 : 0 < q - 1 := by linarith
  set θ := (q - p) / (q - 1) with hθ
  have hθ0 : 0 < θ := div_pos (by linarith) hq1
  have hθ1 : 0 ≤ (p - 1) / (q - 1) := div_nonneg (by linarith) hq1.le
  have hp1 : 0 < 1 / p := one_div_pos.2 hp0
  set C := (2 ^ q * A) ^ ((p - 1) / (q - 1)) with hC
  have hCt : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hθ1
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top) hA)
  set r := (ρ ^ θ) ^ (1 / p) with hr
  have hr1 : r < 1 := ENNReal.rpow_lt_one (ENNReal.rpow_lt_one hρ hθ0) hp1
  have hterm : ∀ k : ℕ, ((B * ρ ^ k) ^ θ * C) ^ (1 / p) = (B ^ θ * C) ^ (1 / p) * r ^ k := by
    intro k
    rw [ENNReal.mul_rpow_of_nonneg _ _ hθ0.le, mul_right_comm,
      ENNReal.mul_rpow_of_nonneg _ _ hp1.le, hr, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 2
    ring
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp1.le
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hθ0.le hB) hCt)) ?_
  exact ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hr1).ne'

/-- The explicit finite constant of the supremum bound on a probability space. -/
def supMomConst (p q : ℝ) (A B ρ : ℝ≥0∞) : ℝ≥0∞ :=
  ((1 + A) ^ (1 / p) + ∑' k : ℕ, ((B * ρ ^ k) ^ ((q - p) / (q - 1)) *
    (2 ^ q * A) ^ ((p - 1) / (q - 1))) ^ (1 / p)) ^ p

theorem supMomConst_ne_top {p q : ℝ} (hp : 1 ≤ p) (hpq : p < q) {A B ρ : ℝ≥0∞}
    (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hρ : ρ < 1) : supMomConst p q A B ρ ≠ ⊤ := by
  have hp0 : 0 < p := by linarith
  exact ENNReal.rpow_ne_top_of_nonneg hp0.le (ENNReal.add_ne_top.2
    ⟨ENNReal.rpow_ne_top_of_nonneg (one_div_pos.2 hp0).le
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hA⟩), tsum_incrBound_ne_top hp hpq hA hB hρ⟩)

theorem one_le_supMomConst {p q : ℝ} (hp : 1 ≤ p) (A B ρ : ℝ≥0∞) : 1 ≤ supMomConst p q A B ρ := by
  have hp0 : 0 < p := by linarith
  have h1 : (1 : ℝ≥0∞) ≤ (1 + A) ^ (1 / p) := by
    calc (1 : ℝ≥0∞) = 1 ^ (1 / p) := (ENNReal.one_rpow _).symm
      _ ≤ _ := ENNReal.rpow_le_rpow le_self_add (one_div_pos.2 hp0).le
  calc (1 : ℝ≥0∞) = 1 ^ p := (ENNReal.one_rpow _).symm
    _ ≤ _ := ENNReal.rpow_le_rpow (h1.trans le_self_add) hp0.le

/-- **The supremum over levels, probability-space form**: `1 ≤ p < q`, `sup_k E[M_k^q] ≤ A`,
`E|M_{k+1} − M_k| ≤ B ρ^k` give `E[(sup_k M_k)^p] ≤ supMomConst p q A B ρ` (finite when
`A, B < ∞`, `ρ < 1`: `supMomConst_ne_top`). -/
theorem lintegral_iSup_rpow_le_supMomConst [IsProbabilityMeasure μ] {M : ℕ → Ω → ℝ≥0∞}
    (hM : ∀ k, AEMeasurable (M k) μ) {p q : ℝ} (hp : 1 ≤ p) (hpq : p < q) {A B ρ : ℝ≥0∞}
    (hA : A ≠ ⊤) (hqA : ∀ k, ∫⁻ ω, M k ω ^ q ∂μ ≤ A)
    (hinc : ∀ k, ∫⁻ ω, incr M k ω ∂μ ≤ B * ρ ^ k) :
    ∫⁻ ω, (⨆ k, M k ω) ^ p ∂μ ≤ supMomConst p q A B ρ := by
  have hp0 : 0 < p := by linarith
  have h := lintegral_iSup_rpow_le_of_incr hM hp hpq hA hqA hinc
  have h0 : ∫⁻ ω, M 0 ω ^ p ∂μ ≤ 1 + A :=
    (lintegral_rpow_le_one_add hp0.le hpq.le).trans (by gcongr; exact hqA 0)
  have h' : (∫⁻ ω, (⨆ k, M k ω) ^ p ∂μ) ^ (1 / p) ≤ (1 + A) ^ (1 / p) +
      ∑' k : ℕ, ((B * ρ ^ k) ^ ((q - p) / (q - 1)) *
        (2 ^ q * A) ^ ((p - 1) / (q - 1))) ^ (1 / p) :=
    h.trans (by gcongr)
  calc ∫⁻ ω, (⨆ k, M k ω) ^ p ∂μ = ((∫⁻ ω, (⨆ k, M k ω) ^ p ∂μ) ^ (1 / p)) ^ p := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
    _ ≤ _ := ENNReal.rpow_le_rpow h' hp0.le

end GMCMoments
end QuantumZipper
