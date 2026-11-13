/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCUpper.MassGrid at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCUpper.TranslatedMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.WeightedMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ConeTight
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeas2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L4Max

/-!
# From cone mass moments to a uniform small-ball bound

We split centres at a small power of the ball radius. A single cone-point
ball handles near centres. A square grid and the translated whole-plane
moment handle the remaining centres.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric LQGMetric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCUpper

private theorem measure_mass_gt_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P)
    {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    P {ω | ENNReal.ofReal a < f ω} ≤
      (∫⁻ ω, f ω ^ p ∂P) / ENNReal.ofReal (a ^ p) := by
  have hset : {ω | ENNReal.ofReal a < f ω} ⊆
      {ω | ENNReal.ofReal (a ^ p) ≤ f ω ^ p} := by
    intro ω hω
    rw [← ENNReal.ofReal_rpow_of_pos ha]
    exact ENNReal.rpow_le_rpow hω.le hp.le
  calc
    P {ω | ENNReal.ofReal a < f ω} ≤
        P {ω | ENNReal.ofReal (a ^ p) ≤ f ω ^ p} := measure_mono hset
    _ ≤ (∫⁻ ω, f ω ^ p ∂P) / ENNReal.ofReal (a ^ p) :=
      meas_ge_le_lintegral_div (hf.pow_const p)
        (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos ha _)).ne' ENNReal.ofReal_ne_top

theorem measure_mass_gt_le_rpow
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P)
    {δ p ξ e : ℝ} (hδ : 0 < δ) (hp : 0 < p)
    {C : ℝ≥0∞}
    (hI : ∫⁻ ω, f ω ^ p ∂P ≤ C * ENNReal.ofReal (δ ^ e)) :
    P {ω | ENNReal.ofReal (δ ^ ξ) < f ω} ≤
      C * ENNReal.ofReal (δ ^ (e - ξ * p)) := by
  have hpow : 0 < δ ^ ξ := Real.rpow_pos_of_pos hδ _
  calc
    P {ω | ENNReal.ofReal (δ ^ ξ) < f ω} ≤
        (∫⁻ ω, f ω ^ p ∂P) / ENNReal.ofReal ((δ ^ ξ) ^ p) :=
          measure_mass_gt_le hf hpow hp
    _ ≤ (C * ENNReal.ofReal (δ ^ e)) /
        ENNReal.ofReal ((δ ^ ξ) ^ p) := ENNReal.div_le_div_right hI _
    _ = C * ENNReal.ofReal (δ ^ (e - ξ * p)) := by
      rw [← Real.rpow_mul hδ.le, div_eq_mul_inv, mul_assoc]
      conv_lhs =>
        rhs
        rw [← ENNReal.ofReal_rpow_of_pos hδ]
        rw [← ENNReal.ofReal_rpow_of_pos hδ]
      rw [← ENNReal.rpow_neg, ← ENNReal.rpow_add]
      rw [ENNReal.ofReal_rpow_of_pos hδ]
      congr 1
      ring
      exact (ENNReal.ofReal_pos.2 hδ).ne'
      exact ENNReal.ofReal_ne_top

private def massSquare : Set ℂ := LQGMetric.SupTail.ferniqueBox ⟨-1, -1⟩ 2

private lemma ball_subset_massSquare {ρ : ℝ} (hρ : ρ ≤ 1) :
    ball (0 : ℂ) ρ ⊆ massSquare := by
  intro z hz
  have hnorm : ‖z‖ < 1 := (mem_ball_zero_iff.1 hz).trans_le hρ
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  rw [massSquare, LQGMetric.DG.mem_ferniqueBox_iff]
  dsimp
  constructor
  · linarith [neg_abs_le z.re]
  constructor
  · linarith [le_abs_self z.re]
  constructor
  · linarith [neg_abs_le z.im]
  · linarith [le_abs_self z.im]

private lemma ball_subset_grid_ball {z w : ℂ} {δ : ℝ}
    (hzw : ‖z - w‖ ≤ δ) : ball z δ ⊆ ball w (2 * δ) := by
  intro x hx
  rw [mem_ball, dist_eq_norm] at hx ⊢
  calc
    ‖x - w‖ = ‖(x - z) + (z - w)‖ := by congr 1; abel
    _ ≤ ‖x - z‖ + ‖z - w‖ := norm_add_le _ _
    _ < 2 * δ := by linarith

theorem grid_card_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (((⌈4 / δ⌉₊ + 1 : ℕ) : ℝ)) ^ 2 ≤ 36 * δ ^ (-2 : ℝ) := by
  set m := ⌈4 / δ⌉₊
  have hm : (m : ℝ) < 4 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  have h1 : ((m : ℝ) + 1) ≤ 6 / δ := by
    rw [le_div_iff₀ hδ]
    have hd : δ * (4 / δ) = 4 := mul_div_cancel₀ _ hδ.ne'
    have hm' : ((m : ℝ) + 1) * δ < 4 + 2 * δ := by
      have := mul_lt_mul_of_pos_right hm hδ
      have hdiv : 4 / δ * δ = 4 := div_mul_cancel₀ _ hδ.ne'
      rw [add_mul] at this
      rw [hdiv] at this
      linarith
    nlinarith
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1) h1 2
  have hpow : (6 / δ) ^ 2 = 36 * δ ^ (-2 : ℝ) := by
    rw [div_pow, show (6 : ℝ) ^ 2 = 36 by norm_num]
    rw [Real.rpow_neg (by positivity)]
    field_simp
    norm_cast
  simpa only [Nat.cast_add, Nat.cast_one, hpow] using hsq

def massGridPt (δ : ℝ)
    (ij : Fin (⌈4 / δ⌉₊ + 1) × Fin (⌈4 / δ⌉₊ + 1)) : ℂ :=
  LQGMetric.DG.gridPt ⟨-1, -1⟩ 2 ⌈4 / δ⌉₊ ij.1 ij.2

def massGridEligible (ρ δ t : ℝ) (w : ℂ) : Prop :=
  ∃ z ∈ ball (0 : ℂ) ρ, t < ‖z‖ ∧ ‖z - w‖ ≤ δ

theorem far_bad_subset_grid
    {Ω : Type*} [MeasurableSpace Ω] (μ : Ω → Measure ℂ)
    {ρ δ t a : ℝ} (hρ : ρ ≤ 1) (hδ : 0 < δ) :
    {ω | ∃ z ∈ ball (0 : ℂ) ρ,
      t < ‖z‖ ∧ ENNReal.ofReal a < μ ω (ball z δ)} ⊆
      ⋃ ij : Fin (⌈4 / δ⌉₊ + 1) × Fin (⌈4 / δ⌉₊ + 1),
        {ω | massGridEligible ρ δ t (massGridPt δ ij) ∧
          ENNReal.ofReal a < μ ω (ball (massGridPt δ ij) (2 * δ))} := by
  intro ω ⟨z, hz, hzt, hbad⟩
  have hgrid := LQGMetric.DG.exists_gridPt_near
    (x₀ := ⟨-1, -1⟩) (s := 2) (by norm_num) hδ (ball_subset_massSquare hρ hz)
  have hfour : (2 : ℝ) * 2 / δ = 4 / δ := by ring
  rw [hfour] at hgrid
  obtain ⟨i, j, -, hzw⟩ := hgrid
  have hsub := ball_subset_grid_ball hzw
  refine mem_iUnion.2 ⟨(i, j), ?_⟩
  exact ⟨⟨z, hz, hzt, hzw⟩, hbad.trans_le (measure_mono hsub)⟩

theorem exists_outer_exponents (g : ℝ) (hg : 0 < g) (hg4 : g < 4) :
    ∃ q p : ℝ, 0 < q ∧ q < p ∧ p < 4 / g ∧
      2 < q * (2 + g / 2) - p * q * g / 2 := by
  let q : ℝ := (g + 4) / (2 * g)
  have hq1 : 1 < q := by
    dsimp [q]
    rw [lt_div_iff₀ (by positivity : 0 < 2 * g)]
    linarith
  have hq4 : q < 4 / g := by
    dsimp [q]
    rw [div_lt_div_iff₀ (by positivity : 0 < 2 * g) hg]
    nlinarith
  have hqg : 0 < q * g := mul_pos (lt_trans zero_lt_one hq1) hg
  let v : ℝ := q * (2 + g / 2) - q ^ 2 * g / 2 - 2
  have hv : v = (4 - g) ^ 2 / (8 * g) := by
    dsimp [v, q]
    field_simp
    ring
  have hvpos : 0 < v := by
    rw [hv]
    exact div_pos (sq_pos_of_pos (by linarith)) (by positivity)
  let d : ℝ := min (4 / g - q) (v / (q * g))
  have hd : 0 < d := lt_min (by linarith) (div_pos hvpos hqg)
  let p : ℝ := q + d / 2
  refine ⟨q, p, lt_trans zero_lt_one hq1, by dsimp [p]; linarith,
    by dsimp [p]; have := min_le_left (4 / g - q) (v / (q * g)); linarith, ?_⟩
  have hsmall : p - q < v / (q * g) := by
    dsimp [p]
    have := min_le_right (4 / g - q) (v / (q * g))
    linarith
  have hmul : (p - q) * (q * g) < v :=
    (lt_div_iff₀ hqg).1 hsmall
  have hid : q * (2 + g / 2) - p * q * g / 2 - 2 =
      v - (p - q) * (q * g) / 2 := by dsimp [v]; ring
  rw [show 2 < q * (2 + g / 2) - p * q * g / 2 ↔
    0 < q * (2 + g / 2) - p * q * g / 2 - 2 by constructor <;> intro h <;> linarith,
    hid]
  nlinarith [hmul, hvpos]

theorem far_rpow_factor {δ e : ℝ} (hδ : 0 < δ) (C : ℝ≥0∞) :
    ENNReal.ofReal (36 * δ ^ (-2 : ℝ)) * C * ENNReal.ofReal (δ ^ e) =
      (ENNReal.ofReal 36 * C) * ENNReal.ofReal (δ ^ (e - 2)) := by
  have hc : ENNReal.ofReal (δ ^ (-2 : ℝ)) * ENNReal.ofReal (δ ^ e) =
      ENNReal.ofReal (δ ^ (e - 2)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ← Real.rpow_add hδ]
    congr 1
    ring
  rw [ENNReal.ofReal_mul (by norm_num)]
  calc
    _ = (ENNReal.ofReal (δ ^ (-2 : ℝ)) * ENNReal.ofReal (δ ^ e)) *
        (ENNReal.ofReal 36 * C) := by ring
    _ = _ := by rw [hc]; ring

end MatedCRTHarmonic.GMCUpper
