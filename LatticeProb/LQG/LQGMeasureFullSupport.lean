import Mathlib
import LatticeProb.Gauss.GFF
import LatticeProb.LQG.LQGMeasure
import LatticeProb.LQG.LQGMeasureNonatomicMassPoly

/-!
# Volume growth at all small scales and full support

Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795],
Lemma 2.4 and the full-support property of the LQG measure, which that paper states informally. The file covers the
ball-mass event of the ball-volume estimate of Lemma 2.4 (with its window lemma), the volume growth at all small scales
derived from the step of Lemma 2.4, and full support, with the predicates `IsWholePlaneGFF`, `IsLQGMeasureOfField` and
`PolyHighProb`.

* Steps (stated as definitions): `LiouvilleBallMassBoundStepLP`, with the event `ballMassBoundEventLP`.
* Statements (stated as definitions with these predicates): `LQGVolumeGrowthAllScalesStmtLP` (volume growth at all small
  scales) and `LQGMeasureFullSupportStmtLP` (full support of the LQG measure).
* Proved reductions: `lqgVolumeGrowthAllScalesStmt_of_ballMass_lp` (Borel-Cantelli along the dyadic scales) and
  `lqgMeasureFullSupportStmt_of_volumeGrowth_lp`. Nothing is assumed.
-/

namespace LatticeProb.LQG

open MeasureTheory Metric Filter Set
open scoped ENNReal
open LatticeProb.Gauss
open LatticeProb.LQG.LQGMeasureNonatomicMass

universe u

/-- The event of the ball-volume estimate of Lemma 2.4 on `B_R(0)` at scale `ε`:
`ε^{β⁻} ≤ μ(B_ε(z)) ≤ ε^{β⁺}` for every `z ∈ B_R(0)`. -/
def ballMassBoundEventLP {Ω : Type*} (μ : Ω → Measure ℂ) (R βplus βminus ε : ℝ) : Set Ω :=
  {ω | ∀ z ∈ ball (0 : ℂ) R,
    ENNReal.ofReal (ε ^ βminus) ≤ μ ω (ball z ε) ∧ μ ω (ball z ε) ≤ ENNReal.ofReal (ε ^ βplus)}

/-- Step of Lemma 2.4: the ball-volume estimate for centres in every ball `B_R(0)`, with polynomially high probability as `ε → 0`, for each `R > 0`,
`β⁺ ∈ (0, min {(2-γ)²/2, γ(Q-α₀)})` and `β⁻ > max {(2+γ)²/2, γ(Q-α₀)}`. A definition. -/
def LiouvilleBallMassBoundStepLP : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ R : ℝ, 0 < R → ∀ βplus βminus : ℝ, 0 < βplus → βplus < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) →
    max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < βminus →
    PolyHighProb P (ballMassBoundEventLP μ R βplus βminus)

/-- Volume growth at all small scales: for every `R > 0` and exponents in the ranges stated below, a.s. there is `r₀ > 0` with `r^{β⁻} ≤ μ_h(B_r(z)) ≤ r^{β⁺}` for all `r ∈ (0, r₀)` and
`z ∈ B_R`. -/
def LQGVolumeGrowthAllScalesStmtLP : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ βplus βminus : ℝ, 0 < βplus →
    βplus < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) → max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < βminus →
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      ENNReal.ofReal (r ^ βminus) ≤ μ ω (ball z r) ∧ μ ω (ball z r) ≤ ENNReal.ofReal (r ^ βplus)

/-- Full support of the LQG measure: almost surely `μ_h(U) > 0` for every nonempty open `U ⊆ ℂ`. -/
def LQGMeasureFullSupportStmtLP : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U

/-- With slack in the exponents (`a < β⁺`, `b > β⁻`), the ball bounds at the two scales `ε` and `ε/2` give the
bounds with exponents `(a, b)` at every radius `s ∈ [ε/2, ε]`, for small `ε` (the window lemma `ballMassBoundEvent_window`). -/
theorem ballMassBoundEventLP_window {Ω : Type*} (μ : Ω → Measure ℂ) {R a b βplus βminus : ℝ}
    (ha : 0 < a) (hab : a < βplus) (hb : 0 < b) (hba : βminus < b) :
    ∃ r₁ > 0, ∀ ε : ℝ, 0 < ε → ε < r₁ →
      ballMassBoundEventLP μ R βplus βminus ε ∩ ballMassBoundEventLP μ R βplus βminus (2⁻¹ * ε) ⊆
        {ω | ∀ s : ℝ, 2⁻¹ * ε ≤ s → s ≤ ε → ∀ z ∈ ball (0 : ℂ) R,
          ENNReal.ofReal (s ^ b) ≤ μ ω (ball z s) ∧ μ ω (ball z s) ≤ ENNReal.ofReal (s ^ a)} := by
  obtain ⟨r₁, hr₁, h₁⟩ := exists_pos_forall_rpow_le (sub_pos.2 hab)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2⁻¹) a)
  obtain ⟨r₂, hr₂, h₂⟩ := exists_pos_forall_rpow_le (sub_pos.2 hba)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2⁻¹) βminus)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun ε hε hεr ω ⟨hω₁, hω₂⟩ s hs₁ hs₂ z hz => ?_⟩
  have hs : 0 < s := lt_of_lt_of_le (by positivity) hs₁
  have hε₁ := h₁ ε hε (hεr.trans_le (min_le_left _ _))
  have hε₂ := h₂ ε hε (hεr.trans_le (min_le_right _ _))
  refine ⟨?_, ?_⟩
  · have hle : s ^ b ≤ (2⁻¹ * ε) ^ βminus := by
      calc s ^ b ≤ ε ^ b := Real.rpow_le_rpow hs.le hs₂ hb.le
        _ = ε ^ (b - βminus) * ε ^ βminus := by rw [← Real.rpow_add hε, sub_add_cancel]
        _ ≤ 2⁻¹ ^ βminus * ε ^ βminus := by gcongr
        _ = (2⁻¹ * ε) ^ βminus := by rw [Real.mul_rpow (by norm_num) hε.le]
    calc ENNReal.ofReal (s ^ b) ≤ ENNReal.ofReal ((2⁻¹ * ε) ^ βminus) := ENNReal.ofReal_le_ofReal hle
      _ ≤ μ ω (ball z (2⁻¹ * ε)) := (hω₂ z hz).1
      _ ≤ μ ω (ball z s) := measure_mono (ball_subset_ball hs₁)
  · have hle : ε ^ βplus ≤ s ^ a := by
      calc ε ^ βplus = ε ^ (βplus - a) * ε ^ a := by rw [← Real.rpow_add hε, sub_add_cancel]
        _ ≤ 2⁻¹ ^ a * ε ^ a := by gcongr
        _ = (2⁻¹ * ε) ^ a := by rw [Real.mul_rpow (by norm_num) hε.le]
        _ ≤ s ^ a := Real.rpow_le_rpow (by positivity) hs₁ ha.le
    calc μ ω (ball z s) ≤ μ ω (ball z ε) := measure_mono (ball_subset_ball hs₂)
      _ ≤ ENNReal.ofReal (ε ^ βplus) := (hω₁ z hz).2
      _ ≤ ENNReal.ofReal (s ^ a) := ENNReal.ofReal_le_ofReal hle

/-- Volume growth at all small scales (`LQGVolumeGrowthAllScalesStmtLP`) from `LiouvilleBallMassBoundStepLP`: Borel-Cantelli along the dyadic scales,
over the countable family of radii `R = n + 1` and rational exponents. -/
theorem lqgVolumeGrowthAllScalesStmt_of_ballMass_lp (h : LiouvilleBallMassBoundStepLP.{u}) :
    LQGVolumeGrowthAllScalesStmtLP.{u} := by
  intro γ α₀ hγ hγ2 hα₀ Ω _ P hC hcirc μ hGFF hμ
  have hM0 : 0 < max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) :=
    lt_max_of_lt_left (by have : 0 < 2 + γ := by linarith
                          positivity)
  have key : ∀ i : ℕ × ℚ × ℚ, ∀ᵐ ω ∂P, 0 < (i.2.1 : ℝ) →
      (i.2.1 : ℝ) < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) →
      max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < (i.2.2 : ℝ) →
      ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) (i.1 + 1),
        ENNReal.ofReal (r ^ (i.2.2 : ℝ)) ≤ μ ω (ball z r) ∧
          μ ω (ball z r) ≤ ENNReal.ofReal (r ^ (i.2.1 : ℝ)) := by
    rintro ⟨n, a, b⟩
    by_cases hcond : 0 < (a : ℝ) ∧ (a : ℝ) < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) ∧
        max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < (b : ℝ)
    swap
    · exact Eventually.of_forall fun ω h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hcond
    obtain ⟨ha, ham, hMb⟩ := hcond
    set m := min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀))
    set M := max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀))
    have hstep := h γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ ((n : ℝ) + 1) (by positivity)
      ((a + m) / 2) ((b + M) / 2) (by linarith) (by linarith) (by linarith)
    obtain ⟨r₁, hr₁, hwin⟩ := ballMassBoundEventLP_window μ (R := (n : ℝ) + 1) ha
      (by linarith : (a : ℝ) < (a + m) / 2) (by linarith : (0 : ℝ) < b)
      (by linarith : (b + M) / 2 < (b : ℝ))
    have hpoly := polyHighProb_mono_of_small
      (polyHighProb_inter hstep (polyHighProb_comp_mul hstep (by norm_num : (0 : ℝ) < 2⁻¹))) hr₁ hwin
    filter_upwards [polyHighProb_ae_eventually_dyadic hpoly] with ω hω _ _ _
    obtain ⟨K, hK⟩ := eventually_atTop.1 hω
    refine ⟨(2 : ℝ)⁻¹ ^ K, by positivity, fun r hr hrK z hz => ?_⟩
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hr
      (hrK.le.trans (pow_le_one₀ (by norm_num) (by norm_num))) (by norm_num : (0 : ℝ) < 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    have hkK : K ≤ k := by
      by_contra hlt
      have h' : k + 1 ≤ K := by omega
      have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num) h'
      linarith
    refine hK k hkK r ?_ hk2 z hz
    rw [pow_succ] at hk1
    linarith
  filter_upwards [ae_all_iff.2 key] with ω hω R hR βplus βminus hβp hβpm hβmM
  obtain ⟨a, hβa, ham⟩ := exists_rat_btwn hβpm
  obtain ⟨b, hMb, hbβ⟩ := exists_rat_btwn hβmM
  obtain ⟨r₀, hr₀, hr⟩ := hω (⌈R⌉₊, a, b) (hβp.trans hβa) ham hMb
  refine ⟨min r₀ 1, lt_min hr₀ one_pos, fun r hr0 hrr z hz => ?_⟩
  have hz' : z ∈ ball (0 : ℂ) ((⌈R⌉₊ : ℝ) + 1) :=
    ball_subset_ball (by linarith [Nat.le_ceil R]) hz
  obtain ⟨h1, h2⟩ := hr r hr0 (hrr.trans_le (min_le_left _ _)) z hz'
  have hr1 : r < 1 := hrr.trans_le (min_le_right _ _)
  exact ⟨le_trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le hbβ.le)) h1,
    h2.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le hβa.le))⟩

/-- Full support (`LQGMeasureFullSupportStmtLP`) from volume growth: every nonempty open set contains a small ball, whose mass is at
least `r^{β⁻} > 0`. -/
theorem lqgMeasureFullSupportStmt_of_volumeGrowth_lp (h : LQGVolumeGrowthAllScalesStmtLP.{u}) :
    LQGMeasureFullSupportStmtLP.{u} := by
  intro γ α₀ hγ hγ2 hα₀ Ω _ P hC hcirc μ hGFF hμ
  have hm : 0 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) := by
    have h1 : 0 < 2 - γ := by linarith
    have h2 : 0 < lqgQ γ - α₀ := by linarith
    exact lt_min (by positivity) (by positivity)
  filter_upwards [h γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hω U hU hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨r₀, hr₀, hr⟩ := hω (‖x‖ + 1) (by positivity) _
    (max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) + 1) (half_pos hm) (half_lt_self hm) (lt_add_one _)
  have hmin : 0 < min δ r₀ := lt_min hδ hr₀
  have hpos : 0 < min δ r₀ / 2 := half_pos hmin
  have hlt : min δ r₀ / 2 < min δ r₀ := half_lt_self hmin
  obtain ⟨h1, -⟩ := hr (min δ r₀ / 2) hpos (hlt.trans_le (min_le_right _ _)) x
    (by rw [mem_ball_zero_iff]; linarith)
  calc (0 : ℝ≥0∞) < ENNReal.ofReal ((min δ r₀ / 2) ^ (max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) + 1)) :=
        ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hpos _)
    _ ≤ μ ω (ball x (min δ r₀ / 2)) := h1
    _ ≤ μ ω U := measure_mono ((ball_subset_ball (hlt.le.trans (min_le_left _ _))).trans hδU)

end LatticeProb.LQG
