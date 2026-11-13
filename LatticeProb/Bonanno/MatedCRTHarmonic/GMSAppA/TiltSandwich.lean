/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.TiltSandwich at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LongRange

/-!
# The change-of-measure sandwich for a single density

[18], proof of Lemma A.3, (A.13)–(A.18), at a *fixed* shift: if
`ρ ≥ 0` is a density on a probability space `(S, ν)` and `Ψ ≥ 0`, then

* `∫ Ψ ρ ≤ (1 + t) ∫ Ψ + ∫ Ψ ρ 1_{ρ > 1+t}` and `∫ Ψ ≤ ∫ Ψ ρ + t ∫ Ψ + ∫ Ψ 1_{ρ < 1−t}` (the sandwich);
* `∫ Ψ ρ 1_{ρ>1+t} + ∫ Ψ 1_{ρ<1−t} ≤ (∫ Ψ^{p₀})^{1/p₀} · 2 e^{θ(2q²V − qt/4)}`, `θ = 1 − 1/p₀`, when `ρ` has the
  moments of a Gaussian tilt with variance `≤ V` (`∫ρ^q ≤ e^{q²V/2}`, `∫ρ^{−q} ≤ e^{q²V}`, `∫ρ^{2r} ≤ e^{2r²V}`,
  `r = p₀/(p₀ − 1)`, `q ≥ max(1, r)`), by Hölder (A.17)–(A.18) and Chebyshev (A.16).

These are applied pointwise in the coupling variables, so that no measurability of the density in the shift is needed
(the shift is deterministic once the coupling variables are fixed; cf. MoTPort's `GFFAbsCont.absCont_resOn_of_markov`).

* `GMSAppA.lintegral_mul_ofReal_le_tilt`, `GMSAppA.lintegral_le_tilt` — the sandwich.
* `GMSAppA.tails_le_tilt` — the tail bound with the explicit factor `tiltTail`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

variable {S : Type*} [MeasurableSpace S] {ν : Measure S}

/-- the upper tail part `ρ Ψ 1_{ρ > 1+t}` -/
def tUp (Ψ : S → ℝ≥0∞) (ρ : S → ℝ) (t : ℝ) : S → ℝ≥0∞ :=
  {s | 1 + t < ρ s}.indicator fun s => (ENNReal.ofReal (ρ s) * Ψ s) ^ (1 : ℝ)

/-- the lower tail part `Ψ 1_{ρ < 1−t}` -/
def tLo (Ψ : S → ℝ≥0∞) (ρ : S → ℝ) (t : ℝ) : S → ℝ≥0∞ :=
  {s | ρ s < 1 - t}.indicator fun s => Ψ s ^ (1 : ℝ)

/-- **The upper sandwich** `∫ Ψ ρ ≤ (1+t) ∫ Ψ + ∫ Ψ ρ 1_{ρ>1+t}`. -/
theorem lintegral_mul_ofReal_le_tilt {Ψ : S → ℝ≥0∞} (hΨ : Measurable Ψ) {ρ : S → ℝ}
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s, Ψ s * ENNReal.ofReal (ρ s) ∂ν ≤
      ENNReal.ofReal (1 + t) * ∫⁻ s, Ψ s ∂ν + ∫⁻ s, tUp Ψ ρ t s ∂ν := by
  have hpt : ∀ s, Ψ s * ENNReal.ofReal (ρ s) ≤ ENNReal.ofReal (1 + t) * Ψ s + tUp Ψ ρ t s := by
    intro s
    by_cases h : 1 + t < ρ s
    · have : tUp Ψ ρ t s = ENNReal.ofReal (ρ s) * Ψ s := by
        simp only [tUp, Set.indicator_of_mem (show s ∈ {s | 1 + t < ρ s} from h), ENNReal.rpow_one]
      rw [this, mul_comm]
      exact le_add_self
    · have : tUp Ψ ρ t s = 0 := by
        simp only [tUp, Set.indicator_of_notMem (show s ∉ {s | 1 + t < ρ s} from h)]
      rw [this, add_zero, mul_comm]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (not_lt.1 h)) _
  calc ∫⁻ s, Ψ s * ENNReal.ofReal (ρ s) ∂ν
      ≤ ∫⁻ s, (ENNReal.ofReal (1 + t) * Ψ s + tUp Ψ ρ t s) ∂ν := lintegral_mono hpt
    _ = ENNReal.ofReal (1 + t) * ∫⁻ s, Ψ s ∂ν + ∫⁻ s, tUp Ψ ρ t s ∂ν := by
        rw [lintegral_add_left (hΨ.const_mul _), lintegral_const_mul _ hΨ]

/-- **The lower sandwich** `∫ Ψ ≤ ∫ Ψ ρ + t ∫ Ψ + ∫ Ψ 1_{ρ<1−t}`. -/
theorem lintegral_le_tilt {Ψ : S → ℝ≥0∞} (hΨ : Measurable Ψ) {ρ : S → ℝ} (hρm : Measurable ρ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s, Ψ s ∂ν ≤ ∫⁻ s, Ψ s * ENNReal.ofReal (ρ s) ∂ν + ENNReal.ofReal t * ∫⁻ s, Ψ s ∂ν +
      ∫⁻ s, tLo Ψ ρ t s ∂ν := by
  have hpt : ∀ s, Ψ s ≤ Ψ s * ENNReal.ofReal (ρ s) + ENNReal.ofReal t * Ψ s + tLo Ψ ρ t s := by
    intro s
    by_cases h : ρ s < 1 - t
    · have : tLo Ψ ρ t s = Ψ s := by
        simp only [tLo, Set.indicator_of_mem (show s ∈ {s | ρ s < 1 - t} from h), ENNReal.rpow_one]
      rw [this]
      exact le_add_self
    · have : tLo Ψ ρ t s = 0 := by
        simp only [tLo, Set.indicator_of_notMem (show s ∉ {s | ρ s < 1 - t} from h)]
      rw [this, add_zero]
      have h1 : 1 ≤ ENNReal.ofReal (ρ s) + ENNReal.ofReal t :=
        calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
          _ ≤ ENNReal.ofReal (ρ s + t) := ENNReal.ofReal_le_ofReal (by linarith [not_lt.1 h])
          _ ≤ ENNReal.ofReal (ρ s) + ENNReal.ofReal t := ENNReal.ofReal_add_le
      calc Ψ s = Ψ s * 1 := (mul_one _).symm
        _ ≤ Ψ s * (ENNReal.ofReal (ρ s) + ENNReal.ofReal t) := mul_le_mul_right h1 _
        _ = Ψ s * ENNReal.ofReal (ρ s) + ENNReal.ofReal t * Ψ s := by ring
  calc ∫⁻ s, Ψ s ∂ν
      ≤ ∫⁻ s, (Ψ s * ENNReal.ofReal (ρ s) + ENNReal.ofReal t * Ψ s + tLo Ψ ρ t s) ∂ν :=
        lintegral_mono hpt
    _ = ∫⁻ s, Ψ s * ENNReal.ofReal (ρ s) ∂ν + ENNReal.ofReal t * ∫⁻ s, Ψ s ∂ν +
        ∫⁻ s, tLo Ψ ρ t s ∂ν := by
        have hlo : Measurable (tLo Ψ ρ t) :=
          (hΨ.pow_const _).indicator (measurableSet_lt hρm measurable_const)
        have hpr : Measurable fun s => Ψ s * ENNReal.ofReal (ρ s) := hΨ.mul hρm.ennreal_ofReal
        rw [lintegral_add_right _ hlo, lintegral_add_left hpr, lintegral_const_mul _ hΨ]

/-- the tail factor `2 e^{θ(2q²V − qt/4)}`, `θ = 1 − 1/p₀` -/
def tiltTail (p₀ q t V : ℝ) : ℝ := 2 * Real.exp ((1 - 1 / p₀) * (2 * q ^ 2 * V - q * t / 4))

lemma tiltTail_nonneg (p₀ q t V : ℝ) : 0 ≤ tiltTail p₀ q t V := by
  unfold tiltTail; positivity

/-- **(A.16)–(A.18) at a fixed shift**: for a density `ρ` with the moments of a Gaussian tilt of variance `≤ V`,
`∫ Ψ ρ 1_{ρ>1+t} + ∫ Ψ 1_{ρ<1−t} ≤ (∫ Ψ^{p₀})^{1/p₀} · tiltTail p₀ q t V`. -/
theorem tails_le_tilt [IsProbabilityMeasure ν] {Ψ : S → ℝ≥0∞} (hΨ : Measurable Ψ) {ρ : S → ℝ}
    (hρm : Measurable ρ) {p₀ q t V : ℝ} (hp₀ : 1 < p₀) (hq1 : 1 ≤ q) (hqr : p₀ / (p₀ - 1) ≤ q)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hV : 0 ≤ V)
    (hmP : ∫⁻ s, ENNReal.ofReal (ρ s) ^ q ∂ν ≤ ENNReal.ofReal (Real.exp (q ^ 2 * V / 2)))
    (hmN : ∫⁻ s, ENNReal.ofReal (ρ s) ^ (-q) ∂ν ≤ ENNReal.ofReal (Real.exp (q ^ 2 * V)))
    (hm₂ : ∫⁻ s, ENNReal.ofReal (ρ s) ^ (2 * (1 * (p₀ / (p₀ - 1)))) ∂ν ≤
      ENNReal.ofReal (Real.exp (2 * (p₀ / (p₀ - 1)) ^ 2 * V))) :
    ∫⁻ s, tUp Ψ ρ t s ∂ν + ∫⁻ s, tLo Ψ ρ t s ∂ν ≤
      (∫⁻ s, Ψ s ^ p₀ ∂ν) ^ (1 / p₀) * ENNReal.ofReal (tiltTail p₀ q t V) := by
  have hp₀0 : 0 < p₀ := by linarith
  set r := p₀ / (p₀ - 1) with hr
  have hr0 : 0 < r := div_pos hp₀0 (by linarith)
  set θ := 1 - 1 / p₀ with hθ
  have hθ0 : 0 < θ := by
    rw [hθ, sub_pos, div_lt_one hp₀0]; exact hp₀
  have hq0 : 0 < q := by linarith
  set A : Set S := {s | 1 + t < ρ s}
  set B : Set S := {s | ρ s < 1 - t}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hρm
  have hB : MeasurableSet B := measurableSet_lt hρm measurable_const
  have hT := lintegral_mul_rpow_indicator_le (P := ν) hΨ.aemeasurable hρm.ennreal_ofReal.aemeasurable
    hA one_pos hp₀
  have hI := lintegral_rpow_indicator_le (P := ν) hΨ.aemeasurable hB one_pos hp₀
  -- Markov for the two tails
  have hPA : ν A ≤ ENNReal.ofReal (Real.exp (q ^ 2 * V / 2) * Real.exp (-(q * t) / 2)) := by
    refine (measure_gt_le_lintegral_rpow hρm (by linarith : (0 : ℝ) < 1 + t) hq0).trans ?_
    have h1 : ENNReal.ofReal (1 + t) ^ q = ENNReal.ofReal ((1 + t) ^ q) :=
      ENNReal.ofReal_rpow_of_nonneg (by linarith) hq0.le
    have hpos : 0 < (1 + t) ^ q := Real.rpow_pos_of_pos (by linarith) _
    rw [h1]
    calc (∫⁻ s, ENNReal.ofReal (ρ s) ^ q ∂ν) / ENNReal.ofReal ((1 + t) ^ q)
        ≤ ENNReal.ofReal (Real.exp (q ^ 2 * V / 2)) / ENNReal.ofReal ((1 + t) ^ q) := by
          gcongr
      _ = ENNReal.ofReal (Real.exp (q ^ 2 * V / 2) * (1 + t) ^ (-q)) := by
          rw [← ENNReal.ofReal_div_of_pos hpos, Real.rpow_neg (by linarith), div_eq_mul_inv]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
          (one_add_rpow_neg_le_exp ht0 ht1.le hq0.le) (Real.exp_pos _).le)
  have hPB : ν B ≤ ENNReal.ofReal (Real.exp (q ^ 2 * V) * Real.exp (-(q * t))) := by
    refine (measure_lt_le_lintegral_rpow_neg hρm (by linarith : (0 : ℝ) < 1 - t) hq0).trans ?_
    have h1 : ENNReal.ofReal (1 - t) ^ q = ENNReal.ofReal ((1 - t) ^ q) :=
      ENNReal.ofReal_rpow_of_nonneg (by linarith) hq0.le
    rw [h1]
    calc (∫⁻ s, ENNReal.ofReal (ρ s) ^ (-q) ∂ν) * ENNReal.ofReal ((1 - t) ^ q)
        ≤ ENNReal.ofReal (Real.exp (q ^ 2 * V)) * ENNReal.ofReal ((1 - t) ^ q) := by gcongr
      _ = ENNReal.ofReal (Real.exp (q ^ 2 * V) * (1 - t) ^ q) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
          (one_sub_rpow_le_exp ht1 hq0.le) (Real.exp_pos _).le)
  -- the upper tail factor
  set N₀ := (∫⁻ s, Ψ s ^ p₀ ∂ν) ^ (1 / p₀)
  have hfac1 : ((∫⁻ s, ENNReal.ofReal (ρ s) ^ (2 * (1 * r)) ∂ν) ^ (1 / 2 : ℝ) * ν A ^ (1 / 2 : ℝ)) ^
      (1 - 1 / p₀) ≤ ENNReal.ofReal (Real.exp (θ * (2 * q ^ 2 * V - q * t / 4))) := by
    have hstep : (∫⁻ s, ENNReal.ofReal (ρ s) ^ (2 * (1 * r)) ∂ν) ^ (1 / 2 : ℝ) * ν A ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (Real.exp (2 * r ^ 2 * V) * (Real.exp (q ^ 2 * V / 2) *
          Real.exp (-(q * t) / 2))) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      gcongr
    refine (ENNReal.rpow_le_rpow hstep hθ0.le).trans ?_
    rw [← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_mul]
    refine Real.exp_le_exp.2 ?_
    have hrq : r ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hr0.le hqr 2
    have hθ' : (1 / 2 : ℝ) * θ = θ / 2 := by ring
    rw [hθ']
    have h7 : 0 ≤ 7 * q ^ 2 / 4 - r ^ 2 := by nlinarith [sq_nonneg q]
    nlinarith [mul_nonneg (mul_nonneg hθ0.le hV) h7]
  have hfac2 : ν B ^ (1 - 1 / p₀) ≤ ENNReal.ofReal (Real.exp (θ * (2 * q ^ 2 * V - q * t / 4))) := by
    refine (ENNReal.rpow_le_rpow hPB hθ0.le).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hθ0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_add, ← Real.exp_mul]
    refine Real.exp_le_exp.2 ?_
    have h3 : 0 ≤ q ^ 2 * V + 3 * (q * t) / 4 :=
      add_nonneg (mul_nonneg (sq_nonneg q) hV) (by have := mul_nonneg hq0.le ht0; linarith)
    nlinarith [mul_nonneg hθ0.le h3]
  calc ∫⁻ s, tUp Ψ ρ t s ∂ν + ∫⁻ s, tLo Ψ ρ t s ∂ν
      ≤ N₀ * ((∫⁻ s, ENNReal.ofReal (ρ s) ^ (2 * (1 * r)) ∂ν) ^ (1 / 2 : ℝ) *
          ν A ^ (1 / 2 : ℝ)) ^ (1 - 1 / p₀) + N₀ * ν B ^ (1 - 1 / p₀) := add_le_add hT hI
    _ ≤ N₀ * ENNReal.ofReal (Real.exp (θ * (2 * q ^ 2 * V - q * t / 4))) +
        N₀ * ENNReal.ofReal (Real.exp (θ * (2 * q ^ 2 * V - q * t / 4))) := by
        gcongr
    _ = N₀ * ENNReal.ofReal (tiltTail p₀ q t V) := by
        rw [← mul_add, ← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, tiltTail]
        congr 2
        ring

end MatedCRTHarmonic.GMSAppA
