/-
The Laplace transform of the negated one-site law, in two parameter regimes:
a quadratic bound `exp(Cμ²)` for `μ ≤ 1`, which is what a centred law with an
exponential moment gives through `LatticeProb.Prob.SubGaussian`, and the bound
`exp(Cμ^(γ/(γ-1)))` for `μ ≥ 1`, which is what a stretched-exponential lower
tail with exponent `γ > 1` gives through Young's inequality.

Moved from Divisible-Sandpile-Percolation, `Sandpile/Support/Mgf.lean`. The
source file's own import, `Sandpile.Support.SubExponential`, is a full
duplicate of `LatticeProb.Prob.SubGaussian` (identical declaration set,
verified directly): every fact this file needs from it
(`subGaussianOn_of_exp_moment`, `integrable_id_of_exp_moment`) is already in
the library under that name.
-/
import LatticeProb.Prob.SubGaussian

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb

/-- `exp(-(μ z))` is at most `exp(μT)` plus a series of indicators of the lower
half-lines at integer depths below `-T`. -/
theorem ofReal_exp_neg_le_series (T μ : ℝ) (_hT : 0 ≤ T) (hμ : 0 ≤ μ) (z : ℝ) :
    ENNReal.ofReal (Real.exp (-(μ * z))) ≤
      ENNReal.ofReal (Real.exp (μ * T)) +
        ∑' k : ℕ, ENNReal.ofReal (Real.exp (μ * (T + (k : ℝ) + 1))) *
          (Set.Iic (-(T + (k : ℝ)))).indicator (fun _ => (1 : ℝ≥0∞)) z := by
  rcases le_or_gt (-T) z with hz | hz
  · refine le_trans ?_ le_self_add
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    nlinarith
  · set k₀ : ℕ := ⌊-z - T⌋₊ with hk₀
    have hpos : 0 ≤ -z - T := by linarith
    have hfloor : (k₀ : ℝ) ≤ -z - T := Nat.floor_le hpos
    have hfloor' : -z - T < (k₀ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hmem : z ∈ Set.Iic (-(T + (k₀ : ℝ))) := by
      simp only [Set.mem_Iic]
      linarith
    have hterm : ENNReal.ofReal (Real.exp (-(μ * z))) ≤
        ENNReal.ofReal (Real.exp (μ * (T + (k₀ : ℝ) + 1))) *
          (Set.Iic (-(T + (k₀ : ℝ)))).indicator (fun _ => (1 : ℝ≥0∞)) z := by
      rw [Set.indicator_of_mem hmem, mul_one]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      nlinarith
    refine le_trans hterm (le_trans (ENNReal.le_tsum k₀) le_add_self)

/-- Young's inequality in the absorbing form `μ x ≤ ε x^γ + K μ^{γ/(γ-1)}`. -/
theorem exists_young_absorb (γ ε : ℝ) (hγ : 1 < γ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ x μ : ℝ, 0 ≤ x → 0 ≤ μ →
      μ * x ≤ ε * x ^ γ + K * μ ^ (γ / (γ - 1)) := by
  set q : ℝ := γ / (γ - 1) with hq
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hγ1 : 0 < γ - 1 := by linarith
  have hqpos : 0 < q := by rw [hq]; positivity
  have hconj : γ.HolderConjugate q := by
    refine Real.holderConjugate_iff.mpr ⟨hγ, ?_⟩
    rw [hq]; field_simp; ring
  set a0 : ℝ := (ε * γ) ^ (γ⁻¹) with ha0
  have hεγ : 0 < ε * γ := by positivity
  have ha0pos : 0 < a0 := Real.rpow_pos_of_pos hεγ _
  have hpow : a0 ^ γ = ε * γ := by
    rw [ha0, ← Real.rpow_mul hεγ.le, inv_mul_cancel₀ hγ0.ne', Real.rpow_one]
  refine ⟨1 / (q * a0 ^ q), by positivity, fun x μ hx hμ => ?_⟩
  have h := Real.young_inequality_of_nonneg (a := a0 * x) (b := μ / a0)
    (by positivity) (by positivity) hconj
  have hab : (a0 * x) * (μ / a0) = μ * x := by field_simp
  have hga : (a0 * x) ^ γ / γ = ε * x ^ γ := by
    rw [Real.mul_rpow ha0pos.le hx, hpow]
    field_simp
  have hgb : (μ / a0) ^ q / q = (1 / (q * a0 ^ q)) * μ ^ q := by
    rw [Real.div_rpow hμ ha0pos.le]
    have : a0 ^ q ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha0pos _)
    field_simp
  rw [hab, hga, hgb] at h
  exact h

/-- The Laplace transform of the negated variable, bounded by the constant and
the series of half-line masses. -/
theorem lintegral_exp_neg_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (T μ : ℝ)
    (hT : 0 ≤ T) (hμ : 0 ≤ μ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (-(μ * z))) ∂ν ≤
      ENNReal.ofReal (Real.exp (μ * T)) +
        ∑' k : ℕ, ENNReal.ofReal (Real.exp (μ * (T + (k : ℝ) + 1))) *
          ν (Set.Iic (-(T + (k : ℝ)))) := by
  have hmeas : ∀ k : ℕ, AEMeasurable
      (fun z : ℝ => ENNReal.ofReal (Real.exp (μ * (T + (k : ℝ) + 1))) *
        (Set.Iic (-(T + (k : ℝ)))).indicator (fun _ => (1 : ℝ≥0∞)) z) ν := by
    intro k
    exact (measurable_const.mul
      ((measurable_const.indicator (measurableSet_Iic)))).aemeasurable
  calc ∫⁻ z, ENNReal.ofReal (Real.exp (-(μ * z))) ∂ν
      ≤ ∫⁻ z, (ENNReal.ofReal (Real.exp (μ * T)) +
          ∑' k : ℕ, ENNReal.ofReal (Real.exp (μ * (T + (k : ℝ) + 1))) *
            (Set.Iic (-(T + (k : ℝ)))).indicator (fun _ => (1 : ℝ≥0∞)) z) ∂ν :=
        lintegral_mono fun z => ofReal_exp_neg_le_series T μ hT hμ z
    _ = ENNReal.ofReal (Real.exp (μ * T)) +
        ∫⁻ z, (∑' k : ℕ, ENNReal.ofReal (Real.exp (μ * (T + (k : ℝ) + 1))) *
            (Set.Iic (-(T + (k : ℝ)))).indicator (fun _ => (1 : ℝ≥0∞)) z) ∂ν := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ = ENNReal.ofReal (Real.exp (μ * T)) +
        ∑' k : ℕ, ∫⁻ z, ENNReal.ofReal (Real.exp (μ * (T + (k : ℝ) + 1))) *
            (Set.Iic (-(T + (k : ℝ)))).indicator (fun _ => (1 : ℝ≥0∞)) z ∂ν := by
        rw [lintegral_tsum hmeas]
    _ = ENNReal.ofReal (Real.exp (μ * T)) +
        ∑' k : ℕ, ENNReal.ofReal (Real.exp (μ * (T + (k : ℝ) + 1))) *
          ν (Set.Iic (-(T + (k : ℝ)))) := by
        congr 1
        refine tsum_congr fun k => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_indicator_one measurableSet_Iic

/-- The shell series converges: at radius `T + k` with `T ≥ 1` the exponent
`(T+k)^γ` is at least `T+k`, so the terms are dominated by a geometric series. -/
theorem summable_shell (T c γ : ℝ) (hT : 1 ≤ T) (hc : 0 < c) (hγ : 1 ≤ γ) :
    Summable fun k : ℕ => Real.exp (-(c * (T + (k : ℝ)) ^ γ)) := by
  have hgeo : Summable fun k : ℕ => Real.exp (-(c * T)) * Real.exp (-c) ^ k := by
    refine Summable.mul_left _ (summable_geometric_of_lt_one (Real.exp_nonneg _) ?_)
    exact Real.exp_lt_one_iff.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_) hgeo
  have hbase : (1 : ℝ) ≤ T + (k : ℝ) := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hpow : T + (k : ℝ) ≤ (T + (k : ℝ)) ^ γ := by
    have := Real.rpow_le_rpow_of_exponent_le hbase hγ
    simpa using this
  have hstep : Real.exp (-(c * (T + (k : ℝ)) ^ γ)) ≤ Real.exp (-(c * (T + (k : ℝ)))) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  refine le_trans hstep (le_of_eq ?_)
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- **The large-parameter regime.**  A stretched-exponential lower tail with
exponent `γ > 1` gives `log E[e^{-μζ}] ≤ Cμ^(γ/(γ-1))` for `μ ≥ 1`. -/
theorem exists_mgf_neg_large (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (γ c₁ C₁ s₀ : ℝ) (hγ : 1 < γ) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (_hs₀ : 0 < s₀)
    (htail : ∀ s : ℝ, s₀ ≤ s →
      ν (Set.Iic (-s)) ≤ ENNReal.ofReal (C₁ * Real.exp (-(c₁ * s ^ γ)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, 1 ≤ μ →
      Integrable (fun z => Real.exp (-(μ * z))) ν ∧
        ∫ z, Real.exp (-(μ * z)) ∂ν ≤ Real.exp (C * μ ^ (γ / (γ - 1))) := by
  set T : ℝ := max s₀ 1 with hTdef
  have hT1 : (1 : ℝ) ≤ T := le_max_right _ _
  have hTs : s₀ ≤ T := le_max_left _ _
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set q : ℝ := γ / (γ - 1) with hqdef
  have hγ1 : (0 : ℝ) < γ - 1 := by linarith
  have hq1 : (1 : ℝ) < q := by
    rw [hqdef, lt_div_iff₀ hγ1]; linarith
  have hq0 : (0 : ℝ) ≤ q := by linarith
  obtain ⟨K, hK, hyoung⟩ := exists_young_absorb γ (c₁ / 2) hγ (by positivity)
  have hsum : Summable fun k : ℕ => Real.exp (-(c₁ / 2 * (T + (k : ℝ)) ^ γ)) :=
    summable_shell T (c₁ / 2) γ hT1 (by positivity) hγ.le
  set S : ℝ := ∑' k : ℕ, Real.exp (-(c₁ / 2 * (T + (k : ℝ)) ^ γ)) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun k => (Real.exp_pos _).le
  set B : ℝ := max T (K + 1) with hBdef
  have hB0 : 0 < B := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hlog0 : 0 ≤ Real.log (1 + C₁ * S) := Real.log_nonneg (by nlinarith)
  refine ⟨B + Real.log (1 + C₁ * S), by linarith, fun μ hμ => ?_⟩
  have hμ0 : (0 : ℝ) ≤ μ := by linarith
  have hqμ : (1 : ℝ) ≤ μ ^ q := Real.one_le_rpow hμ hq0
  have hμq : μ ≤ μ ^ q := by
    have := Real.rpow_le_rpow_of_exponent_le hμ hq1.le
    simpa using this
  -- the real series bound
  have hterm : ∀ k : ℕ,
      Real.exp (μ * (T + (k : ℝ) + 1)) * (C₁ * Real.exp (-(c₁ * (T + (k : ℝ)) ^ γ))) ≤
        C₁ * Real.exp ((K + 1) * μ ^ q) * Real.exp (-(c₁ / 2 * (T + (k : ℝ)) ^ γ)) := by
    intro k
    have hk0 : (0 : ℝ) ≤ T + (k : ℝ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hy := hyoung (T + (k : ℝ)) μ hk0 hμ0
    have hexp : μ * (T + (k : ℝ) + 1) + -(c₁ * (T + (k : ℝ)) ^ γ) ≤
        (K + 1) * μ ^ q + -(c₁ / 2 * (T + (k : ℝ)) ^ γ) := by nlinarith
    calc Real.exp (μ * (T + (k : ℝ) + 1)) * (C₁ * Real.exp (-(c₁ * (T + (k : ℝ)) ^ γ)))
        = C₁ * Real.exp (μ * (T + (k : ℝ) + 1) + -(c₁ * (T + (k : ℝ)) ^ γ)) := by
          rw [Real.exp_add]; ring
      _ ≤ C₁ * Real.exp ((K + 1) * μ ^ q + -(c₁ / 2 * (T + (k : ℝ)) ^ γ)) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC₁.le
      _ = C₁ * Real.exp ((K + 1) * μ ^ q) * Real.exp (-(c₁ / 2 * (T + (k : ℝ)) ^ γ)) := by
          rw [Real.exp_add]; ring
  have hsum2 : Summable fun k : ℕ =>
      Real.exp (μ * (T + (k : ℝ) + 1)) * (C₁ * Real.exp (-(c₁ * (T + (k : ℝ)) ^ γ))) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) hterm ?_
    exact (hsum.mul_left (C₁ * Real.exp ((K + 1) * μ ^ q)))
  have hseries : (∑' k : ℕ,
      Real.exp (μ * (T + (k : ℝ) + 1)) * (C₁ * Real.exp (-(c₁ * (T + (k : ℝ)) ^ γ)))) ≤
      C₁ * Real.exp ((K + 1) * μ ^ q) * S := by
    have := hsum2.tsum_le_tsum hterm (hsum.mul_left (C₁ * Real.exp ((K + 1) * μ ^ q)))
    rwa [tsum_mul_left] at this
  have hAle : Real.exp (μ * T) +
      (∑' k : ℕ, Real.exp (μ * (T + (k : ℝ) + 1)) *
        (C₁ * Real.exp (-(c₁ * (T + (k : ℝ)) ^ γ)))) ≤
      Real.exp ((B + Real.log (1 + C₁ * S)) * μ ^ q) := by
    have h1 : Real.exp (μ * T) ≤ Real.exp (B * μ ^ q) := by
      refine Real.exp_le_exp.mpr ?_
      have : T ≤ B := le_max_left _ _
      nlinarith
    have h2 : C₁ * Real.exp ((K + 1) * μ ^ q) * S ≤ C₁ * S * Real.exp (B * μ ^ q) := by
      have hKB : K + 1 ≤ B := le_max_right _ _
      have : Real.exp ((K + 1) * μ ^ q) ≤ Real.exp (B * μ ^ q) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith
      calc C₁ * Real.exp ((K + 1) * μ ^ q) * S
          = C₁ * S * Real.exp ((K + 1) * μ ^ q) := by ring
        _ ≤ C₁ * S * Real.exp (B * μ ^ q) :=
            mul_le_mul_of_nonneg_left this (by positivity)
    have h3 : Real.exp (B * μ ^ q) + C₁ * S * Real.exp (B * μ ^ q) ≤
        Real.exp ((B + Real.log (1 + C₁ * S)) * μ ^ q) := by
      have hfac : (1 + C₁ * S) * Real.exp (B * μ ^ q) =
          Real.exp (Real.log (1 + C₁ * S)) * Real.exp (B * μ ^ q) := by
        rw [Real.exp_log (by nlinarith)]
      have hmono : Real.exp (Real.log (1 + C₁ * S)) * Real.exp (B * μ ^ q) ≤
          Real.exp ((B + Real.log (1 + C₁ * S)) * μ ^ q) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        nlinarith
      nlinarith [hfac, hmono]
    linarith
  -- the ENNReal chain
  have hlint : ∫⁻ z, ENNReal.ofReal (Real.exp (-(μ * z))) ∂ν ≤
      ENNReal.ofReal (Real.exp ((B + Real.log (1 + C₁ * S)) * μ ^ q)) := by
    refine le_trans (lintegral_exp_neg_le ν T μ hT0 hμ0) ?_
    have hstep : ∀ k : ℕ,
        ENNReal.ofReal (Real.exp (μ * (T + (k : ℝ) + 1))) * ν (Set.Iic (-(T + (k : ℝ)))) ≤
          ENNReal.ofReal (Real.exp (μ * (T + (k : ℝ) + 1)) *
            (C₁ * Real.exp (-(c₁ * (T + (k : ℝ)) ^ γ)))) := by
      intro k
      have hk : s₀ ≤ T + (k : ℝ) := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]
      exact mul_le_mul' le_rfl (htail _ hk)
    calc ENNReal.ofReal (Real.exp (μ * T)) +
          ∑' k : ℕ, ENNReal.ofReal (Real.exp (μ * (T + (k : ℝ) + 1))) *
            ν (Set.Iic (-(T + (k : ℝ))))
        ≤ ENNReal.ofReal (Real.exp (μ * T)) +
          ∑' k : ℕ, ENNReal.ofReal (Real.exp (μ * (T + (k : ℝ) + 1)) *
            (C₁ * Real.exp (-(c₁ * (T + (k : ℝ)) ^ γ)))) :=
          add_le_add le_rfl (ENNReal.tsum_le_tsum hstep)
      _ = ENNReal.ofReal (Real.exp (μ * T) +
            ∑' k : ℕ, Real.exp (μ * (T + (k : ℝ) + 1)) *
              (C₁ * Real.exp (-(c₁ * (T + (k : ℝ)) ^ γ)))) := by
          rw [ENNReal.ofReal_add (Real.exp_nonneg _)
            (tsum_nonneg fun k => by positivity),
            ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum2]
      _ ≤ ENNReal.ofReal (Real.exp ((B + Real.log (1 + C₁ * S)) * μ ^ q)) :=
          ENNReal.ofReal_le_ofReal hAle
  have hmeas : AEStronglyMeasurable (fun z : ℝ => Real.exp (-(μ * z))) ν :=
    (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[ν] fun z : ℝ => Real.exp (-(μ * z)) := by
    filter_upwards with z
    simpa using (Real.exp_pos (-(μ * z))).le
  have hint : Integrable (fun z => Real.exp (-(μ * z))) ν := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _) hlint

/-- **Both regimes at once.**  For a centred law with an exponential moment and
a stretched-exponential lower tail with exponent `γ > 1`, the Laplace
transform of the negated variable is finite for every parameter, is
`exp(Cμ²)` below one, and is `exp(Cμ^(γ/(γ-1)))` above one. -/
theorem exists_mgf_neg_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀)
    (hmean : ∫ z, z ∂ν = 0)
    (γ c₁ C₁ s₀ : ℝ) (hγ : 1 < γ) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hs₀ : 0 < s₀)
    (htail : ∀ s : ℝ, s₀ ≤ s →
      ν (Set.Iic (-s)) ≤ ENNReal.ofReal (C₁ * Real.exp (-(c₁ * s ^ γ)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, 0 ≤ μ →
      Integrable (fun z => Real.exp (-(μ * z))) ν ∧
        (μ ≤ 1 → ∫ z, Real.exp (-(μ * z)) ∂ν ≤ Real.exp (C * μ ^ 2)) ∧
        (1 ≤ μ → ∫ z, Real.exp (-(μ * z)) ∂ν ≤ Real.exp (C * μ ^ (γ / (γ - 1)))) := by
  obtain ⟨CL, hCL, hlarge⟩ :=
    exists_mgf_neg_large ν γ c₁ C₁ s₀ hγ hc₁ hC₁ hs₀ htail
  have hK₀ : (1 : ℝ) ≤ K₀ := by
    have h1 : ∫ z : ℝ, (1 : ℝ) ∂ν ≤ ∫ z, Real.exp (θ₀ * |z|) ∂ν := by
      refine integral_mono (integrable_const 1) hexpint fun z => ?_
      have : (0 : ℝ) ≤ θ₀ * |z| := by positivity
      simpa using Real.one_le_exp this
    have huniv : ν.real Set.univ = 1 := by simp
    simp only [integral_const, smul_eq_mul, huniv, mul_one] at h1
    linarith
  have hid : Integrable id ν := integrable_id_of_exp_moment ν θ₀ hθ₀ hexpint
  have hSG := subGaussianOn_of_exp_moment ν θ₀ K₀ hθ₀ hexpint hexp hid hmean
  set cSG : ℝ := 16 / θ₀ ^ 2 * K₀ with hcSG
  have hcSG0 : 0 < cSG := by rw [hcSG]; positivity
  -- the value at parameter one
  obtain ⟨hint1, hval1⟩ := hlarge 1 le_rfl
  have hE1 : (1 : ℝ) ≤ Real.exp CL + 1 := by
    have := Real.exp_pos CL; linarith
  set E1 : ℝ := Real.exp CL + 1 with hE1def
  have hlogE1 : 0 ≤ Real.log E1 := Real.log_nonneg hE1
  set C : ℝ := max (max cSG (4 * Real.log E1 / θ₀ ^ 2)) CL with hCdef
  have hCcSG : cSG ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hClog : 4 * Real.log E1 / θ₀ ^ 2 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCCL : CL ≤ C := le_max_right _ _
  have hC0 : 0 < C := lt_of_lt_of_le hcSG0 hCcSG
  have hval1' : ∫ z, Real.exp (-(1 * z)) ∂ν ≤ Real.exp CL := by
    have : (1 : ℝ) ^ (γ / (γ - 1)) = 1 := Real.one_rpow _
    rw [this, mul_one] at hval1
    exact hval1
  -- the small-parameter branch
  have hsmall : ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 →
      Integrable (fun z => Real.exp (-(μ * z))) ν ∧
        ∫ z, Real.exp (-(μ * z)) ∂ν ≤ Real.exp (C * μ ^ 2) := by
    intro μ hμ0 hμ1
    rcases le_or_gt μ (θ₀ / 2) with hcase | hcase
    · have habs : |(-μ)| ≤ θ₀ / 2 := by rw [abs_neg, abs_of_nonneg hμ0]; exact hcase
      obtain ⟨hi, hb⟩ := hSG (-μ) habs
      have hi' : Integrable (fun z => Real.exp (-(μ * z))) ν := by
        refine hi.congr (Filter.Eventually.of_forall fun z => ?_)
        simp [id]
      refine ⟨hi', ?_⟩
      have hb' : ∫ z, Real.exp (-(μ * z)) ∂ν ≤ Real.exp (cSG * (-μ) ^ 2) := by
        refine le_trans (le_of_eq ?_) hb
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp [id]
      refine le_trans hb' (Real.exp_le_exp.mpr ?_)
      have : (-μ) ^ 2 = μ ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hCcSG (by positivity)
    · have hdom : ∀ z : ℝ, Real.exp (-(μ * z)) ≤ Real.exp (-(1 * z)) + 1 := by
        intro z
        rcases le_or_gt z 0 with hz | hz
        · have : -(μ * z) ≤ -(1 * z) := by nlinarith
          have := Real.exp_le_exp.mpr this
          linarith [Real.exp_pos (-(1 * z))]
        · have : -(μ * z) ≤ 0 := by nlinarith
          have h2 : Real.exp (-(μ * z)) ≤ 1 := by
            simpa using Real.exp_le_one_iff.mpr this
          linarith [Real.exp_pos (-(1 * z))]
      have hgint : Integrable (fun z : ℝ => Real.exp (-(1 * z)) + 1) ν :=
        hint1.add (integrable_const 1)
      have hi : Integrable (fun z => Real.exp (-(μ * z))) ν := by
        refine Integrable.mono' hgint
          ((Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hdom z
      refine ⟨hi, ?_⟩
      have hle : ∫ z, Real.exp (-(μ * z)) ∂ν ≤ E1 := by
        have hstep := integral_mono hi hgint hdom
        have hsplit : ∫ z, (Real.exp (-(1 * z)) + 1) ∂ν
            = (∫ z, Real.exp (-(1 * z)) ∂ν) + 1 := by
          rw [integral_add hint1 (integrable_const 1)]
          simp
        rw [hsplit] at hstep
        rw [hE1def]
        linarith
      refine le_trans hle ?_
      have hlog : Real.log E1 ≤ C * μ ^ 2 := by
        have hμsq : θ₀ ^ 2 / 4 ≤ μ ^ 2 := by nlinarith
        have h1 : C * (θ₀ ^ 2 / 4) ≤ C * μ ^ 2 := mul_le_mul_of_nonneg_left hμsq hC0.le
        have h2 : 4 * Real.log E1 / θ₀ ^ 2 * (θ₀ ^ 2 / 4) ≤ C * (θ₀ ^ 2 / 4) :=
          mul_le_mul_of_nonneg_right hClog (by positivity)
        have h3 : 4 * Real.log E1 / θ₀ ^ 2 * (θ₀ ^ 2 / 4) = Real.log E1 := by
          field_simp
        linarith
      calc E1 = Real.exp (Real.log E1) := (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp (C * μ ^ 2) := Real.exp_le_exp.mpr hlog
  refine ⟨C, hC0, fun μ hμ0 => ?_⟩
  have hi : Integrable (fun z => Real.exp (-(μ * z))) ν := by
    rcases le_or_gt μ 1 with h | h
    · exact (hsmall μ hμ0 h).1
    · exact (hlarge μ h.le).1
  refine ⟨hi, fun hμ1 => (hsmall μ hμ0 hμ1).2, fun hμ1 => ?_⟩
  refine le_trans (hlarge μ hμ1).2 (Real.exp_le_exp.mpr ?_)
  exact mul_le_mul_of_nonneg_right hCCL (Real.rpow_nonneg hμ0 _)

end LatticeProb
