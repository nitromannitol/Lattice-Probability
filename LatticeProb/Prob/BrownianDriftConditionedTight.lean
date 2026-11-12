/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.BrownianDriftConditionedModulus

/-!
# Uniform modulus estimate for the drifted Brownian motion conditioned to stay above `-δ`

Let `Y t = B t + c t` with `c > 0`, let `G_δ = {Y t > -δ for all t}`.  For every level `ε > 0`
and time `η₀ > 0`, the event on `G_δ` that `Y` has no modulus `ε + δ + a` at scale `η₁` on
`[0, T]` has probability at most `P(G_δ)` times a quantity which, in the regime `δ ≤ ε`, is
`(2ε)² / (η₀ ε)` plus the Brownian modulus bound divided by `1 - e^{-2cε}`.  The Brownian modulus
bound tends to zero with the scale, so that for a given `ε` the scale `η'` can be chosen to make
the whole bound small, uniformly in `δ`.

* `LatticeProb.measure_stayAbove_inter_not_hasModulus_le`: the estimate on `G_δ`, without
  restriction on the hitting time.
* `LatticeProb.exists_modulusBound_le`: the Brownian modulus bound at the scale `η'` is arbitrarily
  small for `η'` small.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

section Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Uniform modulus estimate on the conditioned event.** -/
theorem measure_stayAbove_inter_not_hasModulus_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) {η : ℝ≥0} (hη : 0 < η) {D : Set ℝ≥0} (hD : D.Countable) (hDd : Dense D)
    {T T' η₁ η' : ℝ≥0} (hT : T < T') (hη₁ : η₁ < η') (hη' : 0 < η') {a : ℝ} (ha : c * η' < a) :
    P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩
        {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) T η₁ (ε + δ + a)}) ≤
      P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} *
        ((η : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((ε + δ) ^ 2) +
          (ENNReal.ofReal (1 - Real.exp (-(2 * c * ε))))⁻¹ *
            (((⌈(T' : ℝ) / η'⌉₊ + 1 : ℕ) : ℝ≥0∞) *
              (4 * ENNReal.ofReal
                (Real.exp (-(((a - c * η') / 2) ^ 2 / (32 * (2 * (η' : ℝ))))))))) := by
  set G : Set Ω := {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} with hG
  set H : Set Ω := {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)} with hH
  set X : Set Ω := {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) T η₁ (ε + δ + a)} with hX
  set Bd : ℝ≥0∞ := ((⌈(T' : ℝ) / η'⌉₊ + 1 : ℕ) : ℝ≥0∞) *
    (4 * ENNReal.ofReal (Real.exp (-(((a - c * η') / 2) ^ 2 / (32 * (2 * (η' : ℝ))))))) with hBd
  have hsub : G ∩ X ⊆ (G ∩ H ∩ X) ∪ (G ∩ {ω | (η : ℝ≥0∞) < hitDrift B c ε ω}) := by
    intro ω hω
    by_cases h : hitDrift B c ε ω ≤ (η : ℝ≥0∞)
    · exact Or.inl ⟨⟨hω.1, h⟩, hω.2⟩
    · exact Or.inr ⟨hω.1, not_le.1 h⟩
  -- the part after the time `η`
  have h2 : P (G ∩ {ω | (η : ℝ≥0∞) < hitDrift B c ε ω}) ≤
      P G * ((η : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((ε + δ) ^ 2)) := by
    have := mul_measure_stayAbove_inter_lt_hitDrift_le hB hm hcont hc hε hδ η
    have hη0 : (η : ℝ≥0∞) ≠ 0 := by exact_mod_cast hη.ne'
    rw [ENNReal.mul_le_iff_le_inv hη0 ENNReal.coe_ne_top] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  -- the part before the time `η`
  have hfε : 0 < 1 - Real.exp (-(2 * c * ε)) := by
    have : Real.exp (-(2 * c * ε)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    linarith
  have h1 : P (G ∩ H ∩ X) ≤
      P G * ((ENNReal.ofReal (1 - Real.exp (-(2 * c * ε))))⁻¹ * Bd) := by
    have hmain := measure_stayAbove_inter_not_hasModulus_mul_le hB hm hcont hc hε hδ η hD hDd hT
      hη₁ hη' ha
    have hmono : ENNReal.ofReal (1 - Real.exp (-(2 * c * ε))) ≤
        ENNReal.ofReal (1 - Real.exp (-(2 * c * (ε + δ)))) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have : Real.exp (-(2 * c * (ε + δ))) ≤ Real.exp (-(2 * c * ε)) :=
        Real.exp_le_exp.2 (by nlinarith)
      linarith
    have h3 : P (G ∩ H ∩ X) * ENNReal.ofReal (1 - Real.exp (-(2 * c * ε))) ≤ P G * Bd :=
      calc _ ≤ P (G ∩ H ∩ X) * ENNReal.ofReal (1 - Real.exp (-(2 * c * (ε + δ)))) :=
            mul_le_mul' le_rfl hmono
        _ ≤ P (G ∩ H) * Bd := hmain
        _ ≤ P G * Bd := mul_le_mul' (measure_mono Set.inter_subset_left) le_rfl
    have hf0 : ENNReal.ofReal (1 - Real.exp (-(2 * c * ε))) ≠ 0 :=
      (ENNReal.ofReal_pos.2 hfε).ne'
    rw [mul_comm, ENNReal.mul_le_iff_le_inv hf0 ENNReal.ofReal_ne_top] at h3
    calc _ ≤ _ := h3
      _ = _ := by ring
  calc P (G ∩ X) ≤ P ((G ∩ H ∩ X) ∪ (G ∩ {ω | (η : ℝ≥0∞) < hitDrift B c ε ω})) :=
        measure_mono hsub
    _ ≤ P (G ∩ H ∩ X) + P (G ∩ {ω | (η : ℝ≥0∞) < hitDrift B c ε ω}) := measure_union_le _ _
    _ ≤ _ := by
      calc _ ≤ P G * ((ENNReal.ofReal (1 - Real.exp (-(2 * c * ε))))⁻¹ * Bd) +
          P G * ((η : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((ε + δ) ^ 2)) := add_le_add h1 h2
        _ = _ := by ring

end Prob


/-- The function `x ↦ 4 ((T/κ) x + 2) e^{-x}` tends to zero at infinity. -/
theorem tendsto_poly_mul_exp_neg (T κ : ℝ) :
    Tendsto (fun x : ℝ => 4 * ((T / κ) * x + 2) * Real.exp (-x)) atTop (𝓝 0) := by
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 := Real.tendsto_exp_neg_atTop_nhds_zero
  have h3 := ((h1.const_mul (4 * (T / κ))).add (h2.const_mul 8))
  simp only [pow_one, mul_zero, add_zero] at h3
  refine h3.congr fun x => ?_
  ring

/-- **The Brownian modulus bound is small at small scales.**  For `c, a > 0`, `T ≥ 0` and `r > 0`
there are arbitrarily small scales `η'` with `c η' < a` at which the bound of
`LatticeProb.measure_badMod_le` for the level `a - c η'` is at most `r`. -/
theorem exists_modulusBound_le (T : ℝ≥0) {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 0 < a) {r : ℝ}
    (hr : 0 < r) {m : ℝ≥0} (hm : 0 < m) :
    ∃ η' : ℝ≥0, 0 < η' ∧ η' < m ∧ c * η' < a ∧
      (((⌈(T : ℝ) / η'⌉₊ + 1 : ℕ) : ℝ≥0∞) *
        (4 * ENNReal.ofReal
          (Real.exp (-(((a - c * η') / 2) ^ 2 / (32 * (2 * (η' : ℝ)))))))) ≤ ENNReal.ofReal r := by
  set κ : ℝ := a ^ 2 / 1024 with hκ
  have hκ0 : 0 < κ := by positivity
  set g : ℝ → ℝ := fun η => 4 * ((T / κ) * (κ * η⁻¹) + 2) * Real.exp (-(κ * η⁻¹)) with hg
  have hx : Tendsto (fun η : ℝ => κ * η⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop hκ0
  have hlim : Tendsto g (𝓝[>] 0) (𝓝 0) := (tendsto_poly_mul_exp_neg (T : ℝ) κ).comp hx
  set ηm : ℝ := min (m : ℝ) (a / (2 * (c + 1))) with hηm
  have hηm0 : 0 < ηm := lt_min (by exact_mod_cast hm) (by positivity)
  have e0 : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η := eventually_mem_nhdsWithin
  have e1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Set.Ioo 0 ηm := Ioo_mem_nhdsGT hηm0
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ η < ηm ∧ g η < r :=
    (e0.and (e1.and (hlim.eventually (gt_mem_nhds hr)))).mono fun η h => ⟨h.1, h.2.1.2, h.2.2⟩
  obtain ⟨η, hη0, hηlt, hgη⟩ := hev.exists
  refine ⟨⟨η, hη0.le⟩, by exact_mod_cast hη0, ?_, ?_, ?_⟩
  · have : η < (m : ℝ) := lt_of_lt_of_le hηlt (min_le_left _ _)
    exact_mod_cast this
  · have h1 : η < a / (2 * (c + 1)) := lt_of_lt_of_le hηlt (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    show c * η < a
    nlinarith
  · have h1 : η < a / (2 * (c + 1)) := lt_of_lt_of_le hηlt (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    have hcη : c * η ≤ a / 2 := by nlinarith
    show (((⌈(T : ℝ) / η⌉₊ + 1 : ℕ) : ℝ≥0∞) *
        (4 * ENNReal.ofReal
          (Real.exp (-(((a - c * η) / 2) ^ 2 / (32 * (2 * η))))))) ≤ ENNReal.ofReal r
    have hceil : ((⌈(T : ℝ) / η⌉₊ + 1 : ℕ) : ℝ) ≤ (T : ℝ) / η + 2 := by
      have := Nat.ceil_lt_add_one (R := ℝ) (a := (T : ℝ) / η) (by positivity)
      push_cast
      linarith
    have hexp : Real.exp (-(((a - c * η) / 2) ^ 2 / (32 * (2 * η)))) ≤ Real.exp (-(κ * η⁻¹)) := by
      refine Real.exp_le_exp.2 ?_
      rw [neg_le_neg_iff]
      have h2 : a / 4 ≤ (a - c * η) / 2 := by linarith
      have h3 : (a / 4) ^ 2 ≤ ((a - c * η) / 2) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity) h2
      have h4 : κ * η⁻¹ = (a / 4) ^ 2 / (32 * (2 * η)) := by
        rw [hκ]; field_simp; ring
      rw [h4]
      exact div_le_div_of_nonneg_right h3 (by positivity)
    have hreal : ((⌈(T : ℝ) / η⌉₊ + 1 : ℕ) : ℝ) *
        (4 * Real.exp (-(((a - c * η) / 2) ^ 2 / (32 * (2 * η))))) ≤ r := by
      refine le_trans ?_ hgη.le
      have hTκ : (T : ℝ) / κ * (κ * η⁻¹) = (T : ℝ) / η := by
        field_simp
      simp only [hg, hTκ]
      calc _ ≤ ((T : ℝ) / η + 2) * (4 * Real.exp (-(κ * η⁻¹))) := by
            apply mul_le_mul hceil (by gcongr) (by positivity) (by positivity)
        _ = _ := by ring
    calc _ = ENNReal.ofReal (((⌈(T : ℝ) / η⌉₊ + 1 : ℕ) : ℝ) *
          (4 * Real.exp (-(((a - c * η) / 2) ^ 2 / (32 * (2 * η)))))) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal


section Uniform

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Uniform small-`δ` modulus of the conditioned drifted motion.**  For every modulus level
`w > 0`, horizon `T` and tolerance `ρ > 0`, there are `ε > 0` and a scale `η₁ > 0` such that, for
every `0 < δ ≤ ε`, the drifted motion `B + c ·` conditioned on `{B t + c t > -δ for all t}` has no
modulus `w` at scale `η₁` on `[0, T]` with conditional probability at most `ρ`. -/
theorem exists_uniform_modulus [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    (T : ℝ≥0) {w ρ : ℝ} (hw : 0 < w) (hρ : 0 < ρ) :
    ∃ (ε : ℝ) (η₁ : ℝ≥0), 0 < ε ∧ 0 < η₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩
          {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) T η₁ w}) ≤
        ENNReal.ofReal ρ * P {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  set ε : ℝ := min (w / 4) (ρ / 8) with hεdef
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεw : ε ≤ w / 4 := min_le_left _ _
  have hερ : ε ≤ ρ / 8 := min_le_right _ _
  set f : ℝ := 1 - Real.exp (-(2 * c * ε)) with hf
  have hf0 : 0 < f := by
    have : Real.exp (-(2 * c * ε)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    linarith
  have hr : 0 < f * ρ / 2 := by positivity
  obtain ⟨η', hη'0, -, hcη', hbd⟩ := exists_modulusBound_le (T + 1) hc (a := w / 2)
    (by positivity) hr (m := 1) one_pos
  have hη₁ : η' / 2 < η' := half_lt_self hη'0
  refine ⟨ε, η' / 2, hε, half_pos hη'0, fun δ hδ hδε => ?_⟩
  have hε0 : 0 < ε.toNNReal := Real.toNNReal_pos.2 hε
  have key := measure_stayAbove_inter_not_hasModulus_le hB hm hcont hc hε hδ hε0 hDc hDd
    (T := T) (T' := T + 1) (η₁ := η' / 2) (η' := η') (lt_add_one T) hη₁ hη'0 hcη'
    (a := w / 2)
  have hsub : ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩
      {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) T (η' / 2) w}) ⊆
      ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩
      {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) T (η' / 2) (ε + δ + w / 2)}) := by
    rintro ω ⟨hG, hX⟩
    refine ⟨hG, fun h => hX fun s t hs ht hst => (h s t hs ht hst).trans ?_⟩
    linarith
  refine (measure_mono hsub).trans (key.trans ?_)
  rw [mul_comm]
  refine mul_le_mul' ?_ le_rfl
  have e1 : (ε.toNNReal : ℝ≥0∞) = ENNReal.ofReal ε := rfl
  have h1 : (ε.toNNReal : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((ε + δ) ^ 2) ≤ ENNReal.ofReal (ρ / 2) := by
    rw [e1, ← ENNReal.ofReal_inv_of_pos hε, ← ENNReal.ofReal_mul (inv_nonneg.2 hε.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : (ε + δ) ^ 2 ≤ 4 * ε ^ 2 := by nlinarith
    calc ε⁻¹ * (ε + δ) ^ 2 ≤ ε⁻¹ * (4 * ε ^ 2) := by gcongr
      _ = 4 * ε := by field_simp
      _ ≤ ρ / 2 := by linarith
  have h2 : (ENNReal.ofReal f)⁻¹ * (((⌈((T + 1 : ℝ≥0) : ℝ) / η'⌉₊ + 1 : ℕ) : ℝ≥0∞) *
      (4 * ENNReal.ofReal (Real.exp (-(((w / 2 - c * η') / 2) ^ 2 / (32 * (2 * (η' : ℝ)))))))) ≤
      ENNReal.ofReal (ρ / 2) := by
    refine (mul_le_mul' le_rfl hbd).trans ?_
    rw [← ENNReal.ofReal_inv_of_pos hf0, ← ENNReal.ofReal_mul (inv_nonneg.2 hf0.le)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    field_simp
  calc _ ≤ ENNReal.ofReal (ρ / 2) + ENNReal.ofReal (ρ / 2) := add_le_add h1 h2
    _ = ENNReal.ofReal ρ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end Uniform

end LatticeProb
