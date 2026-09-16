/-
The quantitative tail of the supremum of a process over a box, from an
almost-sure modulus of continuity at a fixed scale.

`LatticeProb.KolmogorovSup.integral_sup_sub_rpow_le_of_ae_modulus` bounds the
`p`-th moment of the box supremum of the increments.  The tightness argument of
the parking paper and the growth argument of the sandpile paper consume the
Chebyshev consequence instead: a bound on the probability that the box supremum
exceeds a level `lam`, with the SAME constant for every translate of the box.

The two ingredients are separated.  `ae_sSup_abs_le_of_ae_modulus` turns the
almost-sure modulus at scale `δ` into an almost-sure pointwise bound on the box
supremum of `|X ·|` itself, by the deterministic chaining estimate
`LatticeProb.abs_le_of_modulus_and_bound` and the triangle inequality.
`rpow_le_of_lt_sSup` is the elementary monotonicity of `x ↦ x ^ p` on the
nonnegative reals that identifies the level set of the supremum with the level
set of its `p`-th power.
-/
import Mathlib
import LatticeProb.Prob.SupTail
import LatticeProb.Prob.KolmogorovBound

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Filter

namespace LatticeProb.KolmogorovSup

/-- An almost-sure modulus of continuity at scale `δ` bounds the box supremum of
`|X ·|` by `|X a|` plus the chaining length. -/
theorem ae_sSup_abs_le_of_ae_modulus {k : ℕ} {a b : Fin k → ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {X : (Fin k → ℝ) → Ω → ℝ} {δ : ℝ} (hδ0 : 0 < δ)
    (hae : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b,
      dist s r < δ → |X s ω - X r ω| ≤ 1) :
    ∀ᵐ ω ∂P, sSup ((fun u => |X u ω|) '' Set.Icc a b)
      ≤ |X a ω| + ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) := by
  filter_upwards [hae] with ω hω
  by_cases hab : a ≤ b
  · refine csSup_le ⟨|X a ω|, a, ⟨le_refl a, hab⟩, rfl⟩ ?_
    rintro y ⟨u, hu, rfl⟩
    have hN : 0 < Nat.ceil (dist a b / δ) + 1 := Nat.succ_pos _
    have hstep : dist a b / ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) < δ := by
      rw [div_lt_iff₀ (by positivity)]
      have h1 : dist a b / δ ≤ (Nat.ceil (dist a b / δ) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (dist a b / δ) : ℝ) < ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      calc dist a b = dist a b / δ * δ := (div_mul_cancel₀ _ hδ0.ne').symm
        _ ≤ (Nat.ceil (dist a b / δ) : ℝ) * δ := mul_le_mul_of_nonneg_right h1 hδ0.le
        _ < ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) * δ := mul_lt_mul_of_pos_right h2 hδ0
        _ = δ * ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) := mul_comm _ _
    exact LatticeProb.abs_le_of_modulus_and_bound a b hN hδ0 hstep
      (X := fun u => X u ω) (t := |X a ω|) (fun s hs r hr hsr => hω s hs r hr hsr) (le_refl _) u hu
  · have hI : Set.Icc a b = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨h1, h2⟩
      exact hab (le_trans h1 h2)
    rw [hI, Set.image_empty, Real.sSup_empty]
    positivity

/-- The level set of the box supremum is the level set of its `p`-th power. -/
theorem rpow_le_of_lt_sSup {k : ℕ} {a b : Fin k → ℝ}
    {Ω : Type} [MeasurableSpace Ω] {X : (Fin k → ℝ) → Ω → ℝ}
    {p lam : ℝ} (hp : 0 < p) (hlam : 0 < lam) (ω : Ω)
    (h : lam < sSup ((fun u => |X u ω - X a ω|) '' Set.Icc a b)) :
    lam ^ p ≤ (sSup ((fun u => |X u ω - X a ω|) '' Set.Icc a b)) ^ p :=
  Real.rpow_le_rpow hlam.le h.le hp.le

/-- **The quantitative tail of the box supremum.**  For a process with an
almost-sure modulus of continuity at a fixed scale `δ`, the probability that the
supremum of `|X ·|` over the box exceeds `lam` is at most
`2 ^ p * (∫ |X a| ^ p + (⌈dist a b / δ⌉ + 1) ^ p) / lam ^ p`, with a constant
depending only on the dimension, the exponents, the box and the moment at the
base point. -/
theorem measure_sup_abs_gt_le_of_ae_modulus {k : ℕ} {a b : Fin k → ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : (Fin k → ℝ) → Ω → ℝ} {p δ : ℝ} (hp : 0 < p) (hδ0 : 0 < δ)
    (hint : Integrable (fun ω => |X a ω| ^ p) P) (hmeas : Measurable (X a))
    (hae : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b,
      dist s r < δ → |X s ω - X r ω| ≤ 1) :
    ∀ lam : ℝ, 0 < lam →
      P {ω | lam < sSup ((fun u => |X u ω|) '' Set.Icc a b)}
        ≤ ENNReal.ofReal ((2 : ℝ) ^ p *
            (∫ ω, |X a ω| ^ p ∂P + ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) ^ p) / lam ^ p) := by
  intro lam hlam
  set N : ℝ := ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  have hpt := ae_sSup_abs_le_of_ae_modulus P hδ0 hae
  have hsub : {ω | lam < sSup ((fun u => |X u ω|) '' Set.Icc a b)}
      ≤ᵐ[P] {ω | lam ≤ |X a ω| + N} := by
    filter_upwards [hpt] with ω hω hlt
    change lam ≤ |X a ω| + N
    exact hlt.le.trans (by simpa [hN] using hω)
  have hg : Integrable (fun ω => (2 : ℝ) ^ p * (|X a ω| ^ p + N ^ p)) P :=
    ((hint.add (integrable_const _)).const_mul _)
  have hf' : Integrable (fun ω => (|X a ω| + N) ^ p) P := by
    refine hg.mono' (((hmeas.abs.add_const N).pow_const p).aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (add_nonneg (abs_nonneg _) hN0) p)]
    exact LatticeProb.RpowAdd.add_rpow_le_two_rpow_mul (abs_nonneg _) hN0 hp
  have hbound' : ∫ ω, (|X a ω| + N) ^ p ∂P
      ≤ (2 : ℝ) ^ p * (∫ ω, |X a ω| ^ p ∂P + N ^ p) := by
    have h1 : ∫ ω, (|X a ω| + N) ^ p ∂P
        ≤ ∫ ω, (2 : ℝ) ^ p * (|X a ω| ^ p + N ^ p) ∂P :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
        Real.rpow_nonneg (add_nonneg (abs_nonneg _) hN0) p) hg
        (Filter.Eventually.of_forall fun ω =>
          LatticeProb.RpowAdd.add_rpow_le_two_rpow_mul (abs_nonneg _) hN0 hp)
    rw [integral_const_mul, integral_add hint (integrable_const _), integral_const,
      Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at h1
    exact h1
  have hmain := LatticeProb.measure_abs_ge_le_moment (f := fun ω => |X a ω| + N) P hp hlam
    (by simpa only [abs_of_nonneg (add_nonneg (abs_nonneg _) hN0)] using hf')
    (by simpa only [abs_of_nonneg (add_nonneg (abs_nonneg _) hN0)] using hbound')
  have hset : {ω | lam ≤ |(|X a ω| + N)|} = {ω | lam ≤ |X a ω| + N} := by
    apply Set.ext
    intro ω
    show (lam ≤ |(|X a ω| + N)|) ↔ (lam ≤ |X a ω| + N)
    rw [abs_of_nonneg (add_nonneg (abs_nonneg (X a ω)) hN0)]
  rw [hset] at hmain
  exact (measure_mono_ae hsub).trans (by simpa [hN] using hmain)

/-- The `p`-th moment of the box supremum of `|X ·|` itself, from an almost-sure
modulus of continuity at a fixed scale. -/
theorem integral_sup_abs_rpow_le_of_ae_modulus {k : ℕ} {a b : Fin k → ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : (Fin k → ℝ) → Ω → ℝ} {p δ : ℝ} (hp : 0 < p) (hδ0 : 0 < δ)
    (hint : Integrable (fun ω => |X a ω| ^ p) P) (hmeas : Measurable (X a))
    (hae : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b,
      dist s r < δ → |X s ω - X r ω| ≤ 1) :
    ∫ ω, (sSup ((fun u => |X u ω|) '' Set.Icc a b)) ^ p ∂P
      ≤ (2 : ℝ) ^ p * (∫ ω, |X a ω| ^ p ∂P +
          ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) ^ p) :=
  integral_sup_rpow_le_of_ae_pointwise (X := fun u ω => X u ω) P hp
    (by positivity) hint hmeas (ae_sSup_abs_le_of_ae_modulus P hδ0 hae)

/-- The tail of the box supremum in the form "some point of the box exceeds
`lam`", which is the shape the Borel–Cantelli argument over the unit boxes
consumes. -/
theorem measure_exists_abs_gt_le_of_ae_modulus {k : ℕ} {a b : Fin k → ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : (Fin k → ℝ) → Ω → ℝ} {p δ : ℝ} (hp : 0 < p) (hδ0 : 0 < δ)
    (hint : Integrable (fun ω => |X a ω| ^ p) P) (hmeas : Measurable (X a))
    (hae : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b,
      dist s r < δ → |X s ω - X r ω| ≤ 1) :
    ∀ lam : ℝ, 0 < lam →
      P {ω | ∃ u ∈ Set.Icc a b, lam < |X u ω|}
        ≤ ENNReal.ofReal ((2 : ℝ) ^ p *
            (∫ ω, |X a ω| ^ p ∂P + ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) ^ p) / lam ^ p) := by
  intro lam hlam
  have hsub : {ω | ∃ u ∈ Set.Icc a b, lam < |X u ω|}
      ≤ᵐ[P] {ω | lam < sSup ((fun u => |X u ω|) '' Set.Icc a b)} := by
    filter_upwards [hae] with ω hω
    rintro ⟨u, hu, hlt⟩
    by_cases hab : a ≤ b
    · have hN : 0 < Nat.ceil (dist a b / δ) + 1 := Nat.succ_pos _
      have hstep : dist a b / ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) < δ := by
        rw [div_lt_iff₀ (by positivity)]
        have h1 : dist a b / δ ≤ (Nat.ceil (dist a b / δ) : ℝ) := Nat.le_ceil _
        have h2 : (Nat.ceil (dist a b / δ) : ℝ)
            < ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) := by push_cast; linarith
        calc dist a b = dist a b / δ * δ := (div_mul_cancel₀ _ hδ0.ne').symm
          _ ≤ (Nat.ceil (dist a b / δ) : ℝ) * δ := mul_le_mul_of_nonneg_right h1 hδ0.le
          _ < ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) * δ := mul_lt_mul_of_pos_right h2 hδ0
          _ = δ * ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) := mul_comm _ _
      exact lt_of_lt_of_le hlt (le_csSup ⟨|X a ω| + _, fun y hy => by
        obtain ⟨v, hv, rfl⟩ := hy
        exact LatticeProb.abs_le_of_modulus_and_bound a b hN hδ0 hstep
          (fun s hs r hr hsr => hω s hs r hr hsr) (le_refl _) v hv⟩ ⟨u, hu, rfl⟩)
    · exact absurd (le_trans hu.1 hu.2) hab
  exact (measure_mono_ae hsub).trans
    (measure_sup_abs_gt_le_of_ae_modulus P hp hδ0 hint hmeas hae lam hlam)

/-- The tail of the box supremum with the threshold made EXPLICIT in the accuracy
`ε`: the level `(2 ^ p * (M + (⌈dist a b / δ⌉ + 1) ^ p) / ε) ^ (1 / p) + 1` is
exceeded with probability at most `ε`.  This is the form the Borel–Cantelli
argument over the unit boxes consumes, since the threshold is a polynomial in
`1 / ε`. -/
theorem measure_exists_abs_gt_le_of_kolmogorov_explicit {k : ℕ} {a b : Fin k → ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : (Fin k → ℝ) → Ω → ℝ} {p M δ : ℝ} (hp : 0 < p) (hδ0 : 0 < δ)
    (hint : Integrable (fun ω => |X a ω| ^ p) P) (hmeas : Measurable (X a))
    (hae : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b,
      dist s r < δ → |X s ω - X r ω| ≤ 1)
    (hintM : ∫ ω, |X a ω| ^ p ∂P ≤ M) (hM0 : 0 ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    P {ω | ∃ u ∈ Set.Icc a b,
        (2 ^ p * (M + ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) ^ p) / ε) ^ (1 / p) + 1
          < |X u ω|} ≤ ENNReal.ofReal ε := by
  set N : ℝ := ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  set A : ℝ := 2 ^ p * (M + N ^ p) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  set c : ℝ := (A / ε) ^ (1 / p) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by positivity) _
  have hcp : c ^ p = A / ε := by
    rw [hc, ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]
  have hlam : 0 < c + 1 := by linarith
  have hkey : A / (c + 1) ^ p ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    calc A = A / ε * ε := (div_mul_cancel₀ _ hε.ne').symm
      _ = c ^ p * ε := by rw [hcp]
      _ ≤ (c + 1) ^ p * ε :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hc0 (by linarith) hp.le) hε.le
      _ = ε * (c + 1) ^ p := mul_comm _ _
  refine (measure_exists_abs_gt_le_of_ae_modulus P hp hδ0 hint hmeas hae (c + 1) hlam).trans ?_
  rw [ENNReal.ofReal_le_ofReal_iff hε.le]
  calc 2 ^ p * (∫ ω, |X a ω| ^ p ∂P + N ^ p) / (c + 1) ^ p
      ≤ 2 ^ p * (M + N ^ p) / (c + 1) ^ p := by
        gcongr
    _ = A / (c + 1) ^ p := by rw [hA]
    _ ≤ ε := hkey

end LatticeProb.KolmogorovSup
