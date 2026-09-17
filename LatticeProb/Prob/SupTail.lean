/-
A quantitative moment bound for the supremum of a process over a box.

`LatticeProb.kolmogorovModulusPi` gives a modulus of continuity for a process
whose increments satisfy a Kolmogorov condition, but only through an existential
threshold for a prescribed accuracy.  The tightness argument of the parking paper
needs the quantitative companion: the `p`-th moment of the supremum of the
increments over a box is bounded by a constant depending only on the dimension,
the exponents, the moment constant and the box.

The two ingredients are separated.  `integral_sup_rpow_le_of_ae_pointwise` turns
an almost-sure pointwise bound on the box supremum into a moment bound, using
`LatticeProb.RpowAdd.add_rpow_le_two_rpow_mul` for the `p`-th power of a sum.
`ae_sSup_sub_le_of_ae_modulus` turns an almost-sure modulus of continuity at a
scale `δ` into the pointwise bound, by the deterministic chaining estimate
`LatticeProb.abs_le_of_modulus_and_bound` with `ceil (dist a b / δ) + 1` steps.
-/
import Mathlib
import LatticeProb.Prob.KolmogorovBound
import LatticeProb.Prob.RpowAdd

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Filter

namespace LatticeProb.KolmogorovSup

/-- The `p`-th moment of the box supremum, from an almost-sure pointwise bound. -/
theorem integral_sup_rpow_le_of_ae_pointwise {k : ℕ} {a b : Fin k → ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : (Fin k → ℝ) → Ω → ℝ} {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hint : Integrable (fun ω => |X a ω| ^ p) P)
    (hmeas : Measurable (X a))
    (hpt : ∀ᵐ ω ∂P, sSup ((fun u => |X u ω|) '' Set.Icc a b) ≤ |X a ω| + C) :
    ∫ ω, (sSup ((fun u => |X u ω|) '' Set.Icc a b)) ^ p ∂P
      ≤ (2 : ℝ) ^ p * (∫ ω, |X a ω| ^ p ∂P + C ^ p) := by
  have hg : Integrable (fun ω => (2 : ℝ) ^ p * (|X a ω| ^ p + C ^ p)) P :=
    ((hint.add (integrable_const _)).const_mul _)
  have hf : Integrable (fun ω => (|X a ω| + C) ^ p) P :=
    hg.mono' (((hmeas.abs.add_const _).pow_const p).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) p)]
        exact LatticeProb.RpowAdd.add_rpow_le_two_rpow_mul (abs_nonneg _) hC hp)
  calc ∫ ω, (sSup ((fun u => |X u ω|) '' Set.Icc a b)) ^ p ∂P
      ≤ ∫ ω, (|X a ω| + C) ^ p ∂P :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
          Real.rpow_nonneg (Real.sSup_nonneg fun y hy => by
            obtain ⟨u, _, rfl⟩ := hy
            exact abs_nonneg _) p) hf
          (Filter.Eventually.mono hpt fun ω hω =>
            Real.rpow_le_rpow (Real.sSup_nonneg fun y hy => by
              obtain ⟨u, _, rfl⟩ := hy
              exact abs_nonneg _) hω hp.le)
    _ ≤ ∫ ω, (2 : ℝ) ^ p * (|X a ω| ^ p + C ^ p) ∂P :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
          Real.rpow_nonneg (by positivity) p) hg
          (Filter.Eventually.of_forall fun ω =>
            LatticeProb.RpowAdd.add_rpow_le_two_rpow_mul (abs_nonneg _) hC hp)
    _ = (2 : ℝ) ^ p * ∫ ω, (|X a ω| ^ p + C ^ p) ∂P :=
        integral_const_mul _ _
    _ = (2 : ℝ) ^ p * (∫ ω, |X a ω| ^ p ∂P + C ^ p) := by
        rw [integral_add hint (integrable_const _), integral_const, Measure.real,
          measure_univ, ENNReal.toReal_one, one_smul]

/-- An almost-sure modulus of continuity at scale `δ` bounds the box supremum of
the increments from the base point. -/
theorem ae_sSup_sub_le_of_ae_modulus {k : ℕ} {a b : Fin k → ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {X : (Fin k → ℝ) → Ω → ℝ} {δ : ℝ} (hδ0 : 0 < δ)
    (hae : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b,
      dist s r < δ → |X s ω - X r ω| ≤ 1) :
    ∀ᵐ ω ∂P, sSup ((fun u => |X u ω - X a ω|) '' Set.Icc a b)
      ≤ |X a ω - X a ω| + ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) := by
  filter_upwards [hae] with ω hω
  by_cases hab : a ≤ b
  · refine csSup_le ⟨|X a ω - X a ω|, a, ⟨le_refl a, hab⟩, rfl⟩ ?_
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
    have := LatticeProb.abs_le_of_modulus_and_bound a b hN hδ0 hstep
      (X := fun u => X u ω - X a ω) (t := 0) (fun s hs r hr hsr => by
        simpa using hω s hs r hr hsr) (by simp) u hu
    simpa using this
  · have hI : Set.Icc a b = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨h1, h2⟩
      exact hab (le_trans h1 h2)
    rw [hI, Set.image_empty, Real.sSup_empty]
    positivity

/-- The quantitative moment bound for a process with an almost-sure modulus of
continuity at a fixed scale `δ`: the `p`-th moment of the supremum of
`|X · - X a|` over the box is bounded by `2 ^ p` times the sum of the `p`-th
moment at the base point and the `p`-th power of the chaining length
`ceil (dist a b / δ) + 1`. -/
theorem integral_sup_sub_rpow_le_of_ae_modulus {k : ℕ} {a b : Fin k → ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : (Fin k → ℝ) → Ω → ℝ} {p δ : ℝ} (hp : 0 < p) (hδ0 : 0 < δ)
    (hint : Integrable (fun ω => |X a ω - X a ω| ^ p) P)
    (hmeas : Measurable (X a))
    (hae : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b,
      dist s r < δ → |X s ω - X r ω| ≤ 1) :
    ∫ ω, (sSup ((fun u => |X u ω - X a ω|) '' Set.Icc a b)) ^ p ∂P
      ≤ (2 : ℝ) ^ p * (∫ ω, |X a ω - X a ω| ^ p ∂P +
          ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) ^ p) :=
  integral_sup_rpow_le_of_ae_pointwise (X := fun u ω => X u ω - X a ω) P hp
    (by positivity) hint ((hmeas.sub hmeas))
    (ae_sSup_sub_le_of_ae_modulus P hδ0 hae)

/-- The Kolmogorov condition gives an almost-sure modulus of continuity: for
almost every `ω` there is a scale `δ (ω) > 0` at which the increments over the box
are at most `1`.  The scale depends on `ω`; a uniform scale is false in general,
since a process with a jump at a random location has a positive-probability bad
set at every fixed scale. -/
theorem ae_modulus_of_kolmogorov {k : ℕ} {a b : Fin k → ℝ}
    {p q M : ℝ} (hp : 0 < p) (hq : (k : ℝ) < q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : (Fin k → ℝ) → Ω → ℝ} (hmeas : ∀ u, Measurable (X u))
    (hint : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      Integrable (fun ω => |X u ω - X v ω| ^ p) P)
    (hbound : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      ∫ ω, |X u ω - X v ω| ^ p ∂P ≤ M * dist u v ^ q)
    (hcont : ∀ ω, ContinuousOn (fun u => X u ω) (Set.Icc a b)) :
    ∀ᵐ ω ∂P, ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b,
      dist s r < δ → |X s ω - X r ω| ≤ 1 := by
  have hmod : ∀ n : ℕ, ∃ δ : ℝ, 0 < δ ∧
      P {ω | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b, dist u v < δ ∧ 1 < |X u ω - X v ω|}
        ≤ ENNReal.ofReal ((1/2 : ℝ) ^ n) := fun n => by
    obtain ⟨δ, hδ0, hδ⟩ := LatticeProb.kolmogorovModulusPi k a b p q M hp hq
      ((1/2 : ℝ) ^ n) 1 (by positivity) one_pos
    exact ⟨δ, hδ0, hδ P (inferInstance : IsProbabilityMeasure P) X hmeas hint hbound hcont⟩
  choose δ hδ using hmod
  have hsum : ∑' n : ℕ, P {ω | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b,
      dist u v < δ n ∧ 1 < |X u ω - X v ω|} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => (hδ n).2)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  have hBC : P (limsup (fun n => {ω | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b,
      dist u v < δ n ∧ 1 < |X u ω - X v ω|}) atTop) = 0 :=
    measure_limsup_atTop_eq_zero hsum
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hBC
  simp only [Set.mem_setOf_eq, not_exists] at hω
  rw [mem_limsup_iff_frequently_mem, Filter.frequently_atTop]
  intro n₀
  have h1 : ¬ (∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b,
      dist s r < δ n₀ → |X s ω - X r ω| ≤ 1) :=
    fun h => hω (δ n₀) ⟨(hδ n₀).1, h⟩
  push Not at h1
  obtain ⟨s, hs, r, hr, hsr, hgt⟩ := h1
  exact ⟨n₀, le_rfl, s, hs, r, hr, hsr, hgt⟩

/-- The quantitative moment bound for a process with an almost-sure modulus of
continuity at a FIXED scale `δ`, in the form the tightness argument consumes: the
`p`-th moment of the supremum of `|X · - X a|` over the box is bounded by `2 ^ p`
times the sum of the `p`-th moment at the base point and the `p`-th power of the
chaining length `ceil (dist a b / δ) + 1`.

The fixed scale is what the consumer supplies; the Kolmogorov condition alone
gives only a scale depending on `ω` (`ae_modulus_of_kolmogorov`), and the passage
from that to a fixed scale is the dyadic chaining argument, which is not needed
here. -/
theorem integral_sup_sub_rpow_le_of_kolmogorov {k : ℕ} {a b : Fin k → ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : (Fin k → ℝ) → Ω → ℝ} {p δ : ℝ} (hp : 0 < p) (hδ0 : 0 < δ)
    (hint : Integrable (fun ω => |X a ω - X a ω| ^ p) P)
    (hmeas : Measurable (X a))
    (hae : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b,
      dist s r < δ → |X s ω - X r ω| ≤ 1) :
    ∫ ω, (sSup ((fun u => |X u ω - X a ω|) '' Set.Icc a b)) ^ p ∂P
      ≤ (2 : ℝ) ^ p * (∫ ω, |X a ω - X a ω| ^ p ∂P +
          ((Nat.ceil (dist a b / δ) + 1 : ℕ) : ℝ) ^ p) :=
  integral_sup_rpow_le_of_ae_pointwise (X := fun u ω => X u ω - X a ω) P hp
    (by positivity) hint (hmeas.sub hmeas)
    (ae_sSup_sub_le_of_ae_modulus P hδ0 hae)

end LatticeProb.KolmogorovSup
