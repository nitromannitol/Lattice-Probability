import LatticeProb.Prob.CorrelatedBMRegularPaths

/-!
# A common weak contour pair of a correlated Brownian pair straddles a rational time

Let `μ` be the law of the two-sided correlated Brownian pair `(L, R)` (`IsCorrelatedBM2 γ μ`), and write
`U = L + R` and `V = L - R`.

* **No flat rational increments.** The increment `L_p - L_q` (and likewise `R_p - R_q`) is a centred Gaussian
  variable of variance `|p - q|` (`hasLaw_lrCoord_sub`), which has no atom when `p ≠ q`. Hence almost surely
  `L_p ≠ L_q` and `R_p ≠ R_q` for all rationals `p < q`: no coordinate is constant on a nondegenerate interval.
* **Rational straddle of a common weak contour pair** (deterministic). Let `(s, t)` be a weak contour pair of both
  `L` and `R`. On `[s, t]` both increments `L u - L s` and `R u - R s` are nonnegative, so
  `U u - U s ≥ |V u - V s|`, and `V u = V s` wherever `U u = U s`. Since `L` has no flat rational increment, `U`
  exceeds `U s` at a rational time `q ∈ (s, t)`; the straddling pair `(lastBelow U q l, firstBelow U q l)` of `U`
  at `q` at the level `l = U s` lies in `[s, t]`, and `U = l` at both of its ends. So `V` takes the value `V s` at
  both ends of this straddling pair.

## Main results
* `ae_lrCoord_ne`: for `s ≠ t`, almost surely `lrCoord i s ω ≠ lrCoord i t ω`.
* `ae_lrCoord_ne_of_rat_lt`: almost surely, `L_p ≠ L_q` and `R_p ≠ R_q` for all rationals `p < q`.
* `sub_eq_sub_of_add_eq_add`: on a common weak contour pair `(s, t)` of `X` and `Y`, a return of `X + Y` to its
  value at `s` is a return of `X - Y` to its value at `s`.
* `exists_rat_straddle_of_isWeakContourPair`: the rational straddle for continuous `X`, `Y`.
* `exists_rat_straddle_of_not_noCommonWeakContourPair`: if the coordinates of `ω` have no flat rational increment
  and a common weak contour pair, then there are a rational `q` and a level `l < U q` such that `V` takes the same
  value at both ends of the straddling pair of `U` at `q` at the level `l`.
-/

set_option autoImplicit false

open Set MeasureTheory ProbabilityTheory

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {μ : Measure Path2}

/-- **A Brownian increment has no atom at `0`.** For `s ≠ t` the increment `lrCoord i s - lrCoord i t` of the
correlated Brownian pair has law `N(0, |s - t|)` of positive variance, so almost surely
`lrCoord i s ω ≠ lrCoord i t ω`. -/
theorem ae_lrCoord_ne (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) {s t : ℝ} (hst : s ≠ t) :
    ∀ᵐ ω ∂μ, lrCoord i s ω ≠ lrCoord i t ω := by
  have hX := hasLaw_lrCoord_sub hμ i s t
  have hv : nndist s t ≠ 0 := fun h =>
    hst (dist_eq_zero.1 (by rw [← coe_nndist, h, NNReal.coe_zero]))
  have := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) hv
  have hnull : μ ((fun ω => lrCoord i s ω - lrCoord i t ω) ⁻¹' {0}) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable hX.aemeasurable (measurableSet_singleton 0), hX.map_eq]
    exact measure_singleton 0
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hnull
  exact sub_eq_zero.2 (not_not.1 hω)

/-- **No flat rational increments.** Almost surely, for all rationals `p < q`, `L_p ≠ L_q` and `R_p ≠ R_q`; in
particular no coordinate of the correlated Brownian pair is constant on a nondegenerate interval. -/
theorem ae_lrCoord_ne_of_rat_lt (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ p q : ℚ, p < q →
      lrCoord 0 (p : ℝ) ω ≠ lrCoord 0 (q : ℝ) ω ∧ lrCoord 1 (p : ℝ) ω ≠ lrCoord 1 (q : ℝ) ω := by
  refine ae_all_iff.2 fun p => ae_all_iff.2 fun q => ?_
  by_cases hpq : p < q
  · have hne : (p : ℝ) ≠ q := by exact_mod_cast hpq.ne
    filter_upwards [ae_lrCoord_ne hμ 0 hne, ae_lrCoord_ne hμ 1 hne] with ω h0 h1
    exact fun _ => ⟨h0, h1⟩
  · exact Filter.Eventually.of_forall fun _ h => absurd h hpq

/-- **Returns of `X + Y` on a common weak contour pair.** If `(s, t)` is a weak contour pair of both `X` and `Y`,
then at a time `u ∈ [s, t]` where `X + Y` returns to its value at `s`, the two nonnegative increments `X u - X s`
and `Y u - Y s` vanish, so `X - Y` also takes its value at `s`. -/
theorem sub_eq_sub_of_add_eq_add {X Y : ℝ → ℝ} {s t u : ℝ} (hX : IsWeakContourPair X s t)
    (hY : IsWeakContourPair Y s t) (hu : u ∈ Icc s t) (h : X u + Y u = X s + Y s) :
    X u - Y u = X s - Y s := by
  have hXu := hX.2.2 u hu
  have hYu := hY.2.2 u hu
  have hXs : X u = X s := by linarith
  have hYs : Y u = Y s := by linarith
  rw [hXs, hYs]

/-- **Rational straddle of a common weak contour pair.** Let `X`, `Y` be continuous with `X p ≠ X q` for all
rationals `p < q`, and let `(s, t)` be a weak contour pair of both `X` and `Y`. Then `U = X + Y` exceeds `U s` at a
rational time `q ∈ (s, t)`; at the level `l = U s < U q` the straddling pair of `U` at `q` lies in `[s, t]`, and `U`
returns to `l` at both of its ends, so `V = X - Y` takes the value `V s` at both ends. -/
theorem exists_rat_straddle_of_isWeakContourPair {X Y : ℝ → ℝ} (hXc : Continuous X) (hYc : Continuous Y)
    (h0 : ∀ p q : ℚ, p < q → X p ≠ X q) {s t : ℝ} (hX : IsWeakContourPair X s t)
    (hY : IsWeakContourPair Y s t) :
    ∃ q : ℚ, ∃ l : ℝ, l < X q + Y q ∧
      X (lastBelow (fun u => X u + Y u) q l) - Y (lastBelow (fun u => X u + Y u) q l) =
        X (firstBelow (fun u => X u + Y u) q l) - Y (firstBelow (fun u => X u + Y u) q l) := by
  -- `X` exceeds `X s` at a rational time of `(s, t)`, since it is not constant between two rationals there
  obtain ⟨p, hsp, hpt⟩ := exists_rat_btwn hX.1
  obtain ⟨r, hpr, hrt⟩ := exists_rat_btwn hpt
  have hq : ∃ q : ℚ, s < q ∧ (q : ℝ) < t ∧ X s < X q := by
    rcases (hX.2.2 p ⟨hsp.le, hpt.le⟩).lt_or_eq with h | h
    · exact ⟨p, hsp, hpt, h⟩
    rcases (hX.2.2 r ⟨(hsp.trans hpr).le, hrt.le⟩).lt_or_eq with h' | h'
    · exact ⟨r, hsp.trans hpr, hrt, h'⟩
    exact absurd (h.symm.trans h') (h0 p r (by exact_mod_cast hpr))
  obtain ⟨q, hsq, hqt, hXq⟩ := hq
  have hYq := hY.2.2 q ⟨hsq.le, hqt.le⟩
  -- the straddling pair of `U = X + Y` at `q` at the level `U s` lies in `[s, t]`
  have hU : Continuous fun u => X u + Y u := hXc.add hYc
  have hl : X s + Y s < X q + Y q := by linarith
  have hbt : X t + Y t ≤ X s + Y s := le_of_eq (by rw [hX.2.1, hY.2.1])
  have ha : ∃ a ≤ (q : ℝ), X a + Y a ≤ X s + Y s := ⟨s, hsq.le, le_rfl⟩
  have hb : ∃ b, (q : ℝ) ≤ b ∧ X b + Y b ≤ X s + Y s := ⟨t, hqt.le, hbt⟩
  refine ⟨q, X s + Y s, hl, ?_⟩
  have hs' : lastBelow (fun u => X u + Y u) q (X s + Y s) ∈ Icc s t :=
    ⟨le_lastBelow hsq.le le_rfl, (lastBelow_mem hU ha).1.trans hqt.le⟩
  have ht' : firstBelow (fun u => X u + Y u) q (X s + Y s) ∈ Icc s t :=
    ⟨hsq.le.trans (firstBelow_mem hU hb).1, firstBelow_le hqt.le hbt⟩
  -- `U` returns to `U s` at both ends, so `V = X - Y` takes the value `V s` at both ends
  exact (sub_eq_sub_of_add_eq_add hX hY hs' (apply_lastBelow hU hl ha)).trans
    (sub_eq_sub_of_add_eq_add hX hY ht' (apply_firstBelow hU hl hb)).symm

/-- **Rational straddle of a common weak contour pair of the coordinates** (deterministic). Write `U = L + R` and
`V = L - R` for the coordinates `L`, `R` of `ω`. If no coordinate of `ω` has a flat rational increment and some pair
of times is a weak contour pair of both `L` and `R`, then there are a rational `q` and a level `l < U q` such that
`V` takes the same value at both ends of the straddling pair `(lastBelow U q l, firstBelow U q l)` of `U` at `q`. -/
theorem exists_rat_straddle_of_not_noCommonWeakContourPair (ω : Path2)
    (h0 : ∀ p q : ℚ, p < q →
      lrCoord 0 (p : ℝ) ω ≠ lrCoord 0 (q : ℝ) ω ∧ lrCoord 1 (p : ℝ) ω ≠ lrCoord 1 (q : ℝ) ω)
    (h : ¬ NoCommonWeakContourPair ω) :
    ∃ q : ℚ, ∃ l : ℝ, l < lrCoord 0 (q : ℝ) ω + lrCoord 1 (q : ℝ) ω ∧
      (let U : ℝ → ℝ := fun u => lrCoord 0 u ω + lrCoord 1 u ω
       let V : ℝ → ℝ := fun u => lrCoord 0 u ω - lrCoord 1 u ω
       V (lastBelow U q l) = V (firstBelow U q l)) := by
  obtain ⟨s, t, hL, hR⟩ : ∃ s t, IsWeakContourPair (fun u => lrCoord 0 u ω) s t ∧
      IsWeakContourPair (fun u => lrCoord 1 u ω) s t := by
    by_contra hne
    exact h fun s t hL hR => hne ⟨s, t, hL, hR⟩
  exact exists_rat_straddle_of_isWeakContourPair (continuous_lrCoord_time 0 ω)
    (continuous_lrCoord_time 1 ω) (fun p q hpq => (h0 p q hpq).1) hL hR

end LatticeProb.CorrelatedBM
