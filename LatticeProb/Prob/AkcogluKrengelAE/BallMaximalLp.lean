/-
# The multiparameter pointwise ergodic maximal inequality (Krengel's `Lᵖ` bound)

This file is the library-side home of the statement VRW's worker isolated as
`VRW.KrengelLpBall` (`_wip/MaximalErgodicReduction.lean`): for a measure-preserving action
`T : ℤ^d → Ω → Ω` of the lattice on a probability space, `p > 1` and a measurable
`f : Ω → ℝ≥0∞`, the `ℓ¹`-ball averaging maximal is `Lᵖ`-bounded,

`∫⁻ (⨆_{1 ≤ R} avg (l1Ball 0 R) (fun y => f (T y ω)))ᵖ ∂μ ≤ C ∫⁻ fᵖ ∂μ`.

The definitions `l1Ball` and `avg` reproduce VRW's (`VRW/Model/Lattice.lean:72`,
`VRW/Model/Conductance.lean:76`), so the statement transfers verbatim.

## Status

The one-parameter weak-type `(1,1)` bound is already in the library in normalised form
(`maximal_inequality` read through `bAvg`; see `measureReal_normalizedMaximalSet_le` below).
The two genuinely missing inputs are isolated as named `Prop`s and are **not** proved here:

* `BirkhoffLpMaximal` — the one-parameter strong `Lᵖ` maximal (Wiener's maximal theorem for a
  single measure-preserving transformation). Mathlib has only Doob's *weak*-type maximal
  inequality (`MeasureTheory.maximal_ineq`) and no Marcinkiewicz interpolation
  (`grep -rn "Marcinkiewicz" .lake/packages/mathlib` is empty), so this must be built from the
  layer-cake identity `MeasureTheory.lintegral_eq_lintegral_meas_lt` plus
  `maximal_inequality`.
* `KrengelLpBall` — the multiparameter bound. The precise route: since
  `l1Ball 0 R ⊆ [-R,R]^d`, the `ℓ¹`-ball maximal is dominated by the cube maximal
  `sup_s avg (box s) (f ∘ T_·)`, and the cube average factors by Fubini as the `d`-fold
  iterate `M_1 M_2 ⋯ M_d` of the one-parameter maximals `M_i f(x) =
  sup_{N} (1/N) ∑_{k<N} f(T_{k e_i} x)`. Applying `BirkhoffLpMaximal` once per coordinate
  (and `MeasurePreserving.lintegral_comp` / Fubini for the measure-preserving factors) gives
  the bound. Nothing in this library assembles the iteration.

Everything below is `sorry`-free; the two `Prop`s mark the exact remaining gap rather than
assume it.
-/
import LatticeProb.Prob.Birkhoff
import LatticeProb.Walk.Ball

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb

/-! ### The `ℓ¹`-ball vocabulary, matching VRW -/

/-- The `ℓ¹` ball `B¹_R(x) = {y : ‖y - x‖₁ ≤ R}` for a real radius `R`. -/
noncomputable def l1Ball {d : ℕ} (x : Site d) (R : ℝ) : Finset (Site d) :=
  (Fintype.piFinset fun i : Fin d => Finset.Icc (x i - ⌈R⌉₊) (x i + ⌈R⌉₊)).filter
    fun y => ((graphNorm (y - x) : ℕ) : ℝ) ≤ R

/-- The uniform average of an `ℝ≥0∞`-valued field over a finite set. -/
noncomputable def avg {d : ℕ} (B : Finset (Site d)) (f : Site d → ℝ≥0∞) : ℝ≥0∞ :=
  (B.card : ℝ≥0∞)⁻¹ * ∑ y ∈ B, f y

/-- The one-parameter strong `Lᵖ` maximal for a measure-preserving transformation.  This is
Wiener's maximal theorem in the form the `d = 1` case of `KrengelLpBall` consumes; it is the
first missing input (see the file header). -/
def BirkhoffLpMaximal : Prop :=
  ∀ p : ℝ, 1 < p → ∃ C : ℝ, 0 ≤ C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
      ∀ (T : Ω → Ω), MeasurePreserving T μ μ →
        ∀ f : Ω → ℝ≥0∞, Measurable f →
          ∫⁻ x, (⨆ (N : ℕ), (N : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range N, f (T^[k] x)) ^ p ∂μ ≤
            ENNReal.ofReal C * ∫⁻ x, f x ^ p ∂μ

/-- **Krengel's multiparameter `Lᵖ` maximal bound for `ℓ¹`-ball averages.**  For every `p > 1`
there is `C` with, for every probability space, every action `T : ℤ^d → Ω → Ω` by
measure-preserving maps that is additive, and every measurable `f : Ω → ℝ≥0∞`,
`∫⁻ (⨆_{1 ≤ R} avg (B¹_R(0)) (f ∘ T_·))ᵖ ≤ C ∫⁻ fᵖ`. -/
def KrengelLpBall (d : ℕ) : Prop :=
  ∀ p : ℝ, 1 < p → ∃ C : ℝ, 0 ≤ C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
      ∀ (T : Site d → Ω → Ω),
        (∀ x, MeasurePreserving (T x) μ μ) →
        (∀ x y, T (x + y) = T x ∘ T y) →
        ∀ f : Ω → ℝ≥0∞, Measurable f →
          ∫⁻ ω, (⨆ (R : ℕ) (_ : 1 ≤ R),
              avg (l1Ball (0 : Site d) R) (fun y => f (T y ω))) ^ p ∂μ ≤
            ENNReal.ofReal C * ∫⁻ ω, f ω ^ p ∂μ

/-! ### The normalised one-parameter weak-type bound

`maximal_inequality` already controls the set where some *Birkhoff sum* of `f - c` is
positive.  Rewriting that set through `bAvg` gives the weak-type `(1,1)` bound for the
normalised one-parameter maximal, the hypothesis half of the missing Marcinkiewicz step. -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω} {f : Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- The set where some normalised Birkhoff average of `f` exceeds `c` in absolute value is
contained in `maximalSet` of `|f|` at level `c`. -/
theorem normalizedMaximalSet_subset_maximalSet {c : ℝ} (hc : 0 < c) :
    {x | ∃ n : ℕ, c < |bAvg T f n x|} ⊆ maximalSet T (fun y => |f y|) c := by
  rintro x ⟨n, hn⟩
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hpos
    · rw [hn0] at hn
      simp [bAvg] at hn
      linarith
    · omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hle : |bAvg T f n x| ≤ bAvg T (fun y => |f y|) n x := by
    rw [bAvg, bAvg, abs_div, abs_of_pos hnpos]
    gcongr
    exact Finset.abs_sum_le_sum_abs _ _
  have hgt : c < bAvg T (fun y => |f y|) n x := lt_of_lt_of_le hn hle
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  have hbs : birkhoffSum T (fun y => |f y| - c) n x
      = (n : ℝ) * (bAvg T (fun y => |f y|) n x - c) := by
    rw [birkhoffSum_sub_const, bAvg]
    field_simp
  have hpos : 0 < birkhoffSum T (fun y => |f y| - c) n x := by
    rw [hbs]
    nlinarith
  exact lt_of_lt_of_le hpos (birkhoffSum_le_maxBirkhoff T (fun y => |f y| - c) le_rfl x)

/-- **The normalised one-parameter weak-type `(1,1)` bound.**  For a measure-preserving `T`, an
integrable `f` and `c > 0`, the measure of the set where some normalised Birkhoff average
exceeds `c` in absolute value is at most `‖f‖₁ / c`. -/
theorem measureReal_normalizedMaximalSet_le [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) {c : ℝ} (hc : 0 < c) :
    (μ {x | ∃ n : ℕ, c < |bAvg T f n x|}).toReal ≤ (∫ x, |f x| ∂μ) / c := by
  have hsub := normalizedMaximalSet_subset_maximalSet (T := T) (f := f) hc
  have hmax := maximal_inequality hT hfm.abs hf.abs (c := c) hc
  have h1 : (μ {x | ∃ n : ℕ, c < |bAvg T f n x|}).toReal
      ≤ (μ (maximalSet T (fun y => |f y|) c)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have h2 : ∫ x, |(|f x|)| ∂μ = ∫ x, |f x| ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => abs_abs _)
  rw [h2] at hmax
  rw [le_div_iff₀ hc]
  calc (μ {x | ∃ n : ℕ, c < |bAvg T f n x|}).toReal * c
      ≤ (μ (maximalSet T (fun y => |f y|) c)).toReal * c :=
        mul_le_mul_of_nonneg_right h1 hc.le
    _ = c * (μ (maximalSet T (fun y => |f y|) c)).toReal := by ring
    _ ≤ ∫ x, |f x| ∂μ := hmax

end LatticeProb
