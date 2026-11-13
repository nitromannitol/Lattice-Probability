/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.RS.TraceGrid at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.TailBounds
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.TraceShift
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# EXT-RS node TR1: the grid bound on the imaginary axis at dyadic times

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §3, node TR1.
Sources: A. Kemppainen, *Schramm–Loewner Evolution*, SpringerBriefs Math. Phys. 24 (2017),
Prop. 5.10 and Remark 5.13 (p. 99); S. Rohde, O. Schramm, *Basic properties of SLE*,
Ann. Math. 161 (2005), Thm. 3.6 and (3.19) (pp. 16–18); G. Lawler, *Conformally Invariant
Processes in the Plane*, AMS 2005, proof of Thm. 7.4 (p. 157).

For `κ ∈ (0, 8]`, `θ ∈ (0, θ₀(κ))` with `θ₀ = (κ/16 + 4/κ − 1)/(κ/16 + 4/κ + 1)`, and
`N ∈ ℕ`, almost surely there is `C < ∞` with
`‖(f̂_t)'(i 2^{−n})‖ ≤ C 2^{n(1−θ)}` for every `n ∈ ℕ` and every dyadic time `t = k/4ⁿ ≤ N`.

Proof (Kemppainen, p. 99, first half; RS (3.19), pp. 16–18). For a grid point `t = k/4ⁿ`:
P3(e) (`fwdMapInv_drive_eq_revMap_revBM`) identifies the derivative of `f̂_t` with that of the
reverse map driven by the time-reversed Brownian path `revBM B' t`, which is again a Brownian
motion (`isBrownianReal_revBM`); E2 (`rs_tail_bound_axis`) with `r = rsR1 κ` and `β = θ` gives

  `P{‖(u_t)'(i2^{−n})‖ > 2^{n(1−θ)}} ≤ qⁿ`, `q = 2^{−(1−θ)(8+κ)²/(16κ)}`,

there are at most `N 4ⁿ + 1` such grid points, and `4 q < 1` exactly when
`θ < θ₀ = 1 − 32κ/(8+κ)² = (κ/16 + 4/κ − 1)/(κ/16 + 4/κ + 1)` (Remark 5.13), so
`∑ₙ (N 4ⁿ + 1) qⁿ < ∞`; the first Borel–Cantelli lemma (`MeasureTheory.ae_eventually_notMem`)
gives that a.s. all but finitely many levels `n` are good, and the finitely many exceptional
levels have finite (hence bounded) normalized derivatives, absorbed by `C`.

Deviation (for `DEVIATIONS.md`): the hypothesis `κ ≤ 8` is needed. E2 requires
`0 ≤ rsZeta κ r`, i.e. `r ≤ 4/κ`, which at `r = rsR1 κ = (8+κ)/(4κ)` holds iff `κ ≤ 8`. For
`κ > 8` one may still apply E2 with any `r ∈ [0, 4/κ]`, but there `λ + ζ = rsLam κ r + rsZeta κ r
= r(4 + κ/2) − κr²` has maximum `2` (attained only at `r = 4/κ`), so the Borel–Cantelli
exponent `(1−θ)(λ+ζ)` of this route can never exceed `2`, and the level sum `∑ₙ (N4ⁿ+1) qⁿ` with
`q = 2^{−(1−θ)(λ+ζ)}` diverges for every `θ > 0`. So no choice of `r` makes the E2-based argument
reach any positive `θ` when `κ > 8`; Kemppainen's Prop. 5.10 for `κ > 8` (itself, or at least with
his Remark 5.13 value of `θ₀`, whose display on p. 99 drops the loss `y₀^{rsZeta}` that (5.39)
carries) is not obtained here. The `κ ≤ 8` case is what the consumers TR2/TR3/TR4 (`κ < 8`) use.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace RS

open UnzipInvariance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ## Rewriting the dyadic grid point `i 2^{−n}` -/

theorem rpow_two_neg_natCast_sub_one (n : ℕ) (θ : ℝ) :
    ((2 : ℝ) ^ (-(n : ℝ))) ^ (θ - 1) = (2 : ℝ) ^ ((n : ℝ) * (1 - θ)) := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem ofReal_two_neg_rpow_mul_I (n : ℕ) :
    (((2 : ℝ) ^ (-(n : ℝ)) : ℝ) : ℂ) * Complex.I = Complex.I / 2 ^ n := by
  have h1 : (2 : ℝ) ^ (-(n : ℝ)) = ((2 : ℝ) ^ n)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have h2 : (((2 : ℝ) ^ n : ℝ) : ℂ) = (2 : ℂ) ^ n := by
    rw [Complex.ofReal_pow]
    norm_num
  rw [h1, Complex.ofReal_inv, h2, div_eq_mul_inv]
  ring

theorem rpow_two_neg_natCast_mul (n : ℕ) (c : ℝ) :
    ((2 : ℝ) ^ (-(n : ℝ))) ^ c = ((2 : ℝ) ^ (-c)) ^ n := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast ((2 : ℝ) ^ (-c)) n,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-! ## The grid events -/

/-- The per-level decay factor `q = 2^{−(1−θ)(λ+ζ)}` of the TR1 grid bound, evaluated at
`r = rsR1 κ` (where `λ + ζ = (8+κ)²/(16κ)`). -/
def rsGridQ (κ θ : ℝ) : ℝ :=
  (2 : ℝ) ^ (-((1 - θ) * (rsLam κ (rsR1 κ) + rsZeta κ (rsR1 κ))))

/-- Normalized derivative at the grid point `(n,k)`:
`‖(f̂_{k/4ⁿ})'(i2^{−n})‖ / 2^{n(1−θ)}`, the quantity bounded by `C` in TR1. -/
def gridVal (κ θ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (n k : ℕ) : ℝ :=
  ‖deriv (fwdMapInv (drive κ B ω) ((k : ℝ) / 4 ^ n))
      (((2 : ℝ) ^ (-(n : ℝ)) : ℝ) * Complex.I)‖ / (2 : ℝ) ^ ((n : ℝ) * (1 - θ))

/-- The bad grid event at level `n` for the driver `B`: some dyadic time `k/4ⁿ` with
`k ≤ N 4ⁿ` at which the normalized derivative exceeds `1`. -/
def gridBad (κ θ : ℝ) (B : ℝ≥0 → Ω → ℝ) (N n : ℕ) : Set Ω :=
  {ω | ∃ k ∈ Finset.range (N * 4 ^ n + 1), 1 < gridVal κ θ B ω n k}

/-- The same grid point, for the reverse map driven by the time-reversed Brownian path
`revBM B (k/4ⁿ)`: the event that E2 controls. -/
def gridBadRev (κ θ : ℝ) (B : ℝ≥0 → Ω → ℝ) (N n k : ℕ) : Set Ω :=
  {ω | (2 : ℝ) ^ ((n : ℝ) * (1 - θ)) <
    ‖deriv (revMap (drive κ (revBM B ((k : ℝ) / 4 ^ n).toNNReal) ω) ((k : ℝ) / 4 ^ n))
      (((2 : ℝ) ^ (-(n : ℝ)) : ℝ) * Complex.I)‖}

theorem gridVal_nonneg (κ θ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (n k : ℕ) :
    0 ≤ gridVal κ θ B ω n k :=
  div_nonneg (norm_nonneg _) (Real.rpow_nonneg (by norm_num) _)

/-! ## The derivative under time reversal (P3(e), differentiated) -/

/-- P3(e) at the level of derivatives: on `H`, `f̂_t` and the reverse map of the time-reversed
Brownian path agree, so their derivatives agree at every point of `H`. -/
theorem deriv_fwdMapInv_eq_deriv_revMap_revBM (κ : ℝ) {B : ℝ≥0 → Ω → ℝ} {t : ℝ} (ht : 0 ≤ t)
    {ω : Ω} (hc : Continuous (B · ω)) (h0 : B 0 ω = 0) {w : ℂ} (hw : w ∈ H) :
    deriv (fwdMapInv (drive κ B ω) t) w =
      deriv (revMap (drive κ (revBM B t.toNNReal) ω) t) w :=
  Filter.EventuallyEq.deriv_eq <|
    eventually_of_mem (isOpen_H.mem_nhds hw) fun z hz =>
      fwdMapInv_drive_eq_revMap_revBM κ B ht hc h0 hz

/-! ## E2 in grid coordinates -/

/-- **TR1, one grid point.** E2 (`rs_tail_bound_axis`) with `r = rsR1 κ`, `β = θ` and
`y = 2^{−n}`: `P{‖(u_T)'(i2^{−n})‖ > 2^{n(1−θ)}} ≤ qⁿ`. -/
theorem rs_grid_tail_le (hB : IsBrownianReal B P) {κ θ : ℝ} (hκ : 0 < κ) (hκ8 : κ ≤ 8)
    (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    P {ω | (2 : ℝ) ^ ((n : ℝ) * (1 - θ)) <
        ‖deriv (revMap (drive κ B ω) T) (((2 : ℝ) ^ (-(n : ℝ)) : ℝ) * Complex.I)‖}
      ≤ ENNReal.ofReal ((rsGridQ κ θ) ^ n) := by
  have hy : 0 < (2 : ℝ) ^ (-(n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h := rs_tail_bound_axis (B := B) hB hκ (rsR1_nonneg hκ) hT hy (rsLam_rsR1_nonneg hκ)
    (rsZeta_rsR1_nonneg hκ hκ8) θ
  rw [rsGridQ]
  rwa [rpow_two_neg_natCast_sub_one n θ,
    rpow_two_neg_natCast_mul n ((1 - θ) * (rsLam κ (rsR1 κ) + rsZeta κ (rsR1 κ)))] at h

/-! ## TR1 -/

/-- **TR1 (EXT-RS), grid bound on the imaginary axis at dyadic times.** Kemppainen, *Schramm–
Loewner Evolution*, Prop. 5.10 and Remark 5.13 (p. 99); Rohde–Schramm, Thm. 3.6 and (3.19)
(pp. 16–18).

For `0 < κ ≤ 8`, `0 < θ < (κ/16 + 4/κ − 1)/(κ/16 + 4/κ + 1)` and `N ∈ ℕ`, almost surely there
is `C : ℝ` with `‖(f̂_{k/4ⁿ})'(i2^{−n})‖ ≤ C 2^{n(1−θ)}` for all `n, k ∈ ℕ` with
`k/4ⁿ ≤ N` (so `t = k/4ⁿ ∈ [0,N]` is a dyadic time of mesh `2^{−2n}` and `i2^{−n} ∈ H`).

The hypothesis `κ ≤ 8` is not in the blueprint statement: E2's side condition
`0 ≤ rsZeta κ (rsR1 κ)` holds iff `κ ≤ 8`, and for `κ > 8` no admissible `r` of that route has
`λ + ζ > 2` (the maximum over `r ≤ 4/κ` is `2`), so the Borel–Cantelli sum diverges for every
`θ > 0`. See the module docstring; the case proved here is the one TR2–TR4 (`κ < 8`) consume. -/
theorem ae_grid_bound_le_eight (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ ≤ 8)
    {θ : ℝ} (hθ : 0 < θ) (hθ0 : θ < (κ / 16 + 4 / κ - 1) / (κ / 16 + 4 / κ + 1)) (N : ℕ) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ n k : ℕ, (k : ℝ) / 4 ^ n ≤ N →
      ‖deriv (fwdMapInv (drive κ B ω) ((k : ℝ) / 4 ^ n)) (Complex.I / 2 ^ n)‖ ≤
        C * 2 ^ ((n : ℝ) * (1 - θ)) := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hB'pre : IsPreBrownianReal B' P :=
    hB.toIsPreBrownianReal.congr fun t => hB'eq.mono fun ω h => (h t).symm
  have hB'0 : ∀ᵐ ω ∂P, B' 0 ω = 0 := by
    filter_upwards [hB'eq, hB.eval_zero_ae_eq_zero] with ω h1 h2
    rw [h1 0, h2]
  -- exponent arithmetic: `θ < θ₀` gives exponent `> 2` at `r = r₁`
  have hkey : 2 < (1 - θ) * (rsLam κ (rsR1 κ) + rsZeta κ (rsR1 κ)) := by
    have hA : (κ / 16 + 4 / κ - 1) / (κ / 16 + 4 / κ + 1) = (κ - 8) ^ 2 / (κ + 8) ^ 2 := by
      field_simp
      ring
    have h1 : θ < (κ - 8) ^ 2 / (κ + 8) ^ 2 := hA ▸ hθ0
    have h2 : (κ - 8) ^ 2 / (κ + 8) ^ 2 = 1 - 32 * κ / (8 + κ) ^ 2 := by
      field_simp
      ring
    rw [rsLam_add_rsZeta_rsR1 hκ]
    have h3 : 32 * κ / (8 + κ) ^ 2 < 1 - θ := by linarith
    have h4 : (0 : ℝ) < (8 + κ) ^ 2 / (16 * κ) := by positivity
    have h5 := mul_lt_mul_of_pos_right h3 h4
    have h6 : 32 * κ / (8 + κ) ^ 2 * ((8 + κ) ^ 2 / (16 * κ)) = 2 := by
      field_simp
      ring
    linarith
  have hq0 : 0 < rsGridQ κ θ := Real.rpow_pos_of_pos (by norm_num) _
  have h4q : 4 * rsGridQ κ θ < 1 := by
    have h14 : ((1 : ℝ) / 2) ^ (2 : ℝ) = 1 / 4 := by
      rw [Real.rpow_two]
      norm_num
    have hlt := Real.rpow_lt_rpow_of_exponent_gt (x := (1 : ℝ) / 2) (y := (1 - θ) *
      (rsLam κ (rsR1 κ) + rsZeta κ (rsR1 κ))) (z := (2 : ℝ)) (by norm_num) (by norm_num) hkey
    rw [h14] at hlt
    have hq : rsGridQ κ θ = ((1 : ℝ) / 2) ^ ((1 - θ) * (rsLam κ (rsR1 κ) + rsZeta κ (rsR1 κ))) := by
      rw [rsGridQ, one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hq]
    linarith
  -- per-level probability bound
  have hFn : ∀ n : ℕ, P (gridBad κ θ B' N n) ≤
      ENNReal.ofReal (((N : ℝ) * (4 : ℝ) ^ n + 1) * (rsGridQ κ θ) ^ n) := by
    intro n
    have hsub : gridBad κ θ B' N n ∩ {ω | B' 0 ω = 0} ⊆
        ⋃ k ∈ Finset.range (N * 4 ^ n + 1), gridBadRev κ θ B' N n k := by
      rintro ω ⟨⟨k, hk, hbad⟩, h0⟩
      simp only [gridVal] at hbad
      refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, ?_⟩⟩
      simp only [gridBadRev]
      have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * (1 - θ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have ht : 0 ≤ (k : ℝ) / 4 ^ n := by positivity
      have hp : (((2 : ℝ) ^ (-(n : ℝ)) : ℝ) : ℂ) * Complex.I ∈ H :=
        mul_I_mem_H (Real.rpow_pos_of_pos (by norm_num) _)
      have hder := deriv_fwdMapInv_eq_deriv_revMap_revBM κ ht (hB'c ω) h0 hp
      rw [lt_div_iff₀ hpos, one_mul] at hbad
      rwa [hder] at hbad
    have hG0c : P ({ω | B' 0 ω = 0} : Set Ω)ᶜ = 0 := by
      have h : P {ω | ¬ B' 0 ω = 0} = 0 := ae_iff.1 hB'0
      rwa [← show ({ω | B' 0 ω = 0} : Set Ω)ᶜ = {ω | ¬ B' 0 ω = 0} by ext ω; simp] at h
    have h1 : gridBad κ θ B' N n ⊆
        {ω | B' 0 ω = 0}ᶜ ∪ (gridBad κ θ B' N n ∩ {ω | B' 0 ω = 0}) := by
      intro ω hω
      by_cases h : ω ∈ {ω | B' 0 ω = 0}
      · exact Or.inr ⟨hω, h⟩
      · exact Or.inl h
    calc P (gridBad κ θ B' N n)
        ≤ P ({ω | B' 0 ω = 0}ᶜ ∪ (gridBad κ θ B' N n ∩ {ω | B' 0 ω = 0})) := measure_mono h1
      _ ≤ P {ω | B' 0 ω = 0}ᶜ + P (gridBad κ θ B' N n ∩ {ω | B' 0 ω = 0}) := measure_union_le _ _
      _ = P (gridBad κ θ B' N n ∩ {ω | B' 0 ω = 0}) := by rw [hG0c, zero_add]
      _ ≤ P (⋃ k ∈ Finset.range (N * 4 ^ n + 1), gridBadRev κ θ B' N n k) := measure_mono hsub
      _ ≤ ∑ k ∈ Finset.range (N * 4 ^ n + 1), P (gridBadRev κ θ B' N n k) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range (N * 4 ^ n + 1), ENNReal.ofReal ((rsGridQ κ θ) ^ n) :=
          Finset.sum_le_sum fun k hk => by
            have hT : 0 ≤ (k : ℝ) / 4 ^ n := by positivity
            exact rs_grid_tail_le (isBrownianReal_revBM hB'pre hB'c ((k : ℝ) / 4 ^ n).toNNReal)
              hκ hκ8 n hT
      _ = ENNReal.ofReal (((N : ℝ) * (4 : ℝ) ^ n + 1) * (rsGridQ κ θ) ^ n) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            (show ((N * 4 ^ n + 1 : ℕ) : ℝ) = (N : ℝ) * (4 : ℝ) ^ n + 1 by push_cast; ring),
            ENNReal.ofReal_mul (by positivity)]
  -- summability of the level probabilities
  have hsumm : Summable fun n : ℕ => ((N : ℝ) * (4 : ℝ) ^ n + 1) * (rsGridQ κ θ) ^ n := by
    have h4qnn : 0 ≤ 4 * rsGridQ κ θ := by linarith
    have hgeom4 : Summable fun n : ℕ => (4 * rsGridQ κ θ) ^ n :=
      summable_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg h4qnn]; exact h4q)
    have hgeomq : Summable fun n : ℕ => (rsGridQ κ θ) ^ n :=
      summable_geometric_of_norm_lt_one
        (by rw [Real.norm_eq_abs, abs_of_nonneg hq0.le]; exact lt_of_le_of_lt (by linarith) h4q)
    have h : Summable fun n : ℕ => (N : ℝ) * (4 * rsGridQ κ θ) ^ n + 1 * (rsGridQ κ θ) ^ n :=
      (hgeom4.mul_left (N : ℝ)).add (hgeomq.mul_left 1)
    have hfun : (fun n : ℕ => (N : ℝ) * (4 * rsGridQ κ θ) ^ n + 1 * (rsGridQ κ θ) ^ n) =
        fun n : ℕ => ((N : ℝ) * (4 : ℝ) ^ n + 1) * (rsGridQ κ θ) ^ n := by
      funext n
      rw [mul_pow]
      ring
    rwa [hfun] at h
  have htsum : (∑' n, P (gridBad κ θ B' N n)) ≠ ∞ := by
    have h1 : ∑' n, P (gridBad κ θ B' N n) ≤
        ∑' n, ENNReal.ofReal (((N : ℝ) * (4 : ℝ) ^ n + 1) * (rsGridQ κ θ) ^ n) :=
      ENNReal.tsum_le_tsum hFn
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (by positivity) (pow_nonneg hq0.le n)) hsumm] at h1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  -- Borel–Cantelli: a.s. only finitely many bad levels
  filter_upwards [ae_eventually_notMem htsum, hB'eq] with ω hω heq
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.1 hω
  set C : ℝ := 1 + ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (N * 4 ^ n + 1),
    gridVal κ θ B' ω n k with hCdef
  have hC1 : 1 ≤ C := by
    rw [hCdef]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i hi =>
      Finset.sum_nonneg fun j hj => gridVal_nonneg κ θ B' ω i j)
  have hsum0 : (0 : ℝ) ≤ ∑ n' ∈ Finset.range (m + 1),
      ∑ k' ∈ Finset.range (N * 4 ^ n' + 1), gridVal κ θ B' ω n' k' :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => gridVal_nonneg κ θ B' ω i j
  have hdrive : drive κ B' ω = drive κ B ω := by
    funext t
    simp only [drive]
    rw [heq t.toNNReal]
  refine ⟨C, fun n k hk => ?_⟩
  rw [← hdrive, ← ofReal_two_neg_rpow_mul_I n]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * (1 - θ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hkn : k ≤ N * 4 ^ n := by
    have h1 : (k : ℝ) ≤ (N : ℝ) * (4 : ℝ) ^ n := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ n)] at hk
      exact hk
    have h2 : ((N * 4 ^ n : ℕ) : ℝ) = (N : ℝ) * (4 : ℝ) ^ n := by push_cast; ring
    rw [← h2] at h1
    exact_mod_cast h1
  have hkF : k ∈ Finset.range (N * 4 ^ n + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hkn)
  rcases le_or_gt m n with hmn | hmn
  · have hnot : ω ∉ gridBad κ θ B' N n := hm n hmn
    have hle : gridVal κ θ B' ω n k ≤ 1 := by
      by_contra hc
      exact hnot (show ∃ k ∈ Finset.range (N * 4 ^ n + 1), 1 < gridVal κ θ B' ω n k from
        ⟨k, hkF, not_le.mp hc⟩)
    exact (div_le_iff₀ hpos).mp (hle.trans hC1)
  · have hinner : gridVal κ θ B' ω n k ≤
        ∑ k' ∈ Finset.range (N * 4 ^ n + 1), gridVal κ θ B' ω n k' :=
      Finset.single_le_sum (fun j hj => gridVal_nonneg κ θ B' ω n j) hkF
    have houter : (∑ k' ∈ Finset.range (N * 4 ^ n + 1), gridVal κ θ B' ω n k') ≤
        ∑ n' ∈ Finset.range (m + 1), ∑ k' ∈ Finset.range (N * 4 ^ n' + 1),
          gridVal κ θ B' ω n' k' :=
      Finset.single_le_sum (f := fun n' : ℕ =>
          ∑ k' ∈ Finset.range (N * 4 ^ n' + 1), gridVal κ θ B' ω n' k')
        (fun i hi => Finset.sum_nonneg fun j hj => gridVal_nonneg κ θ B' ω i j)
        (Finset.mem_range.2 (Nat.lt_succ_of_lt hmn))
    have hC : gridVal κ θ B' ω n k ≤ C := by
      rw [hCdef]
      linarith
    exact (div_le_iff₀ hpos).mp hC

end RS
end QuantumZipper
