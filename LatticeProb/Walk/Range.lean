/-
The range of the simple random walk as a functional of the path: its
expectation, the hitting identity behind it, and the lower bound

    E_0 |R_t| ≥ (t + 1) / ∑_{k ≤ t} p_k(0,0) .

The range is the sum over the sites of the indicator that the walk visits them,
so its expectation is the sum over the sites of the chance of visiting one.  The
chance of visiting `z` from `x` by time `t` is the chance of visiting the origin
from `x - z`, which the first-passage kernel computes.

The lower bound is the first-passage decomposition summed twice.  Reaching `z`
at time `k` is reaching it first at some time and returning in the rest, so the
expected number of visits to `z` before time `t` is at most the chance of ever
visiting it times the number of returns; summing over `z` makes the left side
`t + 1`.
-/
import LatticeProb.Walk.HitProb
import LatticeProb.Prob.CountableMeasurable
import LatticeProb.Walk.SRWDiag
import LatticeProb.ParticleHoleLemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset MeasureTheory
open scoped ENNReal

namespace LatticeProb

variable {d : ℕ}

/-! ### The range of a path -/

/-- `|R_t|`, the number of distinct sites the path visits by time `t`. -/
def rangeCard (X : ℕ → Site d) (t : ℕ) : ℕ := ((Finset.range (t + 1)).image X).card

theorem mem_rangeImage_iff (X : ℕ → Site d) (t : ℕ) (z : Site d) :
    z ∈ (Finset.range (t + 1)).image X ↔ ∃ j ≤ t, X j = z := by
  simp only [Finset.mem_image, Finset.mem_range]
  exact ⟨fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩, fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩⟩

theorem rangeCard_le_succ (X : ℕ → Site d) (t : ℕ) : rangeCard X t ≤ t + 1 :=
  le_trans Finset.card_image_le (by rw [Finset.card_range])

theorem rangeCard_eq_fin (X : ℕ → Site d) (t : ℕ) :
    rangeCard X t = (Finset.univ.image fun j : Fin (t + 1) => X (j : ℕ)).card := by
  rw [rangeCard]
  congr 1
  apply Finset.ext
  intro z
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and]
  exact ⟨fun ⟨j, hj, h⟩ => ⟨⟨j, hj⟩, h⟩, fun ⟨j, h⟩ => ⟨(j : ℕ), j.isLt, h⟩⟩

theorem measurable_rangeCard (t : ℕ) :
    Measurable fun X : ℕ → Site d => rangeCard X t := by
  have h1 : Measurable fun X : ℕ → Site d => (fun j : Fin (t + 1) => X (j : ℕ)) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  have h2 : Measurable fun v : Fin (t + 1) → Site d => (Finset.univ.image v).card :=
    measurable_from_countable' _
  have hcomp : (fun X : ℕ → Site d => rangeCard X t)
      = (fun v : Fin (t + 1) → Site d => (Finset.univ.image v).card)
        ∘ (fun X : ℕ → Site d => (fun j : Fin (t + 1) => X (j : ℕ))) :=
    funext fun X => rangeCard_eq_fin X t
  rw [hcomp]
  exact h2.comp h1

/-! ### The event of visiting a site -/

/-- The event that the path visits `z` by time `t`. -/
def visitBy (d : ℕ) (z : Site d) (t : ℕ) : Set (ℕ → Site d) := {X | ∃ j ≤ t, X j = z}

theorem measurableSet_visitBy (z : Site d) (t : ℕ) : MeasurableSet (visitBy d z t) := by
  have hrw : visitBy d z t = ⋃ j ∈ Finset.range (t + 1),
      (fun X : ℕ → Site d => X j) ⁻¹' {z} := by
    ext X
    simp only [visitBy, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact ⟨fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩, fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩⟩
  rw [hrw]
  exact MeasurableSet.biUnion (Set.to_countable _) fun j _ =>
    (measurable_pi_apply j) (measurableSet_singleton z)

theorem rangeCard_eq_tsum (X : ℕ → Site d) (t : ℕ) :
    (rangeCard X t : ℝ≥0∞)
      = ∑' z : Site d, Set.indicator (visitBy d z t) (1 : (ℕ → Site d) → ℝ≥0∞) X := by
  classical
  have hiff : ∀ z : Site d,
      Set.indicator (visitBy d z t) (1 : (ℕ → Site d) → ℝ≥0∞) X
        = if z ∈ (Finset.range (t + 1)).image X then 1 else 0 := by
    intro z
    by_cases hz : X ∈ visitBy d z t
    · rw [Set.indicator_of_mem hz, if_pos ((mem_rangeImage_iff X t z).mpr hz)]
      rfl
    · rw [Set.indicator_of_notMem hz, if_neg (fun h => hz ((mem_rangeImage_iff X t z).mp h))]
  rw [tsum_congr hiff, tsum_eq_sum (s := (Finset.range (t + 1)).image X)
    (fun z hz => by rw [if_neg hz])]
  rw [Finset.sum_congr rfl (fun z hz => by rw [if_pos hz]), Finset.sum_const, nsmul_eq_mul,
    mul_one, rangeCard]

/-- **The expectation of the range** is the sum over the sites of the chance of
visiting one of them. -/
theorem lintegral_rangeCard (x : Site d) (t : ℕ) :
    ∫⁻ X, (rangeCard X t : ℝ≥0∞) ∂(siteWalkLaw d x)
      = ∑' z : Site d, siteWalkLaw d x (visitBy d z t) := by
  rw [lintegral_congr fun X => rangeCard_eq_tsum X t,
    lintegral_tsum fun z => (measurable_one.indicator (measurableSet_visitBy z t)).aemeasurable]
  exact tsum_congr fun z => lintegral_indicator_one (measurableSet_visitBy z t)

/-! ### Visiting a site is visiting the origin from the difference -/

theorem sitePath_sub (x z : Site d) (ξ : ℕ → Site d) (j : ℕ) :
    sitePath (x - z) ξ j = sitePath x ξ j - z := by
  simp only [sitePath]
  abel

theorem siteWalkLaw_visitBy (hd : 1 ≤ d) [NeZero d] (x z : Site d) (t : ℕ) :
    siteWalkLaw d x (visitBy d z t) = ENNReal.ofReal (srwHitBy d t (x - z)) := by
  have hpre : sitePath x ⁻¹' visitBy d z t = sitePath (x - z) ⁻¹' hitOriginBy d t := by
    ext ξ
    simp only [Set.mem_preimage, visitBy, hitOriginBy, Set.mem_setOf_eq]
    constructor
    · rintro ⟨j, hj, h⟩
      exact ⟨j, hj, by rw [sitePath_sub, h, sub_self]⟩
    · rintro ⟨j, hj, h⟩
      rw [sitePath_sub, sub_eq_zero] at h
      exact ⟨j, hj, h⟩
  rw [siteWalkLaw, Measure.map_apply (measurable_sitePath x) (measurableSet_visitBy z t), hpre,
    ← Measure.map_apply (measurable_sitePath (x - z)) (measurableSet_hitOriginBy t),
    ← siteWalkLaw]
  exact siteWalkLaw_hitOriginBy hd t (x - z)

/-! ### The first-passage bound on the occupation sum -/

/-- The expected number of visits to `z` before time `t` is at most the chance
of ever visiting it times the expected number of returns. -/
theorem sum_srwHeat_le_srwHitBy_mul (t : ℕ) (z : Site d) :
    ∑ k ∈ Finset.range (t + 1), srwHeat d k z
      ≤ srwHitBy d t z * srwGreen d (t + 1) 0 := by
  classical
  have hexch : ∑ k ∈ Finset.range (t + 1), ∑ j ∈ Finset.range (k + 1),
        srwFirstHit d j z * srwHeat d (k - j) 0
      = ∑ j ∈ Finset.range (t + 1), ∑ k ∈ Finset.Icc j t,
        srwFirstHit d j z * srwHeat d (k - j) 0 := by
    refine Finset.sum_comm' ?_
    intro k j
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega
  have hinner : ∀ j ∈ Finset.range (t + 1),
      ∑ k ∈ Finset.Icc j t, srwFirstHit d j z * srwHeat d (k - j) 0
        ≤ srwFirstHit d j z * srwGreen d (t + 1) 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    have himg : Finset.image (fun i => i + j) (Finset.range (t + 1 - j)) = Finset.Icc j t := by
      ext k
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨i, hi, rfl⟩; omega
      · intro h; exact ⟨k - j, by omega, by omega⟩
    rw [← himg, Finset.sum_image (fun a _ b _ h => by omega)]
    have hterm : ∀ i ∈ Finset.range (t + 1 - j),
        srwFirstHit d j z * srwHeat d (i + j - j) 0 = srwFirstHit d j z * srwHeat d i 0 := by
      intro i _
      congr 2
      omega
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (srwFirstHit_nonneg j z)
    rw [srwGreen]
    have hsub : Finset.range (t + 1 - j) ⊆ Finset.range (t + 1) := by
      intro i hi
      rw [Finset.mem_range] at hi ⊢
      omega
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => srwHeat_nonneg i 0)
  calc ∑ k ∈ Finset.range (t + 1), srwHeat d k z
      = ∑ k ∈ Finset.range (t + 1), ∑ j ∈ Finset.range (k + 1),
          srwFirstHit d j z * srwHeat d (k - j) 0 :=
        Finset.sum_congr rfl fun k _ => srwHeat_eq_sum_srwFirstHit k z
    _ = ∑ j ∈ Finset.range (t + 1), ∑ k ∈ Finset.Icc j t,
          srwFirstHit d j z * srwHeat d (k - j) 0 := hexch
    _ ≤ ∑ j ∈ Finset.range (t + 1), srwFirstHit d j z * srwGreen d (t + 1) 0 :=
        Finset.sum_le_sum hinner
    _ = srwHitBy d t z * srwGreen d (t + 1) 0 := by
        rw [← Finset.sum_mul, srwHitBy]

/-! ### The first-passage kernel is dominated by the heat kernel -/

theorem srwFirstHit_le_srwHeat (j : ℕ) (z : Site d) :
    srwFirstHit d j z ≤ srwHeat d j z := by
  have hdecomp := srwHeat_eq_sum_srwFirstHit j z
  have hmem : j ∈ Finset.range (j + 1) := Finset.mem_range.mpr (by omega)
  have hle : srwFirstHit d j z * srwHeat d (j - j) 0
      ≤ ∑ i ∈ Finset.range (j + 1), srwFirstHit d i z * srwHeat d (j - i) 0 :=
    Finset.single_le_sum
      (f := fun i => srwFirstHit d i z * srwHeat d (j - i) 0)
      (fun i _ => mul_nonneg (srwFirstHit_nonneg i z) (srwHeat_nonneg _ 0)) hmem
  rw [Nat.sub_self, srwHeat_zero, if_pos rfl, mul_one] at hle
  rw [hdecomp]
  exact hle

theorem srwHitBy_eq_zero_of_lt {t : ℕ} {z : Site d} (h : t < graphNorm z) :
    srwHitBy d t z = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_range] at hj
  have h0 : srwHeat d j z = 0 := srwHeat_eq_zero_of_lt (by omega)
  have := srwFirstHit_le_srwHeat j z
  have := srwFirstHit_nonneg j z
  linarith

theorem mem_boxFinset_of_graphNorm_le {t : ℕ} {z : Site d} (h : graphNorm z ≤ t) :
    z ∈ boxFinset (0 : Site d) t := by
  rw [mem_boxFinset_iff]
  intro i
  have hi : (z i).natAbs ≤ graphNorm z :=
    Finset.single_le_sum (f := fun j => (z j).natAbs) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have : (z i).natAbs ≤ t := le_trans hi h
  have hcast : ((z i).natAbs : ℤ) ≤ (t : ℤ) := by exact_mod_cast this
  have hz0 : (0 : Site d) i = 0 := rfl
  rw [hz0, sub_zero, Int.abs_eq_natAbs]
  exact hcast

theorem summable_srwHitBy (t : ℕ) : Summable fun z : Site d => srwHitBy d t z := by
  refine summable_of_ne_finset_zero (s := boxFinset (0 : Site d) t) fun z hz => ?_
  refine srwHitBy_eq_zero_of_lt ?_
  by_contra hcon
  exact hz (mem_boxFinset_of_graphNorm_le (by omega))

/-! ### The lower bound on the expected range -/

/-- `t + 1 ≤ (∑_z P_0(τ_z ≤ t)) · ∑_{k ≤ t} p_k(0,0)`: the walk makes `t + 1`
visits in all, and each site it ever reaches is revisited at most
`∑_{k ≤ t} p_k(0,0)` times on average. -/
theorem succ_le_tsum_srwHitBy_mul (hd : 0 < d) (t : ℕ) :
    (t : ℝ) + 1 ≤ (∑' z : Site d, srwHitBy d t z) * srwGreen d (t + 1) 0 := by
  have hsumz : ∀ k : ℕ, Summable fun z : Site d => srwHeat d k z := fun k => by
    simpa using summable_srwHeat_mul (d := d) k (fun _ => (1 : ℝ))
  have hleft : ∑' z : Site d, ∑ k ∈ Finset.range (t + 1), srwHeat d k z = (t : ℝ) + 1 := by
    rw [Summable.tsum_finsetSum fun k _ => hsumz k]
    rw [Finset.sum_congr rfl fun k _ => tsum_srwHeat hd k]
    simp
  have hsum1 : Summable fun z : Site d => ∑ k ∈ Finset.range (t + 1), srwHeat d k z :=
    summable_sum fun k _ => hsumz k
  have hsum2 : Summable fun z : Site d => srwHitBy d t z * srwGreen d (t + 1) 0 :=
    (summable_srwHitBy t).mul_right _
  have hcmp : ∑' z : Site d, ∑ k ∈ Finset.range (t + 1), srwHeat d k z
      ≤ ∑' z : Site d, srwHitBy d t z * srwGreen d (t + 1) 0 :=
    hsum1.tsum_le_tsum (fun z => sum_srwHeat_le_srwHitBy_mul t z) hsum2
  rw [hleft, (summable_srwHitBy t).tsum_mul_right] at hcmp
  exact hcmp

/-! ### The expected range -/

theorem integrable_rangeCard [NeZero d] (x : Site d) (t : ℕ) :
    Integrable (fun X : ℕ → Site d => (rangeCard X t : ℝ)) (siteWalkLaw d x) := by
  refine Integrable.mono' (integrable_const ((t : ℝ) + 1))
    (((measurable_from_countable' (fun n : ℕ => (n : ℝ))).comp
      (measurable_rangeCard t)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h : ((rangeCard X t : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (rangeCard_le_succ X t)
  simpa using h

/-- **The expected range is the sum over the sites of the chance of reaching
one**, in the reals. -/
theorem integral_rangeCard_eq_tsum (hd : 1 ≤ d) [NeZero d] (x : Site d) (t : ℕ) :
    ∫ X, (rangeCard X t : ℝ) ∂(siteWalkLaw d x) = ∑' z : Site d, srwHitBy d t (x - z) := by
  have hsum : Summable fun z : Site d => srwHitBy d t (x - z) :=
    (summable_srwHitBy (d := d) t).comp_injective (fun a b h => by
      have h' : x - a = x - b := h
      have := congrArg (fun y : Site d => x - y) h'
      simpa using sub_right_injective h')
  have hnn : ∀ z : Site d, 0 ≤ srwHitBy d t (x - z) := fun z => srwHitBy_nonneg t (x - z)
  have hL : ENNReal.ofReal (∫ X, (rangeCard X t : ℝ) ∂(siteWalkLaw d x))
      = ∫⁻ X, (rangeCard X t : ℝ≥0∞) ∂(siteWalkLaw d x) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_rangeCard x t)
      (Filter.Eventually.of_forall fun X => by positivity)]
    exact lintegral_congr fun X => ENNReal.ofReal_natCast _
  have hR : ∫⁻ X, (rangeCard X t : ℝ≥0∞) ∂(siteWalkLaw d x)
      = ENNReal.ofReal (∑' z : Site d, srwHitBy d t (x - z)) := by
    rw [lintegral_rangeCard, ENNReal.ofReal_tsum_of_nonneg hnn hsum]
    exact tsum_congr fun z => siteWalkLaw_visitBy hd x z t
  have heq : ENNReal.ofReal (∫ X, (rangeCard X t : ℝ) ∂(siteWalkLaw d x))
      = ENNReal.ofReal (∑' z : Site d, srwHitBy d t (x - z)) := by rw [hL, hR]
  exact (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg fun X => by positivity) (tsum_nonneg hnn)).mp heq

theorem tsum_srwHitBy_sub (x : Site d) (t : ℕ) :
    ∑' z : Site d, srwHitBy d t (x - z) = ∑' w : Site d, srwHitBy d t w :=
  (Equiv.subLeft x).tsum_eq fun w => srwHitBy d t w

theorem one_le_srwGreen_origin (t : ℕ) : (1 : ℝ) ≤ srwGreen d (t + 1) 0 := by
  have hmem : 0 ∈ Finset.range (t + 1) := Finset.mem_range.mpr (by omega)
  have := Finset.single_le_sum (f := fun k => srwHeat d k (0 : Site d))
    (fun k _ => srwHeat_nonneg k 0) hmem
  rw [srwHeat_zero, if_pos rfl] at this
  exact this

/-- **The first moment of the range from below**:
`E_x |R_t| ≥ (t + 1) / ∑_{k ≤ t} p_k(0,0)`. -/
theorem succ_le_integral_rangeCard_mul (hd : 1 ≤ d) [NeZero d] (x : Site d) (t : ℕ) :
    (t : ℝ) + 1 ≤ (∫ X, (rangeCard X t : ℝ) ∂(siteWalkLaw d x)) * srwGreen d (t + 1) 0 := by
  rw [integral_rangeCard_eq_tsum hd x t, tsum_srwHitBy_sub x t]
  exact succ_le_tsum_srwHitBy_mul (by omega) t

theorem div_le_integral_rangeCard (hd : 1 ≤ d) [NeZero d] (x : Site d) (t : ℕ) :
    ((t : ℝ) + 1) / srwGreen d (t + 1) 0 ≤ ∫ X, (rangeCard X t : ℝ) ∂(siteWalkLaw d x) := by
  have hpos : (0 : ℝ) < srwGreen d (t + 1) 0 :=
    lt_of_lt_of_le zero_lt_one (one_le_srwGreen_origin t)
  rw [div_le_iff₀ hpos]
  exact succ_le_integral_rangeCard_mul hd x t

end LatticeProb