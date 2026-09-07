/-
The probability of ever hitting the origin, and the Green-function identity
`P_x(τ_0 < ∞) = G(x,0)/G(0,0)`.

The first-passage kernel `f_k(x)` is defined by its own recursion: it is one at
`k = 0, x = 0`, zero at `x = 0` afterwards, and otherwise one step of the walk.
Reaching the origin at time `k` is reaching it first at some time `j ≤ k` and
returning in the remaining `k - j` steps, which on the kernels is

  `p_k(x, 0) = ∑_{j ≤ k} f_j(x) p_{k-j}(0, 0)`.

Summing on `k` is a Cauchy product, and in dimension three and above both
series converge, so `G(x,0) = (∑_k f_k(x)) G(0,0)`.  The partial sums of `f`
are the probabilities of hitting the origin by time `k`, which identifies
`∑_k f_k(x)` with the law of the event `{∃ j, X_j = 0}` under the walk started
at `x`.
-/
import LatticeProb.Walk.Markov
import LatticeProb.Walk.GreenIdentity
import LatticeProb.Walk.SimpleTransfer
import LatticeProb.Prob.InfinitePiSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset MeasureTheory
open scoped ENNReal

namespace LatticeProb

variable {d : ℕ}

/-! ### The first-passage kernel of the origin -/

/-- `f_k(x)`, the probability that the walk started at `x` is at the origin for
the FIRST time at step `k`. -/
noncomputable def srwFirstHit (d : ℕ) : ℕ → Site d → ℝ
  | 0 => fun x => if x = 0 then 1 else 0
  | k + 1 => fun x => if x = 0 then 0 else walkOp (srwFirstHit d k) x

theorem srwFirstHit_zero (x : Site d) :
    srwFirstHit d 0 x = if x = 0 then 1 else 0 := rfl

theorem srwFirstHit_succ (k : ℕ) (x : Site d) :
    srwFirstHit d (k + 1) x = if x = 0 then 0 else walkOp (srwFirstHit d k) x := rfl

theorem srwFirstHit_succ_origin (k : ℕ) : srwFirstHit d (k + 1) 0 = 0 := by
  rw [srwFirstHit_succ, if_pos rfl]

theorem srwFirstHit_succ_of_ne {x : Site d} (hx : x ≠ 0) (k : ℕ) :
    srwFirstHit d (k + 1) x = walkOp (srwFirstHit d k) x := by
  rw [srwFirstHit_succ, if_neg hx]

theorem srwFirstHit_zero_of_ne {x : Site d} (hx : x ≠ 0) :
    srwFirstHit d 0 x = 0 := by
  rw [srwFirstHit_zero, if_neg hx]

theorem srwFirstHit_nonneg : ∀ (k : ℕ) (x : Site d), 0 ≤ srwFirstHit d k x := by
  intro k
  induction k with
  | zero => intro x; rw [srwFirstHit_zero]; split <;> norm_num
  | succ k ih =>
      intro x
      rw [srwFirstHit_succ]
      split
      · exact le_rfl
      · exact div_nonneg (Finset.sum_nonneg fun i _ => add_nonneg (ih _) (ih _)) (by positivity)

/-! ### The linearity of the walk operator over a finite sum -/

theorem walkOp_finsetSum {ι : Type*} (s : Finset ι) (F : ι → Site d → ℝ) (x : Site d) :
    walkOp (fun y => ∑ j ∈ s, F j y) x = ∑ j ∈ s, walkOp (F j) x := by
  simp only [walkOp, nbrSum, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => (Finset.sum_add_distrib).symm

theorem walkOp_mul_const (u : Site d → ℝ) (c : ℝ) (x : Site d) :
    walkOp (fun y => u y * c) x = walkOp u x * c := by
  simp only [walkOp, nbrSum, div_mul_eq_mul_div, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The first-passage decomposition -/

/-- **The first-passage decomposition.**  Being at the origin at time `k` is
being there first at some time `j ≤ k` and returning in the rest. -/
theorem srwHeat_eq_sum_srwFirstHit :
    ∀ (k : ℕ) (x : Site d),
      srwHeat d k x = ∑ j ∈ Finset.range (k + 1), srwFirstHit d j x * srwHeat d (k - j) 0 := by
  intro k
  induction k with
  | zero =>
      intro x
      rw [Finset.sum_range_one]
      simp [srwFirstHit_zero]
  | succ k ih =>
      intro x
      by_cases hx : x = 0
      · subst hx
        rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
        · rw [srwFirstHit_zero, if_pos rfl, one_mul, Nat.sub_zero]
        · intro j _ hj
          obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
          rw [srwFirstHit_succ_origin, zero_mul]
      · have hfun : srwHeat d k
            = fun y => ∑ j ∈ Finset.range (k + 1), srwFirstHit d j y * srwHeat d (k - j) 0 :=
          funext (fun y => ih y)
        rw [srwHeat_succ, hfun, walkOp_finsetSum]
        rw [Finset.sum_range_succ' (fun j => srwFirstHit d j x * srwHeat d (k + 1 - j) 0) (k + 1)]
        rw [srwFirstHit_zero_of_ne hx, zero_mul, add_zero]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [walkOp_mul_const, srwFirstHit_succ_of_ne hx]
        congr 2
        omega

/-! ### The partial sums -/

/-- `∑_{j ≤ k} f_j(x)`, the probability of reaching the origin by time `k`. -/
noncomputable def srwHitBy (d : ℕ) (k : ℕ) (x : Site d) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), srwFirstHit d j x

theorem srwHitBy_zero (x : Site d) : srwHitBy d 0 x = if x = 0 then 1 else 0 := by
  rw [srwHitBy, Finset.sum_range_one, srwFirstHit_zero]

theorem srwHitBy_succ_origin (k : ℕ) : srwHitBy d (k + 1) (0 : Site d) = 1 := by
  rw [srwHitBy, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
  · rw [srwFirstHit_zero, if_pos rfl]
  · intro j _ hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    exact srwFirstHit_succ_origin m

theorem srwHitBy_succ_of_ne {x : Site d} (hx : x ≠ 0) (k : ℕ) :
    srwHitBy d (k + 1) x = walkOp (srwHitBy d k) x := by
  rw [srwHitBy, Finset.sum_range_succ' (fun j => srwFirstHit d j x) (k + 1),
    srwFirstHit_zero_of_ne hx, add_zero]
  have hfun : srwHitBy d k = fun y => ∑ j ∈ Finset.range (k + 1), srwFirstHit d j y := rfl
  rw [hfun, walkOp_finsetSum]
  exact Finset.sum_congr rfl fun j _ => srwFirstHit_succ_of_ne hx j

theorem srwHitBy_nonneg (k : ℕ) (x : Site d) : 0 ≤ srwHitBy d k x :=
  Finset.sum_nonneg fun j _ => srwFirstHit_nonneg j x

theorem srwHitBy_le_one (hd : 0 < d) : ∀ (k : ℕ) (x : Site d), srwHitBy d k x ≤ 1 := by
  intro k
  induction k with
  | zero => intro x; rw [srwHitBy_zero]; split <;> norm_num
  | succ k ih =>
      intro x
      by_cases hx : x = 0
      · subst hx; rw [srwHitBy_succ_origin]
      · rw [srwHitBy_succ_of_ne hx]
        have hb : ∀ y : Site d, ‖srwHitBy d k y‖ ≤ 1 := fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (srwHitBy_nonneg k y)]
          exact ih y
        have := norm_walkOp_le hd hb x
        rw [Real.norm_eq_abs] at this
        exact le_trans (le_abs_self _) this

/-! ### Summability and the hitting probability -/

theorem summable_srwFirstHit (hd : 0 < d) (x : Site d) :
    Summable fun k : ℕ => srwFirstHit d k x := by
  refine summable_of_sum_range_le (c := 1) (fun k => srwFirstHit_nonneg k x) fun n => ?_
  cases n with
  | zero => simp
  | succ m => exact srwHitBy_le_one hd m x

/-- `P_x(τ_0 < ∞)`, the probability that the walk started at `x` ever reaches
the origin. -/
noncomputable def srwHitProb (d : ℕ) (x : Site d) : ℝ := ∑' k : ℕ, srwFirstHit d k x

theorem srwHitProb_nonneg (x : Site d) : 0 ≤ srwHitProb d x :=
  tsum_nonneg fun k => srwFirstHit_nonneg k x

/-! ### The Green-function identity -/

theorem srwGreenInf_eq_hitProb_mul (hd : 3 ≤ d) (x : Site d) :
    srwGreenInf d x = srwHitProb d x * srwGreenInf d 0 := by
  have hd0 : 0 < d := by omega
  have hf : Summable fun k : ℕ => ‖srwFirstHit d k x‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (srwFirstHit_nonneg _ x)] using
      (summable_srwFirstHit hd0 x)
  have hg : Summable fun k : ℕ => ‖srwHeat d k (0 : Site d)‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (srwHeat_nonneg _ (0 : Site d))] using
      (summable_srwHeat hd (0 : Site d))
  rw [srwHitProb, srwGreenInf, srwGreenInf,
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg]
  exact tsum_congr fun k => srwHeat_eq_sum_srwFirstHit k x

theorem one_le_srwGreenInf_origin (hd : 3 ≤ d) : 1 ≤ srwGreenInf d (0 : Site d) := by
  have hs := summable_srwHeat hd (0 : Site d)
  have := hs.le_tsum 0 (fun k _ => srwHeat_nonneg k (0 : Site d))
  simpa [srwGreenInf] using this

/-- **The hitting probability of the origin is a ratio of Green functions.** -/
theorem srwHitProb_eq_green_ratio (hd : 3 ≤ d) (x : Site d) :
    srwHitProb d x = srwGreenInf d x / srwGreenInf d 0 := by
  have h0 : srwGreenInf d (0 : Site d) ≠ 0 := by
    have := one_le_srwGreenInf_origin (d := d) hd
    linarith
  rw [srwGreenInf_eq_hitProb_mul hd x, mul_div_assoc, div_self h0, mul_one]

/-! ### The hitting probability is the law of the event `{∃ j, X_j = 0}` -/

/-- Every function on the lattice is integrable against the law of one
increment, which is a finite sum of Dirac masses. -/
theorem integrable_of_incLaw (hd : 1 ≤ d) (f : Site d → ℝ) : Integrable f (incLaw d) := by
  have hint : ∀ a : Site d, Integrable f (Measure.dirac a) := fun a =>
    integrable_dirac (by simp [enorm_lt_top])
  have hdne : (d : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hd0 : (2 * (d : ℝ≥0∞)) ≠ 0 := mul_ne_zero two_ne_zero hdne
  rw [incLaw, instructionLaw]
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr hd0)
  exact integrable_finsetSum_measure.2 fun i _ => (hint _).add_measure (hint _)

/-- The event that the walk has reached the origin by time `k`. -/
def hitOriginBy (d : ℕ) (k : ℕ) : Set (ℕ → Site d) := {X | ∃ j ≤ k, X j = 0}

/-- The event that the walk ever reaches the origin. -/
def hitOrigin (d : ℕ) : Set (ℕ → Site d) := {X | ∃ j, X j = 0}

theorem measurableSet_hitOriginBy (k : ℕ) : MeasurableSet (hitOriginBy d k) := by
  have : hitOriginBy d k
      = ⋃ j ∈ Finset.range (k + 1), (fun X : ℕ → Site d => X j) ⁻¹' {(0 : Site d)} := by
    ext X
    simp only [hitOriginBy, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range,
      Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩, fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩⟩
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun j _ =>
    (measurable_pi_apply j) (measurableSet_singleton _)

theorem measurableSet_hitOrigin : MeasurableSet (hitOrigin d) := by
  have : hitOrigin d = ⋃ k : ℕ, hitOriginBy d k := by
    ext X
    simp only [hitOrigin, hitOriginBy, Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun ⟨j, h⟩ => ⟨j, j, le_rfl, h⟩, fun ⟨_, j, _, h⟩ => ⟨j, h⟩⟩
  rw [this]
  exact MeasurableSet.iUnion fun k => measurableSet_hitOriginBy k

theorem hitOriginBy_monotone : Monotone (hitOriginBy d) := by
  intro m n hmn X hX
  obtain ⟨j, hj, h⟩ := hX
  exact ⟨j, le_trans hj hmn, h⟩

/-- Consing an increment onto the front shifts the path by one step. -/
theorem tailNat_consNat {X : Type*} (u : X) (ω : ℕ → X) : tailNat (consNat u ω) = ω :=
  funext fun _ => rfl

theorem sitePath_consNat (x u : Site d) (ω : ℕ → Site d) (m : ℕ) :
    sitePath x (consNat u ω) (m + 1) = sitePath (x + u) ω m := by
  simp only [sitePath]
  rw [Finset.sum_range_succ' (fun j => consNat u ω j) m]
  simp only [consNat_zero, consNat_succ]
  abel

theorem preimage_hitOriginBy_succ (x : Site d) (k : ℕ) :
    sitePath x ⁻¹' hitOriginBy d (k + 1)
      = if x = 0 then Set.univ
        else {ξ : ℕ → Site d | sitePath (x + ξ 0) (tailNat ξ) ∈ hitOriginBy d k} := by
  by_cases hx : x = 0
  · rw [if_pos hx]
    ext ξ
    simp only [Set.mem_preimage, Set.mem_univ, iff_true, hitOriginBy, Set.mem_setOf_eq]
    exact ⟨0, by omega, by rw [sitePath_zero]; exact hx⟩
  · rw [if_neg hx]
    ext ξ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hitOriginBy]
    have hkey : ∀ m : ℕ,
        sitePath x ξ (m + 1) = sitePath (x + ξ 0) (tailNat ξ) m := by
      intro m
      have h := sitePath_consNat x (ξ 0) (tailNat ξ) m
      rw [consNat_head_tail] at h
      exact h
    constructor
    · rintro ⟨j, hj, h⟩
      cases j with
      | zero =>
          rw [sitePath_zero] at h
          exact absurd h hx
      | succ m =>
          refine ⟨m, by omega, ?_⟩
          rw [← hkey m]
          exact h
    · rintro ⟨m, hm, h⟩
      refine ⟨m + 1, by omega, ?_⟩
      rw [hkey m]
      exact h

/-- **The law of the event of hitting the origin by time `k`.** -/
theorem siteWalkLaw_hitOriginBy (hd : 1 ≤ d) [NeZero d] :
    ∀ (k : ℕ) (x : Site d),
      siteWalkLaw d x (hitOriginBy d k) = ENNReal.ofReal (srwHitBy d k x) := by
  intro k
  induction k with
  | zero =>
      intro x
      rw [siteWalkLaw, Measure.map_apply (measurable_sitePath x) (measurableSet_hitOriginBy 0)]
      have hpre : sitePath x ⁻¹' hitOriginBy d 0 = if x = 0 then Set.univ else ∅ := by
        by_cases hx : x = 0
        · rw [if_pos hx]
          ext ξ
          simp only [Set.mem_preimage, Set.mem_univ, iff_true, hitOriginBy, Set.mem_setOf_eq]
          exact ⟨0, le_rfl, by rw [sitePath_zero]; exact hx⟩
        · rw [if_neg hx]
          ext ξ
          simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false, hitOriginBy,
            Set.mem_setOf_eq]
          rintro ⟨j, hj, h⟩
          rw [Nat.le_zero] at hj
          subst hj
          rw [sitePath_zero] at h
          exact hx h
      rw [hpre, srwHitBy_zero]
      by_cases hx : x = 0
      · rw [if_pos hx, if_pos hx]
        simp
      · rw [if_neg hx, if_neg hx]
        simp
  | succ k ih =>
      intro x
      rw [siteWalkLaw, Measure.map_apply (measurable_sitePath x)
        (measurableSet_hitOriginBy (k + 1)), preimage_hitOriginBy_succ]
      by_cases hx : x = 0
      · subst hx
        rw [if_pos rfl, srwHitBy_succ_origin]
        simp
      · rw [if_neg hx, srwHitBy_succ_of_ne hx]
        set B : Set (ℕ → Site d) := hitOriginBy d k with hB
        have hBm : MeasurableSet B := measurableSet_hitOriginBy k
        have hshift : Measurable fun ξ : ℕ → Site d => sitePath (x + ξ 0) (tailNat ξ) :=
          measurable_sitePath_uncurry.comp
            ((((measurable_of_countable fun v : Site d => x + v).comp
              (measurable_pi_apply 0))).prodMk measurable_tailNat)
        have hset : MeasurableSet
            {ξ : ℕ → Site d | sitePath (x + ξ 0) (tailNat ξ) ∈ B} := hshift hBm
        have hmeas : Measurable (Set.indicator
            {ξ : ℕ → Site d | sitePath (x + ξ 0) (tailNat ξ) ∈ B} (1 : (ℕ → Site d) → ℝ≥0∞)) :=
          measurable_one.indicator hset
        have e1 : (Measure.infinitePi fun _ : ℕ => incLaw d)
              {ξ : ℕ → Site d | sitePath (x + ξ 0) (tailNat ξ) ∈ B}
            = ∫⁻ ξ, Set.indicator {ξ : ℕ → Site d | sitePath (x + ξ 0) (tailNat ξ) ∈ B}
                (1 : (ℕ → Site d) → ℝ≥0∞) ξ ∂(Measure.infinitePi fun _ : ℕ => incLaw d) :=
          (lintegral_indicator_one hset).symm
        have e2 : ∀ u : Site d,
            (∫⁻ ω, Set.indicator {ξ : ℕ → Site d | sitePath (x + ξ 0) (tailNat ξ) ∈ B}
                (1 : (ℕ → Site d) → ℝ≥0∞) (consNat u ω)
              ∂(Measure.infinitePi fun _ : ℕ => incLaw d))
              = ENNReal.ofReal (srwHitBy d k (x + u)) := by
          intro u
          have hpre : ∀ ω : ℕ → Site d,
              Set.indicator {ξ : ℕ → Site d | sitePath (x + ξ 0) (tailNat ξ) ∈ B}
                  (1 : (ℕ → Site d) → ℝ≥0∞) (consNat u ω)
                = Set.indicator (sitePath (x + u) ⁻¹' B) (1 : (ℕ → Site d) → ℝ≥0∞) ω := by
            intro ω
            rfl
          rw [lintegral_congr hpre, lintegral_indicator_one (measurable_sitePath (x + u) hBm),
            ← Measure.map_apply (measurable_sitePath (x + u)) hBm]
          exact ih (x + u)
        rw [e1, lintegral_infinitePi_nat_head_tail (incLaw d) _ hmeas, lintegral_congr e2,
          ← ofReal_integral_eq_lintegral_ofReal (integrable_of_incLaw hd _)
            (Filter.Eventually.of_forall fun u => srwHitBy_nonneg k (x + u)),
          integral_incLaw_add]

/-- **The probability of ever hitting the origin.** -/
theorem siteWalkLaw_hitOrigin (hd : 1 ≤ d) [NeZero d] (x : Site d) :
    siteWalkLaw d x (hitOrigin d) = ENNReal.ofReal (srwHitProb d x) := by
  have hunion : hitOrigin d = ⋃ k : ℕ, hitOriginBy d k := by
    ext X
    simp only [hitOrigin, hitOriginBy, Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun ⟨j, h⟩ => ⟨j, j, le_rfl, h⟩, fun ⟨_, j, _, h⟩ => ⟨j, h⟩⟩
  have h1 : Filter.Tendsto (fun k => siteWalkLaw d x (hitOriginBy d k)) Filter.atTop
      (nhds (siteWalkLaw d x (hitOrigin d))) := by
    rw [hunion]
    exact tendsto_measure_iUnion_atTop hitOriginBy_monotone
  have h2 : Filter.Tendsto (fun k => srwHitBy d k x) Filter.atTop (nhds (srwHitProb d x)) := by
    have hs := (summable_srwFirstHit (d := d) (by omega) x).hasSum.tendsto_sum_nat
    exact hs.comp (Filter.tendsto_add_atTop_nat 1)
  have h3 : Filter.Tendsto (fun k => ENNReal.ofReal (srwHitBy d k x)) Filter.atTop
      (nhds (ENNReal.ofReal (srwHitProb d x))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp h2
  refine tendsto_nhds_unique h1 ?_
  simpa only [siteWalkLaw_hitOriginBy hd] using h3

/-- **The hitting probability of the origin is a ratio of Green functions**,
in the vocabulary of the walk on path space. -/
theorem siteWalkLaw_hitOrigin_eq_green_ratio (hd : 3 ≤ d) [NeZero d] (x : Site d) :
    siteWalkLaw d x (hitOrigin d) = ENNReal.ofReal (srwGreenInf d x / srwGreenInf d 0) := by
  rw [siteWalkLaw_hitOrigin (by omega) x, srwHitProb_eq_green_ratio hd x]

end LatticeProb
