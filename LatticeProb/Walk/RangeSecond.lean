/-
The second moment of the range of the walk.

`E_x|R_t|^2 ≤ 2 (E_x|R_t|)^2`.  Pair the sites the path visits and split the
pairs by which of the two is reached first.  The two halves have the same
number of pairs, so the count of all pairs is at most twice the count of the
ordered ones, and the sites reached after `z` are, seen from `z`, sites the
shifted path reaches in at most `t` steps.  That is the pathwise inequality

    |R_t|^2 ≤ 2 ∑_{z ∈ R_t} |R_t(θ_{τ_z} X)| ,

and the strong Markov property at `τ_z`, the hitting time of `z` truncated at
`t`, turns each term of the sum into `P_x(τ_z ≤ t) · E_z|R_t|`.  Summing on `z`
gives `2 (E_x|R_t|)(E_0|R_t|)`, and the first moment does not depend on the
starting site.

The truncated hitting time is bounded by `t + 1`, so the bounded strong Markov
property `LatticeProb.markov_stopping` is all that is needed; the value `t + 1`
off the event `{τ_z ≤ t}` is what keeps it a stopping time, where `ENat.toNat`
of the untruncated time would not be.
-/
import LatticeProb.Walk.Range
import LatticeProb.Walk.MarkovAE
import LatticeProb.Walk.ExteriorDirichlet

noncomputable section

namespace LatticeProb

open MeasureTheory
open scoped Classical

variable {d : ℕ}

/-! ### Pairs ordered by a rank -/

/-- Half of the pairs of a finite set are ordered by any given rank. -/
theorem card_sq_le_two_mul_sum_filter {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ) :
    S.card ^ 2 ≤ 2 * ∑ z ∈ S, (S.filter fun w => f z ≤ f w).card := by
  classical
  have hone : ∀ z w : α,
      (if f z ≤ f w then (1 : ℕ) else 0) + (if f w < f z then (1 : ℕ) else 0) = 1 := by
    intro z w
    by_cases h : f z ≤ f w
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg h, if_pos (by omega)]
  have hsq : S.card ^ 2 = ∑ _z ∈ S, ∑ _w ∈ S, (1 : ℕ) := by
    simp [Finset.sum_const, sq]
  have hB : ∑ z ∈ S, ∑ w ∈ S, (if f w < f z then (1 : ℕ) else 0)
      = ∑ z ∈ S, ∑ w ∈ S, (if f z < f w then (1 : ℕ) else 0) := Finset.sum_comm
  have hle : ∑ z ∈ S, ∑ w ∈ S, (if f z < f w then (1 : ℕ) else 0)
      ≤ ∑ z ∈ S, ∑ w ∈ S, (if f z ≤ f w then (1 : ℕ) else 0) := by
    refine Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun w _ => ?_
    by_cases h : f z < f w
    · rw [if_pos h, if_pos (le_of_lt h)]
    · rw [if_neg h]; positivity
  have hcard : ∑ z ∈ S, (S.filter fun w => f z ≤ f w).card
      = ∑ z ∈ S, ∑ w ∈ S, (if f z ≤ f w then (1 : ℕ) else 0) :=
    Finset.sum_congr rfl fun z _ => Finset.card_filter _ _
  have hsplit : S.card ^ 2
      = (∑ z ∈ S, ∑ w ∈ S, (if f z ≤ f w then (1 : ℕ) else 0))
        + ∑ z ∈ S, ∑ w ∈ S, (if f w < f z then (1 : ℕ) else 0) := by
    rw [hsq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => (hone z w).symm
  rw [hcard, hsplit, hB]
  omega

/-! ### The hitting time truncated at the horizon -/

/-- The first time at most `t` at which the path is at `z`, and `t + 1` if there
is none. -/
noncomputable def hitTrunc (z : Site d) (t : ℕ) (X : ℕ → Site d) : ℕ :=
  if h : ∃ j, j ≤ t ∧ X j = z then Nat.find h else t + 1

theorem hitTrunc_le_succ (z : Site d) (t : ℕ) (X : ℕ → Site d) : hitTrunc z t X ≤ t + 1 := by
  rw [hitTrunc]
  split
  · rename_i h
    exact le_trans (Nat.find_spec h).1 (Nat.le_succ t)
  · exact le_rfl

theorem hitTrunc_le_iff {z : Site d} {t : ℕ} {X : ℕ → Site d} :
    hitTrunc z t X ≤ t ↔ ∃ j, j ≤ t ∧ X j = z := by
  constructor
  · intro h
    by_contra hc
    rw [hitTrunc, dif_neg hc] at h
    omega
  · intro h
    rw [hitTrunc, dif_pos h]
    exact (Nat.find_spec h).1

theorem hitTrunc_apply {z : Site d} {t : ℕ} {X : ℕ → Site d} (h : ∃ j, j ≤ t ∧ X j = z) :
    X (hitTrunc z t X) = z := by
  rw [hitTrunc, dif_pos h]
  exact (Nat.find_spec h).2

theorem hitTrunc_le_of {z : Site d} {t j : ℕ} {X : ℕ → Site d} (hj : j ≤ t) (hX : X j = z) :
    hitTrunc z t X ≤ j := by
  have h : ∃ j, j ≤ t ∧ X j = z := ⟨j, hj, hX⟩
  rw [hitTrunc, dif_pos h]
  exact Nat.find_le ⟨hj, hX⟩

theorem isWalkStopping_hitTrunc (z : Site d) (t : ℕ) :
    IsWalkStopping (hitTrunc z t) := by
  intro k X Y hXY hk
  by_cases hkt : k ≤ t
  · have hXt : hitTrunc z t X ≤ t := by omega
    have hX : ∃ j, j ≤ t ∧ X j = z := hitTrunc_le_iff.mp hXt
    have hXk : X k = z := by rw [← hk]; exact hitTrunc_apply hX
    have hYk : Y k = z := by rw [← hXY k le_rfl]; exact hXk
    refine le_antisymm (hitTrunc_le_of hkt hYk) ?_
    by_contra hlt
    rw [not_le] at hlt
    have hY : ∃ j, j ≤ t ∧ Y j = z := ⟨k, hkt, hYk⟩
    have hm : Y (hitTrunc z t Y) = z := hitTrunc_apply hY
    have hmt : hitTrunc z t Y ≤ t := le_trans (le_of_lt hlt) hkt
    have hXm : X (hitTrunc z t Y) = z := by
      rw [hXY (hitTrunc z t Y) (le_of_lt hlt)]; exact hm
    have := hitTrunc_le_of hmt hXm
    omega
  · have h1 := hitTrunc_le_succ z t X
    have hk1 : k = t + 1 := by omega
    have hXn : ¬ ∃ j, j ≤ t ∧ X j = z := by
      intro hc
      have := hitTrunc_le_iff.mpr hc
      omega
    have hYn : ¬ ∃ j, j ≤ t ∧ Y j = z := by
      rintro ⟨j, hj, hjz⟩
      exact hXn ⟨j, hj, by rw [hXY j (by omega)]; exact hjz⟩
    rw [hitTrunc, dif_neg hYn, hk1]

/-! ### The pathwise inequality -/

/-- The sites reached after `z` are, seen from `z`, sites the shifted path
reaches in at most `t` steps. -/
theorem filter_subset_image_shiftPath {X : ℕ → Site d} {t : ℕ} (z : Site d) :
    (((Finset.range (t + 1)).image X).filter
        fun w => hitTrunc z t X ≤ hitTrunc w t X)
      ⊆ (Finset.range (t + 1)).image (shiftPath (hitTrunc z t X) X) := by
  classical
  intro w hw
  rw [Finset.mem_filter] at hw
  obtain ⟨hwS, hle⟩ := hw
  have hwex : ∃ j, j ≤ t ∧ X j = w := by
    obtain ⟨j, hj, hjw⟩ := (mem_rangeImage_iff X t w).mp hwS
    exact ⟨j, hj, hjw⟩
  have hwt : hitTrunc w t X ≤ t := hitTrunc_le_iff.mpr hwex
  have hwval : X (hitTrunc w t X) = w := hitTrunc_apply hwex
  rw [mem_rangeImage_iff]
  refine ⟨hitTrunc w t X - hitTrunc z t X, by omega, ?_⟩
  rw [shiftPath]
  have : hitTrunc z t X + (hitTrunc w t X - hitTrunc z t X) = hitTrunc w t X := by omega
  rw [this, hwval]

/-- **The pathwise second-moment inequality.**  `|R_t|^2 ≤ 2 ∑_{z ∈ R_t}
|R_t(θ_{τ_z} X)|`. -/
theorem rangeCard_sq_le_sum (X : ℕ → Site d) (t : ℕ) :
    rangeCard X t ^ 2
      ≤ 2 * ∑ z ∈ (Finset.range (t + 1)).image X,
          rangeCard (shiftPath (hitTrunc z t X) X) t := by
  classical
  refine le_trans
    (card_sq_le_two_mul_sum_filter ((Finset.range (t + 1)).image X)
      (fun z => hitTrunc z t X)) ?_
  refine Nat.mul_le_mul_left 2 (Finset.sum_le_sum fun z hz => ?_)
  exact Finset.card_le_card (filter_subset_image_shiftPath z)

/-! ### The range is almost surely inside a box -/

theorem mem_boxFinset_of_graphNorm_sub_le {x z : Site d} {t : ℕ}
    (h : graphNorm (x - z) ≤ t) : z ∈ boxFinset x t := by
  rw [mem_boxFinset_iff]
  intro i
  have hi : ((x - z) i).natAbs ≤ graphNorm (x - z) :=
    Finset.single_le_sum (f := fun j => ((x - z) j).natAbs) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hle : ((x - z) i).natAbs ≤ t := le_trans hi h
  have hcast : (((x - z) i).natAbs : ℤ) ≤ (t : ℤ) := by exact_mod_cast hle
  have hval : (x - z) i = x i - z i := rfl
  rw [hval] at hcast
  rw [abs_sub_comm, Int.abs_eq_natAbs]
  exact hcast

theorem siteWalkLaw_visitBy_eq_zero (hd : 1 ≤ d) [NeZero d] {x z : Site d} {t : ℕ}
    (hz : z ∉ boxFinset x t) : siteWalkLaw d x (visitBy d z t) = 0 := by
  rw [siteWalkLaw_visitBy hd]
  have hgt : t < graphNorm (x - z) := by
    by_contra hc
    exact hz (mem_boxFinset_of_graphNorm_sub_le (by omega))
  rw [srwHitBy_eq_zero_of_lt hgt, ENNReal.ofReal_zero]

/-- Almost surely the path stays in the box of radius `t` about its start. -/
theorem ae_image_subset_boxFinset (hd : 1 ≤ d) [NeZero d] (x : Site d) (t : ℕ) :
    ∀ᵐ X ∂(siteWalkLaw d x), (Finset.range (t + 1)).image X ⊆ boxFinset x t := by
  classical
  set A : Site d → Set (ℕ → Site d) :=
    fun z => if z ∈ boxFinset x t then (∅ : Set (ℕ → Site d)) else visitBy d z t with hA
  have hnull : siteWalkLaw d x (⋃ z : Site d, A z) = 0 := by
    refine measure_iUnion_null fun z => ?_
    rw [hA]
    by_cases hz : z ∈ boxFinset x t
    · simp [hz]
    · simpa [hz] using siteWalkLaw_visitBy_eq_zero hd hz
  rw [ae_iff]
  refine measure_mono_null (fun X hX => ?_) hnull
  simp only [Set.mem_setOf_eq] at hX
  obtain ⟨w, hwS, hwB⟩ := Finset.not_subset.mp hX
  refine Set.mem_iUnion.mpr ⟨w, ?_⟩
  rw [hA]
  simp only [hwB, if_false]
  obtain ⟨j, hj, hjw⟩ := (mem_rangeImage_iff X t w).mp hwS
  exact ⟨j, hj, hjw⟩

/-! ### The strong Markov step -/

theorem visitBy_eq_setOf_hitTrunc (z : Site d) (t : ℕ) :
    visitBy d z t = {X : ℕ → Site d | hitTrunc z t X ≤ t} := by
  ext X
  simp only [visitBy, Set.mem_setOf_eq, hitTrunc_le_iff]

theorem measurable_hitIndicator (z : Site d) (t : ℕ) :
    Measurable fun X : ℕ → Site d => if hitTrunc z t X ≤ t then (1 : ℝ) else 0 := by
  refine measurable_of_dependsUpTo (n := t + 1) fun X Y hXY => ?_
  have hk : hitTrunc z t Y = hitTrunc z t X :=
    isWalkStopping_hitTrunc z t (hitTrunc z t X) X Y
      (fun j hj => hXY j (le_trans hj (hitTrunc_le_succ z t X))) rfl
  rw [hk]

theorem measurable_hitRange (z : Site d) (t : ℕ) :
    Measurable fun X : ℕ → Site d =>
      if hitTrunc z t X ≤ t then (rangeCard (shiftPath (hitTrunc z t X) X) t : ℝ) else 0 := by
  have hF : Measurable fun Y : ℕ → Site d => (rangeCard Y t : ℝ) :=
    (measurable_from_countable' (fun n : ℕ => (n : ℝ))).comp (measurable_rangeCard t)
  have h1 := measurable_comp_shiftPath_stopping (isWalkStopping_hitTrunc z t)
    (hitTrunc_le_succ z t) hF
  have heq : (fun X : ℕ → Site d =>
      if hitTrunc z t X ≤ t then (rangeCard (shiftPath (hitTrunc z t X) X) t : ℝ) else 0)
      = fun X : ℕ → Site d => (rangeCard (shiftPath (hitTrunc z t X) X) t : ℝ)
          * (if hitTrunc z t X ≤ t then (1 : ℝ) else 0) := by
    funext X
    by_cases h : hitTrunc z t X ≤ t <;> simp [h]
  rw [heq]
  exact h1.mul (measurable_hitIndicator z t)

theorem hitRange_le (z : Site d) (t : ℕ) (X : ℕ → Site d) :
    |if hitTrunc z t X ≤ t then (rangeCard (shiftPath (hitTrunc z t X) X) t : ℝ) else 0|
      ≤ (t : ℝ) + 1 := by
  by_cases h : hitTrunc z t X ≤ t
  · rw [if_pos h, abs_of_nonneg (by positivity)]
    have := rangeCard_le_succ (shiftPath (hitTrunc z t X) X) t
    have hc : ((rangeCard (shiftPath (hitTrunc z t X) X) t : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ) :=
      Nat.cast_le.mpr this
    simpa using hc
  · rw [if_neg h, abs_zero]
    positivity

theorem integrable_hitRange [NeZero d] (x z : Site d) (t : ℕ) :
    Integrable (fun X : ℕ → Site d =>
      if hitTrunc z t X ≤ t then (rangeCard (shiftPath (hitTrunc z t X) X) t : ℝ) else 0)
      (siteWalkLaw d x) :=
  Integrable.of_bound (measurable_hitRange z t).aestronglyMeasurable ((t : ℝ) + 1)
    (Filter.Eventually.of_forall fun X => by
      simpa [Real.norm_eq_abs] using hitRange_le z t X)

/-- **The strong Markov property at the truncated hitting time of `z`.**  The
expected range of the path after it first reaches `z` is the chance of reaching
`z` times the expected range from `z`. -/
theorem integral_hitRange (hd : 1 ≤ d) [NeZero d] (x z : Site d) (t : ℕ) :
    ∫ X, (if hitTrunc z t X ≤ t then (rangeCard (shiftPath (hitTrunc z t X) X) t : ℝ) else 0)
        ∂(siteWalkLaw d x)
      = (∫ Y, (rangeCard Y t : ℝ) ∂(siteWalkLaw d z)) * srwHitBy d t (x - z) := by
  classical
  set F : (ℕ → Site d) → ℝ := fun Y => (rangeCard Y t : ℝ) with hFdef
  set G : (ℕ → Site d) → ℝ := fun X => if hitTrunc z t X ≤ t then (1 : ℝ) else 0 with hGdef
  have hFm : Measurable F :=
    (measurable_from_countable' (fun n : ℕ => (n : ℝ))).comp (measurable_rangeCard t)
  have hFb : ∀ Y, ‖F Y‖ ≤ (t : ℝ) + 1 := by
    intro Y
    rw [hFdef, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hc : ((rangeCard Y t : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (rangeCard_le_succ Y t)
    simpa using hc
  have hGb : ∀ X, ‖G X‖ ≤ 1 := by
    intro X
    rw [hGdef]
    by_cases h : hitTrunc z t X ≤ t <;> simp [h]
  have hGdep : ∀ (k : ℕ) (X Y : ℕ → Site d), (∀ j ≤ k, X j = Y j) →
      hitTrunc z t X = k → G X = G Y := by
    intro k X Y hXY hk
    have hkY : hitTrunc z t Y = k := isWalkStopping_hitTrunc z t k X Y hXY hk
    rw [hGdef]
    simp only [hk, hkY]
  have hmark := markov_stopping d (t + 1) x (hitTrunc z t) (isWalkStopping_hitTrunc z t)
    (hitTrunc_le_succ z t) F hFm hFb G hGb hGdep
  have hL : ∀ X : ℕ → Site d, F (shiftPath (hitTrunc z t X) X) * G X
      = if hitTrunc z t X ≤ t then (rangeCard (shiftPath (hitTrunc z t X) X) t : ℝ) else 0 := by
    intro X
    rw [hGdef, hFdef]
    by_cases h : hitTrunc z t X ≤ t <;> simp [h]
  have hR : ∀ X : ℕ → Site d, pathExpect d F (X (hitTrunc z t X)) * G X
      = (∫ Y, (rangeCard Y t : ℝ) ∂(siteWalkLaw d z)) * G X := by
    intro X
    by_cases h : hitTrunc z t X ≤ t
    · have hx : X (hitTrunc z t X) = z := hitTrunc_apply (hitTrunc_le_iff.mp h)
      rw [hx]
      rfl
    · rw [hGdef]
      simp [h]
  rw [← integral_congr_ae (Filter.Eventually.of_forall hL), hmark,
    integral_congr_ae (Filter.Eventually.of_forall hR), integral_const_mul]
  congr 1
  have hGind : G = (visitBy d z t).indicator (fun _ => (1 : ℝ)) := by
    funext X
    rw [hGdef, visitBy_eq_setOf_hitTrunc, Set.indicator_apply]
    rfl
  rw [hGind, integral_indicator_const (1 : ℝ) (by
      rw [visitBy_eq_setOf_hitTrunc] at *
      exact (measurableSet_visitBy z t).congr (by rw [visitBy_eq_setOf_hitTrunc])),
    smul_eq_mul, mul_one, measureReal_def, siteWalkLaw_visitBy hd,
    ENNReal.toReal_ofReal (srwHitBy_nonneg t (x - z))]

/-! ### The second moment -/

theorem hitRange_nonneg (z : Site d) (t : ℕ) (X : ℕ → Site d) :
    0 ≤ if hitTrunc z t X ≤ t then (rangeCard (shiftPath (hitTrunc z t X) X) t : ℝ) else 0 := by
  by_cases h : hitTrunc z t X ≤ t
  · rw [if_pos h]; positivity
  · rw [if_neg h]

theorem rangeCard_sq_le_sum_box (X : ℕ → Site d) (t : ℕ) (B : Finset (Site d))
    (hB : (Finset.range (t + 1)).image X ⊆ B) :
    ((rangeCard X t : ℝ)) ^ 2
      ≤ 2 * ∑ z ∈ B,
          (if hitTrunc z t X ≤ t then (rangeCard (shiftPath (hitTrunc z t X) X) t : ℝ) else 0) := by
  classical
  have h1 : ((rangeCard X t : ℝ)) ^ 2
      ≤ 2 * ∑ z ∈ (Finset.range (t + 1)).image X,
          ((rangeCard (shiftPath (hitTrunc z t X) X) t : ℕ) : ℝ) := by
    have hnat := rangeCard_sq_le_sum X t
    have hcast : ((rangeCard X t ^ 2 : ℕ) : ℝ)
        ≤ ((2 * ∑ z ∈ (Finset.range (t + 1)).image X,
              rangeCard (shiftPath (hitTrunc z t X) X) t : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    push_cast at hcast
    exact hcast
  refine le_trans h1 ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have h2 : ∑ z ∈ (Finset.range (t + 1)).image X,
        ((rangeCard (shiftPath (hitTrunc z t X) X) t : ℕ) : ℝ)
      = ∑ z ∈ (Finset.range (t + 1)).image X,
          (if hitTrunc z t X ≤ t then (rangeCard (shiftPath (hitTrunc z t X) X) t : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun z hz => ?_
    obtain ⟨j, hj, hjz⟩ := (mem_rangeImage_iff X t z).mp hz
    rw [if_pos (hitTrunc_le_iff.mpr ⟨j, hj, hjz⟩)]
  rw [h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg hB fun z _ _ => hitRange_nonneg z t X

theorem summable_srwHitBy_sub (x : Site d) (t : ℕ) :
    Summable fun z : Site d => srwHitBy d t (x - z) :=
  (summable_srwHitBy (d := d) t).comp_injective (fun a b h => by
    have h' : x - a = x - b := h
    exact sub_right_injective h')

theorem integrable_rangeCard_sq [NeZero d] (x : Site d) (t : ℕ) :
    Integrable (fun X : ℕ → Site d => ((rangeCard X t : ℝ)) ^ 2) (siteWalkLaw d x) := by
  have hF : Measurable fun X : ℕ → Site d => ((rangeCard X t : ℝ)) ^ 2 :=
    ((measurable_from_countable' (fun n : ℕ => (n : ℝ))).comp (measurable_rangeCard t)).pow_const 2
  refine Integrable.of_bound hF.aestronglyMeasurable (((t : ℝ) + 1) ^ 2)
    (Filter.Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hc : ((rangeCard X t : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (rangeCard_le_succ X t)
  have hc' : (rangeCard X t : ℝ) ≤ (t : ℝ) + 1 := by simpa using hc
  exact pow_le_pow_left₀ (by positivity) hc' 2

/-- **The second moment of the range.**  `E_x|R_t|^2 ≤ 2 (E_x|R_t|)^2`. -/
theorem integral_rangeCard_sq_le (hd : 1 ≤ d) [NeZero d] (x : Site d) (t : ℕ) :
    ∫ X, ((rangeCard X t : ℝ)) ^ 2 ∂(siteWalkLaw d x)
      ≤ 2 * (∫ X, (rangeCard X t : ℝ) ∂(siteWalkLaw d x)) ^ 2 := by
  classical
  set m : ℝ := ∑' w : Site d, srwHitBy d t w with hm
  have hmz : ∀ z : Site d, ∫ Y, (rangeCard Y t : ℝ) ∂(siteWalkLaw d z) = m := by
    intro z
    rw [integral_rangeCard_eq_tsum hd, tsum_srwHitBy_sub]
  have hmnn : 0 ≤ m := by
    rw [hm]
    exact tsum_nonneg fun w => srwHitBy_nonneg t w
  set B : Finset (Site d) := boxFinset x t with hB
  have hae : ∀ᵐ X ∂(siteWalkLaw d x), ((rangeCard X t : ℝ)) ^ 2
      ≤ 2 * ∑ z ∈ B,
          (if hitTrunc z t X ≤ t then (rangeCard (shiftPath (hitTrunc z t X) X) t : ℝ) else 0) := by
    filter_upwards [ae_image_subset_boxFinset hd x t] with X hX
    exact rangeCard_sq_le_sum_box X t B hX
  have hintR : Integrable (fun X : ℕ → Site d => 2 * ∑ z ∈ B,
      (if hitTrunc z t X ≤ t then (rangeCard (shiftPath (hitTrunc z t X) X) t : ℝ) else 0))
      (siteWalkLaw d x) :=
    (integrable_finsetSum B fun z _ => integrable_hitRange x z t).const_mul 2
  refine le_trans (integral_mono_ae (integrable_rangeCard_sq x t) hintR hae) ?_
  rw [integral_const_mul, integral_finsetSum B fun z _ => integrable_hitRange x z t]
  have hterm : ∀ z : Site d,
      ∫ X, (if hitTrunc z t X ≤ t then (rangeCard (shiftPath (hitTrunc z t X) X) t : ℝ) else 0)
          ∂(siteWalkLaw d x) = m * srwHitBy d t (x - z) := by
    intro z
    rw [integral_hitRange hd, hmz]
  rw [Finset.sum_congr rfl fun z _ => hterm z, ← Finset.mul_sum]
  have hsumle : ∑ z ∈ B, srwHitBy d t (x - z) ≤ m := by
    refine le_trans (Summable.sum_le_tsum B (fun z _ => srwHitBy_nonneg t (x - z))
      (summable_srwHitBy_sub x t)) ?_
    rw [tsum_srwHitBy_sub]
  have hmx : ∫ X, (rangeCard X t : ℝ) ∂(siteWalkLaw d x) = m := hmz x
  rw [hmx, sq]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumle hmnn) (by norm_num)

/-! ### The block decomposition -/

theorem walkOp_iterate_const (hd : 1 ≤ d) (c : ℝ) : ∀ (n : ℕ) (x : Site d),
    walkOp^[n] (fun _ : Site d => c) x = c := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply]
      have : walkOp (fun _ : Site d => c) = fun _ : Site d => c := funext fun y => walkOp_const hd c y
      rw [this]
      exact ih x

/-- The expected range of the path after a deterministic time is the expected
range of the walk. -/
theorem integral_rangeCard_shiftPath (hd : 1 ≤ d) [NeZero d] (x : Site d) (n t : ℕ) :
    ∫ X, (rangeCard (shiftPath n X) t : ℝ) ∂(siteWalkLaw d x)
      = ∑' w : Site d, srwHitBy d t w := by
  have hFm : Measurable fun Y : ℕ → Site d => (rangeCard Y t : ℝ) :=
    (measurable_from_countable' (fun k : ℕ => (k : ℝ))).comp (measurable_rangeCard t)
  have hFb : ∀ Y : ℕ → Site d, ‖(rangeCard Y t : ℝ)‖ ≤ (t : ℝ) + 1 := by
    intro Y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hc : ((rangeCard Y t : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (rangeCard_le_succ Y t)
    simpa using hc
  have hpe : pathExpect d (fun Y : ℕ → Site d => (rangeCard Y t : ℝ))
      = fun _ : Site d => ∑' w : Site d, srwHitBy d t w := by
    funext z
    rw [pathExpect, integral_rangeCard_eq_tsum hd, tsum_srwHitBy_sub]
  rw [integral_comp_shiftPath d n x _ hFm hFb, hpe, walkOp_iterate_const hd]

/-- **The block decomposition of the range.**  The sites visited in `n` blocks of
`t + 1` steps are the sites visited by the `n` shifted paths. -/
theorem card_image_le_sum_blocks (X : ℕ → Site d) (n t : ℕ) :
    ((Finset.range (n * (t + 1))).image X).card
      ≤ ∑ i ∈ Finset.range n, rangeCard (shiftPath (i * (t + 1)) X) t := by
  classical
  refine le_trans (Finset.card_le_card (?_ :
      (Finset.range (n * (t + 1))).image X ⊆
        (Finset.range n).biUnion
          fun i => (Finset.range (t + 1)).image (shiftPath (i * (t + 1)) X))) ?_
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨j, hj, hjy⟩ := hy
    rw [Finset.mem_range] at hj
    have ht : 0 < t + 1 := Nat.succ_pos t
    refine Finset.mem_biUnion.mpr ⟨j / (t + 1), Finset.mem_range.mpr ?_, ?_⟩
    · refine Nat.div_lt_of_lt_mul ?_
      rw [mul_comm]
      exact hj
    · rw [Finset.mem_image]
      refine ⟨j % (t + 1), Finset.mem_range.mpr (Nat.mod_lt _ ht), ?_⟩
      rw [shiftPath]
      have hdm : j / (t + 1) * (t + 1) + j % (t + 1) = j := Nat.div_add_mod' j (t + 1)
      rw [hdm]
      exact hjy
  · exact le_trans Finset.card_biUnion_le (le_of_eq rfl)

end LatticeProb
