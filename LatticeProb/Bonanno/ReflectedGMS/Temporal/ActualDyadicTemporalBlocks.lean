/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.ActualDyadicTemporalBlocks at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Geometry.DyadicGridTranslation
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NonmacroscopicSelectedBlocks

/-!
# The actual dyadic temporal blocks `J_m(s)`

This module builds the manuscript's temporal block family of
`p:sec:timeblocks` (manuscript section 16, display `p:eq:timekappa`):

```
  D(J) = sup {|I| : I ∈ 𝓘, I ∩ J ≠ ∅},   α(J) = sup_{k ≥ 0} D(J⁽ᵏ⁾)/|J⁽ᵏ⁾|,
  β(J) = α(J)⁻¹,                          κ(J) = ∑_{k ≥ 0} 4⁻ᵏ β(J⁽ᵏ⁾),
  J_m(s) = the largest dyadic interval through `s` with κ(J) ≤ m,
```

together with the three structural properties that the conditional temporal
averaging lemma `p:lem:timeconditional` and the chain convergence lemma
`p:lem:timeconverge` actually consume:

* **the block-partition identity**: `t ∈ J_m(s)` forces `J_m(t) = J_m(s)`, which is
  what makes the incoming integral of the manuscript transport kernel
  `V(Ω,𝒟_t,s,t) = |J_m(s)|⁻¹ 1_{t ∈ J_m(s)} U(θ_t Ω, 𝒟_t - t)` collapse to
  `U(Ω,𝒟_t)` (`timeSelected_of_mem`, `timeBlockAt_eq_of_mem`);
* **nesting in the block parameter**: `m ≤ m'` gives `J_m(s) ⊆ J_{m'}(s)`
  (`timeBlockAt_subset_of_selected_le`), the source of the decreasing sigma-fields
  `𝒢_m`;
* **re-rooting covariance with the time grid shifted as well**
  (`timeSelected_translate`, `timeBlockAt_translate`): re-rooting the trajectory at
  `r` and translating the marked dyadic system by the same `r` transports
  `J_m(s)` to `J_m(s - r) = J_m(s) - r`.  This is the exact covariance the
  manuscript uses when it says the average is invariant "with the time grid
  shifted as well"; it is the scaling-free half of the invariance of `𝒢_m`.

Deterministic content only: no law, no measure and no stationarity hypothesis
occurs in this file.  In particular nothing here asserts annealed probability
stationarity of the rooted law.

## The one-dimensional marked dyadic system

The manuscript's `𝒟_t` is "an independent uniform one-dimensional dyadic system":
a uniform logarithmic phase, a uniform origin position at every level, and uniform
successive parent digits.  That is exactly one coordinate of the *existing* marked
grid `ReflectedGMS.DyadicApproximation.Grid`, whose cylinder law
`UniformGridLaw` is already the manuscript's uniform marking.  So no new grid
structure is introduced: `timeBlockAt D k s` is the level-`k` half-open dyadic
interval of the first coordinate of `D` containing `s`, and the re-rooting action
is the *existing* `DyadicGridTranslation.translate`, reused through
`translatedOrigin_eq`.

Because the chain through a fixed time `s` is indexed by its level, the whole
ancestor chain of the manuscript is the family `k ↦ timeBlockAt D k s`, and no
separate parent map on interval indices is needed: `timeBlockAt_subset_succ` is
the nesting `J ⊆ J⁽¹⁾` and `timeBlockAt_subset_of_le` iterates it.

## The holding-interval input

`𝓘` is the family of *actual* vertex holding intervals.  As in
`ReflectedGMS.Temporal.ActualHolding`, that family is carried by the two-sided
sequence `c : ℤ → ℝ` of actual entrance/departure times of one trajectory, the
interval of index `n` being `Ico (c n) (c (n+1))`; `holdingIntervalOf` and
`holdingLengthOf` below are that family and its lengths for one fixed
configuration, so that `holdingIntervalOf (c ω) n = ActualHolding.actualHoldingInterval c ω n`
holds definitionally.  No holding-interval transport, counting or law is reproved
here; the two places where holding sizes genuinely enter are isolated as

* `blockKappa_le_of_mem_holding` / `exists_blockKappa_le`: the manuscript's
  "down a chain through a holding interval `I_s`, `κ(J) ≤ 2|J|/|I_s| → 0`", which
  needs only that `s` lies in a holding interval of positive length;
* `SublinearBlockDiam` and `exists_lt_blockKappa`: the manuscript's "along
  ancestors `κ → ∞`", which is exactly the submacroscopic conclusion
  `p:eq:holdsmall` of `p:lem:holdingsmall` read along one chain.  This is kept as
  an explicit named hypothesis, not assumed silently: its producer is the actual
  two-sided holding-interval transport, not this file.

The selection theorems are then stated from these two inputs plus the strict
increase of `κ` along the chain, which is derived here
(`blockKappa_lt_succ_of_sublinear`).
-/

set_option autoImplicit false

open Set Filter

open scoped ENNReal Topology

namespace ReflectedGMS.Temporal.ActualDyadicTemporalBlocks

open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridTranslation

/-! ## One-dimensional dyadic time blocks of a marked grid -/

/-- The time origin of the marked dyadic system at level `k`: the first coordinate
of the grid origin. -/
noncomputable def timeOrigin (D : Grid) (k : ℤ) : ℝ := D.origin k 0

/-- Position of the time `s` inside the level-`k` grid, in units of the side length. -/
noncomputable def timeCoord (D : Grid) (k : ℤ) (s : ℝ) : ℝ :=
  (s - timeOrigin D k) / side D k

/-- The integer index of the level-`k` dyadic interval containing `s`. -/
noncomputable def timeIndexAt (D : Grid) (k : ℤ) (s : ℝ) : ℤ := ⌊timeCoord D k s⌋

/-- The left endpoint of the level-`k` dyadic interval containing `s`. -/
noncomputable def timeLowerAt (D : Grid) (k : ℤ) (s : ℝ) : ℝ :=
  timeOrigin D k + side D k * (timeIndexAt D k s : ℝ)

/-- The level-`k` half-open dyadic time interval containing `s`: one member of the
manuscript's `𝒟_t`. -/
noncomputable def timeBlockAt (D : Grid) (k : ℤ) (s : ℝ) : Set ℝ :=
  Set.Ico (timeLowerAt D k s) (timeLowerAt D k s + side D k)

theorem measurableSet_timeBlockAt (D : Grid) (k : ℤ) (s : ℝ) :
    MeasurableSet (timeBlockAt D k s) := measurableSet_Ico

theorem mem_timeBlockAt_self (D : Grid) (k : ℤ) (s : ℝ) : s ∈ timeBlockAt D k s := by
  have hσ : (0 : ℝ) < side D k := side_pos D k
  have hsx : s = timeOrigin D k + side D k * timeCoord D k s := by
    rw [timeCoord]
    field_simp
    ring
  have h1 : ((⌊timeCoord D k s⌋ : ℤ) : ℝ) ≤ timeCoord D k s := Int.floor_le _
  have h2 : timeCoord D k s < ((⌊timeCoord D k s⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  simp only [timeBlockAt, timeLowerAt, timeIndexAt, Set.mem_Ico]
  constructor
  · nlinarith
  · nlinarith

/-- Two times in a common level-`k` block have the same level-`k` index. -/
theorem timeIndexAt_eq_of_mem {D : Grid} {k : ℤ} {s t : ℝ} (h : t ∈ timeBlockAt D k s) :
    timeIndexAt D k t = timeIndexAt D k s := by
  have hσ : (0 : ℝ) < side D k := side_pos D k
  obtain ⟨h1, h2⟩ := h
  simp only [timeLowerAt] at h1 h2
  rw [timeIndexAt, Int.floor_eq_iff]
  constructor
  · rw [timeCoord, le_div_iff₀ hσ]
    linarith
  · rw [timeCoord, div_lt_iff₀ hσ]
    push_cast
    linarith

/-- **The level-`k` partition identity.** -/
theorem timeBlockAt_eq_of_mem {D : Grid} {k : ℤ} {s t : ℝ} (h : t ∈ timeBlockAt D k s) :
    timeBlockAt D k t = timeBlockAt D k s := by
  simp only [timeBlockAt, timeLowerAt, timeIndexAt_eq_of_mem h]

/-! ### Passing to the parent level -/

theorem timeOrigin_compatible (D : Grid) (k : ℤ) :
    timeOrigin D k = timeOrigin D (k + 1) + side D k * ((D.digit k 0).val : ℝ) :=
  D.compatible k 0

theorem timeCoord_succ (D : Grid) (k : ℤ) (s : ℝ) :
    timeCoord D (k + 1) s = (timeCoord D k s + ((D.digit k 0).val : ℝ)) / 2 := by
  have hσ : (0 : ℝ) < side D k := side_pos D k
  have hside : side D (k + 1) = 2 * side D k := DyadicGridTranslation.side_succ D k
  have hcomp := timeOrigin_compatible D k
  simp only [timeCoord, hside]
  rw [hcomp]
  field_simp
  ring

/-- The integer step relation `2 N ≤ n + d ≤ 2 N + 1` between the level-`k` index
`n` and the level-`(k+1)` index `N` of the same time. -/
theorem timeIndex_succ_bounds (D : Grid) (k : ℤ) (s : ℝ) :
    2 * timeIndexAt D (k + 1) s ≤ timeIndexAt D k s + ((D.digit k 0).val : ℤ) ∧
      timeIndexAt D k s + ((D.digit k 0).val : ℤ) ≤ 2 * timeIndexAt D (k + 1) s + 1 := by
  have hc := timeCoord_succ D k s
  have hfloor : timeIndexAt D k s = ⌊timeCoord D k s⌋ := rfl
  have hN1 : ((timeIndexAt D (k + 1) s : ℤ) : ℝ)
      ≤ (timeCoord D k s + ((D.digit k 0).val : ℝ)) / 2 := by
    rw [timeIndexAt, hc]
    exact Int.floor_le _
  have hN2 : (timeCoord D k s + ((D.digit k 0).val : ℝ)) / 2
      < ((timeIndexAt D (k + 1) s : ℤ) : ℝ) + 1 := by
    rw [timeIndexAt, hc]
    exact Int.lt_floor_add_one _
  have hle : 2 * timeIndexAt D (k + 1) s - ((D.digit k 0).val : ℤ) ≤ ⌊timeCoord D k s⌋ :=
    Int.le_floor.2 (by push_cast; linarith)
  have hlt : ⌊timeCoord D k s⌋ < 2 * timeIndexAt D (k + 1) s + 2 - ((D.digit k 0).val : ℤ) :=
    Int.floor_lt.2 (by push_cast; linarith)
  omega

theorem timeLowerAt_succ_le (D : Grid) (k : ℤ) (s : ℝ) :
    timeLowerAt D (k + 1) s ≤ timeLowerAt D k s := by
  obtain ⟨hb1, -⟩ := timeIndex_succ_bounds D k s
  have hσ : (0 : ℝ) < side D k := side_pos D k
  have hside : side D (k + 1) = 2 * side D k := DyadicGridTranslation.side_succ D k
  have hcomp := timeOrigin_compatible D k
  have hb1' : 2 * ((timeIndexAt D (k + 1) s : ℤ) : ℝ)
      ≤ ((timeIndexAt D k s : ℤ) : ℝ) + ((D.digit k 0).val : ℝ) := by
    exact_mod_cast hb1
  simp only [timeLowerAt, hside]
  rw [hcomp]
  nlinarith

theorem timeLowerAt_add_side_le (D : Grid) (k : ℤ) (s : ℝ) :
    timeLowerAt D k s + side D k ≤ timeLowerAt D (k + 1) s + side D (k + 1) := by
  obtain ⟨-, hb2⟩ := timeIndex_succ_bounds D k s
  have hσ : (0 : ℝ) < side D k := side_pos D k
  have hside : side D (k + 1) = 2 * side D k := DyadicGridTranslation.side_succ D k
  have hcomp := timeOrigin_compatible D k
  have hb2' : ((timeIndexAt D k s : ℤ) : ℝ) + ((D.digit k 0).val : ℝ)
      ≤ 2 * ((timeIndexAt D (k + 1) s : ℤ) : ℝ) + 1 := by
    exact_mod_cast hb2
  simp only [timeLowerAt, hside]
  rw [hcomp]
  nlinarith

/-- The manuscript's nesting `J ⊆ J⁽¹⁾`. -/
theorem timeBlockAt_subset_succ (D : Grid) (k : ℤ) (s : ℝ) :
    timeBlockAt D k s ⊆ timeBlockAt D (k + 1) s :=
  Set.Ico_subset_Ico (timeLowerAt_succ_le D k s) (timeLowerAt_add_side_le D k s)

theorem timeBlockAt_subset_of_le (D : Grid) {k l : ℤ} (hkl : k ≤ l) (s : ℝ) :
    timeBlockAt D k s ⊆ timeBlockAt D l s := by
  induction l, hkl using Int.le_induction with
  | base => exact subset_rfl
  | succ l _ ih => exact ih.trans (timeBlockAt_subset_succ D l s)

/-- Two times in a common level-`k` block share every block at every higher level. -/
theorem timeBlockAt_eq_of_mem_of_le (D : Grid) {k l : ℤ} (hkl : k ≤ l) {s t : ℝ}
    (h : t ∈ timeBlockAt D k s) : timeBlockAt D l t = timeBlockAt D l s :=
  timeBlockAt_eq_of_mem (timeBlockAt_subset_of_le D hkl s h)

/-! ### Re-rooting the marked dyadic system

Re-rooting the time axis at `u 0` is the existing translation action
`DyadicGridTranslation.translate u` on the marked grid.  Its effect on the
one-dimensional blocks is the exact translation, with the integer lattice
reindexing absorbed by the containing-index construction.
-/

theorem timeOrigin_translate (D : Grid) (u : Plane) (k : ℤ) :
    timeOrigin (translate u D) k
      = timeOrigin D k - u 0 + side D k * ((latticeShift D u k 0 : ℤ) : ℝ) :=
  translatedOrigin_eq D u k 0

theorem timeCoord_translate (D : Grid) (u : Plane) (k : ℤ) (s : ℝ) :
    timeCoord (translate u D) k (s - u 0)
      = timeCoord D k s - ((latticeShift D u k 0 : ℤ) : ℝ) := by
  have hσ : (0 : ℝ) < side D k := side_pos D k
  have ho := timeOrigin_translate D u k
  simp only [timeCoord, side_translate, ho]
  field_simp
  ring

theorem timeIndexAt_translate (D : Grid) (u : Plane) (k : ℤ) (s : ℝ) :
    timeIndexAt (translate u D) k (s - u 0) = timeIndexAt D k s - latticeShift D u k 0 := by
  simp only [timeIndexAt, timeCoord_translate]
  exact Int.floor_sub_intCast _ _

theorem timeLowerAt_translate (D : Grid) (u : Plane) (k : ℤ) (s : ℝ) :
    timeLowerAt (translate u D) k (s - u 0) = timeLowerAt D k s - u 0 := by
  have ho := timeOrigin_translate D u k
  simp only [timeLowerAt, side_translate, timeIndexAt_translate, ho]
  push_cast
  ring

/-- **Re-rooting covariance of the dyadic time blocks.** -/
theorem timeBlockAt_translate (D : Grid) (u : Plane) (k : ℤ) (s : ℝ) :
    timeBlockAt (translate u D) k (s - u 0)
      = (fun x : ℝ => x + u 0) ⁻¹' timeBlockAt D k s := by
  ext x
  simp only [timeBlockAt, side_translate, timeLowerAt_translate, Set.mem_Ico,
    Set.mem_preimage]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-! ## The actual holding intervals and the block diameter `D(J)` -/

/-! ## The indices `α`, `β`, `κ` along the chain through a time -/

/-! ### The chain statistics only see levels above the current one -/

/-! ### Re-rooting covariance of the chain statistics

Under a re-rooting by `r` the actual holding data is translated by `-r` and
re-indexed, which is exactly the structural covariance
`ReflectedGMS.Temporal.ActualHolding.HoldingShiftCovariant`.
-/

/-! ## The selected temporal block `J_m(s)` -/

/-! ### Existence, uniqueness and nesting -/

/-! ### Cofinal rational selection parameters

The manuscript's "every root dyadic interval occurs on a nonempty parameter
interval `[κ(J), κ(J⁽¹⁾))`" and "every root dyadic interval is selected on an
interval containing a rational".
-/

/-! ## The actual holding-size inputs

The two places where the geometry of the actual holding intervals enters.
-/

/-! ## The selected temporal block from the actual holding data -/

end ReflectedGMS.Temporal.ActualDyadicTemporalBlocks
