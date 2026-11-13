/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.LabelHoldingIntervals at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedRegenerationFlow

/-!
# Holding intervals of a càdlàg label path

Section 17 of the singular-set manuscript (`work/singular/manuscript-text.txt:2039-2086`) builds its
time blocks from the **holding intervals** `[s, t)` of the label path: the maximal intervals on
which the walk sits at one vertex, "including their vertex entrance time and excluding their
departure time".  This module defines them for an arbitrary two-sided càdlàg path
`Y : CadlagPath ℕ∞` (`⊤` is the cemetery / end state, at which there is no holding interval) and
proves the pointwise facts the construction of Section 17 consumes.

* `exitLen Y s` (the residual lifetime) and `entryLen Y s` (the age) are `ℝ≥0∞`-valued infima
  over the real times at which the label differs from `Y s`; `holdLen Y s` is their sum at a vertex
  time and `0` at a cemetery time; `holdSet Y s` is the holding interval through `s`, defined
  intrinsically as the set of times `t` with `Y ≡ Y s` on the closed interval between `s` and `t`.
* `mem_holdSet_iff_of_ge` / `mem_holdSet_iff_of_le`: `holdSet Y s ∩ [s, ∞) = {t | t - s < exitLen}`
  and `holdSet Y s ∩ (-∞, s] = {t | s - t ≤ entryLen}` — right-continuity into the discrete vertex
  states makes the right end open and the left end closed; `holdSet_eq_Ico` in the finite case,
  `volume_holdSet_of_ne_top`.
* `holdSet_eq_of_mem`, `holdLen_eq_of_mem`, `endpoints_eq_of_mem`: the holding intervals partition
  the vertex times, and length and endpoints are read off at any time of the interval.
* `exists_rat_mem_holdSet_inter_Ico`: every holding interval meeting a half-open interval does so
  at a rational time (the countable reductions of Section 17 rest on this).
* `exitLen_eq_iInf_rat`, `entryLen_eq_iInf_rat`, `measurable_holdLen`: rational infima and joint
  measurability in `(Y, s)`.
* `exitLen_of_shift`, `holdLen_of_dilate`, …: covariance under `t ↦ liftLabel σ (Y (t + r))` and
  `t ↦ liftLabel σ (Y (a⁻¹ t))` for injective `σ` — the pointwise formulas of the label paths of
  `reRootFlow r ω` and `reScale C ω` (`TwoSidedRegenerationFlow.reRootFlow_label`, `reScale_label`).

Nothing here is probabilistic.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace ReflectedGMS.LabelHoldingIntervals

open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow

/-! ## 1. Right-continuity into the vertex states -/

/-- Just to the right of `u` the label keeps differing from any label `Y u` differs from
(`ℕ∞` is `T1`). -/
theorem eventually_ne_right (Y : CadlagPath ℕ∞) {u : ℝ} {n : ℕ∞} (h : Y.toFun u ≠ n) :
    ∀ᶠ v in 𝓝[≥] u, Y.toFun v ≠ n :=
  (Y.continuousWithinAt_Ici u).tendsto.eventually ((isOpen_ne (x := n)).eventually_mem h)

/-- Just to the right of a vertex time the label is constant (vertex states are isolated). -/
theorem eventually_eq_right (Y : CadlagPath ℕ∞) {u : ℝ} (h : Y.toFun u ≠ ⊤) :
    ∀ᶠ v in 𝓝[≥] u, Y.toFun v = Y.toFun u :=
  (Y.continuousWithinAt_Ici u).tendsto.eventually
    ((ENat.isOpen_singleton h).eventually_mem (Set.mem_singleton _))

/-- The `ε`-form of a right-neighbourhood statement on the real line. -/
theorem exists_pos_forall_of_eventually {u : ℝ} {p : ℝ → Prop} (h : ∀ᶠ v in 𝓝[≥] u, p v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : ℝ, u ≤ v → v < u + ε → p v := by
  obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 h
  have hu'' : u < u' := hu'
  refine ⟨u' - u, by linarith, fun v huv hv => hsub ⟨huv, by linarith⟩⟩

/-! ## 2. Residual lifetime, age, holding length, holding interval -/

/-- **The residual lifetime** at `s`: the distance to the first later time at which the label
differs from `Y s` (`∞` if there is none). -/
noncomputable def exitLen (Y : CadlagPath ℕ∞) (s : ℝ) : ℝ≥0∞ :=
  ⨅ (u : ℝ) (_ : s < u ∧ Y.toFun u ≠ Y.toFun s), ENNReal.ofReal (u - s)

/-- **The age** at `s`: the distance to the last earlier time at which the label differs from
`Y s` (`∞` if there is none). -/
noncomputable def entryLen (Y : CadlagPath ℕ∞) (s : ℝ) : ℝ≥0∞ :=
  ⨅ (u : ℝ) (_ : u < s ∧ Y.toFun u ≠ Y.toFun s), ENNReal.ofReal (s - u)

/-- **The length of the holding interval** through `s`: age plus residual lifetime at a vertex
time, `0` at a cemetery time. -/
noncomputable def holdLen (Y : CadlagPath ℕ∞) (s : ℝ) : ℝ≥0∞ :=
  if Y.toFun s = ⊤ then 0 else entryLen Y s + exitLen Y s

/-- **The holding interval** through `s`: the times `t` such that the label is constantly `Y s` on
the closed interval between `s` and `t`; empty at a cemetery time. -/
def holdSet (Y : CadlagPath ℕ∞) (s : ℝ) : Set ℝ :=
  {t | Y.toFun s ≠ ⊤ ∧ ∀ u ∈ Set.uIcc s t, Y.toFun u = Y.toFun s}

theorem exitLen_le (Y : CadlagPath ℕ∞) {s u : ℝ} (hsu : s < u) (hne : Y.toFun u ≠ Y.toFun s) :
    exitLen Y s ≤ ENNReal.ofReal (u - s) :=
  iInf₂_le u ⟨hsu, hne⟩

theorem le_exitLen (Y : CadlagPath ℕ∞) {s : ℝ} {c : ℝ≥0∞}
    (h : ∀ u : ℝ, s < u → Y.toFun u ≠ Y.toFun s → c ≤ ENNReal.ofReal (u - s)) :
    c ≤ exitLen Y s :=
  le_iInf₂ fun u hu => h u hu.1 hu.2

theorem entryLen_le (Y : CadlagPath ℕ∞) {s u : ℝ} (hus : u < s) (hne : Y.toFun u ≠ Y.toFun s) :
    entryLen Y s ≤ ENNReal.ofReal (s - u) :=
  iInf₂_le u ⟨hus, hne⟩

theorem le_entryLen (Y : CadlagPath ℕ∞) {s : ℝ} {c : ℝ≥0∞}
    (h : ∀ u : ℝ, u < s → Y.toFun u ≠ Y.toFun s → c ≤ ENNReal.ofReal (s - u)) :
    c ≤ entryLen Y s :=
  le_iInf₂ fun u hu => h u hu.1 hu.2

/-- At a vertex time the residual lifetime is positive. -/
theorem exitLen_pos (Y : CadlagPath ℕ∞) {s : ℝ} (hs : Y.toFun s ≠ ⊤) : 0 < exitLen Y s := by
  obtain ⟨ε, hε, hεv⟩ := exists_pos_forall_of_eventually (eventually_eq_right Y hs)
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε) (le_exitLen Y fun u hsu hne => ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  by_contra hlt
  push_neg at hlt
  exact hne (hεv u hsu.le (by linarith))

theorem holdLen_of_top (Y : CadlagPath ℕ∞) {s : ℝ} (hs : Y.toFun s = ⊤) : holdLen Y s = 0 :=
  if_pos hs

theorem holdLen_of_ne_top (Y : CadlagPath ℕ∞) {s : ℝ} (hs : Y.toFun s ≠ ⊤) :
    holdLen Y s = entryLen Y s + exitLen Y s :=
  if_neg hs

theorem holdLen_pos (Y : CadlagPath ℕ∞) {s : ℝ} (hs : Y.toFun s ≠ ⊤) : 0 < holdLen Y s := by
  rw [holdLen_of_ne_top Y hs]
  exact lt_of_lt_of_le (exitLen_pos Y hs) le_add_self

theorem holdLen_eq_zero_iff (Y : CadlagPath ℕ∞) (s : ℝ) : holdLen Y s = 0 ↔ Y.toFun s = ⊤ := by
  constructor
  · intro h
    by_contra hs
    exact (holdLen_pos Y hs).ne' h
  · exact holdLen_of_top Y

theorem entryLen_ne_top_of_holdLen (Y : CadlagPath ℕ∞) {s : ℝ} (hs : Y.toFun s ≠ ⊤)
    (h : holdLen Y s ≠ ∞) : entryLen Y s ≠ ∞ := by
  rw [holdLen_of_ne_top Y hs] at h
  exact (ENNReal.add_ne_top.1 h).1

theorem exitLen_ne_top_of_holdLen (Y : CadlagPath ℕ∞) {s : ℝ} (hs : Y.toFun s ≠ ⊤)
    (h : holdLen Y s ≠ ∞) : exitLen Y s ≠ ∞ := by
  rw [holdLen_of_ne_top Y hs] at h
  exact (ENNReal.add_ne_top.1 h).2

theorem holdLen_ne_top_of (Y : CadlagPath ℕ∞) {s : ℝ} (he : entryLen Y s ≠ ∞)
    (hx : exitLen Y s ≠ ∞) : holdLen Y s ≠ ∞ := by
  unfold holdLen
  split_ifs
  · exact ENNReal.zero_ne_top
  · exact ENNReal.add_ne_top.2 ⟨he, hx⟩

/-! ### The interval characterization -/

/-- **Right half**: for `t ≥ s` at a vertex time `s`, `t` lies in the holding interval iff
`t - s < exitLen Y s`. -/
theorem mem_holdSet_iff_of_ge (Y : CadlagPath ℕ∞) {s t : ℝ} (hs : Y.toFun s ≠ ⊤) (hst : s ≤ t) :
    t ∈ holdSet Y s ↔ ENNReal.ofReal (t - s) < exitLen Y s := by
  constructor
  · rintro ⟨-, hconst⟩
    have hts : Y.toFun t = Y.toFun s := hconst t Set.right_mem_uIcc
    have ht : Y.toFun t ≠ ⊤ := by
      rw [hts]
      exact hs
    obtain ⟨ε, hε, hεv⟩ := exists_pos_forall_of_eventually (eventually_eq_right Y ht)
    have hkey : ENNReal.ofReal (t - s + ε / 2) ≤ exitLen Y s := by
      refine le_exitLen Y fun u hsu hne => ENNReal.ofReal_le_ofReal ?_
      by_contra hlt
      push_neg at hlt
      have hut : t < u := by
        by_contra hle
        push_neg at hle
        exact hne (hconst u (by
          rw [Set.uIcc_of_le hst]
          exact ⟨hsu.le, hle⟩))
      exact hne (by rw [hεv u hut.le (by linarith), hts])
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)) hkey
  · intro h
    refine ⟨hs, fun u hu => ?_⟩
    rw [Set.uIcc_of_le hst] at hu
    rcases eq_or_lt_of_le hu.1 with hsu | hsu
    · rw [← hsu]
    · by_contra hne
      exact absurd (lt_of_lt_of_le h (exitLen_le Y hsu hne))
        (not_lt.2 (ENNReal.ofReal_le_ofReal (by linarith [hu.2])))

/-- **Left half**: for `t ≤ s` at a vertex time `s`, `t` lies in the holding interval iff
`s - t ≤ entryLen Y s` (the entrance time belongs to the interval). -/
theorem mem_holdSet_iff_of_le (Y : CadlagPath ℕ∞) {s t : ℝ} (hs : Y.toFun s ≠ ⊤) (hts : t ≤ s) :
    t ∈ holdSet Y s ↔ ENNReal.ofReal (s - t) ≤ entryLen Y s := by
  constructor
  · rintro ⟨-, hconst⟩
    refine le_entryLen Y fun u hus hne => ENNReal.ofReal_le_ofReal ?_
    by_contra hlt
    push_neg at hlt
    exact hne (hconst u (by
      rw [Set.uIcc_of_ge hts]
      exact ⟨by linarith, hus.le⟩))
  · intro h
    refine ⟨hs, fun u hu => ?_⟩
    rw [Set.uIcc_of_ge hts] at hu
    rcases eq_or_lt_of_le hu.2 with hus | hus
    · rw [hus]
    · rcases eq_or_lt_of_le hu.1 with htu | htu
      · rw [← htu]
        by_contra hne
        have hts' : t < s := by
          rw [htu]
          exact hus
        obtain ⟨ε, hε, hεv⟩ := exists_pos_forall_of_eventually (eventually_ne_right Y hne)
        have hmin : 0 < min ε (s - t) := lt_min hε (by linarith)
        have hv1 : t < t + min ε (s - t) / 2 := by linarith
        have hv2 : t + min ε (s - t) / 2 < s := by
          have := min_le_right ε (s - t)
          linarith
        have hv3 : t + min ε (s - t) / 2 < t + ε := by
          have := min_le_left ε (s - t)
          linarith
        have hvne : Y.toFun (t + min ε (s - t) / 2) ≠ Y.toFun s := hεv _ hv1.le hv3
        have h1 := entryLen_le Y hv2 hvne
        have h2 : ENNReal.ofReal (s - (t + min ε (s - t) / 2)) < ENNReal.ofReal (s - t) :=
          (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
        exact absurd (lt_of_le_of_lt h1 h2) (not_lt.2 h)
      · by_contra hne
        have h1 := entryLen_le Y hus hne
        have h2 : ENNReal.ofReal (s - u) < ENNReal.ofReal (s - t) :=
          (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
        exact absurd (lt_of_le_of_lt h1 h2) (not_lt.2 h)

theorem holdSet_eq_empty (Y : CadlagPath ℕ∞) {s : ℝ} (hs : Y.toFun s = ⊤) : holdSet Y s = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h => h.1 hs

theorem self_mem_holdSet (Y : CadlagPath ℕ∞) {s : ℝ} (hs : Y.toFun s ≠ ⊤) : s ∈ holdSet Y s :=
  ⟨hs, fun u hu => by
    rw [Set.uIcc_self, Set.mem_singleton_iff] at hu
    rw [hu]⟩

theorem eq_of_mem_holdSet (Y : CadlagPath ℕ∞) {s t : ℝ} (ht : t ∈ holdSet Y s) :
    Y.toFun t = Y.toFun s :=
  ht.2 t Set.right_mem_uIcc

theorem ne_top_of_mem_holdSet (Y : CadlagPath ℕ∞) {s t : ℝ} (ht : t ∈ holdSet Y s) :
    Y.toFun t ≠ ⊤ := by
  rw [eq_of_mem_holdSet Y ht]
  exact ht.1

/-- **The holding intervals partition the vertex times.** -/
theorem holdSet_eq_of_mem (Y : CadlagPath ℕ∞) {s t : ℝ} (ht : t ∈ holdSet Y s) :
    holdSet Y t = holdSet Y s := by
  have hts : Y.toFun t = Y.toFun s := eq_of_mem_holdSet Y ht
  have hs : Y.toFun s ≠ ⊤ := ht.1
  have ht' : Y.toFun t ≠ ⊤ := ne_top_of_mem_holdSet Y ht
  have hst : s ∈ holdSet Y t := ⟨ht', fun u hu => by
    rw [Set.uIcc_comm] at hu
    rw [ht.2 u hu, hts]⟩
  ext u
  constructor
  · rintro ⟨-, hu⟩
    refine ⟨hs, fun v hv => ?_⟩
    rcases Set.uIcc_subset_uIcc_union_uIcc (b := t) hv with hv' | hv'
    · exact ht.2 v hv'
    · rw [hu v hv', hts]
  · rintro ⟨-, hu⟩
    refine ⟨ht', fun v hv => ?_⟩
    rcases Set.uIcc_subset_uIcc_union_uIcc (b := s) hv with hv' | hv'
    · exact hst.2 v hv'
    · rw [hu v hv', hts]

theorem Iic_subset_holdSet (Y : CadlagPath ℕ∞) {s : ℝ} (hs : Y.toFun s ≠ ⊤)
    (h : entryLen Y s = ∞) : Set.Iic s ⊆ holdSet Y s := fun t ht =>
  (mem_holdSet_iff_of_le Y hs ht).2 (by
    rw [h]
    exact le_top)

theorem Ici_subset_holdSet (Y : CadlagPath ℕ∞) {s : ℝ} (hs : Y.toFun s ≠ ⊤)
    (h : exitLen Y s = ∞) : Set.Ici s ⊆ holdSet Y s := fun t ht =>
  (mem_holdSet_iff_of_ge Y hs ht).2 (by
    rw [h]
    exact ENNReal.ofReal_lt_top)

/-- **The holding interval is `[s - age, s + residual)`** when both are finite. -/
theorem holdSet_eq_Ico (Y : CadlagPath ℕ∞) {s : ℝ} (hs : Y.toFun s ≠ ⊤)
    (he : entryLen Y s ≠ ∞) (hx : exitLen Y s ≠ ∞) :
    holdSet Y s = Set.Ico (s - (entryLen Y s).toReal) (s + (exitLen Y s).toReal) := by
  have hxpos : 0 < (exitLen Y s).toReal := ENNReal.toReal_pos (exitLen_pos Y hs).ne' hx
  have henn : 0 ≤ (entryLen Y s).toReal := ENNReal.toReal_nonneg
  ext t
  rcases le_or_gt t s with hts | hst
  · rw [mem_holdSet_iff_of_le Y hs hts, ENNReal.ofReal_le_iff_le_toReal he, Set.mem_Ico]
    constructor
    · intro h
      exact ⟨by linarith, by linarith⟩
    · intro h
      linarith [h.1]
  · rw [mem_holdSet_iff_of_ge Y hs hst.le, ENNReal.ofReal_lt_iff_lt_toReal (by linarith) hx,
      Set.mem_Ico]
    constructor
    · intro h
      exact ⟨by linarith, by linarith⟩
    · intro h
      linarith [h.2]

/-- The length of a bounded holding interval is `holdLen`. -/
theorem volume_holdSet_of_ne_top (Y : CadlagPath ℕ∞) {s : ℝ} (hs : Y.toFun s ≠ ⊤)
    (he : entryLen Y s ≠ ∞) (hx : exitLen Y s ≠ ∞) : volume (holdSet Y s) = holdLen Y s := by
  rw [holdSet_eq_Ico Y hs he hx, Real.volume_Ico, holdLen_of_ne_top Y hs]
  have h1 : s + (exitLen Y s).toReal - (s - (entryLen Y s).toReal)
      = (entryLen Y s).toReal + (exitLen Y s).toReal := by ring
  rw [h1, ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal he, ENNReal.ofReal_toReal hx]

/-- The holding interval as a union of its two halves (at a vertex time). -/
theorem holdSet_eq_union (Y : CadlagPath ℕ∞) {s : ℝ} (hs : Y.toFun s ≠ ⊤) :
    holdSet Y s = (Set.Iic s ∩ {t | ENNReal.ofReal (s - t) ≤ entryLen Y s})
      ∪ (Set.Ici s ∩ {t | ENNReal.ofReal (t - s) < exitLen Y s}) := by
  ext t
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici, Set.mem_ofPred_eq]
  rcases le_or_gt t s with hts | hst
  · rw [mem_holdSet_iff_of_le Y hs hts]
    constructor
    · intro h
      exact Or.inl ⟨hts, h⟩
    · rintro (h | h)
      · exact h.2
      · have hts' : t = s := le_antisymm hts h.1
        rw [hts', sub_self, ENNReal.ofReal_zero]
        exact zero_le
  · rw [mem_holdSet_iff_of_ge Y hs hst.le]
    constructor
    · intro h
      exact Or.inr ⟨hst.le, h⟩
    · rintro (h | h)
      · exact absurd (lt_of_lt_of_le hst h.1) (lt_irrefl _)
      · exact h.2

theorem measurableSet_holdSet (Y : CadlagPath ℕ∞) (s : ℝ) : MeasurableSet (holdSet Y s) := by
  by_cases hs : Y.toFun s = ⊤
  · rw [holdSet_eq_empty Y hs]
    exact MeasurableSet.empty
  · rw [holdSet_eq_union Y hs]
    refine MeasurableSet.union (measurableSet_Iic.inter ?_) (measurableSet_Ici.inter ?_)
    · exact measurableSet_le ((continuous_const.sub continuous_id).measurable.ennreal_ofReal)
        measurable_const
    · exact measurableSet_lt ((continuous_id.sub continuous_const).measurable.ennreal_ofReal)
        measurable_const

/-- On a bounded holding interval the endpoints and the length are read off at any of its
times. -/
theorem endpoints_eq_of_mem (Y : CadlagPath ℕ∞) {s t : ℝ} (ht : t ∈ holdSet Y s)
    (hlen : holdLen Y s ≠ ∞) :
    t - (entryLen Y t).toReal = s - (entryLen Y s).toReal ∧
      t + (exitLen Y t).toReal = s + (exitLen Y s).toReal ∧ holdLen Y t = holdLen Y s := by
  have hs : Y.toFun s ≠ ⊤ := ht.1
  have ht' : Y.toFun t ≠ ⊤ := ne_top_of_mem_holdSet Y ht
  have he := entryLen_ne_top_of_holdLen Y hs hlen
  have hx := exitLen_ne_top_of_holdLen Y hs hlen
  have hset := holdSet_eq_of_mem Y ht
  have he' : entryLen Y t ≠ ∞ := by
    intro h
    have hsub := Iic_subset_holdSet Y ht' h
    rw [hset, holdSet_eq_Ico Y hs he hx] at hsub
    have hmem := hsub (Set.mem_Iic.2 (show min t (s - (entryLen Y s).toReal) - 1 ≤ t by
      linarith [min_le_left t (s - (entryLen Y s).toReal)]))
    linarith [hmem.1, min_le_right t (s - (entryLen Y s).toReal)]
  have hx' : exitLen Y t ≠ ∞ := by
    intro h
    have hsub := Ici_subset_holdSet Y ht' h
    rw [hset, holdSet_eq_Ico Y hs he hx] at hsub
    have hmem := hsub (Set.mem_Ici.2 (le_max_left t (s + (exitLen Y s).toReal)))
    linarith [hmem.2, le_max_right t (s + (exitLen Y s).toReal)]
  have hIco : Set.Ico (t - (entryLen Y t).toReal) (t + (exitLen Y t).toReal)
      = Set.Ico (s - (entryLen Y s).toReal) (s + (exitLen Y s).toReal) := by
    rw [← holdSet_eq_Ico Y ht' he' hx', ← holdSet_eq_Ico Y hs he hx, hset]
  have hne : t - (entryLen Y t).toReal < t + (exitLen Y t).toReal := by
    have := ENNReal.toReal_pos (exitLen_pos Y ht').ne' hx'
    linarith [(ENNReal.toReal_nonneg : 0 ≤ (entryLen Y t).toReal)]
  obtain ⟨h1, h2⟩ := (Set.Ico_eq_Ico_iff (Or.inl hne)).1 hIco
  refine ⟨h1, h2, ?_⟩
  rw [holdLen_of_ne_top Y ht', holdLen_of_ne_top Y hs]
  have h3 : (entryLen Y t).toReal + (exitLen Y t).toReal
      = (entryLen Y s).toReal + (exitLen Y s).toReal := by linarith
  have h4 := congrArg ENNReal.ofReal h3
  rwa [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal he',
    ENNReal.ofReal_toReal hx', ENNReal.ofReal_toReal he, ENNReal.ofReal_toReal hx] at h4

/-- The length of the holding interval is constant along it (bounded or not). -/
theorem holdLen_eq_of_mem (Y : CadlagPath ℕ∞) {s t : ℝ} (ht : t ∈ holdSet Y s) :
    holdLen Y t = holdLen Y s := by
  by_cases hlen : holdLen Y s = ∞
  · rw [hlen]
    by_contra hne
    have hs : Y.toFun s ≠ ⊤ := ht.1
    have ht' : Y.toFun t ≠ ⊤ := ne_top_of_mem_holdSet Y ht
    have he' := entryLen_ne_top_of_holdLen Y ht' hne
    have hx' := exitLen_ne_top_of_holdLen Y ht' hne
    have hset := holdSet_eq_of_mem Y ht
    rw [holdLen_of_ne_top Y hs, ENNReal.add_eq_top] at hlen
    rcases hlen with he | hx
    · have hsub := Iic_subset_holdSet Y hs he
      rw [← hset, holdSet_eq_Ico Y ht' he' hx'] at hsub
      have hmem := hsub (Set.mem_Iic.2 (show min s (t - (entryLen Y t).toReal) - 1 ≤ s by
        linarith [min_le_left s (t - (entryLen Y t).toReal)]))
      linarith [hmem.1, min_le_right s (t - (entryLen Y t).toReal)]
    · have hsub := Ici_subset_holdSet Y hs hx
      rw [← hset, holdSet_eq_Ico Y ht' he' hx'] at hsub
      have hmem := hsub (Set.mem_Ici.2 (le_max_left s (t + (exitLen Y t).toReal)))
      linarith [hmem.2, le_max_right s (t + (exitLen Y t).toReal)]
  · exact (endpoints_eq_of_mem Y ht hlen).2.2

/-! ### Rational times in holding intervals -/

/-- An initial segment `[s, s + δ)` of the holding interval through a vertex time. -/
theorem exists_Ico_subset_holdSet (Y : CadlagPath ℕ∞) {s : ℝ} (hs : Y.toFun s ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ Set.Ico s (s + δ) ⊆ holdSet Y s := by
  obtain ⟨ε, hε, hεv⟩ := exists_pos_forall_of_eventually (eventually_eq_right Y hs)
  refine ⟨ε, hε, fun t ht => ⟨hs, fun u hu => ?_⟩⟩
  rw [Set.uIcc_of_le ht.1] at hu
  exact hεv u hu.1 (by linarith [hu.2, ht.2])

/-- Every vertex time `u` of a half-open interval `[c, d)` shares its holding interval with a
rational time of `[c, d)`. -/
theorem exists_rat_mem_holdSet_inter_Ico (Y : CadlagPath ℕ∞) {u c d : ℝ} (hu : Y.toFun u ≠ ⊤)
    (huJ : u ∈ Set.Ico c d) :
    ∃ q : ℚ, (q : ℝ) ∈ Set.Ico c d ∧ (q : ℝ) ∈ holdSet Y u := by
  obtain ⟨δ, hδ, hsub⟩ := exists_Ico_subset_holdSet Y hu
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u < min (u + δ) d from lt_min (by linarith) huJ.2)
  exact ⟨q, ⟨le_trans huJ.1 hq1.le, lt_of_lt_of_le hq2 (min_le_right _ _)⟩,
    hsub ⟨hq1.le, lt_of_lt_of_le hq2 (min_le_left _ _)⟩⟩

/-- Every vertex time shares its holding interval with a rational time. -/
theorem exists_rat_mem_holdSet (Y : CadlagPath ℕ∞) {u : ℝ} (hu : Y.toFun u ≠ ⊤) :
    ∃ q : ℚ, (q : ℝ) ∈ holdSet Y u := by
  obtain ⟨q, -, hq⟩ := exists_rat_mem_holdSet_inter_Ico Y hu (show u ∈ Set.Ico u (u + 1) from
    ⟨le_rfl, by linarith⟩)
  exact ⟨q, hq⟩

/-! ## 3. Rational infima and joint measurability -/

theorem exitLen_eq_iInf_rat (Y : CadlagPath ℕ∞) (s : ℝ) :
    exitLen Y s = ⨅ (q : ℚ) (_ : s < q ∧ Y.toFun q ≠ Y.toFun s), ENNReal.ofReal (q - s) := by
  refine le_antisymm (le_iInf₂ fun q hq => exitLen_le Y hq.1 hq.2)
    (le_exitLen Y fun u hsu hne => ?_)
  obtain ⟨ε, hε, hεv⟩ := exists_pos_forall_of_eventually (eventually_ne_right Y hne)
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hδ' : (0 : ℝ) < δ := NNReal.coe_pos.2 hδ
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u < u + min ε (δ : ℝ) from by
    have := lt_min hε hδ'
    linarith)
  have hqε : (q : ℝ) < u + ε := lt_of_lt_of_le hq2 (by linarith [min_le_left ε (δ : ℝ)])
  have hqδ : (q : ℝ) - s ≤ u - s + δ := by linarith [min_le_right ε (δ : ℝ)]
  calc (⨅ (q : ℚ) (_ : s < q ∧ Y.toFun q ≠ Y.toFun s), ENNReal.ofReal (q - s))
      ≤ ENNReal.ofReal (q - s) := iInf₂_le q ⟨by linarith, hεv q hq1.le hqε⟩
    _ ≤ ENNReal.ofReal (u - s + δ) := ENNReal.ofReal_le_ofReal hqδ
    _ = ENNReal.ofReal (u - s) + δ := by
        rw [ENNReal.ofReal_add (by linarith) hδ'.le, ENNReal.ofReal_coe_nnreal]

theorem entryLen_eq_iInf_rat (Y : CadlagPath ℕ∞) (s : ℝ) :
    entryLen Y s = ⨅ (q : ℚ) (_ : q < s ∧ Y.toFun q ≠ Y.toFun s), ENNReal.ofReal (s - q) := by
  refine le_antisymm (le_iInf₂ fun q hq => entryLen_le Y hq.1 hq.2)
    (le_entryLen Y fun u hus hne => ?_)
  obtain ⟨ε, hε, hεv⟩ := exists_pos_forall_of_eventually (eventually_ne_right Y hne)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u < min (u + ε) s from lt_min (by linarith) hus)
  have hqε : (q : ℝ) < u + ε := lt_of_lt_of_le hq2 (min_le_left _ _)
  have hqs : (q : ℝ) < s := lt_of_lt_of_le hq2 (min_le_right _ _)
  calc (⨅ (q : ℚ) (_ : q < s ∧ Y.toFun q ≠ Y.toFun s), ENNReal.ofReal (s - q))
      ≤ ENNReal.ofReal (s - q) := iInf₂_le q ⟨hqs, hεv q hq1.le hqε⟩
    _ ≤ ENNReal.ofReal (s - u) := ENNReal.ofReal_le_ofReal (by linarith)

theorem measurable_evalRat (q : ℚ) :
    Measurable fun p : CadlagPath ℕ∞ × ℝ => p.1.toFun q :=
  (CadlagPath.measurable_eval (q : ℝ)).comp measurable_fst

theorem measurable_evalSnd : Measurable fun p : CadlagPath ℕ∞ × ℝ => p.1.toFun p.2 :=
  CadlagPath.measurable_eval_uncurry

theorem measurableSet_ne_evalRat (q : ℚ) :
    MeasurableSet {p : CadlagPath ℕ∞ × ℝ | p.1.toFun q ≠ p.1.toFun p.2} :=
  (measurableSet_eq_fun (measurable_evalRat q) measurable_evalSnd).compl

open Classical in
theorem measurable_exitLen : Measurable fun p : CadlagPath ℕ∞ × ℝ => exitLen p.1 p.2 := by
  have hEq : (fun p : CadlagPath ℕ∞ × ℝ => exitLen p.1 p.2) = fun p =>
      ⨅ q : ℚ, if p.2 < (q : ℝ) ∧ p.1.toFun q ≠ p.1.toFun p.2 then ENNReal.ofReal ((q : ℝ) - p.2)
        else ⊤ := by
    funext p
    rw [exitLen_eq_iInf_rat]
    refine iInf_congr fun q => ?_
    by_cases hq : p.2 < (q : ℝ) ∧ p.1.toFun q ≠ p.1.toFun p.2
    · rw [if_pos hq]
      exact iInf_pos hq
    · rw [if_neg hq]
      exact iInf_neg hq
  rw [hEq]
  refine Measurable.iInf fun q => Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_snd measurable_const).inter (measurableSet_ne_evalRat q)
  · exact (measurable_const.sub measurable_snd).ennreal_ofReal

open Classical in
theorem measurable_entryLen : Measurable fun p : CadlagPath ℕ∞ × ℝ => entryLen p.1 p.2 := by
  have hEq : (fun p : CadlagPath ℕ∞ × ℝ => entryLen p.1 p.2) = fun p =>
      ⨅ q : ℚ, if (q : ℝ) < p.2 ∧ p.1.toFun q ≠ p.1.toFun p.2 then ENNReal.ofReal (p.2 - (q : ℝ))
        else ⊤ := by
    funext p
    rw [entryLen_eq_iInf_rat]
    refine iInf_congr fun q => ?_
    by_cases hq : (q : ℝ) < p.2 ∧ p.1.toFun q ≠ p.1.toFun p.2
    · rw [if_pos hq]
      exact iInf_pos hq
    · rw [if_neg hq]
      exact iInf_neg hq
  rw [hEq]
  refine Measurable.iInf fun q => Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_const measurable_snd).inter (measurableSet_ne_evalRat q)
  · exact (measurable_snd.sub measurable_const).ennreal_ofReal

theorem measurableSet_evalSnd_top :
    MeasurableSet {p : CadlagPath ℕ∞ × ℝ | p.1.toFun p.2 = ⊤} :=
  measurable_evalSnd (measurableSet_singleton ⊤)

theorem measurable_holdLen : Measurable fun p : CadlagPath ℕ∞ × ℝ => holdLen p.1 p.2 := by
  have hEq : (fun p : CadlagPath ℕ∞ × ℝ => holdLen p.1 p.2) = fun p =>
      if p.1.toFun p.2 = ⊤ then 0 else entryLen p.1 p.2 + exitLen p.1 p.2 := rfl
  rw [hEq]
  exact Measurable.ite measurableSet_evalSnd_top measurable_const
    (measurable_entryLen.add measurable_exitLen)

/-! ## 4. Covariance under the label-path formulas of the flow and the scaling -/

theorem liftLabel_injective {σ : ℕ → ℕ} (hσ : Function.Injective σ) :
    Function.Injective (liftLabel σ) := by
  intro x y hxy
  induction x using ENat.recTopCoe with
  | top =>
    induction y using ENat.recTopCoe with
    | top => rfl
    | coe n =>
      rw [liftLabel_top, liftLabel_natCast] at hxy
      exact absurd hxy.symm (ENat.natCast_ne_top _)
  | coe m =>
    induction y using ENat.recTopCoe with
    | top =>
      rw [liftLabel_top, liftLabel_natCast] at hxy
      exact absurd hxy (ENat.natCast_ne_top _)
    | coe n =>
      rw [liftLabel_natCast, liftLabel_natCast] at hxy
      have hmn : σ m = σ n := by exact_mod_cast hxy
      rw [hσ hmn]

theorem liftLabel_eq_top_iff (σ : ℕ → ℕ) (x : ℕ∞) : liftLabel σ x = ⊤ ↔ x = ⊤ := by
  induction x using ENat.recTopCoe with
  | top => simp
  | coe n => simp

section Covariance

variable {Y Y' : CadlagPath ℕ∞} {σ : ℕ → ℕ}

/-- Shift-and-relabel covariance of the residual lifetime, for a path `Y'` given pointwise by
`Y' t = liftLabel σ (Y (t + r))` (the label path of `reRootFlow r ω`). -/
theorem exitLen_of_shift (hσ : Function.Injective σ) {r : ℝ}
    (hY' : ∀ t : ℝ, Y'.toFun t = liftLabel σ (Y.toFun (t + r))) (s : ℝ) :
    exitLen Y' s = exitLen Y (s + r) := by
  unfold exitLen
  simp only [hY', (liftLabel_injective hσ).ne_iff]
  refine le_antisymm (le_iInf₂ fun u hu => ?_) (le_iInf₂ fun u hu => ?_)
  · refine iInf₂_le_of_le (u - r) ⟨by linarith [hu.1], by
      rw [sub_add_cancel]
      exact hu.2⟩ ?_
    rw [show u - r - s = u - (s + r) by ring]
  · refine iInf₂_le_of_le (u + r) ⟨by linarith [hu.1], hu.2⟩ ?_
    rw [show u + r - (s + r) = u - s by ring]

theorem entryLen_of_shift (hσ : Function.Injective σ) {r : ℝ}
    (hY' : ∀ t : ℝ, Y'.toFun t = liftLabel σ (Y.toFun (t + r))) (s : ℝ) :
    entryLen Y' s = entryLen Y (s + r) := by
  unfold entryLen
  simp only [hY', (liftLabel_injective hσ).ne_iff]
  refine le_antisymm (le_iInf₂ fun u hu => ?_) (le_iInf₂ fun u hu => ?_)
  · refine iInf₂_le_of_le (u - r) ⟨by linarith [hu.1], by
      rw [sub_add_cancel]
      exact hu.2⟩ ?_
    rw [show s - (u - r) = s + r - u by ring]
  · refine iInf₂_le_of_le (u + r) ⟨by linarith [hu.1], hu.2⟩ ?_
    rw [show s + r - (u + r) = s - u by ring]

theorem holdLen_of_shift (hσ : Function.Injective σ) {r : ℝ}
    (hY' : ∀ t : ℝ, Y'.toFun t = liftLabel σ (Y.toFun (t + r))) (s : ℝ) :
    holdLen Y' s = holdLen Y (s + r) := by
  simp only [holdLen, hY' s, liftLabel_eq_top_iff, entryLen_of_shift hσ hY' s,
    exitLen_of_shift hσ hY' s]

/-- Dilation-and-relabel covariance of the residual lifetime, for a path `Y'` given pointwise by
`Y' t = liftLabel σ (Y (a⁻¹ t))` (the label path of `reScale C ω`, with `a = C²`). -/
theorem exitLen_of_dilate (hσ : Function.Injective σ) {a : ℝ} (ha : 0 < a)
    (hY' : ∀ t : ℝ, Y'.toFun t = liftLabel σ (Y.toFun (a⁻¹ * t))) (s : ℝ) :
    exitLen Y' (a * s) = ENNReal.ofReal a * exitLen Y s := by
  have h0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.2 ha).ne'
  unfold exitLen
  simp only [hY', (liftLabel_injective hσ).ne_iff, inv_mul_cancel_left₀ ha.ne']
  simp_rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_antisymm (le_iInf₂ fun v hv => ?_) (le_iInf₂ fun u hu => ?_)
  · refine iInf₂_le_of_le (a * v)
      ⟨mul_lt_mul_of_pos_left hv.1 ha, by
        rw [inv_mul_cancel_left₀ ha.ne']
        exact hv.2⟩ ?_
    rw [← mul_sub, ENNReal.ofReal_mul ha.le]
  · refine iInf₂_le_of_le (a⁻¹ * u) ⟨?_, hu.2⟩ ?_
    · have h := mul_lt_mul_of_pos_left hu.1 (inv_pos.2 ha)
      rwa [inv_mul_cancel_left₀ ha.ne'] at h
    · rw [← ENNReal.ofReal_mul ha.le, mul_sub, mul_inv_cancel_left₀ ha.ne']

theorem entryLen_of_dilate (hσ : Function.Injective σ) {a : ℝ} (ha : 0 < a)
    (hY' : ∀ t : ℝ, Y'.toFun t = liftLabel σ (Y.toFun (a⁻¹ * t))) (s : ℝ) :
    entryLen Y' (a * s) = ENNReal.ofReal a * entryLen Y s := by
  have h0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.2 ha).ne'
  unfold entryLen
  simp only [hY', (liftLabel_injective hσ).ne_iff, inv_mul_cancel_left₀ ha.ne']
  simp_rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_antisymm (le_iInf₂ fun v hv => ?_) (le_iInf₂ fun u hu => ?_)
  · refine iInf₂_le_of_le (a * v)
      ⟨mul_lt_mul_of_pos_left hv.1 ha, by
        rw [inv_mul_cancel_left₀ ha.ne']
        exact hv.2⟩ ?_
    rw [← mul_sub, ENNReal.ofReal_mul ha.le]
  · refine iInf₂_le_of_le (a⁻¹ * u) ⟨?_, hu.2⟩ ?_
    · have h := mul_lt_mul_of_pos_left hu.1 (inv_pos.2 ha)
      rwa [inv_mul_cancel_left₀ ha.ne'] at h
    · rw [← ENNReal.ofReal_mul ha.le, mul_sub, mul_inv_cancel_left₀ ha.ne']

theorem holdLen_of_dilate (hσ : Function.Injective σ) {a : ℝ} (ha : 0 < a)
    (hY' : ∀ t : ℝ, Y'.toFun t = liftLabel σ (Y.toFun (a⁻¹ * t))) (s : ℝ) :
    holdLen Y' (a * s) = ENNReal.ofReal a * holdLen Y s := by
  simp only [holdLen, hY' (a * s), inv_mul_cancel_left₀ ha.ne', liftLabel_eq_top_iff,
    entryLen_of_dilate hσ ha hY' s, exitLen_of_dilate hσ ha hY' s]
  split_ifs
  · rw [mul_zero]
  · rw [mul_add]

end Covariance

end ReflectedGMS.LabelHoldingIntervals

#print axioms ReflectedGMS.LabelHoldingIntervals.mem_holdSet_iff_of_ge
#print axioms ReflectedGMS.LabelHoldingIntervals.mem_holdSet_iff_of_le
#print axioms ReflectedGMS.LabelHoldingIntervals.holdSet_eq_of_mem
#print axioms ReflectedGMS.LabelHoldingIntervals.holdSet_eq_Ico
#print axioms ReflectedGMS.LabelHoldingIntervals.endpoints_eq_of_mem
#print axioms ReflectedGMS.LabelHoldingIntervals.holdLen_eq_of_mem
#print axioms ReflectedGMS.LabelHoldingIntervals.exists_rat_mem_holdSet_inter_Ico
#print axioms ReflectedGMS.LabelHoldingIntervals.measurable_holdLen
#print axioms ReflectedGMS.LabelHoldingIntervals.measurableSet_holdSet
#print axioms ReflectedGMS.LabelHoldingIntervals.holdLen_of_shift
#print axioms ReflectedGMS.LabelHoldingIntervals.holdLen_of_dilate
