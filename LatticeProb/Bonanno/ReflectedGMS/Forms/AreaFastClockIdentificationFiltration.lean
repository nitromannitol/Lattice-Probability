/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.AreaFastClockIdentificationFiltration at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.AreaFastClockIdentificationPath
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedAdaptedness
import LatticeProb.Bonanno.ReflectedGMS.Limit.BoundedStopping
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedFormAssociationCompletedMartingale
import LatticeProb.Bonanno.ReflectedGMS.InvarianceMainStatement

/-!
# Step (c) of bracket atom 1: the area filtration sits inside the time-changed fast filtration

The clock change `StoppedFormAssociation.martingale_stoppedValue_clock_of_bound_of_ae` turns a
martingale `N` of the completed fast filtration `𝔽` into the martingale `t ↦ N_{h t}` of a
filtration `𝔾` as soon as every event of `𝔾_t` is (up to null sets) an event of the stopped
σ-algebra `𝔽_{h t}`.  This file proves the **exact** inclusion

`areaFiltration t ≤ 𝔽_{h t}`,  `h = AreaFastClockStopping.fastClock` (the patched inverse area clock),

so the consumer's `hG` binder holds with `B' = B`.

## Route

`areaFiltration t = ⋂_{u > t} (σ(X^{area}_s : s ≤ u) ∨ null events)`.

1. **Generators.**  For `s ≤ u`, `X^{area}_s` is `𝔽_{h u}`-measurable.  On the good event
   (`AreaFastClockPath.ae_clockGood_and_path_eq`), `X^{area}_s = Y_{h s}`, and on
   `{h u ≤ v}` one has `h s = min(h s, v)`; the stopped value of the fast path at the bounded
   stopping time `min(h s, v)` is `𝔽_v`-measurable.  The fast path is **not** right continuous
   at its `none` times, so the checked `MartingaleLimit.stronglyMeasurable_stoppedValue_of_ae_rightContinuous`
   does not apply; its grid argument needs right continuity only *at the stopping time*, which
   holds almost surely because `X^{area}_s` and `Y_v` are vertices at the fixed times `s`, `v`
   (property (ii)) and the path is right-constant at vertex times (property (iii)).
   That pointwise variant is `stronglyMeasurable_stoppedValue_of_ae_continuousWithinAt`.
2. **Null events** lie in every stopped σ-algebra of the completed filtration.
3. **Right continuity of `t ↦ 𝔽_{h t}`** (`measurableSet_stopped_of_forall_gt`): `𝔽` is right
   continuous and the patched clock is continuous and monotone in `t` *for every sample*
   (on the good event it is an order isomorphism, off it the identity), so
   `⋂_{u > t} 𝔽_{h u} ⊆ 𝔽_{h t}`.  Mathlib has no such lemma for stopped σ-algebras.

Nothing here uses summability of a speed measure beyond the canonical fast rate, and no
`HasFiniteEnergy` hypothesis occurs.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.AreaFastClockFiltration

open ReflectedWalk ReflectedWalk.IndexSet ReflectedWalk.Theorem16
open ReflectedGMS.ProcessFiltration ReflectedGMS.MartingaleLimit
open ReflectedGMS.AreaClockLocalFiniteness ReflectedGMS.AreaTimeChangeJumpLaw
open ReflectedGMS.AreaFastClockStopping ReflectedGMS.AreaFastClockPath
open ReflectedGMS.AreaClockFastSpeedOccupation
open StatementIngredients AreaClocks

universe u

/-! ## Stopped values at a point of right continuity -/

section StoppedValue

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- `MartingaleLimit.boundedGridApprox_stoppedValue_tendsto` with right continuity required only
at the stopping time itself. -/
theorem boundedGridApprox_stoppedValue_tendsto_of_continuousWithinAt
    {E : Type*} [TopologicalSpace E] (X : ℝ≥0 → Ω → E)
    {τ : Ω → WithTop ℝ≥0} (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) (ω : Ω)
    (hr : ContinuousWithinAt (fun t => X t ω) (Ioi (τ ω).untopA) (τ ω).untopA) :
    Tendsto (fun n => stoppedValue X (boundedGridApprox τ T n) ω)
      atTop (𝓝 (stoppedValue X τ ω)) := by
  have hne : τ ω ≠ ⊤ := (lt_of_le_of_lt (hτT ω) (WithTop.coe_lt_top T)).ne
  have htime : Tendsto (fun n => (boundedGridApprox τ T n ω).untopA)
      atTop (𝓝[≥] (τ ω).untopA) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (WithTop.tendsto_untopA hne).comp
        (tendsto_nhds_of_tendsto_nhdsWithin (boundedGridApprox_tendsto_right T hτT ω))
    · exact Eventually.of_forall fun n => by
        have hn : boundedGridApprox τ T n ω ≠ ⊤ :=
          (lt_of_le_of_lt (boundedGridApprox_bounds T hτT n ω).2 (WithTop.coe_lt_top T)).ne
        exact WithTop.untopA_mono hn (boundedGridApprox_bounds T hτT n ω).1
  exact Filter.Tendsto.comp (continuousWithinAt_Ioi_iff_Ici.mp hr) htime

/-- **Horizon measurability of a stopped value, with right continuity only at the stopping
time.**  The pointwise form of
`MartingaleLimit.stronglyMeasurable_stoppedValue_of_ae_rightContinuous`. -/
theorem stronglyMeasurable_stoppedValue_of_ae_continuousWithinAt
    {P : Measure Ω} {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : StronglyAdapted F M) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hnull : ∀ A : Set Ω, P A = 0 → MeasurableSet[F T] A)
    (hr : ∀ᵐ ω ∂P, ContinuousWithinAt (fun t => M t ω) (Ioi (τ ω).untopA) (τ ω).untopA) :
    StronglyMeasurable[F T] (stoppedValue M τ) := by
  apply stronglyMeasurable_limit_of_null_events (P := P) (F.le T) hnull
    (f := fun n => stoppedValue M (boundedGridApprox τ T n))
  · intro n
    exact stronglyMeasurable_stoppedValue_of_finite_range hM
      (isStoppingTime_boundedGridApprox hτ T hτT n)
      (finite_range_boundedGridApprox T hτT n) T
      (fun ω => (boundedGridApprox_bounds T hτT n ω).2)
  · exact hr.mono fun ω hω =>
      boundedGridApprox_stoppedValue_tendsto_of_continuousWithinAt M T hτT ω hω

/-- A function right-constant at `a` is right continuous at `a`. -/
theorem continuousWithinAt_Ioi_of_eqOn_Ico {E : Type*} [TopologicalSpace E]
    {f : ℝ≥0 → E} {a ε : ℝ≥0} (hε : 0 < ε) (h : ∀ r ∈ Ico a (a + ε), f r = f a) :
    ContinuousWithinAt f (Ioi a) a := by
  have hev : (fun _ : ℝ≥0 => f a) =ᶠ[𝓝[>] a] f := by
    filter_upwards [Ioo_mem_nhdsGT (lt_add_of_pos_right a hε)] with r hr
    exact (h r ⟨hr.1.le, hr.2⟩).symm
  exact tendsto_const_nhds.congr' hev

end StoppedValue

/-! ## Stopped σ-algebras of finite stopping times -/

section StoppedSigma

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A set whose sections `s ∩ {τ ≤ i}` are all `𝔽_i`-measurable lies in the stopped σ-algebra
of a finite stopping time (the `⨆ 𝔽_t` clause is automatic). -/
theorem measurableSet_stopped_of_forall {f : Filtration ℝ≥0 m} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime f τ) (hfin : ∀ ω, τ ω ≠ ⊤) {s : Set Ω}
    (hs : ∀ i : ℝ≥0, MeasurableSet[f i] (s ∩ {ω | τ ω ≤ (i : WithTop ℝ≥0)})) :
    MeasurableSet[hτ.measurableSpace] s := by
  refine ⟨?_, hs⟩
  have heq : s = ⋃ n : ℕ, (s ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro hω
      obtain ⟨n, hn⟩ := exists_nat_ge ((τ ω).untop (hfin ω))
      refine ⟨n, hω, ?_⟩
      rw [← WithTop.coe_untop (τ ω) (hfin ω)]
      exact WithTop.coe_le_coe.2 hn
    · rintro ⟨n, hω, -⟩
      exact hω
  rw [heq]
  exact MeasurableSet.iUnion fun n => (le_iSup (fun t => f t) (n : ℝ≥0)) _ (hs n)

/-- **Right continuity of the stopped σ-algebras along a continuous clock.**  For a right
continuous filtration and a family of finite stopping times `h t = g t` with `t ↦ g t ω`
monotone and continuous for every sample, `⋂_{u > t} 𝔽_{h u} ⊆ 𝔽_{h t}`. -/
theorem measurableSet_stopped_of_forall_gt {f : Filtration ℝ≥0 m}
    (hrc : ∀ (v : ℝ≥0) (S : Set Ω), (∀ j > v, MeasurableSet[f j] S) → MeasurableSet[f v] S)
    {h : ℝ≥0 → Ω → WithTop ℝ≥0} (hh : ∀ t, IsStoppingTime f (h t))
    {g : ℝ≥0 → Ω → ℝ≥0} (hg : ∀ t ω, h t ω = ((g t ω : ℝ≥0) : WithTop ℝ≥0))
    (hmono : ∀ ω, Monotone (fun t => g t ω)) (hcont : ∀ ω, Continuous (fun t => g t ω))
    (t : ℝ≥0) {B : Set Ω} (hB : ∀ u > t, MeasurableSet[(hh u).measurableSpace] B) :
    MeasurableSet[(hh t).measurableSpace] B := by
  refine measurableSet_stopped_of_forall (hh t)
    (fun ω => by rw [hg]; exact WithTop.coe_ne_top) fun v => ?_
  refine hrc v _ fun j hvj => ?_
  -- levels decreasing to `v` from above, below `j`
  have hcv : ∀ k : ℕ, v < v + (j - v) * (1 / ((k : ℝ≥0) + 1)) := fun k =>
    lt_add_of_pos_right v (mul_pos (tsub_pos_of_lt hvj) (by positivity))
  have hcj : ∀ k : ℕ, v + (j - v) * (1 / ((k : ℝ≥0) + 1)) ≤ j := by
    intro k
    have h1 : (1 : ℝ≥0) / ((k : ℝ≥0) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact le_add_of_nonneg_left zero_le
    calc v + (j - v) * (1 / ((k : ℝ≥0) + 1)) ≤ v + (j - v) :=
          add_le_add le_rfl (mul_le_of_le_one_right zero_le h1)
      _ = j := add_tsub_cancel_of_le hvj.le
  have hclim : Tendsto (fun k : ℕ => v + (j - v) * (1 / ((k : ℝ≥0) + 1))) atTop (𝓝 v) := by
    have h1 : Tendsto (fun k : ℕ => (1 : ℝ≥0) / ((k : ℝ≥0) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero, add_zero] using (h1.const_mul (j - v)).const_add v
  -- times decreasing to `t` from above
  have hut : ∀ n : ℕ, t < t + 1 / ((n : ℝ≥0) + 1) := fun n =>
    lt_add_of_pos_right t (by positivity)
  have hulim : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 t) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := t)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  have hset : B ∩ {ω | h t ω ≤ ((v : ℝ≥0) : WithTop ℝ≥0)} =
      ⋂ k : ℕ, ⋃ n : ℕ, (B ∩ {ω | h (t + 1 / ((n : ℝ≥0) + 1)) ω ≤
        ((v + (j - v) * (1 / ((k : ℝ≥0) + 1)) : ℝ≥0) : WithTop ℝ≥0)}) := by
    ext ω
    simp only [mem_inter_iff, mem_setOf_eq, mem_iInter, mem_iUnion, hg, WithTop.coe_le_coe]
    constructor
    · rintro ⟨hωB, hle⟩ k
      obtain ⟨n, hn⟩ := (((hcont ω).tendsto t).comp hulim).eventually_lt_const
        (lt_of_le_of_lt hle (hcv k)) |>.exists
      exact ⟨n, hωB, hn.le⟩
    · intro hall
      obtain ⟨n, hωB, -⟩ := hall 0
      refine ⟨hωB, ge_of_tendsto' hclim fun k => ?_⟩
      obtain ⟨n, -, hn⟩ := hall k
      exact (hmono ω (hut n).le).trans hn
  show MeasurableSet[f j] (B ∩ {ω | h t ω ≤ ((v : ℝ≥0) : WithTop ℝ≥0)})
  rw [hset]
  refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun n => ?_
  exact f.mono (hcj k) _ ((hB _ (hut n)).2 _)

end StoppedSigma

/-! ## The completed natural filtration -/

section Completed

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The raw natural filtration sits inside the completed one. -/
theorem natural_le_completedNaturalFiltration (P : Measure Ω) (X : ℝ≥0 → Ω → ℕ)
    (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) :
    Filtration.natural (Ω := NullMeasurableSpace Ω P) X
        (fun t => (hX t).nullMeasurable.measurable'.stronglyMeasurable) t
      ≤ completedNaturalFiltration P X hX t := by
  unfold completedNaturalFiltration
  dsimp only
  refine le_trans ?_ (Filtration.le_rightCont _ t)
  exact le_sup_left

/-- The observed process is measurable for its completed natural filtration. -/
theorem measurable_completedNaturalFiltration (P : Measure Ω) (X : ℝ≥0 → Ω → ℕ)
    (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) :
    Measurable[completedNaturalFiltration P X hX t]
      (fun ω : NullMeasurableSpace Ω P => X t ω) :=
  ((Filtration.stronglyAdapted_natural
      (fun t => (hX t).nullMeasurable.measurable'.stronglyMeasurable) t).mono
    (natural_le_completedNaturalFiltration P X hX t)).measurable

/-- **The completed natural filtration is right continuous**, in the elementwise form. -/
theorem measurableSet_completedNaturalFiltration_of_forall_gt (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℕ) (hX : ∀ t, Measurable (X t)) (v : ℝ≥0)
    (S : Set (NullMeasurableSpace Ω P))
    (hS : ∀ j > v, MeasurableSet[completedNaturalFiltration P X hX j] S) :
    MeasurableSet[completedNaturalFiltration P X hX v] S := by
  have hrc : (completedNaturalFiltration P X hX).rightCont =
      completedNaturalFiltration P X hX := by
    unfold completedNaturalFiltration
    dsimp only
    exact Filtration.rightCont_self _
  rw [← hrc, Filtration.rightCont_eq]
  exact MeasurableSpace.measurableSet_iInf.2 fun j =>
    MeasurableSpace.measurableSet_iInf.2 fun hj => hS j hj

/-- The completed natural filtration at `t` sits inside the augmented raw natural filtration at
every later time. -/
theorem completedNaturalFiltration_le_natural_sup_null (P : Measure Ω) (X : ℝ≥0 → Ω → ℕ)
    (hX : ∀ t, Measurable (X t)) {t u : ℝ≥0} (htu : t < u) :
    completedNaturalFiltration P X hX t ≤
      Filtration.natural (Ω := NullMeasurableSpace Ω P) X
        (fun t => (hX t).nullMeasurable.measurable'.stronglyMeasurable) u ⊔
      nullEventSigma P := by
  unfold completedNaturalFiltration
  dsimp only
  rw [Filtration.rightCont_eq]
  exact iInf₂_le u htu

/-- An event of the completed natural filtration at `t` is an event of the augmented raw
natural filtration at every later time. -/
theorem measurableSet_natural_sup_null_of_completed (P : Measure Ω) (X : ℝ≥0 → Ω → ℕ)
    (hX : ∀ t, Measurable (X t)) {t u : ℝ≥0} (htu : t < u)
    {B : Set (NullMeasurableSpace Ω P)}
    (hB : MeasurableSet[completedNaturalFiltration P X hX t] B) :
    MeasurableSet[Filtration.natural (Ω := NullMeasurableSpace Ω P) X
        (fun t => (hX t).nullMeasurable.measurable'.stronglyMeasurable) u ⊔
      nullEventSigma P] B :=
  completedNaturalFiltration_le_natural_sup_null P X hX htu B hB

end Completed

/-! ## The patched clock as a real-valued, continuous clock -/

section Clock

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]
  {F : IndexedCells V} {m : V → ℝ} {PF : ProcessFamily V}

open Classical in
/-- The patched clock `AreaFastClockStopping.fastClock`, as an `ℝ≥0`-valued function. -/
noncomputable def fastClockNN (F : IndexedCells V) (m : V → ℝ) (PF : ProcessFamily V)
    (t : ℝ≥0) (ω : PF.Ω) : ℝ≥0 :=
  if ClockGood F m PF ω then inverseAreaClock F m PF ω t else t

theorem fastClockNN_of_good {ω : PF.Ω} (hω : ClockGood F m PF ω) (t : ℝ≥0) :
    fastClockNN F m PF t ω = inverseAreaClock F m PF ω t := by
  unfold fastClockNN
  exact if_pos hω

theorem fastClockNN_of_not_good {ω : PF.Ω} (hω : ¬ ClockGood F m PF ω) (t : ℝ≥0) :
    fastClockNN F m PF t ω = t := by
  unfold fastClockNN
  exact if_neg hω

theorem fastClock_eq_coe_fastClockNN (F : IndexedCells V) (m : V → ℝ) (PF : ProcessFamily V)
    (t : ℝ≥0) (ω : PF.Ω) :
    fastClock F m PF t ω = ((fastClockNN F m PF t ω : ℝ≥0) : WithTop ℝ≥0) := by
  by_cases hω : ClockGood F m PF ω
  · rw [fastClock_of_good hω, fastClockNN_of_good hω]
  · rw [fastClock_of_not_good hω, fastClockNN_of_not_good hω]

theorem monotone_fastClockNN (F : IndexedCells V) (m : V → ℝ) (PF : ProcessFamily V)
    (ω : PF.Ω) : Monotone (fun t => fastClockNN F m PF t ω) := by
  intro s t hst
  show fastClockNN F m PF s ω ≤ fastClockNN F m PF t ω
  by_cases hω : ClockGood F m PF ω
  · rw [fastClockNN_of_good hω, fastClockNN_of_good hω]
    exact monotone_inverseAreaClock_of_good hω hst
  · rw [fastClockNN_of_not_good hω, fastClockNN_of_not_good hω]
    exact hst

/-- **The patched clock is continuous in time for every sample.** -/
theorem continuous_fastClockNN (F : IndexedCells V) (m : V → ℝ) (PF : ProcessFamily V)
    (ω : PF.Ω) : Continuous (fun t => fastClockNN F m PF t ω) := by
  by_cases hω : ClockGood F m PF ω
  · have heq : (fun t => fastClockNN F m PF t ω) = (goodOrderIso hω).symm := by
      funext t
      rw [fastClockNN_of_good hω, inverseAreaClock_eq_symm_of_good hω]
    rw [heq]
    exact (goodOrderIso hω).symm.continuous
  · have heq : (fun t => fastClockNN F m PF t ω) = id := by
      funext t
      rw [fastClockNN_of_not_good hω]
      rfl
    rw [heq]
    exact continuous_id

end Clock

/-! ## The inclusion -/

section Inclusion

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The real encoding of an `Option V`-valued path. -/
noncomputable def encReal {Ω : Type*} (enc : Option V → ℕ) (X : ℝ≥0 → Ω → Option V)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ((enc (X t ω) : ℕ) : ℝ)

/-- **Step (c), generic form.**  For the constructed family, a fast rate `w` dominating the
Lemma 3.5 rate function, and any stopping-time certificate `hh` for the patched inverse area
clock in the completed fast filtration, the completed natural filtration of the area path at
`t` is contained in the stopped σ-algebra `𝔽_{h t}`. -/
theorem completedArea_le_measurableSpace_fastClock
    (F : IndexedCells V) (hF : Geometry F) (D : F.graph.Exhaustion)
    (hG : F.graph.toSimpleGraph.Connected) (hmin : F.graph.EnergyMinimizer)
    (w : V → ℝ) (hw : ∀ v, 0 < w v) (hdom : ∀ v, D.rateFunction hG v ≤ w v) (z : V)
    (hwalkA : IsReflectedWalk F.graph (areaRate F) hmin
      (Existence.processFamily D hG (areaRate F)))
    (harea : ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2)
    (enc : Option V → ℕ)
    (hh : ∀ t, IsStoppingTime
      (completedNaturalFiltration (Existence.sampleLaw D hG z)
        (fun t ω => enc (Existence.process D w t ω))
        (fun t => (measurable_of_countable enc).comp (Existence.measurable_process D w t)))
      (fastClock F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w) t))
    (t : ℝ≥0) :
    completedNaturalFiltration (Existence.sampleLaw D hG z)
        (fun t ω => enc (Existence.process D (areaRate F) t ω))
        (fun t => (measurable_of_countable enc).comp
          (Existence.measurable_process D (areaRate F) t)) t
      ≤ (hh t).measurableSpace := by
  have hwalk : IsReflectedWalk F.graph w hmin (Existence.processFamily D hG w) :=
    canonical_isReflectedWalk_of_rate_le D hG hmin w hw hdom
  have hXf : ∀ t, Measurable (fun ω => enc (Existence.process D w t ω)) :=
    fun t => (measurable_of_countable enc).comp (Existence.measurable_process D w t)
  have hXa : ∀ t, Measurable (fun ω => enc (Existence.process D (areaRate F) t ω)) :=
    fun t => (measurable_of_countable enc).comp (Existence.measurable_process D (areaRate F) t)
  -- null events
  have hnullF : ∀ (v : ℝ≥0) (A : Set (NullMeasurableSpace (Existence.Sample V)
      (Existence.sampleLaw D hG z))), (Existence.sampleLaw D hG z).completion A = 0 →
      MeasurableSet[completedNaturalFiltration (Existence.sampleLaw D hG z)
        (fun t ω => enc (Existence.process D w t ω)) hXf v] A :=
    fun v A hA => measurableSet_completedNaturalFiltration_of_null _ _ hXf v A hA
  have hnullS : ∀ (u : ℝ≥0) (A : Set (NullMeasurableSpace (Existence.Sample V)
      (Existence.sampleLaw D hG z))), (Existence.sampleLaw D hG z).completion A = 0 →
      MeasurableSet[(hh u).measurableSpace] A := fun u A hA =>
    measurableSet_stopped_of_forall (hh u)
      (fun ω => fastClock_ne_top F (fun v => F.graph.pi v / w v)
        (Existence.processFamily D hG w) u ω)
      fun v => hnullF v _ (measure_mono_null inter_subset_left hA)
  -- the good event: good clock and the path identity of step (b)
  have hgoodpath := ae_clockGood_and_path_eq F hF D hG hmin w hw hdom z harea
  have hbad : (Existence.sampleLaw D hG z).completion
      {ω | ¬ (ClockGood F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w) ω ∧
        ∀ t : ℝ≥0, Existence.process D (areaRate F) t ω =
          areaTimeChangedPath F (fun v => F.graph.pi v / w v)
            (Existence.processFamily D hG w) t ω)} = 0 :=
    (Measure.completion_apply _ _).trans (ae_iff.1 hgoodpath)
  -- the fast path, real-encoded, is adapted
  have hMf : StronglyAdapted (completedNaturalFiltration (Existence.sampleLaw D hG z)
      (fun t ω => enc (Existence.process D w t ω)) hXf)
      (encReal enc (Existence.processFamily D hG w).X) := fun r =>
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_completedNaturalFiltration _ _ hXf r)).stronglyMeasurable
  -- on the good event, below the horizon, the stopped fast value is the area value
  have hstop : ∀ s u v : ℝ≥0, s ≤ u →
      ∀ ω : NullMeasurableSpace (Existence.Sample V) (Existence.sampleLaw D hG z),
      (ClockGood F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w) ω ∧
        ∀ t : ℝ≥0, Existence.process D (areaRate F) t ω =
          areaTimeChangedPath F (fun v => F.graph.pi v / w v)
            (Existence.processFamily D hG w) t ω) →
      fastClock F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w) u ω
        ≤ (v : WithTop ℝ≥0) →
      stoppedValue (encReal enc (Existence.processFamily D hG w).X)
          (fun ω => min (fastClock F (fun v => F.graph.pi v / w v)
            (Existence.processFamily D hG w) s ω) (v : WithTop ℝ≥0)) ω
        = ((enc (Existence.process D (areaRate F) s ω) : ℕ) : ℝ) := by
    intro s u v hsu ω hω hωu
    obtain ⟨hgood, hpath⟩ := hω
    have hsle : fastClock F (fun v => F.graph.pi v / w v) (Existence.processFamily D hG w) s ω
        ≤ (v : WithTop ℝ≥0) :=
      (monotone_fastClock F (fun v => F.graph.pi v / w v)
        (Existence.processFamily D hG w) ω hsu).trans hωu
    have hmin' : min (fastClock F (fun v => F.graph.pi v / w v)
        (Existence.processFamily D hG w) s ω) (v : WithTop ℝ≥0) =
        ((inverseAreaClock F (fun v => F.graph.pi v / w v)
          (Existence.processFamily D hG w) ω s : ℝ≥0) : WithTop ℝ≥0) := by
      rw [min_eq_left hsle, fastClock_of_good hgood]
    have hval : areaTimeChangedPath F (fun v => F.graph.pi v / w v)
        (Existence.processFamily D hG w) s ω = Existence.process D (areaRate F) s ω :=
      (hpath s).symm
    show encReal enc (Existence.processFamily D hG w).X
      (min (fastClock F (fun v => F.graph.pi v / w v)
        (Existence.processFamily D hG w) s ω) (v : WithTop ℝ≥0)).untopA ω = _
    rw [hmin']
    show ((enc (areaTimeChangedPath F (fun v => F.graph.pi v / w v)
      (Existence.processFamily D hG w) s ω) : ℕ) : ℝ) = _
    rw [hval]
  -- right continuity of the fast path at the bounded stopping time `min (h s) v`
  have hrcAt : ∀ s v : ℝ≥0, ∀ᵐ ω ∂(Existence.sampleLaw D hG z).completion,
      ContinuousWithinAt (fun r => encReal enc (Existence.processFamily D hG w).X r ω)
        (Ioi (min (fastClock F (fun v => F.graph.pi v / w v)
          (Existence.processFamily D hG w) s ω) (v : WithTop ℝ≥0)).untopA)
        (min (fastClock F (fun v => F.graph.pi v / w v)
          (Existence.processFamily D hG w) s ω) (v : WithTop ℝ≥0)).untopA := by
    intro s v
    have hAs : ∀ᵐ ω ∂Existence.sampleLaw D hG z,
        (∃ x, Existence.process D (areaRate F) s ω = some x) :=
      ((hwalkA z).2.1 s).mono fun _ h => h.1
    have hFv : ∀ᵐ ω ∂Existence.sampleLaw D hG z,
        (∃ x, (Existence.processFamily D hG w).X v ω = some x) :=
      ((hwalk z).2.1 v).mono fun _ h => h.1
    have hrc : ∀ᵐ ω ∂Existence.sampleLaw D hG z, ∀ r : ℝ≥0,
        (∃ x, (Existence.processFamily D hG w).X r ω = some x) →
          ∃ ε : ℝ≥0, 0 < ε ∧ ∀ q ∈ Ico r (r + ε),
            (Existence.processFamily D hG w).X q ω = (Existence.processFamily D hG w).X r ω :=
      (hwalk z).2.2.1
    refine StoppedFormAssociation.ae_completion_of_ae ?_
    filter_upwards [hgoodpath, hAs, hFv, hrc] with ω hω hAsω hFvω hrcω
    obtain ⟨hgood, hpath⟩ := hω
    rw [fastClock_of_good hgood, ← WithTop.coe_min]
    change ContinuousWithinAt (fun r => encReal enc (Existence.processFamily D hG w).X r ω)
      (Ioi (min (inverseAreaClock F (fun v => F.graph.pi v / w v)
        (Existence.processFamily D hG w) ω s) v))
      (min (inverseAreaClock F (fun v => F.graph.pi v / w v)
        (Existence.processFamily D hG w) ω s) v)
    have hvert : ∃ x, (Existence.processFamily D hG w).X
        (min (inverseAreaClock F (fun v => F.graph.pi v / w v)
          (Existence.processFamily D hG w) ω s) v) ω = some x := by
      rcases le_total (inverseAreaClock F (fun v => F.graph.pi v / w v)
          (Existence.processFamily D hG w) ω s) v with hle | hle
      · rw [min_eq_left hle]
        obtain ⟨x, hx⟩ := hAsω
        refine ⟨x, ?_⟩
        have h1 : areaTimeChangedPath F (fun v => F.graph.pi v / w v)
            (Existence.processFamily D hG w) s ω = some x := (hpath s).symm.trans hx
        exact h1
      · rw [min_eq_right hle]
        exact hFvω
    obtain ⟨ε, hε, hconst⟩ := hrcω _ hvert
    refine continuousWithinAt_Ioi_of_eqOn_Ico hε fun r hr => ?_
    show ((enc ((Existence.processFamily D hG w).X r ω) : ℕ) : ℝ) = ((enc
      ((Existence.processFamily D hG w).X (min (inverseAreaClock F (fun v => F.graph.pi v / w v)
        (Existence.processFamily D hG w) ω s) v) ω) : ℕ) : ℝ)
    rw [hconst r hr]
  -- (1) the generators: `X^{area}_s` is `𝔽_{h u}`-measurable for `s ≤ u`
  have hsing : ∀ s u : ℝ≥0, s ≤ u → ∀ k : ℕ,
      MeasurableSet[(hh u).measurableSpace]
        ((fun ω : NullMeasurableSpace (Existence.Sample V) (Existence.sampleLaw D hG z) =>
          enc (Existence.process D (areaRate F) s ω)) ⁻¹' {k}) := by
    intro s u hsu k
    refine measurableSet_stopped_of_forall (hh u)
      (fun ω => fastClock_ne_top F (fun v => F.graph.pi v / w v)
        (Existence.processFamily D hG w) u ω)
      fun v => ?_
    have hτ' := (hh s).min_const v
    have hsv := stronglyMeasurable_stoppedValue_of_ae_continuousWithinAt
      (P := (Existence.sampleLaw D hG z).completion) hMf hτ' v (fun ω => min_le_right _ _)
      (hnullF v) (hrcAt s v)
    have hA' := (hsv.measurable (measurableSet_singleton ((k : ℕ) : ℝ))).inter (hh u v)
    refine measurableSet_of_null_diff (hnullF v) hA' ?_ ?_
    · refine measure_mono_null (fun ω hω => ?_) hbad
      intro hgood
      obtain ⟨⟨hωk, hωu⟩, hωA'⟩ := hω
      apply hωA'
      refine ⟨?_, hωu⟩
      have hk : enc (Existence.process D (areaRate F) s ω) = k := hωk
      show stoppedValue (encReal enc (Existence.processFamily D hG w).X)
        (fun ω => min (fastClock F (fun v => F.graph.pi v / w v)
          (Existence.processFamily D hG w) s ω) (v : WithTop ℝ≥0)) ω ∈ ({((k : ℕ) : ℝ)} : Set ℝ)
      rw [hstop s u v hsu ω hgood hωu, hk]
      exact Set.mem_singleton _
    · refine measure_mono_null (fun ω hω => ?_) hbad
      intro hgood
      obtain ⟨⟨hωk, hωu⟩, hωA⟩ := hω
      apply hωA
      refine ⟨?_, hωu⟩
      have hk : stoppedValue (encReal enc (Existence.processFamily D hG w).X)
          (fun ω => min (fastClock F (fun v => F.graph.pi v / w v)
            (Existence.processFamily D hG w) s ω) (v : WithTop ℝ≥0)) ω = ((k : ℕ) : ℝ) := hωk
      rw [hstop s u v hsu ω hgood hωu] at hk
      show enc (Existence.process D (areaRate F) s ω) ∈ ({k} : Set ℕ)
      exact Set.mem_singleton_iff.2 (by exact_mod_cast hk)
  have hkey : ∀ s u : ℝ≥0, s ≤ u → Measurable[(hh u).measurableSpace]
      (fun ω : NullMeasurableSpace (Existence.Sample V) (Existence.sampleLaw D hG z) =>
        enc (Existence.process D (areaRate F) s ω)) := by
    intro s u hsu S _
    have heq : (fun ω : NullMeasurableSpace (Existence.Sample V) (Existence.sampleLaw D hG z) =>
        enc (Existence.process D (areaRate F) s ω)) ⁻¹' S =
        ⋃ k ∈ S, ((fun ω : NullMeasurableSpace (Existence.Sample V)
          (Existence.sampleLaw D hG z) => enc (Existence.process D (areaRate F) s ω)) ⁻¹' {k}) := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.biUnion (Set.to_countable S) fun k _ => hsing s u hsu k
  -- (2) the augmented raw natural filtration at `u` sits in `𝔽_{h u}`
  have hG0 : ∀ u : ℝ≥0,
      Filtration.natural (Ω := NullMeasurableSpace (Existence.Sample V)
          (Existence.sampleLaw D hG z)) (fun t ω => enc (Existence.process D (areaRate F) t ω))
          (fun t => (hXa t).nullMeasurable.measurable'.stronglyMeasurable) u ⊔
        nullEventSigma (Existence.sampleLaw D hG z) ≤ (hh u).measurableSpace := by
    intro u
    refine sup_le ?_ ?_
    · refine iSup₂_le fun s hs => ?_
      exact measurable_iff_comap_le.1 (hkey s u hs)
    · refine MeasurableSpace.generateFrom_le fun A hA => hnullS u A ?_
      exact (Measure.completion_apply _ A).trans hA
  -- (3) right continuity along the continuous clock
  intro B hB
  exact measurableSet_stopped_of_forall_gt
    (measurableSet_completedNaturalFiltration_of_forall_gt _ _ hXf) hh
    (g := fun t ω => fastClockNN F (fun v => F.graph.pi v / w v)
      (Existence.processFamily D hG w) t ω)
    (fun t ω => fastClock_eq_coe_fastClockNN F (fun v => F.graph.pi v / w v)
      (Existence.processFamily D hG w) t ω)
    (fun ω => monotone_fastClockNN F (fun v => F.graph.pi v / w v)
      (Existence.processFamily D hG w) ω)
    (fun ω => continuous_fastClockNN F (fun v => F.graph.pi v / w v)
      (Existence.processFamily D hG w) ω) t
    fun u hu => hG0 u B (measurableSet_natural_sup_null_of_completed _ _ hXa hu hB)

end Inclusion

/-! ## The environment level: the `hG` binder of the clock change -/

section Environment

open Code EnvironmentFields QuenchedFormulation InvarianceMainStatement
open ReflectedGMS.InvarianceAssembly ReflectedGMS.SpatialExtensionConstruction
open ReflectedGMS.EnvironmentWalkDataProducer

/-- **The canonical clock certificate**: each value of the patched inverse area clock of the
canonical summable fast walk is an exact stopping time of that walk's completed natural
filtration, from the environment walk data alone. -/
theorem isStoppingTime_fastClock_env (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (start : Vertex e.val) (t : ℝ≥0) :
    IsStoppingTime
      (completedNaturalFiltration (areaSampleLaw (decode e) D hG start)
        (fun t ω => observedState e (Existence.process D (summableFastRate e D hG) t ω))
        (fun t => (measurable_of_countable (observedState e)).comp
          (Existence.measurable_process D (summableFastRate e D hG) t)))
      (fastClock (decode e) (fastSpeed e D hG)
        (Existence.processFamily D hG (summableFastRate e D hG)) t) := by
  obtain ⟨hmin, -, -, -⟩ := id hdat
  obtain ⟨hw, hdom, -, -⟩ := summableFastRate_spec e D hG
  exact isStoppingTime_fastClock (decode e) (fastSpeed e D hG)
    (canonical_isReflectedWalk_of_rate_le D hG hmin (summableFastRate e D hG) hw hdom) start
    (observedState_injective e)
    (fun t ω => observedState e (Existence.process D (summableFastRate e D hG) t ω))
    (fun _ _ => rfl)
    (fun t => (measurable_of_countable (observedState e)).comp
      (Existence.measurable_process D (summableFastRate e D hG) t))
    (ae_clockGood_fastSpeed e D hG hdat start) t

/-- **Step (c).**  The completed natural filtration of the exponential area path is contained,
at every time, in the stopped σ-algebra of the patched inverse area clock in the completed
filtration of the canonical summable fast walk. -/
theorem areaFiltration_le_measurableSpace_fastClock (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (start : Vertex e.val)
    (hh : ∀ t, IsStoppingTime
      (completedNaturalFiltration (areaSampleLaw (decode e) D hG start)
        (fun t ω => observedState e (Existence.process D (summableFastRate e D hG) t ω))
        (fun t => (measurable_of_countable (observedState e)).comp
          (Existence.measurable_process D (summableFastRate e D hG) t)))
      (fastClock (decode e) (fastSpeed e D hG)
        (Existence.processFamily D hG (summableFastRate e D hG)) t))
    (t : ℝ≥0) :
    areaFiltration e D (areaSampleLaw (decode e) D hG start) t ≤ (hh t).measurableSpace := by
  obtain ⟨hmin, -, hwalkA, -⟩ := id hdat
  obtain ⟨hw, hdom, -, -⟩ := summableFastRate_spec e D hG
  exact completedArea_le_measurableSpace_fastClock (decode e) (decode_geometry e) D hG hmin
    (summableFastRate e D hG) hw hdom start hwalkA
    (areaClock_holdingTimesSummable e D hG
      (AreaClockLevelZeroFiniteness.areaClockReachesLevelZeroIndices_of_environmentWalkData
        e D hG hdat) start)
    (observedState e) hh t

/-- **The `hG` binder of `martingale_stoppedValue_clock_of_bound_of_ae`, verbatim**, at the area
filtration, the completed canonical law and the canonical clock certificate. -/
theorem areaFiltration_ae_le_measurableSpace_fastClock (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (start : Vertex e.val) :
    ∀ (t : ℝ≥0) (B : Set (NullMeasurableSpace (Existence.Sample (Vertex e.val))
        (areaSampleLaw (decode e) D hG start))),
      MeasurableSet[areaFiltration e D (areaSampleLaw (decode e) D hG start) t] B →
      ∃ B', MeasurableSet[(isStoppingTime_fastClock_env e D hG hdat start t).measurableSpace] B' ∧
        B =ᵐ[(areaSampleLaw (decode e) D hG start).completion] B' :=
  fun t B hB => ⟨B, areaFiltration_le_measurableSpace_fastClock e D hG hdat start
    (isStoppingTime_fastClock_env e D hG hdat start) t B hB, EventuallyEq.rfl⟩

end Environment

end ReflectedGMS.AreaFastClockFiltration
