/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.AreaClockContinuity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaClockLocalFiniteness

/-!
# Continuity and strict increase of the actual area clock

Manuscript theorem `p:thm:areaclock` states that the area clock of the actual
reflected process is a homeomorphism of `[0,∞)`.  Its local-finiteness clause is
`AreaClockLocalFiniteness.areaClock_finite_on_compact_times`.  This file proves
the next two clauses for the very same clock
`AreaClockLocalFiniteness.areaClock`, with no new record and with neither
conclusion assumed:

* **continuity**, from absolute continuity of the indefinite Lebesgue integral
  (`MeasureTheory.tendsto_setLIntegral_zero`) on a compact time window, which
  needs only the checked pathwise finiteness;
* **strict increase**, from positivity of the actual area density `a_v / m(v)`
  at every vertex, together with the Lebesgue-null `∞`-sojourn of the actual
  path (property (i) of `IsReflectedWalk`, transported to the jointly
  measurable dyadic version).

Divergence of the clock at `∞` is proved elsewhere; the three clauses are
composed into the homeomorphism statement only once that producer exists.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ReflectedGMS.AreaClockContinuity

open ReflectedWalk ReflectedWalk.Theorem16
open PositiveOccupationClock AreaClockLocalFiniteness

universe u

/-! ## The elapsed-time clock of a nonnegative time density -/

section TimeClock

/-- The elapsed-time integral of a nonnegative density on `[0, t]`.  This is the
literal shape of `PositiveOccupationClock.weightedOccupationClock` along a fixed
trajectory. -/
noncomputable def timeClock (f : ℝ → ℝ≥0∞) (t : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ r in Icc (0 : ℝ) (t : ℝ), f r

/-- Exact increment of the clock over a later horizon. -/
theorem timeClock_eq_add_setLIntegral_Ioc (f : ℝ → ℝ≥0∞) {s t : ℝ≥0} (hst : s ≤ t) :
    timeClock f t = timeClock f s + ∫⁻ r in Ioc (s : ℝ) (t : ℝ), f r := by
  have hs : (0 : ℝ) ≤ (s : ℝ) := s.coe_nonneg
  have hst' : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
  have hdisj : Disjoint (Icc (0 : ℝ) (s : ℝ)) (Ioc (s : ℝ) (t : ℝ)) := by
    refine Set.disjoint_left.2 ?_
    intro r hr hr'
    exact absurd hr.2 (not_le.2 hr'.1)
  rw [timeClock, timeClock, ← Set.Icc_union_Ioc_eq_Icc hs hst',
    lintegral_union measurableSet_Ioc hdisj]

theorem timeClock_mono (f : ℝ → ℝ≥0∞) : Monotone (timeClock f) := by
  intro s t hst
  rw [timeClock_eq_add_setLIntegral_Ioc f hst]
  exact le_self_add

/-- Two-sided increment bound: the clocks at two horizons differ by at most the
integral over the interval between them. -/
theorem timeClock_le_add_setLIntegral (f : ℝ → ℝ≥0∞) (s t : ℝ≥0) :
    timeClock f t ≤ timeClock f s +
      ∫⁻ r in Ioc (min (s : ℝ) (t : ℝ)) (max (s : ℝ) (t : ℝ)), f r := by
  rcases le_total s t with hst | hts
  · have hst' : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    rw [min_eq_left hst', max_eq_right hst', ← timeClock_eq_add_setLIntegral_Ioc f hst]
  · exact (timeClock_mono f hts).trans le_self_add

/-- **Continuity from local finiteness alone.**  No measurability of the density
is needed: absolute continuity of the indefinite Lebesgue integral on the
compact window `[0, t₀ + 1]` controls both one-sided increments. -/
theorem continuousAt_timeClock (f : ℝ → ℝ≥0∞)
    (hfin : ∀ T : ℝ≥0, timeClock f T < ∞) (t₀ : ℝ≥0) :
    ContinuousAt (timeClock f) t₀ := by
  set T : ℝ≥0 := t₀ + 1 with hTdef
  have ht₀T : t₀ < T := by
    rw [hTdef]
    exact lt_add_of_pos_right t₀ one_pos
  have hνfin : (∫⁻ r, f r ∂(volume.restrict (Icc (0 : ℝ) (T : ℝ)))) ≠ ∞ := (hfin T).ne
  have hvol : Tendsto
      (fun t : ℝ≥0 => (volume.restrict (Icc (0 : ℝ) (T : ℝ)))
        (Ioc (min (t₀ : ℝ) (t : ℝ)) (max (t₀ : ℝ) (t : ℝ)))) (𝓝 t₀) (𝓝 0) := by
    have hcont : Continuous fun t : ℝ≥0 =>
        ENNReal.ofReal (max (t₀ : ℝ) (t : ℝ) - min (t₀ : ℝ) (t : ℝ)) :=
      ENNReal.continuous_ofReal.comp
        ((continuous_const.max NNReal.continuous_coe).sub
          (continuous_const.min NNReal.continuous_coe))
    have hlim := hcont.tendsto t₀
    rw [max_self, min_self, sub_self, ENNReal.ofReal_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) (fun t => ?_)
    refine (Measure.restrict_apply_le _ _).trans ?_
    rw [Real.volume_Ioc]
  have hD : Tendsto
      (fun t : ℝ≥0 => ∫⁻ r in Ioc (min (t₀ : ℝ) (t : ℝ)) (max (t₀ : ℝ) (t : ℝ)), f r
        ∂(volume.restrict (Icc (0 : ℝ) (T : ℝ)))) (𝓝 t₀) (𝓝 0) :=
    tendsto_setLIntegral_zero hνfin hvol
  show Tendsto (timeClock f) (𝓝 t₀) (𝓝 (timeClock f t₀))
  rw [ENNReal.tendsto_nhds (hfin t₀).ne]
  intro ε hε
  filter_upwards [gt_mem_nhds ht₀T, ENNReal.tendsto_nhds_zero.1 hD ε hε] with t htT hDt
  have hsub : Ioc (min (t₀ : ℝ) (t : ℝ)) (max (t₀ : ℝ) (t : ℝ)) ⊆ Icc (0 : ℝ) (T : ℝ) := by
    intro r hr
    refine ⟨(le_min t₀.coe_nonneg t.coe_nonneg).trans hr.1.le, hr.2.trans ?_⟩
    exact max_le (by exact_mod_cast ht₀T.le) (by exact_mod_cast htT.le)
  have hDt' : (∫⁻ r in Ioc (min (t₀ : ℝ) (t : ℝ)) (max (t₀ : ℝ) (t : ℝ)), f r) ≤ ε := by
    rwa [Measure.restrict_restrict_of_subset hsub] at hDt
  rw [Set.mem_Icc]
  constructor
  · rw [tsub_le_iff_right]
    calc timeClock f t₀
        ≤ timeClock f t + ∫⁻ r in Ioc (min (t : ℝ) (t₀ : ℝ)) (max (t : ℝ) (t₀ : ℝ)), f r :=
          timeClock_le_add_setLIntegral f t t₀
      _ = timeClock f t + ∫⁻ r in Ioc (min (t₀ : ℝ) (t : ℝ)) (max (t₀ : ℝ) (t : ℝ)), f r := by
          rw [min_comm, max_comm]
      _ ≤ timeClock f t + ε := add_le_add le_rfl hDt'
  · calc timeClock f t
        ≤ timeClock f t₀ + ∫⁻ r in Ioc (min (t₀ : ℝ) (t : ℝ)) (max (t₀ : ℝ) (t : ℝ)), f r :=
          timeClock_le_add_setLIntegral f t₀ t
      _ ≤ timeClock f t₀ + ε := add_le_add le_rfl hDt'

theorem continuous_timeClock (f : ℝ → ℝ≥0∞) (hfin : ∀ T : ℝ≥0, timeClock f T < ∞) :
    Continuous (timeClock f) :=
  continuous_iff_continuousAt.2 (continuousAt_timeClock f hfin)

/-- **Strict increase from an almost-everywhere positive density.**  The finite
value at the earlier horizon is what makes the positive increment strict. -/
theorem timeClock_lt_timeClock (f : ℝ → ℝ≥0∞) (hf : Measurable f) {s t : ℝ≥0}
    (hst : s < t) (hs : timeClock f s ≠ ∞)
    (hpos : ∀ᵐ r ∂(volume.restrict (Ioc (s : ℝ) (t : ℝ))), f r ≠ 0) :
    timeClock f s < timeClock f t := by
  rw [timeClock_eq_add_setLIntegral_Ioc f hst.le]
  refine ENNReal.lt_add_right hs fun h0 => ?_
  have hae : f =ᵐ[volume.restrict (Ioc (s : ℝ) (t : ℝ))] 0 := (lintegral_eq_zero_iff hf).1 h0
  have hfalse : ∀ᵐ _r ∂(volume.restrict (Ioc (s : ℝ) (t : ℝ))), False := by
    filter_upwards [hae, hpos] with r h1 h2
    exact h2 h1
  rw [eventually_false_iff_eq_bot, ae_eq_bot] at hfalse
  have hzero : volume (Ioc (s : ℝ) (t : ℝ)) = 0 := by
    have := congrArg (fun μ : Measure ℝ => μ univ) hfalse
    simpa using this
  rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hzero
  have hst' : (s : ℝ) < (t : ℝ) := by exact_mod_cast hst
  exact absurd hzero (not_le.2 (sub_pos.2 hst'))

end TimeClock

/-! ## The actual area clock -/

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The time density of the actual area clock along one trajectory. -/
noncomputable def areaClockPathDensity (F : IndexedCells V) (m : V → ℝ)
    (PF : ProcessFamily V) (ω : PF.Ω) (r : ℝ) : ℝ≥0∞ :=
  (PF.X (Real.toNNReal r) ω).elim 0 (areaClockDensity F m)

theorem measurable_areaClockPathDensity (F : IndexedCells V) (m : V → ℝ)
    (PF : ProcessFamily V) (ω : PF.Ω)
    (hX : Measurable fun r : ℝ => PF.X (Real.toNNReal r) ω) :
    Measurable (areaClockPathDensity F m PF ω) :=
  (measurable_of_countable fun p : Option V => p.elim 0 (areaClockDensity F m)).comp hX

/-- The actual area density `a_v / m(v)` is positive at every vertex. -/
theorem areaClockDensity_pos (F : IndexedCells V) (hF : Geometry F) {m : V → ℝ}
    (hm : ∀ v, 0 < m v) (v : V) : 0 < areaClockDensity F m v := by
  rw [areaClockDensity, ENNReal.ofReal_pos]
  exact div_pos (StatementIngredients.cellArea_pos F hF v) (hm v)

/-- **Public bridge: a finite clock is a continuous clock.**  Pathwise finiteness
at every horizon, as supplied by
`AreaClockLocalFiniteness.areaClock_finite_on_compact_times`, already gives
continuity of the actual area clock. -/
theorem continuous_areaClock_of_finite (F : IndexedCells V) (m : V → ℝ)
    (PF : ProcessFamily V) (ω : PF.Ω)
    (hfin : ∀ T : ℝ≥0, areaClock F m PF T ω < ∞) :
    Continuous fun t : ℝ≥0 => areaClock F m PF t ω :=
  continuous_timeClock (areaClockPathDensity F m PF ω) hfin

/-- Almost surely the path of the actual process agrees with its jointly
measurable dyadic version at every time and spends Lebesgue-null time at `∞`. -/
theorem ae_dyadicLimit_eq_and_sojournNone_eq_zero
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V} (h : IsReflectedWalk G w hmin PF) (o : V) :
    ∀ᵐ ω ∂PF.P o, (∀ s : ℝ≥0, dyadicLimit PF.X s ω = PF.X s ω) ∧
      ∀ T : ℝ≥0, sojournNone PF.X T ω = 0 := by
  have hnone : ∀ s : ℝ≥0, PF.P o {ω | dyadicLimit PF.X s ω = none} = 0 := by
    intro s
    have hae : ∀ᵐ ω ∂PF.P o, dyadicLimit PF.X s ω ≠ none := by
      filter_upwards [(h o).2.1 s, ae_dyadicLimit_eq (h o).2.2.1 (h o).2.2.2.1] with ω hω hv
      obtain ⟨⟨x, hx⟩, -⟩ := hω
      rw [hv s, hx]
      exact Option.some_ne_none x
    simpa only [ne_eq, not_not] using ae_iff.1 hae
  have hnat : ∀ᵐ ω ∂PF.P o, ∀ n : ℕ,
      sojournNone (dyadicLimit PF.X) (n : ℝ≥0) ω = 0 :=
    ae_all_iff.2 fun n => ae_sojournNone_eq_zero
      (measurable_uncurry_dyadicLimit PF.measurable_X) hnone (n : ℝ≥0)
  filter_upwards [hnat, ae_dyadicLimit_eq (h o).2.2.1 (h o).2.2.2.1] with ω hω hv
  refine ⟨hv, fun T => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge T
  have hcast : (T : ℝ) ≤ (((n : ℝ≥0) : ℝ)) := by exact_mod_cast hn
  refine measure_mono_null ?_ (hω n)
  intro r hr
  refine ⟨⟨hr.1.1, hr.1.2.trans hcast⟩, ?_⟩
  rw [hv (Real.toNNReal r)]
  exact hr.2

/-- On a path with null `∞`-sojourn, the actual area density is almost
everywhere nonzero on every time interval below the horizon. -/
theorem ae_areaClockPathDensity_ne_zero (F : IndexedCells V) (hF : Geometry F)
    {m : V → ℝ} (hm : ∀ v, 0 < m v) (PF : ProcessFamily V) (ω : PF.Ω) {s t : ℝ≥0}
    (hnull : sojournNone PF.X t ω = 0) :
    ∀ᵐ r ∂(volume.restrict (Ioc (s : ℝ) (t : ℝ))),
      areaClockPathDensity F m PF ω r ≠ 0 := by
  rw [ae_restrict_iff' measurableSet_Ioc, ae_iff]
  refine measure_mono_null ?_ hnull
  intro r hr
  simp only [Set.mem_setOf_eq, Classical.not_imp, not_not] at hr
  obtain ⟨hrI, hr0⟩ := hr
  refine ⟨⟨s.coe_nonneg.trans hrI.1.le, hrI.2⟩, ?_⟩
  by_contra hx
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hx
  rw [areaClockPathDensity, hv] at hr0
  exact (areaClockDensity_pos F hF hm v).ne' hr0

/-- **Strict increase of the actual area clock along one path**, from finiteness,
path measurability and null `∞`-sojourn. -/
theorem strictMono_areaClock_of_path (F : IndexedCells V) (hF : Geometry F)
    {m : V → ℝ} (hm : ∀ v, 0 < m v) (PF : ProcessFamily V) (ω : PF.Ω)
    (hX : Measurable fun r : ℝ => PF.X (Real.toNNReal r) ω)
    (hfin : ∀ T : ℝ≥0, areaClock F m PF T ω < ∞)
    (hnull : ∀ T : ℝ≥0, sojournNone PF.X T ω = 0) :
    StrictMono fun t : ℝ≥0 => areaClock F m PF t ω := by
  intro s t hst
  exact timeClock_lt_timeClock (areaClockPathDensity F m PF ω)
    (measurable_areaClockPathDensity F m PF ω hX) hst (hfin s).ne
    (ae_areaClockPathDensity_ne_zero F hF hm PF ω (hnull t))

section ActualClauses

variable {F : IndexedCells V} {m : V → ℝ} {hmin : F.graph.EnergyMinimizer}
  {PF : ProcessFamily V}

end ActualClauses

/-! ## The actual area clock as a homeomorphism of `[0,∞)`

The divergence input is the already checked
`PositiveOccupationClock.weightedOccupationClock_iSup_eq_top`, applied to the
area density, which is positive at the starting vertex. -/

section Homeomorphism

/-- The clock starts at `0`. -/
theorem timeClock_zero (f : ℝ → ℝ≥0∞) : timeClock f 0 = 0 := by
  rw [timeClock]
  refine setLIntegral_measure_zero _ _ ?_
  rw [NNReal.coe_zero, Real.volume_Icc, sub_self, ENNReal.ofReal_zero]

theorem areaClock_zero (F : IndexedCells V) (m : V → ℝ) (PF : ProcessFamily V)
    (ω : PF.Ω) : areaClock F m PF 0 ω = 0 :=
  timeClock_zero (areaClockPathDensity F m PF ω)

/-- The `ℝ≥0`-valued actual area clock along one trajectory. -/
noncomputable def areaClockNN (F : IndexedCells V) (m : V → ℝ)
    (PF : ProcessFamily V) (ω : PF.Ω) (t : ℝ≥0) : ℝ≥0 :=
  (areaClock F m PF t ω).toNNReal

theorem coe_areaClockNN (F : IndexedCells V) (m : V → ℝ) (PF : ProcessFamily V)
    (ω : PF.Ω) {t : ℝ≥0} (ht : areaClock F m PF t ω ≠ ∞) :
    (areaClockNN F m PF ω t : ℝ≥0∞) = areaClock F m PF t ω :=
  ENNReal.coe_toNNReal ht

theorem areaClockNN_zero (F : IndexedCells V) (m : V → ℝ) (PF : ProcessFamily V)
    (ω : PF.Ω) : areaClockNN F m PF ω 0 = 0 := by
  rw [areaClockNN, areaClock_zero, ENNReal.toNNReal_zero]

theorem continuous_areaClockNN (F : IndexedCells V) (m : V → ℝ)
    (PF : ProcessFamily V) (ω : PF.Ω)
    (hfin : ∀ T : ℝ≥0, areaClock F m PF T ω < ∞) :
    Continuous (areaClockNN F m PF ω) := by
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  have hc : ContinuousAt (fun t : ℝ≥0 => areaClock F m PF t ω) t₀ :=
    (continuous_areaClock_of_finite F m PF ω hfin).continuousAt
  exact (ENNReal.tendsto_toNNReal (hfin t₀).ne).comp hc

theorem strictMono_areaClockNN (F : IndexedCells V) (m : V → ℝ)
    (PF : ProcessFamily V) (ω : PF.Ω)
    (hfin : ∀ T : ℝ≥0, areaClock F m PF T ω < ∞)
    (hstrict : StrictMono fun t : ℝ≥0 => areaClock F m PF t ω) :
    StrictMono (areaClockNN F m PF ω) := fun s t hst =>
  (ENNReal.toNNReal_lt_toNNReal (hfin s).ne (hfin t).ne).2 (hstrict hst)

/-- Divergence of the clock plus continuity gives every value in `[0,∞)`. -/
theorem surjective_areaClockNN (F : IndexedCells V) (m : V → ℝ)
    (PF : ProcessFamily V) (ω : PF.Ω)
    (hfin : ∀ T : ℝ≥0, areaClock F m PF T ω < ∞)
    (htop : (⨆ t : ℝ≥0, areaClock F m PF t ω) = ⊤) :
    Function.Surjective (areaClockNN F m PF ω) := by
  intro y
  have hy : (y : ℝ≥0∞) < ⨆ t : ℝ≥0, areaClock F m PF t ω := by
    rw [htop]
    exact ENNReal.coe_lt_top
  obtain ⟨T, hT⟩ := lt_iSup_iff.1 hy
  have hyT : y < areaClockNN F m PF ω T := by
    rw [← ENNReal.coe_lt_coe, coe_areaClockNN F m PF ω (hfin T).ne]
    exact hT
  have hmem : y ∈ Icc (areaClockNN F m PF ω 0) (areaClockNN F m PF ω T) := by
    rw [areaClockNN_zero]
    exact ⟨zero_le, hyT.le⟩
  obtain ⟨t, -, ht⟩ :=
    intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ T)
      (continuous_areaClockNN F m PF ω hfin).continuousOn hmem
  exact ⟨t, ht⟩

variable {F : IndexedCells V} {m : V → ℝ} {hmin : F.graph.EnergyMinimizer}
  {PF : ProcessFamily V}

end Homeomorphism

end ReflectedGMS.AreaClockContinuity
