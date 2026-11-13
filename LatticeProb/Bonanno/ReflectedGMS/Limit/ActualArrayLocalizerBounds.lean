/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ActualArrayLocalizerBounds at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppingCrossMoment
import LatticeProb.Bonanno.ReflectedGMS.Limit.ThresholdStoppedMartingaleMoments

/-!
# The actual path localizer for a càdlàg martingale array: levels and exit bounds

`ReflectedGMS.Limit.ActualArrayQuadraticUniformIntegrability` reduces the uniform
square-tail premise of `QuadraticLimitMartingale` to two inputs that a genuine
localizer must supply, for a family of stopping times `σ j n`:

* a deterministic path level `c j` with `|N^{σ j n}| ≤ c j`, and
* an exit bound `P(σ j n ≤ T) ≤ g j` with `g j → 0`,

both uniform in `n`.  This file produces those two inputs for the actual càdlàg
martingale array, at the threshold localizer itself, and feeds them to that
theorem.

The localizer is the first time the *running supremum* `absRunningSup` of `|N|`
reaches the level `R`.  Working with the running supremum rather than with `|N|`
directly is what makes the hitting time an honest `F t`-stopping time: the
running supremum is monotone, and right continuity of the path turns
`{σ_R ≤ t}` into the terminal event `{R ≤ absRunningSup N t}` (lemmas
`ofReal_le_absRunningSup_of_forall_gt` and `absThresholdStop_le_iff`), which is a
countable union/intersection of `F t`-events modulo `P`-null sets by the existing
dense-exceedance lemma `rightContinuous_exceedance_dense`.

The two producers are then

* `abs_stoppedProcess_absThresholdStop_le`: the **path level**.  Before the
  threshold time the path is below `R`; at the threshold time the value is below
  `R + δ`, where `δ` is the actual jump size of the array path, i.e. the overshoot
  bound `dist (leftLim) (value) ≤ δ`.  Nothing is inferred about grid increments.
* `absThresholdStop_exit_le_div`: the **exit bound** `P(σ_R ≤ T) ≤ K / R²` from
  the existing square-martingale maximal inequality
  `SquareMartingaleMaximal.continuous_time_abs_maximal` and the terminal second
  moment `∫ (N T)² ≤ K`.

`uniform_tail_sq_increment_of_threshold_localizers` assembles them: for the
actual compensated-square array the terminal second moment is exactly the mean
bracket (`BracketSecondMoment.compensated_square_second_moment_of_zero`), so the
same constant `K` that bounds the bracket on `[0, T]` gives the exit bound, and
no new hypothesis beyond the array's jump size `δ` is added.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-! ### The running supremum and its threshold time -/

/-- The running supremum of `|N|` on `[0, t]`, valued in `ℝ≥0∞` so that no a priori
path bound is needed for it to be defined. -/
noncomputable def absRunningSup (N : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ≥0∞ :=
  fun t ω => ⨆ s ∈ Iic t, ENNReal.ofReal |N s ω|

/-- The actual path localizer at level `R`: the first time the running supremum of
`|N|` reaches `R`. -/
noncomputable def absThresholdStop (N : ℝ≥0 → Ω → ℝ) (R : ℝ) : Ω → WithTop ℝ≥0 :=
  hittingAfter (absRunningSup N) (Ici (ENNReal.ofReal R)) 0

theorem ofReal_abs_le_absRunningSup (N : ℝ≥0 → Ω → ℝ) (ω : Ω) {s t : ℝ≥0}
    (hst : s ≤ t) :
    ENNReal.ofReal |N s ω| ≤ absRunningSup N t ω :=
  le_iSup₂ (f := fun s (_ : s ∈ Iic t) => ENNReal.ofReal |N s ω|) s (mem_Iic.mpr hst)

theorem absRunningSup_mono (N : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Monotone fun t => absRunningSup N t ω := by
  intro a b hab
  refine iSup₂_le fun s hs => ?_
  exact ofReal_abs_le_absRunningSup N ω ((mem_Iic.mp hs).trans hab)

/-- Strictly before the threshold time the path is strictly below the level. -/
theorem abs_lt_of_lt_absThresholdStop {N : ℝ≥0 → Ω → ℝ} {R : ℝ} {ω : Ω} {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) < absThresholdStop N R ω) : |N s ω| < R := by
  have hnot : absRunningSup N s ω ∉ Ici (ENNReal.ofReal R) :=
    notMem_of_lt_hittingAfter hs zero_le
  have hlt : absRunningSup N s ω < ENNReal.ofReal R := by
    simpa only [mem_Ici, not_le] using hnot
  by_contra hcon
  have hR : ENNReal.ofReal R ≤ ENNReal.ofReal |N s ω| :=
    ENNReal.ofReal_le_ofReal (le_of_not_gt hcon)
  exact absurd (hR.trans (ofReal_abs_le_absRunningSup N ω (le_refl s))) (not_le.mpr hlt)

/-- Right continuity closes the level event from the right: if the running supremum
reaches the level at every later time, it already does so at `t`. -/
theorem ofReal_le_absRunningSup_of_forall_gt {N : ℝ≥0 → Ω → ℝ} {ω : Ω} {R : ℝ}
    {t : ℝ≥0} (hr : IsRightContinuous fun s => N s ω)
    (h : ∀ u : ℝ≥0, t < u → ENNReal.ofReal R ≤ absRunningSup N u ω) :
    ENNReal.ofReal R ≤ absRunningSup N t ω := by
  by_contra hcon
  push_neg at hcon
  have hbtop : absRunningSup N t ω ≠ ⊤ := hcon.ne_top
  have hRpos : 0 < R := by
    by_contra hR
    push_neg at hR
    rw [ENNReal.ofReal_eq_zero.mpr hR] at hcon
    exact absurd hcon (not_lt.mpr zero_le)
  have hbR : (absRunningSup N t ω).toReal < R := by
    have h1 := (ENNReal.toReal_lt_toReal hbtop ENNReal.ofReal_ne_top).mpr hcon
    rwa [ENNReal.toReal_ofReal hRpos.le] at h1
  set y : ℝ := ((absRunningSup N t ω).toReal + R) / 2 with hy
  have hby : (absRunningSup N t ω).toReal < y := by rw [hy]; linarith
  have hyR : y < R := by rw [hy]; linarith
  have hypos : 0 < y := lt_of_le_of_lt ENNReal.toReal_nonneg hby
  have hbylt : absRunningSup N t ω < ENNReal.ofReal y := by
    rw [← ENNReal.ofReal_toReal hbtop]
    exact (ENNReal.ofReal_lt_ofReal_iff hypos).mpr hby
  have habs : |N t ω| < y := by
    by_contra hcon2
    push_neg at hcon2
    have h1 : ENNReal.ofReal |N t ω| ≤ absRunningSup N t ω :=
      ofReal_abs_le_absRunningSup N ω (le_refl t)
    exact absurd ((ENNReal.ofReal_le_ofReal hcon2).trans h1) (not_le.mpr hbylt)
  have htend : Tendsto (fun s => N s ω) (𝓝[>] t) (𝓝 (N t ω)) := hr t
  have hev : ∀ᶠ s in 𝓝[>] t, |N s ω| < y :=
    htend.abs.eventually (eventually_lt_nhds habs)
  obtain ⟨u, htu, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  obtain ⟨v, hv1, hv2⟩ := exists_between (mem_Ioi.mp htu)
  have hSv : absRunningSup N v ω ≤ ENNReal.ofReal y := by
    refine iSup₂_le fun s hs => ?_
    rcases le_or_gt s t with hst | hst
    · exact (ofReal_abs_le_absRunningSup N ω hst).trans hbylt.le
    · exact ENNReal.ofReal_le_ofReal (hu ⟨hst, (mem_Iic.mp hs).trans_lt hv2⟩).le
  have hfin := (h v hv1).trans hSv
  exact absurd hfin (not_le.mpr ((ENNReal.ofReal_lt_ofReal_iff hRpos).mpr hyR))

/-- Below the level, the running supremum still exceeds any strictly smaller level
at some time before `t`. -/
theorem exists_lt_abs_of_ofReal_le_absRunningSup {N : ℝ≥0 → Ω → ℝ} {R : ℝ} {ω : Ω}
    {t : ℝ≥0} (h : ENNReal.ofReal R ≤ absRunningSup N t ω) {c : ℝ} (hc : c < R) :
    ∃ s ∈ Icc (0 : ℝ≥0) t, c < |N s ω| := by
  rcases lt_or_ge c 0 with hneg | hpos
  · exact ⟨0, mem_Icc.mpr ⟨le_rfl, zero_le⟩, hneg.trans_le (abs_nonneg _)⟩
  · have hRpos : 0 < R := hpos.trans_lt hc
    have hlt : ENNReal.ofReal c < absRunningSup N t ω :=
      ((ENNReal.ofReal_lt_ofReal_iff hRpos).mpr hc).trans_le h
    obtain ⟨s, hs1⟩ :=
      lt_iSup_iff.mp (show ENNReal.ofReal c < ⨆ s ∈ Iic t, ENNReal.ofReal |N s ω| from hlt)
    obtain ⟨hs, hlt2⟩ := lt_iSup_iff.mp hs1
    refine ⟨s, mem_Icc.mpr ⟨zero_le, mem_Iic.mp hs⟩, ?_⟩
    by_contra hcon
    push_neg at hcon
    exact absurd (ENNReal.ofReal_le_ofReal hcon) (not_le.mpr hlt2)

/-- Conversely, exceeding every strictly smaller level before `t` forces the running
supremum to reach the level. -/
theorem ofReal_le_absRunningSup_of_forall_lt {N : ℝ≥0 → Ω → ℝ} {R : ℝ} {ω : Ω}
    {t : ℝ≥0} (h : ∀ c : ℝ, c < R → ∃ s ∈ Icc (0 : ℝ≥0) t, c < |N s ω|) :
    ENNReal.ofReal R ≤ absRunningSup N t ω := by
  by_contra hcon
  push_neg at hcon
  have hbtop : absRunningSup N t ω ≠ ⊤ := hcon.ne_top
  have hRpos : 0 < R := by
    by_contra hR
    push_neg at hR
    rw [ENNReal.ofReal_eq_zero.mpr hR] at hcon
    exact absurd hcon (not_lt.mpr zero_le)
  have hbR : (absRunningSup N t ω).toReal < R := by
    have h1 := (ENNReal.toReal_lt_toReal hbtop ENNReal.ofReal_ne_top).mpr hcon
    rwa [ENNReal.toReal_ofReal hRpos.le] at h1
  set y : ℝ := ((absRunningSup N t ω).toReal + R) / 2 with hy
  have hby : (absRunningSup N t ω).toReal < y := by rw [hy]; linarith
  have hyR : y < R := by rw [hy]; linarith
  have hypos : 0 < y := lt_of_le_of_lt ENNReal.toReal_nonneg hby
  obtain ⟨s, hs, hlt⟩ := h y hyR
  have h1 : ENNReal.ofReal y < ENNReal.ofReal |N s ω| :=
    (ENNReal.ofReal_lt_ofReal_iff (hypos.trans hlt)).mpr hlt
  have h2 : ENNReal.ofReal |N s ω| ≤ absRunningSup N t ω :=
    ofReal_abs_le_absRunningSup N ω hs.2
  have h3 : absRunningSup N t ω < ENNReal.ofReal y := by
    rw [← ENNReal.ofReal_toReal hbtop]
    exact (ENNReal.ofReal_lt_ofReal_iff hypos).mpr hby
  exact lt_asymm h3 (h1.trans_le h2)

/-- For a right-continuous path the threshold time is at most `t` exactly when the
running supremum has reached the level by time `t`.  This is the identity that makes
the threshold time an `F t`-stopping time. -/
theorem absThresholdStop_le_iff {N : ℝ≥0 → Ω → ℝ} {R : ℝ} {ω : Ω}
    (hr : IsRightContinuous fun s => N s ω) (t : ℝ≥0) :
    absThresholdStop N R ω ≤ (t : WithTop ℝ≥0) ↔
      ENNReal.ofReal R ≤ absRunningSup N t ω := by
  classical
  constructor
  · intro hle
    have hex : ∃ j : ℝ≥0, 0 ≤ j ∧ absRunningSup N j ω ∈ Ici (ENNReal.ofReal R) := by
      by_contra hno
      rw [absThresholdStop, hittingAfter, if_neg hno] at hle
      exact absurd (top_unique hle) WithTop.coe_ne_top
    refine ofReal_le_absRunningSup_of_forall_gt hr fun u htu => ?_
    rw [absThresholdStop, hittingAfter, if_pos hex] at hle
    have hcoe : sInf {i : ℝ≥0 | 0 ≤ i ∧ absRunningSup N i ω ∈ Ici (ENNReal.ofReal R)} ≤ t :=
      WithTop.coe_le_coe.mp hle
    have hne : {i : ℝ≥0 | 0 ≤ i ∧ absRunningSup N i ω ∈ Ici (ENNReal.ofReal R)}.Nonempty :=
      hex
    obtain ⟨a, ha, hau⟩ :=
      (csInf_lt_iff (OrderBot.bddBelow _) hne).mp (hcoe.trans_lt htu)
    exact ha.2.trans (absRunningSup_mono N ω hau.le)
  · intro hmem
    exact hittingAfter_le_of_mem zero_le hmem

/-- The threshold localizer is an actual stopping time for the array filtration.
Only adaptedness, a.e. right continuity of the paths and the project's usual
null-event completion of the filtration are used. -/
theorem isStoppingTime_absThresholdStop
    {P : Measure Ω} {F : Filtration ℝ≥0 m} {N : ℝ≥0 → Ω → ℝ} {R : ℝ}
    (hN : Adapted F N)
    (hnull : ∀ (t : ℝ≥0) (B : Set Ω), P B = 0 → MeasurableSet[F t] B)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous fun t => N t ω) :
    IsStoppingTime F (absThresholdStop N R) := by
  intro t
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hcount : (insert t (D ∩ Iic t)).Countable := (hDcount.mono inter_subset_left).insert t
  set S : Set Ω := {ω | absThresholdStop N R ω ≤ (t : WithTop ℝ≥0)} with hSdef
  set A : Set Ω :=
    ⋂ k : ℕ, {ω | ∃ s ∈ insert t (D ∩ Iic t), R - 1 / ((k : ℝ) + 1) < |N s ω|} with hAdef
  have hAmeas : MeasurableSet[F t] A := by
    refine MeasurableSet.iInter fun k => ?_
    have hshape :
        {ω | ∃ s ∈ insert t (D ∩ Iic t), R - 1 / ((k : ℝ) + 1) < |N s ω|} =
          ⋃ s ∈ insert t (D ∩ Iic t), {ω | R - 1 / ((k : ℝ) + 1) < |N s ω|} := by
      ext ω
      simp only [mem_setOf_eq, mem_iUnion, exists_prop]
    rw [hshape]
    refine MeasurableSet.biUnion hcount fun s hs => ?_
    have hst : s ≤ t := by
      rcases hs with rfl | hs
      · exact le_rfl
      · exact hs.2
    have hmeas : MeasurableSet[F s] {ω | R - 1 / ((k : ℝ) + 1) < |N s ω|} :=
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (hN s))
    exact F.mono hst _ hmeas
  have hiff : ∀ᵐ ω ∂P, (ω ∈ S ↔ ω ∈ A) := by
    filter_upwards [hr] with ω hω
    have habs : IsRightContinuous fun s => |N s ω| := fun a => (hω a).abs
    simp only [hSdef, hAdef, mem_setOf_eq, mem_iInter]
    rw [absThresholdStop_le_iff hω t]
    constructor
    · intro h k
      have hck : R - 1 / ((k : ℝ) + 1) < R := by
        have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      obtain ⟨s, hs, hlt⟩ := exists_lt_abs_of_ofReal_le_absRunningSup h hck
      exact (rightContinuous_exceedance_dense habs hDdense t _).mp ⟨s, hs, hlt⟩
    · intro h
      refine ofReal_le_absRunningSup_of_forall_lt fun c hc => ?_
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < R - c by linarith)
      have hck : c < R - 1 / ((k : ℝ) + 1) := by linarith
      obtain ⟨s, hs, hlt⟩ := (rightContinuous_exceedance_dense habs hDdense t _).mpr (h k)
      exact ⟨s, hs, hck.trans hlt⟩
  have hSA : P (S \ A) = 0 := by
    have hnot : ∀ᵐ ω ∂P, ω ∉ S \ A := by
      filter_upwards [hiff] with ω hω
      exact fun hs => hs.2 (hω.mp hs.1)
    have hshape : {ω | ¬ω ∉ S \ A} = S \ A := by
      ext ω
      simp only [mem_setOf_eq, not_not]
    rw [← hshape]
    exact ae_iff.mp hnot
  have hAS : P (A \ S) = 0 := by
    have hnot : ∀ᵐ ω ∂P, ω ∉ A \ S := by
      filter_upwards [hiff] with ω hω
      exact fun hs => hs.2 (hω.mpr hs.1)
    have hshape : {ω | ¬ω ∉ A \ S} = A \ S := by
      ext ω
      simp only [mem_setOf_eq, not_not]
    rw [← hshape]
    exact ae_iff.mp hnot
  have hset : S = (A \ (A \ S)) ∪ (S \ A) := by
    ext ω
    simp only [mem_diff, mem_union]
    tauto
  change MeasurableSet[F t] S
  rw [hset]
  exact (hAmeas.diff (hnull t _ hAS)).union (hnull t _ hSA)

/-! ### The path level `R + δ` -/

/-! ### The exit bound `K / R²` -/

/-! ### The array statement consumed by the uniform-integrability theorem -/

end ReflectedGMS.MartingaleLimit
