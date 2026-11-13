/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.HoldingDataFlowSpace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.HoldingIntervalsSubmacroscopic
import LatticeProb.Bonanno.ReflectedGMS.Temporal.SupTypeBlockSystem
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CellRootedTemporalTransport

/-!
# The holding data on the flow carrier, and `hsys` without a path gate

The abstract holding data `SupTypeTimeIndex.HoldingData` is instantiated on the flow carrier
`FlowSpace = Env × (CadlagPath ℕ∞ × CadlagPath Plane)` with `hold := flowHold` (the length of the
holding interval of the label path) and the gate

  `holdGate = flowGate ∩ {window sums finite} ∩ {window sums sublinear} ∩ {nonvertex times null}`

— the manuscript's invariant domain of Section 17 ("holding intervals have positive finite
length and cover almost every time, the maximal interval length meeting each bounded window is
finite, and (17.2)"), in a countable, hence measurable, form.  The gate is exactly invariant
under the re-rooting flow and the parabolic scaling (`holdGate_shift_iff`, `holdGate_scale_iff`),
which is why the manuscript imposes these bounds rather than (17.1) itself.

* `holdingData_flowSpace : HoldingData holdGate reRootFlow reScale flowHold`.
* `ae_mem_holdGate`: the gate is conull for every finite law satisfying the temporal mass
  transport (Lemma 17.1, `ae_forall_finite_submacroscopic`) and the two walk-level clauses of
  `HoldingLawInputs` (nonvertex times null, holding intervals bounded).
* `scaledRootChainSystemOn_holdGate`: **`hsys` on the flow carrier from the unmarked transport and
  `HoldingLawInputs` alone** — no lower bound on any time scale along the path, hence no
  `SpatialScaleSingular.pathGate` and no `hpath`.
* `scaledRootChainSystemOn_cellRooted_of_plainTransport_holding`: the cell-rooted consumer join,
  the drop-in for `CellRootedTemporalTransport.scaledRootChainSystemOn_cellRooted_of_plainTransport`
  in the singular setting.

## The one named law-level input

`HoldingLawInputs Q` collects three almost-sure properties of the label path under the rooted law:
the origin is a vertex time, the nonvertex (end-valued) times are Lebesgue-null, and every holding
interval is bounded.  These are properties of the reflected walk (fixed-time definedness and
finite exponential holding times), not of the geometry, and are satisfiable at the actual
cell-rooted law; they are NOT the positivity of a spatial scale along the path
(`SpatialScaleSingular.pathGate`), which fails at accumulation ends.  Producers at the flow kernel
for the first two clauses existed before the 2026-09-2x pruning (see the docstring of
`CellRootedTemporalTransport`, `ae_label_ne_top_flowKernel`, `ae_volume_labelTop_flowKernel`) and
are not re-proved here; the third is the finiteness of the walk's holding times.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace ReflectedGMS.HoldingDataFlowSpace

open Code EnvironmentLaws HarmonicLawIngredients
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.TwoSidedRegenerationFlowGrid
open ReflectedGMS.SimilarityClosedGate ReflectedGMS.SimilarityClosedGateFlow
open ReflectedGMS.FlowSpaceBlockSystem ReflectedGMS.FlowGateRootChainGate
open ReflectedGMS.ScaledRootChainGated ReflectedGMS.ScaledRootChain
open ReflectedGMS.ParabolicTransport ReflectedGMS.DyadicApproximation
open ReflectedGMS.LabelHoldingIntervals ReflectedGMS.HoldingIntervalsSubmacroscopic
open ReflectedGMS.SupTypeTimeIndex ReflectedGMS.SupTypeTimeBlocks ReflectedGMS.SupTypeBlockSystem
open ReflectedGMS.FlowSpaceTimeScale

/-! ## 1. Window sums and their bounds under the flow and the scaling -/

/-- The window supremum of the holding lengths (`SupTypeTimeIndex.windowSup` at `flowHold`). -/
noncomputable abbrev Wsup (ω : FlowSpace) (T : ℝ) : ℝ≥0∞ :=
  SupTypeTimeIndex.windowSup flowHold ω T

theorem Wsup_eq (ω : FlowSpace) (T : ℝ) :
    Wsup ω T = HoldingIntervalsSubmacroscopic.windowSup ω T := rfl

theorem Wsup_mono (ω : FlowSpace) {T T' : ℝ} (h : T ≤ T') : Wsup ω T ≤ Wsup ω T' :=
  HoldingIntervalsSubmacroscopic.windowSup_mono ω h

/-- **The rational-time property, at every carrier point**: a vertex time of `[c, d)` shares its
holding interval (and its holding length) with a rational time of `[c, d)`. -/
theorem flowHold_rat (ω : FlowSpace) (c d u : ℝ) (hu : u ∈ Set.Ico c d) (h0 : flowHold ω u ≠ 0) :
    ∃ q : ℚ, (q : ℝ) ∈ Set.Ico c d ∧ flowHold ω q = flowHold ω u := by
  have hv : ω.2.1.toFun u ≠ ⊤ := fun h => h0 ((flowHold_eq_zero_iff ω u).2 h)
  obtain ⟨q, hq, hmem⟩ := exists_rat_mem_holdSet_inter_Ico ω.2.1 hv hu
  exact ⟨q, hq, holdLen_eq_of_mem ω.2.1 hmem⟩

/-- Every holding length of a time of the window is dominated by the window supremum. -/
theorem le_Wsup (ω : FlowSpace) {T u : ℝ} (hu : u ∈ Set.Ico (-T) T) : flowHold ω u ≤ Wsup ω T := by
  by_cases h0 : flowHold ω u = 0
  · rw [h0]
    exact zero_le
  · obtain ⟨q, hq, hqu⟩ := flowHold_rat ω (-T) T u hu h0
    rw [← hqu]
    exact HoldingIntervalsSubmacroscopic.le_windowSup ω hq

/-- Under the re-rooting flow the window supremum is dominated by a larger window. -/
theorem Wsup_reRootFlow_le (r : ℝ) (ω : FlowSpace) (T : ℝ) :
    Wsup (reRootFlow r ω) T ≤ Wsup ω (T + |r|) := by
  refine iSup₂_le fun q hq => ?_
  rw [flowHold_shift]
  refine le_Wsup ω ⟨?_, ?_⟩
  · linarith [hq.1, neg_abs_le r]
  · linarith [hq.2, le_abs_self r]

theorem Wsup_le_reRootFlow (r : ℝ) (ω : FlowSpace) (T : ℝ) :
    Wsup ω T ≤ Wsup (reRootFlow r ω) (T + |r|) := by
  refine iSup₂_le fun q hq => ?_
  have h := flowHold_shift r ω ((q : ℝ) - r)
  rw [sub_add_cancel] at h
  rw [← h]
  refine le_Wsup (reRootFlow r ω) ⟨?_, ?_⟩
  · linarith [hq.1, le_abs_self r]
  · linarith [hq.2, neg_abs_le r]

/-- Under the parabolic scaling the window supremum scales with a rescaled window. -/
theorem Wsup_reScale_le {C : ℝ} (hC : 0 < C) (ω : FlowSpace) (T : ℝ) :
    Wsup (reScale C ω) T ≤ ENNReal.ofReal (C ^ 2) * Wsup ω (T / C ^ 2) := by
  have hC2 : 0 < C ^ 2 := pow_pos hC 2
  refine iSup₂_le fun q hq => ?_
  have h := flowHold_scale hC ω ((q : ℝ) / C ^ 2)
  rw [mul_div_cancel₀ _ hC2.ne'] at h
  rw [h]
  refine mul_le_mul_of_nonneg_left (le_Wsup ω ⟨?_, div_lt_div_of_pos_right hq.2 hC2⟩) zero_le
  rw [← neg_div]
  exact div_le_div_of_nonneg_right hq.1 hC2.le

theorem Wsup_le_reScale {C : ℝ} (hC : 0 < C) (ω : FlowSpace) (T : ℝ) :
    Wsup ω T ≤ ENNReal.ofReal ((C ^ 2)⁻¹) * Wsup (reScale C ω) (C ^ 2 * T) := by
  have hC2 : 0 < C ^ 2 := pow_pos hC 2
  have hc0 : ENNReal.ofReal (C ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hC2).ne'
  refine iSup₂_le fun q hq => ?_
  have h := flowHold_scale hC ω q
  have h2 : flowHold ω q = ENNReal.ofReal ((C ^ 2)⁻¹) * flowHold (reScale C ω) (C ^ 2 * q) := by
    rw [h, ← mul_assoc, ENNReal.ofReal_inv_of_pos hC2,
      ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
  rw [h2]
  refine mul_le_mul_of_nonneg_left (le_Wsup (reScale C ω) ⟨?_, ?_⟩) zero_le
  · have := mul_le_mul_of_nonneg_left hq.1 hC2.le
    linarith
  · exact mul_lt_mul_of_pos_left hq.2 hC2

/-! ## 2. The countable window conditions and their transfer -/

/-- **The window conditions of the gate**, in countable form: finite on every natural window and
sublinear along the natural windows with rational slopes. -/
def WindowGood (W : ℝ → ℝ≥0∞) : Prop :=
  (∀ n : ℕ, W n < ∞) ∧
    (∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → W n ≤ ENNReal.ofReal (ε * n))

/-- The window conditions transfer along an affine comparison `W' T ≤ a · W (b T + c)`. -/
theorem windowGood_of_le {W W' : ℝ → ℝ≥0∞} (hW : WindowGood W) (hmono : Monotone W)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (h : ∀ T : ℝ, 0 ≤ T → W' T ≤ ENNReal.ofReal a * W (b * T + c)) : WindowGood W' := by
  refine ⟨fun n => ?_, fun ε hε => ?_⟩
  · calc W' n ≤ ENNReal.ofReal a * W (b * n + c) := h n (Nat.cast_nonneg n)
      _ ≤ ENNReal.ofReal a * W ⌈b * n + c⌉₊ := by
          refine mul_le_mul_of_nonneg_left (hmono ?_) zero_le
          exact Nat.le_ceil _
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hW.1 _)
  · have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    obtain ⟨ε', hε'0, hε'le⟩ := exists_rat_btwn (show (0 : ℝ) < ε / (2 * a * b) by positivity)
    have hε'0' : (0 : ℚ) < ε' := by exact_mod_cast hε'0
    obtain ⟨N, hN⟩ := hW.2 ε' hε'0'
    refine ⟨max ⌈(N : ℝ) / b⌉₊ ⌈2 * a * ε' * (c + 1) / ε⌉₊, fun n hn => ?_⟩
    have hn1 : (N : ℝ) / b ≤ n :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_left _ _) hn)
    have hn2 : 2 * a * ε' * (c + 1) / ε ≤ n :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hn)
    have hbn : (N : ℝ) ≤ b * n := by
      rw [div_le_iff₀ hb] at hn1
      linarith
    have hNle : N ≤ ⌈b * n + c⌉₊ := by
      have : (N : ℝ) ≤ ⌈b * n + c⌉₊ := le_trans (by linarith) (Nat.le_ceil (b * n + c))
      exact_mod_cast this
    calc W' n ≤ ENNReal.ofReal a * W (b * n + c) := h n (Nat.cast_nonneg n)
      _ ≤ ENNReal.ofReal a * W ⌈b * n + c⌉₊ :=
          mul_le_mul_of_nonneg_left (hmono (Nat.le_ceil _)) zero_le
      _ ≤ ENNReal.ofReal a * ENNReal.ofReal (ε' * ⌈b * n + c⌉₊) :=
          mul_le_mul_of_nonneg_left (hN _ hNle) zero_le
      _ = ENNReal.ofReal (a * (ε' * ⌈b * n + c⌉₊)) := (ENNReal.ofReal_mul ha.le).symm
      _ ≤ ENNReal.ofReal (ε * n) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hceil : (⌈b * n + c⌉₊ : ℝ) ≤ b * n + c + 1 :=
            (Nat.ceil_lt_add_one (by positivity)).le
          have h1 : a * ε' * b ≤ ε / 2 := by
            rw [lt_div_iff₀ (by positivity)] at hε'le
            nlinarith
          have h2 : 2 * a * ε' * (c + 1) ≤ ε * n := by
            rw [div_le_iff₀ hε'] at hn2
            linarith
          nlinarith [mul_le_mul_of_nonneg_left hceil (by positivity : (0 : ℝ) ≤ a * ε'),
            Nat.cast_nonneg (α := ℝ) n]

theorem windowGood_reRootFlow {ω : FlowSpace} (h : WindowGood (Wsup ω)) (r : ℝ) :
    WindowGood (Wsup (reRootFlow r ω)) :=
  windowGood_of_le h (fun _ _ hTT => Wsup_mono ω hTT) one_pos one_pos (abs_nonneg r)
    fun T _ => by
      rw [ENNReal.ofReal_one, one_mul, one_mul]
      exact Wsup_reRootFlow_le r ω T

theorem windowGood_of_reRootFlow {ω : FlowSpace} (r : ℝ) (h : WindowGood (Wsup (reRootFlow r ω))) :
    WindowGood (Wsup ω) :=
  windowGood_of_le h (fun _ _ hTT => Wsup_mono _ hTT) one_pos one_pos (abs_nonneg r)
    fun T _ => by
      rw [ENNReal.ofReal_one, one_mul, one_mul]
      exact Wsup_le_reRootFlow r ω T

theorem windowGood_reScale {ω : FlowSpace} (h : WindowGood (Wsup ω)) {C : ℝ} (hC : 0 < C) :
    WindowGood (Wsup (reScale C ω)) := by
  have hC2 : 0 < C ^ 2 := pow_pos hC 2
  refine windowGood_of_le h (fun _ _ hTT => Wsup_mono ω hTT) hC2 (inv_pos.2 hC2) le_rfl
    fun T _ => ?_
  rw [add_zero, inv_mul_eq_div]
  exact Wsup_reScale_le hC ω T

theorem windowGood_of_reScale {ω : FlowSpace} {C : ℝ} (hC : 0 < C)
    (h : WindowGood (Wsup (reScale C ω))) : WindowGood (Wsup ω) := by
  have hC2 : 0 < C ^ 2 := pow_pos hC 2
  refine windowGood_of_le h (fun _ _ hTT => Wsup_mono _ hTT) (inv_pos.2 hC2) hC2 le_rfl
    fun T _ => ?_
  rw [add_zero]
  exact Wsup_le_reScale hC ω T

/-! ## 3. The null-set condition and its transfer -/

/-- The nonvertex times of the label path. -/
def nonvertexSet (ω : FlowSpace) : Set ℝ := {s : ℝ | flowHold ω s = 0}

theorem nonvertexSet_reRootFlow (r : ℝ) (ω : FlowSpace) :
    nonvertexSet (reRootFlow r ω) = (fun s : ℝ => s + r) ⁻¹' nonvertexSet ω := by
  ext s
  simp only [nonvertexSet, Set.mem_setOf_eq, Set.mem_preimage, flowHold_shift]

theorem volume_nonvertexSet_reRootFlow (r : ℝ) (ω : FlowSpace) :
    volume (nonvertexSet (reRootFlow r ω)) = volume (nonvertexSet ω) := by
  rw [nonvertexSet_reRootFlow]
  exact measure_preimage_add_right volume r _

theorem nonvertexSet_reScale {C : ℝ} (hC : 0 < C) (ω : FlowSpace) :
    nonvertexSet (reScale C ω) = (fun s : ℝ => (C ^ 2)⁻¹ * s) ⁻¹' nonvertexSet ω := by
  have hC2 : 0 < C ^ 2 := pow_pos hC 2
  ext s
  simp only [nonvertexSet, Set.mem_setOf_eq, Set.mem_preimage]
  have h := flowHold_scale hC ω ((C ^ 2)⁻¹ * s)
  rw [mul_inv_cancel_left₀ hC2.ne'] at h
  rw [h, mul_eq_zero]
  constructor
  · rintro (h0 | h0)
    · exact absurd h0 (ENNReal.ofReal_pos.2 hC2).ne'
    · exact h0
  · intro h0
    exact Or.inr h0

theorem volume_nonvertexSet_reScale_eq_zero_iff {C : ℝ} (hC : 0 < C) (ω : FlowSpace) :
    volume (nonvertexSet (reScale C ω)) = 0 ↔ volume (nonvertexSet ω) = 0 := by
  have hC2 : 0 < C ^ 2 := pow_pos hC 2
  rw [nonvertexSet_reScale hC, Real.volume_preimage_mul_left (inv_ne_zero hC2.ne'), mul_eq_zero]
  constructor
  · rintro (h0 | h0)
    · exact absurd h0 (ENNReal.ofReal_pos.2 (by rw [inv_inv]; exact abs_pos.2 hC2.ne')).ne'
    · exact h0
  · intro h0
    exact Or.inr h0

/-! ## 4. The gate -/

/-- **The holding gate**: the environment gate, the window conditions and the null-set
condition — the manuscript's invariant domain of Section 17. -/
def holdGate : Set FlowSpace :=
  flowGate ∩ {ω | WindowGood (Wsup ω) ∧ volume (nonvertexSet ω) = 0}

theorem mem_holdGate_iff (ω : FlowSpace) :
    ω ∈ holdGate ↔ ω.1 ∈ similarityClosedGate ∧ WindowGood (Wsup ω)
      ∧ volume (nonvertexSet ω) = 0 := by
  simp only [holdGate, Set.mem_inter_iff, Set.mem_setOf_eq, mem_flowGate_iff, and_assoc]

/-- **Exact invariance of the gate under the re-rooting flow.** -/
theorem reRootFlow_mem_holdGate_iff (r : ℝ) (ω : FlowSpace) :
    reRootFlow r ω ∈ holdGate ↔ ω ∈ holdGate := by
  rw [mem_holdGate_iff, mem_holdGate_iff, volume_nonvertexSet_reRootFlow]
  have hg : (reRootFlow r ω).1 ∈ similarityClosedGate ↔ ω.1 ∈ similarityClosedGate :=
    reRootFlow_mem_flowGate_iff r ω
  rw [hg]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, windowGood_of_reRootFlow r h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, windowGood_reRootFlow h2 r, h3⟩

/-- **Exact invariance of the gate under the parabolic scaling.** -/
theorem reScale_mem_holdGate_iff {C : ℝ} (hC : 0 < C) (ω : FlowSpace) :
    reScale C ω ∈ holdGate ↔ ω ∈ holdGate := by
  rw [mem_holdGate_iff, mem_holdGate_iff, volume_nonvertexSet_reScale_eq_zero_iff hC]
  have hg : (reScale C ω).1 ∈ similarityClosedGate ↔ ω.1 ∈ similarityClosedGate := by
    have h := reScale_mem_flowGate_iff C ω
    rw [mem_flowGate_iff, mem_flowGate_iff] at h
    exact h
  rw [hg]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, windowGood_of_reScale hC h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, windowGood_reScale h2 hC, h3⟩

/-! ### Measurability of the gate -/

theorem measurable_flowHold_fixed (t : ℝ) : Measurable fun ω : FlowSpace => flowHold ω t := by
  have h := measurable_flowHold.comp
    (measurable_id.prodMk (measurable_const : Measurable fun _ : FlowSpace => t))
  simpa only [Function.comp_def, id_eq] using h

theorem measurable_Wsup (T : ℝ) : Measurable fun ω : FlowSpace => Wsup ω T :=
  Measurable.iSup fun q => Measurable.iSup_Prop _ (measurable_flowHold_fixed q)

theorem measurableSet_windowGood : MeasurableSet {ω : FlowSpace | WindowGood (Wsup ω)} := by
  have h1 : MeasurableSet {ω : FlowSpace | ∀ n : ℕ, Wsup ω n < ∞} := by
    have hEq : {ω : FlowSpace | ∀ n : ℕ, Wsup ω n < ∞} = ⋂ n : ℕ, {ω | Wsup ω n < ∞} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hEq]
    exact MeasurableSet.iInter fun n => measurableSet_lt (measurable_Wsup n) measurable_const
  have h2 : MeasurableSet {ω : FlowSpace | ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Wsup ω n ≤ ENNReal.ofReal (ε * n)} := by
    have hEq : {ω : FlowSpace | ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        Wsup ω n ≤ ENNReal.ofReal (ε * n)}
        = ⋂ ε : ℚ, ⋂ _ : 0 < ε, ⋃ N : ℕ, ⋂ n : ℕ, ⋂ _ : N ≤ n,
          {ω | Wsup ω n ≤ ENNReal.ofReal (ε * n)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    rw [hEq]
    exact MeasurableSet.iInter fun ε => MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun N =>
      MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
        measurableSet_le (measurable_Wsup n) measurable_const
  have hEq : {ω : FlowSpace | WindowGood (Wsup ω)}
      = {ω : FlowSpace | ∀ n : ℕ, Wsup ω n < ∞} ∩ {ω : FlowSpace | ∀ ε : ℚ, 0 < ε → ∃ N : ℕ,
          ∀ n : ℕ, N ≤ n → Wsup ω n ≤ ENNReal.ofReal (ε * n)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, WindowGood]
  rw [hEq]
  exact h1.inter h2

theorem measurableSet_nonvertexSet (ω : FlowSpace) : MeasurableSet (nonvertexSet ω) :=
  (measurable_flowHold.comp (measurable_const.prodMk measurable_id)) (measurableSet_singleton 0)

theorem measurable_volume_nonvertexSet :
    Measurable fun ω : FlowSpace => volume (nonvertexSet ω) := by
  have hset : MeasurableSet {p : FlowSpace × ℝ | flowHold p.1 p.2 = 0} :=
    measurable_flowHold (measurableSet_singleton 0)
  have hind : Measurable (Set.indicator {p : FlowSpace × ℝ | flowHold p.1 p.2 = 0}
      (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hset
  have hEq : (fun ω : FlowSpace => volume (nonvertexSet ω)) = fun ω : FlowSpace =>
      ∫⁻ s : ℝ, Set.indicator {p : FlowSpace × ℝ | flowHold p.1 p.2 = 0}
        (fun _ => (1 : ℝ≥0∞)) (ω, s) := by
    funext ω
    have hsimp : (fun s : ℝ => Set.indicator {p : FlowSpace × ℝ | flowHold p.1 p.2 = 0}
        (fun _ => (1 : ℝ≥0∞)) (ω, s)) = (nonvertexSet ω).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext s
      by_cases hs : s ∈ nonvertexSet ω
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem
          (show ((ω, s) : FlowSpace × ℝ) ∈ {p : FlowSpace × ℝ | flowHold p.1 p.2 = 0} from hs)]
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem
          (show ((ω, s) : FlowSpace × ℝ) ∉ {p : FlowSpace × ℝ | flowHold p.1 p.2 = 0} from hs)]
    rw [hsimp, lintegral_indicator_const (measurableSet_nonvertexSet ω) 1, one_mul]
  rw [hEq]
  exact hind.lintegral_prod_right'

theorem measurableSet_holdGate : MeasurableSet holdGate := by
  refine measurableSet_flowGate.inter ?_
  have hEq : {ω : FlowSpace | WindowGood (Wsup ω) ∧ volume (nonvertexSet ω) = 0}
      = {ω : FlowSpace | WindowGood (Wsup ω)} ∩ {ω : FlowSpace | volume (nonvertexSet ω) = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [hEq]
  exact measurableSet_windowGood.inter
    (measurable_volume_nonvertexSet (measurableSet_singleton 0))

/-! ## 5. The holding data on the flow carrier -/

theorem windowGood_window_lt_top {ω : FlowSpace} (h : WindowGood (Wsup ω)) (T : ℝ) :
    Wsup ω T < ∞ :=
  lt_of_le_of_lt (Wsup_mono ω (Nat.le_ceil T)) (h.1 ⌈T⌉₊)

theorem windowGood_sublinear {ω : FlowSpace} (h : WindowGood (Wsup ω)) {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → Wsup ω T ≤ ENNReal.ofReal (ε * T) := by
  obtain ⟨ε', hε'0, hε'le⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 2 by positivity)
  have hε'0' : (0 : ℚ) < ε' := by exact_mod_cast hε'0
  obtain ⟨N, hN⟩ := h.2 ε' hε'0'
  refine ⟨max N 1, fun T hT => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hTN : (N : ℝ) ≤ T := le_trans (le_max_left _ _) hT
  have hNle : N ≤ ⌈T⌉₊ := by
    have : (N : ℝ) ≤ ⌈T⌉₊ := le_trans hTN (Nat.le_ceil T)
    exact_mod_cast this
  calc Wsup ω T ≤ Wsup ω ⌈T⌉₊ := Wsup_mono ω (Nat.le_ceil T)
    _ ≤ ENNReal.ofReal (ε' * ⌈T⌉₊) := hN _ hNle
    _ ≤ ENNReal.ofReal (ε * T) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hceil : (⌈T⌉₊ : ℝ) ≤ T + 1 := (Nat.ceil_lt_add_one (by linarith)).le
        have h2 : (ε' : ℝ) * (T + 1) ≤ ε * T := by nlinarith [hT1, hε'le, hε'0]
        exact le_trans (mul_le_mul_of_nonneg_left hceil hε'0.le) h2

/-- **The holding data on the flow carrier.** -/
theorem holdingData_flowSpace : HoldingData holdGate reRootFlow reScale flowHold where
  measurableSet_gate := measurableSet_holdGate
  flow_mem := reRootFlow_mem_holdGate_iff
  scale_mem := fun _ hC ω => reScale_mem_holdGate_iff hC ω
  shift := flowHold_shift
  scale := fun _ hC ω s => flowHold_scale hC ω s
  measurable := measurable_flowHold
  rat := fun ω _ c d u hu h0 => flowHold_rat ω c d u hu h0
  window_lt_top := fun ω hω T => windowGood_window_lt_top ((mem_holdGate_iff ω).1 hω).2.1 T
  window_sublinear := fun ω hω _ hε => windowGood_sublinear ((mem_holdGate_iff ω).1 hω).2.1 hε
  null_zero := fun ω hω => ((mem_holdGate_iff ω).1 hω).2.2

/-! ## 6. The gate is conull: Lemma 17.1 and the walk-level inputs -/

/-- **The walk-level inputs of the singular block construction**, almost surely under the rooted
law: the origin is a vertex time, the nonvertex times are Lebesgue-null, and every holding interval
is bounded.  Properties of the reflected walk (fixed-time definedness and finite holding times),
not of the geometry. -/
def HoldingLawInputs (Q : Measure FlowSpace) : Prop :=
  (∀ᵐ ω ∂Q, ω.2.1.toFun 0 ≠ ⊤) ∧ (∀ᵐ ω ∂Q, volume {s : ℝ | ω.2.1.toFun s = ⊤} = 0) ∧
    (∀ᵐ ω ∂Q, ∀ q : ℚ, ω.2.1.toFun q ≠ ⊤ → holdLen ω.2.1 q ≠ ∞)

theorem nonvertexSet_eq (ω : FlowSpace) : nonvertexSet ω = {s : ℝ | ω.2.1.toFun s = ⊤} := by
  ext s
  simp only [nonvertexSet, Set.mem_setOf_eq, flowHold_eq_zero_iff]

/-- The countable sublinearity clause from (17.2). -/
theorem windowGood_of_finite {ω : FlowSpace} (hcount : ∀ K : ℕ, (countedSet K ω).Finite)
    (hall : ∀ q : ℚ, ω.2.1.toFun q ≠ ⊤ → holdLen ω.2.1 q ≠ ∞) : WindowGood (Wsup ω) := by
  refine ⟨fun n => windowSup_lt_top_of_finite hcount hall n, fun ε hε => ?_⟩
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨C, hC, hbound⟩ := windowSup_le_of_finite hcount hall (show (0 : ℝ) < ε / 2 by positivity)
  refine ⟨⌈2 * C.toReal / ε⌉₊, fun n hn => ?_⟩
  have hn' : 2 * C.toReal / ε ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  calc Wsup ω n ≤ ENNReal.ofReal (ε / 2 * n) + C := hbound n (Nat.cast_nonneg n)
    _ ≤ ENNReal.ofReal (ε / 2 * n) + ENNReal.ofReal (ε / 2 * n) := by
        refine add_le_add le_rfl ?_
        rw [← ENNReal.ofReal_toReal hC]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hε'] at hn'
        linarith
    _ = ENNReal.ofReal (ε * n) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The gate is conull** under any finite law with the temporal mass transport and the
walk-level inputs. -/
theorem ae_mem_holdGate {Q : Measure FlowSpace} [IsFiniteMeasure Q]
    (hQ : ∀ᵐ ω ∂Q, ω.1 ∈ similarityClosedGate)
    (htr : ParabolicTemporalTransport Q reRootFlow reScale) (hlaw : HoldingLawInputs Q) :
    ∀ᵐ ω ∂Q, ω ∈ holdGate := by
  filter_upwards [hQ, ae_forall_finite_submacroscopic htr, hlaw.2.1, hlaw.2.2] with ω h1 h2 h3 h4
  refine (mem_holdGate_iff ω).2 ⟨h1, windowGood_of_finite h2 h4, ?_⟩
  rw [nonvertexSet_eq]
  exact h3

/-! ## 7. `hsys` on the flow carrier without a path gate -/

/-- The marked holding gate. -/
def markedHoldGate : Set (FlowSpace × Grid) := Prod.fst ⁻¹' holdGate

/-- **The gated root-chain system from the unmarked transport and the walk-level inputs**, for
every probability law on the flow carrier whose environment coordinate lies a.s. in the
similarity-closed gate.  No path gate, no lower bound on a time scale. -/
theorem scaledRootChainSystemOn_holdGate {Q : Measure FlowSpace} [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ ω ∂Q, ω.1 ∈ similarityClosedGate)
    (htr : ParabolicTemporalTransport Q reRootFlow reScale) (hlaw : HoldingLawInputs Q) :
    ScaledRootChainSystemOn markedHoldGate Q DyadicGridLaw.gridMeasure gridFlow gridScaleFlow
      (supBlock flowHold holdGate) (supSel flowHold holdingData_flowSpace) :=
  haveI : IsProbabilityMeasure DyadicGridLaw.gridMeasure :=
    DyadicGridLaw.isProbabilityMeasure_gridMeasure
  scaledRootChainSystemOn_of_holdingData flowHold holdingData_flowSpace gridFlow_apply
    gridScaleFlow_apply gridFlow_zero gridFlow_add measurable_gridFlow flowScaleIntertwine_gridFlow
    (parabolicTemporalTransport_prod_of_uniformGridLaw DyadicCylinderLaw.uniformGridLaw_gridMeasure
      gridFlow_apply gridScaleFlow_apply htr)
    (ae_mem_holdGate hQ htr hlaw)
    (by
      filter_upwards [hlaw.1] with ω hω _
      exact fun h => hω ((flowHold_eq_zero_iff ω 0).1 h))

/-! ### The cell-rooted consumer join -/

section CellRooted

open EnvironmentFields RootDensities
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.TemporalMassTransport ReflectedGMS.FlowCodingLine ReflectedGMS.FlowCodingKernel
open ReflectedGMS.FlowCodingFrontier ReflectedGMS.CellRootedEncodingRepair
open ReflectedGMS.CellRootedTemporalTransport

/-- **`hsys` at the cell-rooted law in the singular setting**: the drop-in for
`CellRootedTemporalTransport.scaledRootChainSystemOn_cellRooted_of_plainTransport`, with the
path gate `hpath` of `SpatialScaleSingular` REPLACED by the walk-level `HoldingLawInputs`. -/
theorem scaledRootChainSystemOn_cellRooted_of_plainTransport_holding {ν : Measure Env}
    [IsProbabilityMeasure ν] (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (z : CellField) (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (hext : ExtensionGate z G)
    (hplain : CellRootedPlainTransport (ν ⊗ₘ flowKernel z G hG hwalk hext))
    (hlaw : HoldingLawInputs ((ν ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot)) :
    ScaledRootChainSystemOn markedHoldGate ((ν ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot)
      DyadicGridLaw.gridMeasure gridFlow gridScaleFlow (supBlock flowHold holdGate)
      (supSel flowHold holdingData_flowSpace) := by
  have : IsProbabilityMeasure ((ν ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot) :=
    (Measure.isProbabilityMeasure_map_iff measurable_cellRoot.aemeasurable).2 inferInstance
  have hQ0 : ∀ᵐ ω ∂(ν ⊗ₘ flowKernel z G hG hwalk hext), ω.1 ∈ similarityClosedGate := by
    refine Measure.ae_compProd_of_ae_ae (measurable_fst measurableSet_similarityClosedGate) ?_
    filter_upwards [ae_mem_similarityClosedGate ν hmt hFE] with e he
    exact Filter.Eventually.of_forall fun _ => he
  have hQ : ∀ᵐ ω ∂((ν ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot),
      ω.1 ∈ similarityClosedGate :=
    ae_mem_similarityClosedGate_map_rootMap (c := fun _ : Env => (0 : Plane)) hQ0
      measurable_const
  exact scaledRootChainSystemOn_holdGate hQ
    ((parabolicTemporalTransport_map_cellRoot_iff _).2 hplain) hlaw

end CellRooted

end ReflectedGMS.HoldingDataFlowSpace

#print axioms ReflectedGMS.HoldingDataFlowSpace.holdingData_flowSpace
#print axioms ReflectedGMS.HoldingDataFlowSpace.reRootFlow_mem_holdGate_iff
#print axioms ReflectedGMS.HoldingDataFlowSpace.reScale_mem_holdGate_iff
#print axioms ReflectedGMS.HoldingDataFlowSpace.measurableSet_holdGate
#print axioms ReflectedGMS.HoldingDataFlowSpace.ae_mem_holdGate
#print axioms ReflectedGMS.HoldingDataFlowSpace.scaledRootChainSystemOn_holdGate
#print axioms ReflectedGMS.HoldingDataFlowSpace.scaledRootChainSystemOn_cellRooted_of_plainTransport_holding
