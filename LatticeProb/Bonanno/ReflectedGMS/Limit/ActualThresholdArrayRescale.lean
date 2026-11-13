/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ActualThresholdArrayRescale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalThresholdArrayWiring
import LatticeProb.Bonanno.ReflectedGMS.Limit.ActualThresholdArrayShift
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalMartingaleCombination

/-!
# The rescaling wrapper: `harray` from one scalar coordinate's local martingale data

`Limit/ActualThresholdArrayShift` repaired the centering trap and the linear time change of the
càdlàg paths.  This module is the rescaling wrapper the predecessor packet named "mechanical": it
turns **one scalar coordinate's** data `(𝔽, N, A, C)` into the threshold-lane inputs of the
diffusively rescaled rows

`Yₙ(u) = εₙ · N(εₙ⁻² u)`,   `Vₙ(u) = εₙ² · A(εₙ⁻² u)`,   filtrations `rescaleFiltration 𝔽 εₙ`,

and composes everything up to the `harray` slot.

* `thresholdArrayInputs_rescaled` — **the global wrapper**: from a true square-integrable
  martingale `N` with compensator `A`, the global `ThresholdArrayInputs` of the rescaled rows at
  slope `C` and threshold `C·H + 1` (the pattern of
  `ApproximateBracketCLTRescaled.rescaledIncrementCharFunLimit_of_bracket_data`, :437-460).
* `localThresholdArrayInputs_rescaled` — **the local wrapper**: the same from a *locally*
  square-integrable martingale whose compensated square is a *local* martingale — exactly the
  form `HasOrdinaryEdgeBracket` delivers.  The new ingredient is that the diffusive time change
  preserves the local properties: a localizing sequence `τ` of `𝔽` becomes the localizing
  sequence `εₙ² τ` of `rescaleFiltration 𝔽 εₙ` (`locally_timeScale`), for `εₙ > 0`.
* `harray_of_local_coordinate` — **`harray` for one coordinate**, including the centering
  repair: the producer is applied to the centred process `N − p` (legitimate since `N 0 = p`
  a.s.) and the output array is shifted back by `εₙ p` with
  `localizedMartingaleArray_add_const`, so the array is for the **actual, uncentred** rows.

The bracket slope needs no separate hypothesis: `rescaledBracketLLN_const_nonneg` shows that the
bracket law of large numbers of a nonnegative bracket forces `C ≥ 0` on a probability space.

**This is an implication about an abstract coordinate.**  Nothing here mentions the reflected
walk; the walk instance is `Limit/ActualThresholdArrayWalk`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.ActualThresholdArray

open ReflectedGMS.LocalizedArrayProducer ReflectedGMS.WindowModulusGridTransfer
open ReflectedGMS.LocalizedThresholdArray ReflectedGMS.LocalThresholdArrayWiring
open ReflectedGMS.RescaledBracketLLNBridge ReflectedGMS.ApproximateBracketCLT
open ReflectedGMS.RescaledFddCharFun ReflectedGMS.LocalMartingaleCombination
open ReflectedGMS.BracketLLNUniform

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-! ## The diffusive time change of an extended time -/

/-- The time change `τ ↦ c⁻¹ τ` of an extended time.  With `c = ε⁻²` this carries a stopping
time of `𝔽` to a stopping time of `rescaleFiltration 𝔽 ε`. -/
noncomputable def timeScaleTop (c : ℝ≥0) (τ : WithTop ℝ≥0) : WithTop ℝ≥0 :=
  WithTop.map (fun s => c⁻¹ * s) τ

@[simp] theorem timeScaleTop_top (c : ℝ≥0) : timeScaleTop c ⊤ = ⊤ := rfl

@[simp] theorem timeScaleTop_coe (c s : ℝ≥0) :
    timeScaleTop c (s : WithTop ℝ≥0) = ((c⁻¹ * s : ℝ≥0) : WithTop ℝ≥0) := rfl

theorem timeScaleTop_mono (c : ℝ≥0) : Monotone (timeScaleTop c) :=
  Monotone.withTop_map fun _ _ hab => mul_le_mul_of_nonneg_left hab zero_le

theorem timeScaleTop_le_coe_iff {c : ℝ≥0} (hc : c ≠ 0) (τ : WithTop ℝ≥0) (u : ℝ≥0) :
    timeScaleTop c τ ≤ (u : WithTop ℝ≥0) ↔ τ ≤ ((c * u : ℝ≥0) : WithTop ℝ≥0) := by
  induction τ using WithTop.recTopCoe with
  | top =>
    rw [timeScaleTop_top]
    exact ⟨fun h => absurd h (not_le.2 (WithTop.coe_lt_top u)),
      fun h => absurd h (not_le.2 (WithTop.coe_lt_top _))⟩
  | coe s =>
    rw [timeScaleTop_coe, WithTop.coe_le_coe, WithTop.coe_le_coe]
    exact inv_mul_le_iff₀ (pos_iff_ne_zero.2 hc)

theorem coe_lt_timeScaleTop_iff {c : ℝ≥0} (hc : c ≠ 0) (τ : WithTop ℝ≥0) (u : ℝ≥0) :
    (u : WithTop ℝ≥0) < timeScaleTop c τ ↔ ((c * u : ℝ≥0) : WithTop ℝ≥0) < τ := by
  rw [← not_le, ← not_le, timeScaleTop_le_coe_iff hc]

theorem bot_lt_timeScaleTop_iff {c : ℝ≥0} (hc : c ≠ 0) (τ : WithTop ℝ≥0) :
    ⊥ < timeScaleTop c τ ↔ ⊥ < τ := by
  have h := coe_lt_timeScaleTop_iff hc τ 0
  rw [mul_zero] at h
  exact h

/-- **Stopping commutes with the time change.** -/
theorem untopA_min_timeScaleTop {c : ℝ≥0} (hc : c ≠ 0) (u : ℝ≥0) (τ : WithTop ℝ≥0) :
    c * (min (u : WithTop ℝ≥0) (timeScaleTop c τ)).untopA =
      (min ((c * u : ℝ≥0) : WithTop ℝ≥0) τ).untopA := by
  induction τ using WithTop.recTopCoe with
  | top =>
    rw [timeScaleTop_top, min_top_right, min_top_right]
    simp only [WithTop.untopD_coe]
  | coe s =>
    rw [timeScaleTop_coe, ← WithTop.coe_min, ← WithTop.coe_min]
    simp only [WithTop.untopD_coe]
    rw [mul_min, mul_inv_cancel_left₀ hc]

theorem isStoppingTime_timeScaleTop {𝔽 : Filtration ℝ≥0 m} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝔽 τ) {ε : ℝ≥0} (hε : ε ≠ 0) :
    IsStoppingTime (rescaleFiltration 𝔽 ε) (fun ω => timeScaleTop (ε⁻¹ ^ 2) (τ ω)) := by
  intro u
  have hc : ε⁻¹ ^ 2 ≠ 0 := pow_ne_zero _ (inv_ne_zero hε)
  have hset : {ω | timeScaleTop (ε⁻¹ ^ 2) (τ ω) ≤ (u : WithTop ℝ≥0)} =
      {ω | τ ω ≤ ((ε⁻¹ ^ 2 * u : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    exact timeScaleTop_le_coe_iff hc (τ ω) u
  have h := hτ (ε⁻¹ ^ 2 * u)
  rw [← hset] at h
  exact h

theorem tendsto_timeScaleTop_top {c : ℝ≥0} (hc : c ≠ 0) {f : ℕ → WithTop ℝ≥0}
    (hf : Tendsto f atTop (𝓝 ⊤)) : Tendsto (fun n => timeScaleTop c (f n)) atTop (𝓝 ⊤) := by
  rw [tendsto_order] at hf ⊢
  refine ⟨fun a ha => ?_, fun a ha => absurd ha (not_lt.2 le_top)⟩
  induction a using WithTop.recTopCoe with
  | top => exact absurd ha (lt_irrefl _)
  | coe u =>
    filter_upwards [hf.1 _ (WithTop.coe_lt_top (c * u))] with n hn
    exact (coe_lt_timeScaleTop_iff hc (f n) u).2 hn

/-- **A localizing sequence of `𝔽` becomes one of the rescaled filtration.** -/
theorem isLocalizingSequence_timeScaleTop {P : Measure Ω} {𝔽 : Filtration ℝ≥0 m}
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : IsLocalizingSequence 𝔽 τ P) {ε : ℝ≥0} (hε : ε ≠ 0) :
    IsLocalizingSequence (rescaleFiltration 𝔽 ε)
      (fun n ω => timeScaleTop (ε⁻¹ ^ 2) (τ n ω)) P where
  isStoppingTime n := isStoppingTime_timeScaleTop (hτ.isStoppingTime n) hε
  tendsto_top := by
    filter_upwards [hτ.tendsto_top] with ω hω
    exact tendsto_timeScaleTop_top (pow_ne_zero _ (inv_ne_zero hε)) hω
  mono := by
    filter_upwards [hτ.mono] with ω hω
    exact fun a b hab => timeScaleTop_mono _ (hω hab)

/-- **The exact localization of the time-changed process is the time change of the exact
localization.** -/
theorem stoppedProcess_indicator_timeScaleTop {E : Type*} [Zero E] (N : ℝ≥0 → Ω → E)
    (τ : Ω → WithTop ℝ≥0) {c : ℝ≥0} (hc : c ≠ 0) (u : ℝ≥0) (ω : Ω) :
    stoppedProcess (fun u => {ω | ⊥ < timeScaleTop c (τ ω)}.indicator (fun ω => N (c * u) ω))
        (fun ω => timeScaleTop c (τ ω)) u ω =
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (N s)) τ (c * u) ω := by
  simp only [stoppedProcess, Set.indicator, Set.mem_setOf_eq, bot_lt_timeScaleTop_iff hc]
  split_ifs
  · rw [untopA_min_timeScaleTop hc]
  · rfl

/-- **Local properties survive the diffusive time change**, provided the property itself does
(`hpq`).  The localizing sequence is `εₙ² τ`. -/
theorem locally_timeScale {E : Type*} [Zero E] {p q : (ℝ≥0 → Ω → E) → Prop}
    {P : Measure Ω} {𝔽 : Filtration ℝ≥0 m} {N : ℝ≥0 → Ω → E} {ε : ℝ≥0} (hε : ε ≠ 0)
    (hpq : ∀ Y : ℝ≥0 → Ω → E, p Y → q (fun u ω => Y (ε⁻¹ ^ 2 * u) ω))
    (h : Locally p 𝔽 N P) :
    Locally q (rescaleFiltration 𝔽 ε) (fun u ω => N (ε⁻¹ ^ 2 * u) ω) P := by
  have hc : ε⁻¹ ^ 2 ≠ 0 := pow_ne_zero _ (inv_ne_zero hε)
  refine ⟨fun n ω => timeScaleTop (ε⁻¹ ^ 2) (h.localSeq n ω),
    isLocalizingSequence_timeScaleTop h.isLocalizingSequence_localSeq hε, fun n => ?_⟩
  have key := hpq _ (h.stoppedProcess_localSeq n)
  convert key using 1
  funext u ω
  exact stoppedProcess_indicator_timeScaleTop N (h.localSeq n) hc u ω

/-- A martingale stays a martingale under the diffusive time change (any scale). -/
theorem martingale_timeScale {P : Measure Ω} {𝔽 : Filtration ℝ≥0 m} {Y : ℝ≥0 → Ω → ℝ}
    (hY : Martingale Y 𝔽 P) (ε : ℝ≥0) :
    Martingale (fun u ω => Y (ε⁻¹ ^ 2 * u) ω) (rescaleFiltration 𝔽 ε) P :=
  ⟨fun u => hY.stronglyAdapted (ε⁻¹ ^ 2 * u),
    fun _ _ hij => hY.condExp_ae_eq (mul_le_mul_of_nonneg_left hij zero_le)⟩

theorem isLocalMartingale_timeScale {P : Measure Ω} {𝔽 : Filtration ℝ≥0 m}
    {N : ℝ≥0 → Ω → ℝ} (hN : MartingaleIngredients.IsLocalMartingale P 𝔽 N)
    {ε : ℝ≥0} (hε : ε ≠ 0) :
    MartingaleIngredients.IsLocalMartingale P (rescaleFiltration 𝔽 ε)
      (fun u ω => N (ε⁻¹ ^ 2 * u) ω) :=
  ⟨fun u => hN.1 (ε⁻¹ ^ 2 * u),
    locally_timeScale hε (fun _ hY => martingale_timeScale hY ε) hN.2⟩

theorem isLocallySquareIntegrableMartingale_timeScale {P : Measure Ω} {𝔽 : Filtration ℝ≥0 m}
    {N : ℝ≥0 → Ω → ℝ} (hN : MartingaleIngredients.IsLocallySquareIntegrableMartingale P 𝔽 N)
    {ε : ℝ≥0} (hε : ε ≠ 0) :
    MartingaleIngredients.IsLocallySquareIntegrableMartingale P (rescaleFiltration 𝔽 ε)
      (fun u ω => N (ε⁻¹ ^ 2 * u) ω) :=
  ⟨fun u => hN.1 (ε⁻¹ ^ 2 * u),
    locally_timeScale hε (fun _ hY => ⟨martingale_timeScale hY.1 ε, fun _ => hY.2 _⟩) hN.2⟩

/-! ## Constants and centring -/

theorem isLocalMartingale_const {P : Measure Ω} [IsFiniteMeasure P] (𝔽 : Filtration ℝ≥0 m)
    (c : ℝ) : MartingaleIngredients.IsLocalMartingale P 𝔽 (fun _ _ => c) :=
  ⟨fun _ => stronglyMeasurable_const, Locally.of_prop (martingale_const 𝔽 P c)⟩

theorem isLocallySquareIntegrableMartingale_const {P : Measure Ω} [IsFiniteMeasure P]
    (𝔽 : Filtration ℝ≥0 m) (c : ℝ) :
    MartingaleIngredients.IsLocallySquareIntegrableMartingale P 𝔽 (fun _ _ => c) :=
  ⟨fun _ => stronglyMeasurable_const,
    Locally.of_prop ⟨martingale_const 𝔽 P c, fun _ => memLp_const c⟩⟩

/-- Centring a locally square-integrable martingale at a constant. -/
theorem isLocallySquareIntegrableMartingale_sub_const {P : Measure Ω} [IsFiniteMeasure P]
    {𝔽 : Filtration ℝ≥0 m} {N : ℝ≥0 → Ω → ℝ}
    (hN : MartingaleIngredients.IsLocallySquareIntegrableMartingale P 𝔽 N)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[𝔽 t] A)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N t ω)) (p : ℝ) :
    MartingaleIngredients.IsLocallySquareIntegrableMartingale P 𝔽 (fun t ω => N t ω - p) := by
  have heq : (fun t ω => N t ω - p) = fun t ω => N t ω + (fun (_ : ℝ≥0) (_ : Ω) => -p) t ω := by
    funext t ω
    ring
  rw [heq]
  exact isLocallySquareIntegrableMartingale_add hN
    (isLocallySquareIntegrableMartingale_const 𝔽 (-p)) hnull hr
    (ae_of_all _ fun _ => IsRightContinuous.const)

/-- **The centred compensated square is a local martingale with the same compensator**:
`(N − p)² − A = (N² − A) − 2p N + p²`. -/
theorem isLocalMartingale_sub_const_compensated {P : Measure Ω} [IsFiniteMeasure P]
    {𝔽 : Filtration ℝ≥0 m} {N A : ℝ≥0 → Ω → ℝ}
    (hN : MartingaleIngredients.IsLocallySquareIntegrableMartingale P 𝔽 N)
    (hNA : MartingaleIngredients.IsLocalMartingale P 𝔽 (fun t ω => N t ω * N t ω - A t ω))
    (hnull : ∀ (t : ℝ≥0) (S : Set Ω), P S = 0 → MeasurableSet[𝔽 t] S)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N t ω))
    (hrA : ∀ᵐ ω ∂P, IsRightContinuous (fun t => A t ω)) (p : ℝ) :
    MartingaleIngredients.IsLocalMartingale P 𝔽
      (fun t ω => (N t ω - p) * (N t ω - p) - A t ω) := by
  have hrNA : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N t ω * N t ω - A t ω) := by
    filter_upwards [hr, hrA] with ω h1 h2
    exact (h1.mul h1).sub h2
  have hr2N : ∀ᵐ ω ∂P, IsRightContinuous (fun t => -2 * p * N t ω) := by
    filter_upwards [hr] with ω h1
    have hc : IsRightContinuous (fun _ : ℝ≥0 => -2 * p) := IsRightContinuous.const
    exact hc.mul h1
  have hrsum : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => (N t ω * N t ω - A t ω) + -2 * p * N t ω) := by
    filter_upwards [hrNA, hr2N] with ω h1 h2
    exact h1.add h2
  have h1 := isLocalMartingale_add hNA (isLocalMartingale_const_mul hN.isLocalMartingale (-2 * p))
    hnull hrNA hr2N
  have h2 := isLocalMartingale_add h1 (isLocalMartingale_const 𝔽 (p ^ 2)) hnull hrsum
    (ae_of_all _ fun _ => IsRightContinuous.const)
  have heq : (fun t ω => (N t ω - p) * (N t ω - p) - A t ω) =
      fun t ω => ((N t ω * N t ω - A t ω) + -2 * p * N t ω) + p ^ 2 := by
    funext t ω
    ring
  rw [heq]
  exact h2

/-! ## The bracket slope is nonnegative -/

/-- **The bracket law of large numbers of a nonnegative bracket has a nonnegative slope**, on a
probability space.  Along `εₖ = 1/(k+1)` at `t = 1`, a negative `C` would put every rescaled
bracket at distance `≥ -C` from `C`, so the bad events would have probability one. -/
theorem rescaledBracketLLN_const_nonneg {P : Measure Ω} [IsProbabilityMeasure P]
    {A : ℝ≥0 → Ω → ℝ} {C : ℝ} (hA : ∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω)
    (hLLN : RescaledBracketLLN P A C) : 0 ≤ C := by
  by_contra hC0
  have hC : C < 0 := not_le.mp hC0
  have hε : Tendsto (fun k : ℕ => 1 / ((k : ℝ≥0) + 1)) atTop
      (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.2
      ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0), ?_⟩
    exact Eventually.of_forall fun k => Set.mem_Ioi.2 (by positivity)
  have hlim := hLLN _ hε 1 (-C / 2) (by linarith)
  have hone : ∀ k : ℕ, (1 : ℝ≥0∞) ≤ P {ω | -C / 2 <
      |((1 / ((k : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ 2 * A ((1 / ((k : ℝ≥0) + 1))⁻¹ ^ 2 * 1) ω
        - C * ((1 : ℝ≥0) : ℝ)|} := by
    intro k
    set S := {ω | -C / 2 < |((1 / ((k : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ 2 *
        A ((1 / ((k : ℝ≥0) + 1))⁻¹ ^ 2 * 1) ω - C * ((1 : ℝ≥0) : ℝ)|} with hSdef
    have hSc : P Sᶜ = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hA)
      rw [Set.mem_compl_iff] at hω
      rw [Set.mem_setOf_eq]
      intro hcon
      refine hω ?_
      rw [hSdef, Set.mem_setOf_eq, NNReal.coe_one]
      have hx : 0 ≤ ((1 / ((k : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ 2 *
          A ((1 / ((k : ℝ≥0) + 1))⁻¹ ^ 2 * 1) ω := mul_nonneg (sq_nonneg _) (hcon _)
      exact lt_of_lt_of_le (by linarith) (le_abs_self _)
    calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
      _ = P (S ∪ Sᶜ) := by rw [Set.union_compl_self]
      _ ≤ P S + P Sᶜ := measure_union_le _ _
      _ = P S := by rw [hSc, add_zero]
  have h10 : (1 : ℝ≥0∞) ≤ 0 := ge_of_tendsto' hlim hone
  exact absurd h10 (by norm_num)

/-! ## The rescaled bracket fields -/

section BracketFields

variable {P : Measure Ω} {𝔽 : Filtration ℝ≥0 m} {A : ℝ≥0 → Ω → ℝ} {ε : ℕ → ℝ≥0}

theorem rescaledBracket_start (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0) (n : ℕ) :
    ∀ᵐ ω ∂P, rescaledBracket A ε n 0 ω = 0 := by
  filter_upwards [hA0] with ω hω
  simp only [rescaledBracket, mul_zero, hω]

theorem rescaledBracket_adapted (hAad : ∀ u, StronglyMeasurable[𝔽 u] (A u)) (n : ℕ) :
    Adapted (rescaleFiltration 𝔽 (ε n)) (rescaledBracket A ε n) := fun u =>
  ((hAad ((ε n)⁻¹ ^ 2 * u)).const_mul ((ε n : ℝ) ^ 2)).measurable

theorem rescaledBracket_continuous (hAc : ∀ᵐ ω ∂P, Continuous (fun t => A t ω)) (n : ℕ) :
    ∀ᵐ ω ∂P, Continuous (fun t => rescaledBracket A ε n t ω) := by
  filter_upwards [hAc] with ω hω
  exact continuous_const.mul (hω.comp (continuous_const.mul continuous_id))

theorem rescaledBracket_monotone (hAm : ∀ᵐ ω ∂P, Monotone (fun t => A t ω)) (n : ℕ) :
    ∀ᵐ ω ∂P, Monotone (fun t => rescaledBracket A ε n t ω) := by
  filter_upwards [hAm] with ω hω
  intro a b hab
  exact mul_le_mul_of_nonneg_left (hω (mul_le_mul_of_nonneg_left hab zero_le)) (sq_nonneg _)

theorem rescaledBracket_nonneg (hA0 : ∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ rescaledBracket A ε n t ω := by
  filter_upwards [hA0] with ω hω
  intro t
  exact mul_nonneg (sq_nonneg _) (hω _)

/-- A monotone bracket starting at `0` is nonnegative. -/
theorem ae_nonneg_of_monotone_start (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hAm : ∀ᵐ ω ∂P, Monotone (fun t => A t ω)) : ∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω := by
  filter_upwards [hA0, hAm] with ω h0 hm
  intro t
  rw [← h0]
  exact hm zero_le

/-- The compensator is adapted, since `A = N·N − (N·N − A)`. -/
theorem stronglyAdapted_compensator {N : ℝ≥0 → Ω → ℝ} (hN : StronglyAdapted 𝔽 N)
    (hNA : StronglyAdapted 𝔽 (fun t ω => N t ω * N t ω - A t ω)) :
    ∀ u, StronglyMeasurable[𝔽 u] (A u) := by
  intro u
  have heq : A u = fun ω => N u ω * N u ω - (N u ω * N u ω - A u ω) := by
    funext ω
    ring
  rw [heq]
  exact ((hN u).mul (hN u)).sub (hNA u)

end BracketFields

/-! ## The rescaled row fields -/

theorem rescaledRow_cadlag {P : Measure Ω} {N : ℝ≥0 → Ω → ℝ}
    (hcad : ∀ᵐ ω ∂P, IsCadlag (fun t => N t ω)) (ε : ℕ → ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂P, IsCadlag (fun u => (ε n : ℝ) * N ((ε n)⁻¹ ^ 2 * u) ω) := by
  filter_upwards [hcad] with ω hω
  have h := (isCadlag_comp_const_mul hω ((ε n)⁻¹ ^ 2)).continuous_comp
    (continuous_const.mul continuous_id : Continuous fun x : ℝ => (ε n : ℝ) * x)
  exact h

theorem rescaledRow_start {P : Measure Ω} {N : ℝ≥0 → Ω → ℝ}
    (hN0 : ∀ᵐ ω ∂P, N 0 ω = 0) (ε : ℕ → ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂P, (ε n : ℝ) * N ((ε n)⁻¹ ^ 2 * 0) ω = 0 := by
  filter_upwards [hN0] with ω hω
  rw [mul_zero, hω, mul_zero]

/-! ## The global wrapper -/

/-! ## The local wrapper -/

/-- **The rescaling wrapper, local form.**  The same as `thresholdArrayInputs_rescaled` with the
three global martingale fields replaced by their local versions — the form
`HasOrdinaryEdgeBracket` delivers.  Here the scale must be positive (`hεpos`): the diffusive time
change of a localizing sequence divides by `εₙ⁻²`. -/
theorem localThresholdArrayInputs_rescaled {P : Measure Ω} [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 m) (N A : ℝ≥0 → Ω → ℝ) (C : ℝ)
    (hnull : ∀ (t : ℝ≥0) (S : Set Ω), P S = 0 → MeasurableSet[𝔽 t] S)
    (hN : MartingaleIngredients.IsLocallySquareIntegrableMartingale P 𝔽 N)
    (hNA : MartingaleIngredients.IsLocalMartingale P 𝔽 (fun t ω => N t ω * N t ω - A t ω))
    (hcad : ∀ᵐ ω ∂P, IsCadlag (fun t => N t ω))
    (hN0 : ∀ᵐ ω ∂P, N 0 ω = 0)
    (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hAc : ∀ᵐ ω ∂P, Continuous (fun t => A t ω))
    (hAm : ∀ᵐ ω ∂P, Monotone (fun t => A t ω))
    (hLLN : RescaledBracketLLN P A C)
    {ε : ℕ → ℝ≥0} (hεpos : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0)) (H : ℝ≥0) :
    LocalThresholdArrayInputs P (fun n => rescaleFiltration 𝔽 (ε n))
      (fun n u ω => (ε n : ℝ) * N ((ε n)⁻¹ ^ 2 * u) ω) (rescaledBracket A ε) H C
      (C * (H : ℝ) + 1) := by
  have hAnn := ae_nonneg_of_monotone_start hA0 hAm
  have hC : 0 ≤ C := rescaledBracketLLN_const_nonneg hAnn hLLN
  have hAad := stronglyAdapted_compensator hN.1 hNA.1
  have hε : Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hεlim, Eventually.of_forall fun n => hεpos n⟩
  refine localThresholdArrayInputs_of_rescaledBracketLLN hC (by linarith) hε ?_ ?_
    (fun n t S hS => hnull _ S hS) (rescaledRow_cadlag hcad ε)
    (rescaledRow_start hN0 ε) (rescaledBracket_start hA0) (rescaledBracket_adapted hAad)
    (rescaledBracket_continuous hAc) (rescaledBracket_monotone hAm)
    (rescaledBracket_nonneg hAnn) hLLN
  · intro n
    exact isLocallySquareIntegrableMartingale_const_mul
      (isLocallySquareIntegrableMartingale_timeScale hN (hεpos n).ne') (ε n : ℝ)
  · intro n
    have heq : (fun t ω => (ε n : ℝ) * N ((ε n)⁻¹ ^ 2 * t) ω *
          ((ε n : ℝ) * N ((ε n)⁻¹ ^ 2 * t) ω) - rescaledBracket A ε n t ω) =
        fun u ω => (ε n : ℝ) ^ 2 * (fun t ω => N t ω * N t ω - A t ω) ((ε n)⁻¹ ^ 2 * u) ω := by
      funext u ω
      simp only [rescaledBracket]
      ring
    rw [heq]
    exact isLocalMartingale_const_mul (isLocalMartingale_timeScale hNA (hεpos n).ne') _

/-! ## `harray` for one coordinate, with the centring repair -/

/-- **`harray` for one scalar coordinate, from local martingale data.**

The rows are the actual, uncentred `εₙ N(εₙ⁻² u)`.  `N` starts at a deterministic `p` (the
coordinate of the start point); the producer is applied to the centred `N − p` through
`localThresholdArrayInputs_rescaled`, and the output array is shifted back by `εₙ p` with
`localizedMartingaleArray_add_const` (the shift is bounded because a null scale sequence is
bounded, `exists_bound_of_tendsto_zero`).  The compensator of `N − p` is still `A`
(`isLocalMartingale_sub_const_compensated`). -/
theorem harray_of_local_coordinate {P : Measure Ω} [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 m) (N A : ℝ≥0 → Ω → ℝ) (p C : ℝ)
    (hnull : ∀ (t : ℝ≥0) (S : Set Ω), P S = 0 → MeasurableSet[𝔽 t] S)
    (hN : MartingaleIngredients.IsLocallySquareIntegrableMartingale P 𝔽 N)
    (hNA : MartingaleIngredients.IsLocalMartingale P 𝔽 (fun t ω => N t ω * N t ω - A t ω))
    (hcad : ∀ᵐ ω ∂P, IsCadlag (fun t => N t ω))
    (hstart : ∀ᵐ ω ∂P, N 0 ω = p)
    (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hAc : ∀ᵐ ω ∂P, Continuous (fun t => A t ω))
    (hAm : ∀ᵐ ω ∂P, Monotone (fun t => A t ω))
    (hLLN : RescaledBracketLLN P A C) :
    ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ H : ℝ≥0, Nonempty (LocalizedMartingaleArray P
        (fun n u ω => (ε n : ℝ) * N ((ε n)⁻¹ ^ 2 * u) ω) H) := by
  intro ε hεpos hεlim H
  have hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N t ω) :=
    hcad.mono fun _ h => h.isRightContinuous
  have hrA : ∀ᵐ ω ∂P, IsRightContinuous (fun t => A t ω) :=
    hAc.mono fun _ h => h.isRightContinuous
  have hNc := isLocallySquareIntegrableMartingale_sub_const hN hnull hr p
  have hNcA := isLocalMartingale_sub_const_compensated hN hNA hnull hr hrA p
  have hcadc : ∀ᵐ ω ∂P, IsCadlag (fun t => N t ω - p) := by
    filter_upwards [hcad] with ω hω
    exact hω.continuous_comp (continuous_sub_right p)
  have hstartc : ∀ᵐ ω ∂P, N 0 ω - p = 0 := by
    filter_upwards [hstart] with ω hω
    rw [hω, sub_self]
  obtain ⟨Arr⟩ := nonempty_localizedMartingaleArray_of_localThresholdInputs
    (localThresholdArrayInputs_rescaled 𝔽 (fun t ω => N t ω - p) A C hnull hNc hNcA hcadc
      hstartc hA0 hAc hAm hLLN hεpos hεlim H)
  obtain ⟨B, hB⟩ := exists_bound_of_tendsto_zero hεlim
  have hb : ∀ n, |(ε n : ℝ) * p| ≤ (B : ℝ) * |p| := by
    intro n
    rw [abs_mul, NNReal.abs_eq]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hB n) (abs_nonneg p)
  have heq : (fun n u ω => (ε n : ℝ) * N ((ε n)⁻¹ ^ 2 * u) ω) =
      fun n t ω => (ε n : ℝ) * (N ((ε n)⁻¹ ^ 2 * t) ω - p) + (ε n : ℝ) * p := by
    funext n t ω
    ring
  rw [heq]
  exact ⟨localizedMartingaleArray_add_const Arr (fun n => (ε n : ℝ) * p) ((B : ℝ) * |p|) hb⟩

end ReflectedGMS.ActualThresholdArray
