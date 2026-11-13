/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.ItoLite.OptionalStopping at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# ITO-LITE: continuous-time optional stopping, hitting times, and the glue lemma

Blueprint nodes IL-4 and IL-5 (`blueprint/THM11_BLUEPRINT.md`, §3 and §10).

Time is `ℝ≥0`, `𝓕` is an arbitrary filtration, stopping times take values in
`WithTop ℝ≥0` (mathlib's convention).

* `ItoLite.integral_mul_stoppedValue_eq_of_le` : optional sampling for a bounded martingale
  with continuous paths at a bounded stopping time, tested against bounded
  `𝓕_σ`-measurable functions (dyadic approximation from the right).
* `ItoLite.martingale_stoppedProcess_of_continuous` (IL-4) : a bounded martingale with
  continuous paths, stopped at a stopping time, is a martingale.
* `ItoLite.isStoppingTime_hittingBtwn_of_isClosed` (IL-4) : the hitting time of a closed set by
  a continuous adapted process is a stopping time.
* `ItoLite.martingale_glue` (IL-5) : `ξ (M_t - M_{t ∧ ρ})` is a martingale for bounded
  `𝓕_ρ`-measurable `ξ`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ItoLite

/-! ### Dyadic approximation from the right -/

/-- The dyadic ceiling `⌈r 2^n⌉ / 2^n`. -/
noncomputable def dyadicCeil (n : ℕ) (r : ℝ≥0) : ℝ≥0 :=
  (⌈r * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n

lemma dyadicCeil_le_iff (n : ℕ) (r u : ℝ≥0) :
    dyadicCeil n r ≤ u ↔ r ≤ (⌊u * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  unfold dyadicCeil
  rw [div_le_iff₀ h2, le_div_iff₀ h2, ← Nat.le_floor_iff zero_le, Nat.ceil_le]

lemma le_dyadicCeil (n : ℕ) (r : ℝ≥0) : r ≤ dyadicCeil n r := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  unfold dyadicCeil
  rw [le_div_iff₀ h2]
  exact Nat.le_ceil _

lemma dyadicCeil_le_add (n : ℕ) (r : ℝ≥0) : dyadicCeil n r ≤ r + (1 / 2) ^ n := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  unfold dyadicCeil
  rw [div_le_iff₀ h2, add_mul, one_div_pow, div_mul_cancel₀ _ h2.ne']
  exact (Nat.ceil_lt_add_one zero_le).le

lemma floor_div_le (n : ℕ) (u : ℝ≥0) : (⌊u * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n ≤ u := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  rw [div_le_iff₀ h2]
  exact Nat.floor_le zero_le

lemma tendsto_dyadicCeil (r : ℝ≥0) : Tendsto (fun n => dyadicCeil n r) atTop (𝓝 r) := by
  have h : Tendsto (fun n : ℕ => r + (1 / 2 : ℝ≥0) ^ n) atTop (𝓝 (r + 0)) :=
    tendsto_const_nhds.add
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num))
  rw [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun n => le_dyadicCeil n r) (fun n => dyadicCeil_le_add n r)

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 m}

lemma untopA_coe_nnreal (r : ℝ≥0) : (r : WithTop ℝ≥0).untopA = r := rfl

lemma eq_coe_untopA_of_le {σ : Ω → WithTop ℝ≥0} {t : ℝ≥0} (hle : ∀ ω, σ ω ≤ t) (ω : Ω) :
    σ ω = ((σ ω).untopA : WithTop ℝ≥0) := by
  have hne : σ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hle ω)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hr]; rfl

/-- The dyadic approximation from the right of a stopping time bounded by `t`. -/
noncomputable def approxST (σ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (n : ℕ) : Ω → WithTop ℝ≥0 :=
  fun ω => ((min (dyadicCeil n (σ ω).untopA) t : ℝ≥0) : WithTop ℝ≥0)

lemma isStoppingTime_approxST {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ) {t : ℝ≥0}
    (hle : ∀ ω, σ ω ≤ t) (n : ℕ) : IsStoppingTime 𝓕 (approxST σ t n) := by
  intro u
  by_cases htu : t ≤ u
  · have : {ω | approxST σ t n ω ≤ (u : WithTop ℝ≥0)} = Set.univ := by
      ext ω
      simp only [approxST, Set.mem_ofPred_eq, WithTop.coe_le_coe, Set.mem_univ, iff_true]
      exact (min_le_right _ _).trans htu
    rw [this]; exact MeasurableSet.univ
  · have : {ω | approxST σ t n ω ≤ (u : WithTop ℝ≥0)} =
        {ω | σ ω ≤ (((⌊u * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [approxST, Set.mem_ofPred_eq, WithTop.coe_le_coe, min_le_iff, htu, or_false]
      rw [dyadicCeil_le_iff, eq_coe_untopA_of_le hle ω, WithTop.coe_le_coe, untopA_coe_nnreal]
    rw [this]
    exact 𝓕.mono (floor_div_le n u) _ (hσ _)

lemma countable_range_approxST (σ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (n : ℕ) :
    (Set.range (approxST σ t n)).Countable := by
  refine (Set.countable_range
    (fun k : ℕ => ((min ((k : ℝ≥0) / 2 ^ n) t : ℝ≥0) : WithTop ℝ≥0))).mono ?_
  rintro _ ⟨ω, rfl⟩
  exact ⟨⌈(σ ω).untopA * 2 ^ n⌉₊, rfl⟩

lemma le_approxST {σ : Ω → WithTop ℝ≥0} {t : ℝ≥0} (hle : ∀ ω, σ ω ≤ t) (n : ℕ) :
    σ ≤ approxST σ t n := by
  intro ω
  rw [eq_coe_untopA_of_le hle ω]
  simp only [approxST, WithTop.coe_le_coe, le_min_iff]
  refine ⟨le_dyadicCeil n _, ?_⟩
  have := hle ω
  rw [eq_coe_untopA_of_le hle ω, WithTop.coe_le_coe] at this
  exact this

lemma approxST_le (σ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (n : ℕ) (ω : Ω) :
    approxST σ t n ω ≤ t := WithTop.coe_le_coe.mpr (min_le_right _ _)

lemma tendsto_approxST {σ : Ω → WithTop ℝ≥0} {t : ℝ≥0} (hle : ∀ ω, σ ω ≤ t) (ω : Ω) :
    Tendsto (fun n => (approxST σ t n ω).untopA) atTop (𝓝 (σ ω).untopA) := by
  have ht : (σ ω).untopA ≤ t := by
    have := hle ω
    rwa [eq_coe_untopA_of_le hle ω, WithTop.coe_le_coe] at this
  have h := (tendsto_dyadicCeil (σ ω).untopA).min (tendsto_const_nhds (x := t))
  rw [min_eq_left ht] at h
  exact h

/-! ### Boundedness and integrability helpers -/

lemma integrable_of_bound_abs [IsFiniteMeasure P] {f : Ω → ℝ} (hf : StronglyMeasurable f)
    {K : ℝ} (hK : ∀ ω, |f ω| ≤ K) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable K
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hK ω)

lemma abs_mul_le_of_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-! ### Optional sampling at bounded stopping times -/

/-- **Optional sampling in continuous time.** For a bounded martingale with continuous paths and a
stopping time `σ ≤ t`, `E[Y M_σ] = E[Y M_t]` for every bounded `𝓕_σ`-measurable `Y`. -/
theorem integral_mul_stoppedValue_eq_of_le [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝓕 P) (hc : ∀ ω, Continuous (M · ω)) {C : ℝ}
    (hbd : ∀ t ω, |M t ω| ≤ C) {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ) {t : ℝ≥0}
    (hle : ∀ ω, σ ω ≤ t) {Y : Ω → ℝ} (hY : Measurable[hσ.measurableSpace] Y) {CY : ℝ}
    (hYb : ∀ ω, |Y ω| ≤ CY) :
    ∫ ω, Y ω * stoppedValue M σ ω ∂P = ∫ ω, Y ω * M t ω ∂P := by
  have hprog : IsStronglyProgressive 𝓕 M := hM.stronglyAdapted.isStronglyProgressive_of_continuous hc
  have hσn := isStoppingTime_approxST hσ hle
  have hYm : Measurable Y := hY.mono hσ.measurableSpace_le le_rfl
  have hMt_int : Integrable (M t) P := hM.integrable t
  have hYMt_int : Integrable (Y * M t) P :=
    integrable_of_bound_abs (hYm.stronglyMeasurable.mul (hM.stronglyMeasurable t |>.mono (𝓕.le t)))
      (fun ω => abs_mul_le_of_le (hYb ω) (hbd t ω))
  -- the identity along the approximating sequence
  have key : ∀ n, ∫ ω, Y ω * stoppedValue M (approxST σ t n) ω ∂P = ∫ ω, Y ω * M t ω ∂P := by
    intro n
    have h1 := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hσn n)
      (approxST_le σ t n) (countable_range_approxST σ t n)
    have hYn : StronglyMeasurable[(hσn n).measurableSpace] Y :=
      (hY.mono (hσ.measurableSpace_mono (hσn n) (le_approxST hle n)) le_rfl).stronglyMeasurable
    have h2 := condExp_mul_of_stronglyMeasurable_left hYn hYMt_int hMt_int
    calc ∫ ω, Y ω * stoppedValue M (approxST σ t n) ω ∂P
        = ∫ ω, (Y * P[M t | (hσn n).measurableSpace]) ω ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [h1] with ω hω
          simp [hω]
      _ = ∫ ω, (P[Y * M t | (hσn n).measurableSpace]) ω ∂P := integral_congr_ae h2.symm
      _ = ∫ ω, (Y * M t) ω ∂P := integral_condExp (hσn n).measurableSpace_le
      _ = ∫ ω, Y ω * M t ω ∂P := rfl
  -- pass to the limit
  have hlim : Tendsto (fun n => ∫ ω, Y ω * stoppedValue M (approxST σ t n) ω ∂P) atTop
      (𝓝 (∫ ω, Y ω * stoppedValue M σ ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => CY * C) (fun n => ?_)
      (integrable_const _) (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · exact (hYm.mul ((measurable_stoppedValue hprog (hσn n)).mono
        (hσn n).measurableSpace_le le_rfl)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact abs_mul_le_of_le (hYb ω) (hbd _ ω)
    · refine Tendsto.const_mul (Y ω) ?_
      exact ((hc ω).tendsto _).comp (tendsto_approxST hle ω)
  simp_rw [key] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

/-- Optional sampling at `σ ∧ t` for an arbitrary stopping time `σ`: for bounded `𝓕_σ`-measurable
`Y`, `E[Y M_{σ ∧ t}] = E[Y M_t]`. -/
theorem integral_mul_stoppedProcess_eq [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝓕 P) (hc : ∀ ω, Continuous (M · ω)) {C : ℝ}
    (hbd : ∀ t ω, |M t ω| ≤ C) {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ) (t : ℝ≥0)
    {Y : Ω → ℝ} (hY : Measurable[hσ.measurableSpace] Y) {CY : ℝ} (hYb : ∀ ω, |Y ω| ≤ CY) :
    ∫ ω, Y ω * stoppedProcess M σ t ω ∂P = ∫ ω, Y ω * M t ω ∂P := by
  set τ' : Ω → WithTop ℝ≥0 := fun ω => min (t : WithTop ℝ≥0) (σ ω) with hτ'_def
  have hτ' : IsStoppingTime 𝓕 τ' := (isStoppingTime_const 𝓕 t).min hσ
  set s : Set Ω := {ω | σ ω ≤ t} with hs_def
  set Z : Ω → ℝ := s.indicator Y with hZ_def
  have hZ : StronglyMeasurable[hτ'.measurableSpace] Z := by
    refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on
      (m := hσ.measurableSpace) (hσ.measurableSet_le' t) (fun u hu => ?_)
      (hY.stronglyMeasurable.indicator (hσ.measurableSet_le' t))
      (fun ω hω => Set.indicator_of_notMem hω _)
    refine ⟨hu.1, fun i => ?_⟩
    have : s ∩ u ∩ {ω | τ' ω ≤ i} = s ∩ u ∩ {ω | σ ω ≤ i} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hs_def, hτ'_def]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, by rwa [min_eq_right h1] at h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, by rwa [min_eq_right h1]⟩
    rw [this]; exact hu.2 i
  have hZb : ∀ ω, |Z ω| ≤ CY := fun ω => by
    by_cases h : ω ∈ s
    · simp [hZ_def, Set.indicator_of_mem h, hYb ω]
    · simp only [hZ_def, Set.indicator_of_notMem h, abs_zero]
      exact (abs_nonneg _).trans (hYb ω)
  have hcore := integral_mul_stoppedValue_eq_of_le hM hc hbd hτ' (fun ω => min_le_left _ _)
    hZ.measurable hZb
  have hYm : Measurable Y := hY.mono hσ.measurableSpace_le le_rfl
  have hZm : Measurable Z := hZ.measurable.mono hτ'.measurableSpace_le le_rfl
  have hsp : StronglyMeasurable (stoppedProcess M σ t) :=
    (hM.stronglyAdapted.stronglyMeasurable_stoppedProcess hc hσ t)
  have hMt : StronglyMeasurable (M t) := (hM.stronglyMeasurable t).mono (𝓕.le t)
  have hspb : ∀ ω, |stoppedProcess M σ t ω| ≤ C := fun ω => hbd _ ω
  have i1 : Integrable (fun ω => Y ω * stoppedProcess M σ t ω) P :=
    integrable_of_bound_abs (hYm.stronglyMeasurable.mul hsp)
      (fun ω => abs_mul_le_of_le (hYb ω) (hspb ω))
  have i2 : Integrable (fun ω => Y ω * M t ω) P :=
    integrable_of_bound_abs (hYm.stronglyMeasurable.mul hMt)
      (fun ω => abs_mul_le_of_le (hYb ω) (hbd t ω))
  have i3 : Integrable (fun ω => Z ω * stoppedProcess M σ t ω) P :=
    integrable_of_bound_abs (hZm.stronglyMeasurable.mul hsp)
      (fun ω => abs_mul_le_of_le (hZb ω) (hspb ω))
  have i4 : Integrable (fun ω => Z ω * M t ω) P :=
    integrable_of_bound_abs (hZm.stronglyMeasurable.mul hMt)
      (fun ω => abs_mul_le_of_le (hZb ω) (hbd t ω))
  have hpt : ∀ ω, Y ω * stoppedProcess M σ t ω - Y ω * M t ω
      = Z ω * stoppedProcess M σ t ω - Z ω * M t ω := by
    intro ω
    by_cases h : ω ∈ s
    · simp [hZ_def, Set.indicator_of_mem h]
    · have hlt : (t : WithTop ℝ≥0) ≤ σ ω := (lt_of_not_ge h).le
      have : stoppedProcess M σ t ω = M t ω := by
        simp only [stoppedProcess, min_eq_left hlt]; rfl
      simp [this]
  have hstop : stoppedValue M τ' = stoppedProcess M σ t := rfl
  rw [hstop] at hcore
  have : ∫ ω, Y ω * stoppedProcess M σ t ω ∂P - ∫ ω, Y ω * M t ω ∂P = 0 := by
    rw [← integral_sub i1 i2]
    simp_rw [hpt]
    rw [integral_sub i3 i4, hcore, sub_self]
  linarith

/-! ### IL-4: stopped martingales -/

lemma setIntegral_eq_integral_indicator_one_mul {A : Set Ω} (hA : MeasurableSet A)
    (f : Ω → ℝ) : ∫ ω in A, f ω ∂P = ∫ ω, A.indicator 1 ω * f ω ∂P := by
  rw [← integral_indicator hA]
  congr 1
  ext ω
  by_cases h : ω ∈ A <;> simp [h]

/-- Pointwise identity: with `π = max σ s` and `s ≤ t`,
`M_{π ∧ t} - M_s = M_{σ ∧ t} - M_{σ ∧ s}`. -/
lemma stoppedProcess_max_const_sub (M : ℝ≥0 → Ω → ℝ) (σ : Ω → WithTop ℝ≥0) {s t : ℝ≥0}
    (hst : s ≤ t) (ω : Ω) :
    stoppedProcess M (fun ω => max (σ ω) s) t ω - M s ω
      = stoppedProcess M σ t ω - stoppedProcess M σ s ω := by
  have hst' : (s : WithTop ℝ≥0) ≤ t := WithTop.coe_le_coe.mpr hst
  simp only [stoppedProcess]
  rcases le_total (σ ω) s with h1 | h1
  · rw [max_eq_right h1, min_eq_right hst', min_eq_right h1, min_eq_right (h1.trans hst')]
    simp only [untopA_coe_nnreal, sub_self]
  · rw [max_eq_left h1, min_eq_left h1, untopA_coe_nnreal]

/-- A bounded strongly adapted process whose set integrals over `𝓕_s`-sets do not depend on the
time `t ≥ s` is a martingale. -/
lemma martingale_of_setIntegral_eq_nnreal [IsFiniteMeasure P] {g : ℝ≥0 → Ω → ℝ}
    (hg : StronglyAdapted 𝓕 g) (hint : ∀ t, Integrable (g t) P)
    (h : ∀ s t, s ≤ t → ∀ A, MeasurableSet[𝓕 s] A → ∫ ω in A, g s ω ∂P = ∫ ω in A, g t ω ∂P) :
    Martingale g 𝓕 P :=
  ⟨hg, fun s t hst => (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hint t)
    (fun _ _ _ => (hint s).integrableOn) (fun A hA _ => h s t hst A hA)
    (hg s).aestronglyMeasurable).symm⟩

/-- **IL-4 (optional stopping).** A bounded martingale with continuous paths, stopped at a
stopping time, is a martingale. -/
theorem martingale_stoppedProcess_of_continuous [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝓕 P) (hc : ∀ ω, Continuous (M · ω)) {C : ℝ}
    (hbd : ∀ t ω, |M t ω| ≤ C) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) :
    Martingale (stoppedProcess M τ) 𝓕 P := by
  have hsp : ∀ t, StronglyMeasurable (stoppedProcess M τ t) := fun t =>
    hM.stronglyAdapted.stronglyMeasurable_stoppedProcess hc hτ t
  have hint : ∀ t, Integrable (stoppedProcess M τ t) P := fun t =>
    integrable_of_bound_abs (hsp t) (fun ω => hbd _ ω)
  refine martingale_of_setIntegral_eq_nnreal (hM.stronglyAdapted.stoppedProcess hc hτ) hint ?_
  intro s t hst A hA
  have hAm : MeasurableSet A := 𝓕.le s _ hA
  have hπ : IsStoppingTime 𝓕 (fun ω => max (τ ω) s) := hτ.max_const s
  have h1A : Measurable[hπ.measurableSpace] (A.indicator (1 : Ω → ℝ)) :=
    (stronglyMeasurable_const.indicator
      (hπ.le_measurableSpace_of_const_le (fun ω => le_max_right _ _) _ hA)).measurable
  have h1Ab : ∀ ω, |A.indicator (1 : Ω → ℝ) ω| ≤ 1 := fun ω => by
    by_cases h : ω ∈ A <;> simp [h]
  have hos := integral_mul_stoppedProcess_eq hM hc hbd hπ t h1A h1Ab
  have hmart : ∫ ω in A, M s ω ∂P = ∫ ω in A, M t ω ∂P := by
    have h1As : Measurable[(isStoppingTime_const 𝓕 s).measurableSpace]
        (A.indicator (1 : Ω → ℝ)) := by
      rw [IsStoppingTime.measurableSpace_const]
      exact (stronglyMeasurable_const.indicator hA).measurable
    have hos' := integral_mul_stoppedProcess_eq hM hc hbd (isStoppingTime_const 𝓕 s) t h1As h1Ab
    have : stoppedProcess M (fun _ => (s : WithTop ℝ≥0)) t = M s := by
      ext ω; simp only [stoppedProcess, min_eq_right (WithTop.coe_le_coe.mpr hst)]; rfl
    rw [this] at hos'
    rw [setIntegral_eq_integral_indicator_one_mul hAm, setIntegral_eq_integral_indicator_one_mul hAm,
      hos']
  have hMs : Integrable (M s) P := hM.integrable s
  have hMt : Integrable (M t) P := hM.integrable t
  have hπt : Integrable (stoppedProcess M (fun ω => max (τ ω) s) t) P :=
    integrable_of_bound_abs (hM.stronglyAdapted.stronglyMeasurable_stoppedProcess hc hπ t)
      (fun ω => hbd _ ω)
  have hπA : ∫ ω in A, stoppedProcess M (fun ω => max (τ ω) s) t ω ∂P = ∫ ω in A, M t ω ∂P := by
    rw [setIntegral_eq_integral_indicator_one_mul hAm, setIntegral_eq_integral_indicator_one_mul hAm,
      hos]
  have hdiff : ∫ ω in A, (stoppedProcess M τ t ω - stoppedProcess M τ s ω) ∂P = 0 := by
    simp_rw [← stoppedProcess_max_const_sub M τ hst]
    rw [integral_sub hπt.integrableOn hMs.integrableOn, hπA, hmart, sub_self]
  rw [integral_sub (hint t).integrableOn (hint s).integrableOn] at hdiff
  linarith

/-- IL-4, real-valued stopping-time form: `t ↦ M (min t (τ ω)) ω` is a martingale. -/
theorem martingale_stopped_of_continuous [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝓕 P) (hc : ∀ ω, Continuous (M · ω)) {C : ℝ}
    (hbd : ∀ t ω, |M t ω| ≤ C) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) :
    Martingale (fun t ω => M (min t (τ ω)) ω) 𝓕 P := by
  have h := martingale_stoppedProcess_of_continuous hM hc hbd hτ
  have : stoppedProcess M (fun ω => (τ ω : WithTop ℝ≥0)) = fun t ω => M (min t (τ ω)) ω := by
    ext t ω
    simp only [stoppedProcess, ← WithTop.coe_min]
    rfl
  rwa [this] at h

/-! ### IL-4: hitting times of closed sets -/

/-- **IL-4 (hitting times).** The hitting time of a closed set by a continuous adapted process,
capped at `T`, is a stopping time. -/
theorem isStoppingTime_hittingBtwn_of_isClosed {β : Type*} [PseudoMetricSpace β]
    [MeasurableSpace β] [OpensMeasurableSpace β] {U : ℝ≥0 → Ω → β} (hU : Adapted 𝓕 U)
    (hc : ∀ ω, Continuous (U · ω)) {K : Set β} (hK : IsClosed K) (T : ℝ≥0) :
    IsStoppingTime 𝓕 (fun ω => ((hittingBtwn U K 0 T ω : ℝ≥0) : WithTop ℝ≥0)) := by
  intro u
  simp only [WithTop.coe_le_coe]
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp only [hittingBtwn_empty]
    exact MeasurableSet.const _
  by_cases hTu : T ≤ u
  · have : {ω | hittingBtwn U K 0 T ω ≤ u} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (hittingBtwn_le ω).trans hTu
    rw [this]; exact MeasurableSet.univ
  have huT : u < T := lt_of_not_ge hTu
  -- step 1: `hit ≤ u` iff the path meets `K` during `[0, u]`
  have step1 : ∀ ω, hittingBtwn U K 0 T ω ≤ u ↔ ∃ j ∈ Set.Icc 0 u, U j ω ∈ K := by
    intro ω
    constructor
    · intro h
      by_cases hex : ∃ j ∈ Set.Icc 0 T, U j ω ∈ K
      · set S : Set ℝ≥0 := Set.Icc 0 T ∩ {i | U i ω ∈ K} with hS
        have hSc : IsClosed S := isClosed_Icc.inter (hK.preimage (hc ω))
        have hSne : S.Nonempty := by
          obtain ⟨j, hj, hjK⟩ := hex; exact ⟨j, hj, hjK⟩
        have hmem := hSc.csInf_mem hSne (OrderBot.bddBelow S)
        have heq : hittingBtwn U K 0 T ω = sInf S := by
          simp only [hittingBtwn, hex, ↓reduceIte, hS]
        rw [heq] at h
        exact ⟨sInf S, ⟨zero_le, h⟩, hmem.2⟩
      · have heq : hittingBtwn U K 0 T ω = T := by
          simp only [hittingBtwn, hex, ↓reduceIte]
        rw [heq] at h
        exact absurd h (not_le.mpr huT)
    · rintro ⟨j, hj, hjK⟩
      exact (hittingBtwn_le_of_mem hj.1 (hj.2.trans huT.le) hjK).trans hj.2
  -- step 2: a countable description
  obtain ⟨D, hDc, hDsub, hDdense⟩ :=
    TopologicalSpace.exists_countable_dense_subset (Set.Icc (0 : ℝ≥0) u)
  have step2 : ∀ ω, (∃ j ∈ Set.Icc 0 u, U j ω ∈ K) ↔
      ∀ k : ℕ, ∃ q ∈ D, Metric.infDist (U q ω) K < 1 / ((k : ℝ) + 1) := by
    intro ω
    constructor
    · rintro ⟨j, hj, hjK⟩ k
      have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      obtain ⟨δ, hδ, hδU⟩ := Metric.continuous_iff.mp (hc ω) j _ hε
      obtain ⟨q, hqD, hq⟩ := Metric.mem_closure_iff.mp (hDdense hj) δ hδ
      refine ⟨q, hqD, ?_⟩
      calc Metric.infDist (U q ω) K ≤ dist (U q ω) (U j ω) := Metric.infDist_le_dist_of_mem hjK
        _ < _ := hδU q (by rw [dist_comm]; exact hq)
    · intro h
      choose q hqD hq using h
      obtain ⟨a, ha, φ, hφ, hlim⟩ :=
        (isCompact_Icc (a := (0 : ℝ≥0)) (b := u)).tendsto_subseq (fun n => hDsub (hqD n))
      have h1 : Tendsto (fun n => Metric.infDist (U (q (φ n)) ω) K) atTop
          (𝓝 (Metric.infDist (U a ω) K)) :=
        (((Metric.continuous_infDist_pt K).comp (hc ω)).tendsto a).comp hlim
      have h2 : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
      have hle : Metric.infDist (U a ω) K ≤ 0 :=
        le_of_tendsto_of_tendsto' h1 h2 (fun n => (hq (φ n)).le)
      refine ⟨a, ha, ?_⟩
      rw [hK.mem_iff_infDist_zero hKne]
      exact le_antisymm hle Metric.infDist_nonneg
  have hset : {ω | hittingBtwn U K 0 T ω ≤ u} =
      ⋂ k : ℕ, ⋃ q ∈ D, {ω | Metric.infDist (U q ω) K < 1 / ((k : ℝ) + 1)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
    exact (step1 ω).trans (step2 ω)
  rw [hset]
  refine MeasurableSet.iInter fun k => MeasurableSet.biUnion hDc fun q hq => ?_
  have hUq : Measurable[𝓕 u] (U q) := (hU q).mono (𝓕.mono (hDsub hq).2) le_rfl
  exact measurableSet_lt ((Metric.continuous_infDist_pt K).measurable.comp hUq) measurable_const

/-! ### IL-5: the glue lemma -/

/-- **IL-5 (glue).** For a bounded martingale `M` with continuous paths, a stopping time `ρ` and a
bounded `𝓕_ρ`-measurable `ξ`, the process `ξ (M_t - M_{t ∧ ρ})` is a martingale. -/
theorem martingale_glue [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝓕 P) (hc : ∀ ω, Continuous (M · ω)) {C : ℝ}
    (hbd : ∀ t ω, |M t ω| ≤ C) {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓕 ρ) {ξ : Ω → ℝ}
    (hξ : Measurable[hρ.measurableSpace] ξ) {Cξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Cξ) :
    Martingale (fun t ω => ξ ω * (M t ω - stoppedProcess M ρ t ω)) 𝓕 P := by
  have hξm : Measurable ξ := hξ.mono hρ.measurableSpace_le le_rfl
  have hsp : ∀ t, StronglyMeasurable (stoppedProcess M ρ t) := fun t =>
    hM.stronglyAdapted.stronglyMeasurable_stoppedProcess hc hρ t
  have hspA := hM.stronglyAdapted.stoppedProcess hc hρ
  have hWb : ∀ t ω, |ξ ω * (M t ω - stoppedProcess M ρ t ω)| ≤ Cξ * (C + C) := fun t ω =>
    abs_mul_le_of_le (hξb ω) ((abs_sub _ _).trans (add_le_add (hbd t ω) (hbd _ ω)))
  have hint : ∀ t, Integrable (fun ω => ξ ω * (M t ω - stoppedProcess M ρ t ω)) P := fun t =>
    integrable_of_bound_abs (hξm.stronglyMeasurable.mul
      (((hM.stronglyMeasurable t).mono (𝓕.le t)).sub (hsp t))) (hWb t)
  -- adaptedness
  have hadapt : StronglyAdapted 𝓕 (fun t ω => ξ ω * (M t ω - stoppedProcess M ρ t ω)) := by
    intro t
    set s : Set Ω := {ω | ρ ω ≤ t}
    have hZ : StronglyMeasurable[𝓕 t] (s.indicator ξ) := by
      refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on
        (m := hρ.measurableSpace) (hρ.measurableSet_le' t) (fun u hu => ?_)
        (hξ.stronglyMeasurable.indicator (hρ.measurableSet_le' t))
        (fun ω hω => Set.indicator_of_notMem hω _)
      have := hu.2 t
      rwa [Set.inter_eq_left.mpr Set.inter_subset_left] at this
    have hprod : StronglyMeasurable[𝓕 t]
        (fun ω => s.indicator ξ ω * (M t ω - stoppedProcess M ρ t ω)) :=
      hZ.mul ((hM.stronglyMeasurable t).sub (hspA t))
    have heq : (fun ω => ξ ω * (M t ω - stoppedProcess M ρ t ω))
        = fun ω => s.indicator ξ ω * (M t ω - stoppedProcess M ρ t ω) := by
      funext ω
      by_cases h : ω ∈ s
      · rw [Set.indicator_of_mem h]
      · have hlt : (t : WithTop ℝ≥0) ≤ ρ ω := (lt_of_not_ge h).le
        have : stoppedProcess M ρ t ω = M t ω := by
          simp only [stoppedProcess, min_eq_left hlt]; rfl
        rw [this]; simp
    show StronglyMeasurable[𝓕 t] (fun ω => ξ ω * (M t ω - stoppedProcess M ρ t ω))
    rw [heq]; exact hprod
  -- the martingale property
  refine martingale_of_setIntegral_eq_nnreal hadapt hint ?_
  intro s t hst A hA
  have hAm : MeasurableSet A := 𝓕.le s _ hA
  have hπ : IsStoppingTime 𝓕 (fun ω => max (ρ ω) s) := hρ.max_const s
  have hY : Measurable[hπ.measurableSpace] (fun ω => A.indicator (1 : Ω → ℝ) ω * ξ ω) :=
    ((stronglyMeasurable_const.indicator
      (hπ.le_measurableSpace_of_const_le (fun ω => le_max_right _ _) _ hA)).mul
      (hξ.mono (hρ.measurableSpace_mono hπ (fun ω => le_max_left _ _))
        le_rfl).stronglyMeasurable).measurable
  have hYb : ∀ ω, |A.indicator (1 : Ω → ℝ) ω * ξ ω| ≤ 1 * Cξ := fun ω =>
    abs_mul_le_of_le (by by_cases h : ω ∈ A <;> simp [h]) (hξb ω)
  have hos := integral_mul_stoppedProcess_eq hM hc hbd hπ t hY hYb
  beta_reduce at hos
  have hYm : Measurable (fun ω => A.indicator (1 : Ω → ℝ) ω * ξ ω) :=
    hY.mono hπ.measurableSpace_le le_rfl
  have i1 : Integrable (fun ω => A.indicator (1 : Ω → ℝ) ω * ξ ω * M t ω) P :=
    integrable_of_bound_abs (hYm.stronglyMeasurable.mul ((hM.stronglyMeasurable t).mono (𝓕.le t)))
      (fun ω => abs_mul_le_of_le (hYb ω) (hbd t ω))
  have i2 : Integrable (fun ω => A.indicator (1 : Ω → ℝ) ω * ξ ω *
      stoppedProcess M (fun ω => max (ρ ω) s) t ω) P :=
    integrable_of_bound_abs (hYm.stronglyMeasurable.mul
      (hM.stronglyAdapted.stronglyMeasurable_stoppedProcess hc hπ t))
      (fun ω => abs_mul_le_of_le (hYb ω) (hbd _ ω))
  have hpt : ∀ ω, A.indicator (1 : Ω → ℝ) ω * (ξ ω * (M t ω - stoppedProcess M ρ t ω)
      - ξ ω * (M s ω - stoppedProcess M ρ s ω))
      = A.indicator (1 : Ω → ℝ) ω * ξ ω * M t ω
        - A.indicator (1 : Ω → ℝ) ω * ξ ω * stoppedProcess M (fun ω => max (ρ ω) s) t ω := by
    intro ω
    have h := stoppedProcess_max_const_sub M ρ hst ω
    linear_combination (A.indicator (1 : Ω → ℝ) ω * ξ ω) * h
  have hdiff : ∫ ω in A, (ξ ω * (M t ω - stoppedProcess M ρ t ω)
      - ξ ω * (M s ω - stoppedProcess M ρ s ω)) ∂P = 0 := by
    rw [setIntegral_eq_integral_indicator_one_mul hAm]
    simp_rw [hpt]
    rw [integral_sub i1 i2, hos, sub_self]
  rw [integral_sub (hint t).integrableOn (hint s).integrableOn] at hdiff
  linarith

end ItoLite
end QuantumZipper
