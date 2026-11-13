/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.WindowModulusUniformScales at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.DiffusiveModulusTranslation
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Window moduli along every null sequence of scales give a window modulus uniform over
# a continuum of scales

`ReflectedGMS.DiffusiveModulusTranslation.rescaledWindowModulusTail_of_diffusive_window_tails`
reduces the consumer input `RescaledWindowModulusTail μ T` of
`TwoClockScalingLimitReduction.twoClockScalingLimit_of_window_modulus_of_finiteDimensional`
to a bound, **uniform over the continuum of scales `ε ∈ T`**, on the probability that a path
of the unrescaled law `μ` oscillates by more than `c / ε` across a time lag `< ε⁻² d` inside
the window `[0, ε⁻² m]`.

The martingale-array estimates of this development
(`MartingaleLimit.uniform_grid_oscillation_probability_le`) are instead indexed by `ℕ` and
hold only for all *sufficiently large* indices (`∀ᶠ n in atTop`).  This file bridges the
two, with no reference to the reflected walk:

* **small scales** — a contradiction argument: if no lag worked uniformly on some interval
  `(0, a]`, one could pick scales `ε_k ≤ 1/(k+1)` failing at lag `1/(k+1)`; the sequential
  hypothesis along the null sequence `ε_k` provides one lag `d > 0` good for all large `k`,
  and monotonicity of the failure set in the lag gives a contradiction
  (`exists_scale_lag_of_sequential`, stated for an abstract failure function);
* **scales bounded away from `0`** — for `a ≤ ε ≤ 1` the dilated failure set at scale `ε`
  sits inside the one at scale `a` with threshold `c`
  (`diffusive_windowModulusFailure_subset_of_le_scale`), and a *single* finite law on
  continuous paths has vanishing window-modulus failure as the lag decreases, because each
  path is uniformly continuous on the compact window
  (`finite_measure_windowModulusFailure_tail`).

This file proves no tightness estimate.  Its hypothesis `hseq` is the sequential form in
which a martingale functional-limit argument delivers the modulus ("apply the sequential
theorem to an arbitrary sequence `ε ↓ 0`", manuscript proof of `p:thm:areaclt`).

## Main results

* `windowModulusFailure_mono`, `isOpen_windowModulusFailure`,
  `measurableSet_windowModulusFailure` — monotonicity and Borel measurability of the
  window failure set for an arbitrary real window.
* `finite_measure_windowModulusFailure_tail` — one finite law has a window modulus.
* `exists_scale_lag_of_sequential` — the abstract sequential-to-uniform principle.
* `diffusive_window_tail_uniform_of_sequential` — dilated window moduli uniform over
  `ε ∈ (0, 1]` from dilated window moduli along every positive null sequence.
* `rescaledWindowModulusTail_Ioc_of_sequential` — the consumer's
  `RescaledWindowModulusTail μ (Set.Ioc 0 1)`, with `Ioc_zero_one_mem_nhdsWithin`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.WindowModulusUniformScales

open ReflectedGMS.MartingaleLimit
open ReflectedGMS.TwoClockScalingLimitReduction
open ReflectedGMS.DiffusiveModulusTranslation

/-! ## The sequential-to-uniform principle, for an abstract failure function -/

/-- **Sequential eventual bounds along every positive null sequence of scales give one lag
that works on a whole interval of small scales.**

`p ε d` is an abstract failure quantity at scale `ε` and lag `d`, monotone in the lag.
Proof by contradiction: otherwise pick `0 < ε_k ≤ 1/(k+1)` with `η < p ε_k (1/(k+1))`;
the hypothesis along the null sequence `ε_k` gives a lag `d > 0` with `p ε_k d ≤ η` for
all large `k`, while `1/(k+1) ≤ d` eventually. -/
theorem exists_scale_lag_of_sequential {p : ℝ≥0 → ℝ → ℝ≥0∞} {η : ℝ≥0∞}
    (hmono : ∀ (ε : ℝ≥0) (d d' : ℝ), d ≤ d' → p ε d ≤ p ε d')
    (hseq : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∃ d : ℝ, 0 < d ∧ ∀ᶠ n in atTop, p (ε n) d ≤ η) :
    ∃ a : ℝ, 0 < a ∧ ∃ d : ℝ, 0 < d ∧
      ∀ ε : ℝ≥0, 0 < ε → (ε : ℝ) ≤ a → p ε d ≤ η := by
  by_contra hcon
  push_neg at hcon
  have hpick : ∀ k : ℕ, ∃ ε : ℝ≥0, 0 < ε ∧ (ε : ℝ) ≤ 1 / ((k : ℝ) + 1) ∧
      η < p ε (1 / ((k : ℝ) + 1)) := fun k =>
    hcon (1 / ((k : ℝ) + 1)) (by positivity) (1 / ((k : ℝ) + 1)) (by positivity)
  choose ε hεpos hεle hεbad using hpick
  have hreal : Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (fun k => (ε k).coe_nonneg) hεle
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    rw [← NNReal.tendsto_coe, NNReal.coe_zero]
    exact hreal
  obtain ⟨d, hd, hev⟩ := hseq ε hεpos hεlim
  have hlag : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) ≤ d :=
    ((tendsto_order.1 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 d hd).mono
      fun _ hk => hk.le
  obtain ⟨k, hk, hkd⟩ := (hev.and hlag).exists
  exact (not_le.mpr (hεbad k)) ((hmono (ε k) _ _ hkd).trans hk)

/-! ## The window failure set on an arbitrary real window -/

section Window

variable {E : Type*} [MetricSpace E] [ProperSpace E]

/-- The window failure set grows with the window and the lag and shrinks with the
threshold. -/
theorem windowModulusFailure_mono {b b' : ℝ≥0} {a a' δ δ' : ℝ}
    (hb : b ≤ b') (ha : a' ≤ a) (hδ : δ ≤ δ') :
    windowModulusFailure (E := E) b a δ ⊆ windowModulusFailure (E := E) b' a' δ' := by
  intro f hf
  obtain ⟨s, hs, t, ht, hst, hlt⟩ := hf
  exact ⟨s, hs.trans hb, t, ht.trans hb, hst.trans_le hδ, ha.trans_lt hlt⟩

/-- The window failure set is open (a union of open two-point evaluation conditions). -/
theorem isOpen_windowModulusFailure (b : ℝ≥0) (a δ : ℝ) :
    IsOpen (windowModulusFailure (E := E) b a δ) := by
  rw [isOpen_iff_forall_mem_open]
  intro f hf
  obtain ⟨s, hs, t, ht, hst, hlt⟩ := hf
  refine ⟨{g : C(ℝ≥0, E) | a < dist (g s) (g t)}, ?_, ?_, hlt⟩
  · intro g hg
    exact ⟨s, hs, t, ht, hst, hg⟩
  · exact isOpen_lt continuous_const
      ((continuous_eval_const s).dist (continuous_eval_const t))

theorem measurableSet_windowModulusFailure (b : ℝ≥0) (a δ : ℝ) :
    MeasurableSet (windowModulusFailure (E := E) b a δ) :=
  (isOpen_windowModulusFailure b a δ).measurableSet

/-- No continuous path fails the window modulus at every lag `1/(k+1)`: it is uniformly
continuous on the compact window `[0, b]`. -/
theorem iInter_windowModulusFailure_eq_empty (b : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    ⋂ k : ℕ, windowModulusFailure (E := E) b a (1 / ((k : ℝ) + 1)) = ∅ := by
  ext f
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro hf
  have huc : UniformContinuousOn f (Set.Icc (0 : ℝ≥0) b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous f.continuous.continuousOn
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuousOn_iff.1 huc a ha
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  obtain ⟨s, hs, t, ht, hst, hlt⟩ := hf k
  exact lt_asymm hlt (hfδ s ⟨zero_le, hs⟩ t ⟨zero_le, ht⟩ (hst.trans hk))

/-- **A single finite law on continuous paths has a window modulus.** -/
theorem finite_measure_windowModulusFailure_tail (μ : Measure C(ℝ≥0, E)) [IsFiniteMeasure μ]
    (b : ℝ≥0) {a : ℝ} (ha : 0 < a) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ μ (windowModulusFailure (E := E) b a δ) ≤ η := by
  let A : ℕ → Set C(ℝ≥0, E) := fun k =>
    windowModulusFailure (E := E) b a (1 / ((k : ℝ) + 1))
  have hAmeas : ∀ k, NullMeasurableSet (A k) μ := fun k =>
    (measurableSet_windowModulusFailure b a (1 / ((k : ℝ) + 1))).nullMeasurableSet
  have hAanti : Antitone A := by
    intro i j hij f hf
    exact windowModulusFailure_mono le_rfl le_rfl
      (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)) hf
  have hAinter : ⋂ k, A k = ∅ := iInter_windowModulusFailure_eq_empty b ha
  have htend : Tendsto (fun k => μ (A k)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop hAmeas hAanti ⟨0, measure_ne_top μ _⟩
    simpa [Function.comp_def, hAinter] using h
  obtain ⟨k, hk⟩ := ((tendsto_order.1 htend).2 η hη).exists
  exact ⟨1 / ((k : ℝ) + 1), by positivity, hk.le⟩

/-- **Scales bounded away from zero.**  For `a ≤ ε ≤ 1`, the dilated failure set at scale
`ε` is contained in the dilated failure set at scale `a` with the undilated threshold `c`. -/
theorem diffusive_windowModulusFailure_subset_of_le_scale {a ε : ℝ≥0} (ha : 0 < a)
    (haε : a ≤ ε) (hε1 : ε ≤ 1) (m : ℕ) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    windowModulusFailure (E := E) (ε⁻¹ ^ 2 * (m : ℝ≥0)) (c / (ε : ℝ))
        (((ε : ℝ))⁻¹ ^ 2 * d) ⊆
      windowModulusFailure (E := E) (a⁻¹ ^ 2 * (m : ℝ≥0)) c (((a : ℝ))⁻¹ ^ 2 * d) := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have haεR : (a : ℝ) ≤ (ε : ℝ) := by exact_mod_cast haε
  have hεR : (0 : ℝ) < (ε : ℝ) := haR.trans_le haεR
  have hε1R : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
  have hsqR : ((ε : ℝ))⁻¹ ^ 2 ≤ ((a : ℝ))⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hεR.le) (inv_anti₀ haR haεR) 2
  have hwin : ε⁻¹ ^ 2 * (m : ℝ≥0) ≤ a⁻¹ ^ 2 * (m : ℝ≥0) := by
    have h : ((ε⁻¹ ^ 2 * (m : ℝ≥0) : ℝ≥0) : ℝ) ≤ ((a⁻¹ ^ 2 * (m : ℝ≥0) : ℝ≥0) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_right hsqR (Nat.cast_nonneg m)
    exact_mod_cast h
  have hthr : c ≤ c / (ε : ℝ) := by
    rw [le_div_iff₀ hεR]
    exact mul_le_of_le_one_right hc hε1R
  exact windowModulusFailure_mono hwin hthr (mul_le_mul_of_nonneg_right hsqR hd)

/-- **Dilated window moduli, uniformly over the scales `ε ∈ (0, 1]`, from dilated window
moduli along every positive null sequence of scales.**

CONDITIONAL on `hseq`; this proves no tightness estimate. -/
theorem diffusive_window_tail_uniform_of_sequential (μ : Measure C(ℝ≥0, E))
    [IsFiniteMeasure μ]
    (hseq : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (m : ℕ) (c : ℝ), 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∃ d : ℝ, 0 < d ∧
        ∀ᶠ n in atTop, μ (windowModulusFailure (E := E) ((ε n)⁻¹ ^ 2 * (m : ℝ≥0))
          (c / (ε n : ℝ)) (((ε n : ℝ))⁻¹ ^ 2 * d)) ≤ η)
    (m : ℕ) (c : ℝ) (hc : 0 < c) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ d : ℝ, 0 < d ∧ ∀ ε ∈ Set.Ioc (0 : ℝ≥0) 1,
      μ (windowModulusFailure (E := E) (ε⁻¹ ^ 2 * (m : ℝ≥0)) (c / (ε : ℝ))
        (((ε : ℝ))⁻¹ ^ 2 * d)) ≤ η := by
  have hmono : ∀ (ε : ℝ≥0) (d d' : ℝ), d ≤ d' →
      μ (windowModulusFailure (E := E) (ε⁻¹ ^ 2 * (m : ℝ≥0)) (c / (ε : ℝ))
        (((ε : ℝ))⁻¹ ^ 2 * d)) ≤
      μ (windowModulusFailure (E := E) (ε⁻¹ ^ 2 * (m : ℝ≥0)) (c / (ε : ℝ))
        (((ε : ℝ))⁻¹ ^ 2 * d')) := by
    intro ε d d' hdd'
    exact measure_mono (windowModulusFailure_mono le_rfl le_rfl
      (mul_le_mul_of_nonneg_left hdd' (sq_nonneg _)))
  obtain ⟨a, ha, d₁, hd₁, hsmall⟩ := exists_scale_lag_of_sequential
    (p := fun (ε : ℝ≥0) (d : ℝ) => μ (windowModulusFailure (E := E)
      (ε⁻¹ ^ 2 * (m : ℝ≥0)) (c / (ε : ℝ)) (((ε : ℝ))⁻¹ ^ 2 * d)))
    hmono (fun ε hε hlim => hseq ε hε hlim m c hc η hη)
  obtain ⟨a₀, rfl⟩ : ∃ a₀ : ℝ≥0, (a₀ : ℝ) = a := ⟨⟨a, ha.le⟩, rfl⟩
  have ha₀ : 0 < a₀ := by exact_mod_cast ha
  obtain ⟨d₂, hd₂, hfar⟩ :=
    finite_measure_windowModulusFailure_tail μ (a₀⁻¹ ^ 2 * (m : ℝ≥0)) hc hη
  have hd₂' : (0 : ℝ) < (a₀ : ℝ) ^ 2 * d₂ := mul_pos (pow_pos ha 2) hd₂
  refine ⟨min d₁ ((a₀ : ℝ) ^ 2 * d₂), lt_min hd₁ hd₂', ?_⟩
  rintro ε ⟨hε0, hε1⟩
  have hmin0 : (0 : ℝ) ≤ min d₁ ((a₀ : ℝ) ^ 2 * d₂) := le_min hd₁.le hd₂'.le
  by_cases hεa : (ε : ℝ) ≤ (a₀ : ℝ)
  · have hle : ((ε : ℝ))⁻¹ ^ 2 * min d₁ ((a₀ : ℝ) ^ 2 * d₂) ≤ ((ε : ℝ))⁻¹ ^ 2 * d₁ :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg _)
    exact (measure_mono (windowModulusFailure_mono le_rfl le_rfl hle)).trans
      (hsmall ε hε0 hεa)
  · have haε : a₀ ≤ ε := by
      have h : (a₀ : ℝ) ≤ (ε : ℝ) := (not_le.mp hεa).le
      exact_mod_cast h
    have hlag : ((a₀ : ℝ))⁻¹ ^ 2 * min d₁ ((a₀ : ℝ) ^ 2 * d₂) ≤ d₂ := by
      have ha₀R : (a₀ : ℝ) ≠ 0 := ha.ne'
      calc ((a₀ : ℝ))⁻¹ ^ 2 * min d₁ ((a₀ : ℝ) ^ 2 * d₂)
          ≤ ((a₀ : ℝ))⁻¹ ^ 2 * ((a₀ : ℝ) ^ 2 * d₂) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg _)
        _ = d₂ := by
            rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ ha₀R, one_pow, one_mul]
    have hsub := (diffusive_windowModulusFailure_subset_of_le_scale (E := E) ha₀ haε hε1 m
      hc.le hmin0).trans (windowModulusFailure_mono le_rfl le_rfl hlag)
    exact (measure_mono hsub).trans hfar

end Window

/-! ## The consumer's input -/

/-- The scale set `(0, 1]` is a neighbourhood of `0` within the positive scales. -/
theorem Ioc_zero_one_mem_nhdsWithin :
    Set.Ioc (0 : ℝ≥0) 1 ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0) := by
  have h1 : Set.Iic (1 : ℝ≥0) ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0) :=
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds zero_lt_one)
  have h2 : Set.Ioi (0 : ℝ≥0) ∈ nhdsWithin (0 : ℝ≥0) (Set.Ioi 0) := self_mem_nhdsWithin
  filter_upwards [h1, h2] with ε hε1 hε0
  exact ⟨hε0, hε1⟩

/-- **The consumer's `RescaledWindowModulusTail μ (Set.Ioc 0 1)` from dilated window
moduli of the unrescaled law along every positive null sequence of scales.**

CONDITIONAL on `hseq`; this proves no tightness estimate. -/
theorem rescaledWindowModulusTail_Ioc_of_sequential
    (μ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (hseq : ∀ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ (m : ℕ) (c : ℝ), 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∃ d : ℝ, 0 < d ∧
        ∀ᶠ n in atTop, (μ : Measure (BouRabeeGwynne.BrownianPath 2))
          (windowModulusFailure (E := BouRabeeGwynne.Euc 2) ((ε n)⁻¹ ^ 2 * (m : ℝ≥0))
            (c / (ε n : ℝ)) (((ε n : ℝ))⁻¹ ^ 2 * d)) ≤ η) :
    RescaledWindowModulusTail μ (Set.Ioc 0 1) :=
  rescaledWindowModulusTail_of_diffusive_window_tails μ (Set.Ioc 0 1) (fun _ hε => hε.1)
    (fun m c hc η hη => diffusive_window_tail_uniform_of_sequential
      (E := BouRabeeGwynne.Euc 2) (μ : Measure (BouRabeeGwynne.BrownianPath 2))
      hseq m c hc η hη)

end ReflectedGMS.WindowModulusUniformScales
