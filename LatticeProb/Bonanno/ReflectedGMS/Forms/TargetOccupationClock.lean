/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.TargetOccupationClock at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.UniquenessLimit
import LatticeProb.Bonanno.ReflectedWalk.FiniteApproximation

/-!
# Occupation clocks for finite targets

The clock below records the actual amount of original-process time spent in a
target.  Thus all time outside the target, including time at `none`, is deleted.
The complement is exactly `ReflectedWalk.Theorem16.sojourn`, so its established
almost-sure convergence supplies convergence of the target clocks without a
second Fubini or dominated-convergence argument.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal ReflectedWalk

universe u

namespace ReflectedGMS.TargetOccupationClock

variable {V : Type u} {Ω : Type u} [MeasurableSpace Ω]

/-- Time up to `t` at which the original process lies in `A`. -/
noncomputable def occupationClock (A : Set V) (X : ℝ≥0 → Ω → Option V)
    (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  volume {s : ℝ | s ∈ Icc (0 : ℝ) (t : ℝ) ∧ X (Real.toNNReal s) ω ∈ some '' A}

theorem occupationClock_le (A : Set V) (X : ℝ≥0 → Ω → Option V)
    (t : ℝ≥0) (ω : Ω) : occupationClock A X t ω ≤ (t : ℝ≥0∞) := by
  refine (measure_mono fun s hs => hs.1).trans_eq ?_
  simp [Real.volume_Icc]

/-- If the path stays at a target vertex throughout the next interval, its
occupation clock increases there with unit slope. -/
theorem occupationClock_add_of_stays_in_target (A : Set V)
    (X : ℝ≥0 → Ω → Option V) (t δ : ℝ≥0) (ω : Ω) (y : V) (hy : y ∈ A)
    (hstay : ∀ u ∈ Icc t (t + δ), X u ω = some y) :
    occupationClock A X (t + δ) ω = occupationClock A X t ω + (δ : ℝ≥0∞) := by
  let S : Set ℝ :=
    {s : ℝ | s ∈ Icc (0 : ℝ) (t : ℝ) ∧ X (Real.toNNReal s) ω ∈ some '' A}
  let T : Set ℝ := Ioc (t : ℝ) ((t + δ : ℝ≥0) : ℝ)
  have hdisj : Disjoint S T := by
    refine Set.disjoint_left.2 ?_
    intro s hs ht
    exact (not_lt_of_ge hs.1.2) ht.1
  have hunion :
      {s : ℝ | s ∈ Icc (0 : ℝ) ((t + δ : ℝ≥0) : ℝ) ∧
          X (Real.toNNReal s) ω ∈ some '' A} = S ∪ T := by
    ext s
    simp only [S, T, Set.mem_union, Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · intro hs
      by_cases hst : s ≤ (t : ℝ)
      · exact Or.inl ⟨⟨hs.1.1, hst⟩, hs.2⟩
      · exact Or.inr ⟨lt_of_not_ge hst, hs.1.2⟩
    · rintro (hs | hs)
      · exact ⟨⟨hs.1.1, hs.1.2.trans (NNReal.coe_le_coe.2 (le_add_right le_rfl))⟩, hs.2⟩
      · have hs0 : 0 ≤ s := (show (0 : ℝ) ≤ (t : ℝ) from t.property).trans hs.1.le
        have hu : Real.toNNReal s ∈ Icc t (t + δ) := by
          constructor
          · apply NNReal.coe_le_coe.1
            simpa [Real.coe_toNNReal s hs0] using hs.1.le
          · apply NNReal.coe_le_coe.1
            simpa [Real.coe_toNNReal s hs0] using hs.2
        refine ⟨⟨hs0, hs.2⟩, ⟨y, hy, ?_⟩⟩
        exact (hstay _ hu).symm
  change volume
    {s : ℝ | s ∈ Icc (0 : ℝ) ((t + δ : ℝ≥0) : ℝ) ∧
      X (Real.toNNReal s) ω ∈ some '' A} = volume S + (δ : ℝ≥0∞)
  rw [hunion, measure_union hdisj measurableSet_Ioc]
  congr 1
  rw [Real.volume_Ioc]
  simp

/-- For a measurable path section, target time and time outside the target
partition `[0,t]`. -/
theorem occupationClock_add_sojourn [Countable V] (A : ℕ → Set V) (n : ℕ)
    (X : ℝ≥0 → Ω → Option V) (t : ℝ≥0) (ω : Ω)
    (hX : Measurable fun s : ℝ => X (Real.toNNReal s) ω) :
    occupationClock (A n) X t ω +
        ReflectedWalk.Theorem16.sojourn A X n t ω = (t : ℝ≥0∞) := by
  let S : Set ℝ :=
    {s : ℝ | s ∈ Icc (0 : ℝ) (t : ℝ) ∧ X (Real.toNNReal s) ω ∈ some '' A n}
  let T : Set ℝ :=
    {s : ℝ | s ∈ Icc (0 : ℝ) (t : ℝ) ∧ X (Real.toNNReal s) ω ∉ some '' A n}
  have hTm : MeasurableSet T :=
    measurableSet_Icc.inter
      (hX (ReflectedWalk.Theorem16.measurableSet_option (some '' A n)ᶜ))
  have hdisj : Disjoint S T := by
    refine Set.disjoint_left.2 ?_
    intro s hs ht
    exact ht.2 hs.2
  have hunion : S ∪ T = Icc (0 : ℝ) (t : ℝ) := by
    ext s
    simp only [S, T, Set.mem_union, Set.mem_ofPred_eq, Set.mem_Icc]
    tauto
  change volume S + volume T = (t : ℝ≥0∞)
  rw [← measure_union hdisj hTm, hunion, Real.volume_Icc]
  simp

/-- The target clock is the finite total interval length minus the complementary
sojourn. -/
theorem occupationClock_eq_sub_sojourn [Countable V] (A : ℕ → Set V) (n : ℕ)
    (X : ℝ≥0 → Ω → Option V) (t : ℝ≥0) (ω : Ω)
    (hX : Measurable fun s : ℝ => X (Real.toNNReal s) ω) :
    occupationClock (A n) X t ω = (t : ℝ≥0∞) -
      ReflectedWalk.Theorem16.sojourn A X n t ω := by
  apply ENNReal.eq_sub_of_add_eq
  · change volume
      {s : ℝ | s ∈ Icc (0 : ℝ) (t : ℝ) ∧ X (Real.toNNReal s) ω ∉ some '' A n} ≠ ∞
    have hIcc : volume (Icc (0 : ℝ) (t : ℝ)) ≠ ∞ := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    refine ne_top_of_le_ne_top hIcc ?_
    exact measure_mono fun s hs => hs.1
  · exact occupationClock_add_sojourn A n X t ω hX

/-- Enlarging the time horizon can only increase the complementary sojourn. -/
theorem sojourn_mono_time (A : ℕ → Set V) (X : ℝ≥0 → Ω → Option V)
    (n : ℕ) {s t : ℝ≥0} (hst : s ≤ t) (ω : Ω) :
    ReflectedWalk.Theorem16.sojourn A X n s ω ≤
      ReflectedWalk.Theorem16.sojourn A X n t ω := by
  apply measure_mono
  intro r hr
  exact ⟨⟨hr.1.1, hr.1.2.trans (NNReal.coe_le_coe.2 hst)⟩, hr.2⟩

/-- A single full-measure set supports complementary-sojourn convergence at
every finite horizon.  Countable integer horizons suffice by monotonicity. -/
theorem ae_tendsto_sojourn_all_t [Countable V] {P : Measure Ω}
    [SFinite P] {A : ℕ → Set V} (hAmono : Monotone A)
    (hAcov : ∀ x, ∃ n, x ∈ A n) (X : ℝ≥0 → Ω → Option V)
    (hX : ∀ s, Measurable (X s))
    (hi : ReflectedWalk.Theorem16.AlmostEverywhereDefined P X)
    (hii : ReflectedWalk.Theorem16.RightContinuous P X)
    (hR : ReflectedWalk.Theorem16.RightContinuousAtInfty P X) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n => ReflectedWalk.Theorem16.sojourn A X n t ω) atTop (𝓝 0) := by
  have hnat : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Tendsto (fun n => ReflectedWalk.Theorem16.sojourn A X n (k : ℝ≥0) ω)
        atTop (𝓝 0) := by
    apply ae_all_iff.2
    intro k
    exact ReflectedWalk.Theorem16.ae_tendsto_sojourn hAmono hAcov hX hi hii hR k
  filter_upwards [hnat] with ω hω
  intro t
  let k : ℕ := ⌈(t : ℝ)⌉₊
  have htk : t ≤ (k : ℝ≥0) := by
    exact_mod_cast Nat.le_ceil (t : ℝ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hω k)
    (fun _ => bot_le) (fun n => sojourn_mono_time A X n htk ω)

/-- Clock convergence holds simultaneously for every finite time on one
full-measure set. -/
theorem ae_tendsto_occupationClock_all_t [Countable V] {P : Measure Ω}
    [SFinite P] {A : ℕ → Set V} (hAmono : Monotone A)
    (hAcov : ∀ x, ∃ n, x ∈ A n) (X : ℝ≥0 → Ω → Option V)
    (hX : ∀ s, Measurable (X s))
    (hi : ReflectedWalk.Theorem16.AlmostEverywhereDefined P X)
    (hii : ReflectedWalk.Theorem16.RightContinuous P X)
    (hR : ReflectedWalk.Theorem16.RightContinuousAtInfty P X) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n => occupationClock (A n) X t ω) atTop (𝓝 (t : ℝ≥0∞)) := by
  filter_upwards [ReflectedWalk.Theorem16.ae_dyadicLimit_eq hii hR,
    ae_tendsto_sojourn_all_t hAmono hAcov X hX hi hii hR]
      with ω hversion hsojourn
  have hpath : Measurable fun s : ℝ => X (Real.toNNReal s) ω := by
    have hm := ReflectedWalk.Theorem16.measurable_section
      (ReflectedWalk.Theorem16.measurable_uncurry_dyadicLimit hX) ω
    rw [show (fun s : ℝ => X (Real.toNNReal s) ω) =
      (fun s : ℝ => ReflectedWalk.Theorem16.dyadicLimit X (Real.toNNReal s) ω) by
        funext s
        exact (hversion (Real.toNNReal s)).symm]
    exact hm
  intro t
  have heq : ∀ n, occupationClock (A n) X t ω = (t : ℝ≥0∞) -
      ReflectedWalk.Theorem16.sojourn A X n t ω := by
    intro n
    exact occupationClock_eq_sub_sojourn A n X t ω hpath
  simp_rw [heq]
  simpa using ENNReal.Tendsto.sub
    (show Tendsto (fun _ : ℕ => (t : ℝ≥0∞)) atTop (𝓝 (t : ℝ≥0∞)) from
      tendsto_const_nhds)
    (hsojourn t) (Or.inl (by simp))

/-- Reflected-walk specialization with one common full-measure set for all
finite horizons. -/
theorem IsReflectedWalk.ae_tendsto_occupationClock_all_t [Countable V]
    {G : ReflectedWalk.ConductanceGraph V} {w : V → ℝ}
    {hmin : G.EnergyMinimizer} {𝓧 : ReflectedWalk.ProcessFamily V}
    (hwalk : ReflectedWalk.IsReflectedWalk G w hmin 𝓧)
    {A : ℕ → Set V} (hAmono : Monotone A) (hAcov : ∀ x, ∃ n, x ∈ A n)
    (z : V) :
    ∀ᵐ ω ∂𝓧.P z, ∀ t : ℝ≥0,
      Tendsto (fun n => occupationClock (A n) 𝓧.X t ω) atTop (𝓝 (t : ℝ≥0∞)) := by
  exact ReflectedGMS.TargetOccupationClock.ae_tendsto_occupationClock_all_t
    hAmono hAcov 𝓧.X
    (fun s => 𝓧.measurable_X s) (hwalk z).2.1 (hwalk z).2.2.1
    (hwalk z).2.2.2.1

end ReflectedGMS.TargetOccupationClock
