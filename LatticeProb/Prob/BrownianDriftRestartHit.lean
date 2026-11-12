/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.BrownianStrongMarkov
import LatticeProb.Prob.BrownianExpMartingale

/-!
# Restarting a Brownian motion with drift at the hitting time of a level

For a real Brownian motion `B` with continuous paths and a drift `c`, the first time `τ_a` at
which `B s + c s ≥ a` is a stopping time of the natural filtration, and so is its truncation at a
finite horizon `N`.  The strong Markov property of the `ℝ ^ 1`-valued lift of `B`
(`LatticeProb.IsBrownianSpace.hasStrongMarkovRestart`) therefore gives, for every event `E` of the
past at a stopping time and every measurable set `Γ` of paths, the product formula

`P (E ∩ {restarted increments of B + c · lie in Γ}) = P E * P {B + c · ∈ Γ}`.

## Main results

* `LatticeProb.isBrownianSpace_liftOne`: a real Brownian motion is a Brownian motion on `ℝ ^ 1`.
* `LatticeProb.isStoppingTime_hitDrift`, `LatticeProb.isStoppingTime_hitDriftTrunc`: hitting times
  of a level by `B + c ·` are stopping times of the natural filtration.
* `LatticeProb.restart_real`, `LatticeProb.restart_drift`: the restart identities.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The lift of a real process to `ℝ ^ 1`. -/
def liftOne (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 1) :=
  fun t ω => WithLp.toLp 2 (fun _ => B t ω)

omit [MeasurableSpace Ω] in
theorem liftOne_apply (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) (i : Fin 1) :
    liftOne B t ω i = B t ω := rfl

theorem stronglyMeasurable_liftOne (hm : ∀ t, Measurable (B t)) (t : ℝ≥0) :
    StronglyMeasurable (liftOne B t) := by
  have h : Measurable (fun ω => (fun _ : Fin 1 => B t ω)) :=
    Measurable.of_eval (fun _ => hm t)
  exact ((PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).measurable.comp h).stronglyMeasurable

omit [MeasurableSpace Ω] in
theorem continuous_liftOne (hcont : ∀ ω, Continuous fun t => B t ω) (ω : Ω) :
    Continuous fun t => liftOne B t ω :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).comp (continuous_pi fun _ => hcont ω)

/-- **A real Brownian motion is a Brownian motion on `ℝ ^ 1`.** -/
theorem isBrownianSpace_liftOne [IsProbabilityMeasure P] (hB : IsBrownianReal B P) :
    IsBrownianSpace 1 0 (liftOne B) P where
  start := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω h
    ext i
    simp [liftOne_apply, h]
  coord := fun i => by
    have : (fun t ω => Real.sqrt ((1 : ℕ) : ℝ) *
        (liftOne B t ω i - (0 : EuclideanSpace ℝ (Fin 1)) i)) = B := by
      funext t ω
      simp [liftOne_apply]
    rw [this]
    exact hB
  indep := iIndepFun.of_subsingleton

open Classical in
/-- The first time `B s + c s` reaches the level `a` (`⊤` if never). -/
def hitDrift (B : ℝ≥0 → Ω → ℝ) (c a : ℝ) (ω : Ω) : ℝ≥0∞ :=
  if _h : ∃ s : ℝ≥0, a ≤ B s ω + c * s then
    ((sInf {s : ℝ≥0 | a ≤ B s ω + c * s} : ℝ≥0) : ℝ≥0∞)
  else ⊤

omit [MeasurableSpace Ω] in
theorem hitDrift_le_iff (hcont : ∀ ω, Continuous fun s => B s ω) (c a : ℝ) (ω : Ω) (t : ℝ≥0) :
    hitDrift B c a ω ≤ (t : ℝ≥0∞) ↔ ∃ s ≤ t, a ≤ B s ω + c * s := by
  classical
  have hclosed : IsClosed {s : ℝ≥0 | a ≤ B s ω + c * s} :=
    IsClosed.preimage ((hcont ω).add (continuous_const.mul NNReal.continuous_coe)) isClosed_Ici
  unfold hitDrift
  split_ifs with h
  · rw [ENNReal.coe_le_coe]
    constructor
    · intro hle
      refine ⟨sInf {s : ℝ≥0 | a ≤ B s ω + c * s}, hle, ?_⟩
      exact hclosed.csInf_mem h (OrderBot.bddBelow _)
    · rintro ⟨s, hs, hA⟩
      exact le_trans (csInf_le (OrderBot.bddBelow _) hA) hs
  · constructor
    · intro hle
      exact absurd hle (by simp)
    · rintro ⟨s, -, hA⟩
      exact absurd ⟨s, hA⟩ h

omit [MeasurableSpace Ω] in
theorem measurableSet_comap_exists_le_lt_drift
    (hcont : ∀ ω, Continuous fun s => B s ω) (c a : ℝ) (t : ℝ≥0) :
    MeasurableSet[MeasurableSpace.comap
      (fun ω (s : Set.Iic t) => liftOne B (s : ℝ≥0) ω) inferInstance]
      {ω | ∃ s ≤ t, a < B s ω + c * s} := by
  classical
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense ↥(Set.Icc (0:ℝ≥0) t)
  have hEq : {ω | ∃ s ≤ t, a < B s ω + c * s}
      = ⋃ q ∈ D, {ω | a < B (q : ℝ≥0) ω + c * (q : ℝ≥0)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨s, hs, hsA⟩
      have hcont' : Continuous fun r : ↥(Set.Icc (0:ℝ≥0) t) => B (r : ℝ≥0) ω + c * (r : ℝ≥0) :=
        ((hcont ω).comp continuous_subtype_val).add
          (continuous_const.mul (NNReal.continuous_coe.comp continuous_subtype_val))
      have hopen : IsOpen {r : ↥(Set.Icc (0:ℝ≥0) t) | a < B (r : ℝ≥0) ω + c * (r : ℝ≥0)} :=
        isOpen_lt continuous_const hcont'
      have hne : ({r : ↥(Set.Icc (0:ℝ≥0) t) | a < B (r : ℝ≥0) ω + c * (r : ℝ≥0)}).Nonempty :=
        ⟨⟨s, zero_le, hs⟩, hsA⟩
      obtain ⟨q, hqD, hq⟩ := hDdense.exists_mem_open hopen hne
      exact ⟨q, hqD, hq⟩
    · rintro ⟨q, hqD, hq⟩
      exact ⟨(q : ℝ≥0), q.2.2, hq⟩
  rw [hEq]
  refine MeasurableSet.biUnion hDcount (fun q _ => ?_)
  have hpre : {ω | a < B (q : ℝ≥0) ω + c * (q : ℝ≥0)}
      = (fun ω (s : Set.Iic t) => liftOne B (s : ℝ≥0) ω) ⁻¹'
        {g : Set.Iic t → EuclideanSpace ℝ (Fin 1) |
          a < g ⟨(q : ℝ≥0), q.2.2⟩ 0 + c * (q : ℝ≥0)} := rfl
  rw [hpre]
  exact ⟨_, measurableSet_lt measurable_const
    (((EuclideanSpace.proj (0 : Fin 1)).continuous.measurable.comp
      (measurable_pi_apply (⟨(q : ℝ≥0), q.2.2⟩ : Set.Iic t))).add measurable_const), rfl⟩

omit [MeasurableSpace Ω] in
theorem measurableSet_comap_exists_le_le_drift
    (hcont : ∀ ω, Continuous fun s => B s ω) (c a : ℝ) (t : ℝ≥0) :
    MeasurableSet[MeasurableSpace.comap
      (fun ω (s : Set.Iic t) => liftOne B (s : ℝ≥0) ω) inferInstance]
      {ω | ∃ s ≤ t, a ≤ B s ω + c * s} := by
  have hEq : {ω | ∃ s ≤ t, a ≤ B s ω + c * s}
      = ⋂ k : ℕ, {ω | ∃ s ≤ t, a - 1 / (k + 1 : ℝ) < B s ω + c * s} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨s, hs, hA⟩ k
      refine ⟨s, hs, lt_of_lt_of_le ?_ hA⟩
      have : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
      linarith
    · intro hk
      obtain ⟨s₀, hs₀mem, hs₀max⟩ :=
        (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_isMaxOn ⟨0, by simp⟩
          ((hcont ω).add (continuous_const.mul NNReal.continuous_coe)).continuousOn
      refine ⟨s₀, hs₀mem.2, ?_⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨k, hk'⟩ := exists_nat_one_div_lt (sub_pos.2 hcon)
      obtain ⟨s, hs, hslt⟩ := hk k
      have hle : B s ω + c * s ≤ B s₀ ω + c * s₀ := hs₀max ⟨zero_le, hs⟩
      linarith
  rw [hEq]
  exact MeasurableSet.iInter fun k => measurableSet_comap_exists_le_lt_drift hcont c _ t

/-- **The hitting time of a level by `B + c ·` is a stopping time** of the natural filtration of
the `ℝ ^ 1`-lift, for a motion with continuous paths. -/
theorem isStoppingTime_hitDrift (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (c a : ℝ) :
    IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      (hitDrift B c a) := by
  intro t
  refine MeasurableSet.congr (s := {ω | ∃ s ≤ t, a ≤ B s ω + c * s}) ?_ ?_
  · rw [natFiltration_eq_comap (liftOne B) (stronglyMeasurable_liftOne hm) t]
    exact measurableSet_comap_exists_le_le_drift hcont c a t
  · ext ω
    exact (hitDrift_le_iff hcont c a ω t).symm

/-- The hitting time truncated at the horizon `N`, with values in `ℝ≥0`. -/
def hitDriftTrunc (B : ℝ≥0 → Ω → ℝ) (c a : ℝ) (N : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (hitDrift B c a ω ⊓ (N : ℝ≥0∞)).toNNReal

omit [MeasurableSpace Ω] in
theorem coe_hitDriftTrunc (B : ℝ≥0 → Ω → ℝ) (c a : ℝ) (N : ℝ≥0) (ω : Ω) :
    ((hitDriftTrunc B c a N ω : ℝ≥0) : ℝ≥0∞) = hitDrift B c a ω ⊓ (N : ℝ≥0∞) := by
  rw [hitDriftTrunc, ENNReal.coe_toNNReal]
  exact (lt_of_le_of_lt inf_le_right ENNReal.coe_lt_top).ne

theorem isStoppingTime_hitDriftTrunc (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) (c a : ℝ) (N : ℝ≥0) :
    IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => ((hitDriftTrunc B c a N ω : ℝ≥0) : ℝ≥0∞) := by
  have h := (isStoppingTime_hitDrift hm hcont c a).min_const (i := N)
  have hfun : (fun ω => ((hitDriftTrunc B c a N ω : ℝ≥0) : ℝ≥0∞))
      = fun ω => min (hitDrift B c a ω) (N : ℝ≥0∞) := by
    funext ω
    exact coe_hitDriftTrunc B c a N ω
  rw [hfun]
  exact h

omit [MeasurableSpace Ω] in
/-- On the event that the level is reached before the horizon the truncated time is the
hitting time. -/
theorem coe_hitDriftTrunc_of_le (B : ℝ≥0 → Ω → ℝ) (c a : ℝ) (N : ℝ≥0) (ω : Ω)
    (h : hitDrift B c a ω ≤ (N : ℝ≥0∞)) :
    ((hitDriftTrunc B c a N ω : ℝ≥0) : ℝ≥0∞) = hitDrift B c a ω := by
  rw [coe_hitDriftTrunc, inf_eq_left.2 h]

/-- **The strong Markov property for a real Brownian motion** at a stopping time of the
natural filtration of its `ℝ ^ 1`-lift: the restarted increments are independent of the past at
the stopping time and have the law of the motion. -/
theorem restart_real [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => (τ ω : ℝ≥0∞))
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E)
    (Γ : Set (ℝ≥0 → ℝ)) (hΓ : MeasurableSet Γ) :
    P (E ∩ {ω | (fun t => B (τ ω + t) ω - B (τ ω) ω) ∈ Γ})
      = P E * P {ω | (fun t => B t ω) ∈ Γ} := by
  have hmeas : Measurable (fun (f : ℝ≥0 → EuclideanSpace ℝ (Fin 1)) (t : ℝ≥0) => f t 0) :=
    Measurable.of_eval fun t =>
      (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable.comp (measurable_pi_apply t)
  have key := (isBrownianSpace_liftOne hB).hasStrongMarkovRestart
    (stronglyMeasurable_liftOne hm) (continuous_liftOne hcont) |>.restart τ hτ E hE _ (hmeas hΓ)
  have h1 : {ω | (fun t => liftOne B (τ ω + t) ω - liftOne B (τ ω) ω) ∈
        (fun (f : ℝ≥0 → EuclideanSpace ℝ (Fin 1)) (t : ℝ≥0) => f t 0) ⁻¹' Γ}
      = {ω | (fun t => B (τ ω + t) ω - B (τ ω) ω) ∈ Γ} := rfl
  have h2 : {ω | (fun t => liftOne B t ω - liftOne B 0 ω) ∈
        (fun (f : ℝ≥0 → EuclideanSpace ℝ (Fin 1)) (t : ℝ≥0) => f t 0) ⁻¹' Γ}
      =ᵐ[P] {ω | (fun t => B t ω) ∈ Γ} := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω h
    have : (fun t => liftOne B t ω - liftOne B 0 ω) ∈
        (fun (f : ℝ≥0 → EuclideanSpace ℝ (Fin 1)) (t : ℝ≥0) => f t 0) ⁻¹' Γ
        ↔ (fun t => B t ω) ∈ Γ := by
      show (fun t => B t ω - B 0 ω) ∈ Γ ↔ _
      simp [h]
    exact propext this
  rw [h1] at key
  rw [key, measure_congr h2]

/-- **Restart of `B + c ·` at a stopping time**: the increments of the drifted motion after
the stopping time `τ` lie in `Γ` with the probability that the drifted motion does, independently
of any event `E` of the past at `τ`. -/
theorem restart_drift [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (c : ℝ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => (τ ω : ℝ≥0∞))
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E)
    (Γ : Set (ℝ≥0 → ℝ)) (hΓ : MeasurableSet Γ) :
    P (E ∩ {ω | (fun t => (B (τ ω + t) ω + c * ((τ ω + t : ℝ≥0) : ℝ))
        - (B (τ ω) ω + c * (τ ω : ℝ))) ∈ Γ})
      = P E * P {ω | (fun t => B t ω + c * (t : ℝ)) ∈ Γ} := by
  have hmeas : Measurable (fun (g : ℝ≥0 → ℝ) (t : ℝ≥0) => g t + c * (t : ℝ)) :=
    Measurable.of_eval fun t => (measurable_pi_apply t).add measurable_const
  have key := restart_real hB hm hcont τ hτ E hE _ (hmeas hΓ)
  have h1 : ∀ ω : Ω, ((fun t => (B (τ ω + t) ω + c * ((τ ω + t : ℝ≥0) : ℝ))
        - (B (τ ω) ω + c * (τ ω : ℝ))) ∈ Γ) ↔
      (fun t => B (τ ω + t) ω - B (τ ω) ω) ∈ (fun (g : ℝ≥0 → ℝ) (t : ℝ≥0) => g t + c * (t : ℝ)) ⁻¹' Γ := by
    intro ω
    have : (fun t : ℝ≥0 => (B (τ ω + t) ω + c * ((τ ω + t : ℝ≥0) : ℝ))
        - (B (τ ω) ω + c * (τ ω : ℝ)))
        = (fun t : ℝ≥0 => (B (τ ω + t) ω - B (τ ω) ω) + c * (t : ℝ)) := by
      funext t
      push_cast
      ring
    rw [this]
    rfl
  have h2 : {ω | (fun t => (B (τ ω + t) ω + c * ((τ ω + t : ℝ≥0) : ℝ))
        - (B (τ ω) ω + c * (τ ω : ℝ))) ∈ Γ}
      = {ω | (fun t => B (τ ω + t) ω - B (τ ω) ω) ∈
        (fun (g : ℝ≥0 → ℝ) (t : ℝ≥0) => g t + c * (t : ℝ)) ⁻¹' Γ} :=
    Set.ext fun ω => h1 ω
  rw [h2]
  exact key

end LatticeProb

end
