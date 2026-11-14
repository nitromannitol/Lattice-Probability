import Mathlib
import LatticeProb.Prob.CrossingTimesBM
import LatticeProb.Prob.BrownianRestartCanonical

/-!
# Restarting a Brownian motion at an almost surely finite stopping time

`LatticeProb.IsBrownianSpace.restart` restarts the motion at a stopping time with values in `ℝ≥0`.
Here the stopping time `σ` takes values in `[0, ∞]` and is only almost surely finite, as is
every crossing time of a Brownian motion.  The restarted path, defined with `σ.toNNReal`, is
independent of the past at `σ`, and has the law of the centred motion.  The proof truncates at
`σ ∧ N`, applies the strong Markov property on the event `{σ ≤ N}` of the past, and lets
`N → ∞`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The measurable spaces of two stopping times that are equal as functions agree. -/
theorem isStoppingTime_measurableSpace_congr {f : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {τ π : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (h : τ = π) :
    hτ.measurableSpace = hπ.measurableSpace := by
  subst h
  rfl

/-- **Restart at an almost surely finite stopping time.** For a stopping time `σ` of the natural
filtration of a Brownian motion, with `σ < ∞` almost surely, an event `E` of the past at `σ`
and a measurable set `S` of continuous paths, the event `E` and the restarted path
`t ↦ B (σ + t) - B σ` are independent, and the restarted path has the law of the centred
motion. -/
theorem IsBrownianSpace.restart_ennreal [IsProbabilityMeasure P]
    {x : EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : IsBrownianSpace d x B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {σ : Ω → ℝ≥0∞}
    (hσ : IsStoppingTime (natFiltration B hm) σ) (hfin : ∀ᵐ ω ∂P, σ ω ≠ ⊤)
    {E : Set Ω} (hE : MeasurableSet[hσ.measurableSpace] E) {S : Set (BrownianPath d)}
    (hS : MeasurableSet S) :
    P (E ∩ {ω | restartPath B hcont (fun ω => (σ ω).toNNReal) ω ∈ S})
      = P E * P {ω | restartPath B hcont (fun _ => 0) ω ∈ S} := by
  obtain ⟨Γ, hΓ, hΓS⟩ := exists_measurableSet_coe_preimage_brownianPath hS
  have hmem : ∀ w : BrownianPath d, w ∈ S ↔ (w : ℝ≥0 → EuclideanSpace ℝ (Fin d)) ∈ Γ := by
    intro w
    rw [← hΓS]
    rfl
  set p := P {ω | restartPath B hcont (fun _ => 0) ω ∈ S} with hp
  have hp0 : P {ω | (fun t => B t ω - B 0 ω) ∈ Γ} = p := by
    rw [hp]
    congr 1
    ext ω
    have hz : ((restartPath B hcont (fun _ => 0) ω : BrownianPath d) :
        ℝ≥0 → EuclideanSpace ℝ (Fin d)) = fun t => B t ω - B 0 ω := by
      funext t
      simp [restartPath]
    show (fun t => B t ω - B 0 ω) ∈ Γ ↔ restartPath B hcont (fun _ => 0) ω ∈ S
    rw [hmem, hz]
  -- truncations of `σ`
  set τ : ℕ → Ω → ℝ≥0 := fun N ω => (min (σ ω) (N : ℝ≥0∞)).toNNReal with hτdef
  have hτeq : ∀ (N : ℕ) ω, ((τ N ω : ℝ≥0) : ℝ≥0∞) = min (σ ω) ((N : ℝ≥0) : ℝ≥0∞) := by
    intro N ω
    simp only [hτdef]
    rw [ENNReal.coe_toNNReal]
    · simp
    · exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
  have hτ : ∀ N : ℕ, IsStoppingTime (natFiltration B hm) fun ω => ((τ N ω : ℝ≥0) : ℝ≥0∞) := by
    intro N
    have h := hσ.min_const (N : ℝ≥0)
    have hfun : (fun ω => ((τ N ω : ℝ≥0) : ℝ≥0∞)) = fun ω => min (σ ω) ((N : ℝ≥0) : ℝ≥0∞) :=
      funext (hτeq N)
    rw [hfun]
    exact h
  have hEN : ∀ N : ℕ, MeasurableSet[(hτ N).measurableSpace] (E ∩ {ω | σ ω ≤ N}) := by
    intro N
    have h1 := hσ.measurableSet_inter_le (isStoppingTime_const (natFiltration B hm)
      (N : ℝ≥0)) E hE
    have h2 := isStoppingTime_measurableSpace_congr (hσ.min (isStoppingTime_const
      (natFiltration B hm) (N : ℝ≥0))) (hτ N) (funext fun ω => (hτeq N ω).symm)
    rw [← h2]
    exact h1
  have hstep : ∀ N : ℕ, P ((E ∩ {ω | σ ω ≤ N}) ∩
      {ω | restartPath B hcont (fun ω => (σ ω).toNNReal) ω ∈ S}) = P (E ∩ {ω | σ ω ≤ N}) * p := by
    intro N
    have h := hB.restart hm hcont (τ N) (hτ N) _ (hEN N) Γ hΓ
    rw [hp0] at h
    rw [← h]
    congr 1
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hωE, hωN⟩, hωS⟩
      have hτω : τ N ω = (σ ω).toNNReal := by
        simp only [hτdef]
        rw [min_eq_left hωN]
      refine ⟨⟨hωE, hωN⟩, ?_⟩
      rw [hτω]
      exact (hmem _).1 hωS
    · rintro ⟨⟨hωE, hωN⟩, hωS⟩
      have hτω : τ N ω = (σ ω).toNNReal := by
        simp only [hτdef]
        rw [min_eq_left hωN]
      refine ⟨⟨hωE, hωN⟩, ?_⟩
      rw [hτω] at hωS
      exact (hmem _).2 hωS
  have hstep' : ∀ N : ℕ, P ((E ∩ {ω | restartPath B hcont (fun ω => (σ ω).toNNReal) ω ∈ S}) ∩
      {ω | σ ω ≤ N}) = P (E ∩ {ω | σ ω ≤ N}) * p := by
    intro N
    rw [Set.inter_right_comm]
    exact hstep N
  have hnull : P {ω | σ ω = ⊤} = 0 := by
    have h := ae_iff.1 hfin
    simpa using h
  have hUn : ∀ F : Set Ω, P (⋃ N : ℕ, F ∩ {ω | σ ω ≤ N}) = P F := by
    intro F
    refine le_antisymm (measure_mono (Set.iUnion_subset fun N => Set.inter_subset_left)) ?_
    calc P F ≤ P ((⋃ N : ℕ, F ∩ {ω | σ ω ≤ N}) ∪ {ω | σ ω = ⊤}) := by
          apply measure_mono
          intro ω hω
          by_cases h : σ ω = ⊤
          · exact Or.inr h
          · left
            obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt h
            exact Set.mem_iUnion.2 ⟨N, hω, hN.le⟩
      _ ≤ P (⋃ N : ℕ, F ∩ {ω | σ ω ≤ N}) + P {ω | σ ω = ⊤} := measure_union_le _ _
      _ = P (⋃ N : ℕ, F ∩ {ω | σ ω ≤ N}) := by rw [hnull, add_zero]
  have hmono : ∀ F : Set Ω, Monotone fun N : ℕ => F ∩ {ω | σ ω ≤ N} := by
    intro F M N hMN ω hω
    refine ⟨hω.1, ?_⟩
    have h2 : σ ω ≤ M := hω.2
    show σ ω ≤ N
    exact h2.trans (by exact_mod_cast hMN)
  have hlimA : Tendsto (fun N : ℕ => P ((E ∩ {ω | restartPath B hcont
      (fun ω => (σ ω).toNNReal) ω ∈ S}) ∩ {ω | σ ω ≤ N})) atTop
      (𝓝 (P (E ∩ {ω | restartPath B hcont (fun ω => (σ ω).toNNReal) ω ∈ S}))) := by
    have h := tendsto_measure_iUnion_atTop (μ := P) (hmono (E ∩ {ω | restartPath B hcont
      (fun ω => (σ ω).toNNReal) ω ∈ S}))
    rw [hUn] at h
    exact h
  have hlimE : Tendsto (fun N : ℕ => P (E ∩ {ω | σ ω ≤ N}) * p) atTop (𝓝 (P E * p)) := by
    have h := tendsto_measure_iUnion_atTop (μ := P) (hmono E)
    rw [hUn] at h
    exact ENNReal.Tendsto.mul_const h (Or.inr (measure_ne_top P _))
  exact tendsto_nhds_unique (Tendsto.congr hstep' hlimA) hlimE

end LatticeProb
