import LatticeProb.Prob.Process.BDGUpper

/-!
# Stopped dyadic skeletons and their square functions

Ported from the vertex-reinforced walk development. Stopping times on the dyadic grid, optional
stopping for countable ranges and for continuous martingales, the path facts of the stopped
skeleton, the stopped `Lᵖ` contraction, and the square-function bound for the lower half of the
Burkholder–Davis–Gundy inequality at exponents `1 < p < 2`.
-/

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

namespace LatticeProb.Process.StoppedSkeleton.ContinuousOST

noncomputable section

/-- The stopped process at a finite stopping time `ρ` is the process read at `min u (ρ ω)`. -/
theorem stoppedProcess_coe {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) :
    stoppedProcess X (fun ω => (ρ ω : WithTop ℝ≥0)) u ω = X (min u (ρ ω)) ω := by
  show X (min (u : WithTop ℝ≥0) (ρ ω : WithTop ℝ≥0)).untopA ω = _
  rw [← WithTop.coe_min]
  rfl

/-- If `ρ` is the clipped time `min τ t` and `u ≤ t`, then the stopped process at time `u` is the
process read at `min u (ρ ω)`. -/
theorem stoppedProcess_eq_of_clip {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    {t u : ℝ≥0} (hu : u ≤ t) (ρ : Ω → ℝ≥0)
    (hρ : ∀ ω, (ρ ω : WithTop ℝ≥0) = min (τ ω) (t : WithTop ℝ≥0)) (ω : Ω) :
    stoppedProcess X τ u ω = X (min u (ρ ω)) ω := by
  have h : min (u : WithTop ℝ≥0) (τ ω) = ((min u (ρ ω) : ℝ≥0) : WithTop ℝ≥0) := by
    rw [WithTop.coe_min, hρ ω, min_comm (τ ω), ← min_assoc,
      min_eq_left (WithTop.coe_le_coe.2 hu)]
  show X (min (u : WithTop ℝ≥0) (τ ω)).untopA ω = _
  rw [h]
  rfl

/-- The stopped processes at countably valued stopping times, read at a fixed time `u`, are
uniformly integrable: by optional sampling they are conditional expectations of `X u`. -/
theorem uniformIntegrable_stoppedProcess {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : ℝ≥0 → Ω → ℝ)
    (hX : Martingale X ℱ P) (σ : ℕ → Ω → WithTop ℝ≥0) (hσ : ∀ m, IsStoppingTime ℱ (σ m))
    (hcount : ∀ m, (Set.range (σ m)).Countable) (u : ℝ≥0) :
    UniformIntegrable (fun m => stoppedProcess X (σ m) u) 1 P := by
  have hτ : ∀ m, IsStoppingTime ℱ (fun ω => min (u : WithTop ℝ≥0) (σ m ω)) :=
    fun m => (isStoppingTime_const ℱ u).min (hσ m)
  have hle : ∀ m ω, min (u : WithTop ℝ≥0) (σ m ω) ≤ u := fun m ω => min_le_left _ _
  have hUI := (hX.integrable u).uniformIntegrable_condExp
    (ℱ := fun m => (hτ m).measurableSpace) fun m => (hτ m).measurableSpace_le_of_le (hle m)
  refine hUI.ae_eq fun m => ?_
  have hcm : (Set.range fun ω => min (u : WithTop ℝ≥0) (σ m ω)).Countable := by
    refine ((hcount m).image fun a => min (u : WithTop ℝ≥0) a).mono ?_
    rintro _ ⟨ω, rfl⟩
    exact ⟨σ m ω, ⟨ω, rfl⟩, rfl⟩
  exact (hX.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hτ m) (hle m) hcm).symm

/-- A uniformly integrable (in `L¹`) sequence converging almost everywhere to an a.e. strongly
measurable limit has an integrable limit: Fatou's lemma for the `L¹` norm. -/
theorem integrable_of_uniformIntegrable_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {F : ℕ → Ω → ℝ} {G : Ω → ℝ} (hG : AEStronglyMeasurable G P)
    (hui : UniformIntegrable F 1 P) (hlim : ∀ᵐ ω ∂P, Tendsto (fun m => F m ω) atTop (𝓝 (G ω))) :
    Integrable G P := by
  have hFm : ∀ i, AEStronglyMeasurable (F i) P := fun i => hui.aestronglyMeasurable i
  obtain ⟨-, C, hC⟩ := hui
  refine memLp_one_iff_integrable.1 ?_
  exact lt_of_le_of_lt (Lp.eLpNorm_le_of_ae_tendsto (C := (C : ℝ≥0∞))
    (Eventually.of_forall hC) hFm hG hlim) ENNReal.coe_lt_top

/-- Vitali: a uniformly integrable sequence converging almost everywhere converges in `L¹`, hence
its set integrals converge to the set integral of the limit. -/
theorem tendsto_setIntegral_of_uniformIntegrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : ℕ → Ω → ℝ} {G : Ω → ℝ} (hG : AEStronglyMeasurable G P)
    (hui : UniformIntegrable F 1 P) (hlim : ∀ᵐ ω ∂P, Tendsto (fun m => F m ω) atTop (𝓝 (G ω)))
    (A : Set Ω) :
    Tendsto (fun m => ∫ ω in A, F m ω ∂P) atTop (𝓝 (∫ ω in A, G ω ∂P)) := by
  have hint : Integrable G P := integrable_of_uniformIntegrable_tendsto hG hui hlim
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (fun i => hui.aestronglyMeasurable i) (memLp_one_iff_integrable.2 hint) hui.unifIntegrable hlim
  exact tendsto_setIntegral_of_L1' G
    (Eventually.of_forall fun m => memLp_one_iff_integrable.1 (hui.memLp m)) hL1 A

/-- The dyadic upper approximations of the clipped stopping time `min τ t` are stopping times. -/
theorem isStoppingTime_dyUp_clip {Ω : Type} [MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (t : ℝ≥0) (ρ : Ω → ℝ≥0) (hρ : ∀ ω, (ρ ω : WithTop ℝ≥0) = min (τ ω) (t : WithTop ℝ≥0))
    (m : ℕ) :
    IsStoppingTime ℱ fun ω => ((LatticeProb.dyUp m (ρ ω) : ℝ≥0) : WithTop ℝ≥0) := by
  have hρst : IsStoppingTime ℱ fun ω => (ρ ω : ℝ≥0∞) := by
    have h := hτ.min_const t
    have e : (fun ω => (ρ ω : WithTop ℝ≥0)) = fun ω => min (τ ω) (t : WithTop ℝ≥0) := funext hρ
    rw [← e] at h
    exact h
  exact LatticeProb.isStoppingTime_dyUp hρst m

/-- The dyadic approximation step at a fixed time `u ≤ t`. Let `ρ` be the finite clipped stopping
time `min τ t`. The stopped process at time `u` is integrable, and the set integrals of the stopped
processes at the dyadic upper approximations of `ρ` converge to its set integrals. -/
theorem approx_stopped_integrals {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (hX : Martingale X ℱ P) (hcont : ∀ ω, Continuous fun t => X t ω)
    (hτ : IsStoppingTime ℱ τ) {t u : ℝ≥0} (hu : u ≤ t) (ρ : Ω → ℝ≥0)
    (hρ : ∀ ω, (ρ ω : WithTop ℝ≥0) = min (τ ω) (t : WithTop ℝ≥0)) :
    Integrable (stoppedProcess X τ u) P ∧
      ∀ A : Set Ω, Tendsto
        (fun m : ℕ => ∫ ω in A, stoppedProcess X
          (fun ω => ((LatticeProb.dyUp m (ρ ω) : ℝ≥0) : WithTop ℝ≥0)) u ω ∂P) atTop
        (𝓝 (∫ ω in A, stoppedProcess X τ u ω ∂P)) := by
  have hσ : ∀ m : ℕ, IsStoppingTime ℱ
      fun ω => ((LatticeProb.dyUp m (ρ ω) : ℝ≥0) : WithTop ℝ≥0) :=
    fun m => isStoppingTime_dyUp_clip ℱ τ hτ t ρ hρ m
  have hui := uniformIntegrable_stoppedProcess P ℱ X hX
    (fun m ω => ((LatticeProb.dyUp m (ρ ω) : ℝ≥0) : WithTop ℝ≥0)) hσ
    (fun m => LatticeProb.countable_range_dyUp m ρ) u
  have hmeas : AEStronglyMeasurable (stoppedProcess X τ u) P :=
    ((hX.1.isStronglyProgressive_of_continuous hcont).stronglyMeasurable_stoppedProcess hτ
      u).aestronglyMeasurable
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun m : ℕ => stoppedProcess X
      (fun ω => ((LatticeProb.dyUp m (ρ ω) : ℝ≥0) : WithTop ℝ≥0)) u ω) atTop
      (𝓝 (stoppedProcess X τ u ω)) := by
    refine Eventually.of_forall fun ω => ?_
    simp_rw [stoppedProcess_coe X (fun ω => LatticeProb.dyUp _ (ρ ω)) u ω]
    rw [stoppedProcess_eq_of_clip X τ hu ρ hρ ω]
    exact ((hcont ω).continuousAt.tendsto).comp
      (tendsto_const_nhds.min (LatticeProb.tendsto_dyUp (ρ ω)))
  exact ⟨integrable_of_uniformIntegrable_tendsto hmeas hui hlim,
    fun A => tendsto_setIntegral_of_uniformIntegrable hmeas hui hlim A⟩

/-- The clipped stopping time `min τ t` is finite: it is the coercion of a nonnegative real. -/
theorem exists_clip {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) :
    ∃ ρ : Ω → ℝ≥0, ∀ ω, (ρ ω : WithTop ℝ≥0) = min (τ ω) (t : WithTop ℝ≥0) := by
  have hex : ∀ ω, ∃ r : ℝ≥0, (r : WithTop ℝ≥0) = min (τ ω) (t : WithTop ℝ≥0) := fun ω =>
    WithTop.ne_top_iff_exists.1
      (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _))
  choose ρ hρ using hex
  exact ⟨ρ, hρ⟩

/-- A continuous martingale stopped at a stopping time is integrable at every time. -/
theorem integrable_stoppedProcess {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (hX : Martingale X ℱ P) (hcont : ∀ ω, Continuous fun t => X t ω)
    (hτ : IsStoppingTime ℱ τ) (u : ℝ≥0) : Integrable (stoppedProcess X τ u) P := by
  obtain ⟨ρ, hρ⟩ := exists_clip τ u
  exact (approx_stopped_integrals P ℱ X τ hX hcont hτ le_rfl ρ hρ).1

/-- Given optional stopping at countably valued stopping times, the stopped process of a continuous
martingale has equal set integrals at times `s ≤ t` over every event of `ℱ s`. -/
theorem stoppedProcess_setIntegral_eq (hC : CountableRangeStoppedIntegral) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    (hX : Martingale X ℱ P) (hcont : ∀ ω, Continuous fun t => X t ω) (hτ : IsStoppingTime ℱ τ)
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, stoppedProcess X τ s ω ∂P = ∫ ω in A, stoppedProcess X τ t ω ∂P := by
  obtain ⟨ρ, hρ⟩ := exists_clip τ t
  have hs := (approx_stopped_integrals P ℱ X τ hX hcont hτ hst ρ hρ).2 A
  have ht := (approx_stopped_integrals P ℱ X τ hX hcont hτ le_rfl ρ hρ).2 A
  have heq : ∀ m : ℕ,
      ∫ ω in A, stoppedProcess X
        (fun ω => ((LatticeProb.dyUp m (ρ ω) : ℝ≥0) : WithTop ℝ≥0)) t ω ∂P =
      ∫ ω in A, stoppedProcess X
        (fun ω => ((LatticeProb.dyUp m (ρ ω) : ℝ≥0) : WithTop ℝ≥0)) s ω ∂P :=
    fun m => hC P ℱ X _ hX (isStoppingTime_dyUp_clip ℱ τ hτ t ρ hρ m)
      (LatticeProb.countable_range_dyUp m ρ) s t hst A hA
  exact tendsto_nhds_unique hs (ht.congr heq)

/-- **A continuous martingale stopped at any stopping time is a martingale**, given optional
stopping for stopping times with countably many values. -/
theorem continuousStoppedMartingale_of_countable (hC : CountableRangeStoppedIntegral) :
    ContinuousStoppedMartingale := by
  intro Ω inst P hP ℱ X τ hX hcont hτ
  have hadapt : StronglyAdapted ℱ (stoppedProcess X τ) :=
    (hX.1.isStronglyProgressive_of_continuous hcont).stronglyAdapted_stoppedProcess hτ
  refine ⟨hadapt, fun s t hst => ?_⟩
  exact (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s)
    (integrable_stoppedProcess P ℱ X τ hX hcont hτ t)
    (fun A _ _ => (integrable_stoppedProcess P ℱ X τ hX hcont hτ s).integrableOn)
    (fun A hA _ => stoppedProcess_setIntegral_eq hC P ℱ X τ hX hcont hτ hst hA)
    (hadapt s).aestronglyMeasurable).symm

end

end LatticeProb.Process.StoppedSkeleton.ContinuousOST


namespace LatticeProb.Process.StoppedSkeleton.StoppingTime

noncomputable section

/-- The infimum of a finite family of stopping times is a stopping time. -/
theorem isStoppingTime_finset_inf {Ω κ : Type*} {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} (s : Finset κ) (τ : κ → Ω → WithTop ℝ≥0)
    (hτ : ∀ k ∈ s, IsStoppingTime ℱ (τ k)) :
    IsStoppingTime ℱ fun ω => s.inf (fun k => τ k ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro i
    have hempty : {ω : Ω | (∅ : Finset κ).inf (fun k => τ k ω) ≤ (i : WithTop ℝ≥0)} = ∅ := by
      ext ω
      refine ⟨fun hω => absurd hω ?_, fun hω => absurd hω (Set.notMem_empty ω)⟩
      intro hω
      exact WithTop.not_top_le_coe i (by simpa only [Set.mem_ofPred_eq, Finset.inf_empty] using hω)
    rw [hempty]
    exact @MeasurableSet.empty _ (ℱ i)
  | insert a s ha ih =>
    have h1 := hτ a (Finset.mem_insert_self a s)
    have h2 := ih (fun k hk => hτ k (Finset.mem_insert_of_mem hk))
    have h3 := h1.min h2
    simpa only [Finset.inf_insert] using h3

/-- The grid times are monotone in the index. -/
theorem gridT_mono (T : ℝ≥0) (n : ℕ) {j k : ℕ} (h : j ≤ k) : gridT T n j ≤ gridT T n k := by
  unfold gridT
  gcongr

/-- The running sum of squared grid increments is measurable as soon as the path values at the
grid times `t_j`, `j ≤ k`, are measurable. -/
theorem measurable_gridSq {Ω : Type*} {mi : MeasurableSpace Ω} (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (n k : ℕ) (hX : ∀ j, j ≤ k → Measurable (X (gridT T n j))) :
    Measurable fun ω => gridSq (fun t => X t ω) T n k := by
  unfold gridSq
  refine Finset.measurable_sum _ fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  exact ((hX (i + 1) (by omega)).sub (hX i (by omega))).pow_const 2

/-- The event that the running sum of squared grid increments exceeds `L` is measurable. -/
theorem measurableSet_lt_gridSq {Ω : Type*} {mi : MeasurableSpace Ω} (X : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n k : ℕ) (L : ℝ) (hX : ∀ j, j ≤ k → Measurable (X (gridT T n j))) :
    MeasurableSet {ω | L < gridSq (fun t => X t ω) T n k} :=
  measurableSet_lt measurable_const (measurable_gridSq X T n k hX)

open Classical in
/-- Each term of the grid stop is a stopping time: the time `t_k` on the event that the running
sum of squared grid increments at `k` exceeds `L`, and `⊤` elsewhere. -/
theorem isStoppingTime_gridPiece {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 m)
    (X : ℝ≥0 → Ω → ℝ) (hX : StronglyAdapted ℱ X) (T : ℝ≥0) (n : ℕ) (L : ℝ) (k : ℕ) :
    IsStoppingTime ℱ fun ω =>
      if L < gridSq (fun t => X t ω) T n k then ((gridT T n k : ℝ≥0) : WithTop ℝ≥0) else ⊤ := by
  intro i
  by_cases h : gridT T n k ≤ i
  · have hmeas : MeasurableSet[ℱ (gridT T n k)] {ω | L < gridSq (fun t => X t ω) T n k} :=
      measurableSet_lt_gridSq (mi := ℱ (gridT T n k)) X T n k L fun j hj =>
        (hX _).measurable.mono (ℱ.mono (gridT_mono T n hj)) le_rfl
    refine (ℱ.mono h _ hmeas).congr ?_
    ext ω
    by_cases hc : L < gridSq (fun t => X t ω) T n k
    · refine iff_of_true hc ?_
      show (if L < gridSq (fun t => X t ω) T n k then ((gridT T n k : ℝ≥0) : WithTop ℝ≥0)
        else ⊤) ≤ (i : WithTop ℝ≥0)
      rw [ite_eq_left hc]
      exact WithTop.coe_le_coe.2 h
    · refine ⟨fun h => absurd h hc, fun hω => absurd hω fun hω => ?_⟩
      have hω' : (⊤ : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0) := by
        simpa only [Set.mem_ofPred_eq, ite_eq_right hc] using hω
      exact WithTop.not_top_le_coe i hω'
  · refine (@MeasurableSet.empty _ (ℱ i)).congr ?_
    ext ω
    refine ⟨fun h => absurd h (Set.notMem_empty ω), fun hω => absurd hω fun hω => ?_⟩
    by_cases hc : L < gridSq (fun t => X t ω) T n k
    · have hω' : ((gridT T n k : ℝ≥0) : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0) := by
        simpa only [Set.mem_ofPred_eq, ite_eq_left hc] using hω
      exact h (WithTop.coe_le_coe.1 hω')
    · have hω' : (⊤ : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0) := by
        simpa only [Set.mem_ofPred_eq, ite_eq_right hc] using hω
      exact WithTop.not_top_le_coe i hω'

/-- **Pathwise characterisation of the oscillation hit.** For a continuous path, the first
oscillation hit in the grid interval `[t_k, t_{k+1}]` is at most `i` if and only if the path
oscillates by at least `b` from its value at `t_k` at some time `s ∈ [t_k, t_{k+1}]` with
`s ≤ i`. -/
theorem oscHit_le_iff {f : ℝ≥0 → ℝ} (hf : Continuous f) (T : ℝ≥0) (n : ℕ) (b : ℝ) (k : ℕ)
    (i : ℝ≥0) :
    oscHit f T n b k ≤ (i : WithTop ℝ≥0) ↔
      ∃ s : ℝ≥0, gridT T n k ≤ s ∧ s ≤ gridT T n (k + 1) ∧ s ≤ i ∧
        b ≤ |f s - f (gridT T n k)| := by
  classical
  have hclosed : IsClosed {s : ℝ≥0 | gridT T n k ≤ s ∧ s ≤ gridT T n (k + 1) ∧
      b ≤ |f s - f (gridT T n k)|} :=
    (isClosed_le continuous_const continuous_id).inter
      ((isClosed_le continuous_id continuous_const).inter
        (isClosed_le continuous_const ((hf.sub continuous_const).abs)))
  unfold oscHit
  split_ifs with h
  · rw [WithTop.coe_le_coe]
    constructor
    · intro hle
      have hmem := hclosed.csInf_mem h (OrderBot.bddBelow _)
      exact ⟨_, hmem.1, hmem.2.1, hle, hmem.2.2⟩
    · rintro ⟨s, h1, h2, h3, h4⟩
      exact le_trans (csInf_le (OrderBot.bddBelow _) ⟨h1, h2, h4⟩) h3
  · constructor
    · intro hle
      exact absurd hle (WithTop.not_top_le_coe i)
    · rintro ⟨s, h1, h2, -, h4⟩
      exact absurd ⟨s, h1, h2, h4⟩ h

/-- The event of strictly exceeding a level on a compact time interval is decided by a countable
dense set of times. -/
theorem measurableSet_exists_Icc_lt {Ω : Type*} {mi : MeasurableSpace Ω} (X : ℝ≥0 → Ω → ℝ)
    (hcont : ∀ ω, Continuous fun t => X t ω) (a c : ℝ≥0) (A : ℝ)
    (hX : ∀ s, s ≤ c → Measurable (X s)) (hac : a ≤ c) :
    MeasurableSet {ω | ∃ s : ℝ≥0, a ≤ s ∧ s ≤ c ∧ A < |X s ω - X a ω|} := by
  classical
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense ↥(Set.Icc a c)
  have hEq : {ω | ∃ s : ℝ≥0, a ≤ s ∧ s ≤ c ∧ A < |X s ω - X a ω|}
      = ⋃ q ∈ D, {ω | A < |X (q : ℝ≥0) ω - X a ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨s, hs1, hs2, hsA⟩
      have hcont' : Continuous fun r : ↥(Set.Icc a c) => |X (r : ℝ≥0) ω - X a ω| :=
        (((hcont ω).comp continuous_subtype_val).sub continuous_const).abs
      have hopen : IsOpen {r : ↥(Set.Icc a c) | A < |X (r : ℝ≥0) ω - X a ω|} :=
        isOpen_lt continuous_const hcont'
      have hne : ({r : ↥(Set.Icc a c) | A < |X (r : ℝ≥0) ω - X a ω|}).Nonempty :=
        ⟨⟨s, hs1, hs2⟩, hsA⟩
      obtain ⟨q, hqD, hq⟩ := hDdense.exists_mem_open hopen hne
      exact ⟨q, hqD, hq⟩
    · rintro ⟨q, hqD, hq⟩
      exact ⟨(q : ℝ≥0), q.2.1, q.2.2, hq⟩
  rw [hEq]
  refine MeasurableSet.biUnion hDcount (fun q _ => ?_)
  exact measurableSet_lt measurable_const
    (continuous_abs.measurable.comp ((hX _ q.2.2).sub (hX a hac)))

/-- The event of reaching a level on a compact time interval is the countable intersection of the
events of strictly exceeding slightly lower levels, hence measurable. -/
theorem measurableSet_exists_Icc_le {Ω : Type*} {mi : MeasurableSpace Ω} (X : ℝ≥0 → Ω → ℝ)
    (hcont : ∀ ω, Continuous fun t => X t ω) (a c : ℝ≥0) (b : ℝ)
    (hX : ∀ s, s ≤ c → Measurable (X s)) :
    MeasurableSet {ω | ∃ s : ℝ≥0, a ≤ s ∧ s ≤ c ∧ b ≤ |X s ω - X a ω|} := by
  by_cases hac : a ≤ c
  swap
  · have hempty : {ω | ∃ s : ℝ≥0, a ≤ s ∧ s ≤ c ∧ b ≤ |X s ω - X a ω|} = ∅ := by
      ext ω
      refine ⟨fun hω => absurd hω ?_, fun hω => absurd hω (Set.notMem_empty ω)⟩
      simp only [Set.mem_ofPred_eq, not_exists]
      intro s h1
      exact hac (h1.1.trans h1.2.1)
    rw [hempty]
    exact MeasurableSet.empty
  have hEq : {ω | ∃ s : ℝ≥0, a ≤ s ∧ s ≤ c ∧ b ≤ |X s ω - X a ω|}
      = ⋂ j : ℕ, {ω | ∃ s : ℝ≥0, a ≤ s ∧ s ≤ c ∧ b - 1 / (j + 1 : ℝ) < |X s ω - X a ω|} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨s, hs1, hs2, hA⟩ j
      refine ⟨s, hs1, hs2, lt_of_lt_of_le ?_ hA⟩
      have : (0 : ℝ) < 1 / (j + 1 : ℝ) := by positivity
      linarith
    · intro hk
      obtain ⟨s₀, hs₀mem, hs₀max⟩ :=
        (isCompact_Icc (a := a) (b := c)).exists_isMaxOn ⟨a, le_rfl, hac⟩
          (((hcont ω).sub continuous_const).abs).continuousOn
      refine ⟨s₀, hs₀mem.1, hs₀mem.2, ?_⟩
      by_contra hcon
      have hcon' := not_le.1 hcon
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 hcon')
      obtain ⟨s, hs1, hs2, hslt⟩ := hk j
      have hle : |X s ω - X a ω| ≤ |X s₀ ω - X a ω| := hs₀max ⟨hs1, hs2⟩
      linarith
  rw [hEq]
  exact MeasurableSet.iInter fun j => measurableSet_exists_Icc_lt X hcont a c _ hX hac

/-- Each oscillation hit of the grid is a stopping time. -/
theorem isStoppingTime_oscHit {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 m)
    (X : ℝ≥0 → Ω → ℝ) (hX : StronglyAdapted ℱ X) (hcont : ∀ ω, Continuous fun t => X t ω)
    (T : ℝ≥0) (n : ℕ) (b : ℝ) (k : ℕ) :
    IsStoppingTime ℱ fun ω => oscHit (fun t => X t ω) T n b k := by
  intro i
  have hmeas : MeasurableSet[ℱ i] {ω | ∃ s : ℝ≥0, gridT T n k ≤ s ∧
      s ≤ min (gridT T n (k + 1)) i ∧ b ≤ |X s ω - X (gridT T n k) ω|} :=
    measurableSet_exists_Icc_le (mi := ℱ i) X hcont _ _ b fun s hs =>
      (hX s).measurable.mono (ℱ.mono (hs.trans (min_le_right _ _))) le_rfl
  refine hmeas.congr ?_
  ext ω
  simp only [Set.mem_ofPred_eq]
  rw [oscHit_le_iff (hcont ω) T n b k i]
  simp only [le_min_iff, and_assoc]

/-- **The localising time of the dyadic skeleton is a stopping time.** The oscillation stop is the
infimum of finitely many oscillation hits, the grid stop is the infimum of finitely many grid
pieces, and the localising time is the minimum of the two. -/
theorem skeletonStopIsStoppingTime_holds : SkeletonStopIsStoppingTime := by
  intro Ω _ ℱ X hX hcont T n b L
  have hosc : IsStoppingTime ℱ fun ω => oscStop (fun t => X t ω) T n b :=
    isStoppingTime_finset_inf (Finset.range (2 ^ n))
      (fun k ω => oscHit (fun t => X t ω) T n b k)
      (fun k _ => isStoppingTime_oscHit ℱ X hX hcont T n b k)
  have hgrid : IsStoppingTime ℱ fun ω => gridStop (fun t => X t ω) T n L :=
    isStoppingTime_finset_inf (Finset.range (2 ^ n + 1))
      (fun k ω => if L < gridSq (fun t => X t ω) T n k then
        ((gridT T n k : ℝ≥0) : WithTop ℝ≥0) else ⊤)
      (fun k _ => isStoppingTime_gridPiece ℱ X hX T n L k)
  exact hosc.min hgrid

end

end LatticeProb.Process.StoppedSkeleton.StoppingTime


namespace LatticeProb.Process.StoppedSkeleton.PathFacts

noncomputable section

/-! ### Grid facts, oscillation hits, the localising time, and the four items of `SkeletonPathFacts` -/

/-- The grid time `t_0` is `0`. -/
theorem gridT_zero (T : ℝ≥0) (n : ℕ) : gridT T n 0 = 0 := by
  simp [gridT]

/-- For `T = 0` every grid time is `0`. -/
theorem gridT_of_zero (n k : ℕ) : gridT 0 n k = 0 := by
  simp [gridT]

/-- The last grid time `t_{2^n}` is `T`. -/
theorem gridT_last (T : ℝ≥0) (n : ℕ) : gridT T n (2 ^ n) = T := by
  simp [gridT]

/-- Consecutive grid times differ by `T / 2^n`. -/
theorem gridT_succ_sub (T : ℝ≥0) (n k : ℕ) :
    ((gridT T n (k + 1) : ℝ≥0) : ℝ) - ((gridT T n k : ℝ≥0) : ℝ) = (T : ℝ) / 2 ^ n := by
  simp only [gridT, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow,
    NNReal.coe_ofNat]
  push_cast
  ring

/-- The grid times are monotone in the index. -/
theorem gridT_mono (T : ℝ≥0) (n : ℕ) : Monotone (gridT T n) := by
  intro i j hij
  unfold gridT
  have : ((i : ℕ) : ℝ≥0) ≤ ((j : ℕ) : ℝ≥0) := by exact_mod_cast hij
  gcongr

/-- For `T > 0` the grid times are strictly increasing in the index. -/
theorem gridT_strictMono {T : ℝ≥0} (hT : 0 < T) (n : ℕ) : StrictMono (gridT T n) := by
  intro i j hij
  unfold gridT
  have : ((i : ℕ) : ℝ≥0) < ((j : ℕ) : ℝ≥0) := by exact_mod_cast hij
  gcongr

/-- Grid times with index at most `2^n` do not exceed `T`. -/
theorem gridT_le (T : ℝ≥0) (n k : ℕ) (hk : k ≤ 2 ^ n) : gridT T n k ≤ T :=
  (gridT_mono T n hk).trans_eq (gridT_last T n)

/-- The running sum of squared grid increments is nonnegative. -/
theorem gridSq_nonneg (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n k : ℕ) : 0 ≤ gridSq f T n k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The running sum of squared grid increments is monotone in the index. -/
theorem gridSq_mono (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) : Monotone (gridSq f T n) := by
  intro k l hkl
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkl) fun _ _ _ => sq_nonneg _

/-- One more term in the running sum of squared grid increments. -/
theorem gridSq_succ (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n k : ℕ) :
    gridSq f T n (k + 1) = gridSq f T n k + (f (gridT T n (k + 1)) - f (gridT T n k)) ^ 2 := by
  simp only [gridSq, Finset.sum_range_succ]

/-- The empty running sum of squared grid increments is `0`. -/
theorem gridSq_zero (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) : gridSq f T n 0 = 0 := by
  simp [gridSq]

/-- Every element of `WithTop ℝ≥0` is at least `0`. -/
theorem coe_zero_le (r : WithTop ℝ≥0) : ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ r := by
  induction r using WithTop.recTopCoe with
  | top => exact le_top
  | coe a => exact WithTop.coe_le_coe.2 zero_le

/-- If `t ≤ r` then `min t r` reads back as `t`. -/
theorem untopA_min_of_le {t : ℝ≥0} {r : WithTop ℝ≥0} (h : (t : WithTop ℝ≥0) ≤ r) :
    (min (t : WithTop ℝ≥0) r).untopA = t := by
  rw [min_eq_left h]
  exact WithTop.untopD_coe _ _

/-- If `ρ ≤ t` then `min t ρ` reads back as `ρ`. -/
theorem untopA_min_of_coe {t ρ : ℝ≥0} (h : ρ ≤ t) :
    (min (t : WithTop ℝ≥0) (ρ : WithTop ℝ≥0)).untopA = ρ := by
  rw [min_eq_right (WithTop.coe_le_coe.2 h)]
  exact WithTop.untopD_coe _ _

/-- If there is no oscillation hit in the `k`-th grid interval, the path stays within `b` of its value at `t_k` on the whole interval. -/
theorem oscHit_eq_top_lt {f : ℝ≥0 → ℝ} {T : ℝ≥0} {n : ℕ} {b : ℝ} {k : ℕ}
    (h : oscHit f T n b k = ⊤) {s : ℝ≥0} (h1 : gridT T n k ≤ s) (h2 : s ≤ gridT T n (k + 1)) :
    |f s - f (gridT T n k)| < b := by
  by_contra hcon
  replace hcon := not_lt.1 hcon
  unfold oscHit at h
  rw [ite_eq_left ⟨s, h1, h2, hcon⟩] at h
  exact WithTop.coe_ne_top h

/-- Properties of a finite oscillation hit `h` in the `k`-th grid interval of a continuous path: `t_k ≤ h ≤ t_{k+1}`, the distance from `f t_k` at `h` is exactly `b`, and it is less than `b` on `[t_k, h)`. -/
theorem oscHit_coe {f : ℝ≥0 → ℝ} (hf : Continuous f) {T : ℝ≥0} {n : ℕ} {b : ℝ} (hb : 0 < b)
    {k : ℕ} {h : ℝ≥0} (hh : oscHit f T n b k = (h : WithTop ℝ≥0)) :
    gridT T n k ≤ h ∧ h ≤ gridT T n (k + 1) ∧ |f h - f (gridT T n k)| = b ∧
      ∀ s : ℝ≥0, gridT T n k ≤ s → s < h → |f s - f (gridT T n k)| < b := by
  set a := gridT T n k with ha
  set S : Set ℝ≥0 := {s | a ≤ s ∧ s ≤ gridT T n (k + 1) ∧ b ≤ |f s - f a|} with hS
  have hex : ∃ s : ℝ≥0, a ≤ s ∧ s ≤ gridT T n (k + 1) ∧ b ≤ |f s - f a| := by
    by_contra hne
    unfold oscHit at hh
    rw [ite_eq_right hne] at hh
    exact WithTop.top_ne_coe hh
  have hhS : h = sInf S := by
    unfold oscHit at hh
    rw [ite_eq_left hex] at hh
    exact (WithTop.coe_injective hh).symm
  have hclosed : IsClosed S := by
    have h1 : IsClosed {s : ℝ≥0 | a ≤ s} := isClosed_le continuous_const continuous_id
    have h2 : IsClosed {s : ℝ≥0 | s ≤ gridT T n (k + 1)} :=
      isClosed_le continuous_id continuous_const
    have h3 : IsClosed {s : ℝ≥0 | b ≤ |f s - f a|} :=
      isClosed_le continuous_const (hf.sub continuous_const).abs
    exact h1.inter (h2.inter h3)
  have hmem : h ∈ S := hhS ▸ hclosed.csInf_mem hex (OrderBot.bddBelow S)
  have hlt : ∀ s : ℝ≥0, a ≤ s → s < h → |f s - f a| < b := by
    intro s hs1 hs2
    by_contra hcon
    replace hcon := not_lt.1 hcon
    have hsS : s ∈ S := ⟨hs1, hs2.le.trans hmem.2.1, hcon⟩
    have hle := csInf_le (OrderBot.bddBelow S) hsS
    rw [← hhS] at hle
    exact absurd hs2 (not_lt.2 hle)
  refine ⟨hmem.1, hmem.2.1, le_antisymm ?_ hmem.2.2, hlt⟩
  rcases hmem.1.eq_or_lt with hEq | hlt'
  · rw [← hEq]
    simp [hb.le]
  · have hcl : IsClosed {s : ℝ≥0 | |f s - f a| ≤ b} :=
      isClosed_le (hf.sub continuous_const).abs continuous_const
    have hsub : Set.Ico a h ⊆ {s : ℝ≥0 | |f s - f a| ≤ b} := fun s hs => (hlt s hs.1 hs.2).le
    have hcls := hcl.closure_subset_iff.2 hsub
    rw [closure_Ico hlt'.ne] at hcls
    exact hcls (Set.right_mem_Icc.2 hlt'.le)

/-- The oscillation stop is at most each oscillation hit. -/
theorem oscStop_le_hit (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (b : ℝ) {i : ℕ} (hi : i < 2 ^ n) :
    oscStop f T n b ≤ oscHit f T n b i :=
  Finset.inf_le (Finset.mem_range.2 hi)

/-- The oscillation stop equals the oscillation hit of some grid interval. -/
theorem exists_oscStop_eq (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (b : ℝ) :
    ∃ j, j < 2 ^ n ∧ oscStop f T n b = oscHit f T n b j := by
  obtain ⟨j, hj, h⟩ := Finset.exists_mem_eq_inf (Finset.range (2 ^ n))
    (Finset.nonempty_range_iff.2 (by positivity)) (oscHit f T n b)
  exact ⟨j, Finset.mem_range.1 hj, h⟩

/-- The grid stop is at most `t_k` whenever the running sum at `k` exceeds `L`. -/
theorem gridStop_le_coe (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (L : ℝ) {k : ℕ} (hk : k ≤ 2 ^ n)
    (hL : L < gridSq f T n k) : gridStop f T n L ≤ ((gridT T n k : ℝ≥0) : WithTop ℝ≥0) := by
  unfold gridStop
  refine le_trans (Finset.inf_le (Finset.mem_range.2 (Nat.lt_succ_of_le hk))) ?_
  exact le_of_eq (ite_eq_left hL)

open Classical in
/-- A finite grid stop is a grid time `t_K` at which the running sum exceeds `L`. -/
theorem gridStop_coe {f : ℝ≥0 → ℝ} {T : ℝ≥0} {n : ℕ} {L : ℝ} {g : ℝ≥0}
    (hg : gridStop f T n L = (g : WithTop ℝ≥0)) :
    ∃ K, K ≤ 2 ^ n ∧ L < gridSq f T n K ∧ g = gridT T n K := by
  have hne : (Finset.range (2 ^ n + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨K, hK, hK2⟩ := Finset.exists_mem_eq_inf (Finset.range (2 ^ n + 1)) hne
    (fun k => if L < gridSq f T n k then ((gridT T n k : ℝ≥0) : WithTop ℝ≥0) else ⊤)
  have hg' : (if L < gridSq f T n K then ((gridT T n K : ℝ≥0) : WithTop ℝ≥0) else ⊤) =
      (g : WithTop ℝ≥0) := by
    rw [← hK2]
    exact hg
  have hK' : K ≤ 2 ^ n := Nat.le_of_lt_succ (Finset.mem_range.1 hK)
  by_cases hL : L < gridSq f T n K
  · rw [ite_eq_left hL] at hg'
    exact ⟨K, hK', hL, (WithTop.coe_injective hg').symm⟩
  · rw [ite_eq_right hL] at hg'
    exact absurd hg'.symm WithTop.coe_ne_top

/-- The skeleton stop is at most the oscillation stop. -/
theorem skelStop_le_oscStop (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (b L : ℝ) :
    skelStop f T n b L ≤ oscStop f T n b :=
  min_le_left _ _

/-- The skeleton stop is at most the grid stop. -/
theorem skelStop_le_gridStop (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (b L : ℝ) :
    skelStop f T n b L ≤ gridStop f T n L :=
  min_le_right _ _

/-- For an index at most `2^n` the cap in `skelVal` is inactive. -/
theorem skelVal_eq_of_le (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (b L : ℝ) {k : ℕ} (hk : k ≤ 2 ^ n) :
    skelVal f T n b L k =
      f (min ((gridT T n k : ℝ≥0) : WithTop ℝ≥0) (skelStop f T n b L)).untopA := by
  unfold skelVal
  rw [min_eq_left hk]

/-- The skeleton starts at `f 0`. -/
theorem skelVal_zero (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (b L : ℝ) :
    skelVal f T n b L 0 = f 0 := by
  rw [skelVal_eq_of_le f T n b L (Nat.zero_le _), gridT_zero,
    untopA_min_of_le (coe_zero_le _)]

/-- Each of the first `2^n` increments of the stopped skeleton is at most `b` in absolute value. -/
theorem skelVal_incr_le {f : ℝ≥0 → ℝ} (hf : Continuous f) {T : ℝ≥0} (hT : 0 < T) {n : ℕ}
    {b L : ℝ} (hb : 0 < b) {i : ℕ} (hi : i < 2 ^ n) :
    |skelVal f T n b L (i + 1) - skelVal f T n b L i| ≤ b := by
  rw [skelVal_eq_of_le f T n b L (Nat.succ_le_of_lt hi), skelVal_eq_of_le f T n b L hi.le]
  have hmono : ((gridT T n i : ℝ≥0) : WithTop ℝ≥0) ≤ ((gridT T n (i + 1) : ℝ≥0) : WithTop ℝ≥0) :=
    WithTop.coe_le_coe.2 (gridT_mono T n (Nat.le_succ i))
  by_cases h1 : skelStop f T n b L ≤ ((gridT T n i : ℝ≥0) : WithTop ℝ≥0)
  · rw [min_eq_right h1, min_eq_right (h1.trans hmono)]
    simp [hb.le]
  by_cases h2 : ((gridT T n (i + 1) : ℝ≥0) : WithTop ℝ≥0) ≤ skelStop f T n b L
  · rw [untopA_min_of_le (hmono.trans h2), untopA_min_of_le h2]
    have hge : ((gridT T n (i + 1) : ℝ≥0) : WithTop ℝ≥0) ≤ oscHit f T n b i :=
      h2.trans ((skelStop_le_oscStop f T n b L).trans (oscStop_le_hit f T n b hi))
    by_cases htop : oscHit f T n b i = ⊤
    · exact (oscHit_eq_top_lt htop (gridT_mono T n (Nat.le_succ i)) le_rfl).le
    · obtain ⟨h, hh⟩ := WithTop.ne_top_iff_exists.1 htop
      obtain ⟨_, hle, habs, _⟩ := oscHit_coe hf hb hh.symm
      rw [← hh] at hge
      have heq : h = gridT T n (i + 1) := le_antisymm hle (WithTop.coe_le_coe.1 hge)
      rw [← heq]
      exact habs.le
  · replace h1 := not_le.1 h1
    replace h2 := not_le.1 h2
    obtain ⟨ρ, hρ⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt h2)
    rw [← hρ] at h1 h2
    have hs := gridT_strictMono hT n
    have hgrid : gridStop f T n L ≠ (ρ : WithTop ℝ≥0) := by
      intro hg
      obtain ⟨K, _, _, hgK⟩ := gridStop_coe hg
      rw [hgK] at h1 h2
      have a1 := hs.lt_iff_lt.1 (WithTop.coe_lt_coe.1 h1)
      have a2 := hs.lt_iff_lt.1 (WithTop.coe_lt_coe.1 h2)
      omega
    have hosc : oscStop f T n b = (ρ : WithTop ℝ≥0) := by
      have hmin : min (oscStop f T n b) (gridStop f T n L) = (ρ : WithTop ℝ≥0) := by
        rw [hρ]
        rfl
      rcases min_choice (oscStop f T n b) (gridStop f T n L) with h | h
      · rw [← h]
        exact hmin
      · exact absurd (h.symm.trans hmin) hgrid
    obtain ⟨j, hj, hjeq⟩ := exists_oscStop_eq f T n b
    rw [hosc] at hjeq
    obtain ⟨hj1, hj2, habs, _⟩ := oscHit_coe hf hb hjeq.symm
    have b1 : j < i + 1 := hs.lt_iff_lt.1 (lt_of_le_of_lt hj1 (WithTop.coe_lt_coe.1 h2))
    have b2 : i < j + 1 := hs.lt_iff_lt.1 (lt_of_lt_of_le (WithTop.coe_lt_coe.1 h1) hj2)
    have hji : j = i := by omega
    subst hji
    rw [← hρ, untopA_min_of_le h1.le, untopA_min_of_coe (WithTop.coe_lt_coe.1 h2).le]
    exact habs.le

/-- If the grid time `t_k` is at most the skeleton stop, the skeleton at `k` is `f t_k`. -/
theorem skelVal_of_le_stop (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (b L : ℝ) {k : ℕ} (hk : k ≤ 2 ^ n)
    (h : ((gridT T n k : ℝ≥0) : WithTop ℝ≥0) ≤ skelStop f T n b L) :
    skelVal f T n b L k = f (gridT T n k) := by
  rw [skelVal_eq_of_le f T n b L hk, untopA_min_of_le h]

/-- For any stop time `r` there is a largest grid index `J ≤ 2^n` with `t_J ≤ r`; all later grid times (up to `2^n`) exceed `r`. -/
theorem exists_split_index (T : ℝ≥0) (n : ℕ) (r : WithTop ℝ≥0) :
    ∃ J, J ≤ 2 ^ n ∧ ((gridT T n J : ℝ≥0) : WithTop ℝ≥0) ≤ r ∧
      (∀ k, k ≤ J → ((gridT T n k : ℝ≥0) : WithTop ℝ≥0) ≤ r) ∧
      ∀ k, J < k → k ≤ 2 ^ n → r < ((gridT T n k : ℝ≥0) : WithTop ℝ≥0) := by
  classical
  have hspec : ((gridT T n (Nat.findGreatest
      (fun k => ((gridT T n k : ℝ≥0) : WithTop ℝ≥0) ≤ r) (2 ^ n)) : ℝ≥0) : WithTop ℝ≥0) ≤ r :=
    Nat.findGreatest_spec (P := fun k => ((gridT T n k : ℝ≥0) : WithTop ℝ≥0) ≤ r) (m := 0)
      (Nat.zero_le _) (by rw [gridT_zero]; exact coe_zero_le r)
  refine ⟨Nat.findGreatest (fun k => ((gridT T n k : ℝ≥0) : WithTop ℝ≥0) ≤ r) (2 ^ n),
    Nat.findGreatest_le _, hspec, fun k hk => ?_, fun k hk1 hk2 => ?_⟩
  · exact (WithTop.coe_le_coe.2 (gridT_mono T n hk)).trans hspec
  · exact not_le.1 (Nat.findGreatest_is_greatest hk1 hk2)

/-- Abstract bound for the sum of squared increments of a sequence that follows `x` up to the index `J`, is constant afterwards, and has increments at most `b`. -/
theorem sum_sq_split (g x : ℕ → ℝ) {J N : ℕ} (hJ : J ≤ N) {b : ℝ}
    (hlow : ∀ k, k ≤ J → g k = x k)
    (hhigh : ∀ k l, J < k → k ≤ l → l ≤ N → g l = g k)
    (hstep : ∀ i, i < N → |g (i + 1) - g i| ≤ b) :
    ∑ i ∈ Finset.range N, (g (i + 1) - g i) ^ 2 ≤
      ∑ i ∈ Finset.range J, (x (i + 1) - x i) ^ 2 + b ^ 2 := by
  rw [← Finset.sum_range_add_sum_Ico _ hJ]
  have h1 : ∑ i ∈ Finset.range J, (g (i + 1) - g i) ^ 2 =
      ∑ i ∈ Finset.range J, (x (i + 1) - x i) ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    rw [hlow i hi.le, hlow (i + 1) hi]
  have h2 : ∑ i ∈ Finset.Ico J N, (g (i + 1) - g i) ^ 2 ≤ b ^ 2 := by
    rcases Nat.eq_or_lt_of_le hJ with hJN | hJN
    · subst hJN
      simp [sq_nonneg]
    · rw [Finset.sum_eq_single_of_mem J (Finset.mem_Ico.2 ⟨le_rfl, hJN⟩)]
      · exact sq_le_sq' (abs_le.1 (hstep J hJN)).1 (abs_le.1 (hstep J hJN)).2
      · intro i hi hne
        have hi := Finset.mem_Ico.1 hi
        have hJi : J < i := lt_of_le_of_ne hi.1 (Ne.symm hne)
        rw [hhigh i (i + 1) hJi (Nat.le_succ i) (Nat.succ_le_of_lt hi.2)]
        simp
  rw [h1]
  linarith

/-- The running sum of squared grid increments at the last grid index not beyond the skeleton stop is at most `L + b²`. -/
theorem gridSq_split_le {f : ℝ≥0 → ℝ} (hf : Continuous f) {T : ℝ≥0} (hT : 0 < T) {n : ℕ}
    {b L : ℝ} (hb : 0 < b) (hL : 0 ≤ L) {J : ℕ} (hJN : J ≤ 2 ^ n)
    (hJr : ((gridT T n J : ℝ≥0) : WithTop ℝ≥0) ≤ skelStop f T n b L) :
    gridSq f T n J ≤ L + b ^ 2 := by
  rcases Nat.eq_zero_or_pos J with h0 | hpos
  · subst h0
    rw [gridSq_zero]
    positivity
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hj : j < 2 ^ n := hJN
    have hjr : ((gridT T n j : ℝ≥0) : WithTop ℝ≥0) ≤ skelStop f T n b L :=
      (WithTop.coe_le_coe.2 (gridT_mono T n (Nat.le_succ j))).trans hJr
    have hstep := skelVal_incr_le (L := L) hf hT hb hj
    rw [skelVal_of_le_stop f T n b L hJN hJr, skelVal_of_le_stop f T n b L hj.le hjr] at hstep
    have hsq : (f (gridT T n (j + 1)) - f (gridT T n j)) ^ 2 ≤ b ^ 2 :=
      sq_le_sq' (abs_le.1 hstep).1 (abs_le.1 hstep).2
    have hgs : gridSq f T n j ≤ L := by
      by_contra hcon
      have hlt := not_le.1 hcon
      have hge := (skelStop_le_gridStop f T n b L).trans (gridStop_le_coe f T n L hj.le hlt)
      have hs := gridT_strictMono hT n (Nat.lt_succ_self j)
      exact absurd (hJr.trans hge) (not_le.2 (WithTop.coe_lt_coe.2 hs))
    rw [gridSq_succ]
    linarith

/-- The sum of squared increments of the stopped skeleton is at most `min (gridSq + b²) (L + 2 b²)`. -/
theorem skelVal_sum_le {f : ℝ≥0 → ℝ} (hf : Continuous f) {T : ℝ≥0} (hT : 0 < T) {n : ℕ}
    {b L : ℝ} (hb : 0 < b) (hL : 0 ≤ L) :
    ∑ i ∈ Finset.range (2 ^ n),
      (skelVal f T n b L (i + 1) - skelVal f T n b L i) ^ 2 ≤
        min (gridSq f T n (2 ^ n) + b ^ 2) (L + 2 * b ^ 2) := by
  obtain ⟨J, hJN, hJr, hlow, hhigh⟩ := exists_split_index T n (skelStop f T n b L)
  have hsum := sum_sq_split (skelVal f T n b L) (fun k => f (gridT T n k)) hJN (b := b)
    (fun k hk => skelVal_of_le_stop f T n b L (hk.trans hJN) (hlow k hk))
    (fun k l hJk hkl hlN => by
      rw [skelVal_eq_of_le f T n b L hlN, skelVal_eq_of_le f T n b L (hkl.trans hlN),
        min_eq_right (hhigh l (hJk.trans_le hkl) hlN).le, min_eq_right (hhigh k hJk (hkl.trans hlN)).le])
    (fun i hi => skelVal_incr_le hf hT hb hi)
  have hgJ : ∑ i ∈ Finset.range J, (f (gridT T n (i + 1)) - f (gridT T n i)) ^ 2 =
      gridSq f T n J := rfl
  rw [hgJ] at hsum
  have h1 := gridSq_mono f T n hJN
  have h2 := gridSq_split_le hf hT hb hL hJN hJr
  exact le_min (by linarith) (by linarith)

/-- Under the modulus condition and the bound `gridSq ≤ L`, the skeleton ends at `f T`. -/
theorem skelVal_last {f : ℝ≥0 → ℝ} {T : ℝ≥0} {n : ℕ} {b L : ℝ}
    (hmod : ∀ s t : ℝ≥0, s ≤ T → t ≤ T → |(s : ℝ) - t| ≤ (T : ℝ) / 2 ^ n → |f s - f t| < b)
    (hgs : gridSq f T n (2 ^ n) ≤ L) : skelVal f T n b L (2 ^ n) = f T := by
  have hosc : ∀ k, k < 2 ^ n → oscHit f T n b k = ⊤ := by
    intro k hk
    unfold oscHit
    rw [ite_eq_right]
    rintro ⟨s, hs1, hs2, hs3⟩
    have hsT : s ≤ T := hs2.trans (gridT_le T n (k + 1) (Nat.succ_le_of_lt hk))
    have htT : gridT T n k ≤ T := gridT_le T n k hk.le
    have habs : |(s : ℝ) - ((gridT T n k : ℝ≥0) : ℝ)| ≤ (T : ℝ) / 2 ^ n := by
      have e1 : ((gridT T n k : ℝ≥0) : ℝ) ≤ s := by exact_mod_cast hs1
      have e2 : (s : ℝ) ≤ ((gridT T n (k + 1) : ℝ≥0) : ℝ) := by exact_mod_cast hs2
      have e3 := gridT_succ_sub T n k
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact absurd (hmod s _ hsT htT habs) (not_lt.2 hs3)
  have hosc' : oscStop f T n b = ⊤ := by
    unfold oscStop
    rw [Finset.inf_eq_top_iff]
    intro k hk
    exact hosc k (Finset.mem_range.1 hk)
  have hgrid' : gridStop f T n L = ⊤ := by
    unfold gridStop
    rw [Finset.inf_eq_top_iff]
    intro k hk
    have hle : gridSq f T n k ≤ L :=
      (gridSq_mono f T n (Nat.le_of_lt_succ (Finset.mem_range.1 hk))).trans hgs
    exact ite_eq_right (not_lt.2 hle)
  have hr : skelStop f T n b L = ⊤ := by
    unfold skelStop
    rw [hosc', hgrid']
    exact min_self _
  rw [skelVal_eq_of_le f T n b L le_rfl, hr, gridT_last, untopA_min_of_le le_top]

/-- The path bookkeeping of the stopped skeleton. -/
theorem skeletonPathFacts_holds : SkeletonPathFacts := by
  intro f hf T n b L hb hL
  by_cases hT : T = 0
  · subst hT
    have hv : ∀ k, skelVal f 0 n b L k = f 0 := by
      intro k
      unfold skelVal
      rw [gridT_of_zero, untopA_min_of_le (coe_zero_le _)]
    refine ⟨hv 0, ?_, ?_, ?_⟩
    · intro i _
      rw [hv, hv, sub_self, abs_zero]
      exact hb.le
    · have hz : ∑ i ∈ Finset.range (2 ^ n),
          (skelVal f 0 n b L (i + 1) - skelVal f 0 n b L i) ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hv, hv, sub_self]
        norm_num
      rw [hz]
      exact le_min (add_nonneg (gridSq_nonneg f 0 n _) (sq_nonneg b)) (by positivity)
    · intro _ _
      exact hv _
  · have hT' : 0 < T := pos_iff_ne_zero.2 hT
    exact ⟨skelVal_zero f T n b L, fun i hi => skelVal_incr_le hf hT' hb hi,
      skelVal_sum_le hf hT' hb hL, fun hmod hgs => skelVal_last hmod hgs⟩

end

end LatticeProb.Process.StoppedSkeleton.PathFacts


namespace LatticeProb.Process.BdgUpperContinuous.SkelAssembly

noncomputable section


/-- The coordinate of a one-dimensional vector-valued martingale is a real martingale. -/
theorem martingale_coord_zero {Ω : Type} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 m0} {M : ℝ≥0 → Ω → Fin 1 → ℝ} (hM : Martingale M ℱ P) :
    Martingale (fun t ω => M t ω 0) ℱ P := by
  refine ⟨fun t => ?_, fun i j hij => ?_⟩
  · exact (continuous_apply (0 : Fin 1)).comp_stronglyMeasurable (hM.1 t)
  · have h1 : (fun ω => (P[M j | ℱ i]) ω 0) =ᵐ[P] P[fun ω => M j ω 0 | ℱ i] :=
      ContinuousLinearMap.comp_condExp_comm (hM.integrable j)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
    filter_upwards [h1, hM.2 i j hij] with ω h1ω h2ω
    rw [← h1ω, h2ω]

/-- The dyadic grid times `t_k = T k / 2^n` are monotone in the index `k`. -/
theorem gridT_monotone (T : ℝ≥0) (n : ℕ) : Monotone (LatticeProb.Process.StoppedSkeleton.gridT T n) := by
  intro i j hij
  unfold LatticeProb.Process.StoppedSkeleton.gridT
  exact mul_le_mul_right (div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) zero_le) T

/-- The capped grid times `t_{min k 2^n}` are monotone in the index `k`. -/
theorem cappedGridT_monotone (T : ℝ≥0) (n : ℕ) :
    Monotone fun k : ℕ => LatticeProb.Process.StoppedSkeleton.gridT T n (min k (2 ^ n)) :=
  fun _ _ hij => gridT_monotone T n (min_le_min_right _ hij)

/-- **The stopped dyadic skeleton from its three components**: optional stopping for continuous
martingales, the localising time being a stopping time, and the path bookkeeping of the skeleton. -/
theorem stoppedDyadicSkeleton_of_components
    (hOST : LatticeProb.Process.StoppedSkeleton.ContinuousStoppedMartingale)
    (hStop : LatticeProb.Process.StoppedSkeleton.SkeletonStopIsStoppingTime)
    (hPath : LatticeProb.Process.StoppedSkeleton.SkeletonPathFacts) : StoppedDyadicSkeleton := by
  intro Ω _ P _ ℱ M T hM hcont h0 n b L hb hL
  let X : ℝ≥0 → Ω → ℝ := fun t ω => M t ω 0
  have hX : Martingale X ℱ P := martingale_coord_zero hM
  have hXcont : ∀ ω, Continuous fun t => X t ω :=
    fun ω => (continuous_apply (0 : Fin 1)).comp (hcont ω)
  have hτ := hStop ℱ X hX.1 hXcont T n b L
  have hY := hOST P ℱ X _ hX hXcont hτ
  let g : ℕ → ℝ≥0 := fun k => LatticeProb.Process.StoppedSkeleton.gridT T n (min k (2 ^ n))
  have hg : Monotone g := cappedGridT_monotone T n
  let 𝒢 : Filtration ℕ ‹MeasurableSpace Ω› :=
    ⟨fun k => ℱ (g k), fun _ _ hij => ℱ.mono (hg hij), fun k => ℱ.le _⟩
  refine ⟨𝒢, fun k ω => LatticeProb.Process.StoppedSkeleton.skelVal (fun t => X t ω) T n b L k,
    ⟨fun k => hY.1 (g k), fun i j hij => hY.2 (g i) (g j) (hg hij)⟩, ?_, ?_, ?_, ?_⟩
  · intro ω
    have h := (hPath (fun t => X t ω) (hXcont ω) T n hb hL).1
    show LatticeProb.Process.StoppedSkeleton.skelVal (fun t => X t ω) T n b L 0 = 0
    rw [h]
    show M 0 ω 0 = 0
    simp [h0 ω]
  · intro i hi ω
    exact (hPath (fun t => X t ω) (hXcont ω) T n hb hL).2.1 i hi
  · intro ω
    have h := (hPath (fun t => X t ω) (hXcont ω) T n hb hL).2.2.1
    rw [LatticeProb.Process.StoppedSkeleton.realizedCovar_eq_gridSq]
    exact h
  · intro ω hmod hrc
    rw [LatticeProb.Process.StoppedSkeleton.realizedCovar_eq_gridSq] at hrc
    exact (hPath (fun t => X t ω) (hXcont ω) T n hb hL).2.2.2 hmod hrc

end

end LatticeProb.Process.BdgUpperContinuous.SkelAssembly


namespace LatticeProb.Process.BdgUpperContinuous

/-- **The localisation of a continuous martingale on its dyadic skeleton** holds. -/
theorem stoppedDyadicSkeleton_holds : StoppedDyadicSkeleton :=
  SkelAssembly.stoppedDyadicSkeleton_of_components
    (LatticeProb.Process.StoppedSkeleton.ContinuousOST.continuousStoppedMartingale_of_countable
      LatticeProb.Process.StoppedSkeleton.CountableOST.countableRangeStoppedIntegral_holds)
    LatticeProb.Process.StoppedSkeleton.StoppingTime.skeletonStopIsStoppingTime_holds
    LatticeProb.Process.StoppedSkeleton.PathFacts.skeletonPathFacts_holds

/-- **The upper half of the Burkholder–Davis–Gundy statement** holds for every `p > 1`. -/
theorem burkholderDavisGundyUpper_holds : BurkholderDavisGundyUpper :=
  bdgUpper_of_skeleton stoppedDyadicSkeleton_holds

end LatticeProb.Process.BdgUpperContinuous



/-!
## The lower half: component statements

The lower Burkholder–Davis–Gundy bound `c E Q^{p/2} ≤ E |M_T|^p` is split into:

* `SquareMaximalBoundedAt p`: the discrete square function is controlled by the maximal function,
  for martingales with increments at most `b` (Garsia–Neveu for `p ≥ 2`; predictable weights,
  Abel summation and Hölder for `1 < p < 2`);
* `StoppedLpContraction`: stopping a continuous martingale does not increase `E |·|^p`, `p ≥ 1`;
* `SkeletonFullSum`: on the good event the skeleton is not stopped, so its square sum is the
  full sum of squared grid increments;
* `StoppedDyadicSkeletonLower`: the stopped skeleton with the three properties used below;
* `DiscreteLowerBoundedAt p` and `BdgLowerAt p`: the discrete and the continuous lower bounds.
-/

namespace LatticeProb.Process.StoppedSkeleton

noncomputable section

/-- **Square function by the maximal function, bounded increments, exponent `p`.** Every discrete
real martingale `Z` from `0` with increments at most `b` on `i < N` satisfies
`E (∑_{i<N} (Z_{i+1} - Z_i)²)^{p/2} ≤ C_p (E (max_{k ≤ N} |Z_k|)^p + b^p)`. -/
def SquareMaximalBoundedAt (p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ) (N : ℕ) {b : ℝ}, 0 < b →
      Martingale Z 𝒢 P → (∀ ω, Z 0 ω = 0) →
      (∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) →
        ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ∂P ≤
          ENNReal.ofReal C *
            (∫⁻ ω, (⨆ k ≤ N, ENNReal.ofReal |Z k ω|) ^ p ∂P + ENNReal.ofReal (b ^ p))

/-- **Stopping a continuous martingale contracts `Lᵖ`, `p ≥ 1`.** -/
def StoppedLpContraction : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0),
    Martingale X ℱ P → (∀ ω, Continuous fun t => X t ω) → IsStoppingTime ℱ τ →
    ∀ (t : ℝ≥0) {p : ℝ}, 1 ≤ p →
      ∫⁻ ω, ENNReal.ofReal |stoppedProcess X τ t ω| ^ p ∂P ≤
        ∫⁻ ω, ENNReal.ofReal |X t ω| ^ p ∂P

/-- **On the good event the skeleton is the full grid skeleton.** If the path oscillates by less
than `b` over every pair of times in `[0, T]` at distance at most `T / 2^n`, and the full sum of
squared grid increments is at most `L`, then the square sum of the stopped skeleton equals that full
sum. -/
def SkeletonFullSum : Prop :=
  ∀ (f : ℝ≥0 → ℝ), Continuous f → ∀ (T : ℝ≥0) (n : ℕ) {b L : ℝ}, 0 < b → 0 ≤ L →
    (∀ s t : ℝ≥0, s ≤ T → t ≤ T → |(s : ℝ) - t| ≤ (T : ℝ) / 2 ^ n → |f s - f t| < b) →
    gridSq f T n (2 ^ n) ≤ L →
      ∑ i ∈ Finset.range (2 ^ n), (skelVal f T n b L (i + 1) - skelVal f T n b L i) ^ 2 =
        gridSq f T n (2 ^ n)

end

end LatticeProb.Process.StoppedSkeleton

namespace LatticeProb.Process.BdgUpperContinuous

noncomputable section

/-- The lower half of the Burkholder–Davis–Gundy statement at the exponent `p`: there is
`c > 0` such that `c E Q^{p/2} ≤ E |M_T|^p` for every real continuous martingale `M` from `0` whose
quadratic covariation at the deterministic time `T` is `Q`. -/
def BdgLowerAt (p : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → Fin 1 → ℝ) (T : ℝ≥0)
      (Q : Ω → Fin 1 → Fin 1 → ℝ),
      Martingale M ℱ P → (∀ ω, Continuous fun t => M t ω) → (∀ ω, M 0 ω = 0) →
      LatticeProb.Process.HasQuadCovar P M T Q →
        ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal (Q ω 0 0) ^ (p / 2) ∂P ≤
          ∫⁻ ω, ‖M T ω 0‖ₑ ^ p ∂P

/-- **Discrete lower Burkholder bound with a bounded-increment term, exponent `p`.** -/
def DiscreteLowerBoundedAt (p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ) (N : ℕ) {b : ℝ}, 0 < b →
      Martingale Z 𝒢 P → (∀ ω, Z 0 ω = 0) →
      (∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) →
        ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ∂P ≤
          ENNReal.ofReal C * (∫⁻ ω, ENNReal.ofReal |Z N ω| ^ p ∂P + ENNReal.ofReal (b ^ p))

/-- **The stopped dyadic skeleton for the lower bound.** For a real continuous martingale `M` from
`0`, a level `n`, `b > 0` and `L ≥ 0`, there is a discrete martingale `Z` from `0` with increments at
most `b`, whose terminal value has `p`-th moment at most that of `M_T` for every `p ≥ 1`, and whose
square sum equals the full dyadic realized covariation on the event where the paths oscillate by
less than `b` at the scale `T / 2^n` and the realized covariation is at most `L`. -/
def StoppedDyadicSkeletonLower : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → Fin 1 → ℝ) (T : ℝ≥0),
    Martingale M ℱ P → (∀ ω, Continuous fun t => M t ω) → (∀ ω, M 0 ω = 0) →
    ∀ (n : ℕ) {b L : ℝ}, 0 < b → 0 ≤ L →
      ∃ (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ),
        Martingale Z 𝒢 P ∧ (∀ ω, Z 0 ω = 0) ∧
        (∀ i, i < 2 ^ n → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) ∧
        (∀ p : ℝ, 1 ≤ p →
          ∫⁻ ω, ENNReal.ofReal |Z (2 ^ n) ω| ^ p ∂P ≤ ∫⁻ ω, ‖M T ω 0‖ₑ ^ p ∂P) ∧
        (∀ ω, (∀ s t : ℝ≥0, s ≤ T → t ≤ T → |(s : ℝ) - t| ≤ (T : ℝ) / 2 ^ n →
            |M s ω 0 - M t ω 0| < b) →
          LatticeProb.Process.realizedCovar M T n ω 0 0 ≤ L →
          ∑ i ∈ Finset.range (2 ^ n), (Z (i + 1) ω - Z i ω) ^ 2 = LatticeProb.Process.realizedCovar M T n ω 0 0)

end

end LatticeProb.Process.BdgUpperContinuous

/-!
## The square function is controlled by the maximal function for `1 < p < 2`

For a discrete martingale `Z` from `0` with increments at most `b`, write `d_k = Z_{k+1} - Z_k`,
`M_k = max_{j ≤ k} |Z_j|`, `Y_k = M_k + b`, `w_k = Y_k^(p-2)` and `A = ∑_{k<N} w_k d_k²`.

* `w_k Z_k` is bounded and measurable for the history up to time `k`, so it is orthogonal to `d_k`;
  hence the expectation of `A` equals the expectation of `∑ w_k (Z_{k+1}² - Z_k²)`.
* A pointwise Abel summation, with the tangent-line bounds for `t^(p-2)` and `t^p`, shows
  `∑_{k<N} w_k (Z_{k+1}² - Z_k²) ≤ (2/p) Y_N^p`.
* Since `w_k ≥ Y_N^(p-2)`, the square sum satisfies `S ≤ A Y_N^(2-p)`, and the weighted
  arithmetic–geometric mean inequality gives `S^(p/2) ≤ (p/2) A + (1 - p/2) Y_N^p`.
* Integrating gives `E S^(p/2) ≤ (2 - p/2) E Y_N^p`, and `Y^p ≤ 2^p (M^p + b^p)`.
-/

namespace LatticeProb.Process.StoppedSkeleton.SquareMaxLow

noncomputable section

/-- A bounded measurable real function is integrable on a probability space. -/
lemma integrable_of_abs_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (h : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using h ω)

/-- The martingale difference `X (i+1) - X i` has zero conditional mean given `ℱ i`. -/
lemma condExp_diff_ae_zero {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ} (hM : Martingale X ℱ P)
    (i : ℕ) : P[fun ω => X (i + 1) ω - X i ω | ℱ i] =ᵐ[P] 0 := by
  have h3 := condExp_sub (μ := P) (hM.integrable (i + 1)) (hM.integrable i) (ℱ i)
  have h1 : P[X (i + 1) | ℱ i] =ᵐ[P] X i := hM.condExp_ae_eq (Nat.le_succ i)
  have h2 : P[X i | ℱ i] = X i :=
    condExp_of_stronglyMeasurable (ℱ.le i) (hM.stronglyMeasurable i) (hM.integrable i)
  filter_upwards [h3, h1] with ω e3 e1
  show P[X (i + 1) - X i | ℱ i] ω = 0
  rw [e3]
  simp only [Pi.sub_apply]
  rw [e1, h2, sub_self]

/-- A discrete martingale from `0` with increments at most `b` on `i < N` satisfies
`|Z_k| ≤ k b` for `k ≤ N`. -/
lemma abs_le_mul_of_increments {Ω : Type*} {Z : ℕ → Ω → ℝ} {N : ℕ} {b : ℝ}
    (hZ0 : ∀ ω, Z 0 ω = 0) (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) (ω : Ω) :
    ∀ k, k ≤ N → |Z k ω| ≤ k * b := by
  intro k
  induction k with
  | zero => intro _; simp [hZ0]
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := hinc k (by omega) ω
    have h3 : |Z (k + 1) ω| ≤ |Z k ω| + |Z (k + 1) ω - Z k ω| := by
      calc |Z (k + 1) ω| = |Z k ω + (Z (k + 1) ω - Z k ω)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    push_cast
    linarith

/-- For a bounded `ℱ i`-measurable `g`, `g (X_{i+1} - X_i)` is integrable and has integral `0`. -/
lemma integral_mul_diff_eq_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ)
    (hM : Martingale X ℱ P) (i : ℕ) {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ i] g) {C : ℝ}
    (hgb : ∀ ω, |g ω| ≤ C) :
    Integrable (fun ω => g ω * (X (i + 1) ω - X i ω)) P ∧
      ∫ ω, g ω * (X (i + 1) ω - X i ω) ∂P = 0 := by
  have hdI : Integrable (fun ω => X (i + 1) ω - X i ω) P :=
    (hM.integrable (i + 1)).sub (hM.integrable i)
  have hIh : Integrable (fun ω => g ω * (X (i + 1) ω - X i ω)) P :=
    hdI.bdd_mul (hg.mono (ℱ.le i)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hgb ω)
  refine ⟨hIh, ?_⟩
  have h1 := condExp_mul_of_stronglyMeasurable_left (μ := P) (m := ℱ i) hg
    (g := fun ω => X (i + 1) ω - X i ω) (by exact hIh) hdI
  have h2 := condExp_diff_ae_zero hM i
  calc ∫ ω, g ω * (X (i + 1) ω - X i ω) ∂P
      = ∫ ω, P[g * (fun ω => X (i + 1) ω - X i ω) | ℱ i] ω ∂P :=
        (integral_condExp (ℱ.le i)).symm
    _ = ∫ ω, (0 : ℝ) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [h1, h2] with ω e1 e2
        rw [e1]
        show g ω * P[fun ω => X (i + 1) ω - X i ω | ℱ i] ω = 0
        rw [e2]
        simp
    _ = 0 := integral_zero _ _

/-- For a bounded measurable nonnegative `f`, `E (ofReal f)^q = ofReal (E f^q)`. -/
lemma lintegral_ofReal_rpow_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (h0 : ∀ ω, 0 ≤ f ω)
    (hC : ∀ ω, f ω ≤ C) {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ^ q ∂P = ENNReal.ofReal (∫ ω, f ω ^ q ∂P) := by
  have hI : Integrable (fun ω => f ω ^ q) P := by
    refine integrable_of_abs_le (C := C ^ q) (hf.pow_const q) fun ω => ?_
    rw [abs_of_nonneg (Real.rpow_nonneg (h0 ω) _)]
    exact Real.rpow_le_rpow (h0 ω) (hC ω) hq
  rw [ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (h0 ω) _)]
  refine lintegral_congr fun ω => ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (h0 ω) hq]

/-- `ofReal` commutes with the nonempty `Finset.sup'` of reals. -/
lemma ofReal_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    ENNReal.ofReal (s.sup' hs f) = s.sup' hs (fun i => ENNReal.ofReal (f i)) := by
  apply le_antisymm
  · refine Finset.sup'_induction hs f
      (p := fun a => ENNReal.ofReal a ≤ s.sup' hs (fun i => ENNReal.ofReal (f i))) ?_ ?_
    · intro a₁ _ a₂ _
      change ENNReal.ofReal (max a₁ a₂) ≤ s.sup' hs (fun i => ENNReal.ofReal (f i))
      rw [ENNReal.ofReal_max]
      exact max_le ‹_› ‹_›
    · intro b hb
      exact Finset.le_sup' (fun i => ENNReal.ofReal (f i)) hb
  · exact Finset.sup'_le hs _ fun i hi => ENNReal.ofReal_le_ofReal (Finset.le_sup' f hi)

/-- Identification of the `Finset.sup'` maximal with the `iSup` maximal. -/
lemma sup'_range_eq_iSup (n : ℕ) (f : ℕ → ℝ≥0∞) :
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one f = ⨆ k ≤ n, f k := by
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro k hk
    exact le_iSup_of_le k (le_iSup_of_le (by simpa [Finset.mem_range] using hk) le_rfl)
  · refine iSup_le fun k => iSup_le fun hk => ?_
    exact Finset.le_sup' f (by simp only [Finset.mem_range]; omega)

/-- `(x + y) ^ q ≤ 2 ^ q (x ^ q + y ^ q)` in `ℝ≥0∞` for `q ≥ 0`. -/
lemma add_rpow_le_two_rpow_mul {q : ℝ} (hq : 0 ≤ q) (x y : ℝ≥0∞) :
    (x + y) ^ q ≤ 2 ^ q * (x ^ q + y ^ q) := by
  have h1 : x + y ≤ 2 * max x y := by
    calc x + y ≤ max x y + max x y := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * max x y := (two_mul _).symm
  calc (x + y) ^ q ≤ (2 * max x y) ^ q := ENNReal.rpow_le_rpow h1 hq
    _ = 2 ^ q * (max x y) ^ q := ENNReal.mul_rpow_of_nonneg _ _ hq
    _ ≤ 2 ^ q * (x ^ q + y ^ q) := by
      gcongr
      rcases le_total x y with h | h
      · rw [max_eq_right h]; exact le_add_self
      · rw [max_eq_left h]; exact le_self_add

/-! ### Scalar inequalities -/

/-- Tangent-line bound for a negative power: for `t > 0` and `r ≥ 0`, `1 + r - r t ≤ t^(-r)`. -/
lemma one_add_sub_mul_le_rpow_neg {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    1 + r - r * t ≤ t ^ (-r) := by
  have h1 : 0 < 1 + r := by linarith
  have key := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 / (1 + r)) (w₂ := r / (1 + r))
    (p₁ := t ^ (-r)) (p₂ := t) (by positivity) (by positivity) (Real.rpow_nonneg ht.le _) ht.le
    (by rw [← add_div]; exact div_self h1.ne')
  have e : (t ^ (-r)) ^ (1 / (1 + r)) * t ^ (r / (1 + r)) = 1 := by
    rw [← Real.rpow_mul ht.le, ← Real.rpow_add ht]
    have : -r * (1 / (1 + r)) + r / (1 + r) = 0 := by ring
    rw [this, Real.rpow_zero]
  rw [e] at key
  have h3 : (1 + r) * 1 ≤ (1 + r) * (1 / (1 + r) * t ^ (-r) + r / (1 + r) * t) :=
    mul_le_mul_of_nonneg_left key h1.le
  have h4 : (1 + r) * (1 / (1 + r) * t ^ (-r) + r / (1 + r) * t) = t ^ (-r) + r * t := by
    field_simp
  linarith

/-- `y^(p-2) * y^2 = y^p` for `y > 0`. -/
lemma rpow_sub_two_mul_sq {p y : ℝ} (hy : 0 < y) : y ^ (p - 2) * y ^ 2 = y ^ p := by
  rw [← Real.rpow_two, ← Real.rpow_add hy]
  congr 1
  ring

/-- The gap of the weights against the growth of the power: for `1 < p < 2` and `x, y > 0`,
`(x^(p-2) - y^(p-2)) x² ≤ ((2-p)/p) (y^p - x^p)`.  It combines the tangent-line bound for
`t ↦ t^(p-2)` with the tangent-line bound for `t ↦ t^p`. -/
lemma weight_gap_le {p x y : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hx : 0 < x) (hy : 0 < y) :
    (x ^ (p - 2) - y ^ (p - 2)) * x ^ 2 ≤ (2 - p) / p * (y ^ p - x ^ p) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨t, ht0, hyt⟩ : ∃ t : ℝ, 0 < t ∧ y = x * t := ⟨y / x, div_pos hy hx, by field_simp⟩
  subst hyt
  have h1 : 1 + (2 - p) - (2 - p) * t ≤ t ^ (p - 2) := by
    have h := one_add_sub_mul_le_rpow_neg ht0 (r := 2 - p) (by linarith)
    have e : -(2 - p) = p - 2 := by ring
    rwa [e] at h
  have h2 : 1 + p * (t - 1) ≤ t ^ p := by
    have h := one_add_mul_self_le_rpow_one_add (s := t - 1) (by linarith) hp1.le
    have e : 1 + (t - 1) = t := by ring
    rwa [e] at h
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx _
  have h3 : 1 - t ^ (p - 2) ≤ (2 - p) / p * (t ^ p - 1) := by
    have h4 : t - 1 ≤ (t ^ p - 1) / p := by
      rw [le_div_iff₀ hp0]
      linarith
    calc 1 - t ^ (p - 2) ≤ (2 - p) * (t - 1) := by linarith
      _ ≤ (2 - p) * ((t ^ p - 1) / p) := mul_le_mul_of_nonneg_left h4 (by linarith)
      _ = (2 - p) / p * (t ^ p - 1) := by ring
  rw [Real.mul_rpow hx.le ht0.le, Real.mul_rpow hx.le ht0.le]
  calc (x ^ (p - 2) - x ^ (p - 2) * t ^ (p - 2)) * x ^ 2
      = x ^ p * (1 - t ^ (p - 2)) := by
        rw [← rpow_sub_two_mul_sq (p := p) hx]
        ring
    _ ≤ x ^ p * ((2 - p) / p * (t ^ p - 1)) := mul_le_mul_of_nonneg_left h3 hxp.le
    _ = (2 - p) / p * (x ^ p * t ^ p - x ^ p) := by ring

/-- The scalar step of the Abel summation: for `0 < x ≤ y` and `s ≤ x²`,
`(x^(p-2) - y^(p-2)) s ≤ ((2-p)/p) (y^p - x^p)`. -/
lemma weight_gap_step_le {p x y s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hx : 0 < x) (hxy : x ≤ y)
    (hs : s ≤ x ^ 2) :
    (x ^ (p - 2) - y ^ (p - 2)) * s ≤ (2 - p) / p * (y ^ p - x ^ p) := by
  have hd : 0 ≤ x ^ (p - 2) - y ^ (p - 2) :=
    sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith))
  calc (x ^ (p - 2) - y ^ (p - 2)) * s ≤ (x ^ (p - 2) - y ^ (p - 2)) * x ^ 2 :=
        mul_le_mul_of_nonneg_left hs hd
    _ ≤ _ := weight_gap_le hp1 hp2 hx (hx.trans_le hxy)

/-- **Pointwise Abel summation.** For a real sequence `z` from `0` and a positive nondecreasing
sequence `y` with `|z_{k+1}| ≤ y_k` for `k < N`,
`∑_{k<N} y_k^(p-2) (z_{k+1}² - z_k²) ≤ (2/p) y_N^p`. -/
lemma abel_sum_le {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {z y : ℕ → ℝ} {N : ℕ}
    (hy0 : ∀ k, 0 < y k) (hmono : ∀ k, y k ≤ y (k + 1)) (hz0 : z 0 = 0)
    (hz : ∀ k, k < N → |z (k + 1)| ≤ y k) :
    ∑ k ∈ Finset.range N, y k ^ (p - 2) * (z (k + 1) ^ 2 - z k ^ 2) ≤ 2 / p * y N ^ p := by
  have hp0 : 0 < p := by linarith
  have hc : 0 ≤ (2 - p) / p := div_nonneg (by linarith) hp0.le
  have hsq : ∀ k, k < N → z (k + 1) ^ 2 ≤ y k ^ 2 := fun k hk =>
    sq_le_sq' (abs_le.mp (hz k hk)).1 (abs_le.mp (hz k hk)).2
  have key : ∀ n, n + 1 ≤ N →
      ∑ k ∈ Finset.range (n + 1), y k ^ (p - 2) * (z (k + 1) ^ 2 - z k ^ 2) ≤
        y n ^ (p - 2) * z (n + 1) ^ 2 + (2 - p) / p * (y n ^ p - y 0 ^ p) := by
    intro n
    induction n with
    | zero => intro _; simp [hz0]
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      rw [Finset.sum_range_succ]
      have h2 := weight_gap_step_le hp1 hp2 (hy0 n) (hmono n) (hsq n (by omega))
      linarith
  cases N with
  | zero =>
    have h0 := mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp0.le)
      (Real.rpow_nonneg (hy0 0).le p)
    simpa using h0
  | succ n =>
    have h1 := key n le_rfl
    have h2 : y n ^ (p - 2) * z (n + 1) ^ 2 ≤ y n ^ p := by
      rw [← rpow_sub_two_mul_sq (p := p) (hy0 n)]
      exact mul_le_mul_of_nonneg_left (hsq n (Nat.lt_succ_self n))
        (Real.rpow_nonneg (hy0 n).le _)
    have h3 : y n ^ p ≤ y (n + 1) ^ p := Real.rpow_le_rpow (hy0 n).le (hmono n) hp0.le
    have h4 : 0 < y 0 ^ p := Real.rpow_pos_of_pos (hy0 0) _
    have h5 : 2 / p = 1 + (2 - p) / p := by field_simp; ring
    rw [h5]
    nlinarith [mul_nonneg hc h4.le, mul_le_mul_of_nonneg_left h3 hc]

/-- The weighted arithmetic–geometric mean step: for `1 < p < 2`, `Y > 0`, `S ≥ 0` and
`S Y^(p-2) ≤ A`, `S^(p/2) ≤ (p/2) A + (1 - p/2) Y^p`. -/
lemma sq_sum_rpow_le {p S A Y : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hY : 0 < Y) (hS : 0 ≤ S)
    (hSA : S * Y ^ (p - 2) ≤ A) :
    S ^ (p / 2) ≤ p / 2 * A + (1 - p / 2) * Y ^ p := by
  have hθ0 : 0 < p / 2 := by linarith
  have hθ1 : 0 ≤ 1 - p / 2 := by linarith
  have hYw : 0 < Y ^ (p - 2) := Real.rpow_pos_of_pos hY _
  have hA : 0 ≤ A := (mul_nonneg hS hYw.le).trans hSA
  have e1 : S = (S * Y ^ (p - 2)) * Y ^ (2 - p) := by
    rw [mul_assoc, ← Real.rpow_add hY]
    have : p - 2 + (2 - p) = 0 := by ring
    rw [this, Real.rpow_zero, mul_one]
  have e2 : (Y ^ (2 - p)) ^ (p / 2) = (Y ^ p) ^ (1 - p / 2) := by
    rw [← Real.rpow_mul hY.le, ← Real.rpow_mul hY.le]
    congr 1
    ring
  have h1 : S ^ (p / 2) ≤ A ^ (p / 2) * (Y ^ p) ^ (1 - p / 2) := by
    calc S ^ (p / 2) = ((S * Y ^ (p - 2)) * Y ^ (2 - p)) ^ (p / 2) := by rw [← e1]
      _ = (S * Y ^ (p - 2)) ^ (p / 2) * (Y ^ (2 - p)) ^ (p / 2) :=
          Real.mul_rpow (mul_nonneg hS hYw.le) (Real.rpow_nonneg hY.le _)
      _ ≤ A ^ (p / 2) * (Y ^ (2 - p)) ^ (p / 2) := by
          gcongr
      _ = A ^ (p / 2) * (Y ^ p) ^ (1 - p / 2) := by rw [e2]
  have h2 := Real.geom_mean_le_arith_mean2_weighted hθ0.le hθ1 hA
    (Real.rpow_nonneg hY.le p) (by ring)
  exact h1.trans h2

/-! ### The running maximum -/

/-- The running maximum `max_{j ≤ k} |Z_j ω|`. -/
def maxAbs {Ω : Type*} (Z : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one fun j => |Z j ω|

lemma abs_le_maxAbs {Ω : Type*} {Z : ℕ → Ω → ℝ} {j k : ℕ} (h : j ≤ k) (ω : Ω) :
    |Z j ω| ≤ maxAbs Z k ω :=
  Finset.le_sup' (fun j => |Z j ω|) (Finset.mem_range.mpr (by omega))

lemma maxAbs_nonneg {Ω : Type*} (Z : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : 0 ≤ maxAbs Z k ω :=
  (abs_nonneg _).trans (abs_le_maxAbs (Nat.zero_le k) ω)

lemma maxAbs_le_of {Ω : Type*} {Z : ℕ → Ω → ℝ} {k : ℕ} {a : ℝ} (ω : Ω)
    (h : ∀ j, j ≤ k → |Z j ω| ≤ a) : maxAbs Z k ω ≤ a :=
  Finset.sup'_le _ _ fun j hj => h j (by have := Finset.mem_range.mp hj; omega)

lemma maxAbs_mono {Ω : Type*} (Z : ℕ → Ω → ℝ) {k n : ℕ} (h : k ≤ n) (ω : Ω) :
    maxAbs Z k ω ≤ maxAbs Z n ω :=
  maxAbs_le_of ω fun _ hj => abs_le_maxAbs (hj.trans h) ω

lemma maxAbs_le_mul {Ω : Type*} {Z : ℕ → Ω → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hZ0 : ∀ ω, Z 0 ω = 0) (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) (ω : Ω)
    {k : ℕ} (hk : k ≤ N) : maxAbs Z k ω ≤ N * b :=
  maxAbs_le_of ω fun j hj =>
    (abs_le_mul_of_increments hZ0 hinc ω j (hj.trans hk)).trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hj.trans hk)) hb.le)

lemma measurable_maxAbs {Ω : Type*} {m : MeasurableSpace Ω} {Z : ℕ → Ω → ℝ} {k : ℕ}
    (hZ : ∀ j, j ≤ k → Measurable[m] (Z j)) : Measurable[m] (maxAbs Z k) := by
  have h : maxAbs Z k = fun ω => (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one
      fun j => |Z j ω| := rfl
  rw [h]
  exact Finset.measurable_range_sup'' (f := fun j ω => |Z j ω|) fun j hj => (hZ j hj).abs

lemma measurable_sqSum {Ω : Type*} [MeasurableSpace Ω] {Z : ℕ → Ω → ℝ}
    (hZm : ∀ j, Measurable (Z j)) (N : ℕ) :
    Measurable fun ω => ∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2 :=
  Finset.measurable_sum _ fun i _ => ((hZm (i + 1)).sub (hZm i)).pow_const 2

lemma sqSum_le {Ω : Type*} {Z : ℕ → Ω → ℝ} {N : ℕ} {b : ℝ}
    (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) (ω : Ω) :
    ∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2 ≤ N * b ^ 2 := by
  calc ∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2 ≤ ∑ i ∈ Finset.range N, b ^ 2 :=
        Finset.sum_le_sum fun i hi =>
          sq_le_sq' (abs_le.mp (hinc i (Finset.mem_range.mp hi) ω)).1
            (abs_le.mp (hinc i (Finset.mem_range.mp hi) ω)).2
    _ = N * b ^ 2 := by simp

/-! ### The pointwise bound and the orthogonality -/

/-- **Pointwise bound.** For a sequence `Z` from `0` with increments at most `b` on `i < N`, writing
`Y_k = max_{j ≤ k} |Z_j| + b` and `d_k = Z_{k+1} - Z_k`,
`(∑_{k<N} d_k²)^(p/2) ≤ (2 - p/2) Y_N^p - (p/2) ∑_{k<N} 2 (Y_k^(p-2) Z_k) d_k`. -/
lemma pointwise_sq_rpow_le {Ω : Type*} {Z : ℕ → Ω → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hZ0 : ∀ ω, Z 0 ω = 0) (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (ω : Ω) :
    (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ≤
      (2 - p / 2) * (maxAbs Z N ω + b) ^ p - p / 2 * ∑ k ∈ Finset.range N,
        2 * ((maxAbs Z k ω + b) ^ (p - 2) * Z k ω) * (Z (k + 1) ω - Z k ω) := by
  have hp0 : 0 < p := by linarith
  have hy0 : ∀ k, 0 < maxAbs Z k ω + b := fun k => by
    have := maxAbs_nonneg Z k ω
    linarith
  have hmono : ∀ k, maxAbs Z k ω + b ≤ maxAbs Z (k + 1) ω + b := fun k => by
    have := maxAbs_mono Z (Nat.le_succ k) ω
    linarith
  have hz : ∀ k, k < N → |Z (k + 1) ω| ≤ maxAbs Z k ω + b := fun k hk => by
    have h1 := hinc k hk ω
    have h2 := abs_le_maxAbs (Z := Z) (le_refl k) ω
    have h3 : |Z (k + 1) ω| ≤ |Z k ω| + |Z (k + 1) ω - Z k ω| := by
      calc |Z (k + 1) ω| = |Z k ω + (Z (k + 1) ω - Z k ω)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith
  have habel := abel_sum_le hp1 hp2 (z := fun k => Z k ω) (y := fun k => maxAbs Z k ω + b)
    (N := N) hy0 hmono (hZ0 ω) hz
  have hdec : ∑ k ∈ Finset.range N, (maxAbs Z k ω + b) ^ (p - 2) * (Z (k + 1) ω - Z k ω) ^ 2 =
      ∑ k ∈ Finset.range N, (maxAbs Z k ω + b) ^ (p - 2) * (Z (k + 1) ω ^ 2 - Z k ω ^ 2) -
        ∑ k ∈ Finset.range N,
          2 * ((maxAbs Z k ω + b) ^ (p - 2) * Z k ω) * (Z (k + 1) ω - Z k ω) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hlow : (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) *
      (maxAbs Z N ω + b) ^ (p - 2) ≤
      ∑ k ∈ Finset.range N, (maxAbs Z k ω + b) ^ (p - 2) * (Z (k + 1) ω - Z k ω) ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have hkN : k ≤ N := (Finset.mem_range.mp hk).le
    have hw : (maxAbs Z N ω + b) ^ (p - 2) ≤ (maxAbs Z k ω + b) ^ (p - 2) :=
      Real.rpow_le_rpow_of_nonpos (hy0 k)
        (by have := maxAbs_mono Z hkN ω; linarith) (by linarith)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)
  have hS0 : 0 ≤ ∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hamgm := sq_sum_rpow_le hp1 hp2 (hy0 N) hS0 hlow
  have hθ : p / 2 * (2 / p * (maxAbs Z N ω + b) ^ p) = (maxAbs Z N ω + b) ^ p := by
    field_simp
  have hθ' := mul_le_mul_of_nonneg_left habel (by linarith : (0 : ℝ) ≤ p / 2)
  rw [hθ] at hθ'
  rw [hdec] at hamgm
  nlinarith [hamgm, hθ']

/-- The cross terms `2 (Y_k^(p-2) Z_k) (Z_{k+1} - Z_k)` are integrable with total integral `0`. -/
lemma cross_term_integral {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ) (N : ℕ)
    {b : ℝ} (hb : 0 < b) (hM : Martingale Z 𝒢 P) (hZ0 : ∀ ω, Z 0 ω = 0)
    (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) {p : ℝ} (hp2 : p < 2) :
    Integrable (fun ω => ∑ k ∈ Finset.range N,
        2 * ((maxAbs Z k ω + b) ^ (p - 2) * Z k ω) * (Z (k + 1) ω - Z k ω)) P ∧
      ∫ ω, ∑ k ∈ Finset.range N,
        2 * ((maxAbs Z k ω + b) ^ (p - 2) * Z k ω) * (Z (k + 1) ω - Z k ω) ∂P = 0 := by
  have hT : ∀ k, k < N →
      Integrable (fun ω => 2 * ((maxAbs Z k ω + b) ^ (p - 2) * Z k ω) * (Z (k + 1) ω - Z k ω)) P ∧
        ∫ ω, 2 * ((maxAbs Z k ω + b) ^ (p - 2) * Z k ω) * (Z (k + 1) ω - Z k ω) ∂P = 0 := by
    intro k hk
    have hZk : Measurable[𝒢 k] (Z k) := (hM.stronglyMeasurable k).measurable
    have hwF : Measurable[𝒢 k] fun ω => (maxAbs Z k ω + b) ^ (p - 2) :=
      ((measurable_maxAbs fun j hj =>
        ((hM.stronglyMeasurable j).mono (𝒢.mono hj)).measurable).add_const b).pow_const _
    have hgF : StronglyMeasurable[𝒢 k]
        (fun ω => 2 * ((maxAbs Z k ω + b) ^ (p - 2) * Z k ω)) :=
      (measurable_const.mul (hwF.mul hZk)).stronglyMeasurable
    have hgb : ∀ ω, |2 * ((maxAbs Z k ω + b) ^ (p - 2) * Z k ω)| ≤
        2 * (b ^ (p - 2) * (k * b)) := by
      intro ω
      have h1 : (maxAbs Z k ω + b) ^ (p - 2) ≤ b ^ (p - 2) :=
        Real.rpow_le_rpow_of_nonpos hb (by linarith [maxAbs_nonneg Z k ω]) (by linarith)
      have h2 := abs_le_mul_of_increments hZ0 hinc ω k hk.le
      have h3 : 0 < (maxAbs Z k ω + b) ^ (p - 2) :=
        Real.rpow_pos_of_pos (by linarith [maxAbs_nonneg Z k ω]) _
      rw [abs_mul, abs_mul, abs_of_pos h3, abs_two]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul h1 h2 (abs_nonneg _) (Real.rpow_nonneg hb.le _)) (by norm_num)
    exact integral_mul_diff_eq_zero P 𝒢 Z hM k hgF hgb
  refine ⟨integrable_finsetSum _ fun k hk => (hT k (Finset.mem_range.mp hk)).1, ?_⟩
  rw [integral_finsetSum _ fun k hk => (hT k (Finset.mem_range.mp hk)).1]
  exact Finset.sum_eq_zero fun k hk => (hT k (Finset.mem_range.mp hk)).2

/-- **The real-valued core.** For `1 < p < 2`, `E (∑_{k<N} d_k²)^(p/2) ≤ (2 - p/2) E Y_N^p`, where
`Y_N = max_{k ≤ N} |Z_k| + b`. -/
theorem square_rpow_integral_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ) (N : ℕ)
    {b : ℝ} (hb : 0 < b) (hM : Martingale Z 𝒢 P) (hZ0 : ∀ ω, Z 0 ω = 0)
    (hinc : ∀ i, i < N → ∀ ω, |Z (i + 1) ω - Z i ω| ≤ b) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∫ ω, (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ∂P ≤
      (2 - p / 2) * ∫ ω, (maxAbs Z N ω + b) ^ p ∂P := by
  have hθ0 : 0 < p / 2 := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hZm : ∀ j, Measurable (Z j) := fun j =>
    ((hM.stronglyMeasurable j).mono (𝒢.le j)).measurable
  obtain ⟨hcI, hc0⟩ := cross_term_integral P 𝒢 Z N hb hM hZ0 hinc hp2
  have hS0 : ∀ ω, 0 ≤ ∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2 := fun ω =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSI : Integrable
      (fun ω => (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2)) P :=
    integrable_of_abs_le (C := (N * b ^ 2) ^ (p / 2)) ((measurable_sqSum hZm N).pow_const _)
      fun ω => by
        rw [abs_of_nonneg (Real.rpow_nonneg (hS0 ω) _)]
        exact Real.rpow_le_rpow (hS0 ω) (sqSum_le hinc ω) hθ0.le
  have hYm : Measurable fun ω => maxAbs Z N ω + b :=
    (measurable_maxAbs fun j _ => hZm j).add_const b
  have hYI : Integrable (fun ω => (maxAbs Z N ω + b) ^ p) P :=
    integrable_of_abs_le (C := (N * b + b) ^ p) (hYm.pow_const _) fun ω => by
      have h0 : 0 ≤ maxAbs Z N ω + b := by linarith [maxAbs_nonneg Z N ω]
      rw [abs_of_nonneg (Real.rpow_nonneg h0 _)]
      exact Real.rpow_le_rpow h0 (by linarith [maxAbs_le_mul hb hZ0 hinc ω (le_refl N)]) hp0
  calc ∫ ω, (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ∂P
      ≤ ∫ ω, ((2 - p / 2) * (maxAbs Z N ω + b) ^ p - p / 2 * ∑ k ∈ Finset.range N,
          2 * ((maxAbs Z k ω + b) ^ (p - 2) * Z k ω) * (Z (k + 1) ω - Z k ω)) ∂P :=
        integral_mono hSI ((hYI.const_mul _).sub (hcI.const_mul _)) fun ω =>
          pointwise_sq_rpow_le hb hZ0 hinc hp1 hp2 ω
    _ = (2 - p / 2) * ∫ ω, (maxAbs Z N ω + b) ^ p ∂P - p / 2 * ∫ ω, ∑ k ∈ Finset.range N,
          2 * ((maxAbs Z k ω + b) ^ (p - 2) * Z k ω) * (Z (k + 1) ω - Z k ω) ∂P := by
        rw [integral_sub (hYI.const_mul _) (hcI.const_mul _), integral_const_mul,
          integral_const_mul]
    _ = (2 - p / 2) * ∫ ω, (maxAbs Z N ω + b) ^ p ∂P := by rw [hc0]; ring

/-! ### The statement -/

/-- `E (ofReal (f + b))^p ≤ 2^p (E (ofReal f)^p + ofReal (b^p))` for nonnegative `f`, `b > 0`,
`p ≥ 0`, on a probability space. -/
lemma lintegral_ofReal_add_rpow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) {b p : ℝ} (hb : 0 < b)
    (hp : 0 ≤ p) :
    ∫⁻ ω, ENNReal.ofReal (f ω + b) ^ p ∂P ≤
      2 ^ p * (∫⁻ ω, ENNReal.ofReal (f ω) ^ p ∂P + ENNReal.ofReal (b ^ p)) := by
  calc ∫⁻ ω, ENNReal.ofReal (f ω + b) ^ p ∂P
      ≤ ∫⁻ ω, 2 ^ p * (ENNReal.ofReal (f ω) ^ p + ENNReal.ofReal b ^ p) ∂P :=
        lintegral_mono fun ω => by
          rw [ENNReal.ofReal_add (hf ω) hb.le]
          exact add_rpow_le_two_rpow_mul hp _ _
    _ = 2 ^ p * ∫⁻ ω, (ENNReal.ofReal (f ω) ^ p + ENNReal.ofReal b ^ p) ∂P :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp (by norm_num))
    _ = 2 ^ p * (∫⁻ ω, ENNReal.ofReal (f ω) ^ p ∂P + ENNReal.ofReal (b ^ p)) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
          ENNReal.ofReal_rpow_of_nonneg hb.le hp]

/-- **The discrete square function is bounded by the maximal function for `1 < p < 2`, with bounded
increments.** The constant is `(2 - p/2) 2^p`. -/
theorem squareMaximalBoundedAt_lt_two {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    SquareMaximalBoundedAt p := by
  have hp0 : 0 ≤ p := by linarith
  have hθ : 0 < 2 - p / 2 := by linarith
  refine ⟨(2 - p / 2) * 2 ^ p, by positivity, ?_⟩
  intro Ω _ P _ 𝒢 Z N b hb hM hZ0 hinc
  have hZm : ∀ j, Measurable (Z j) := fun j =>
    ((hM.stronglyMeasurable j).mono (𝒢.le j)).measurable
  have hcore := square_rpow_integral_le P 𝒢 Z N hb hM hZ0 hinc hp1 hp2
  have hS0 : ∀ ω, 0 ≤ ∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2 := fun ω =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hlhs : ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ∂P
      = ENNReal.ofReal
        (∫ ω, (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ∂P) :=
    lintegral_ofReal_rpow_eq (P := P) (measurable_sqSum hZm N) hS0 (C := N * b ^ 2)
      (sqSum_le hinc) (q := p / 2) (by linarith)
  have hiSup : ∀ ω, (⨆ k ≤ N, ENNReal.ofReal |Z k ω|) = ENNReal.ofReal (maxAbs Z N ω) :=
    fun ω => by
      unfold maxAbs
      rw [← sup'_range_eq_iSup, ofReal_sup']
  have hY0 : ∀ ω, 0 ≤ maxAbs Z N ω + b := fun ω => by linarith [maxAbs_nonneg Z N ω]
  have hYm : Measurable fun ω => maxAbs Z N ω + b :=
    (measurable_maxAbs fun j _ => hZm j).add_const b
  have hY : ∫⁻ ω, ENNReal.ofReal (maxAbs Z N ω + b) ^ p ∂P =
      ENNReal.ofReal (∫ ω, (maxAbs Z N ω + b) ^ p ∂P) :=
    lintegral_ofReal_rpow_eq (P := P) hYm hY0 (C := N * b + b)
      (fun ω => by linarith [maxAbs_le_mul hb hZ0 hinc ω (le_refl N)]) hp0
  have hsplit := lintegral_ofReal_add_rpow_le (P := P) (f := maxAbs Z N) (maxAbs_nonneg Z N) hb hp0
  have h2p : ENNReal.ofReal ((2 : ℝ) ^ p) = (2 : ℝ≥0∞) ^ p := by
    rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp
  have hR : ∫⁻ ω, (⨆ k ≤ N, ENNReal.ofReal |Z k ω|) ^ p ∂P =
      ∫⁻ ω, ENNReal.ofReal (maxAbs Z N ω) ^ p ∂P :=
    lintegral_congr fun ω => by rw [hiSup]
  rw [hR]
  calc ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ∂P
      = ENNReal.ofReal
        (∫ ω, (∑ i ∈ Finset.range N, (Z (i + 1) ω - Z i ω) ^ 2) ^ (p / 2) ∂P) := hlhs
    _ ≤ ENNReal.ofReal ((2 - p / 2) * ∫ ω, (maxAbs Z N ω + b) ^ p ∂P) :=
        ENNReal.ofReal_le_ofReal hcore
    _ = ENNReal.ofReal (2 - p / 2) * ∫⁻ ω, ENNReal.ofReal (maxAbs Z N ω + b) ^ p ∂P := by
        rw [ENNReal.ofReal_mul hθ.le, hY]
    _ ≤ ENNReal.ofReal (2 - p / 2) *
          (2 ^ p * (∫⁻ ω, ENNReal.ofReal (maxAbs Z N ω) ^ p ∂P + ENNReal.ofReal (b ^ p))) :=
        mul_le_mul_right hsplit _
    _ = ENNReal.ofReal ((2 - p / 2) * 2 ^ p) *
          (∫⁻ ω, ENNReal.ofReal (maxAbs Z N ω) ^ p ∂P + ENNReal.ofReal (b ^ p)) := by
        rw [ENNReal.ofReal_mul hθ.le, h2p, mul_assoc]

end

end LatticeProb.Process.StoppedSkeleton.SquareMaxLow
