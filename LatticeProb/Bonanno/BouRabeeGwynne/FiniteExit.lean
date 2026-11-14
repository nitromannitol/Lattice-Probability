/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.FiniteExit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedWalk
import LatticeProb.Bonanno.BouRabeeGwynne.FiniteDirichlet
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Exit from a finite conductance network

Accessibility supplies positive interior conductance. The finite-time laws are
constructed by iterating the actual transition PMFs and identified with the
marginals of the Ionescu--Tulcea trajectory measure.
-/

open scoped BigOperators ENNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)

/-- A path to the complement has a first positive edge at each interior starting vertex. -/
lemma totalConductance_pos_of_boundaryAccessible (A : Set V)
    (haccess : N.BoundaryAccessible A) : ∀ v ∈ A, 0 < N.totalConductance v := by
  intro v hv
  obtain ⟨w, hw, hpath⟩ := haccess v hv
  rcases hpath.cases_head with h | ⟨z, hvz, _⟩
  · exact False.elim (hw (h ▸ hv))
  · exact N.totalConductance_pos_of_edge hvz

/-- The genuine finite-time PMF, obtained by successive actual transition rows. -/
noncomputable def nStepPMF (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) : ℕ → V → PMF V
  | 0, v => PMF.pure v
  | n + 1, v => (nStepPMF A hpos n v).bind (N.stepPMF A hpos)

lemma nStepPMF_succ_left (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (n : ℕ) (v : V) :
    N.nStepPMF A hpos (n + 1) v =
      (N.stepPMF A hpos v).bind (fun w ↦ N.nStepPMF A hpos n w) := by
  induction n generalizing v with
  | zero => simp [nStepPMF]
  | succ n ih =>
    change (N.nStepPMF A hpos (n + 1) v).bind (N.stepPMF A hpos) =
      (N.stepPMF A hpos v).bind (fun w ↦ N.nStepPMF A hpos (n + 1) w)
    rw [ih, PMF.bind_bind]
    rfl

lemma nStepPMF_of_not_mem (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) {v : V} (hv : v ∉ A) (n : ℕ) :
    N.nStepPMF A hpos n v = PMF.pure v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [nStepPMF, ih, PMF.pure_bind, N.stepPMF_of_not_mem A hpos hv]

section Measurable

open MeasureTheory ProbabilityTheory Preorder Filter Set
open scoped Topology

variable [MeasurableSpace V] [MeasurableSingletonClass V]

lemma stepKernel_comp_toMeasure (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (p : PMF V) :
    N.stepKernel A hpos ∘ₘ p.toMeasure = (p.bind (N.stepPMF A hpos)).toMeasure := by
  rw [Measure.comp_eq_sum_of_countable]
  ext s hs
  rw [Measure.sum_apply _ hs, PMF.toMeasure_bind_apply _ _ _ hs]
  apply tsum_congr
  intro w
  rw [PMF.toMeasure_apply_singleton p w (measurableSet_singleton w)]
  rfl

lemma trajectoryLaw_marginal_zero (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    (N.trajectoryLaw A hpos v).map (fun ω ↦ ω 0) = Measure.dirac v := by
  calc
    (N.trajectoryLaw A hpos v).map (fun ω ↦ ω 0) =
        (N.trajectoryLaw A hpos v).map (fun _ ↦ v) :=
      Measure.map_congr (N.trajectoryLaw_ae_start A hpos v)
    _ = Measure.dirac v := by simp

lemma trajectoryLaw_marginal_succ (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) (n : ℕ) :
    (N.trajectoryLaw A hpos v).map (fun ω ↦ ω (n + 1)) =
      N.stepKernel A hpos ∘ₘ (N.trajectoryLaw A hpos v).map (fun ω ↦ ω n) := by
  symm
  calc
    N.stepKernel A hpos ∘ₘ (N.trajectoryLaw A hpos v).map (fun ω ↦ ω n) =
        N.stepKernel A hpos ∘ₘ
          ((N.trajectoryLaw A hpos v).map (frestrictLe n)).map
            (fun h ↦ h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
      rw [Measure.map_map
        (f := frestrictLe (π := fun _ : ℕ ↦ V) n)
        (g := fun h : Finset.Iic n → V ↦ h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
        (by fun_prop) (by fun_prop)]
      rfl
    _ = N.historyKernel A hpos n ∘ₘ
        (N.trajectoryLaw A hpos v).map (frestrictLe n) := by
      rw [← Measure.deterministic_comp_eq_map (measurable_pi_apply _),
        Measure.comp_assoc, Kernel.comp_deterministic_eq_comap]
      rfl
    _ = (((N.trajectoryLaw A hpos v).map (frestrictLe n)) ⊗ₘ
        N.historyKernel A hpos n).snd := (Measure.snd_compProd _ _).symm
    _ = (N.trajectoryLaw A hpos v).map (fun ω ↦ ω (n + 1)) := by
      rw [N.trajectoryLaw_history_next A hpos v n, Measure.snd,
        Measure.map_map measurable_snd (by fun_prop)]
      rfl

/-- The finite PMFs above are precisely the actual trajectory marginals. -/
lemma trajectoryLaw_marginal (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) (n : ℕ) :
    (N.trajectoryLaw A hpos v).map (fun ω ↦ ω n) =
      (N.nStepPMF A hpos n v).toMeasure := by
  induction n with
  | zero => rw [N.trajectoryLaw_marginal_zero A hpos v, nStepPMF, PMF.toMeasure_pure]
  | succ n ih =>
    rw [N.trajectoryLaw_marginal_succ A hpos v n, ih, N.stepKernel_comp_toMeasure A hpos]
    rfl

/-- The actual finite-time probability of being in the interior, as a real number. -/
noncomputable def survivalProbability (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (n : ℕ) (v : V) : ℝ :=
  (N.nStepPMF A hpos n v).toMeasure.real A

omit [MeasurableSingletonClass V] in
lemma survivalProbability_nonneg (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (n : ℕ) (v : V) :
    0 ≤ N.survivalProbability A hpos n v := ENNReal.toReal_nonneg

omit [MeasurableSingletonClass V] in
lemma survivalProbability_le_one (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (n : ℕ) (v : V) :
    N.survivalProbability A hpos n v ≤ 1 := measureReal_le_one

lemma survivalProbability_zero_of_mem (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) {v : V} (hv : v ∈ A) :
    N.survivalProbability A hpos 0 v = 1 := by
  classical
  change ((PMF.pure v).toMeasure A).toReal = 1
  rw [PMF.toMeasure_pure, Measure.dirac_apply' v (Set.toFinite A).measurableSet]
  simp [hv]

lemma survivalProbability_of_not_mem (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) {v : V} (hv : v ∉ A) (n : ℕ) :
    N.survivalProbability A hpos n v = 0 := by
  rw [survivalProbability, N.nStepPMF_of_not_mem A hpos hv n, measureReal_def,
    PMF.toMeasure_pure, Measure.dirac_apply' v (Set.toFinite A).measurableSet]
  simp [hv]

/-- Conditioning on the first step gives the finite conductance averaging equation. -/
lemma survivalProbability_succ (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (n : ℕ) (v : V) :
    N.survivalProbability A hpos (n + 1) v =
      ∑ w, N.transitionProbability A v w * N.survivalProbability A hpos n w := by
  simp only [survivalProbability, measureReal_def]
  rw [N.nStepPMF_succ_left A hpos n v,
    PMF.toMeasure_bind_apply _ _ _ (Set.toFinite A).measurableSet, tsum_fintype]
  rw [ENNReal.toReal_sum (fun w _ ↦ ENNReal.mul_ne_top
    ((N.stepPMF A hpos v).apply_ne_top w) (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul, stepPMF_apply,
    ENNReal.toReal_ofReal (N.transitionProbability_nonneg A v _)]

lemma survivalProbability_succ_le (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (n : ℕ) :
    ∀ v, N.survivalProbability A hpos (n + 1) v ≤
      N.survivalProbability A hpos n v := by
  classical
  induction n with
  | zero =>
    intro v
    by_cases hv : v ∈ A
    · simpa only [N.survivalProbability_zero_of_mem A hpos hv] using
        N.survivalProbability_le_one A hpos 1 v
    · rw [N.survivalProbability_of_not_mem A hpos hv,
        N.survivalProbability_of_not_mem A hpos hv]
  | succ n ih =>
    intro v
    rw [N.survivalProbability_succ A hpos (n + 1) v,
      N.survivalProbability_succ A hpos n v]
    exact Finset.sum_le_sum fun w _ ↦
      mul_le_mul_of_nonneg_left (ih w) (N.transitionProbability_nonneg A v w)

lemma survivalProbability_antitone (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    Antitone (fun n ↦ N.survivalProbability A hpos n v) :=
  antitone_nat_of_succ_le (fun n ↦ N.survivalProbability_succ_le A hpos n v)

/-- The decreasing survival limit; its vanishing will follow from the maximum principle. -/
noncomputable def survivalLimit (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) : ℝ :=
  ⨅ n : ℕ, N.survivalProbability A hpos n v

lemma survivalProbability_tendsto (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    Tendsto (fun n ↦ N.survivalProbability A hpos n v) atTop
      (𝓝 (N.survivalLimit A hpos v)) := by
  apply tendsto_atTop_ciInf (N.survivalProbability_antitone A hpos v)
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact N.survivalProbability_nonneg A hpos n v

omit [MeasurableSingletonClass V] in
lemma survivalLimit_nonneg (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    0 ≤ N.survivalLimit A hpos v :=
  le_ciInf (fun n ↦ N.survivalProbability_nonneg A hpos n v)

lemma survivalLimit_of_not_mem (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) {v : V} (hv : v ∉ A) :
    N.survivalLimit A hpos v = 0 := by
  simp [survivalLimit, N.survivalProbability_of_not_mem A hpos hv]

/-- Finite summation commutes with the limit, so the limit satisfies the averaging equation. -/
lemma survivalLimit_averaging (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    (∑ w, N.transitionProbability A v w * N.survivalLimit A hpos w) =
      N.survivalLimit A hpos v := by
  have hsum : Tendsto
      (fun n ↦ ∑ w, N.transitionProbability A v w * N.survivalProbability A hpos n w)
      atTop (𝓝 (∑ w, N.transitionProbability A v w * N.survivalLimit A hpos w)) :=
    tendsto_finsetSum Finset.univ (fun w _ ↦
      tendsto_const_nhds.mul (N.survivalProbability_tendsto A hpos w))
  have hsum' : Tendsto (fun n ↦ N.survivalProbability A hpos (n + 1) v) atTop
      (𝓝 (∑ w, N.transitionProbability A v w * N.survivalLimit A hpos w)) := by
    simpa only [N.survivalProbability_succ A hpos] using hsum
  exact tendsto_nhds_unique hsum'
    ((N.survivalProbability_tendsto A hpos v).comp (tendsto_add_atTop_nat 1))

lemma survivalLimit_laplacian_eq_zero (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) {v : V} (hv : v ∈ A) :
    N.laplacian (N.survivalLimit A hpos) v = 0 := by
  have hconst : (∑ w, N.transitionProbability A v w * N.survivalLimit A hpos v) =
      N.survivalLimit A hpos v := by
    rw [← Finset.sum_mul, N.sum_transitionProbability A hpos v, one_mul]
  have hgen : N.stoppedGenerator A (N.survivalLimit A hpos) v = 0 := by
    simp only [stoppedGenerator, mul_sub, Finset.sum_sub_distrib]
    rw [N.survivalLimit_averaging A hpos v, hconst, sub_self]
  rw [N.stoppedGenerator_eq_laplacian_div A (N.survivalLimit A hpos) hv] at hgen
  exact (div_eq_zero_iff.mp hgen).resolve_right (hpos v hv).ne'

/-- The finite maximum principle rules out positive survival forever. -/
lemma survivalLimit_eq_zero (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A) (v : V) :
    N.survivalLimit A hpos v = 0 := by
  have hmax := N.maximum_principle A haccess (N.survivalLimit A hpos) 0
    (fun w hw ↦ (N.survivalLimit_laplacian_eq_zero A hpos hw).ge)
    (fun w hw ↦ (N.survivalLimit_of_not_mem A hpos hw).le)
  exact le_antisymm (hmax v) (N.survivalLimit_nonneg A hpos v)

lemma survivalProbability_tendsto_zero (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A) (v : V) :
    Tendsto (fun n ↦ N.survivalProbability A hpos n v) atTop (𝓝 0) := by
  simpa only [N.survivalLimit_eq_zero A hpos haccess v] using
    N.survivalProbability_tendsto A hpos v

/-- For the actual trajectory measure, structural boundary accessibility implies
that the first discrete exit is almost surely finite. -/
theorem trajectoryLaw_ae_finiteExit (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A) (v : V) :
    ∀ᵐ ω ∂N.trajectoryLaw A hpos v, exitTime A ω ≠ ⊤ := by
  let μ := N.trajectoryLaw A hpos v
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (N.survivalProbability A hpos n v))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp
        (N.survivalProbability_tendsto_zero A hpos haccess v)
  have hbound (n : ℕ) : μ {ω | exitTime A ω = ⊤} ≤
      ENNReal.ofReal (N.survivalProbability A hpos n v) := by
    calc
      μ {ω | exitTime A ω = ⊤} ≤ μ {ω | ω n ∈ A} :=
        measure_mono fun ω hω ↦ (exitTime_eq_top_iff A ω).mp hω n
      _ = (N.nStepPMF A hpos n v).toMeasure A := by
        rw [← N.trajectoryLaw_marginal A hpos v n,
          Measure.map_apply (f := fun ω : ℕ → V ↦ ω n) (by fun_prop)
            (Set.toFinite A).measurableSet]
        rfl
      _ = ENNReal.ofReal (N.survivalProbability A hpos n v) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hzero : μ {ω | exitTime A ω = ⊤} = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) bot_le
  simpa only [ae_iff, not_not] using hzero

/-- The normalized walk can be defined and shown to exit using accessibility alone. -/
theorem trajectoryLaw_ae_finiteExit_of_boundaryAccessible (A : Set V)
    (haccess : N.BoundaryAccessible A) (v : V) :
    ∀ᵐ ω ∂N.trajectoryLaw A (N.totalConductance_pos_of_boundaryAccessible A haccess) v,
      exitTime A ω ≠ ⊤ :=
  N.trajectoryLaw_ae_finiteExit A _ haccess v

end Measurable

end BouRabeeGwynne.FiniteConductanceNetwork
