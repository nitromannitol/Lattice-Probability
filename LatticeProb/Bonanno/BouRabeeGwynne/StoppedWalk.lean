/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.StoppedWalk at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.DiscretePDEAlgebra
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.HittingTime

/-!
# Finite conductance transitions with absorption

The transition row at an interior vertex is the conductance row divided by its
positive total. Vertices outside the interior set are absorbing, including
isolated exterior vertices. The probability distributions below are constructed
from these weights; their existence is not assumed.
-/

open scoped BigOperators ENNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)

/-- Total conductance out of a vertex. -/
def totalConductance (v : V) : ℝ := ∑ w, N.a v w

lemma totalConductance_nonneg (v : V) : 0 ≤ N.totalConductance v :=
  Finset.sum_nonneg fun w _ ↦ N.nonneg v w

lemma totalConductance_pos_of_edge {v w : V} (h : 0 < N.a v w) :
    0 < N.totalConductance v :=
  h.trans_le (Finset.single_le_sum (fun u _ ↦ N.nonneg v u) (Finset.mem_univ w))

/-- The actual one-step probabilities, with absorption outside `A`. -/
noncomputable def transitionProbability (A : Set V) (v w : V) : ℝ := by
  classical
  exact if v ∈ A then N.a v w / N.totalConductance v else if w = v then 1 else 0

lemma transitionProbability_nonneg (A : Set V) (v w : V) :
    0 ≤ N.transitionProbability A v w := by
  classical
  by_cases hv : v ∈ A
  · simp only [transitionProbability, hv, ite_eq_left]
    exact div_nonneg (N.nonneg v w) (N.totalConductance_nonneg v)
  · by_cases hw : w = v <;> simp [transitionProbability, hv, hw]

lemma sum_transitionProbability (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    ∑ w, N.transitionProbability A v w = 1 := by
  classical
  by_cases hv : v ∈ A
  · simp only [transitionProbability, hv, ite_eq_left]
    rw [← Finset.sum_div]
    exact div_self (hpos v hv).ne'
  · simp [transitionProbability, hv]

/-- The probability mass function of the next vertex. -/
noncomputable def stepPMF (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) : PMF V :=
  PMF.ofFintype (fun w ↦ ENNReal.ofReal (N.transitionProbability A v w)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun w _ ↦ N.transitionProbability_nonneg A v w), N.sum_transitionProbability A hpos v]
    exact ENNReal.ofReal_one)

@[simp] lemma stepPMF_apply (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v w : V) :
    N.stepPMF A hpos v w = ENNReal.ofReal (N.transitionProbability A v w) := rfl

lemma stepPMF_of_not_mem (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) {v : V} (hv : v ∉ A) :
    N.stepPMF A hpos v = PMF.pure v := by
  classical
  ext w
  by_cases hw : w = v <;> simp [stepPMF_apply, transitionProbability, hv, hw]

/-- One-step expected increment, before passing to the trajectory process. -/
noncomputable def stoppedGenerator (A : Set V) (f : V → ℝ) (v : V) : ℝ :=
  ∑ w, N.transitionProbability A v w * (f w - f v)

/-- The discrete-time generator is the normalized, not the unnormalized, Laplacian. -/
lemma stoppedGenerator_eq_laplacian_div (A : Set V) (f : V → ℝ) {v : V} (hv : v ∈ A) :
    N.stoppedGenerator A f v = N.laplacian f v / N.totalConductance v := by
  classical
  simp only [stoppedGenerator, transitionProbability, hv, ite_eq_left, laplacian, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w _
  ring

lemma stoppedGenerator_of_not_mem (A : Set V) (f : V → ℝ) {v : V} (hv : v ∉ A) :
    N.stoppedGenerator A f v = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : w = v <;> simp [transitionProbability, hv, hw]

section PathSemantics

omit [Fintype V]

/-- A path remains at the vertex of its first visit to the complement. -/
def IsAbsorbedPath (A : Set V) (ω : ℕ → V) : Prop :=
  ∀ n, ω n ∉ A → ω (n + 1) = ω n

lemma IsAbsorbedPath.after_exit {A : Set V} {ω : ℕ → V}
    (h : IsAbsorbedPath A ω) {n : ℕ} (hn : ω n ∉ A) (k : ℕ) :
    ω (n + k) = ω n := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      ω (n + (k + 1)) = ω (n + k) := h (n + k) (by simpa only [ih] using hn)
      _ = ω n := ih

/-- First discrete vertex exit, with value infinity on paths that never exit. -/
noncomputable def exitTime (A : Set V) (ω : ℕ → V) : WithTop ℕ :=
  MeasureTheory.hittingAfter (fun n ω ↦ ω n) Aᶜ 0 ω

lemma exitTime_eq_top_iff (A : Set V) (ω : ℕ → V) :
    exitTime A ω = ⊤ ↔ ∀ n, ω n ∈ A := by
  simp [exitTime, MeasureTheory.hittingAfter_eq_top_iff]

lemma exitTime_le_iff (A : Set V) (ω : ℕ → V) (n : ℕ) :
    exitTime A ω ≤ (n : WithTop ℕ) ↔ ∃ k ≤ n, ω k ∉ A := by
  simpa [exitTime, WithTop.coe_natCast] using
    (MeasureTheory.hittingAfter_le_iff (u := fun (n : ℕ) (ω : ℕ → V) ↦ ω n) (s := Aᶜ)
      (n := 0) (i := n) (ω := ω))

lemma exitTime_eq_zero_of_not_mem {A : Set V} {ω : ℕ → V} (h : ω 0 ∉ A) :
    exitTime A ω = 0 :=
  le_antisymm ((exitTime_le_iff A ω 0).mpr ⟨0, le_rfl, h⟩) bot_le

lemma exitTime_mem_compl_of_ne_top {A : Set V} {ω : ℕ → V}
    (h : exitTime A ω ≠ ⊤) : ω (exitTime A ω).untopA ∉ A :=
  MeasureTheory.hittingAfter_mem_set_of_ne_top h

lemma mem_of_lt_exitTime {A : Set V} {ω : ℕ → V} {n : ℕ}
    (h : (n : WithTop ℕ) < exitTime A ω) : ω n ∈ A := by
  by_contra hn
  exact (not_le_of_gt h) ((exitTime_le_iff A ω n).mpr ⟨n, le_rfl, hn⟩)

lemma exitTime_le_iff_of_absorbed {A : Set V} {ω : ℕ → V}
    (h : IsAbsorbedPath A ω) (n : ℕ) :
    exitTime A ω ≤ (n : WithTop ℕ) ↔ ω n ∉ A := by
  rw [exitTime_le_iff]
  constructor
  · rintro ⟨k, hkn, hk⟩
    have heq := h.after_exit hk (n - k)
    rw [Nat.add_sub_of_le hkn] at heq
    simpa only [heq] using hk
  · exact fun hn ↦ ⟨n, le_rfl, hn⟩

end PathSemantics

section Trajectories

open MeasureTheory ProbabilityTheory Preorder

variable [MeasurableSpace V] [MeasurableSingletonClass V]

omit [Fintype V] [MeasurableSingletonClass V] in
lemma coordinateProcess_adapted :
    Adapted (Filtration.piLE (X := fun _ : ℕ ↦ V)) (fun n ω ↦ ω n) := by
  intro n
  exact (measurable_pi_apply (⟨n, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic n)).comp
    (comap_measurable (restrictLe (π := fun _ : ℕ ↦ V) n))

/-- The first vertex exit is a stopping time for the canonical history filtration. -/
lemma exitTime_isStoppingTime (A : Set V) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ V)) (exitTime A) :=
  coordinateProcess_adapted.isStoppingTime_hittingAfter (Set.toFinite Aᶜ).measurableSet

/-- The generator is the expectation under the actual one-step distribution. -/
lemma integral_stepPMF_increment (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (f : V → ℝ) (v : V) :
    ∫ w, (f w - f v) ∂(N.stepPMF A hpos v).toMeasure = N.stoppedGenerator A f v := by
  rw [PMF.integral_eq_sum]
  simp only [stepPMF_apply, ENNReal.toReal_ofReal (N.transitionProbability_nonneg A v _),
    smul_eq_mul, stoppedGenerator]

/-- The transition kernel is constructed from its finite probability rows. -/
noncomputable def stepKernel (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) : Kernel V V where
  toFun v := (N.stepPMF A hpos v).toMeasure
  measurable' := measurable_of_finite _

noncomputable instance stepKernel_isMarkovKernel (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) : IsMarkovKernel (N.stepKernel A hpos) where
  isProbabilityMeasure v := by
    change IsProbabilityMeasure (N.stepPMF A hpos v).toMeasure
    infer_instance

/-- At time `n`, the next step depends on the last vertex of the finite history. -/
noncomputable def historyKernel (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (n : ℕ) :
    Kernel (Finset.Iic n → V) V :=
  (N.stepKernel A hpos).comap (fun h ↦ h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

noncomputable instance historyKernel_isMarkovKernel (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (n : ℕ) :
    IsMarkovKernel (N.historyKernel A hpos n) := by
  unfold historyKernel
  infer_instance

/-- The actual law of the discrete-time walk, from Ionescu--Tulcea. -/
noncomputable def trajectoryLaw (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) : Measure (ℕ → V) :=
  Kernel.trajMeasure (Measure.dirac v) (N.historyKernel A hpos)

noncomputable instance trajectoryLaw_isProbabilityMeasure (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    IsProbabilityMeasure (N.trajectoryLaw A hpos v) := by
  unfold trajectoryLaw
  infer_instance

/-- The initial history consists exactly of the prescribed starting vertex. -/
lemma trajectoryLaw_initialHistory (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    (N.trajectoryLaw A hpos v).map (frestrictLe 0) =
      Measure.dirac (fun _ : Finset.Iic 0 ↦ v) := by
  rw [trajectoryLaw, Kernel.trajMeasure,
    Measure.map_comp _ _ (measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (by fun_prop)]
  rfl

lemma trajectoryLaw_ae_start (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    ∀ᵐ ω ∂N.trajectoryLaw A hpos v, ω 0 = v := by
  have h : ∀ᵐ h ∂(N.trajectoryLaw A hpos v).map (frestrictLe 0),
      h ⟨0, Finset.mem_Iic.mpr le_rfl⟩ = v := by
    rw [N.trajectoryLaw_initialHistory A hpos v]
    simp
  exact ae_of_ae_map (measurable_frestrictLe 0).aemeasurable h

/-- The joint distribution of a history and its next vertex has the stated transition row. -/
lemma trajectoryLaw_history_next (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) (n : ℕ) :
    (N.trajectoryLaw A hpos v).map (frestrictLe n) ⊗ₘ N.historyKernel A hpos n =
      (N.trajectoryLaw A hpos v).map (fun ω ↦ (frestrictLe n ω, ω (n + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

/-- At any fixed time, a walk already outside `A` remains at its current vertex. -/
lemma trajectoryLaw_ae_absorbing_step (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) (n : ℕ) :
    ∀ᵐ ω ∂N.trajectoryLaw A hpos v, ω n ∉ A → ω (n + 1) = ω n := by
  have hpair : ∀ᵐ q ∂(N.trajectoryLaw A hpos v).map
      (fun ω ↦ (frestrictLe n ω, ω (n + 1))),
      q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∉ A →
        q.2 = q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩ := by
    rw [← N.trajectoryLaw_history_next A hpos v n]
    apply Measure.ae_compProd_of_ae_ae (Set.toFinite _).measurableSet
    apply Filter.Eventually.of_forall
    intro h
    by_cases hh : h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ A
    · exact Filter.Eventually.of_forall fun w hw ↦ (hw hh).elim
    · change ∀ᵐ w ∂(N.stepPMF A hpos (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure,
        h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∉ A →
          w = h ⟨n, Finset.mem_Iic.mpr le_rfl⟩
      rw [N.stepPMF_of_not_mem A hpos hh, PMF.toMeasure_pure]
      simp
  exact ae_of_ae_map (by fun_prop) hpair

/-- Absorption holds simultaneously at all discrete times, almost surely. -/
lemma trajectoryLaw_ae_absorbed (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    ∀ᵐ ω ∂N.trajectoryLaw A hpos v, IsAbsorbedPath A ω := by
  exact ae_all_iff.mpr (N.trajectoryLaw_ae_absorbing_step A hpos v)

end Trajectories

end BouRabeeGwynne.FiniteConductanceNetwork
