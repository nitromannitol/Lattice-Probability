/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MeshOnly.MeshOnlyHeatUniformization at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MeshOnly.MeshOnlyHeatGenerator
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedWalk

/-! Uniformization of the finite tile-volume-time process. The actual lazy
one-step PMF has generator `massGenerator / uniformizationRate`; its exterior
states are absorbing. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)

/-- A finite dominating rate. Its size is immaterial to the continuous-time law. -/
noncomputable def uniformizationRate (m : V → ℝ) : ℝ :=
  1 + ∑ v, N.totalConductance v / m v

lemma uniformizationRate_pos (m : V → ℝ) (hm : ∀ v, 0 < m v) :
    0 < N.uniformizationRate m := by
  have h : 0 ≤ ∑ v, N.totalConductance v / m v :=
    Finset.sum_nonneg fun v _ => div_nonneg (N.totalConductance_nonneg v) (hm v).le
  unfold uniformizationRate
  linarith

lemma totalConductance_le_uniformizationRate_mul (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (v : V) : N.totalConductance v ≤ N.uniformizationRate m * m v := by
  have h : N.totalConductance v / m v ≤ ∑ w, N.totalConductance w / m w :=
    Finset.single_le_sum (fun w _ => div_nonneg (N.totalConductance_nonneg w) (hm w).le)
      (Finset.mem_univ v)
  apply (div_le_iff₀ (hm v)).mp
  unfold uniformizationRate
  linarith

/-- Uniformized transition probabilities, with absorption outside `W`. -/
noncomputable def uniformizedTransition (m : V → ℝ) (W : Set V) (v w : V) : ℝ := by
  classical
  exact if v ∈ W then
    N.a v w / (N.uniformizationRate m * m v) +
      if w = v then 1 - N.totalConductance v / (N.uniformizationRate m * m v) else 0
  else if w = v then 1 else 0

lemma uniformizedTransition_nonneg (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (W : Set V) (v w : V) : 0 ≤ N.uniformizedTransition m W v w := by
  classical
  have hden : 0 < N.uniformizationRate m * m v :=
    mul_pos (N.uniformizationRate_pos m hm) (hm v)
  have hrow : N.totalConductance v / (N.uniformizationRate m * m v) ≤ 1 :=
    (div_le_one hden).mpr (N.totalConductance_le_uniformizationRate_mul m hm v)
  by_cases hv : v ∈ W
  · simp only [uniformizedTransition, hv, ↓reduceIte]
    apply add_nonneg (div_nonneg (N.nonneg v w) hden.le)
    split_ifs <;> linarith
  · simp only [uniformizedTransition, hv, ↓reduceIte]
    split_ifs <;> norm_num

lemma sum_uniformizedTransition (m : V → ℝ) (W : Set V) (v : V) :
    ∑ w, N.uniformizedTransition m W v w = 1 := by
  classical
  by_cases hv : v ∈ W
  · simp only [uniformizedTransition, hv, ↓reduceIte]
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
    simp [totalConductance]
  · simp [uniformizedTransition, hv]

/-- The actual lazy step, including the nonnegative holding probability. -/
noncomputable def uniformizedStepPMF (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (W : Set V) (v : V) : PMF V :=
  PMF.ofFintype (fun w => ENNReal.ofReal (N.uniformizedTransition m W v w)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ =>
      N.uniformizedTransition_nonneg m hm W v w), N.sum_uniformizedTransition]
    exact ENNReal.ofReal_one)

@[simp] lemma uniformizedStepPMF_apply (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (W : Set V) (v w : V) :
    N.uniformizedStepPMF m hm W v w = ENNReal.ofReal (N.uniformizedTransition m W v w) := rfl

lemma uniformizedStepPMF_of_not_mem (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (W : Set V) {v : V} (hv : v ∉ W) : N.uniformizedStepPMF m hm W v = PMF.pure v := by
  classical
  ext w
  by_cases hw : w = v <;> simp [uniformizedStepPMF_apply, uniformizedTransition, hv, hw]

lemma uniformizedTransition_generator (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (W : Set V) (f : V → ℝ) {v : V} (hv : v ∈ W) :
    N.uniformizationRate m *
      (∑ w, N.uniformizedTransition m W v w * (f w - f v)) = N.massGenerator m f v := by
  classical
  have hrate : N.uniformizationRate m ≠ 0 := (N.uniformizationRate_pos m hm).ne'
  have hmass : m v ≠ 0 := (hm v).ne'
  have hsum : (∑ w, N.uniformizedTransition m W v w * (f w - f v)) =
      N.laplacian f v / (N.uniformizationRate m * m v) := by
    simp only [uniformizedTransition, hv, ↓reduceIte, add_mul, Finset.sum_add_distrib]
    have hdiag : (∑ w, (if w = v then
        1 - N.totalConductance v / (N.uniformizationRate m * m v) else 0) * (f w - f v)) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      by_cases hw : w = v <;> simp [hw]
    rw [hdiag, add_zero]
    unfold laplacian
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [hsum, massGenerator]
  field_simp [hrate, hmass]

/-- The actual n-step uniformized law, composed from its one-step PMF. -/
noncomputable def uniformizedNStepPMF (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) : ℕ → V → PMF V
  | 0, x => PMF.pure x
  | n+1, x => (N.uniformizedStepPMF m hm S x).bind (uniformizedNStepPMF m hm S n)

lemma uniformizedNStepPMF_of_not_mem (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) {x : V} (hx : x ∉ S) (n : ℕ) :
    N.uniformizedNStepPMF m hm S n x = PMF.pure x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [uniformizedNStepPMF, N.uniformizedStepPMF_of_not_mem m hm S hx, ih]

section Trajectories

variable [MeasurableSpace V] [MeasurableSingletonClass V]

noncomputable def uniformizedStepKernel (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (W : Set V) : Kernel V V where
  toFun v := (N.uniformizedStepPMF m hm W v).toMeasure
  measurable' := measurable_of_finite _

instance uniformizedStepKernel_isMarkov (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (W : Set V) : IsMarkovKernel (N.uniformizedStepKernel m hm W) where
  isProbabilityMeasure _ := inferInstanceAs (IsProbabilityMeasure (PMF.toMeasure _))

noncomputable def uniformizedHistoryKernel (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (W : Set V) (n : ℕ) : Kernel (Finset.Iic n → V) V :=
  (N.uniformizedStepKernel m hm W).comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

instance uniformizedHistoryKernel_isMarkov (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (W : Set V) (n : ℕ) : IsMarkovKernel (N.uniformizedHistoryKernel m hm W n) := by
  unfold uniformizedHistoryKernel
  infer_instance

/-- The actual uniformized discrete trajectory law, to be sampled at an
independent Poisson count for the continuous-time process. -/
noncomputable def uniformizedTrajectoryLaw (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (W : Set V) (v : V) : Measure (ℕ → V) :=
  Kernel.trajMeasure (Measure.dirac v) (N.uniformizedHistoryKernel m hm W)

instance uniformizedTrajectoryLaw_isProbability (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (W : Set V) (v : V) : IsProbabilityMeasure (N.uniformizedTrajectoryLaw m hm W v) := by
  unfold uniformizedTrajectoryLaw
  infer_instance

end Trajectories

end BouRabeeGwynne.FiniteConductanceNetwork
