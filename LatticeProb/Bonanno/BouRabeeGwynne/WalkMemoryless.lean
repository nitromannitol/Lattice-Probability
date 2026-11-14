/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkMemoryless at commit fdb5cad; local imports and linter compatibility are updated. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkRestart

/-! Whole-path continuation of the actual finite conductance walk. The proof
identifies every finite suffix law, then uses cylinder uniqueness; it does not
replace a joint Markov law by a collection of one-time marginals. -/

open MeasureTheory ProbabilityTheory Set Preorder

namespace BouRabeeGwynne
namespace TrajectoryCoupling

variable {X : Type*} [MeasurableSpace X]
  (κ : (n : ℕ) → Kernel (Finset.Iic n → X) X) [∀ n, IsMarkovKernel (κ n)]

lemma prefix_at_start_traj (a : ℕ) (h : Finset.Iic a → X) :
    (Kernel.traj (X := fun _ => X) κ a h).map (frestrictLe a) = Measure.dirac h := by
  have hp := congrArg (fun k : Kernel (Finset.Iic a → X) (Finset.Iic a → X) => k h)
    (Kernel.traj_map_frestrictLe (X := fun _ => X) (κ := κ) a a)
  simpa only [Kernel.map_apply _ (measurable_frestrictLe a),
    Kernel.partialTraj_self, Kernel.id_apply] using hp

lemma prefix_succ_traj (a b : ℕ) (hab : a ≤ b) (h : Finset.Iic a → X) :
    (Kernel.traj (X := fun _ => X) κ a h).map (frestrictLe (b + 1)) =
      ((Kernel.traj (X := fun _ => X) κ a h).map (frestrictLe b) ⊗ₘ κ b).map
        (append b) := by
  have hp := congrArg (fun k : Kernel (Finset.Iic a → X) (Finset.Iic b → X) => k h)
    (Kernel.traj_map_frestrictLe (X := fun _ => X) (κ := κ) a b)
  simp only [Kernel.map_apply _ (measurable_frestrictLe b)] at hp
  have hs := Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ => X) (κ := κ) (x₀ := h) hab
  rw [← hp] at hs
  rw [hs, Measure.map_map (measurable_append b) (by fun_prop)]
  congr 1
  funext ω
  exact (append_restrict b ω).symm

/-- The suffix of a finite history, retaining its initial position. -/
def shiftPrefix (a k : ℕ) (h : Finset.Iic (a + k) → X) : Finset.Iic k → X :=
  fun i => h ⟨a + i.val, Finset.mem_Iic.mpr
    (Nat.add_le_add_left (Finset.mem_Iic.mp i.property) a)⟩

lemma measurable_shiftPrefix (a k : ℕ) : Measurable (shiftPrefix (X := X) a k) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

omit [MeasurableSpace X] in
lemma shiftPrefix_zero (a : ℕ) (h : Finset.Iic a → X) :
    shiftPrefix a 0 h = fun _ => h ⟨a, Finset.mem_Iic.mpr le_rfl⟩ := by
  funext i
  have hi : i.val = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property)
  simp [shiftPrefix, hi]

omit [MeasurableSpace X] in
lemma shiftPrefix_append (a k : ℕ) :
    shiftPrefix (X := X) a (k + 1) ∘ append (a + k) =
      append k ∘ Prod.map (shiftPrefix a k) id := by
  funext p i
  by_cases hi : i.val ≤ k
  · have hai : a + i.val ≤ a + k := Nat.add_le_add_left hi a
    simp [shiftPrefix, append, hi, hai]
  · have hai : ¬ a + i.val ≤ a + k := by omega
    simp [shiftPrefix, append, hi, hai]

end TrajectoryCoupling

namespace FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  (N : FiniteConductanceNetwork V)

open TrajectoryCoupling

/-- Each finite future prefix under the actual continuation kernel has the
law of a fresh walk started from the last vertex of the supplied history. -/
lemma continuation_shiftPrefix_law (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (a : ℕ) (h : Finset.Iic a → V)
    (k : ℕ) :
    ((Kernel.traj (X := fun _ => V) (N.historyKernel A hpos) a h).map
      (frestrictLe (a + k))).map (shiftPrefix a k) =
      (N.trajectoryLaw A hpos (h ⟨a, Finset.mem_Iic.mpr le_rfl⟩)).map (frestrictLe k) := by
  induction k with
  | zero =>
    change ((Kernel.traj (X := fun _ => V) (N.historyKernel A hpos) a h).map
      (frestrictLe a)).map (shiftPrefix a 0) = _
    rw [prefix_at_start_traj (N.historyKernel A hpos) a h,
      Measure.map_dirac' (measurable_shiftPrefix a 0),
      N.trajectoryLaw_initialHistory, shiftPrefix_zero]
  | succ k ih =>
    change ((Kernel.traj (X := fun _ => V) (N.historyKernel A hpos) a h).map
      (frestrictLe (a + k + 1))).map (shiftPrefix a (k + 1)) = _
    have htarget := prefix_succ
      (Measure.dirac (h ⟨a, Finset.mem_Iic.mpr le_rfl⟩)) (N.historyKernel A hpos) k
    change (N.trajectoryLaw A hpos (h ⟨a, Finset.mem_Iic.mpr le_rfl⟩)).map
      (frestrictLe (k + 1)) = _ at htarget
    have hmap (p : Finset.Iic (a + k) → V) :
        (N.historyKernel A hpos (a + k) p).map id =
          N.historyKernel A hpos k (shiftPrefix a k p) := by
      rw [Measure.map_id]
      rfl
    rw [prefix_succ_traj (N.historyKernel A hpos) a (a + k)
      (Nat.le_add_right _ _) h, htarget,
      Measure.map_map (measurable_shiftPrefix a (k + 1)) (measurable_append (a + k)),
      shiftPrefix_append,
      ← Measure.map_map (measurable_append k) ((measurable_shiftPrefix a k).prodMap measurable_id),
      compProd_map_prod_of_kernel_map _ _ _ _ _ (measurable_shiftPrefix a k) measurable_id hmap,
      ih]
    rfl

/-- Exact whole-path restart at a deterministic time under the genuine
continuation kernel. This is the input to the stopping-time decomposition. -/
theorem continuation_walkShift_law (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (a : ℕ) (h : Finset.Iic a → V) :
    (Kernel.traj (X := fun _ => V) (N.historyKernel A hpos) a h).map (walkShift a) =
      N.trajectoryLaw A hpos (h ⟨a, Finset.mem_Iic.mpr le_rfl⟩) := by
  apply measure_eq_of_prefix_eq
  intro k
  rw [Measure.map_map (measurable_frestrictLe k) (measurable_walkShift a)]
  have heq : frestrictLe (π := fun _ : ℕ => V) k ∘ walkShift a =
      shiftPrefix a k ∘ frestrictLe (π := fun _ : ℕ => V) (a + k) := rfl
  rw [heq, ← Measure.map_map (measurable_shiftPrefix a k) (measurable_frestrictLe (a + k))]
  exact N.continuation_shiftPrefix_law A hpos a h k

end FiniteConductanceNetwork
end BouRabeeGwynne
