/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkAbsorption at commit fdb5cad;
   local imports and linter settings are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkPathStopping
import LatticeProb.Bonanno.BouRabeeGwynne.ClockedWalkExcursion
import LatticeProb.Bonanno.BouRabeeGwynne.DependentKernelMap

/-! Stopping the ambient conductance walk in a smaller vertex set gives the
actual absorbed trajectory law in that set. This is a whole-path identity,
proved by the compatible finite-history pushforwards. -/

open MeasureTheory ProbabilityTheory Set Preorder
open scoped Classical

namespace BouRabeeGwynne


namespace FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

open TrajectoryCoupling

lemma exitTime_stoppedWalkPath (B : Set V) (ω : ℕ → V) :
    exitTime B (stoppedWalkPath B ω) = exitTime B ω := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro n
  constructor
  · intro hn
    obtain ⟨k, hkn, hk⟩ := (exitTime_le_iff B (stoppedWalkPath B ω) n).mp hn
    by_contra hτ
    have hlt : (k : WithTop ℕ) < exitTime B ω :=
      (WithTop.coe_le_coe.mpr hkn).trans_lt (lt_of_not_ge hτ)
    rw [stoppedWalkPath_eq_of_le_exitTime B ω k hlt.le] at hk
    exact hk (mem_of_lt_exitTime hlt)
  · intro hn
    have hfin : exitTime B ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hn
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
    have hkn : k ≤ n := WithTop.coe_le_coe.mp (by simpa only [hk] using hn)
    have hbad : ω k ∉ B := by
      simpa only [exitVertex, ← hk, WithTop.untopD_coe] using exitVertex_not_mem hfin
    apply (exitTime_le_iff B (stoppedWalkPath B ω) n).mpr
    refine ⟨k, hkn, ?_⟩
    rw [stoppedWalkPath_eq_of_le_exitTime B ω k hk.le]
    exact hbad

lemma clockedExcursion_stoppedWalkPath {d : ℕ} (pos : V → Euc d)
    (B : Set V) (ω : ℕ → V) :
    ClockedWalkExcursion.ofWalk pos B (stoppedWalkPath B ω) =
      ClockedWalkExcursion.ofWalk pos B ω := by
  unfold ClockedWalkExcursion.ofWalk
  rw [exitTime_stoppedWalkPath]
  dsimp only
  apply Prod.ext
  · rfl
  · funext k
    exact congrArg pos (stoppedWalkPath_eq_of_le_exitTime B ω
      (min k ((exitTime B ω).untopD 0))
      ((WithTop.coe_le_coe.mpr (min_le_right _ _)).trans
        (WithTop.coe_untopD_le _ _)))

set_option linter.unusedSectionVars false in
lemma stopHistory_zero (B : Set V) (v : V) :
    stopHistory B 0 (fun _ => v) = fun _ => v := by
  funext i
  have hi : i.val = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property)
  simp [stopHistory, frestrictLe_apply, hi, stoppedWalkPath_zero, paddedHistory]

lemma stopHistory_last_mem_imp_eq (B : Set V) (n : ℕ) (h : Finset.Iic n → V)
    (hm : stopHistory B n h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ B) :
    stopHistory B n h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ =
      h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ := by
  have he := stoppedWalkPath_mem_imp_eq B (paddedHistory n h).2 n hm
  simpa only [stopHistory, frestrictLe_apply, paddedHistory, min_self] using he

lemma stopHistory_append (B : Set V) (n : ℕ) :
    stopHistory B (n + 1) ∘ append n = append n ∘
      (fun p : (Finset.Iic n → V) × V =>
        (stopHistory B n p.1, if stopHistory B n p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ B
          then p.2 else stopHistory B n p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) := by
  funext p
  let ω := (paddedHistory (n + 1) (append n p)).2
  have hn1 : frestrictLe (n + 1) ω = append n p := by
    funext i
    change append n p ⟨min i.val (n + 1), _⟩ = append n p i
    congr 1
    exact Subtype.ext (min_eq_left (Finset.mem_Iic.mp i.property))
  have hn : frestrictLe n ω = p.1 := by
    funext i
    have hi := Finset.mem_Iic.mp i.property
    change append n p ⟨min i.val (n + 1), _⟩ = p.1 i
    simp only [min_eq_left (hi.trans (Nat.le_succ n)), append, hi, ↓reduceDIte]
  have hx : ω (n + 1) = p.2 := by
    simp [ω, paddedHistory, append]
  change stopHistory B (n + 1) (append n p) = _
  rw [← hn1, stopHistory_prefix, ← append_restrict n (stoppedWalkPath B ω),
    stoppedWalkPath_succ, hx]
  change append n (frestrictLe n (stoppedWalkPath B ω),
    if frestrictLe n (stoppedWalkPath B ω) ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ B then p.2
    else frestrictLe n (stoppedWalkPath B ω) ⟨n, Finset.mem_Iic.mpr le_rfl⟩) = _
  rw [← stopHistory_prefix, hn]
  rfl

variable (N : FiniteConductanceNetwork V)

set_option linter.unusedSectionVars false in
lemma stepPMF_eq_of_mem_both {A B : Set V}
    (hA : ∀ v ∈ A, 0 < N.totalConductance v)
    (hB : ∀ v ∈ B, 0 < N.totalConductance v) {v : V} (hvA : v ∈ A) (hvB : v ∈ B) :
    N.stepPMF A hA v = N.stepPMF B hB v := by
  ext w
  simp only [stepPMF_apply, transitionProbability, hvA, hvB, ↓reduceIte]

lemma historyKernel_map_stopStep {A B : Set V} (hBA : B ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v)
    (hB : ∀ v ∈ B, 0 < N.totalConductance v) (n : ℕ) (h : Finset.Iic n → V) :
    (N.historyKernel A hA n h).map
      (fun x => if stopHistory B n h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ B then x
        else stopHistory B n h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) =
      N.historyKernel B hB n (stopHistory B n h) := by
  by_cases hm : stopHistory B n h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ B
  · simp only [hm, ↓reduceIte]
    change (N.historyKernel A hA n h).map id = _
    rw [Measure.map_id]
    have he := stopHistory_last_mem_imp_eq B n h hm
    change (N.stepPMF A hA (h ⟨n, _⟩)).toMeasure =
      (N.stepPMF B hB (stopHistory B n h ⟨n, _⟩)).toMeasure
    rw [he]
    exact congrArg PMF.toMeasure (N.stepPMF_eq_of_mem_both hA hB
      (hBA (he ▸ hm)) (he ▸ hm))
  · simp only [hm, ↓reduceIte]
    change (N.historyKernel A hA n h).map (fun _ => stopHistory B n h ⟨n, _⟩) =
      (N.stepPMF B hB (stopHistory B n h ⟨n, _⟩)).toMeasure
    rw [N.stepPMF_of_not_mem B hB hm, PMF.toMeasure_pure, Measure.map_const]
    simp

lemma trajectoryLaw_map_stopHistory {A B : Set V} (hBA : B ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v)
    (hB : ∀ v ∈ B, 0 < N.totalConductance v) (v : V) (n : ℕ) :
    ((N.trajectoryLaw A hA v).map (frestrictLe n)).map (stopHistory B n) =
      (N.trajectoryLaw B hB v).map (frestrictLe n) := by
  induction n with
  | zero =>
    rw [N.trajectoryLaw_initialHistory, N.trajectoryLaw_initialHistory,
      Measure.map_dirac' (measurable_stopHistory B 0), stopHistory_zero]
  | succ n ih =>
    unfold trajectoryLaw at ih
    have hpA := prefix_succ (Measure.dirac v) (N.historyKernel A hA) n
    have hpB := prefix_succ (Measure.dirac v) (N.historyKernel B hB) n
    change (N.trajectoryLaw A hA v).map (frestrictLe (n + 1)) = _ at hpA
    change (N.trajectoryLaw B hB v).map (frestrictLe (n + 1)) = _ at hpB
    rw [hpA, hpB, Measure.map_map (measurable_stopHistory B (n + 1)) (measurable_append n),
      stopHistory_append, ← Measure.map_map (measurable_append n) (measurable_of_finite _),
      compProd_map_dependent_of_kernel_map _ _ _ _ _ (measurable_stopHistory B n)
        (measurable_of_finite _) (N.historyKernel_map_stopStep hBA hA hB n), ih]

/-- Actual absorption locality, including paths whose first exit is infinite. -/
theorem trajectoryLaw_map_stoppedWalkPath {A B : Set V} (hBA : B ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v)
    (hB : ∀ v ∈ B, 0 < N.totalConductance v) (v : V) :
    (N.trajectoryLaw A hA v).map (stoppedWalkPath B) = N.trajectoryLaw B hB v := by
  apply measure_eq_of_prefix_eq
  intro n
  rw [Measure.map_map (measurable_frestrictLe n) (measurable_stoppedWalkPath B)]
  have he : frestrictLe (π := fun _ : ℕ => V) n ∘ stoppedWalkPath B =
      stopHistory B n ∘ frestrictLe (π := fun _ : ℕ => V) n := by
    funext ω
    exact (stopHistory_prefix B n ω).symm
  rw [he, ← Measure.map_map (measurable_stopHistory B n) (measurable_frestrictLe n)]
  exact N.trajectoryLaw_map_stopHistory hBA hA hB v n

/-- The richer ball excursion sampled from the original ambient trajectory
has exactly the constructed ball excursion kernel, including its integer clock. -/
theorem trajectoryLaw_map_clockedExcursion {d : ℕ} (pos : V → Euc d)
    {A B : Set V} (hBA : B ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v)
    (hB : ∀ v ∈ B, 0 < N.totalConductance v) (v : V) :
    (N.trajectoryLaw A hA v).map (ClockedWalkExcursion.ofWalk pos B) =
      N.clockedWalkExcursionKernel pos B hB v := by
  change _ = (N.trajectoryLaw B hB v).map (ClockedWalkExcursion.ofWalk pos B)
  rw [← N.trajectoryLaw_map_stoppedWalkPath hBA hA hB v,
    Measure.map_map (ClockedWalkExcursion.measurable_ofWalk pos B)
      (measurable_stoppedWalkPath B)]
  congr 1
  funext ω
  exact (clockedExcursion_stoppedWalkPath pos B ω).symm

end FiniteConductanceNetwork
end BouRabeeGwynne
