/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.TilingWalkRegionEmbedding at commit fdb5cad;
   local import paths and a deprecated conditional proof are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkAbsorption
import LatticeProb.Bonanno.BouRabeeGwynne.TilingNetwork

/-! Enlarging a finite tiling region preserves the actual absorbed walk law
provided every neighbor of each active vertex was already retained. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace BouRabeeGwynne

private lemma pmf_map_injective_apply {X Y : Type*} (p : PMF X) (f : X → Y)
    (hf : Function.Injective f) (x : X) : p.map f (f x) = p x := by
  rw [PMF.map_apply]
  simp only [hf.eq_iff]
  simp

private lemma pmf_map_apply_of_not_range {X Y : Type*} (p : PMF X) (f : X → Y)
    {y : Y} (hy : y ∉ Set.range f) : p.map f y = 0 := by
  rw [PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro x
  split_ifs with h
  · exact (hy ⟨x, h.symm⟩).elim
  · rfl

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d) {R S : Set T.V}

def regionInclusion (hRS : R ⊆ S) : R → S := fun v => ⟨v.val, hRS v.property⟩

lemma regionInclusion_injective (hRS : R ⊆ S) :
    Function.Injective (T.regionInclusion hRS) :=
  fun _ _ h => Subtype.ext (congrArg (fun w : S => w.val) h)

lemma finiteNetwork_totalConductance_inclusion [Fintype R] [Fintype S]
    (hRS : R ⊆ S) (v : R) (hneighbors : T.neighbors v ⊆ R) :
    (T.finiteNetwork R).totalConductance v =
      (T.finiteNetwork S).totalConductance (T.regionInclusion hRS v) := by
  change (∑ w : R, T.conductanceReal v w) = ∑ w : S, T.conductanceReal v w
  rw [Finset.sum_set_coe R, Finset.sum_set_coe S]
  apply Finset.sum_subset
  · intro w hw
    exact Set.mem_toFinset.mpr (hRS (Set.mem_toFinset.mp hw))
  · intro w _ hw
    have hnot : ¬ T.adj v w := fun h => hw (Set.mem_toFinset.mpr (hneighbors h))
    simp [conductanceReal, hnot]

variable [Fintype R] [Fintype S]

theorem finiteNetwork_stepPMF_inclusion (hRS : R ⊆ S) (B : Set T.V)
    (hneighbors : ∀ v : R, (v : T.V) ∈ B → T.neighbors v ⊆ R)
    (hR : ∀ v ∈ (Subtype.val ⁻¹' B : Set R),
      0 < (T.finiteNetwork R).totalConductance v)
    (hS : ∀ v ∈ (Subtype.val ⁻¹' B : Set S),
      0 < (T.finiteNetwork S).totalConductance v) (v : R) :
    ((T.finiteNetwork R).stepPMF (Subtype.val ⁻¹' B) hR v).map (T.regionInclusion hRS) =
      (T.finiteNetwork S).stepPMF (Subtype.val ⁻¹' B) hS (T.regionInclusion hRS v) := by
  by_cases hv : (v : T.V) ∈ B
  · have hvR : v ∈ (Subtype.val ⁻¹' B : Set R) := hv
    have hvS : T.regionInclusion hRS v ∈ (Subtype.val ⁻¹' B : Set S) := hv
    ext w
    by_cases hw : (w : T.V) ∈ R
    · let wR : R := ⟨w.val, hw⟩
      have he : w = T.regionInclusion hRS wR := Subtype.ext rfl
      rw [he, pmf_map_injective_apply _ _ (T.regionInclusion_injective hRS)]
      simp only [FiniteConductanceNetwork.stepPMF_apply,
        FiniteConductanceNetwork.transitionProbability, hvR, hvS, ↓reduceIte]
      rw [T.finiteNetwork_totalConductance_inclusion hRS v (hneighbors v hv)]
      rfl
    · have hn : w ∉ Set.range (T.regionInclusion hRS) := by
        rintro ⟨u, rfl⟩
        exact hw u.property
      rw [pmf_map_apply_of_not_range _ _ hn]
      have hadj : ¬ T.adj v w := fun h => hw (hneighbors v hv h)
      have ha : (T.finiteNetwork S).a (T.regionInclusion hRS v) w = 0 := by
        change T.conductanceReal v w = 0
        simp [conductanceReal, hadj]
      simp only [FiniteConductanceNetwork.stepPMF_apply,
        FiniteConductanceNetwork.transitionProbability, hvS, ↓reduceIte, ha,
        zero_div, ENNReal.ofReal_zero]
  · have hvR : v ∉ (Subtype.val ⁻¹' B : Set R) := hv
    have hvS : T.regionInclusion hRS v ∉ (Subtype.val ⁻¹' B : Set S) := hv
    rw [(T.finiteNetwork R).stepPMF_of_not_mem _ hR hvR,
      (T.finiteNetwork S).stepPMF_of_not_mem _ hS hvS, PMF.pure_map]

variable [MeasurableSpace R] [MeasurableSingletonClass R]
  [MeasurableSpace S] [MeasurableSingletonClass S]

lemma finiteNetwork_stepKernel_inclusion (hRS : R ⊆ S) (B : Set T.V)
    (hneighbors : ∀ v : R, (v : T.V) ∈ B → T.neighbors v ⊆ R)
    (hR : ∀ v ∈ (Subtype.val ⁻¹' B : Set R),
      0 < (T.finiteNetwork R).totalConductance v)
    (hS : ∀ v ∈ (Subtype.val ⁻¹' B : Set S),
      0 < (T.finiteNetwork S).totalConductance v) (v : R) :
    ((T.finiteNetwork R).stepKernel (Subtype.val ⁻¹' B) hR v).map
      (T.regionInclusion hRS) =
      (T.finiteNetwork S).stepKernel (Subtype.val ⁻¹' B) hS (T.regionInclusion hRS v) := by
  change ((T.finiteNetwork R).stepPMF (Subtype.val ⁻¹' B) hR v).toMeasure.map
    (T.regionInclusion hRS) =
      ((T.finiteNetwork S).stepPMF (Subtype.val ⁻¹' B) hS (T.regionInclusion hRS v)).toMeasure
  rw [PMF.toMeasure_map _ _ (measurable_of_finite _),
    T.finiteNetwork_stepPMF_inclusion hRS B hneighbors hR hS v]

/-- The complete absorbed path law is independent of the unused vertices in
the larger finite region; no transition from an active vertex is lost. -/
theorem finiteNetwork_trajectoryLaw_inclusion (hRS : R ⊆ S) (B : Set T.V)
    (hneighbors : ∀ v : R, (v : T.V) ∈ B → T.neighbors v ⊆ R)
    (hR : ∀ v ∈ (Subtype.val ⁻¹' B : Set R),
      0 < (T.finiteNetwork R).totalConductance v)
    (hS : ∀ v ∈ (Subtype.val ⁻¹' B : Set S),
      0 < (T.finiteNetwork S).totalConductance v) (v : R) :
    ((T.finiteNetwork R).trajectoryLaw (Subtype.val ⁻¹' B) hR v).map
      (fun ω n => T.regionInclusion hRS (ω n)) =
      (T.finiteNetwork S).trajectoryLaw (Subtype.val ⁻¹' B) hS (T.regionInclusion hRS v) := by
  apply TrajectoryCoupling.map_trajectory_law (Measure.dirac v)
    ((T.finiteNetwork R).historyKernel (Subtype.val ⁻¹' B) hR)
    (Measure.dirac (T.regionInclusion hRS v))
    ((T.finiteNetwork S).historyKernel (Subtype.val ⁻¹' B) hS)
    (T.regionInclusion hRS) (measurable_of_finite _)
  · exact Measure.map_dirac' (measurable_of_finite _) _
  · intro n h
    exact T.finiteNetwork_stepKernel_inclusion hRS B hneighbors hR hS
      (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)

lemma closedVertices_mono {U W : Set (Euc d)} (hUW : U ⊆ W) :
    T.closedVertices U ⊆ T.closedVertices W := by
  intro v hv
  rcases hv with hv | ⟨hout, u, hu, huv⟩
  · exact Or.inl (hUW hv)
  · exact T.neighbor_mem_closedVertices (hUW hu) huv

end OrthogonalTiling
end BouRabeeGwynne
