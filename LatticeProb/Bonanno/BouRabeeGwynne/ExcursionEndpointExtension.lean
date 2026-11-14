/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ExcursionEndpointExtension at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkExcursionKernel
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-! Extend a genuine finite-vertex excursion kernel to arbitrary spatial
starting points, using constant paths off the embedded vertex set. The
extension agrees exactly with the original kernel at every graph vertex. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace BouRabeeGwynne

variable {d : ℕ} {V : Type*} [Fintype V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

lemma measurableEmbedding_finite_positions (pos : V → Euc d)
    (hpos : Function.Injective pos) : MeasurableEmbedding pos where
  injective := hpos
  measurable := measurable_of_finite _
  measurableSet_image' := fun s _ => ((Set.toFinite s).image pos).measurableSet

/-- Measurable extension retaining the whole supplied excursion state. In
particular the state may include a discrete duration and all visited vertices. -/
noncomputable def finiteVertexKernelExtension {S : Type*} [MeasurableSpace S]
    (pos : V → Euc d) (hpos : Function.Injective pos) (κ : Kernel V S)
    (constantState : Euc d → S) (hconstant : Measurable constantState) : Kernel (Euc d) S where
  toFun := Function.extend pos κ (fun z => Measure.dirac (constantState z))
  measurable' := (measurableEmbedding_finite_positions pos hpos).measurable_extend
    κ.measurable (Measure.measurable_dirac.comp hconstant)

@[simp] lemma finiteVertexKernelExtension_apply_vertex {S : Type*} [MeasurableSpace S]
    (pos : V → Euc d) (hpos : Function.Injective pos) (κ : Kernel V S)
    (constantState : Euc d → S) (hconstant : Measurable constantState) (v : V) :
    finiteVertexKernelExtension pos hpos κ constantState hconstant (pos v) = κ v := by
  change Function.extend pos (fun w => κ w)
    (fun z => Measure.dirac (constantState z)) (pos v) = κ v
  exact hpos.extend_apply (fun w => κ w) (fun z => Measure.dirac (constantState z)) v

lemma finiteVertexKernelExtension_apply_off_graph {S : Type*} [MeasurableSpace S]
    (pos : V → Euc d) (hpos : Function.Injective pos) (κ : Kernel V S)
    (constantState : Euc d → S) (hconstant : Measurable constantState)
    {z : Euc d} (hz : z ∉ Set.range pos) :
    finiteVertexKernelExtension pos hpos κ constantState hconstant z =
      Measure.dirac (constantState z) := by
  change Function.extend pos (fun w => κ w)
    (fun y => Measure.dirac (constantState y)) z = Measure.dirac (constantState z)
  exact Function.extend_apply' (f := pos) (fun w => κ w)
    (fun y => Measure.dirac (constantState y)) z hz

noncomputable instance finiteVertexKernelExtension_isMarkov {S : Type*} [MeasurableSpace S]
    (pos : V → Euc d) (hpos : Function.Injective pos) (κ : Kernel V S)
    [IsMarkovKernel κ] (constantState : Euc d → S) (hconstant : Measurable constantState) :
    IsMarkovKernel (finiteVertexKernelExtension pos hpos κ constantState hconstant) where
  isProbabilityMeasure z := by
    by_cases hz : z ∈ Set.range pos
    · obtain ⟨v, rfl⟩ := hz
      rw [finiteVertexKernelExtension_apply_vertex]
      infer_instance
    · rw [finiteVertexKernelExtension_apply_off_graph pos hpos κ constantState hconstant hz]
      infer_instance

lemma measurable_constantExcursion :
    Measurable (fun z : Euc d => ContinuousMap.const unitInterval z) :=
  ContinuousMap.measurable_iff_eval.mpr (fun _ => measurable_id)

noncomputable def vertexExcursionExtension (pos : V → Euc d)
    (hpos : Function.Injective pos) (κ : Kernel V C(unitInterval, Euc d)) :
    Kernel (Euc d) C(unitInterval, Euc d) :=
  finiteVertexKernelExtension pos hpos κ (ContinuousMap.const unitInterval)
    measurable_constantExcursion

@[simp] lemma vertexExcursionExtension_apply_vertex (pos : V → Euc d)
    (hpos : Function.Injective pos) (κ : Kernel V C(unitInterval, Euc d)) (v : V) :
    vertexExcursionExtension pos hpos κ (pos v) = κ v :=
  finiteVertexKernelExtension_apply_vertex pos hpos κ (ContinuousMap.const unitInterval)
    measurable_constantExcursion v

lemma vertexExcursionExtension_apply_off_graph (pos : V → Euc d)
    (hpos : Function.Injective pos) (κ : Kernel V C(unitInterval, Euc d))
    {z : Euc d} (hz : z ∉ Set.range pos) :
    vertexExcursionExtension pos hpos κ z =
      Measure.dirac (ContinuousMap.const unitInterval z) :=
  finiteVertexKernelExtension_apply_off_graph pos hpos κ (ContinuousMap.const unitInterval)
    measurable_constantExcursion hz

noncomputable instance vertexExcursionExtension_isMarkov (pos : V → Euc d)
    (hpos : Function.Injective pos) (κ : Kernel V C(unitInterval, Euc d))
    [IsMarkovKernel κ] : IsMarkovKernel (vertexExcursionExtension pos hpos κ) where
  isProbabilityMeasure z := by
    by_cases hz : z ∈ Set.range pos
    · obtain ⟨v, rfl⟩ := hz
      rw [vertexExcursionExtension_apply_vertex]
      infer_instance
    · rw [vertexExcursionExtension_apply_off_graph pos hpos κ hz]
      infer_instance

lemma vertexExcursionExtension_ae_start (pos : V → Euc d)
    (hpos : Function.Injective pos) (κ : Kernel V C(unitInterval, Euc d))
    (hstart : ∀ v, ∀ᵐ c ∂κ v, c 0 = pos v) (z : Euc d) :
    ∀ᵐ c ∂vertexExcursionExtension pos hpos κ z, c 0 = z := by
  by_cases hz : z ∈ Set.range pos
  · obtain ⟨v, rfl⟩ := hz
    rw [vertexExcursionExtension_apply_vertex]
    exact hstart v
  · rw [vertexExcursionExtension_apply_off_graph pos hpos κ hz]
    simp

/-- The next excursion starts at the previous curve's exact endpoint,
including for supplied histories that are not genuine graph paths. -/
noncomputable def nextVertexExcursionKernel (pos : V → Euc d)
    (hpos : Function.Injective pos) (κ : Kernel V C(unitInterval, Euc d)) :
    Kernel C(unitInterval, Euc d) C(unitInterval, Euc d) :=
  (vertexExcursionExtension pos hpos κ).comap (fun c => c 1)
    (ContinuousMap.measurable_eval 1)

noncomputable instance nextVertexExcursionKernel_isMarkov (pos : V → Euc d)
    (hpos : Function.Injective pos) (κ : Kernel V C(unitInterval, Euc d))
    [IsMarkovKernel κ] : IsMarkovKernel (nextVertexExcursionKernel pos hpos κ) := by
  unfold nextVertexExcursionKernel
  infer_instance

lemma nextVertexExcursionKernel_ae_start (pos : V → Euc d)
    (hpos : Function.Injective pos) (κ : Kernel V C(unitInterval, Euc d))
    (hstart : ∀ v, ∀ᵐ c ∂κ v, c 0 = pos v) (c : C(unitInterval, Euc d)) :
    ∀ᵐ e ∂nextVertexExcursionKernel pos hpos κ c, e 0 = c 1 :=
  vertexExcursionExtension_ae_start pos hpos κ hstart (c 1)

namespace FiniteConductanceNetwork

lemma extended_walkExcursionKernel_ae_start (N : FiniteConductanceNetwork V)
    (pos : V → Euc d) (hinj : Function.Injective pos) (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (z : Euc d) :
    ∀ᵐ c ∂vertexExcursionExtension pos hinj (N.walkExcursionKernel pos A hpos) z,
      c 0 = z :=
  vertexExcursionExtension_ae_start pos hinj _
    (N.walkExcursionKernel_ae_start pos A hpos) z

end FiniteConductanceNetwork
end BouRabeeGwynne
