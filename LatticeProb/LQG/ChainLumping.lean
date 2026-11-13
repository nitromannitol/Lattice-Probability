import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.Chain
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkKernelIsMarkov
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath

/-!
# Lumping of Markov chains, and the vertex path of the edge-end walk

Dynkin's lumpability criterion for the trajectory law of a time-homogeneous Markov chain: if a measurable map
`π : S → V` satisfies `(K s).map π = κ (π s)` for the transition kernel `K` of the chain on `S` and a Markov
kernel `κ` on `V`, then the image `(π (X_n))_n` of the chain with kernel `K` started at `z` is the chain with
kernel `κ` started at `π z`, as a law on the whole sequence space.

Main results:
* `chainLaw_map_of_factor`: `(chainLaw K z).map (fun ω n => π (ω n)) = chainLaw κ (π z)`.
* `walkLaw_map_vertexPath`: the vertex path of the edge-end simple random walk of a locally finite multigraph
  from `x` is the chain started at `x` whose kernel sends `v` to the image of the uniform measure on the edge
  ends at `v` under the target map `stateVertex`.
* `walkLaw_vertexPath_preimage`: the same statement for measurable events of vertex paths.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open MatedCRTHarmonic MatedCRTHarmonic.Markov

namespace LatticeProb.LQG

section Lumping

variable {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]

/-- Pointwise image of a finite history under a map of the state space. -/
def histMap (π : S → V) (n : ℕ) (h : Finset.Iic n → S) : Finset.Iic n → V := fun i => π (h i)

lemma measurable_histMap {π : S → V} (hπ : Measurable π) (n : ℕ) : Measurable (histMap π n) :=
  measurable_pi_iff.mpr fun i => hπ.comp (measurable_pi_apply i)

omit [MeasurableSpace S] [MeasurableSpace V] in
lemma histMap_histAppend (π : S → V) (n : ℕ) :
    histMap π (n + 1) ∘ histAppend n = histAppend n ∘ Prod.map (histMap π n) π := by
  funext p i
  by_cases hi : i.val ≤ n <;> simp [histMap, histAppend, hi]

/-- The finite-dimensional marginal of the image chain: the image of the prefix law of the chain with kernel
`K` under the pointwise map `π` is the prefix law of the chain with kernel `κ`. -/
lemma map_histMap_prefix_chainLaw (K : Kernel S S) [IsMarkovKernel K] (κ : Kernel V V)
    [IsMarkovKernel κ] {π : S → V} (hπ : Measurable π) (hK : ∀ s, (K s).map π = κ (π s)) (z : S)
    (n : ℕ) :
    ((chainLaw K z).map (frestrictLe n)).map (histMap π n) =
      (chainLaw κ (π z)).map (frestrictLe n) := by
  induction n with
  | zero =>
    rw [chainLaw_initialHistory, chainLaw_initialHistory,
      Measure.map_dirac' (measurable_histMap hπ 0)]
    rfl
  | succ n ih =>
    have hmap : ∀ h, (histKernel K n h).map π = histKernel κ n (histMap π n h) := by
      intro h
      rw [histKernel_apply, histKernel_apply]
      exact hK _
    have h1 : ∀ (K' : Kernel S S) [IsMarkovKernel K'] (z' : S),
        (chainLaw K' z').map (frestrictLe (n + 1)) =
          ((chainLaw K' z').map (frestrictLe n) ⊗ₘ histKernel K' n).map (histAppend n) :=
      fun K' _ z' => prefix_succ (histKernel K') (Measure.dirac z') n
    have h2 : ∀ (K' : Kernel V V) [IsMarkovKernel K'] (z' : V),
        (chainLaw K' z').map (frestrictLe (n + 1)) =
          ((chainLaw K' z').map (frestrictLe n) ⊗ₘ histKernel K' n).map (histAppend n) :=
      fun K' _ z' => prefix_succ (histKernel K') (Measure.dirac z') n
    rw [h1 K z, h2 κ (π z),
      Measure.map_map (measurable_histMap hπ (n + 1)) (measurable_histAppend n), histMap_histAppend,
      ← Measure.map_map (measurable_histAppend n) ((measurable_histMap hπ n).prodMap hπ),
      compProd_map_prod_of_kernel_map _ _ _ _ _ (measurable_histMap hπ n) hπ hmap, ih]

/-- **Lumping of a Markov chain** (Dynkin's criterion). If `π` carries the one-step law of `K` at every state
`s` to the one-step law of `κ` at `π s`, then `π` carries the law of the chain with kernel `K` started at `z`
to the law of the chain with kernel `κ` started at `π z`, as laws on the whole path space. -/
theorem chainLaw_map_of_factor (K : Kernel S S) [IsMarkovKernel K] (κ : Kernel V V) [IsMarkovKernel κ]
    {π : S → V} (hπ : Measurable π) (hK : ∀ s, (K s).map π = κ (π s)) (z : S) :
    (chainLaw K z).map (fun ω n => π (ω n)) = chainLaw κ (π z) := by
  apply measure_eq_of_prefix_eq
  intro n
  have hpath : Measurable (fun ω : ℕ → S => fun k => π (ω k)) :=
    measurable_pi_iff.mpr fun k => hπ.comp (measurable_pi_apply k)
  rw [Measure.map_map (measurable_frestrictLe n) hpath]
  have heq : frestrictLe n ∘ (fun (ω : ℕ → S) k => π (ω k)) = histMap π n ∘ frestrictLe n := rfl
  rw [heq, ← Measure.map_map (measurable_histMap hπ n) (measurable_frestrictLe n)]
  exact map_histMap_prefix_chainLaw K κ hπ hK z n

end Lumping

section Walk

variable {V E : Type*} (G : LFMultigraph V E) [MeasurableSpace V]

/-- **The vertex path of the edge-end walk is a Markov chain on the vertices.** If `κ` sends `x` to the image
of the one-step measure `G.stepMeasure x` under `G.stateVertex`, the law of the vertex path of the edge-end walk
from `x` is the chain with kernel `κ` started at `x`. -/
theorem walkLaw_map_vertexPath (κ : Kernel V V) [IsMarkovKernel κ]
    (hκ : ∀ x, κ x = (G.stepMeasure x).map G.stateVertex) (x : V) :
    (G.walkLaw x).map G.vertexPath = chainLaw κ x :=
  chainLaw_map_of_factor G.walkKernel κ (π := G.stateVertex) measurable_from_top
    (fun s => (hκ (G.stateVertex s)).symm) (Sum.inl x)

/-- The vertex path is measurable for the product structure on `ℕ → V`. -/
lemma measurable_vertexPath' : Measurable G.vertexPath :=
  measurable_pi_iff.mpr fun n => measurable_from_top.comp (measurable_pi_apply n)

/-- Events of vertex paths: the edge-end walk from `x` and the vertex chain give the same probability. -/
theorem walkLaw_vertexPath_preimage (κ : Kernel V V) [IsMarkovKernel κ]
    (hκ : ∀ x, κ x = (G.stepMeasure x).map G.stateVertex) (x : V) {B : Set (ℕ → V)}
    (hB : MeasurableSet B) :
    G.walkLaw x (G.vertexPath ⁻¹' B) = chainLaw κ x B := by
  rw [← walkLaw_map_vertexPath G κ hκ x, Measure.map_apply (measurable_vertexPath' G) hB]

end Walk

end LatticeProb.LQG
