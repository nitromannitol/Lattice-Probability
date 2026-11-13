/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.CanonicalFastFormProcess at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedIdentification
import LatticeProb.Bonanno.ReflectedGMS.Forms.BoundedDomainDensity
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import LatticeProb.Bonanno.ReflectedWalk.MarkovProperty

/-! Apply the full-form identification to the original constructed process,
choosing a faster admissible clock with positive summable speed. -/

-- Merged from `ReflectedGMS/Forms/SummableFastSpeed.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_SummableFastSpeed

/-!
# Summable speed measures above prescribed jump rates

On a countable connected nontrivial conductance graph, every strictly positive
prescribed rate can be increased so that the resulting speed measure
`m v = G.pi v / w v` is strictly positive and summable.
-/

set_option autoImplicit false

namespace ReflectedGMS.FullNetworkForm

noncomputable section

variable {V : Type*} [Countable V] [Nontrivial V]

/-- Every positive prescribed jump rate is dominated by a positive rate whose
associated speed measure `G.pi / w` is summable. -/
theorem exists_summable_fast_speed
    (G : ReflectedWalk.ConductanceGraph V)
    (hG : G.toSimpleGraph.Connected)
    (wstar : V → ℝ) (hwstar : ∀ v, 0 < wstar v) :
    ∃ w : V → ℝ,
      (∀ v, 0 < w v) ∧
      (∀ v, wstar v ≤ w v) ∧
      (∀ v, 0 < G.pi v / w v) ∧
      Summable (fun v => G.pi v / w v) := by
  let _ : Encodable V := Encodable.ofCountable V
  let q : V → ℝ := fun v => (1 / 2 : ℝ) ^ Encodable.encode v
  have hq_pos : ∀ v, 0 < q v := by
    intro v
    simp only [q]
    positivity
  have hq_sum : Summable q := by
    simpa only [q] using (summable_geometric_two_encode (ι := V))
  let w : V → ℝ := fun v => max (wstar v) (G.pi v / q v)
  have hw_pos : ∀ v, 0 < w v := by
    intro v
    exact lt_of_lt_of_le (hwstar v) (le_max_left _ _)
  refine ⟨w, hw_pos, ?_, ?_, ?_⟩
  · intro v
    exact le_max_left _ _
  · intro v
    exact div_pos (G.pi_pos_of_connected hG v) (hw_pos v)
  · refine Summable.of_nonneg_of_le
      (fun v => (div_pos (G.pi_pos_of_connected hG v) (hw_pos v)).le) ?_ hq_sum
    intro v
    apply (div_le_iff₀ (hw_pos v)).2
    have h := (div_le_iff₀ (hq_pos v)).1 (le_max_right (wstar v) (G.pi v / q v))
    simpa only [w, mul_comm] using h

end

end ReflectedGMS.FullNetworkForm

end Merged_SummableFastSpeed

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.IndexSet FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-- The existing constructed process satisfies the full reflected-walk
conditions once its rate dominates the proved admissible threshold. -/
theorem canonical_isReflectedWalk_of_rate_le
    {G : ConductanceGraph V} (E : G.Exhaustion)
    (hG : G.toSimpleGraph.Connected) (hmin : G.EnergyMinimizer)
    (w : V → ℝ) (hw : ∀ v, 0 < w v)
    (hdom : ∀ v, E.rateFunction hG v ≤ w v) :
    IsReflectedWalk G w hmin (Existence.processFamily E hG w) := by
  have hfin : {v | w v < E.rateFunction hG v}.Finite := by
    have he : {v | w v < E.rateFunction hG v} = ∅ := by
      ext v
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact not_lt_of_ge (hdom v)
    rw [he]
    exact finite_empty
  have hsum : ∀ z, ∀ᵐ ω ∂Existence.sampleLaw E hG z,
      HoldingTimesSummable (E.levelSets (E.nz z)) ω.1 w ω.2 := fun z =>
    E.Pz_ae_holdingTimesSummable hG w hw hfin z
  exact Existence.isReflectedWalk E hG w hw hmin hsum
    (Existence.markovProperty E hG w hw hsum)

end ReflectedGMS
