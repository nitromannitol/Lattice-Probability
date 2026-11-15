/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ClockedExcursionRange at commit fdb5cad17d11550228cf8dbaf6216e69fc3d2d82;
   local import paths are updated, and only the initial convex-range export of the source
   (lines 16-27) is included. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ClockedWalkExcursion

/-! The actual clocked walk excursion stays in any closed convex set containing
all embedded vertices of the finite network. The clocked law pushes forward to
the previously defined walk excursion law along the normalized curve, so the
convex-range statement transfers from the latter. -/

open MeasureTheory ProbabilityTheory Set Metric
open scoped unitInterval ENNReal

namespace BouRabeeGwynne
namespace FiniteConductanceNetwork

variable {d : ℕ} {V : Type*} [Fintype V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

lemma clockedWalkExcursionKernel_ae_mem_convex (N : FiniteConductanceNetwork V)
    (pos : V → Euc d) (B : Set V)
    (hB : ∀ v ∈ B, 0 < N.totalConductance v) (v : V)
    {S : Set (Euc d)} (hS : Convex ℝ S) (hclosed : IsClosed S)
    (hvertices : ∀ w, pos w ∈ S) :
    ∀ᵐ e ∂N.clockedWalkExcursionKernel pos B hB v,
      ∀ t, ClockedWalkExcursion.curve e t ∈ S := by
  have h := N.walkExcursionKernel_ae_mem_convex pos B hB v hS hclosed hvertices
  rw [← N.clockedWalkExcursionKernel_curve pos B hB v] at h
  exact ae_of_ae_map ClockedWalkExcursion.measurable_curve.aemeasurable h

end FiniteConductanceNetwork
end BouRabeeGwynne
