import LatticeProb.Bonanno.ReflectedGMS.GeomTop.GMSTopologyTriangle
import LatticeProb.Prob.CellConfigStableInvariantCountable

/-! # Cell configuration patch classes -/

set_option autoImplicit false

open Set

namespace ReflectedGMS.GMS

namespace CellConfig

/-- Two configurations have the same patch at a radius when one plane
homeomorphism matches the restricted cells and preserves adjacency in both directions. -/
def patchSetoid (r : ℝ) : Setoid CellConfig where
  r H H' := ∃ f : Plane ≃ₜ Plane, AdmissibleAt H H' r f
  iseqv := ⟨
    fun H => ⟨Homeomorph.refl Plane, admissibleAt_refl H r⟩,
    fun ⟨f, hf⟩ => ⟨f.symm, by
      simpa only [AdmissibleAt, Homeomorph.symm_symm] using
        And.intro hf.2.1 (And.intro hf.1 (And.intro hf.2.2.2 hf.2.2.1))⟩,
    fun ⟨f, hf⟩ ⟨g, hg⟩ =>
      ⟨f.trans g, ReflectedGMS.GeomTop.GMSTopology.admissibleAt_trans hf hg⟩⟩

/-- The patch class of a configuration at a fixed radius. -/
def patchClass (r : ℝ) (H : CellConfig) : Quotient (patchSetoid r) :=
  Quotient.mk (patchSetoid r) H

/-- Equality of patch classes is witnessed by an admissible plane homeomorphism. -/
theorem patchClass_eq_iff (r : ℝ) (H H' : CellConfig) :
    patchClass r H = patchClass r H' ↔ ∃ f : Plane ≃ₜ Plane, AdmissibleAt H H' r f :=
  Quotient.eq

end CellConfig

/-- Only countably many fixed-radius patch classes occur among configurations
stable on a common interval in a second-countable subspace. -/
theorem countable_patchClasses_of_stable_restrict (T : Set GMSSpace)
    [SecondCountableTopology T] (S : Set T) {a b s : ℝ}
    (ha : 0 ≤ a) (hab : a < b)
    (hstable : ∀ x ∈ S, ∀ r ∈ Ioo a b,
      x.1.1.restrict (Metric.ball 0 r) = x.1.1.restrict (Metric.ball 0 s)) :
    ((fun x : T => CellConfig.patchClass s x.1.1) '' S).Countable := by
  apply countable_image_of_stable_restrict T S _ ha hab hstable
  intro x hx y hy f hf
  exact (CellConfig.patchClass_eq_iff s x.1.1 y.1.1).2 ⟨f, hf⟩

end ReflectedGMS.GMS
