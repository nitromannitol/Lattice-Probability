import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Sets.VietorisTopology

/-! # Matching continuously varying compact images -/

set_option autoImplicit false

open Set Topology TopologicalSpace

namespace LatticeProb

variable {Ω X Y : Type*} [TopologicalSpace Ω] [TopologicalSpace X]
  [LocallyCompactSpace X] [TopologicalSpace Y]

/-- A continuously varying continuous map acts continuously on a varying nonempty compact set. -/
theorem continuous_nonemptyCompacts_image
    (F : Ω → C(X, Y)) (K : Ω → NonemptyCompacts X)
    (hF : Continuous F) (hK : Continuous K) :
    Continuous (fun ω => (K ω).map (F ω) (F ω).continuous) := by
  apply hK.nonemptyCompacts_map'
  exact continuous_eval.comp ((hF.comp continuous_fst).prodMk continuous_snd)

/-- Exact matching of continuously varying nonempty compact images is closed. -/
theorem isClosed_nonemptyCompacts_image_eq [T2Space Y]
    (F : Ω → C(X, Y)) (K : Ω → NonemptyCompacts X)
    (L : Ω → NonemptyCompacts Y)
    (hF : Continuous F) (hK : Continuous K) (hL : Continuous L) :
    IsClosed {ω | (K ω).map (F ω) (F ω).continuous = L ω} :=
  isClosed_eq (continuous_nonemptyCompacts_image F K hF hK) hL

end LatticeProb
