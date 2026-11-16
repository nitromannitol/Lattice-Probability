import LatticeProb.LQG.HullObservationCollar
import LatticeProb.Topology.CompactCommonPoint
import LatticeProb.Prob.MeasurableCarrierInfimum

/-! # Restriction of field observation germs to a compact-anchor carrier -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- The event that a fixed point belongs to a random compact is observed by
its hit sigma algebra. -/
theorem measurableSet_mem_compact_of_setSigma {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (K : Ω → NonemptyCompacts ℂ) (z : ℂ) :
    MeasurableSet[setSigma (fun ω => (K ω : Set ℂ))] {ω | z ∈ (K ω : Set ℂ)} := by
  let : MeasurableSpace Ω := setSigma (fun ω => (K ω : Set ℂ))
  have hK : Measurable K := measurable_compactEncoding_of_setSigma _ K (fun _ => rfl)
  have hclosed : IsClosed {K : NonemptyCompacts ℂ | z ∈ (K : Set ℂ)} := by
    exact LatticeProb.Topology.isClosed_mem_nonemptyCompacts.preimage
      (continuous_const.prodMk continuous_id)
  exact hclosed.measurableSet.preimage hK

/-- The compact-anchor event belongs to each local hull observation. -/
theorem measurableSet_mem_compact_of_localHullFieldSigma {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (z : ℂ)
    (n : ℕ) (a : TestC) {p : ℝ} (hp : 0 < p) :
    MeasurableSet[localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n a hp]
      {ω | z ∈ (K ω : Set ℂ)} := by
  exact (le_sup_left : setSigma (fun ω => (K ω : Set ℂ)) ≤
    hullSigma0 h (fun ω => (K ω : Set ℂ)) n).trans le_sup_left _
      (measurableSet_mem_compact_of_setSigma K z)

/-- The compact-anchor event belongs to each collar code observation. -/
theorem measurableSet_mem_compact_of_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (z : ℂ)
    (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) (k : ℕ) :
    MeasurableSet[MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp k) inferInstance]
      {ω | z ∈ (K ω : Set ℂ)} :=
  setSigma_le_collarFieldCode h K ψ hp k _ (measurableSet_mem_compact_of_setSigma K z)

/-- Restricting a joined hull observation germ to the anchor carrier commutes
with its countable infimum. -/
theorem comap_anchorCarrier_hull_germ {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (H : MeasurableSpace Ω) (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (a : ℕ → TestC) {p : ℝ} (hp : 0 < p) :
    let A := {ω | z ∈ (K ω : Set ℂ)}
    MeasurableSpace.comap (Subtype.val : A → Ω)
        (H ⊔ ⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp) =
      MeasurableSpace.comap (Subtype.val : A → Ω) H ⊔
        ⨅ n, MeasurableSpace.comap (Subtype.val : A → Ω)
          (localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp) :=
  LatticeProb.comap_subtype_sup_iInf_of_measurable H _ _
    (fun n => measurableSet_mem_compact_of_localHullFieldSigma h K z n (a n) hp)

/-- Restricting a joined collar observation germ to the anchor carrier
commutes with its countable infimum. -/
theorem comap_anchorCarrier_collar_germ {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (H : MeasurableSpace Ω) (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) :
    let A := {ω | z ∈ (K ω : Set ℂ)}
    MeasurableSpace.comap (Subtype.val : A → Ω)
        (H ⊔ ⨅ k, MeasurableSpace.comap
          (collarFieldCode h K localDenseTest ψ hp k) inferInstance) =
      MeasurableSpace.comap (Subtype.val : A → Ω) H ⊔
        ⨅ k, MeasurableSpace.comap (Subtype.val : A → Ω)
          (MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance) :=
  LatticeProb.comap_subtype_sup_iInf_of_measurable H _ _
    (fun k => measurableSet_mem_compact_of_collarFieldCode h K z ψ hp k)

end LatticeProb.LQG
