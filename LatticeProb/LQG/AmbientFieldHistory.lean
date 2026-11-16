import LatticeProb.LQG.CoupledAnchorHistory
import LatticeProb.LQG.RandomDiscreteFieldCode
import LatticeProb.Topology.CompactStoppedPrefix

/-! # Ambient measurability of compact field histories -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A compact collar code is measurable from the compact set and field. -/
theorem measurable_collarFieldCode {Ω : Type} {I : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {h : Ω → DistC} {K : Ω → NonemptyCompacts ℂ}
    (hh : Measurable h) (hK : Measurable K) (φ : I → TestC) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) :
    Measurable (collarFieldCode h K φ ψ hp k) := by
  apply Measurable.prodMk hK
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro i
    have hE : MeasurableSet {ω | tsupport (φ i : ℂ → ℝ) ⊆
        thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)} :=
      measurableSet_compact_subset_thickening hK (φ i).hasCompactSupport.isCompact _
    exact (measurable_const.indicator hE).prodMk
      ((((LQGMetric.GFFInv.measurable_pair (φ i)).comp hh).sub
        (measurable_const.mul ((LQGMetric.GFFInv.measurable_pair (ψ k)).comp hh))).indicator hE)
  · exact (LatticeProb.measurable_toIcoMod_zero hp).comp
      ((LQGMetric.GFFInv.measurable_pair (ψ k)).comp hh)

/-- The dyadic hull field observation is measurable from the compact set and field. -/
theorem localHullFieldSigma_le_ambient {Ω : Type} [MeasurableSpace Ω]
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {h : Ω → DistC} {K : Ω → NonemptyCompacts ℂ}
    (hh : Measurable h) (hK : Measurable K) (n : ℕ) (a : TestC)
    {p : ℝ} (hp : 0 < p) :
    localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n a hp ≤ ‹MeasurableSpace Ω› := by
  let A : Ω → Set ℂ := fun ω => K ω
  have hset : setSigma A ≤ ‹MeasurableSpace Ω› := by
    apply MeasurableSpace.generateFrom_le
    rintro E ⟨U, hU, rfl⟩
    exact (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).measurableSet.preimage hK
  have hbounded : ∀ ω, Bornology.IsBounded (A ω) := fun ω => (K ω).isCompact.isBounded
  have hhull : hullSigma0 h A n ≤ ‹MeasurableSpace Ω› := by
    unfold hullSigma0
    apply sup_le hset
    apply MeasurableSpace.generateFrom_le
    rintro E ⟨S, F, hF, rfl⟩
    have hpiece : MeasurableSet {ω | dyadicHull n (A ω) = S} :=
      hset _ (LQGMetric.LocalEvent.measurableSet_hull_eq
        (fun ω => (K ω).isCompact.isClosed) n S)
    have hf : fieldSigma0On h (interior S) ≤ ‹MeasurableSpace Ω› := by
      unfold fieldSigma0On
      apply Measurable.comap_le
      apply measurable_pi_iff.mpr
      intro φ
      exact (LQGMetric.GFFInv.measurable_pair φ.1.1).comp hh
    exact hpiece.inter (hf _ hF)
  unfold localHullFieldSigma
  apply sup_le hhull
  apply Measurable.comap_le
  unfold localHullFieldPhase
  exact ((LatticeProb.measurable_toIcoMod_zero hp).comp
    ((LQGMetric.GFFInv.measurable_pair a).comp hh)).indicator
      (hhull _ (measurableSet_subset_interior_dyadicHull h A hbounded n _))

/-- Both joined field histories are ambient whenever the shared history,
field and compact set are measurable. -/
theorem joined_field_histories_le_ambient {Ω : Type} [m : MeasurableSpace Ω]
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {h : Ω → DistC} {K : Ω → NonemptyCompacts ℂ}
    (hh : Measurable h) (hK : Measurable K) (H : MeasurableSpace Ω)
    (hH : H ≤ m) (a ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) :
    (H ⊔ ⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp) ≤
        m ∧
      (H ⊔ ⨅ k, MeasurableSpace.comap
        (collarFieldCode h K localDenseTest ψ hp k) inferInstance) ≤ m := by
  let : MeasurableSpace Ω := m
  constructor
  · exact sup_le hH ((iInf_le _ 0).trans (localHullFieldSigma_le_ambient hh hK 0 (a 0) hp))
  · exact sup_le hH ((iInf_le _ 0).trans
      (measurable_collarFieldCode hh hK localDenseTest ψ hp 0).comap_le)

end LatticeProb.LQG
