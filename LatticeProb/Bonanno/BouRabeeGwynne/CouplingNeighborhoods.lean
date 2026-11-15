/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.CouplingNeighborhoods at commit fdb5cad; only the module path of the local import is changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.FixedBallCover

/-! Choose the fixed outer boundary collar, ambient region and excursion balls
before the skeleton length and the backward endpoint partitions. -/

open Set Metric

namespace BouRabeeGwynne

theorem exists_coupling_neighborhoods {d : ℕ} {U D : Set (Euc d)}
    (hUb : Bornology.IsBounded U) (hUD : HasAmbientCollar U D)
    {δmax rmax : ℝ} (hδmax : 0 < δmax) (hrmax : 0 < rmax) :
    ∃ (δ r : ℝ) (W Q : Set (Euc d)) (centers : Finset (Euc d)),
      0 < δ ∧ δ ≤ δmax ∧ 0 < r ∧ r ≤ rmax ∧ r ≤ δ / 100 ∧
      IsOpen W ∧ Bornology.IsBounded W ∧ HasAmbientCollar W D ∧
      IsCompact Q ∧ cthickening δ U ⊆ Q ∧
      (∀ c ∈ centers, c ∈ cthickening δ U) ∧
      (∀ z ∈ cthickening δ U, ∃ c ∈ centers, z ∈ ball c (r / 4)) ∧
      (∀ c ∈ centers, closedBall c r ⊆ W) ∧
      (∀ c ∈ centers, closure (ball c r) ⊆ Q) := by
  obtain ⟨α, hα, hαD⟩ := hUb.isCompact_closure.exists_cthickening_subset_open
    isOpen_interior hUD
  let δ := min (α / 4) δmax
  have hδ : 0 < δ := lt_min (by positivity) hδmax
  have hδα : δ ≤ α / 4 := min_le_left _ _
  let W := thickening (2 * δ) U
  let Q := cthickening (2 * δ) U
  have hW : IsOpen W := isOpen_thickening
  have hQ : IsCompact Q := isCompact_of_isClosed_isBounded
    isClosed_cthickening hUb.cthickening
  have hCW : cthickening δ U ⊆ W :=
    cthickening_subset_thickening' (by positivity) (by linarith) U
  have hWQ : W ⊆ Q := thickening_subset_cthickening _ _
  have hWD : HasAmbientCollar W D := by
    apply (closure_thickening_subset_cthickening (2 * δ) U).trans
    apply ((cthickening_mono (by linarith : 2 * δ ≤ α) U).trans
      (cthickening_subset_of_subset α subset_closure)).trans hαD
  obtain ⟨r, hr, hrsmall, centers, hcenters, hcover, hballs⟩ :=
    exists_fixed_ball_cover
      (isCompact_of_isClosed_isBounded isClosed_cthickening hUb.cthickening)
      hW hCW (rmax := min rmax (δ / 100)) (lt_min hrmax (by positivity))
  refine ⟨δ, r, W, Q, centers, hδ, min_le_right _ _, hr,
    hrsmall.trans (min_le_left _ _), hrsmall.trans (min_le_right _ _),
    hW, hUb.thickening, hWD, hQ, hCW.trans hWQ, hcenters, hcover, hballs, ?_⟩
  intro c hc
  exact (closure_minimal ball_subset_closedBall isClosed_closedBall).trans
    ((hballs c hc).trans hWQ)

end BouRabeeGwynne
