import LatticeProb.LQG.CouplingSharedSegmentFrontiers
import LatticeProb.Topology.CompactCurveRange
import LatticeProb.Topology.EmbeddedDiskComponentBound
import LatticeProb.Topology.ConsecutiveDiskIntersectionComponents
import LatticeProb.Topology.CompactPlaneIntersection

/-! # Contact components of coupled curve segments -/

open MeasureTheory Set Metric Bornology
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic.MoTInput

private theorem interval_contact_bounds (f : ℝ → ℂ)
    (hdisk : ∀ a b : ℝ, a < b → Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (f '' Icc a b)))
    (hdis : ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      Disjoint (interior (f '' Icc a b)) (interior (f '' Icc c d))) :
    ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      Cardinal.mk (ConnectedComponents ↥(f '' Icc a b ∩ f '' Icc c d)) ≤ 2 ∧
      (b = c → Cardinal.mk (ConnectedComponents ↥(f '' Icc a b ∩ f '' Icc c d)) ≤ 1) := by
  intro a b c d hab hbc hcd
  let A := f '' Icc a b
  let C := f '' Icc c d
  have eA : closedBall (0 : ℂ) 1 ≃ₜ A := (hdisk a b hab).some
  have eC : closedBall (0 : ℂ) 1 ≃ₜ C := (hdisk c d hcd).some
  have hd : Disjoint (interior A) (interior C) := hdis a b c d hab hbc hcd
  have eqadj (h : b = c) : A ∪ C = f '' Icc a d := by
    subst c
    rw [← image_union, Icc_union_Icc_eq_Icc hab.le hcd.le]
  have hadj (h : b = c) : Cardinal.mk (ConnectedComponents ↥(A ∩ C)) ≤ 1 := by
    have e : closedBall (0 : ℂ) 1 ≃ₜ ↥(A ∪ C) :=
      (hdisk a d (lt_trans hab (lt_of_le_of_lt hbc hcd))).some.trans
        (Homeomorph.setCongr (eqadj h).symm)
    have hcom := (LatticeProb.complex_embedded_closed_disk_compl_preconnected_unbounded e).1
    have hcA : IsCompact A := by
      let : CompactSpace A := eA.compactSpace
      exact isCompact_iff_compactSpace.mpr inferInstance
    have hcC : IsCompact C := by
      let : CompactSpace C := eC.compactSpace
      exact isCompact_iff_compactSpace.mpr inferInstance
    have hA : IsConnected A := (LatticeProb.closure_interior_of_homeomorph_closedDisk eA) ▸
      (LatticeProb.isConnected_interior_of_homeomorph_closedDisk eA).closure
    have hC : IsConnected C := (LatticeProb.closure_interior_of_homeomorph_closedDisk eC) ▸
      (LatticeProb.isConnected_interior_of_homeomorph_closedDisk eC).closure
    let : PreconnectedSpace ↥(A ∩ C) := isPreconnected_iff_preconnectedSpace.mp
      (LatticeProb.Topology.isPreconnected_inter_of_compl_union_preconnected hcA hcC hA hC hcom)
    exact Cardinal.le_one_iff_subsingleton.mpr inferInstance
  refine ⟨?_, hadj⟩
  by_cases h : b = c
  · exact (hadj h).trans (by norm_num)
  · have hbc' : b < c := lt_of_le_of_ne hbc h
    let B := f '' Icc b c
    have eB : closedBall (0 : ℂ) 1 ≃ₜ B := (hdisk b c hbc').some
    have hfull : (A ∪ C) ∪ B = f '' Icc a d := by
      calc
        (A ∪ C) ∪ B = (A ∪ B) ∪ C := by ac_rfl
        _ = f '' Icc a d := by
          dsimp [A, B, C]
          rw [← image_union, ← image_union, Icc_union_Icc_eq_Icc hab.le hbc'.le,
            Icc_union_Icc_eq_Icc (le_trans hab.le hbc'.le) hcd.le]
    have e : closedBall (0 : ℂ) 1 ≃ₜ ↥((A ∪ C) ∪ B) :=
      (hdisk a d (lt_trans hab (lt_trans hbc' hcd))).some.trans
        (Homeomorph.setCongr hfull.symm)
    obtain ⟨hext, hunbounded⟩ :=
      LatticeProb.complex_embedded_closed_disk_compl_preconnected_unbounded e
    let : Subsingleton (LatticeProb.Topology.BoundedPlaneComplementComponent (A ∪ C)) := ⟨by
      intro U V
      obtain ⟨p, hp, hU⟩ := U.val.property
      obtain ⟨q, hq, hV⟩ := V.val.property
      apply Subtype.ext
      apply Subtype.ext
      rw [hU, hV]
      exact LatticeProb.bounded_complement_components_eq_of_embedded_middle_disk
        (LatticeProb.closure_interior_of_homeomorph_closedDisk eA)
        (LatticeProb.closure_interior_of_homeomorph_closedDisk eC) eB hext hunbounded
        (hdis a b b c hab le_rfl hbc').symm (hdis b c c d hbc' le_rfl hcd)
        hp hq (hU ▸ U.property) (hV ▸ V.property)⟩
    exact LatticeProb.Topology.cardinal_inter_components_le_two_of_embedded_disks eA eC hd

/-- Assuming a common event of disk-shaped segments for the Lebesgue curve, all ordered
segments of both coupled area curves have at most two contact components, and adjacent
segments have at most one, simultaneously for every real endpoint. -/
theorem ae_interval_contact_bounds_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hdisk : ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (ηL ω '' Icc a b))) :
    ∀ᵐ ω ∂P, ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      (Cardinal.mk (ConnectedComponents ↥(η ω '' Icc a b ∩ η ω '' Icc c d)) ≤ 2 ∧
        (b = c → Cardinal.mk (ConnectedComponents ↥(η ω '' Icc a b ∩ η ω '' Icc c d)) ≤ 1)) ∧
      (Cardinal.mk (ConnectedComponents ↥(η₀ ω '' Icc a b ∩ η₀ ω '' Icc c d)) ≤ 2 ∧
        (b = c → Cardinal.mk (ConnectedComponents ↥(η₀ ω '' Icc a b ∩ η₀ ω '' Icc c d)) ≤ 1)) := by
  filter_upwards [hdisk, D.areaParam, D.areaParam₀, ae_shared_frontiers_of_coupling D] with ω hd ha ha₀ hf
  obtain ⟨φ, _, hφ⟩ := ha.1
  obtain ⟨ψ, _, hψ⟩ := ha₀.1
  have hsegment (χ : ℝ ≃o ℝ) (f : C(ℝ, ℂ)) (h : ∀ t, f t = ηL ω (χ t)) :
      ∀ a b : ℝ, a < b → Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (f '' Icc a b)) := by
    intro a b hab
    rw [show (f : ℝ → ℂ) = (ηL ω : ℝ → ℂ) ∘ χ from funext h, image_comp, χ.image_Icc]
    exact hd (χ a) (χ b) (χ.strictMono hab)
  have hdis (f : ℝ → ℂ) (h : ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      f '' Icc a b ∩ f '' Icc c d = frontier (f '' Icc a b) ∩ frontier (f '' Icc c d)) :
      ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
        Disjoint (interior (f '' Icc a b)) (interior (f '' Icc c d)) := by
    intro a b c d hab hbc hcd
    rw [disjoint_left]
    intro x hx hy
    have hi : x ∈ f '' Icc a b ∩ f '' Icc c d := ⟨interior_subset hx, interior_subset hy⟩
    rw [h a b c d hab hbc hcd] at hi
    exact hi.1.2 hx
  have hη := interval_contact_bounds (η ω) (hsegment φ (η ω) hφ)
    (hdis (η ω) (fun a b c d hab hbc hcd => (hf a b c d hab hbc hcd).2.1))
  have hη₀ := interval_contact_bounds (η₀ ω) (hsegment ψ (η₀ ω) hψ)
    (hdis (η₀ ω) (fun a b c d hab hbc hcd => (hf a b c d hab hbc hcd).2.2))
  intro a b c d hab hbc hcd
  exact ⟨hη a b c d hab hbc hcd, hη₀ a b c d hab hbc hcd⟩

/-- On the same event, every positive mesh and real phase has the contact bounds for
all ordered pairs of shifted cells of either coupled curve. -/
theorem ae_shifted_cell_contact_bounds_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hdisk : ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (ηL ω '' Icc a b))) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ θ : ℝ, ∀ i j : ℤ, i < j →
      (Cardinal.mk (ConnectedComponents ↥((LatticeProb.shiftedCompactCell (η ω) ε θ i : Set ℂ) ∩
        (LatticeProb.shiftedCompactCell (η ω) ε θ j : Set ℂ))) ≤ 2 ∧
        (j = i + 1 → Cardinal.mk (ConnectedComponents ↥((LatticeProb.shiftedCompactCell (η ω) ε θ i : Set ℂ) ∩
          (LatticeProb.shiftedCompactCell (η ω) ε θ j : Set ℂ))) ≤ 1)) ∧
      (Cardinal.mk (ConnectedComponents ↥((LatticeProb.shiftedCompactCell (η₀ ω) ε θ i : Set ℂ) ∩
        (LatticeProb.shiftedCompactCell (η₀ ω) ε θ j : Set ℂ))) ≤ 2 ∧
        (j = i + 1 → Cardinal.mk (ConnectedComponents ↥((LatticeProb.shiftedCompactCell (η₀ ω) ε θ i : Set ℂ) ∩
          (LatticeProb.shiftedCompactCell (η₀ ω) ε θ j : Set ℂ))) ≤ 1)) := by
  filter_upwards [ae_interval_contact_bounds_of_coupling D hdisk] with ω h
  intro ε hε θ i j hij
  have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
  have hlt (k : ℤ) : ε * ((k : ℝ) - 1 + θ) < ε * ((k : ℝ) + θ) :=
    mul_lt_mul_of_pos_left (by linarith) hε
  have hord : ε * ((i : ℝ) + θ) ≤ ε * ((j : ℝ) - 1 + θ) :=
    mul_le_mul_of_nonneg_left (by linarith) hε.le
  have hc (f : C(ℝ, ℂ)) (k : ℤ) : (LatticeProb.shiftedCompactCell f ε θ k : Set ℂ) =
      f '' Icc (ε * ((k : ℝ) - 1 + θ)) (ε * ((k : ℝ) + θ)) := by
    rw [LatticeProb.coe_shiftedCompactCell, uIcc_of_le (hlt k).le]
  have heq : j = i + 1 → ε * ((i : ℝ) + θ) = ε * ((j : ℝ) - 1 + θ) := by
    intro hj
    subst j
    push_cast
    ring
  rw [hc, hc, hc, hc]
  obtain ⟨h₁, h₂⟩ := h _ _ _ _ (hlt i) hord (hlt j)
  exact ⟨⟨h₁.1, fun hj => h₁.2 (heq hj)⟩, ⟨h₂.1, fun hj => h₂.2 (heq hj)⟩⟩

end MatedCRTHarmonic.MoTInput
