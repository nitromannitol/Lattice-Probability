import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveGeometry

/-! # Cellular embeddings for shifted curve cells -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- A time shift whose root interval contains time zero gives a rooted cellular embedding.
The shifted curve need not itself take the value zero at time zero. -/
def shiftedRootCellularEmbedding {w : Path2} {η ηL : C(ℝ, ℂ)} {ε c : ℝ}
    (hε : 0 < ε) (hc0 : 0 ≤ c) (hcε : c ≤ ε) (hη0 : η 0 = 0)
    (hlf : IsLocallyFinite ε w)
    (P : RouteM.Peanosphere w (fun t => η (t + c)))
    (hs : RouteM.SideStrict ε w)
    (hi : ∀ a b : ℝ, a < b → (interior (η '' Icc a b)).Nonempty)
    (φ : ℝ ≃o ℝ) (hη : ∀ t, η t = ηL (φ t))
    (hvol : ∀ s t : ℝ, s ≤ t → volume (ηL '' Icc s t) = ENNReal.ofReal (t - s)) :
    CellularEmbedding (MatedCRT.graph ε w hlf) 0 := by
  let ξ : C(ℝ, ℂ) := ⟨fun t => η (t + c), η.continuous.comp (by fun_prop)⟩
  have hξ : ∀ t, ξ t = ηL (((OrderIso.addRight c).trans φ) t) := by
    intro t
    exact hη (t + c)
  refine {
    cell := fun x => ξ '' Icc (ε * ((x : ℝ) - 1)) (ε * x)
    isCompact_cell := fun x => isCompact_Icc.image ξ.continuous
    isConnected_cell := fun x => (isConnected_Icc (by nlinarith :
      ε * ((x : ℝ) - 1) ≤ ε * x)).image ξ ξ.continuous.continuousOn
    interior_cell_nonempty := ?_
    locallyFinite_cell := locallyFinite_curve_cellsAt hε P.transient
    iUnion_cell := curve_cellsAt_cover hε P.surj
    volume_inter_cell := fun x y hxy => volume_inter_mesh_cells_zero hε hξ hvol hxy
    inter_of_adj := fun x y hadj => cell_intersects_of_matedCRT_adj hε P hs hadj
    zero_mem_root := ?_ }
  · intro x
    have heq : ξ '' Icc (ε * ((x : ℝ) - 1)) (ε * x) =
        η '' Icc (ε * ((x : ℝ) - 1) + c) (ε * x + c) := by
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t + c, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t - c, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by simp [ξ]⟩
    rw [heq]
    exact hi _ _ (by nlinarith [hε])
  · refine ⟨-c, ?_, ?_⟩
    · constructor <;> simp only [Int.cast_zero, zero_sub, mul_neg, mul_one, mul_zero] <;> linarith
    · change η (-c + c) = 0
      simpa using hη0

end MatedCRTHarmonic.MoTInput
