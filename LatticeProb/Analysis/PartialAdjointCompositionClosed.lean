import LatticeProb.Analysis.PartialAdjointCompositionEnergy

/-! # Closedness of an adjoint composition -/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LatticeProb

/-- The graph of the composition of a densely defined closed operator with its
adjoint is closed. -/
theorem isClosed_adjoint_composition_graph {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (G : E →ₗ.[ℂ] F) (hdense : Dense (G.domain : Set E)) (hclosed : G.IsClosed) :
    IsClosed {p : E × E | ∃ u : G.domain, ∃ hu : G u ∈ G.adjoint.domain,
      ((u : E), G.adjoint ⟨G u, hu⟩) = p} := by
  apply isSeqClosed_iff_isClosed.mp
  intro s p hs hlim
  choose u hu heq using hs
  have hfirst : Tendsto (fun n => (u n : E)) atTop (𝓝 p.1) := by
    have h := (continuous_fst.tendsto p).comp hlim
    convert h using 1
    funext n
    exact congrArg Prod.fst (heq n)
  have hsecond : Tendsto (fun n => G.adjoint ⟨G (u n), hu n⟩) atTop (𝓝 p.2) := by
    have h := (continuous_snd.tendsto p).comp hlim
    convert h using 1
    funext n
    exact congrArg Prod.snd (heq n)
  have hc : CauchySeq (fun n => G (u n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hfirst.cauchySeq ε hε
    obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp hsecond.cauchySeq ε hε
    refine ⟨max N M, fun n hn m hm => ?_⟩
    have h₁ := hN n (le_trans (le_max_left _ _) hn) m (le_trans (le_max_left _ _) hm)
    have h₂ := hM n (le_trans (le_max_right _ _) hn) m (le_trans (le_max_right _ _) hm)
    rw [dist_eq_norm] at h₁ h₂ ⊢
    have hbound := norm_sub_apply_sq_le_adjoint_composition G hdense (u n) (u m) (hu n) (hu m)
    have hnonneg := norm_nonneg (G (u n) - G (u m))
    have hnonneg₁ := norm_nonneg ((u n : E) - (u m : E))
    have hnonneg₂ := norm_nonneg (G.adjoint ⟨G (u n), hu n⟩ - G.adjoint ⟨G (u m), hu m⟩)
    nlinarith
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hc
  have hG : (p.1, w) ∈ G.graph := by
    apply hclosed.mem_of_tendsto (hfirst.prodMk_nhds hw)
    exact Filter.Eventually.of_forall fun n => G.mem_graph (u n)
  obtain ⟨u₀, hu₀, hw₀⟩ := (G.mem_graph_iff).mp hG
  have hAdj : (w, p.2) ∈ G.adjoint.graph := by
    apply (G.adjoint_isClosed hdense).mem_of_tendsto (hw.prodMk_nhds hsecond)
    exact Filter.Eventually.of_forall fun n => G.adjoint.mem_graph ⟨G (u n), hu n⟩
  obtain ⟨w₀, hw₁, hw₂⟩ := (G.adjoint.mem_graph_iff).mp hAdj
  change G u₀ = w at hw₀
  change (w₀ : F) = w at hw₁
  have hwmem : G u₀ ∈ G.adjoint.domain := by rw [hw₀, ← hw₁]; exact w₀.property
  refine ⟨u₀, hwmem, ?_⟩
  apply Prod.ext
  · exact hu₀
  · change G.adjoint ⟨G u₀, hwmem⟩ = p.2
    have he : (⟨G u₀, hwmem⟩ : G.adjoint.domain) = w₀ := Subtype.ext (hw₀.trans hw₁.symm)
    rw [he, hw₂]

end LatticeProb
