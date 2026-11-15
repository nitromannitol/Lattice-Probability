import LatticeProb.Topology.PlanarFilledHull
import LatticeProb.LQG.MatingOfTreesCouplingPathwise
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412hBor2

/-! # Measurability of filled hulls of compact curve images -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Membership of a fixed point in the filled hull of a compact curve image is Borel. -/
theorem measurableSet_mem_planarFilledHull_image {K : Set ℝ} (hK : IsCompact K) (z : ℂ) :
    MeasurableSet {f : C(ℝ, ℂ) | z ∈ planarFilledHull (f '' K)} := by
  let F : C(ℝ, ℂ) → Set ℂ := fun f => f '' K
  have hF : LQGMetric.GM.P412hCT F := by
    refine ⟨?_, ?_, ?_⟩
    · intro w
      exact ((ContinuousMap.isClosed_setOf_mem_image hK).preimage
        (continuous_id.prodMk continuous_const)).measurableSet
    · intro f
      exact (hK.image f.continuous).isClosed
    · intro S hS
      have : CompactSpace K := isCompact_iff_compactSpace.mp hK
      have hclosed : IsClosed {p : C(ℝ, ℂ) × K | p.1 p.2 ∈ S} :=
        hS.isClosed.preimage (ContinuousEval.continuous_eval.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
      have himage : Prod.fst '' {p : C(ℝ, ℂ) × K | p.1 p.2 ∈ S} =
          {f : C(ℝ, ℂ) | ∃ t ∈ K, f t ∈ S} := by
        ext f
        constructor
        · rintro ⟨⟨g, t⟩, ht, hg⟩
          change g = f at hg
          subst g
          exact ⟨t, t.property, ht⟩
        · rintro ⟨t, ht, hft⟩
          exact ⟨(f, ⟨t, ht⟩), hft, rfl⟩
      have hproj : IsClosed {f : C(ℝ, ℂ) | ∃ t ∈ K, f t ∈ S} := by
        rw [← himage]
        exact isClosedMap_fst_of_compactSpace _ hclosed
      have heq : {f : C(ℝ, ℂ) | S ⊆ (F f)ᶜ} =
          {f : C(ℝ, ℂ) | ∃ t ∈ K, f t ∈ S}ᶜ := by
        ext f
        simp only [mem_ofPred_eq, mem_compl_iff, F, subset_compl_iff_disjoint_right,
          Set.disjoint_left, mem_image]
        aesop
      rw [heq]
      exact hproj.measurableSet.compl
  have hmem := hF.mem z
  have hbounded := LQGMetric.GM.p412h_meas_dgB hF z
  simpa only [planarFilledHull, LQGMetric.GM.dgB, F, mem_union, mem_compl_iff, mem_ofPred_eq, ofPred_or] using
    hmem.union hbounded

end LatticeProb
