/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.TopoMain at commit fdb5cad; only the module paths of local imports are changed. -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.TopoSep

/-! # Simply connected bounded planar domains have connected complement

If the complement split into two closed sides, one side would be compact because
the complement contains the connected exterior of a large disk. The frontier of
a compact neighborhood of that side lies in the domain. Eilenberg's criterion
then contradicts the logarithm supplied by simple connectivity.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRTHarmonic

open Set Metric QuantumZipper.CA.Topo

/-- The classical planar topology bridge used in [18], Theorem 1.5 and
Corollary 1.6: a bounded simply connected open domain has connected complement. -/
theorem isConnected_compl_of_simplyConnected {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) (hDne : D.Nonempty)
    [SimplyConnectedSpace D] : IsConnected (Dᶜ) := by
  have hDuniv : D ≠ univ := by
    intro h
    subst D
    exact NormedSpace.unbounded_univ ℂ ℂ hDb
  have hDcne : Dᶜ.Nonempty := Set.nonempty_compl.mpr hDuniv
  by_contra hconn
  have hnotpre : ¬ IsPreconnected Dᶜ := fun hp => hconn ⟨hDcne, hp⟩
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hDo.isClosed_compl] at hnotpre
  push Not at hnotpre
  obtain ⟨K, F, hKcl, hFcl, hcover, hKF, hnotK, hnotF⟩ := hnotpre
  let K₀ : Set ℂ := K ∩ Dᶜ
  let F₀ : Set ℂ := F ∩ Dᶜ
  have hK₀cl : IsClosed K₀ := hKcl.inter hDo.isClosed_compl
  have hF₀cl : IsClosed F₀ := hFcl.inter hDo.isClosed_compl
  have hK₀D : K₀ ⊆ Dᶜ := inter_subset_right
  have hF₀D : F₀ ⊆ Dᶜ := inter_subset_right
  have hK₀F₀ : Disjoint K₀ F₀ := hKF.mono inter_subset_left inter_subset_left
  have hcover₀ : Dᶜ ⊆ K₀ ∪ F₀ := by
    intro z hz
    rcases hcover hz with hzK | hzF
    · exact Or.inl ⟨hzK, hz⟩
    · exact Or.inr ⟨hzF, hz⟩
  have hK₀ne : K₀.Nonempty := by
    obtain ⟨z, hzD, hzF⟩ := Set.not_subset.mp hnotF
    rcases hcover hzD with hzK | hzFin
    · exact ⟨z, hzK, hzD⟩
    · exact False.elim (hzF hzFin)
  have hF₀ne : F₀.Nonempty := by
    obtain ⟨z, hzD, hzK⟩ := Set.not_subset.mp hnotK
    rcases hcover hzD with hzK' | hzF
    · exact False.elim (hzK hzK')
    · exact ⟨z, hzF, hzD⟩
  obtain ⟨R, hDR⟩ := hDb.subset_ball (0 : ℂ)
  let E : Set ℂ := {z : ℂ | R < ‖z‖}
  have hEpre : IsPreconnected E := isPreconnected_setOf_lt_norm R
  have hED : E ⊆ Dᶜ := setOf_lt_norm_subset_compl hDR
  have hEcover : E ⊆ K₀ ∪ F₀ := hED.trans hcover₀
  have hEdis : E ∩ (K₀ ∩ F₀) = ∅ := by
    rw [hK₀F₀.inter_eq, inter_empty]
  have hEside := (isPreconnected_iff_subset_of_disjoint_closed).mp hEpre
    K₀ F₀ hK₀cl hF₀cl hEcover hEdis
  rcases hEside with hEK | hEF
  · have hF₀bd : Bornology.IsBounded F₀ :=
      isBounded_closedBall.subset (by
        intro z hzF
        rw [mem_closedBall_zero_iff]
        by_contra hzR
        exact (disjoint_right.mp hK₀F₀ hzF) (hEK (lt_of_not_ge hzR)))
    exact topo_false_of_closed_separation hDo
      (Metric.isCompact_of_isClosed_isBounded hF₀cl hF₀bd) hK₀cl
      hK₀F₀.symm (by simpa [union_comm] using hcover₀)
      hF₀D hK₀D hF₀ne hK₀ne
  · have hK₀bd : Bornology.IsBounded K₀ :=
      isBounded_closedBall.subset (by
        intro z hzK
        rw [mem_closedBall_zero_iff]
        by_contra hzR
        exact (disjoint_left.mp hK₀F₀ hzK) (hEF (lt_of_not_ge hzR)))
    exact topo_false_of_closed_separation hDo
      (Metric.isCompact_of_isClosed_isBounded hK₀cl hK₀bd) hF₀cl
      hK₀F₀ hcover₀ hK₀D hF₀D hK₀ne hF₀ne

end MatedCRTHarmonic
