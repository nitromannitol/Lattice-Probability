import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K8L2

/-! A based closed-disc parametrization of an inverted exterior. -/

set_option autoImplicit false

noncomputable section

open Set Metric Function
open LQGMetric

namespace LatticeProb

/-- Inverting the exterior of a compact set with Jordan frontier and connected
complement gives a bounded domain with a based closed-disc parametrization. -/
theorem exists_inverted_exterior_disc {K : Set ℂ} {z : ℂ}
    (hK : IsCompact K) (hz : z ∈ interior K) (hKc : IsPreconnected Kᶜ)
    (hJ : JordanMap.IsJordanCurve (frontier K)) :
    ∃ e : closedBall (0 : ℂ) 1 ≃ₜ closure (CONF.DD.toOmega K z),
      (e ⟨0, mem_closedBall_self (by norm_num)⟩ : ℂ) = 0 ∧
      (fun x => (e x : ℂ)) '' {x | (x : ℂ) ∈ sphere 0 1} =
        (fun x => (x - z)⁻¹) '' frontier K := by
  have hzF : z ∉ frontier K := fun h => h.2 hz
  have hpc : IsPreconnected (frontier K) := by
    have h := JordanMap.jm_isPreconnected_diff_of_isJordanCurve hJ z
    rwa [sdiff_singleton_eq_self hzF] at h
  have hne : (frontier K).Nonempty := by
    obtain ⟨γ, _, _, he⟩ := hJ
    rw [← he]
    exact (NormedSpace.sphere_nonempty.2 zero_le_one).image γ
  have hKp := CONF.DD.to_isPreconnected_K hK hpc hne
  have hcomp : ∀ a ∉ CONF.DD.toOmega K z,
      ¬ Bornology.IsBounded (connectedComponentIn (CONF.DD.toOmega K z)ᶜ a) := by
    intro a ha hb
    have hzK : z ∉ K \ {z} := fun h => h.2 rfl
    have hp : IsPreconnected (CONF.DD.toOmega K z)ᶜ := by
      rw [CONF.DD.to_compl_omega]
      exact (CONF.DD.to_isPreconnected_diff hKp hz).image _
        (GM.jo_continuousOn_iota _ hzK)
    have hs := hp.subset_connectedComponentIn ha subset_rfl
    obtain ⟨r, hr, hΩ⟩ := CONF.DD.to_omega_subset hz
    refine GM.jb_not_isBounded_lt_norm (1 / r) (hb.subset (fun w hw => hs fun hwΩ => ?_))
    have h := hΩ hwΩ
    rw [mem_closedBall, dist_zero_right] at h
    exact not_le.2 hw h
  obtain ⟨r, hr, hΩ⟩ := CONF.DD.to_omega_subset hz
  have hfr := CONF.DD.to_frontier_omega hK hz
  have hJΩ : JordanMap.IsJordanCurve (frontier (CONF.DD.toOmega K z)) := by
    rw [hfr]
    exact CONF.k8l_jordan_inv hJ hzF
  obtain ⟨φ, hc, hi, _, hzero, hball, hsphere⟩ :=
    JordanMap.jm_jordan_closedDisc_extension' (CONF.DD.to_isOpen_omega hK hz)
      (CONF.DD.to_isPreconnected_omega hK hz hKc) (Or.inr rfl)
      ((isBounded_closedBall (x := (0 : ℂ))).subset hΩ) hcomp hJΩ
  have hclosure : φ '' closedBall 0 1 = closure (CONF.DD.toOmega K z) := by
    rw [← ball_union_sphere, image_union, hball, hsphere,
      closure_eq_self_union_frontier]
  let F : closedBall (0 : ℂ) 1 → closure (CONF.DD.toOmega K z) :=
    fun x => ⟨φ x, hclosure ▸ mem_image_of_mem φ x.2⟩
  have hbij : Bijective F := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hi x.2 y.2 (congrArg Subtype.val hxy))
    · intro y
      have hy : (y : ℂ) ∈ φ '' closedBall 0 1 := by rw [hclosure]; exact y.2
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hcont : Continuous F :=
    (hc.comp_continuous continuous_subtype_val (fun x => x.2)).subtype_mk _
  let : CompactSpace (closedBall (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  let e : closedBall (0 : ℂ) 1 ≃ₜ closure (CONF.DD.toOmega K z) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hbij) hcont
  refine ⟨e, hzero, ?_⟩
  rw [← hfr, ← hsphere]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, sphere_subset_closedBall hx⟩, hx, rfl⟩

end LatticeProb
