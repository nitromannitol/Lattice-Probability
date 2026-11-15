import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Schoenflies.Disc

/-! A based closed-disc parametrization of a bounded Jordan domain. -/

noncomputable section

namespace MatedCRTHarmonic.Planar.Schoenflies

open Metric Set Function Bornology
open LQGMetric.JordanMap

/-- A bounded Jordan domain has a closed-disc parametrization taking the centre to
any prescribed point in the domain. -/
theorem schoenflies_closedDisc_basepoint {Γ : Set ℂ} (hΓ : IsJordanCurve Γ)
    {p : ℂ} (hp : p ∈ Γᶜ) (hb : IsBounded (connectedComponentIn Γᶜ p)) :
    ∃ e : closedBall (0 : ℂ) 1 ≃ₜ closure (connectedComponentIn Γᶜ p),
      (e ⟨0, mem_closedBall_self (by norm_num)⟩ : ℂ) = p ∧
      (fun z => (e z : ℂ)) '' {z | (z : ℂ) ∈ sphere 0 1} = Γ ∧
      (fun z => (e z : ℂ)) '' {z | (z : ℂ) ∈ ball 0 1} =
        connectedComponentIn Γᶜ p := by
  obtain ⟨φ, hc, hi, _, hzero, hball, hsphere⟩ := schoenflies_disc hΓ hp hb
  have hclosure : φ '' closedBall 0 1 = closure (connectedComponentIn Γᶜ p) := by
    rw [← ball_union_sphere, image_union, hball, hsphere,
      closure_eq_self_union_frontier, (jordan_split hΓ hp hb).1]
  let F : closedBall (0 : ℂ) 1 → closure (connectedComponentIn Γᶜ p) :=
    fun z => ⟨φ z, hclosure ▸ mem_image_of_mem φ z.2⟩
  have hbij : Bijective F := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hi x.2 y.2 (congrArg Subtype.val hxy))
    · intro y
      have hy : (y : ℂ) ∈ φ '' closedBall 0 1 := by rw [hclosure]; exact y.2
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hcont : Continuous F :=
    (hc.comp_continuous continuous_subtype_val (fun z => z.2)).subtype_mk _
  let : CompactSpace (closedBall (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  let e : closedBall (0 : ℂ) 1 ≃ₜ closure (connectedComponentIn Γᶜ p) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hbij) hcont
  refine ⟨e, hzero, ?_, ?_⟩
  · refine Eq.trans ?_ hsphere
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, sphere_subset_closedBall hz⟩, hz, rfl⟩
  · refine Eq.trans ?_ hball
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, ball_subset_closedBall hz⟩, hz, rfl⟩

end MatedCRTHarmonic.Planar.Schoenflies
