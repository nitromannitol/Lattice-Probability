/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorFiber at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree
import Mathlib.Topology.Separation.Hausdorff

 






set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Topology
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 


theorem laneC_exists_fiber_lift_disagreement
    {ρ : ℝ → ℂ} {a b : ℝ} (hρ : ContinuousOn ρ (Icc a b))
    {g : ℂ → ℂ} {L : ℝ → ℂ}
    (hL : ContinuousOn L (Icc a b))
    (hexp : ∀ t ∈ Icc a b, Complex.exp (L t) = g (ρ t))
    (hnolog : ¬ QuantumZipper.CA.Topo.HasLogOn g (ρ '' Icc a b)) :
    ∃ s ∈ Icc a b, ∃ t ∈ Icc a b,
      ρ s = ρ t ∧ L s ≠ L t := by
  classical
  by_contra hnone
  have hfiber : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      ρ s = ρ t → L s = L t := by
    intro s hs t ht heq
    by_contra hne
    exact hnone ⟨s, hs, t, ht, heq, hne⟩
  let I : Set ℝ := Icc a b
  let X : Set ℂ := ρ '' I
  let f : I → X := fun t => ⟨ρ t, ⟨t.1, t.2, rfl⟩⟩
  have hfcont : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact hρ.comp_continuous continuous_subtype_val (fun t => t.2)
  have hfsurj : Function.Surjective f := by
    rintro ⟨z, ⟨t, ht, rfl⟩⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  let F : C(I, X) := ⟨f, hfcont⟩
  let G : C(I, ℂ) := ⟨fun t => L t, hL.comp_continuous continuous_subtype_val
    (fun t => t.2)⟩
  have hfactor : Function.FactorsThrough G F := by
    intro s t heq
    exact hfiber s s.2 t t.2 (congrArg Subtype.val heq)
  let hq : IsQuotientMap F :=
    IsQuotientMap.of_surjective_continuous hfsurj hfcont
  let H : C(X, ℂ) := hq.lift G hfactor
  let L' : ℂ → ℂ := fun z => if hz : z ∈ X then H ⟨z, hz⟩ else 0
  have hLc : ContinuousOn L' X := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : X.domRestrict L' = fun z : X => H z := by
      funext z
      exact dif_pos z.2
    rw [heq]
    exact H.continuous
  apply hnolog
  refine ⟨L', hLc, ?_⟩
  intro z hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hcomp : H (F ⟨t, ht⟩) = G ⟨t, ht⟩ := by
    have h := congrArg (fun F : C(I, ℂ) => F ⟨t, ht⟩) (hq.lift_comp G hfactor)
    simpa only [ContinuousMap.comp_apply] using h
  change Complex.exp (L' (ρ t)) = g (ρ t)
  rw [show L' (ρ t) = H (F ⟨t, ht⟩) by
    dsimp [L', F, f, X]
    rw [dif_pos (mem_image_of_mem ρ ht)]]
  rw [hcomp]
  exact hexp t ht

end SupercriticalLQGUniqueness.B2.DG20Conc
