/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.VagueUniqueOn at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures

/-!
# Uniqueness of vague limits on an open subset of `ℂ`

Two vague limits (in the sense of `IsVagueLimitOn U`) of the same sequence agree. Proof: pull
both limits back to the subtype `↥U` (locally compact, second countable), where they are finite
on compacts hence regular, and apply `Measure.ext_of_integral_eq_on_compactlySupported`,
extending test functions on `↥U` by zero.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped CompactlySupported

namespace QuantumZipper

theorem isVagueLimitOn_unique {U : Set ℂ} (hU : IsOpen U) {μs : ℕ → Measure ℂ}
    {μ μ' : Measure ℂ} (h : IsVagueLimitOn U μs μ) (h' : IsVagueLimitOn U μs μ') :
    μ = μ' := by
  obtain ⟨h0, hK, ht⟩ := h
  obtain ⟨h0', hK', ht'⟩ := h'
  have hUm : MeasurableSet U := hU.measurableSet
  have hr : μ.restrict U = μ := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact h0)
  have hr' : μ'.restrict U = μ' := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact h0')
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  let ν : Measure U := Measure.comap Subtype.val μ
  let ν' : Measure U := Measure.comap Subtype.val μ'
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hKc => by
    rw [comap_subtype_coe_apply hUm]
    exact hK _ (hKc.image continuous_subtype_val) (Subtype.coe_image_subset _ _)⟩
  have : IsFiniteMeasureOnCompacts ν' := ⟨fun K hKc => by
    rw [comap_subtype_coe_apply hUm]
    exact hK' _ (hKc.image continuous_subtype_val) (Subtype.coe_image_subset _ _)⟩
  have hνν' : ν = ν' := by
    refine Measure.ext_of_integral_eq_on_compactlySupported fun g => ?_
    set G : ℂ → ℝ := Subtype.val.extend g 0
    have hGc : Continuous G := HasCompactSupport.continuous_extend_zero hU
      (map_continuous g) g.hasCompactSupport
    have hGs : HasCompactSupport G := g.hasCompactSupport.extend_zero continuous_subtype_val
    have hGU : tsupport G ⊆ U :=
      (g.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val).trans
        (Subtype.coe_image_subset _ _)
    have key : ∀ m : Measure ℂ, ∫ z, G z ∂(m.restrict U) = ∫ x, g x ∂(Measure.comap Subtype.val m) := by
      intro m
      rw [← integral_subtype_comap hUm]
      simp_rw [G, Subtype.val_injective.extend_apply]
    have e1 := key μ
    have e2 := key μ'
    rw [hr] at e1
    rw [hr'] at e2
    rw [← e1, ← e2]
    exact tendsto_nhds_unique (ht G hGc hGs hGU) (ht' G hGc hGs hGU)
  rw [← hr, ← hr', ← map_comap_subtype_coe hUm, ← map_comap_subtype_coe hUm]
  exact congrArg (Measure.map Subtype.val) hνν'

/-- `qAreaMeasure` is any vague limit of `areaApprox` on `H`, when one exists. -/
theorem qAreaMeasure_eq {γ : ℝ} {x : FieldSample} {μ : Measure ℂ}
    (hμ : IsVagueLimitOn H (areaApprox γ x) μ) : qAreaMeasure γ x = μ := by
  have hex : ∃ μ', IsVagueLimitOn H (areaApprox γ x) μ' := ⟨μ, hμ⟩
  unfold qAreaMeasure
  rw [dif_pos hex]
  exact isVagueLimitOn_unique isOpen_H hex.choose_spec hμ

end QuantumZipper
