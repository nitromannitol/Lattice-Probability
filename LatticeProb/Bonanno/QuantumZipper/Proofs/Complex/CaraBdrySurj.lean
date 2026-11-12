/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.CaraBdrySurj at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraBdryFold
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# EXT-CA C7 and the Jordan case of C6: boundary surjectivity, homeomorphism onto the frontier

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 C6 (corollary), C7. Standing data as in
`CaraBdryFold.lean`: `CarHyp ψ D E R₀`, a continuous extension `F` of `ψ` to `Hbar`, and the
limit `wInf` of `ψ` at `∞`.

* **C7** `frontier_eq_insert_range`: `frontier D = {wInf} ∪ F(ℝ)` (compactness of
  `Hbar ∪ {∞}`, `closure_image_subset`, and C1). Pommerenke, *Boundary Behaviour of Conformal
  Maps* (1992), Thm 2.1 and the line "`f(𝔻̄) = Ḡ`, `f(𝕋) = ∂G`" used in the proofs of Prop. 2.5
  and Thm 2.6, printed pp. 20–24.
* `tendsto_extension_cocompact`: `F x → wInf` as `|x| → ∞` along `ℝ`.
* **C6, Jordan case** `isClosedEmbedding_bdryMap`: if `E \ {q}` is preconnected for every `q`,
  the boundary map `ℝ ∪ {∞} → ℂ` (`bdryMap F wInf`) is a closed embedding with range
  `frontier D`, i.e. a homeomorphism of `ℝ ∪ {∞}` onto `frontier D`. Pommerenke (1992), Thm 2.6,
  (iii) ⇒ (i), p. 24: continuous (Thm 2.1), each boundary point attained once (Prop. 2.5), and a
  continuous bijection from a compact space onto a Hausdorff space is a homeomorphism.
-/

noncomputable section

open Set Metric Filter Topology Complex
open scoped Real

namespace QuantumZipper.CA.Car

open QuantumZipper.CA.Topo

/-- **C7 (boundary surjectivity).** `frontier D = {wInf} ∪ F(ℝ)`. -/
theorem frontier_eq_insert_range {ψ F : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : CarHyp ψ D E R₀)
    (hEq : EqOn F ψ H) (hF : ContinuousOn F Hbar) {wInf : ℂ}
    (hInf : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 wInf)) :
    frontier D = insert wInf (range fun x : ℝ => F x) := by
  apply Subset.antisymm
  · intro p hp
    rw [h.isOpen.frontier_eq] at hp
    have hpc : p ∈ closure (ψ '' H) := by rw [h.bij.image_eq]; exact hp.1
    rcases closure_image_subset hEq hF hInf subset_rfl hpc with ⟨z, hz, rfl⟩ | hpw
    · rw [closure_H_eq_Hbar] at hz
      rcases (show (0 : ℝ) ≤ z.im from hz).eq_or_lt with h0 | hpos
      · right
        refine ⟨z.re, show F (z.re : ℂ) = F z from ?_⟩
        congr 1
        exact Complex.ext (by simp) (by simp [h0])
      · exact absurd (by rw [hEq hpos]; exact h.bij.mapsTo hpos) hp.2
    · left; exact hpw
  · rintro p (rfl | ⟨x, rfl⟩)
    · exact limit_infty_mem_frontier h hInf
    · exact extension_mem_frontier h hEq hF x

/-- Boundary values along `ℝ` tend to `wInf` at `±∞`. -/
theorem tendsto_extension_cocompact {ψ F : ℂ → ℂ} (hEq : EqOn F ψ H) (hF : ContinuousOn F Hbar)
    {wInf : ℂ} (hInf : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 wInf)) :
    Tendsto (fun x : ℝ => F x) (cocompact ℝ) (𝓝 wInf) := by
  refine (nhds_basis_closedBall.tendsto_right_iff).2 fun ε hε => ?_
  have hmem := hInf (closedBall_mem_nhds wInf hε)
  rw [mem_map, mem_inf_principal] at hmem
  set S : Set ℂ := {z | z ∈ H → z ∈ ψ ⁻¹' closedBall wInf ε} with hS
  have hSb : Bornology.IsBounded Sᶜ := Bornology.isBounded_def.2 (by rwa [compl_compl])
  obtain ⟨R, hR⟩ := hSb.subset_closedBall 0
  have hcoc : {x : ℝ | R < |x|} ∈ cocompact ℝ := by
    refine mem_cocompact.2 ⟨closedBall 0 R, isCompact_closedBall 0 R, fun x hx => ?_⟩
    simpa [mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] using hx
  refine mem_of_superset hcoc fun x (hx : R < |x|) => ?_
  have hxo : (x : ℂ) ∈ {z : ℂ | R < ‖z‖} := by
    show R < ‖(x : ℂ)‖
    rwa [norm_real, Real.norm_eq_abs]
  have hcl := mem_closure_image_of_mem_nhdsWithin hEq hF (ofReal_mem_Hbar x)
    (inter_mem_nhdsWithin H ((isOpen_lt continuous_const continuous_norm).mem_nhds hxo))
  refine closure_minimal ?_ isClosed_closedBall hcl
  rintro _ ⟨z, ⟨hzH, hzR⟩, rfl⟩
  have hzS : z ∈ S := by
    by_contra hzS
    have := hR hzS
    rw [mem_closedBall, dist_zero_right] at this
    exact not_le.2 hzR this
  exact hzS hzH

/-- The boundary map on `ℝ ∪ {∞}`: `F` on `ℝ`, `wInf` at `∞`. -/
def bdryMap (F : ℂ → ℂ) (wInf : ℂ) : OnePoint ℝ → ℂ := fun o =>
  OnePoint.elim o wInf fun x => F x

theorem continuous_bdryMap {ψ F : ℂ → ℂ} (hEq : EqOn F ψ H) (hF : ContinuousOn F Hbar)
    {wInf : ℂ} (hInf : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 wInf)) :
    Continuous (bdryMap F wInf) := by
  refine (OnePoint.continuous_iff _).2 ⟨?_, ?_⟩
  · rw [coclosedCompact_eq_cocompact]
    exact tendsto_extension_cocompact hEq hF hInf
  · exact hF.comp_continuous continuous_ofReal fun x => ofReal_mem_Hbar x

theorem range_bdryMap (F : ℂ → ℂ) (wInf : ℂ) :
    range (bdryMap F wInf) = insert wInf (range fun x : ℝ => F x) := by
  ext p
  constructor
  · rintro ⟨o, rfl⟩
    induction o using OnePoint.rec with
    | infty => exact Or.inl rfl
    | coe x => exact Or.inr ⟨x, rfl⟩
  · rintro (rfl | ⟨x, rfl⟩)
    · exact ⟨OnePoint.infty, rfl⟩
    · exact ⟨(x : OnePoint ℝ), rfl⟩

/-- **C6, Jordan case.** If `E \ {q}` is preconnected for every `q`, the boundary map
`ℝ ∪ {∞} → ℂ` is a closed embedding onto `frontier D`, i.e. a homeomorphism of `ℝ ∪ {∞}` onto
`frontier D`. -/
theorem isClosedEmbedding_bdryMap {ψ F : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : CarHyp ψ D E R₀)
    (hEq : EqOn F ψ H) (hF : ContinuousOn F Hbar) {wInf : ℂ}
    (hInf : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 wInf))
    (hE : ∀ q, IsPreconnected (E \ {q})) :
    Topology.IsClosedEmbedding (bdryMap F wInf) ∧ range (bdryMap F wInf) = frontier D := by
  have C6 := fun q => eq_of_isPreconnected_diff h hEq hF hInf (hE q)
  refine ⟨(continuous_bdryMap hEq hF hInf).isClosedEmbedding fun a b hab => ?_, ?_⟩
  · induction a using OnePoint.rec with
    | infty =>
      induction b using OnePoint.rec with
      | infty => rfl
      | coe y => exact ((C6 wInf).2 rfl y hab.symm).elim
    | coe x =>
      induction b using OnePoint.rec with
      | infty => exact ((C6 wInf).2 rfl x hab).elim
      | coe y => exact congrArg _ ((C6 (F x)).1 x y rfl hab.symm)
  · rw [range_bdryMap, frontier_eq_insert_range h hEq hF hInf]

end QuantumZipper.CA.Car
