/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm11.FrozenLocalDynkin at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Dynkin
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.OptionalStopping
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Local Dynkin formula with stopping (tool for MF-1, MF-2)

Blueprint `blueprint/THM11_BLUEPRINT.md`, §6 (MF-1, MF-2). The IL-3 Dynkin formula
(`Dynkin.dynkin_additive`) needs a globally `C³` test function with bounded derivatives. The
frozen fields are smooth only on an open set `O` (e.g. `{Im z > c}`), and are bounded only on
the region `K` visited before freezing. This file localizes Dynkin's formula:

* `FrozenMart.martingale_localDynkin_stopped`: if `F` is `C³` on an open `O`, the generator
  `dynkinGen b e F` vanishes on `K \ Cl` (with `K ⊆ O` closed), `F` is bounded on `K`, and the
  solution `U` stays in `K` up to (and including) its hitting time `τ` of the closed set `Cl`
  (capped at `T`), then `t ↦ F (U_{t ∧ τ})` is a martingale.

Proof: multiply `F` by smooth cutoffs `f_R` equal to `1` near `K ∩ closedBall 0 R` and supported
in `O` (smooth Urysohn), apply `dynkin_additive`, freeze at `T`, stop at the hitting time of
`Cl ∪ {‖x‖ ≥ R}` (IL-4), and let `R → ∞` by dominated convergence (the stopped values are
bounded by the bound of `F` on `K`, uniformly in `R`).

Also: `fderiv_apply_eq_deriv_line` and `iteratedFDeriv_two_eq_deriv_deriv_line`, which reduce
the generator to one-variable derivatives along lines.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace QuantumZipper
namespace FrozenMart

/-! ### Derivatives along lines -/

section Lines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Lines

/-! ### Smooth cutoffs -/

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth `[0,1]`-valued cutoff with compact support inside the open set `O`, equal to `1`
near the compact set `S ⊆ O`. -/
theorem exists_cutoff_of_isCompact {S O : Set E} (hS : IsCompact S) (hO : IsOpen O)
    (hSO : S ⊆ O) :
    ∃ f : E → ℝ, ContDiff ℝ 3 f ∧ (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport f ∧
      tsupport f ⊆ O ∧ ∀ x ∈ S, f =ᶠ[𝓝 x] 1 := by
  obtain ⟨η, hη, hηO⟩ := hS.exists_cthickening_subset_open hO hSO
  obtain ⟨f, hfd, hfr, hfs, hf1⟩ := exists_contDiff_support_eq_eq_one_iff (n := 3)
    (isOpen_thickening (δ := η) (E := S)) (isClosed_cthickening (δ := η / 2) (E := S))
    (cthickening_subset_thickening' hη (by linarith) S)
  have hts : tsupport f ⊆ cthickening η S := by
    rw [tsupport, hfs]; exact closure_thickening_subset_cthickening η S
  refine ⟨f, by exact_mod_cast hfd, fun x => hfr (mem_range_self x), ?_, hts.trans hηO, ?_⟩
  · exact (hS.cthickening (r := η)).of_isClosed_subset (isClosed_tsupport f) hts
  · intro x hx
    have hmem : thickening (η / 2) S ∈ 𝓝 x :=
      isOpen_thickening.mem_nhds (self_subset_thickening (by linarith) S hx)
    filter_upwards [hmem] with y hy
    exact (hf1 y).1 (thickening_subset_cthickening _ _ hy)

end Cutoff

/-! ### Local Dynkin formula with stopping -/

section LocalDynkin

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end LocalDynkin

end FrozenMart
end QuantumZipper
