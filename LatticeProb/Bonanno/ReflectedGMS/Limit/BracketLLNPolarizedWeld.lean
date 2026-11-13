/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.BracketLLNPolarizedWeld at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.BracketLLNRootChain

/-!
**⚠ VACUOUS/SUPERSEDED (2026-09-18):** `hQP` of
`canonicalBracket_bracket_limit_of_polarizedAnnealedData` is unsatisfiable when `Q` is the
annealed law mixing over a continuous environment law (the quenched law at one fixed `e` and
`Q.map π` are mutually singular), so the theorem is vacuous there.  It is sound, and used, at a
FIBRE law: `BracketLLNDisintegratedWeld.ae_forall_bracket_limit_of_regenerativeInvariance_disintegrated`
applies it at `Q := κ e`, where the reading-off is checked satisfiable
(`BracketLLNDisintegratedWeld.readOff_prod_fst_areaSampleLaw`).  Use it only through that weld.

# The polarized weld: three directional root-block limits give the bracket limit

`Limit/TwoSidedBracketDensity.canonicalBracket_bracket_limit_of_annealedRootBlockData` takes the
limiting covariance `Σ` as **given** and asks for `HasRootBlockData … (dirForm Σ ζ)` in the three
polarization directions.  The producers on the other side —
`Temporal/GridAveragedInvariantVersion.ae_hasRootBlockData_of_regenerativeInvariance` and its
manuscript-hypothesis refinement
`Limit/ScaledRootChainSystem.ae_hasRootBlockData_of_regenerativeInvariance_scaled` — deliver
**one functional at a time**, with the limit the annealed mean `∫ F ∂P` of that functional.  So a
consumer holds three numbers `a`, `b`, `c` (the annealed means in the directions `(1,0)`, `(0,1)`,
`(1,1)`) and must produce a matrix whose three directional forms are exactly those numbers.

That matrix is the polarization, and this module supplies it together with the weld:

* `polarMatrix a b c` — the symmetric matrix with `Σ₀₀ = a`, `Σ₁₁ = b`, `Σ₀₁ = Σ₁₀ = (c-a-b)/2`;
* `dirForm_polarMatrix_one_zero`, `dirForm_polarMatrix_zero_one`, `dirForm_polarMatrix_one_one` —
  its three directional forms are `a`, `b`, `c`;
* `canonicalBracket_bracket_limit_of_polarizedAnnealedData` — **`p:lem:bracketlimit` for the
  actual quenched array from three separate annealed root-block statements**, with no constraint
  on `Σ` left for the caller to solve and no symmetry hypothesis.

This is the adapter that was missing between two checked but mutually unimported halves:
`Temporal/GridAveragedInvariantVersion` (zero importers except `Limit/ScaledRootChainSystem`) and
`Limit/TwoSidedBracketDensity` (zero importers).

## Why the polarization is forced, and why it costs nothing

The manuscript polarizes because off-diagonal *entries* of the bracket are not monotone in time,
so the transfer step of `p:prop:timeergodic` (which needs a nonnegative density) applies only to
the three directional forms.  `BracketTimeAverage.entry_eq_dirForm` is the inverse map for a
*given* symmetric matrix; `polarMatrix` is the same map read as a construction.  Positive
semidefiniteness of the result is **not** assumed: it comes out of
`canonicalBracket_bracket_limit_of_annealedRootBlockData` itself, from pointwise positive
semidefiniteness of `Γ` along the path.

## What is *not* proved here

The three annealed root-block statements, i.e. `p:lem:regeninvariant` (`RegenerativeInvariance`),
environment ergodicity, and a `RootChainSystem` / `ScaledRootChainSystem` for the actual annealed
two-sided rooted area-clock law; the reading-off clause `hfwd`; and the Fubini/disintegration
clause `hQP`.  Nothing here certifies `p:lem:timeconverge`, `p:lem:regeninvariant`,
`p:prop:timeergodic`, `p:lem:bracketlimit`, `p:thm:areaclt` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

open scoped NNReal ENNReal

namespace ReflectedGMS.BracketLLNPolarizedWeld

open ReflectedGMS.BracketTimeAverage ReflectedGMS.GridBlockTransfer
open ReflectedGMS.RootBlockGridProbability ReflectedGMS.BracketLLNRootChain
open ReflectedGMS.MartingaleIngredients ReflectedGMS.MartingaleLimit

/-! ### 1. The polarization matrix -/

/-- **The symmetric two-by-two matrix with prescribed directional forms.**  Its forms in the
directions `(1,0)`, `(0,1)` and `(1,1)` are `a`, `b` and `c`. -/
noncomputable def polarMatrix (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then (if i = 0 then a else b) else (c - a - b) / 2

theorem polarMatrix_apply (a b c : ℝ) (i j : Fin 2) :
    polarMatrix a b c i j =
      if i = j then (if i = 0 then a else b) else (c - a - b) / 2 := rfl

theorem polarMatrix_zero_zero (a b c : ℝ) : polarMatrix a b c 0 0 = a := by
  rw [polarMatrix_apply, if_pos rfl, if_pos rfl]

theorem polarMatrix_one_one (a b c : ℝ) : polarMatrix a b c 1 1 = b := by
  rw [polarMatrix_apply, if_pos rfl, if_neg (by decide : ¬((1 : Fin 2) = 0))]

theorem polarMatrix_zero_one (a b c : ℝ) : polarMatrix a b c 0 1 = (c - a - b) / 2 := by
  rw [polarMatrix_apply, if_neg (by decide : ¬((0 : Fin 2) = 1))]

theorem polarMatrix_one_zero (a b c : ℝ) : polarMatrix a b c 1 0 = (c - a - b) / 2 := by
  rw [polarMatrix_apply, if_neg (by decide : ¬((1 : Fin 2) = 0))]

/-- **The polarization matrix is symmetric**, so the `hSsymm` hypothesis of every consumer in
the bracket lane is discharged for it. -/
theorem polarMatrix_symm (a b c : ℝ) (i j : Fin 2) :
    polarMatrix a b c i j = polarMatrix a b c j i := by
  rcases eq_or_ne i j with rfl | hne
  · rfl
  · rw [polarMatrix_apply, polarMatrix_apply, if_neg hne, if_neg (Ne.symm hne)]

theorem dirForm_polarMatrix_one_zero (a b c : ℝ) :
    dirForm (polarMatrix a b c) (dirVec 1 0) = a := by
  rw [dirForm_dirVec_one_zero, polarMatrix_zero_zero]

theorem dirForm_polarMatrix_zero_one (a b c : ℝ) :
    dirForm (polarMatrix a b c) (dirVec 0 1) = b := by
  rw [dirForm_dirVec_zero_one, polarMatrix_one_one]

theorem dirForm_polarMatrix_one_one (a b c : ℝ) :
    dirForm (polarMatrix a b c) (dirVec 1 1) = c := by
  rw [dirForm_dirVec, polarMatrix_zero_zero, polarMatrix_zero_one, polarMatrix_one_zero,
    polarMatrix_one_one]
  ring

/-! ### 2. The weld -/

end ReflectedGMS.BracketLLNPolarizedWeld
