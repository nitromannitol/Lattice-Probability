/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Zipper.Welding at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Loewner.Reverse
import LatticeProb.Bonanno.QuantumZipper.Loewner.Curves
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures

/-!
# Conformal welding and the welding-determined reverse flow

`FOUNDATIONS.md` §7, `THEOREM_STATEMENTS_ENGLISH.md` Theorem 1.4 and Corollary 1.5.

* `weldHomR γ x` is the paper's `R_h : (−∞,0] → [0,∞)`, `ν_h([s,0]) = ν_h([0,R_h(s)])`.
* `revMapInv W t` inverts the reverse flow map `revMap W t : ℍ → ℍ \ K_t`.
* `IsWeldingDriver γ x t W'` says that the reverse flow driven by `W'` up to capacity time `t`
  zips up a simple curve whose welding homeomorphism is `R_h` on `[0₋,0]`.
* `weldDriver γ x t` is a driving function chosen by choice among those; it is unique (on
  `[0,t]`) by Theorem 1.4 in the paper's setting. It drives the reverse flow `f^h_t` of
  Corollary 1.5.
-/

open MeasureTheory

namespace QuantumZipper

/-- The paper's welding function `R_h` (Theorem 1.4): for `s ≤ 0`, `weldHomR γ x s` is the
smallest `r ≥ 0` with `ν_h([s,0]) ≤ ν_h([0,r])`, where `ν_h = qBoundaryMeasure γ x`. When
`ν_h` is atom-free and charges every interval (a.s. the case), this is the unique `r ≥ 0` with
`ν_h([s,0]) = ν_h([0,r])`. Same as `weldR` in `Statements/Thm14.lean`. -/
noncomputable def weldHomR (γ : ℝ) (x : FieldSample) (s : ℝ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧
    qBoundaryMeasure γ x (Set.Icc s 0) ≤ qBoundaryMeasure γ x (Set.Icc 0 r)}

open Classical in
/-- Inverse of the reverse flow map `revMap W t : ℍ → ℍ \ revHull W t`: the unique `z ∈ ℍ`
with `revMap W t z = w` if there is exactly one, else the junk value `0`. On `ℍ \ K_t` it is
`(f_t)⁻¹`, which (see `Zipper/Maps.lean`) is the centered forward map of the curve `K_t`. -/
noncomputable def revMapInv (W : ℝ → ℝ) (t : ℝ) (w : ℂ) : ℂ :=
  if h : ∃! z, z ∈ H ∧ revMap W t z = w then h.choose else 0

/-- `W'` is a driving function of the reverse flow determined by the welding `R_h` up to
capacity time `t` (Theorem 1.4 / Corollary 1.5): `W'` is continuous with `W' 0 = 0`, the
reverse hull at time `t` is the hull of a simple curve (or `t = 0`, where the hull is empty and
nothing is zipped), and the induced welding homeomorphism `[0₋,0] → [0,0₊]` agrees with
`R_h = weldHomR γ x`. Only the values of `W'` on `[0,t]` matter.

Design note: the disjunct `t = 0` is added to the specification `IsSimpleCurveHull (revHull W'
t)` because the empty hull at `t = 0` is not a simple-curve hull, which would make the
predicate unsatisfiable at `t = 0` and `zipCap γ 0` junk. -/
def IsWeldingDriver (γ : ℝ) (x : FieldSample) (t : ℝ) (W' : ℝ → ℝ) : Prop :=
  Continuous W' ∧ W' 0 = 0 ∧ (t = 0 ∨ IsSimpleCurveHull (revHull W' t)) ∧
    ∀ s ∈ Set.Icc (zeroMinus W' t) 0, weldingHom W' t s = weldHomR γ x s

/-- The driving function of the reverse Loewner flow `f^h_t` determined by `R_h` (Corollary
1.5), chosen by `Classical.epsilon` among the `IsWeldingDriver γ x t` functions (junk if there
is none). In the paper's setting it exists (Theorem 1.3) and is unique on `[0,t]` (Theorem
1.4); in law it is `√κ` times a Brownian motion, i.e. `f^h_t` is a reverse SLE_κ flow. -/
noncomputable def weldDriver (γ : ℝ) (x : FieldSample) (t : ℝ) : ℝ → ℝ :=
  Classical.epsilon (IsWeldingDriver γ x t)

theorem weldDriver_spec {γ : ℝ} {x : FieldSample} {t : ℝ}
    (h : ∃ W', IsWeldingDriver γ x t W') : IsWeldingDriver γ x t (weldDriver γ x t) :=
  Classical.epsilon_spec h

end QuantumZipper
