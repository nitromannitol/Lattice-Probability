/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5InputsW1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3Wire3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54J1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61P4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B11A
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcL5
import LatticeProb.Bonanno.LQGMetric.Dimension.ChiUnique

/-!
# `DG.DZZInputsDG` from the remaining DZZ leaves (task P2-CONFW)

Ding–Zeitouni–Zhang, *Heat kernel for Liouville Brownian motion and Liouville graph distance*
(arXiv:1807.00422, `LBM_LGDarXiv.tex`, DZZ l.). The conjuncts of `DZZInputsDG`:
* L5.3 upper half at `χ = chiDZZ γ`: `dzzLem53Exp_dzzMuIn_of_event_only` (S5L53B11A) gives
  `DZZLem53Exp P μIn χ` for some `χ`, from **`DZZLem53Event`** at the walled tilde boxes (open);
  `χ = chiDZZ γ` is **`DZZChiIdent`** (open, below);
* L6.1 lower half at `α = 5/8`: `dzzLem61Lower_dzzMuIn_five_eighths` (S6L61P4) from L5.4
  (`dzzLem54Exp_dzzMuIn_of_walls`, S5L54J1), L5.3 and the walled P3.17 at the fixed tilde box;
* P3.17 at `μIn`: `dzzProp317_dzzMuIn` (S3ConcL5), for `ξ < dzzCMc γ`;
* P3.17 at the walls `dgWalls`: **`DZZProp317Walls`** for small `ξ` (open).

## The exponent identification
`chiDZZ γ` (Statement/Dimension.lean) is the exponent of DZZ Thm 1.1 in a.s. limit form
(`IsLGDExponent γ χ`: a.s. `log D_{γ,δ}(u,v) / log δ⁻¹ → χ` for the zero-boundary GFF on the
open unit square, all fixed `u ≠ v` inside, via QZ's `qAreaMeasureOn`), chosen among the positive
ones. The `χ` of `DZZLem53Exp` is a limit of *expectations* of the *walled* distance at the
white-noise measure `μIn`. These are different limits, so they are not identified by uniqueness of
limits alone: DZZ identify them in Prop 5.1 (`prop-existence-exponent`, l. 2254–2258: "the χ(γ)
here is the same as that in Lemma 5.3"), Prop 3.17 (concentration) and Thm 1.1 (l. 126–133,
"amalgamation", l. 135–139), with `χ > 0` from Lemma `lem-obvious-bounds`. The leaf
`DZZChiIdent` states exactly that: the L5.3 exponent at `μIn` is positive and is a DZZ Thm 1.1
exponent. `chiDZZ_eq_of_ident` then gives `χ = chiDZZ γ` by `isLGDExponent_unique`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace LQGMetric
namespace DZZInW

open DZZ WhiteNoise

/-- **The exponent identification** (DZZ Prop 5.1, l. 2254–2258, with Thm 1.1, l. 126–133, and
`lem-obvious-bounds`): the exponent of DZZ Lemma 5.3 at `μIn` is positive and is the a.s.
exponent of DZZ Theorem 1.1 (`IsLGDExponent`). -/
def DZZChiIdent : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ χ : ℝ, DZZLem53Exp P (dzzMuIn γ W) χ →
      0 < χ ∧ IsLGDExponent γ χ

/-- the walled DZZ Proposition 3.17 at the walls of the DG chain, for small `ξ`, for every white
noise (DZZ Remark 5.2, DEC-123 §2) -/
def DZZProp317WallsAll : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ ξ₂ : ℝ, 0 < ξ₂ ∧ ∀ ξ, 0 < ξ → ξ < ξ₂ → DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls

/-- a positive DZZ Thm 1.1 exponent is `chiDZZ γ` -/
theorem chiDZZ_eq_of_ident {γ χ : ℝ} (hχ : 0 < χ) (h : IsLGDExponent γ χ) : chiDZZ γ = χ := by
  have hex : ∃ χ : ℝ, 0 < χ ∧ IsLGDExponent γ χ := ⟨χ, hχ, h⟩
  unfold chiDZZ
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact isLGDExponent_unique hex.choose_spec.2 h

end DZZInW
end LQGMetric
