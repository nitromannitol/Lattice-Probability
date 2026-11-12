/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L2_1C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_1B
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFResults

/-!
# CONF Lemma 2.1 for closed and filled metric balls at positive stopping times (task P2-CONF21)

Source: CONF = Gwynne–Miller, arXiv:1905.00381, `confluence-final.tex`, Lemma 2.1
(`lem-ball-local`, C:476–479) and proof C:481–490 (parts A and B). Statement form: the Blueprint
item `Blueprint.CONFLem2_1` (D32 determined form) with the extra hypothesis `τ > 0` a.s.:

* `confLem2_1_filled_of`, `confLem2_1_closed_of`: the two halves;
* `CONFLem2_1Pos` and **`confLem2_1Pos_of : DFGPSLem3_8 → CONFLem2_1Pos`**.

Why `τ > 0`: in the Lean definitions `𝓑^•_s = cl 𝓑_s = ∅` for `s ≤ 0`, while the limit of the
balls at the dyadic times `τ_n ↓ τ = 0` is `{z₀}`; on `{τ = 0}` (an event of the germ
`⋂_{t>0} 𝓕_t`, not of `𝓕_0`) with `z₀ ∉ U`, `{𝓑_τ ⊆ U} = {τ ≤ 0}` is `σ(h|_U)`-determined only
through a Blumenthal-type 0-1 law for that germ, which CONF does not state or use (CONF's
`𝓑_0` is not defined; its limit argument C:483/490 gives the set `{z₀}` at `τ = 0`).
`DFGPSLem3_8` (bounded compactness of `D_h`, DFGPS Lemma 3.8) gives compact balls, needed by the
measurability and limit steps (CONF uses it implicitly).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.CONF
open GM LocalEvent

section Halves
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **CONF Lemma 2.1, filled balls** (C:478), for stopping times `τ > 0` a.s. -/
theorem confLem2_1_filled_of (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (z₀ : ℂ) (τ : Ω → ℝ) (hτ : IsFilledBallStoppingTime D h z₀ τ)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) :
    IsLocalSetDet P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) :=
  conf21_isLocalSetDet_gen hD hh (ae_mem_lenSet h38 hγ hγ2 hD P h hh)
    (fun d s => filledBall d z₀ s) (fun d hd s => gm_filledBall_isBounded_of_lenSet hd z₀ s)
    (fun d s => gm_filledBall_isClosed d z₀ s) (fun s V hV => conf21_hit_filled z₀ s V hV)
    (fun d₁ d₂ s U hU h1 h2 he hB => conf21_sat_filled d₁ d₂ z₀ s U hU h1 h2 he hB)
    (fun d _ _ hst => gm_filledBall_mono d z₀ hst)
    (fun _ hd _ ht _ hU hK => conf21_rc_filled hd z₀ ht hU hK) τ hτ hpos

end Halves

end LQGMetric.CONF
