/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_2Node at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_2
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
Lemma 3.2 (`lem-good-annulus-all`, T:1452–1456): for each `ν > 0` and `M > 0` there is
`C = C(ν, M) > 1` such that for each `𝕣 > 0`, with probability `1 − O_ε(ε^M)` as `ε → 0`,
uniformly in `𝕣`: every `z ∈ B_{𝕣ε^{-M}}(0)` lies in `B_{𝕣ε^{1+ν}/2}(w)` for some
`w ∈ B_{𝕣ε^{-M}}(0) ∩ (ε^{1+ν}𝕣/4)ℤ²` and `r ∈ [ε^{1+ν}𝕣, ε𝕣] ∩ {2^{-k}𝕣}_{k∈ℕ}` such that
`E_r(w; C)` occurs (`GoodCover` with `good w r := h ∈ annEvent ξ D c C r w`).

Its proof (T:1474–1481) is open: it needs the measurability step `E_r(z;C) ∈
σ((h − h_{3r}(z))|_{𝔸_{r/2,2r}(z)})` (see `handoff/P2-DFA0.md`). Here it is only stated; the
statement follows `handoff/P2-DFA0.md` with the conclusion phrased through `GoodCover`
(`L3_5.lean`). "`O_ε(ε^M)` uniformly in `𝕣`" is read as: there are `K` and `ε₀ > 0` with
`P[not F] ≤ K ε^M` for all `ε ∈ (0, ε₀)` and `𝕣 > 0`. The field is a whole-plane GFF (the event
does not change if a constant is added to `h`, so this covers normalized GFFs).
-/

noncomputable section

open MeasureTheory Set

namespace LQGMetric.DFGPS
open Blueprint

/-- **DFGPS Lemma 3.2** (`lem-good-annulus-all`, T:1452–1456): the event `F^ε_𝕣` that the good
annuli `E_r(w; C)` cover `B_{𝕣ε^{-M}}(0)` has probability `≥ 1 − K ε^M`, uniformly in `𝕣`. -/
def Lem3_2 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ ν M : ℝ, 0 < ν → 0 < M → ∃ C : ℝ, 1 < C ∧ ∃ K ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P → ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ ε ∈ Ioo (0 : ℝ) ε₀,
          P {ω | ¬ GoodCover (fun w r => h ω ∈ annEvent (xiGamma γ) D c C r w) ν M ε 𝕣} ≤
            ENNReal.ofReal (K * ε ^ M)

end LQGMetric.DFGPS
