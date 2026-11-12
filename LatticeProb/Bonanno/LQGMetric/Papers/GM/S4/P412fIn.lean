/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412fIn at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412Step12
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL422F
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2L419B
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412bScale

/-!
# GM Prop 4.12: the times and regions on `ℰ_𝕣` for the deterministic core

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, L4.15 Step 3 (l. 2160:
"By an argument as in (4.39) … `B_{16ε^κ𝕣}(𝓑^•_{t_k}) ⊆ 𝓑^•_{s_{k+1}}`") and the proof of
Prop 4.12 (l. 2233–2247: `𝓑^•_{t_k} ⊆ B_{2ℓ𝕣}(𝕫)`, `t_k ≤ s_{k+1} ≤ τ_{3ℓ𝕣} ≤ τ_{|𝕫−𝕨|}`).

`p412f_times`: on `ℰ_𝕣`, for small `ε` and `k ≤ K`, with `S = 𝔠_𝕣e^{ξh_𝕣(0)}`,
`t = t_k`, `s' = s_{k+1}`:
`t + (17ε^κ)^χ S < s'`, `t + S(ε^κ/2)^{χ'} < s'`, `𝓑^•_t ⊆ B_{2ℓ𝕣}(𝕫)`,
`𝓑^•_{s'} ⊆ B_{3ℓ𝕣}(𝕫)`, `0 < t`, `s' ≤ τ_{2ℓ𝕣}`. Proof as in `p412_eq439` (GM (4.39)):
the gap `s' − t = τ_{ℓ𝕣}(ε^β − ε^{2β})` with `τ_{ℓ𝕣} ≥ (a/2)^{χ'}S` beats `C ε^{κχ/2} S`
because `β < κχ/2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- `(k+1)ε^β ≤ a/c₂` for `k ≤ K` once `ε^β ≤ a/c₂` (as in `p412_eq439`) -/
theorem p412f_succ_le {R : RegPar} {a ε β : ℝ} (hε0 : 0 < ε) (hc2 : 0 < regC2const R a)
    (ha0 : 0 < a) (hεβ : ε ^ β ≤ a / regC2const R a) {k : ℕ} (hk : k ≤ p4K R a ε β) :
    ((k + 1 : ℕ) : ℝ) * ε ^ β ≤ a / regC2const R a := by
  have hεβ0 : 0 ≤ ε ^ β := (Real.rpow_pos_of_pos hε0 _).le
  have hx1 : 1 ≤ a / regC2const R a * ε ^ (-β) := by
    rw [Real.rpow_neg hε0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hε0 _)]
    linarith
  have hk1 : ((k + 1 : ℕ) : ℝ) ≤ a / regC2const R a * ε ^ (-β) := by
    have h1 : k + 1 ≤ ⌊a / regC2const R a * ε ^ (-β)⌋₊ := by
      have := Nat.one_le_floor_iff _ |>.2 hx1
      unfold p4K at hk; omega
    exact (Nat.cast_le.2 h1).trans (Nat.floor_le (by positivity))
  calc ((k + 1 : ℕ) : ℝ) * ε ^ β ≤ a / regC2const R a * ε ^ (-β) * ε ^ β :=
        mul_le_mul_of_nonneg_right hk1 hεβ0
    _ = a / regC2const R a := by
        rw [Real.rpow_neg hε0.le, mul_assoc, inv_mul_cancel₀ (Real.rpow_pos_of_pos hε0 _).ne',
          mul_one]

end LQGMetric.GM
