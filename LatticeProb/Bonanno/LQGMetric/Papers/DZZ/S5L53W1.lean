/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53W1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53P2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53L7
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53H5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5InputsW1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5ChiD1

/-!
# DZZ Lemma 5.3 part 1 as an expectation leaf, and the wiring of `hbadB` (P2-DZZ53W, D131 P-131W)

Ding–Zeitouni–Zhang, arXiv:1807.00422 (`LBM_LGDarXiv.tex`, DZZ l.), Lemma 5.3, proof l. 2361–2548.

The proved route to `DG.DZZInputsDG` (Papers/DZZ/S5InputsW1.lean, `DZZInW.dzzInputsDG_of_leaves`)
only uses the event leaf `DZZInW.DZZLem53EventAll` through `dzzLem53Exp_dzzMuIn_of_event_only`,
i.e. to obtain `∃ χ, DZZLem53Exp P (dzzMuIn γ W) χ` (audit 2026-10-03-L, item L6). The D131 route
(DEC-131 §2) reaches `∃ χ, DZZLem53Exp` directly by `dzzLem53Exp_dzzMuIn_of_hd_hbadB` (S5L53P2),
not through `DZZLem53Event`. So:

* **`DZZLem53ExpAll`**: the replacement leaf (`∃ χ, DZZLem53Exp` for every white noise and
  `γ ∈ (0,2)`); `dzzLem53ExpAll_of_eventAll` shows it is implied by the old leaf.
* **`dzzInputsDG_of_exp`**: copy of `dzzInputsDG_of_leaves` with the proved walls
  (`dzzProp317WallsAll_holds`, S5WallSim6E) and exponent identification (`dzzChiIdent_holds`,
  S5ChiD1).
* **`L53HbadB`**, `L53HbadBAll`, **`dzzLem53ExpAll_of_hbadB`**: the leaf from `hbadB`
  (DEC-131 §2, at every `α* > 0`), the refinement `L53RefineB` (P-131A) being `l53RefineB_of_pos`
  (S5L53L7).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- **DZZ Lemma 5.3 part 1 at `μIn`, expectation form, for every white noise**: the limit
`χ = lim log E[D_{δ}(u,v)] / log δ⁻¹`-statement `DZZLem53Exp` of DZZ L5.3 (l. 2340–2355) holds
for some `χ`. -/
def DZZLem53ExpAll : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ χ, DZZLem53Exp P (dzzMuIn γ W) χ

/-- **`DG.DZZInputsDG` from the expectation leaf** (copy of `DZZInW.dzzInputsDG_of_leaves`,
S5InputsW1, with the proved walls and exponent identification). -/
theorem dzzInputsDG_of_exp (hexp : DZZLem53ExpAll) : DG.DZZInputsDG := by
  intro Ω _ P W hW γ hγ hγ2
  obtain ⟨χ, hL53⟩ := hexp P W hW γ hγ hγ2
  obtain ⟨hχ, hLGD⟩ := dzzChiIdent_holds P W hW γ hγ hγ2 χ hL53
  have hχe : chiDZZ γ = χ := DZZInW.chiDZZ_eq_of_ident hχ hLGD
  obtain ⟨ξ₂, hξ₂, hw⟩ := dzzProp317WallsAll_holds P W hW γ hγ hγ2
  set ξ := min (ξ₂ / 2) (1 / 80) with hξdef
  have hξ0 : 0 < ξ := lt_min (half_pos hξ₂) (by norm_num)
  have hξ1 : ξ ≤ 1 / 80 := min_le_right _ _
  have hξ2 : ξ < ξ₂ := (min_le_left _ _).trans_lt (half_lt_self hξ₂)
  have hW317 := hw ξ hξ0 hξ2
  have h54 : DZZLem54Exp P (dzzMuIn γ W) χ :=
    dzzLem54Exp_dzzMuIn_of_walls hW hγ hγ2 hξ0 hξ1 hL53 hW317
  have h61 : DZZLem61Lower P (dzzMuIn γ W) (5 / 8) χ :=
    dzzLem61Lower_dzzMuIn_five_eighths hW hγ hγ2 h54 hL53
      ⟨ξ, hξ0, hξ1, dzzProp317In_tildeBox_of_walls hW317 ringU₀_mem_dzzVbar ringV₀_mem_dzzVbar
        ringU₀_ne_ringV₀⟩
  rw [hχe]
  refine ⟨hL53.upper, h61, min ξ₂ (dzzCMc γ), lt_min hξ₂ (dzzCMc_pos γ),
    fun ξ' hξ' hξ'' => dzzProp317_dzzMuIn hW hγ hγ2 hξ' (hξ''.trans_le (min_le_right _ _)),
    fun ξ' hξ' hξ'' => hw ξ' hξ' (hξ''.trans_le (min_le_left _ _))⟩

/-- `E X_k` of DZZ l. 2361 at the walled tilde box of `(u, v)`. -/
abbrev l53EX {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ)
    (u v : ℂ) (k : ℕ) : ℝ :=
  ∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ k) {u} {v} ∂P

/-- **`hbadB`** (DEC-131 §2, in the form of `dzzLem53Exp_dzzMuIn_of_hd_hbadB`, S5L53P2) at `α*`:
for `u ≠ v` in `𝕍̄` and large `k`, all `1 ≤ l ≤ k`, the bad event `l53BadB` (S5L53P2: the box chain
`𝒞` of `𝓔*` exists and is not desirable) has probability `≤ e^{-L^{0.22}}`, `L = k log 2`. -/
def L53HbadB {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ) (γ αs : ℝ) :
    Prop :=
  ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
    P (l53BadB γ W αs (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω)) u v k l
      (Metric.cthickening (2 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ)
        (Metric.cthickening (8 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ) (l53Region u v)))
      (l53EX P γ W u v k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))
      (l53EX P γ W u v l + ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))
      (l53EX P γ W u v l + 2 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))) ≤
      ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ)))

/-- `hbadB` for every white noise, every `γ ∈ (0,2)` and every `α* > 0` (the event `l53BadB`
does not involve the good points of `u`, `v`: it is a bound on the box chain once it exists). -/
def L53HbadBAll : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ αs : ℝ, 0 < αs → L53HbadB P W γ αs

/-- **The expectation leaf from `hbadB`** (`dzzLem53Exp_dzzMuIn_of_hd_hbadB`, S5L53P2, which
discharges `hd` by `l53_hd_holds` and `hreg` by `l53_hregN`; the refinement `L53RefineB` is
`l53RefineB_of_pos`, S5L53L7). -/
theorem dzzLem53ExpAll_of_hbadB (h : L53HbadBAll) : DZZLem53ExpAll := by
  intro Ω _ P W hW γ hγ hγ2
  obtain ⟨αs, hαs, -, hfin⟩ := dzzLem53Exp_dzzMuIn_of_hd_hbadB hW hγ hγ2
  exact hfin (l53RefineB_of_pos hαs γ) (h P W hW γ hγ hγ2 αs hαs)

end DZZ
end LQGMetric
