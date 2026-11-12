/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L45Det5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det4

/-!
# GM Lemma 4.5: `GMArcFamDet` from a countable code of local events (task P2-E2R)

`GMArcFamDet` (GM l. 1654) asks for a `σ(𝓑^•_{t_k}, h|) ⊗ Borel`-measurable version of the arc
hit relation `(ω, x) ↦ {arcOf x ∩ U ≠ ∅}`, jointly in the point `x`. A σ-algebra of the form
`⨅ₙ Gₙ` does not commute with `⊗ Borel` in general, so joint measurability is obtained through a
countable code: if the relation is, for all `x` and a.s., read off countably many field events
`{h ∈ Bᵢ}` invariant under the locality data `GMLocData` (each a.s. a
`σ(𝓑^•_{t_k}, h|)`-event by `gm_aeEventIn_Kt`) and `x` through a Borel set `T`, then
`GMArcFamDet` holds (`gm_arcFamDet_of_code`). The remaining input `GMArcCode` is deterministic
(saturation, by `GMLocData.arcOf_eq` for events built from the arcs) plus descriptive set theory
(null-measurability of the `Bᵢ`, Borel-ness of `T`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **`0 < s_k < t_k` surely** (GM (4.6); `ℓ𝕣 > 0`, `ε > 0`), from `τ_{ℓ𝕣} > 0` -/
theorem gm_s4_pos_lt {Ω : Type} [MeasurableSpace Ω] (D : DistC → ContMetric) (h : Ω → DistC)
    (𝕫 : ℂ) {ℓ 𝕣 ε : ℝ} (β : ℝ) (k : ℕ) (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (ω : Ω) :
    0 < s4S D h 𝕫 ℓ 𝕣 ε β k ω ∧ s4S D h 𝕫 ℓ 𝕣 ε β k ω < s4T D h 𝕫 ℓ 𝕣 ε β k ω := by
  have hτ : 0 < s4Unit D h 𝕫 ℓ 𝕣 ω := gm_tauD_pos (D (h ω)) 𝕫 hℓ𝕣
  have h1 : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
  have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨mul_pos hτ (by nlinarith), ?_⟩
  unfold s4T
  nlinarith [mul_pos h2 hτ]

end LQGMetric.GM
