/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.ManyGood at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanPunct
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupStop
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupStab

/-!
# GM.S4.7: a geodesic from the centre crosses `∂𝓑^•_t` once and never re-enters `𝓑^•_t`

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, used at l. 2207 ("A `D_h`-geodesic
started from `𝕫` can hit `∂𝓑^•_{t_k}` at most once"), l. 2241 ("`P` does not re-enter
`𝓑^•_{s_{k+1}}` after time `s_{k+1}`") and l. 2575 (proof of Lemma 4.16). GM_B: GM.S4.7.
GM give no proof (deterministic, elementary); own elementary proof, following the argument of
`gm_geod_mem_frontier` (S-geod-level): after time `t` the geodesic stays at distance `> t`, so in
the component of `ℂ ∖ cl 𝓑_t` of its endpoint, which is unbounded.

* `gm_S4_7_mem_iff` — for a unit-speed geodesic `P : [0,L] → ℂ` from `𝕫` to `w ∉ 𝓑^•_t`
  (`t > 0`): `P(u) ∈ 𝓑^•_t ⟺ u ≤ t`.
* `gm_S4_7_frontier` — `P(u) ∈ ∂𝓑^•_t ⟹ u = t` (hits `∂𝓑^•_t` at most once).
* The third clause of GM.S4.7 ("every point of `∂𝓑^•_s` is at distance `s`") is
  `jp_frontier_subset_sphere`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Topology Set
open LQGMetric.Blueprint

namespace LQGMetric.GM

variable {D : ContMetric} {𝕫 w : ℂ} {P : ℝ → ℂ} {L t : ℝ}

/-- after time `t` a geodesic to `w ∉ 𝓑^•_t` lies outside `𝓑^•_t` -/
theorem gm_S4_7_not_mem (hP : IsGeodesicL D P L 𝕫 w) (ht0 : 0 ≤ t) (hw : w ∉ filledBall D 𝕫 t) {u : ℝ}
    (hu : u ∈ Ioc t L) : P u ∉ filledBall D 𝕫 t := by
  have hc := gm_geodL_continuousOn hP
  have hyc : w ∉ closure (ballM D 𝕫 t) := fun h' => hw (Or.inl h')
  have hyb : ¬ Bornology.IsBounded (connectedComponentIn (closure (ballM D 𝕫 t))ᶜ w) :=
    fun hb => hw (Or.inr ⟨hyc, hb⟩)
  have hsub : P '' Ioc t L ⊆ (closure (ballM D 𝕫 t))ᶜ := by
    rintro _ ⟨v, hv, rfl⟩ h'
    have := gm_closure_ballM_subset D 𝕫 t h'
    simp only [mem_ofPred_eq] at this
    rw [gm_geodL_dist hP ⟨ht0.trans hv.1.le, hv.2⟩] at this
    linarith [hv.1]
  have hconn : IsPreconnected (P '' Ioc t L) :=
    isPreconnected_Ioc.image P (hc.mono (fun v hv => ⟨ht0.trans hv.1.le, hv.2⟩))
  have hwL : w ∈ P '' Ioc t L := ⟨L, ⟨hu.1.trans_le hu.2, le_rfl⟩, hP.2.2.1⟩
  have hcc := hconn.subset_connectedComponentIn hwL hsub
  rintro (h' | ⟨_, hb⟩)
  · exact hsub ⟨u, hu, rfl⟩ h'
  · apply hyb
    rwa [connectedComponentIn_eq (hcc ⟨u, hu, rfl⟩)]

/-- **GM.S4.7** (l. 2207, 2241): a unit-speed `D`-geodesic from `𝕫` to `w ∉ 𝓑^•_t` (`t > 0`)
is in `𝓑^•_t` exactly up to time `t`; in particular it never re-enters `𝓑^•_t`. -/
theorem gm_S4_7_mem_iff (hP : IsGeodesicL D P L 𝕫 w) (ht : 0 < t) (hw : w ∉ filledBall D 𝕫 t)
    {u : ℝ} (hu : u ∈ Icc 0 L) : P u ∈ filledBall D 𝕫 t ↔ u ≤ t := by
  constructor
  · intro hmem
    by_contra hlt
    exact gm_S4_7_not_mem hP ht.le hw ⟨not_le.mp hlt, hu.2⟩ hmem
  · intro hut
    rcases eq_or_lt_of_le hu.1 with h0 | h0
    · refine Or.inl (subset_closure ?_)
      show D.1 (𝕫, P u) < t
      rw [← h0, hP.2.1, D.2.self_eq_zero]
      exact ht
    · exact Or.inl (gm_closure_ballM_mono D 𝕫 hut (gm_geod_mem_closure_ballM hP h0 hu.2))

end LQGMetric.GM
