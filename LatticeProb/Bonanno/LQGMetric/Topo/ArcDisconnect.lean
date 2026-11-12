/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.ArcDisconnect at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.Shortcut
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.LocallyConvex.Bounded
import LatticeProb.Bonanno.LQGMetric.Topo.CircleUnion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A small set disconnecting a boundary arc from `∞` lies in a ball centred on the boundary

Topological step of **CONF Lemma 3.7** (`lem-geo-kill`, Gwynne–Miller, *Confluence of geodesics in
Liouville quantum gravity for γ ∈ (0,2)*, arXiv:1905.00381, `confluence-final.tex` lines
1467–1468): "Since `I` can be disconnected from `∞` in `ℂ \ 𝓑^•_τ` by a set of Euclidean diameter
at most `ε𝕣`, we can choose a point `x ∈ ∂𝓑^•_τ` such that `B_{ε𝕣}(x)` disconnects `I` from
`∞` in `ℂ \ 𝓑^•_τ`."

`DisconnectsFromInfty K Y I`: for some `R`, every path from a point of norm `> R` to a point
`x ∈ I` which meets `K` only at `x` (it "first hits `K` at a point of `I`", reversed) meets `Y`.

`exists_frontier_closedBall_disconnects`: for `K` closed, `I ⊆ ∂K` nonempty and `Y` bounded with
`diam Y ≤ d`, there is `x ∈ ∂K` such that `closedBall x d` disconnects `I` from `∞` in `ℂ \ K`.
CONF gives no argument ("we can choose"); this is an own argument. Let
`W = ⋂_{y ∈ Y} closedBall y d ⊇ Y` (convex, compact). If `W` meets `∂K`, take `x` there.
Otherwise either `W ⊆ int K` (then no admissible path meets `Y`, so none exists) or `W ∩ K = ∅`.
In the last case a convex open neighbourhood `U` of `W` has closure disjoint from `K`; its
"boundary level set" `{gauge = 1}` is path-connected (image of the unit circle), and any
admissible path can be rerouted along it around `U`, avoiding `Y`: again no admissible path
exists. The open ball `B_ρ(x)` of the paper is obtained for `diam Y < ρ`
(`exists_frontier_ball_disconnects`); with `diam Y = ε𝕣` exactly CONF's open ball needs the
closed one (proposed deviation).
-/

namespace LQGMetric

open Set Metric

/-- `Y` disconnects `I` from `∞` in `ℂ \ K`. -/
def DisconnectsFromInfty (K Y I : Set ℂ) : Prop :=
  ∃ R : ℝ, ∀ (y x : ℂ) (γ : Path y x), R < ‖y‖ → x ∈ I → range γ ∩ K ⊆ {x} →
    (range γ ∩ Y).Nonempty

theorem DisconnectsFromInfty.mono {K Y Y' I : Set ℂ} (h : DisconnectsFromInfty K Y I)
    (hY : Y ⊆ Y') : DisconnectsFromInfty K Y' I := by
  obtain ⟨R, hR⟩ := h
  exact ⟨R, fun y x γ hy hx hK => (hR y x γ hy hx hK).mono (inter_subset_inter_right _ hY)⟩

namespace ConvexLevel

variable {U : Set ℂ} {c : ℂ}

/-- The translate `U - c`. -/
def C (U : Set ℂ) (c : ℂ) : Set ℂ := (fun v => v + c) ⁻¹' U

/-- The gauge of `U` centred at `c`. -/
noncomputable def G (U : Set ℂ) (c : ℂ) (z : ℂ) : ℝ := gauge (C U c) (z - c)

variable (hUo : IsOpen U) (hUc : Convex ℝ U) (hUb : Bornology.IsBounded U) (hc : c ∈ U)
include hUo hUc hc

omit hUc in
theorem C_nhds : C U c ∈ nhds (0 : ℂ) :=
  (hUo.preimage (continuous_id.add continuous_const)).mem_nhds (by simpa [C] using hc)

theorem continuous_G : Continuous (G U c) :=
  (continuous_gauge (hUc.translate_preimage_left c) (C_nhds hUo hc)).comp
    (continuous_sub_right c)

theorem G_lt_one_iff (z : ℂ) : G U c z < 1 ↔ z ∈ U := by
  have := setOfPred_gauge_lt_one_eq_self_of_isOpen (hUc.translate_preimage_left c)
    (by simpa [C] using hc) (hUo.preimage (continuous_id.add continuous_const))
  have h2 := congrArg (fun S : Set ℂ => z - c ∈ S) this
  simpa [G, C] using h2

theorem mem_closure_of_G_le_one {z : ℂ} (hz : G U c z ≤ 1) : z ∈ closure U := by
  have h := mem_closure_of_gauge_le_one (hUc.translate_preimage_left c) (by simpa [C] using hc)
    (absorbent_nhds_zero (C_nhds hUo hc)) hz
  have hsub : closure (C U c) ⊆ (fun v => v + c) ⁻¹' closure U :=
    closure_minimal (preimage_mono subset_closure)
      (isClosed_closure.preimage (continuous_id.add continuous_const))
  simpa using hsub h

include hUb in
theorem isPathConnected_level : IsPathConnected {z | G U c z = 1} := by
  have hconv := hUc.translate_preimage_left c
  have hn := C_nhds hUo hc
  have habs : Absorbent ℝ (C U c) := absorbent_nhds_zero hn
  have hb : Bornology.IsVonNBounded ℝ (C U c) := by
    rw [NormedSpace.isVonNBounded_iff ℝ]
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hUb
    refine isBounded_iff_forall_norm_le.2 ⟨M + ‖c‖, fun v hv => ?_⟩
    have := hM _ hv
    calc ‖v‖ = ‖(v + c) - c‖ := by ring_nf
      _ ≤ ‖v + c‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ M + ‖c‖ := by linarith
  set φ : ℂ → ℂ := fun u => c + (gauge (C U c) u)⁻¹ • u with hφ
  have hgc : Continuous (gauge (C U c)) := continuous_gauge hconv hn
  have hφc : ContinuousOn φ (sphere 0 1) := by
    have h1 : ContinuousOn (fun u => (gauge (C U c) u)⁻¹) (sphere 0 1) :=
      (hgc.continuousOn).inv₀ fun u hu =>
        ((gauge_pos habs hb).2 (ne_zero_of_mem_unit_sphere ⟨u, hu⟩)).ne'
    exact continuousOn_const.add (h1.smul continuousOn_id)
  have himg : {z | G U c z = 1} = φ '' sphere 0 1 := by
    ext z
    constructor
    · intro hz
      have hz' : gauge (C U c) (z - c) = 1 := hz
      have hne : z - c ≠ 0 := by
        intro h; rw [h, gauge_zero] at hz'; exact zero_ne_one hz'
      have hnorm : 0 < ‖z - c‖ := norm_pos_iff.2 hne
      refine ⟨(‖z - c‖⁻¹ : ℝ) • (z - c), ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ hnorm.ne']
      · simp only [hφ]
        rw [gauge_smul_of_nonneg (inv_nonneg.2 hnorm.le), hz', smul_eq_mul, mul_one, inv_inv,
          smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
        ring
    · rintro ⟨u, hu, rfl⟩
      have hpos : 0 < gauge (C U c) u := (gauge_pos habs hb).2 (ne_zero_of_mem_unit_sphere ⟨u, hu⟩)
      show gauge (C U c) (c + (gauge (C U c) u)⁻¹ • u - c) = 1
      rw [add_sub_cancel_left, gauge_smul_of_nonneg (inv_nonneg.2 hpos.le), smul_eq_mul,
        inv_mul_cancel₀ hpos.ne']
  rw [himg]
  exact (TopoCircle.isPathConnected_sphere_complex 0 zero_le_one).image' hφc

end ConvexLevel

end LQGMetric
