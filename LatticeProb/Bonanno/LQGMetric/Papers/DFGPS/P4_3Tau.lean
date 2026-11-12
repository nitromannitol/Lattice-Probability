/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_3Tau at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_3Cross
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L4_4
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L4_5Det

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 4.3: the bound (`eqn-tau-upper`) (task P2-DFA10)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Proposition 4.3,
Step 3, (`eqn-tau-upper`, T:2720–2728): `τ_k ≤ t ≤ D_h(0, z) + D_h(z, P(t)) ≤ s + C D_h(∂B_k,
∂(2B_k))` for `P(t) ∈ ∂B_k` and a point `z`. The paper takes `z ∈ ∂𝓑_s(0; D_h)` and uses that
`z` lies on `∂B_k` (it is only shown that `B_k` meets `∂𝓑_s`). We supply `z ∈ ∂B_k` with
`D_h(0, z) < s` (`exists_sphere_lt_of_closure`): if `B_k` meets `cl 𝓑_s` and `0 ∉ B_k`, a
near-geodesic from `0` to a point of `𝓑_s ∩ B_k` stays in `𝓑_s` and crosses `∂B_k` (intermediate
value theorem, length metric; own elementary argument, DEV-DF-A10-3).
-/

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace P43

open Blueprint MetricGeometry

/-- in a length metric, a point `x ∈ B̄_ρ(y)` with `D(z₀, x) < s`, `z₀ ∉ B_ρ(y)`, gives a point
`q ∈ ∂B_ρ(y)` with `D(z₀, q) < s` -/
theorem exists_sphere_lt {D : ContMetric} (hlen : D.IsLength) {z₀ x y : ℂ} {ρ s : ℝ}
    (hx : ‖x - y‖ ≤ ρ) (hz : ρ ≤ ‖z₀ - y‖) (hD : D.1 (z₀, x) < s) :
    ∃ q ∈ sphere y ρ, D.1 (z₀, q) < s := by
  have hD0 : 0 ≤ D.1 (z₀, x) := (dist_nonneg : 0 ≤ dist (D.pt z₀) (D.pt x))
  obtain ⟨γ, hγ⟩ := hlen (D.pt z₀) (D.pt x) ((s - D.1 (z₀, x)) / 2) (by linarith)
  have hγt : pathLength γ < ENNReal.ofReal s := by
    refine hγ.trans_lt ?_
    rw [edist_dist, ← ENNReal.ofReal_add dist_nonneg (by linarith)]
    refine (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 ?_
    show D.1 (z₀, x) + (s - D.1 (z₀, x)) / 2 < s
    linarith
  set f : ℝ → ℝ := fun t => ‖D.unpt (γ.extend t) - y‖ with hf
  have hfc : Continuous f :=
    ((D.continuous_unpt.comp γ.continuous_extend).sub continuous_const).norm
  have hf0 : ρ ≤ f 0 := by simp only [hf, Path.extend_zero]; exact hz
  have hf1 : f 1 ≤ ρ := by simp only [hf, Path.extend_one]; exact hx
  obtain ⟨t₁, ht₁, hft₁⟩ : ∃ t₁ ∈ Icc (0 : ℝ) 1, f t₁ = ρ :=
    intermediate_value_Icc' zero_le_one hfc.continuousOn ⟨hf1, hf0⟩
  refine ⟨D.unpt (γ.extend t₁), mem_sphere.2 (by rw [dist_eq_norm]; exact hft₁), ?_⟩
  have hle : edist (γ.extend 0) (γ.extend t₁) ≤ pathLength γ :=
    (edist_le_curveLength γ.extend ht₁.1).trans (curveLength_mono _ le_rfl ht₁.2)
  rw [Path.extend_zero] at hle
  have e : edist (D.pt z₀) (γ.extend t₁) = ENNReal.ofReal (D.1 (z₀, D.unpt (γ.extend t₁))) :=
    edist_dist _ _
  have h2 := hle.trans_lt hγt
  rw [e] at h2
  have hnn : 0 ≤ D.1 (z₀, D.unpt (γ.extend t₁)) :=
    (dist_nonneg : 0 ≤ dist (D.pt z₀) (γ.extend t₁))
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnn).1 h2

/-- if `B_ρ(y)` meets `cl 𝓑_s(0; D)` and `0 ∉ B_ρ(y)`, some `q ∈ ∂B_ρ(y)` has `D(0, q) < s` -/
theorem exists_sphere_lt_of_closure {D : ContMetric} (hlen : D.IsLength) {y f : ℂ} {ρ s : ℝ}
    (hf : f ∈ ball y ρ) (hfc : f ∈ closure (ballM D 0 s)) (h0 : ρ ≤ ‖(0 : ℂ) - y‖) :
    ∃ q ∈ sphere y ρ, D.1 (0, q) < s := by
  obtain ⟨p, hp, hpB⟩ := mem_closure_iff.1 hfc _ isOpen_ball hf
  rw [mem_ball, dist_eq_norm] at hp
  exact exists_sphere_lt hlen hp.le h0 hpB

/-- (`eqn-tau-upper`, T:2720–2728): if `P` is a `D`-geodesic from `0`, `P(t) ∈ ∂B_ρ(y)`, `B_ρ(y)`
is `C`-good and `q ∈ ∂B_ρ(y)` has `D(0, q) ≤ s`, then `t ≤ s + C D(∂B_ρ(y), ∂B_{2ρ}(y))` -/
theorem tau_upper {D : ContMetric} {P : ℝ → ℂ} {L : ℝ} {x : ℂ} (hP : IsGeodesicL D P L 0 x)
    {t : ℝ} (ht : t ∈ Icc 0 L) {y q : ℂ} {ρ C s : ℝ} (hgood : CGood D C ρ y)
    (hPt : P t ∈ sphere y ρ) (hq : q ∈ sphere y ρ) (hqs : D.1 (0, q) ≤ s) :
    ENNReal.ofReal t ≤ ENNReal.ofReal s +
      ENNReal.ofReal C * setDist D (sphere y ρ) (sphere y (2 * ρ)) := by
  have h1 : t ≤ D.1 (0, q) + D.1 (q, P t) := by
    calc t = D.1 (0, P t) := (GM.gm_geodL_dist hP ht).symm
      _ ≤ D.1 (0, q) + D.1 (q, P t) := D.2.triangle _ _ _
  have h2 : ENNReal.ofReal (D.1 (q, P t)) ≤
      internalDiam D (sphere y ρ) (annulus y (ρ / 2) (2 * ρ)) :=
    (L45.ofReal_le_internal D _ q (P t)).trans (le_iSup₂_of_le q hq (le_iSup₂_of_le (P t) hPt le_rfl))
  calc ENNReal.ofReal t ≤ ENNReal.ofReal (D.1 (0, q) + D.1 (q, P t)) := ENNReal.ofReal_le_ofReal h1
    _ ≤ ENNReal.ofReal (D.1 (0, q)) + ENNReal.ofReal (D.1 (q, P t)) := ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal s + ENNReal.ofReal C * setDist D (sphere y ρ) (sphere y (2 * ρ)) :=
        add_le_add (ENNReal.ofReal_le_ofReal hqs) (h2.trans hgood)

end P43
end LQGMetric.DFGPS
