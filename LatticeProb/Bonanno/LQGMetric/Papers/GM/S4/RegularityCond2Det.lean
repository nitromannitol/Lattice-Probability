/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.RegularityCond2Det at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityDet
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupStop
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightE

/-!
# GM Lemma 4.11, condition 2: deterministic comparison of `τ_r(z)` with a nearby centre `w`

Source: GM (arXiv:1905.00383v3) `uniqueness-final.tex`, condition 2 of `ℰ_𝕣` (l. 1955–1960) and
the proof of Lemma 4.11, l. 1984 ("Again using Axiom V, we can find a small enough `a` … such
that condition 2 … holds with probability at least `1 − (1−p)/6`"). GM give no details; the
covering argument (own argument, P2-M2H item 1) controls every centre `z` through a grid point `w`
with `|z − w|` small, using only distances across annuli and diameters of balls centred at `w`:

* `gm_c2_split`: in a length metric, a near-geodesic from `z` to `y` crosses `∂B_b(c)` at some `x`
  with `D(z,x) + D(x,y) ≤ D(z,y) + η`;
* `gm_c2_tau_ge`: `τ_r(z) ≥ m` as soon as `D(z,y) ≥ m` for all `|y − z| ≥ r` (a point of the filled
  ball outside `B_r(z)` either lies in `cl 𝓑_s(z)` or, by following the ray away from `z`, yields
  one there);
* `gm_c2_incr`: `τ_{r₂}(z) ≥ τ_{r₁}(z) + t` if `t` bounds the `D`-distance across an annulus
  `A_{a',b'}(w)` separating `∂B_{r₁}(z)` from `∂B_{r₂}(z)`;
* `gm_c2_ball`: `B_ρ(w) ⊆ 𝓑^•_{τ_r(z)}(z)` if `z ∈ B_ρ(w)` and the `D`-diameter of `B_ρ(w)` is
  smaller than `D(B_ρ(w), ∂B_{b'}(w))`, `b' + |z − w| ≤ r` (the event of GM U:1434, `GMS2_4e`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- a near-geodesic from `z` to `y` crosses `∂B_b(c)` (`|z − c| ≤ b ≤ |y − c|`) at a point `x`
with `D(z,x) + D(x,y) ≤ D(z,y) + η` -/
theorem gm_c2_split {d : ContMetric} (hlen : d.IsLength) {c z y : ℂ} {b η : ℝ}
    (hz : ‖z - c‖ ≤ b) (hy : b ≤ ‖y - c‖) (hη : 0 < η) :
    ∃ x, ‖x - c‖ = b ∧ d.1 (z, x) + d.1 (x, y) ≤ d.1 (z, y) + η := by
  obtain ⟨γ, hγ⟩ := hlen (d.pt z) (d.pt y) η hη
  set f : ℝ → ℝ := fun s => ‖d.unpt (γ.extend s) - c‖ with hf
  have hfc : Continuous f :=
    ((d.continuous_unpt.comp γ.continuous_extend).sub continuous_const).norm
  have hf0 : f 0 ≤ b := by simp only [hf, Path.extend_zero]; exact hz
  have hf1 : b ≤ f 1 := by simp only [hf, Path.extend_one]; exact hy
  obtain ⟨t₀, ht₀, hft₀⟩ : ∃ t₀ ∈ Icc (0 : ℝ) 1, f t₀ = b :=
    intermediate_value_Icc zero_le_one hfc.continuousOn ⟨hf0, hf1⟩
  refine ⟨d.unpt (γ.extend t₀), hft₀, ?_⟩
  have h1 := MetricGeometry.edist_le_curveLength γ.extend ht₀.1
  have h2 := MetricGeometry.edist_le_curveLength γ.extend ht₀.2
  have hadd := MetricGeometry.curveLength_add γ.extend ht₀.1 ht₀.2
  rw [Path.extend_zero] at h1
  rw [Path.extend_one] at h2
  have hsum : edist (d.pt z) (γ.extend t₀) + edist (γ.extend t₀) (d.pt y) ≤
      edist (d.pt z) (d.pt y) + ENNReal.ofReal η :=
    (add_le_add h1 h2).trans (hadd.le.trans hγ)
  have hD0 : ∀ p q : ℂ, 0 ≤ d.1 (p, q) := fun p q => (dist_nonneg : 0 ≤ dist (d.pt p) (d.pt q))
  have e1 : edist (d.pt z) (γ.extend t₀) = ENNReal.ofReal (d.1 (z, d.unpt (γ.extend t₀))) :=
    edist_dist _ _
  have e2 : edist (γ.extend t₀) (d.pt y) = ENNReal.ofReal (d.1 (d.unpt (γ.extend t₀), y)) :=
    edist_dist _ _
  have e3 : edist (d.pt z) (d.pt y) = ENNReal.ofReal (d.1 (z, y)) := edist_dist _ _
  rw [e1, e2, e3, ← ENNReal.ofReal_add (hD0 _ _) (hD0 _ _),
    ← ENNReal.ofReal_add (hD0 _ _) hη.le] at hsum
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (hD0 _ _) hη.le)).1 hsum

section Det
variable {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC}

/-- `τ_r(z) ≥ m` as soon as `D(z,y) ≥ m` for every `y ∉ B_r(z)` -/
theorem gm_c2_tau_ge {z : ℂ} {r m : ℝ} (hr : 0 < r) {ω : Ω}
    (hm : ∀ y : ℂ, r ≤ ‖y - z‖ → m ≤ (D (h ω)).1 (z, y)) : m ≤ tauR D h z r ω := by
  set d := D (h ω)
  refine le_csInf (gm_tauR_set_nonempty d z r) ?_
  rintro s ⟨-, hsub⟩
  by_contra hlt
  push Not at hlt
  apply hsub
  intro x hx
  by_contra hxb
  have hxr : r ≤ ‖x - z‖ := by rw [mem_ball, dist_eq_norm, not_lt] at hxb; exact hxb
  set X := closure (ballM d z s) with hXdef
  have hX : ∀ y ∈ X, d.1 (z, y) ≤ s := by
    have hcl : IsClosed {y : ℂ | d.1 (z, y) ≤ s} :=
      isClosed_le (d.1.continuous.comp (continuous_const.prodMk continuous_id)) continuous_const
    exact closure_minimal (fun y hy => show d.1 (z, y) ≤ s from le_of_lt hy) hcl
  rcases hx with hx | ⟨hxX, hbd⟩
  · linarith [hm x hxr, hX x hx]
  · -- the ray from `x` away from `z` meets `X`
    have hxz : 0 < ‖x - z‖ := lt_of_lt_of_le hr hxr
    set g : ℝ → ℂ := fun t => x + (t : ℂ) * (x - z) with hg
    have hgn : ∀ t : ℝ, 0 ≤ t → ‖g t - z‖ = (1 + t) * ‖x - z‖ := fun t ht => by
      have : g t - z = ((1 + t : ℝ) : ℂ) * (x - z) := by simp only [hg]; push_cast; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    by_cases hmeet : ∃ t : ℝ, 0 ≤ t ∧ g t ∈ X
    · obtain ⟨t, ht, hgX⟩ := hmeet
      have : r ≤ ‖g t - z‖ := by rw [hgn t ht]; nlinarith
      linarith [hm _ this, hX _ hgX]
    · push Not at hmeet
      have hpre : IsPreconnected (g '' Ici 0) :=
        isPreconnected_Ici.image g (by fun_prop)
      have hx0 : x ∈ g '' Ici 0 := ⟨0, mem_Ici.2 le_rfl, by simp [hg]⟩
      have hsubX : g '' Ici 0 ⊆ Xᶜ := by
        rintro _ ⟨t, ht, rfl⟩; exact hmeet t ht
      have hcc := hpre.subset_connectedComponentIn hx0 hsubX
      obtain ⟨M, hM⟩ := (isBounded_iff_subset_closedBall z).1 (hbd.subset hcc)
      set t : ℝ := |M| / ‖x - z‖ with ht
      have ht0 : 0 ≤ t := by positivity
      have hmem := hM ⟨t, ht0, rfl⟩
      rw [mem_closedBall, dist_eq_norm, hgn t ht0] at hmem
      have : (1 + t) * ‖x - z‖ = ‖x - z‖ + |M| := by
        rw [ht]; field_simp
      linarith [le_abs_self M]

/-- **increment of `τ`**: if `t` bounds the `D`-distance across `A_{a',b'}(w)` and this annulus
separates `∂B_{r₁}(z)` from `∂B_{r₂}(z)`, then `τ_{r₂}(z) ≥ τ_{r₁}(z) + t` -/
theorem gm_c2_incr {ω : Ω} (hlen : (D (h ω)).IsLength) {z w : ℂ} {r₁ r₂ a' b' t : ℝ}
    (hr₁ : 0 < r₁) (h1 : r₁ + ‖z - w‖ ≤ a') (h2 : b' + ‖z - w‖ ≤ r₂) (hab : a' ≤ b')
    (hcross : ∀ u ∈ sphere w a', ∀ v ∈ sphere w b', t ≤ (D (h ω)).1 (u, v)) :
    tauR D h z r₁ ω + t ≤ tauR D h z r₂ ω := by
  have hzw0 := norm_nonneg (z - w)
  have hr₂ : 0 < r₂ := by linarith
  refine gm_c2_tau_ge hr₂ fun y hy => ?_
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨x, hx, hsplit⟩ := gm_c2_split (d := D (h ω)) hlen (c := z) (z := z) (y := y) (b := r₁)
    (by rw [sub_self, norm_zero]; exact hr₁.le) (by linarith) hη
  have hτ := gm_tauR_le_dist (D := D) (h := h) (z := z) (w := x) (Rad := r₁) hx.ge ω
  have hxw : ‖x - w‖ ≤ a' := by
    have := norm_add_le (x - z) (z - w)
    rw [sub_add_sub_cancel] at this; linarith
  have hyw : b' ≤ ‖y - w‖ := by
    have := norm_sub_le (y - w) (z - w)
    rw [show y - w - (z - w) = y - z by ring] at this; linarith
  have hc := Tight.le_of_forall_crossing hlen hab hxw hyw hcross
  linarith

end Det

end LQGMetric.GM
