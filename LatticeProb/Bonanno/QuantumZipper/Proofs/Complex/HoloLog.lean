/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.HoloLog at commit 31e7483; only the module paths of local imports are changed. -/
/-
Copyright (c) 2026 The quantum-zipper authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: quantum-zipper (CA-H4U, EXT-CA node H4)
-/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.PolygonDixon
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.RMTStep1
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Holomorphic logarithms on domains whose complementary components are unbounded (EXT-CA node H4)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "H. Homology Cauchy", node H4.

* `wind_eq_zero_of_unbounded_compl`: if every component of `ℂ \ U` is unbounded, a closed polygon
  in `U` has winding number `0` about every point of `ℂ \ U`.
* `exists_holo_log`: on such an open preconnected `U`, every nonvanishing holomorphic `g` has a
  holomorphic logarithm.
* `CA.RMT.hasHoloSqrt_of_unbounded_compl`: hence `HasHoloSqrt U`, so the Riemann mapping theorem
  `riemann_mapping_of_hasHoloSqrt` (node M4) applies to `U`.

## Sources

Ahlfors, *Complex Analysis* (3rd ed. 1979), Ch. 4 §4.2 (the region `Ω` is simply connected iff
`n(γ, a) = 0` for all cycles `γ ⊆ Ω` and `a ∉ Ω`, where the complement of `Ω` "has no bounded
component") and Ch. 4 §4.4, Theorem 16 and its corollary (an `f` with `∫_γ f dz = 0` for all
cycles has a primitive, obtained by integrating along polygonal arcs from a fixed point; for a
nonvanishing `g` one integrates `g'/g` to get `log g`).  R. B. Burckel, *Classical Analysis in the
Complex Plane* (Birkhäuser 2021), Ch. 4 (index) and Theorem 10.11 (homology Cauchy).

The primitive is defined as `F w := -∮_{q_w} g'/g`, with `q_w` a (chosen) polygon in `U` from `w`
back to the base point; Dixon (node H3) applied to closed polygons `p ++ q_w` shows that
`∮_p g'/g = F w` for every polygon `p` in `U` from the base point to `w`, and the derivative of
`F` is then mathlib's `HasFDerivAt.curveIntegral_segment_source'`.  The last step
(`exp ∘ F = c · g`) uses mathlib's `logDeriv_eqOn_iff` instead of Ahlfors' direct derivative
computation of `g · exp(-F)` (same argument, packaged).
-/

noncomputable section

open Set Metric Filter Complex
open scoped Real
open scoped Topology

namespace QuantumZipper.CA.Homology

/-- If every component of `Uᶜ` is unbounded, a closed polygon in `U` has winding number `0` about
every point outside `U` (Ahlfors Ch. 4 §4.2: the component of `a` in `Uᶜ` is connected, unbounded
and disjoint from the carrier, so it lies in the unbounded component of the carrier's
complement). -/
theorem wind_eq_zero_of_unbounded_compl {U : Set ℂ}
    (hcomp : ∀ a ∉ U, ¬ Bornology.IsBounded (connectedComponentIn Uᶜ a))
    {p : Polygon} (hcl : p.last = p.head) (hpU : p.carrier ⊆ U) :
    ∀ a ∉ U, wind p a = 0 := by
  intro a ha
  have hR := carrier_subset_ball p
  obtain ⟨a₀, ha₀C, ha₀⟩ : ∃ a₀ ∈ connectedComponentIn Uᶜ a,
      1 + (‖p.head‖ + walkLength p.head p.rest) + p.length * ‖(2 * π * I)⁻¹‖ + 1 < ‖a₀‖ := by
    by_contra! h
    exact hcomp a ha (isBounded_iff_forall_norm_le.2 ⟨_, h⟩)
  refine wind_eq_zero_of_mem_connectedComponentIn p hcl hR ha₀ ?_
  have hsub : connectedComponentIn Uᶜ a ⊆ p.carrierᶜ :=
    (connectedComponentIn_subset _ _).trans (compl_subset_compl.2 hpU)
  exact (isPreconnected_connectedComponentIn.subset_connectedComponentIn ha₀C hsub)
    (mem_connectedComponentIn (show a ∈ Uᶜ from ha))

/-- **H4.** On an open preconnected `U ⊆ ℂ` all of whose complementary components are unbounded,
every nonvanishing holomorphic function has a holomorphic logarithm (Ahlfors Ch. 4 §4.4,
Theorem 16 and the discussion following it). -/
theorem exists_holo_log {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    (hcomp : ∀ a ∉ U, ¬ Bornology.IsBounded (connectedComponentIn Uᶜ a))
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U) (h0 : ∀ z ∈ U, g z ≠ 0) :
    ∃ L, DifferentiableOn ℂ L U ∧ ∀ z ∈ U, exp (L z) = g z := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact ⟨0, by simp, by simp⟩
  set h : ℂ → ℂ := fun z => deriv g z / g z with hh
  have hhd : DifferentiableOn ℂ h U := (hg.deriv hU).div hg h0
  have hclosed : ∀ p : Polygon, p.last = p.head → p.carrier ⊆ U → polyIntegral h p = 0 :=
    fun p hcl hpU => walkIntegral_eq_zero_of_wind hU hhd hcl hpU
      (wind_eq_zero_of_unbounded_compl hcomp hcl hpU)
  have hret : ∀ w ∈ U, ∃ q : Polygon, q.head = w ∧ q.last = z₀ ∧ ∀ z ∈ q.carrier, z ∈ U :=
    fun w hw => exists_polygon_of_isPreconnected hU hc hw hz₀
  classical
  let F : ℂ → ℂ := fun w => if hw : w ∈ U then -polyIntegral h (hret w hw).choose else 0
  have hF : ∀ p : Polygon, p.head = z₀ → p.last ∈ U → p.carrier ⊆ U →
      polyIntegral h p = F p.last := by
    intro p hp hpl hpU
    have hq := (hret p.last hpl).choose_spec
    have hpq : p.last = (hret p.last hpl).choose.head := hq.1.symm
    have hz := hclosed (p.append (hret p.last hpl).choose)
      (by rw [Polygon.last_append hpq, Polygon.head_append, hq.2.1, hp])
      (by rw [Polygon.carrier_append hpq]; exact union_subset hpU hq.2.2)
    rw [polyIntegral_append h hpq] at hz
    simp only [F, hpl, ↓reduceDIte]
    linear_combination hz
  have hFd : ∀ z ∈ U, HasDerivAt F (h z) z := by
    intro z hz
    obtain ⟨p, hp1, hp2, hp3⟩ := exists_polygon_of_isPreconnected hU hc hz₀ hz
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z hz
    have hloc : F =ᶠ[𝓝 z] (fun w => F z + ∫ᶜ x in Path.segment z w, dzForm h x) := by
      filter_upwards [ball_mem_nhds z hr] with w hw
      have hseg : _root_.segment ℝ z w ⊆ U :=
        ((convex_ball z r).segment_subset (mem_ball_self hr) hw).trans hrU
      have hpz : p.last = (Polygon.segment z w).head := hp2
      have hA := hF (p.append (Polygon.segment z w)) (by rw [Polygon.head_append, hp1])
        (by rw [Polygon.last_append hpz, Polygon.last_segment]; exact hrU hw)
        (by rw [Polygon.carrier_append hpz, Polygon.carrier_segment]; exact union_subset hp3 hseg)
      rw [polyIntegral_append h hpz, Polygon.last_append hpz, Polygon.last_segment,
        polyIntegral_segment, hF p hp1 (hp2 ▸ hz) hp3, hp2] at hA
      exact hA.symm
    have hcont : ∀ᶠ x in 𝓝 z, ContinuousAt (dzForm h) x := by
      filter_upwards [hU.mem_nhds hz] with x hx
      exact ((hhd x hx).differentiableAt (hU.mem_nhds hx)).continuousAt.smul continuousAt_const
    have hD := (HasFDerivAt.curveIntegral_segment_source' hcont).const_add (F z)
    have hD' : HasDerivAt (fun w => F z + ∫ᶜ x in Path.segment z w, dzForm h x) (h z) z := by
      simpa [dzForm] using hD.hasDerivAt
    exact hD'.congr_of_eventuallyEq hloc
  have hFdiff : DifferentiableOn ℂ F U :=
    fun z hz => (hFd z hz).differentiableAt.differentiableWithinAt
  have hEd : DifferentiableOn ℂ (fun z => exp (F z)) U := hFdiff.cexp
  have hEq : EqOn (logDeriv (fun z => exp (F z))) (logDeriv g) U := by
    intro z hz
    rw [logDeriv_apply, logDeriv_apply, ((hFd z hz).cexp).deriv,
      mul_div_cancel_left₀ _ (exp_ne_zero _)]
  obtain ⟨c, hc0, hcEq⟩ :=
    (logDeriv_eqOn_iff hEd hg hU hc h0 (fun z _ => exp_ne_zero _)).1 hEq
  refine ⟨fun z => F z - log c, hFdiff.sub_const _, fun z hz => ?_⟩
  have := hcEq hz
  simp only [Pi.smul_apply, smul_eq_mul] at this
  rw [exp_sub, exp_log hc0, this, mul_div_cancel_left₀ _ hc0]

end QuantumZipper.CA.Homology

namespace QuantumZipper.CA.RMT

/-- **H4, corollary.** An open preconnected `U` all of whose complementary components are
unbounded has holomorphic square roots (`s = exp (L / 2)`), so node M4 applies to it. -/
theorem hasHoloSqrt_of_unbounded_compl {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    (hcomp : ∀ a ∉ U, ¬ Bornology.IsBounded (connectedComponentIn Uᶜ a)) : HasHoloSqrt U := by
  intro g hg h0
  obtain ⟨L, hL, hexp⟩ := Homology.exists_holo_log hU hc hcomp g hg h0
  refine ⟨fun z => exp (L z / 2), (hL.div_const 2).cexp, fun z hz => ?_⟩
  have h2 : ((2 : ℕ) : ℂ) * (L z / 2) = L z := by push_cast; ring
  rw [← Complex.exp_nat_mul, h2, hexp z hz]

end QuantumZipper.CA.RMT
