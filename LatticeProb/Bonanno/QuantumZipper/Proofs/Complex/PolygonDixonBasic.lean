/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.PolygonDixonBasic at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.Polygon
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# The difference quotient of a holomorphic function (EXT-CA node H3, part 1)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "H. Homology Cauchy", node H3 (Dixon's theorem).

This file contains the analytic core of Dixon's proof that a closed polygon whose winding number
vanishes outside a domain carries zero integral of any holomorphic function.  The function

`sec f z w = (f z - f w)/(z - w)` for `z ≠ w`,  `sec f z z = deriv f z`,

is, for `f` holomorphic on an open `U`, *jointly continuous* on `U × U`: off the diagonal this is
elementary, on the diagonal it is the strict differentiability of `f`, which for a holomorphic `f`
comes from its analyticity (`HasFPowerSeriesAt.hasStrictFDerivAt`).

## Sources

S. A. Dixon, *A brief proof of Cauchy's integral theorem*, Proc. Amer. Math. Soc. **29** (1971)
625-626: the function `(z,w) ↦ (f(z) - f(w))/(z - w)` extended by `f'(z)` on the diagonal is
continuous on `U × U` (there: "strictly differentiable"), the source of the two-variable kernel of
the proof of the homology form of Cauchy's theorem.  The analyticity `DifferentiableOn ℂ f U →
AnalyticOn ℂ f U` used to obtain strict differentiability is mathlib's
`DifferentiableOn.analyticAt`, `HasFPowerSeriesAt.hasStrictFDerivAt`.

The two-variable Cauchy kernel g and the continuity statement are also in R. B. Burckel,
*Classical Analysis in the Complex Plane* (Birkhäuser 2021), Theorem 10.11 area (the homology form
of Cauchy's theorem), and in R. Narasimhan and Y. Nievergelt, *Complex Analysis in One Variable*
(2nd ed.), §5.
-/

noncomputable section

open Set Metric Filter Complex
open scoped Topology

namespace QuantumZipper.CA.Homology

/-! ## The difference quotient -/

/-- The difference quotient `(f z - f w)/(z - w)`, extended to the diagonal by the derivative
`deriv f z` (Dixon 1971; the kernel of the two-variable proof of Cauchy's theorem). -/
def sec (f : ℂ → ℂ) (z w : ℂ) : ℂ := if z = w then deriv f z else (f z - f w) / (z - w)

@[simp] theorem sec_self (f : ℂ → ℂ) (z : ℂ) : sec f z z = deriv f z := by
  simp [sec]

theorem sec_of_ne {f : ℂ → ℂ} {z w : ℂ} (h : z ≠ w) : sec f z w = (f z - f w) / (z - w) := by
  simp [sec, h]

/-! ## Strict differentiability of a holomorphic function -/

/-- A continuous linear map `ℂ →L[ℂ] ℂ` with `L 1 = c` is multiplication by `c`. -/
theorem clm_eq_smul_one (L : ℂ →L[ℂ] ℂ) (c : ℂ) (hL : L 1 = c) :
    L = c • (1 : ℂ →L[ℂ] ℂ) :=
  ContinuousLinearMap.ext fun w => by
    have h1 : (c • (1 : ℂ →L[ℂ] ℂ)) w = c * w := by
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
    rw [h1]
    conv_lhs => rw [show w = w • (1 : ℂ) by simp]
    rw [map_smul, hL, smul_eq_mul, mul_comm]

/-- **Strict differentiability.** A function holomorphic on an open set is strictly differentiable
(in the sense of the two-variable difference quotient) at each of its points. -/
theorem hasStrictFDerivAt_deriv_of_differentiableOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U) :
    HasStrictFDerivAt f ((deriv f z) • (1 : ℂ →L[ℂ] ℂ)) z := by
  obtain ⟨p, hp⟩ := hf.analyticAt (hU.mem_nhds hz)
  have h := hp.hasStrictFDerivAt
  have hderiv : (continuousMultilinearCurryFin1 ℂ ℂ ℂ (p 1)) 1 = deriv f z := by
    have h2 : HasFDerivAt f (continuousMultilinearCurryFin1 ℂ ℂ ℂ (p 1)) z := h.hasFDerivAt
    exact (h2.hasDerivAt.deriv).symm
  rw [clm_eq_smul_one _ (deriv f z) hderiv] at h
  exact h

/-- **Strict bound for the difference quotient.** For `f` holomorphic near `z₀` and every `ε > 0`
there is `δ > 0` with `‖f z - f w - f'(z₀)(z-w)‖ ≤ ε‖z - w‖` for `z, w` in the ball of radius `δ`
around `z₀`. -/
theorem exists_strict_sec_bound {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z w : ℂ, dist z z₀ < δ → dist w z₀ < δ →
      ‖f z - f w - deriv f z₀ * (z - w)‖ ≤ ε * ‖z - w‖ := by
  have hlittle := (hasStrictFDerivAt_deriv_of_differentiableOn hU hf hz₀).isLittleO
  have hev := hlittle.def hε
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hbound⟩ := hev
  refine ⟨δ, hδ, fun z w hz hw => ?_⟩
  have hmem : (z, w) ∈ Metric.ball (z₀, z₀) δ := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hz, hw⟩
  have hb := hbound hmem
  simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.one_apply]
    using hb

/-! ## Joint continuity of the difference quotient -/

/-- The difference quotient of a function holomorphic on an open `U` is continuous on `U × U`
(Dixon 1971). -/
theorem continuousOn_sec {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fun p : ℂ × ℂ => sec f p.1 p.2) (U ×ˢ U) := by
  intro p₀ hp₀
  obtain ⟨hz₀, hw₀⟩ := hp₀
  rcases eq_or_ne p₀.1 p₀.2 with hdiag | hne
  · -- on the diagonal strict differentiability gives the bound
    have hsec₀ : sec f p₀.1 p₀.2 = deriv f p₀.1 := by rw [hdiag, sec_self]
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by linarith
    obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousWithinAt_iff.1
      ((hf.deriv hU).continuousOn p₀.1 hz₀) (ε / 2) hε2
    obtain ⟨δ₂, hδ₂, h₂⟩ := exists_strict_sec_bound hU hf hz₀ hε2
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun q hq hd => ?_⟩
    obtain ⟨hq₁, hq₂⟩ := hq
    have hle1 : dist q.1 p₀.1 ≤ dist q p₀ := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    have hle2 : dist q.2 p₀.2 ≤ dist q p₀ := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    have hd₁' : dist q.1 p₀.1 < min δ₁ δ₂ := lt_of_le_of_lt hle1 hd
    have hd₂' : dist q.2 p₀.2 < min δ₁ δ₂ := lt_of_le_of_lt hle2 hd
    have hd₂'' : dist q.2 p₀.1 < min δ₁ δ₂ := hdiag.symm ▸ hd₂'
    have hb₁ := h₁ hq₁ (lt_of_lt_of_le hd₁' (min_le_left _ _))
    have hb₂ := h₂ q.1 q.2 (lt_of_lt_of_le hd₁' (min_le_right _ _))
      (lt_of_lt_of_le hd₂'' (min_le_right _ _))
    rcases eq_or_ne q.1 q.2 with hqq | hqq
    · rw [show sec f q.1 q.2 = deriv f q.1 by rw [hqq, sec_self], hsec₀]
      rw [dist_eq_norm] at hb₁ ⊢
      linarith
    · rw [sec_of_ne hqq, hsec₀]
      have hnum : (f q.1 - f q.2) / (q.1 - q.2) - deriv f p₀.1
          = (f q.1 - f q.2 - deriv f p₀.1 * (q.1 - q.2)) / (q.1 - q.2) := by
        field_simp
      have hden : (0 : ℝ) < ‖q.1 - q.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hqq)
      have hgoal : ‖(f q.1 - f q.2) / (q.1 - q.2) - deriv f p₀.1‖ < ε := by
        rw [hnum, norm_div, div_lt_iff₀ hden]
        calc ‖f q.1 - f q.2 - deriv f p₀.1 * (q.1 - q.2)‖
            ≤ ε / 2 * ‖q.1 - q.2‖ := hb₂
          _ < ε * ‖q.1 - q.2‖ := mul_lt_mul_of_pos_right (by linarith) hden
      rwa [dist_eq_norm]
  · -- off the diagonal the quotient is continuous
    have hcont : ContinuousAt (fun p : ℂ × ℂ => (f p.1 - f p.2) / (p.1 - p.2)) p₀ := by
      refine ContinuousAt.div ?_ ?_ ?_
      · exact ((hf.continuousOn.continuousAt (hU.mem_nhds hz₀)).comp
          continuous_fst.continuousAt).sub
          ((hf.continuousOn.continuousAt (hU.mem_nhds hw₀)).comp continuous_snd.continuousAt)
      · exact (continuous_fst.sub continuous_snd).continuousAt
      · exact sub_ne_zero.mpr hne
    have hopen : IsOpen {p : ℂ × ℂ | p.1 - p.2 ≠ 0} :=
      isOpen_ne.preimage (continuous_fst.sub continuous_snd)
    have hev : (fun p : ℂ × ℂ => sec f p.1 p.2)
        =ᶠ[𝓝[U ×ˢ U] p₀] (fun p : ℂ × ℂ => (f p.1 - f p.2) / (p.1 - p.2)) := by
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (hopen.eventually_mem (by simpa using sub_ne_zero.mpr hne)),
        self_mem_nhdsWithin] with p hp _
      exact sec_of_ne (sub_ne_zero.mp hp)
    exact hcont.continuousWithinAt.congr_of_eventuallyEq hev (sec_of_ne hne)

end QuantumZipper.CA.Homology
