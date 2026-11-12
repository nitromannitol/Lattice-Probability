/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MeshOnly.MeshOnlyNashTwoRegimes at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MeshOnly.MeshOnlyNashDecay

/-! Integrating the two Nash regimes on the two halves of a time interval. -/

open Set

namespace BouRabeeGwynne

private lemma nash_power_factor {x : ℝ} (hx : 0 < x) (p : ℝ) :
    x ^ (1 + 2 * p) = x ^ (1 + p) * x ^ p := by
  rw [← Real.rpow_add hx]
  congr 1
  ring

/-- A nonnegative dissipative flow with the two Nash rates has an initial-value
independent bound. Comparing `X(t/2)^p` to `ε⁻¹` supplies one whole interval
on which a single reciprocal power can be integrated. -/
theorem nash_two_regime_decay (X X' : ℝ → ℝ) {c ε p : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hp : 0 < p)
    (hX : ∀ s, 0 ≤ s → 0 ≤ X s)
    (hderiv : ∀ s, 0 ≤ s → HasDerivAt X (X' s) s)
    (hdecay : ∀ s, 0 ≤ s →
      c * min (X s ^ (1 + 2 * p)) (X s ^ (1 + p) / ε) ≤ -X' s)
    {t : ℝ} (ht : 0 < t) :
    X t ≤ (c * p * t) ^ (-1 / (2 * p)) +
      (c * p * t / (2 * ε)) ^ (-1 / p) := by
  have hanti : AntitoneOn X (Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hderiv s (interior_subset hs)).differentiableAt.differentiableWithinAt)
      (by
        intro s hs
        have hs0 : 0 ≤ s := interior_subset hs
        rw [(hderiv s hs0).deriv]
        have hmin : 0 ≤ min (X s ^ (1 + 2 * p)) (X s ^ (1 + p) / ε) :=
          le_min (Real.rpow_nonneg (hX s hs0) _)
            (div_nonneg (Real.rpow_nonneg (hX s hs0) _) hε.le)
        have hh := hdecay s hs0
        nlinarith [mul_nonneg hc.le hmin])
  by_cases hXt : 0 < X t
  swap
  · exact (le_of_not_gt hXt).trans (add_nonneg
      (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _))
  have hpositive (s : ℝ) (hs : s ∈ Icc 0 t) : 0 < X s :=
    hXt.trans_le (hanti hs.1 ht.le hs.2)
  have htHalf : 0 < t / 2 := half_pos ht
  have htHalf_le : t / 2 ≤ t := by linarith
  by_cases hphase : ε⁻¹ ≤ X (t / 2) ^ p
  · have hinterval (s : ℝ) (hs : s ∈ Icc 0 (t / 2)) : s ∈ Icc 0 t :=
      ⟨hs.1, hs.2.trans htHalf_le⟩
    have hsingle : ∀ s ∈ Icc 0 (t / 2),
        (c / ε) * X s ^ (1 + p) ≤ -X' s := by
      intro s hs
      have hxp : ε⁻¹ ≤ X s ^ p := hphase.trans
        (Real.rpow_le_rpow (hX (t / 2) htHalf.le)
          (hanti hs.1 htHalf.le hs.2) hp.le)
      have hcompare : X s ^ (1 + p) / ε ≤ X s ^ (1 + 2 * p) := by
        rw [nash_power_factor (hpositive s (hinterval s hs)) p, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hxp (Real.rpow_nonneg (hX s hs.1) _)
      have hh := hdecay s hs.1
      rw [min_eq_right hcompare] at hh
      convert hh using 1 <;> ring
    have hhalf := nash_power_decay_on_interval X X' htHalf (div_pos hc hε) hp
      (fun s hs => hpositive s (hinterval s hs))
      (fun s hs => hderiv s hs.1) hsingle
    have he : (c / ε) * p * (t / 2 - 0) = c * p * t / (2 * ε) := by ring
    rw [he] at hhalf
    exact (hanti htHalf.le ht.le htHalf_le).trans
      (hhalf.trans (le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)))
  · have hphase' : X (t / 2) ^ p ≤ ε⁻¹ := (lt_of_not_ge hphase).le
    have hinterval (s : ℝ) (hs : s ∈ Icc (t / 2) t) : s ∈ Icc 0 t :=
      ⟨htHalf.le.trans hs.1, hs.2⟩
    have hsingle : ∀ s ∈ Icc (t / 2) t,
        c * X s ^ (1 + 2 * p) ≤ -X' s := by
      intro s hs
      have hs0 : 0 ≤ s := (hinterval s hs).1
      have hxp : X s ^ p ≤ ε⁻¹ :=
        (Real.rpow_le_rpow (hX s hs0) (hanti htHalf.le hs0 hs.1) hp.le).trans hphase'
      have hcompare : X s ^ (1 + 2 * p) ≤ X s ^ (1 + p) / ε := by
        rw [nash_power_factor (hpositive s (hinterval s hs)) p, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hxp (Real.rpow_nonneg (hX s hs0) _)
      simpa only [min_eq_left hcompare] using hdecay s hs0
    have htail := nash_power_decay_on_interval X X' (by linarith : t / 2 < t)
      hc (mul_pos zero_lt_two hp) (fun s hs => hpositive s (hinterval s hs))
      (fun s hs => hderiv s (hinterval s hs).1) hsingle
    have he : c * (2 * p) * (t - t / 2) = c * p * t := by ring
    rw [he] at htail
    exact htail.trans (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _))

end BouRabeeGwynne
