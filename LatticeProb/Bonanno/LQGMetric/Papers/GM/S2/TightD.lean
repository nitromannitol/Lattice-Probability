/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightD at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightA
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightAround

/-!
# GM S2.4d: short disconnecting loops around annuli (task P2-TIGHT)

GM (arXiv:1905.00383v3) l. 1331 (condition 3 of the event `𝖤_r(z)`) and l. 1393: "We can again
apply Axiom V (tightness across scales) to find that there exists `A > 1` depending on `α` and
`p̃` such that for each `z ∈ ℂ` and `r > 0`, [there is a path in `𝔸_{αr,r}(z)` which disconnects
the inner and outer boundaries of `𝔸_{αr,r}(z)` and has `D_h`-length at most
`A D_h(∂B_{αr}(z), ∂B_r(z))`] with probability at least `1 − (1 − p̃)/3`." No proof in GM.

`gm_S2_4d` (node S2.4d of decision D-A3, `decisions/DEC-A.md` (c)): for `α ∈ (0, 1)` and
`ε > 0` there is `A > 0` such that, uniformly over whole-plane GFFs `h`, `r > 0` and `z`, with
probability `> 1 − ε` the `D_h`-distance around `𝔸_{αr,r}(z)` (DFGPS Def. 3.7,
`ContMetric.aroundDist`) is `≤ A D_h(x, y)` for all `x ∈ ∂B_{αr}(z)`, `y ∈ ∂B_r(z)`, i.e.
`≤ A D_h(∂B_{αr}(z), ∂B_r(z))`.

Proof (D-A3): S2.4a (separated points, level `s`), S2.4b (level `s/2`) and S2.4a (circles
`∂B_α`, `∂B_1`, level `s′`) each fail with probability `< ε/4`; on their intersection and the
a.s. event that `D_h` is a length metric, `aroundDist_le_of_events` gives a loop of length
`≤ m s 𝔠_r e^{ξh_r(z)} ≤ (m s / s′) D_h(x, y)`. Own argument; DEVIATIONS DA5.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped ENNReal

namespace LQGMetric
namespace GM
namespace Tight

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

/-- **GM.S2.4d** (D-A3): a short loop around `𝔸_{αr,r}(z)`, uniformly in the field, the scale and
the centre. -/
theorem gm_S2_4d (hD : IsWeakLQGMetric γ D c) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      P {ω | ¬ ∀ x ∈ sphere z (α * r), ∀ y ∈ sphere z r,
        (D (h ω)).aroundDist {w | α * r < ‖w - z‖ ∧ ‖w - z‖ < r} (sphere z (α * r))
          (sphere z r) ≤ ENNReal.ofReal (A * (D (h ω)).1 (x, y))} < ε := by
  set ρ : ℝ := (1 + α) / 2 with hρ
  set g : ℝ := (1 - α) / 2 with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hρ0 : 0 ≤ ρ := by rw [hρ]; linarith
  have hε1 : 0 < ε / 2 / 2 := ENNReal.half_pos (ENNReal.half_pos hε.ne').ne'
  have hK := isCompact_closedBall (0 : ℂ) 1
  obtain ⟨s, hs, H1⟩ := gm_S2_4a_sep hD hK (b := g / 4) (by positivity) hε1
  obtain ⟨b, hb, H2⟩ := gm_S2_4b hD hK (s := s / 2) (by positivity) hε1
  have hdisj : Disjoint (sphere (0 : ℂ) α) (sphere (0 : ℂ) 1) :=
    disjoint_left.2 fun u h1 h2 => by
      rw [mem_sphere] at h1 h2
      linarith
  obtain ⟨s', hs', H3⟩ := gm_S2_4a hD (isCompact_sphere 0 α) (isCompact_sphere 0 1) hdisj hε1
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < min b (g / 4) / (2 * π) by positivity)
  set m : ℕ := n + 1 with hm
  have hm0 : 0 < m := Nat.succ_pos n
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have h2pm : 2 * π / m < min b (g / 4) := by
    have : (1 : ℝ) / (n + 1) * (2 * π) < min b (g / 4) := by
      rw [lt_div_iff₀ (by positivity)] at hn; exact hn
    rw [hm]; push_cast
    calc 2 * π / (n + 1) = 1 / (n + 1) * (2 * π) := by ring
      _ < _ := this
  have hstep : ∀ k, ‖ringPt ρ m k - ringPt ρ m (k + 1)‖ ≤ b := fun k => by
    refine (norm_circleMap_sub_circleMap_le hρ0 _ _).trans ?_
    have e : 2 * π * (k : ℕ) / m - 2 * π * ((k + 1 : ℕ) : ℝ) / m = -(2 * π / m) := by
      push_cast; ring
    rw [e, abs_neg, abs_of_pos (by positivity)]
    calc ρ * (2 * π / m) ≤ 1 * (2 * π / m) :=
          mul_le_mul_of_nonneg_right hρ1.le (by positivity)
      _ ≤ b := by rw [one_mul]; exact h2pm.le.trans (min_le_left _ _)
  have hmg : ρ * (2 * π / m) ≤ g / 4 :=
    calc ρ * (2 * π / m) ≤ 1 * (2 * π / m) :=
          mul_le_mul_of_nonneg_right hρ1.le (by positivity)
      _ ≤ g / 4 := by rw [one_mul]; exact h2pm.le.trans (min_le_right _ _)
  refine ⟨m * s / s', by positivity, fun P _ h hh r hr z => ?_⟩
  have hcr := hD.tightness.1 r hr
  have hgood : ∀ ω, (D (h ω)).IsLength →
      (∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1, g / 4 ≤ ‖u - v‖ →
        s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) <
          (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z)) →
      (∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1, ‖u - v‖ ≤ b →
        (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z) <
          s / 2 * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z)) →
      (∀ u ∈ sphere (0 : ℂ) α, ∀ v ∈ sphere (0 : ℂ) 1,
        s' * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) <
          (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z)) →
      ∀ x ∈ sphere z (α * r), ∀ y ∈ sphere z r,
        (D (h ω)).aroundDist {w | α * r < ‖w - z‖ ∧ ‖w - z‖ < r} (sphere z (α * r))
          (sphere z r) ≤ ENNReal.ofReal (m * s / s' * (D (h ω)).1 (x, y)) := by
    intro ω hlen e1 e2 e3 x hx y hy
    set q : ℝ := c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) with hq
    have hq0 : 0 < q := by positivity
    have hround := aroundDist_le_of_events hlen hr z hα0 hα1 (σ := s * q) (τ := s / 2 * q)
      (by positivity) (le_of_eq (by ring)) hm0 hstep hmg
      (fun u hu v hv huv => by have := e1 u hu v hv huv; rwa [mul_assoc] at this)
      (fun u hu v hv huv => by have := e2 u hu v hv huv; rwa [mul_assoc] at this)
    refine hround.trans (ENNReal.ofReal_le_ofReal ?_)
    have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    have hux : x = (r : ℂ) * ((x - z) / r) + z := by field_simp; ring
    have huy : y = (r : ℂ) * ((y - z) / r) + z := by field_simp; ring
    have hnorm : ∀ w : ℂ, ‖(w - z) / r‖ = ‖w - z‖ / r := fun w => by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hxu : (x - z) / r ∈ sphere (0 : ℂ) α := by
      rw [mem_sphere, dist_zero_right, hnorm, ← dist_eq_norm, mem_sphere.1 hx]
      field_simp
    have hyu : (y - z) / r ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere, dist_zero_right, hnorm, ← dist_eq_norm, mem_sphere.1 hy]
      field_simp
    have h3 := e3 _ hxu _ hyu
    rw [← hux, ← huy, mul_assoc] at h3
    rw [show m * s / s' * (D (h ω)).1 (x, y) = m * s * ((D (h ω)).1 (x, y) / s') by ring]
    have : q ≤ (D (h ω)).1 (x, y) / s' := by rw [le_div_iff₀ hs']; linarith
    have hms : 0 ≤ (m : ℝ) * s := by positivity
    calc (m : ℝ) * (s * q) = m * s * q := by ring
      _ ≤ m * s * ((D (h ω)).1 (x, y) / s') := mul_le_mul_of_nonneg_left this hms
  have hlenae := hD.length P h (isGFFPlusCont_of_wp hh)
  calc _ ≤ P (({ω | ¬ ∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1, g / 4 ≤ ‖u - v‖ →
          s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) <
            (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z)} ∪
        {ω | ¬ ∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1, ‖u - v‖ ≤ b →
          (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z) <
            s / 2 * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z)}) ∪
        {ω | ¬ ∀ u ∈ sphere (0 : ℂ) α, ∀ v ∈ sphere (0 : ℂ) 1,
          s' * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) <
            (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z)}) := by
        refine measure_mono_ae ?_
        filter_upwards [hlenae] with ω hlen hbad
        by_contra hcon
        simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hcon
        exact hbad (hgood ω hlen hcon.1.1 hcon.1.2 hcon.2)
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add_left (measure_union_le _ _) _
    _ < ε / 2 / 2 + ε / 2 / 2 + ε / 2 / 2 := by
        exact ENNReal.add_lt_add (ENNReal.add_lt_add (H1 P h hh r hr z) (H2 P h hh r hr z))
          (H3 P h hh r hr z)
    _ ≤ ε / 2 / 2 + ε / 2 / 2 + (ε / 2 / 2 + ε / 2 / 2) := add_le_add le_rfl le_self_add
    _ = ε := by rw [ENNReal.add_halves, ENNReal.add_halves]

end Tight
end GM
end LQGMetric
