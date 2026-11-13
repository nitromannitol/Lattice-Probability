/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CaraR4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR1
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR3Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.WeldingConsistency
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraExt

/-!
# EXT-CA node R4: the boundary extension at non-swallowed real points

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.R, node **R4**. Let `F` be a continuous extension
to `ℍ̄` of `revMap W t`. At a real point `x` not swallowed by time `t`, `F x` is the real flow
map `realRevMap W t x` (`eq_realRevMap_of_extension`); for `s ≤ t`, `F x` factors through the
real flow at time `s` and the extension `F'` of the shifted map (`eq_comp_of_extension`); and the
extension of a `RevExt` is real, of the sign of `x`, outside the swallowed interval `[a,b]`, with
limits `±∞` (`revExt_real_outside`).

Method: vertical limits `x + iy → x` (`y ↓ 0`), the boundary convergence of the reverse flow at
real points (`RealLine.tendsto_revMap_of_isRealRevSol`) and uniqueness of limits. Source for the
flow of real points: G. Lawler, *Conformally Invariant Processes in the Plane* (AMS 2005), §4.1,
p. 80 (paragraph after (4.11)).
-/

noncomputable section

open Set Filter Complex
open scoped Topology

namespace QuantumZipper

namespace CaraR

open RealLine

/-- The vertical approach `y ↦ x + i y` (`y ↓ 0`) tends to `x` within `ℍ`. -/
theorem tendsto_vertical_nhdsWithin_H (x : ℝ) :
    Tendsto (fun y : ℝ => (x : ℂ) + y * I) (𝓝[>] 0) (𝓝[H] (x : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : Continuous (fun y : ℝ => (x : ℂ) + y * I) := by fun_prop
    have := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y (hy : (0 : ℝ) < y)
    show 0 < ((x : ℂ) + y * I).im
    simpa using hy

/-- **R4.** At a real point not swallowed by time `t`, a continuous extension of `revMap W t`
equals the real flow map. -/
theorem eq_realRevMap_of_extension {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {F : ℂ → ℂ} (hEq : EqOn F (revMap W t) H) (hF : ContinuousOn F Hbar) {x : ℝ}
    (hx : x ∉ swallowedSet W t) : F x = realRevMap W t x := by
  obtain ⟨u, hu⟩ := not_mem_swallowedSet_iff.1 hx
  have h1 := tendsto_revMap_of_isRealRevSol hW hu ⟨ht, le_rfl⟩
  have hxH : (x : ℂ) ∈ Hbar := show 0 ≤ (x : ℂ).im by simp
  have h2 := (CA.Car.tendsto_nhdsWithin_H_of_extension hEq hF hxH).comp
    (tendsto_vertical_nhdsWithin_H x)
  rw [realRevMap_eq hW hu ht le_rfl]
  exact tendsto_nhds_unique h2 h1

/-- **R4, composition.** For `s ≤ t` and `x` not swallowed by time `s`, the extension `F` of
`revMap W t` at `x` is the extension `F'` of the shifted map `revMap W⁺ (t - s)` at the real point
`realRevMap W s x`. -/
theorem eq_comp_of_extension {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) {F F' : ℂ → ℂ} (hEq : EqOn F (revMap W t) H)
    (hF : ContinuousOn F Hbar) (hEq' : EqOn F' (revMap (fun r => W (s + r) - W s) (t - s)) H)
    (hF' : ContinuousOn F' Hbar) {x : ℝ} (hx : x ∉ swallowedSet W s) :
    F x = F' (realRevMap W s x) := by
  obtain ⟨u, hu⟩ := not_mem_swallowedSet_iff.1 hx
  have hxH : (x : ℂ) ∈ Hbar := show 0 ≤ (x : ℂ).im by simp
  have hpH : ((realRevMap W s x : ℝ) : ℂ) ∈ Hbar := show 0 ≤ ((realRevMap W s x : ℝ) : ℂ).im by
    simp
  have h1 := (CA.Car.tendsto_nhdsWithin_H_of_extension hEq hF hxH).comp
    (tendsto_vertical_nhdsWithin_H x)
  -- the inner flow tends to the real point within `ℍ`
  have hin : Tendsto (fun y : ℝ => revMap W s ((x : ℂ) + y * I)) (𝓝[>] 0)
      (𝓝[H] ((realRevMap W s x : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := tendsto_revMap_of_isRealRevSol hW hu ⟨hs, le_rfl⟩
      rwa [← realRevMap_eq hW hu hs le_rfl] at this
    · filter_upwards [self_mem_nhdsWithin] with y (hy : (0 : ℝ) < y)
      have hz : 0 < ((x : ℂ) + y * I).im := by simpa using hy
      exact lt_of_lt_of_le hz (im_le_im_revMap W hW _ hz hs)
  have h2 := (CA.Car.tendsto_nhdsWithin_H_of_extension hEq' hF' hpH).comp hin
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with y (hy : (0 : ℝ) < y)
  have hz : ((x : ℂ) + y * I) ∈ H := show 0 < ((x : ℂ) + y * I).im by simpa using hy
  exact (WeldingConsistency.revMap_comp hW hW0 hs hst hz).symm

/-- **R4 for `RevExt`.** Outside the swallowed interval `[a,b]` the extension is real, negative
to the left and positive to the right, and tends to `∓∞` at `∓∞`. -/
theorem revExt_real_outside {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    {γ : ℝ → ℂ} {F : ℂ → ℂ} (hF : RevExt W T γ F) {a b : ℝ} (hS : swallowedSet W T = Icc a b) :
    (∀ x : ℝ, x < a → (F x).im = 0 ∧ (F x).re < 0) ∧
      (∀ x : ℝ, b < x → (F x).im = 0 ∧ 0 < (F x).re) ∧
      Tendsto (fun x : ℝ => (F x).re) atTop atTop ∧
      Tendsto (fun x : ℝ => (F x).re) atBot atBot := by
  have h0 : (0 : ℝ) ∈ Icc a b := hS ▸ zero_mem_swallowedSet hW0 hT.le
  have hval : ∀ x : ℝ, x ∉ Icc a b → F x = realRevMap W T x := fun x hx =>
    eq_realRevMap_of_extension hW hT.le hF.eqOn hF.cont (hS ▸ hx)
  refine ⟨fun x hx => ?_, fun x hx => ?_, ?_, ?_⟩
  · have hxS : x ∉ Icc a b := fun h => absurd h.1 (not_le.2 hx)
    obtain ⟨u, hu⟩ := not_mem_swallowedSet_iff.1 (hS ▸ hxS)
    rw [hval x hxS, realRevMap_eq hW hu hT.le le_rfl]
    have := neg_of_isRealRevSol hu hT.le (by rw [hW0]; linarith [h0.1]) T ⟨hT.le, le_rfl⟩
    exact ⟨by simp, by simpa using this⟩
  · have hxS : x ∉ Icc a b := fun h => absurd h.2 (not_le.2 hx)
    obtain ⟨u, hu⟩ := not_mem_swallowedSet_iff.1 (hS ▸ hxS)
    rw [hval x hxS, realRevMap_eq hW hu hT.le le_rfl]
    have := pos_of_isRealRevSol hu hT.le (by rw [hW0]; linarith [h0.2]) T ⟨hT.le, le_rfl⟩
    exact ⟨by simp, by simpa using this⟩
  · refine (tendsto_realRevMap_atTop hW hT.le).congr' ?_
    filter_upwards [eventually_gt_atTop b] with x hx
    rw [hval x (fun h => absurd h.2 (not_le.2 hx)), Complex.ofReal_re]
  · refine (tendsto_realRevMap_atBot hW hT.le).congr' ?_
    filter_upwards [eventually_lt_atBot a] with x hx
    rw [hval x (fun h => absurd h.1 (not_le.2 hx)), Complex.ofReal_re]

end CaraR

end QuantumZipper
