import LatticeProb.Prob.CorrelatedBMRationalDescent
import LatticeProb.LQG.ConsecutiveContactWindowCoverage

/-! # Strict consecutive contact windows at a fixed mesh

For a fixed real time `a`, each coordinate of the correlated Brownian pair `(L, R)` almost
surely takes values strictly below its value at `a` at times arbitrarily close to `a`, both
before and after `a` (Blumenthal's zero-one law for the recentred and the time-reversed
increments).

Consequently, for a fixed mesh `ε > 0`, almost surely for every label `x` the left and right
contact windows of the consecutive cells `η([ε(x-1), εx])` and `η([εx, ε(x+1)])` are both
strict: `max(inf L on the two cells) < L_{εx}` and likewise for `R`. For `γ ≤ √2` this gives,
almost surely, that every two consecutive cells intersect in exactly one nonsingleton connected
component, the component of `η(εx)`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- **Immediate descent at a fixed time.** For a fixed coordinate `i` and a fixed real time `a`,
almost surely the coordinate path takes values strictly below its value at `a` at times
arbitrarily close to `a`, both before and after `a`. -/
theorem ae_descends_at {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i : Fin 2) (a : ℝ) :
    ∀ᵐ ω ∂μ, (∀ u < a, ∃ w ∈ Set.Ioo u a, lrCoord i w ω < lrCoord i a ω) ∧
      ∀ u, a < u → ∃ w ∈ Set.Ioo a u, lrCoord i w ω < lrCoord i a ω := by
  have hL := ae_forall_pos_exists_lt_zero (reversedCoordinate_isBrownianReal hμ i a)
    (fun t => (measurable_lrCoord (i, a - (t : ℝ))).sub (measurable_lrCoord (i, a)))
  have hR := ae_forall_pos_exists_lt_zero (shiftedCoordinate_isBrownianReal hμ i a)
    (fun t => (measurable_lrCoord (i, a + (t : ℝ))).sub (measurable_lrCoord (i, a)))
  filter_upwards [hL, hR] with ω hωL hωR
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨t, ht0, htε, hneg⟩ := hωL (a - u) (sub_pos.2 hu)
    refine ⟨a - t, ⟨by linarith, by linarith⟩, ?_⟩
    have h' : lrCoord i (a - t) ω - lrCoord i a ω < 0 := hneg
    linarith
  · obtain ⟨t, ht0, htε, hneg⟩ := hωR (u - a) (sub_pos.2 hu)
    refine ⟨a + t, ⟨by linarith, by linarith⟩, ?_⟩
    have h' : lrCoord i (a + t) ω - lrCoord i a ω < 0 := hneg
    linarith

end LatticeProb.CorrelatedBM

namespace MatedCRTHarmonic.RouteM

/-- If a continuous contour takes values below `X(εx)` immediately before and immediately after
`εx`, the lower end of the contact window of the consecutive cells `x`, `x + 1` lies strictly
below `X(εx)`. -/
theorem dWinLo_consecutive_lt {X : ℝ → ℝ} (hX : Continuous X) {ε : ℝ} (hε : 0 < ε)
    {x y : ℤ} (hy : y = x + 1)
    (hleft : ∀ u < ε * x, ∃ w ∈ Ioo u (ε * x), X w < X (ε * x))
    (hright : ∀ u, ε * x < u → ∃ w ∈ Ioo (ε * x) u, X w < X (ε * x)) :
    dWinLo ε X x y < X (ε * x) := by
  have hy' : (y : ℝ) - 1 = x := by rw [hy]; push_cast; ring
  have hy'' : ε * (y : ℝ) = ε * x + ε := by rw [hy]; push_cast; ring
  have hx' : ε * ((x : ℝ) - 1) = ε * x - ε := by ring
  obtain ⟨w, hw, hwlt⟩ := hleft (ε * x - ε) (by linarith)
  obtain ⟨v, hv, hvlt⟩ := hright (ε * x + ε) (by linarith)
  obtain ⟨-, hbl⟩ := DAux.intervalInf_spec hX
    (show ε * ((x : ℝ) - 1) ≤ ε * x by rw [hx']; linarith)
  obtain ⟨-, hbr⟩ := DAux.intervalInf_spec hX
    (show ε * ((y : ℝ) - 1) ≤ ε * y by rw [hy', hy'']; linarith)
  unfold dWinLo
  refine max_lt (lt_of_le_of_lt (hbl w ⟨by rw [hx']; exact hw.1.le, hw.2.le⟩) hwlt) ?_
  exact lt_of_le_of_lt (hbr v ⟨by rw [hy']; exact hv.1.le, by rw [hy'']; exact hv.2.le⟩) hvlt

end MatedCRTHarmonic.RouteM

namespace MatedCRTHarmonic.MoTInput

open MatedCRT RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- For a fixed mesh, almost surely the left and right contact windows of every two consecutive
cells are strict. -/
theorem ae_consecutive_windows_strict
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ x : ℤ,
      dWinLo ε (lCoord (bm ω)) x (x + 1) < lCoord (bm ω) (ε * x) ∧
        dWinLo ε (rCoord (bm ω)) x (x + 1) < rCoord (bm ω) (ε * x) := by
  have h : ∀ᵐ p ∂(P.map bm), ∀ x : ℤ, ∀ i : Fin 2,
      (∀ u < ε * x, ∃ w ∈ Ioo u (ε * x), lrCoord i w p < lrCoord i (ε * x) p) ∧
      ∀ u, ε * x < u → ∃ w ∈ Ioo (ε * x) u, lrCoord i w p < lrCoord i (ε * x) p :=
    ae_all_iff.2 fun x => ae_all_iff.2 fun i =>
      LatticeProb.CorrelatedBM.ae_descends_at D.boundaryLawBM i (ε * x)
  filter_upwards [ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable h] with ω hω x
  obtain ⟨hl1, hl2⟩ := hω x 0
  obtain ⟨hr1, hr2⟩ := hω x 1
  refine ⟨dWinLo_consecutive_lt continuous_lCoord hε rfl ?_ ?_,
    dWinLo_consecutive_lt continuous_rCoord hε rfl ?_ ?_⟩
  · simpa [MatedCRT.lrCoord, lCoord] using hl1
  · simpa [MatedCRT.lrCoord, lCoord] using hl2
  · simpa [MatedCRT.lrCoord, rCoord] using hr1
  · simpa [MatedCRT.lrCoord, rCoord] using hr2

/-- For `0 < γ ≤ √2` and a fixed mesh `ε > 0`, almost surely every two consecutive cells
`η([ε(x-1), εx])` and `η([εx, ε(x+1)])` intersect in exactly one nonsingleton connected
component, the component of `η(εx)`. -/
theorem ae_consecutive_contact_components_count_one_of_le_sqrt_two_fixed_mesh
    (hγ0 : 0 < γ) (hγ : γ ≤ Real.sqrt 2)
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ x : ℤ,
      let S := (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * (((x + 1 : ℤ) : ℝ) - 1)) (ε * ((x + 1 : ℤ) : ℝ))
      LatticeProb.nonSingletonComponents S = {connectedComponentIn S (η ω (ε * x))} ∧
        (LatticeProb.nonSingletonComponents S).ncard = 1 ∧
        (LatticeProb.nonSingletonComponents S).encard = 1 := by
  filter_upwards [ae_consecutive_contact_components_count_one_of_le_sqrt_two hγ0 hγ D,
    ae_consecutive_windows_strict D hε] with ω h1 h2 x
  exact h1 ε x (x + 1) hε rfl (Or.inl (h2 x).1)

end MatedCRTHarmonic.MoTInput
