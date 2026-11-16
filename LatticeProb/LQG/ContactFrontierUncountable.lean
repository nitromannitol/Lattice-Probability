import LatticeProb.LQG.CoupledContactFrontier
import Mathlib.Analysis.Real.Cardinality

/-! # Uncountable contact-frontier components -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace LatticeProb.Topology

/-- A preconnected metric set with two distinct points is uncountable. -/
theorem not_countable_of_isPreconnected_of_ne {X : Type*} [MetricSpace X]
    {K : Set X} (hK : IsPreconnected K) {x y : X}
    (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y) : ¬ K.Countable := by
  intro hcount
  let d : X → ℝ := fun z => dist z x
  have hd : Continuous d := continuous_id.dist continuous_const
  have himage : IsPreconnected (d '' K) := hK.image d hd.continuousOn
  have h0 : (0 : ℝ) ∈ d '' K := ⟨x, hx, by simp [d]⟩
  have hy' : dist y x ∈ d '' K := ⟨y, hy, rfl⟩
  have hsub : Icc (0 : ℝ) (dist y x) ⊆ d '' K := himage.ordConnected.out h0 hy'
  have hi : (Icc (0 : ℝ) (dist y x)).Countable := (hcount.image d).mono hsub
  have hle := Cardinal.Real.Icc_countable_iff.mp hi
  exact (not_le_of_gt (dist_pos.mpr (Ne.symm hxy))) hle

end LatticeProb.Topology

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Left contour windows lie in uncountable components of the shared frontier. -/
theorem ae_left_contact_frontier_component_uncountable
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ) (a b : ℝ),
      0 < ε → x + 1 < y → dWinLo ε (lCoord (bm ω)) x y < a →
      b < dWinHi ε (lCoord (bm ω)) x y → a < b →
      let f := fun level => η ω (ellMinus (bm ω) (ε * x) level)
      let S := frontier ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∩
        frontier ((η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y))
      ∃ C ∈ connectedComponentIn S '' S, ¬ C.Countable ∧ f '' Icc a b ⊆ C := by
  filter_upwards [ae_left_contact_continuum D, ae_left_contact_frontier_component D] with ω hc hf
  intro ε x y a b hε hxy ha hb hab
  obtain ⟨_, hconn, _, hinf, _⟩ := hc ε x y a b hε hxy ha hb hab
  obtain ⟨C, hC, _, hsub⟩ := hf ε x y a b hε hxy ha hb hab
  obtain ⟨p, hp, q, hq, hpq⟩ := hinf.nontrivial
  exact ⟨C, hC, fun hcount =>
    LatticeProb.Topology.not_countable_of_isPreconnected_of_ne hconn.isPreconnected hp hq hpq
      (hcount.mono hsub), hsub⟩

/-- Right contour windows lie in uncountable components of the shared frontier. -/
theorem ae_right_contact_frontier_component_uncountable
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ) (a b : ℝ),
      0 < ε → x + 1 < y → dWinLo ε (rCoord (bm ω)) x y < a →
      b < dWinHi ε (rCoord (bm ω)) x y → a < b →
      let f := fun level => η ω (rhoMinus (bm ω) (ε * x) level)
      let S := frontier ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∩
        frontier ((η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y))
      ∃ C ∈ connectedComponentIn S '' S, ¬ C.Countable ∧ f '' Icc a b ⊆ C := by
  filter_upwards [ae_right_contact_continuum D, ae_right_contact_frontier_component D] with ω hc hf
  intro ε x y a b hε hxy ha hb hab
  obtain ⟨_, hconn, _, hinf, _⟩ := hc ε x y a b hε hxy ha hb hab
  obtain ⟨C, hC, _, hsub⟩ := hf ε x y a b hε hxy ha hb hab
  obtain ⟨p, hp, q, hq, hpq⟩ := hinf.nontrivial
  exact ⟨C, hC, fun hcount =>
    LatticeProb.Topology.not_countable_of_isPreconnected_of_ne hconn.isPreconnected hp hq hpq
      (hcount.mono hsub), hsub⟩

end MatedCRTHarmonic.MoTInput
