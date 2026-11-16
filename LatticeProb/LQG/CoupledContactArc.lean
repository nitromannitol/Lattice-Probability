import LatticeProb.LQG.CoupledContactWindow
import LatticeProb.LQG.CouplingSharedSegmentFrontiers
import LatticeProb.Topology.CompactIntervalImageArc

/-! # Contact arcs for coupled area-parametrized curves -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal unitInterval

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Every strict left contour window contains an arc in both cell frontiers. -/
theorem ae_left_contact_window_arc
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ) (a b : ℝ),
      0 < ε → x + 1 < y → dWinLo ε (lCoord (bm ω)) x y < a →
      b < dWinHi ε (lCoord (bm ω)) x y → a < b →
      ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
        range p ⊆ (fun level => η ω (ellMinus (bm ω) (ε * x) level)) '' Icc a b ∧
        (∀ t, p t ∈ frontier ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x))) ∧
        (∀ t, p t ∈ frontier ((η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y))) := by
  filter_upwards [ae_left_contact_window D, ae_shared_frontiers_of_coupling D] with ω hc hf
  intro ε x y a b hε hxy ha hb hab
  obtain ⟨hcont, hcell, hinf⟩ := hc ε x y a b hε hxy ha hb hab
  have hx : ε * ((x : ℝ) - 1) < ε * x := by nlinarith
  have hy : ε * ((y : ℝ) - 1) < ε * y := by nlinarith
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have horder : ε * x ≤ ε * ((y : ℝ) - 1) := by nlinarith
  have hfront := (hf _ _ _ _ hx horder hy).2.1
  obtain ⟨z, hz, w, hw, hne⟩ := hinf.nontrivial
  obtain ⟨p, hp, hi, _, _, hr⟩ :=
    LatticeProb.exists_arc_between_points_in_compact_interval_image _ hcont hz hw hne
  refine ⟨⟨p, hp⟩, hi, hr, ?_, ?_⟩
  · intro t
    have h := hr ⟨t, rfl⟩
    obtain ⟨level, hl, heq⟩ := h
    change p t ∈ _
    rw [← heq]
    exact (hfront ▸ hcell level hl).1
  · intro t
    have h := hr ⟨t, rfl⟩
    obtain ⟨level, hl, heq⟩ := h
    change p t ∈ _
    rw [← heq]
    exact (hfront ▸ hcell level hl).2

/-- Every strict right contour window contains an arc in both cell frontiers. -/
theorem ae_right_contact_window_arc
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ) (a b : ℝ),
      0 < ε → x + 1 < y → dWinLo ε (rCoord (bm ω)) x y < a →
      b < dWinHi ε (rCoord (bm ω)) x y → a < b →
      ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
        range p ⊆ (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) '' Icc a b ∧
        (∀ t, p t ∈ frontier ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x))) ∧
        (∀ t, p t ∈ frontier ((η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y))) := by
  filter_upwards [ae_right_contact_window D, ae_shared_frontiers_of_coupling D] with ω hc hf
  intro ε x y a b hε hxy ha hb hab
  obtain ⟨hcont, hcell, hinf⟩ := hc ε x y a b hε hxy ha hb hab
  have hx : ε * ((x : ℝ) - 1) < ε * x := by nlinarith
  have hy : ε * ((y : ℝ) - 1) < ε * y := by nlinarith
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have horder : ε * x ≤ ε * ((y : ℝ) - 1) := by nlinarith
  have hfront := (hf _ _ _ _ hx horder hy).2.1
  obtain ⟨z, hz, w, hw, hne⟩ := hinf.nontrivial
  obtain ⟨p, hp, hi, _, _, hr⟩ :=
    LatticeProb.exists_arc_between_points_in_compact_interval_image _ hcont hz hw hne
  refine ⟨⟨p, hp⟩, hi, hr, ?_, ?_⟩
  · intro t
    have h := hr ⟨t, rfl⟩
    obtain ⟨level, hl, heq⟩ := h
    change p t ∈ _
    rw [← heq]
    exact (hfront ▸ hcell level hl).1
  · intro t
    have h := hr ⟨t, rfl⟩
    obtain ⟨level, hl, heq⟩ := h
    change p t ∈ _
    rw [← heq]
    exact (hfront ▸ hcell level hl).2

end MatedCRTHarmonic.MoTInput
