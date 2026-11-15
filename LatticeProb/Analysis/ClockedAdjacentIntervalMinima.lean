import LatticeProb.Analysis.AdjacentIntervalMinimaGlobal

/-! # Matching adjacent interval minima under a change of clock -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A change of clock and an injective phase map preserve countability of matching
adjacent interval minima. -/
theorem countable_clocked_adjacent_interval_minima (f : ℝ → ℝ) (hf : Continuous f)
    (ψ : ℝ ≃o ℝ) (ρ : ℝ → ℝ) (hρ : Function.Injective ρ)
    (δ D : ℝ) (hδ : 0 < δ) (hδD : δ < D)
    (hdist : ∀ x y, x ≠ y → IsLocalMin f x → IsLocalMin f y → f x ≠ f y) :
    {θ : ℝ | sInf (f '' Icc (ψ (ρ θ)) (ψ (ρ θ + δ))) =
      sInf (f '' Icc (ψ (ρ θ + δ)) (ψ (ρ θ + D)))}.Countable := by
  let g : ℝ → ℝ := f ∘ ψ
  have hg : Continuous g := hf.comp ψ.continuous
  have hgdist : ∀ x y, x ≠ y → IsLocalMin g x → IsLocalMin g y → g x ≠ g y := by
    intro x y hxy hx hy
    have hx' : IsLocalMin f (ψ x) := by
      have hx₀ : IsLocalMin g (ψ.symm (ψ x)) := by simpa only [ψ.symm_apply_apply] using hx
      have h := hx₀.comp_continuous (ψ.symm.continuous.continuousAt (x := ψ x))
      simpa only [g, Function.comp_def, ψ.apply_symm_apply, ψ.symm_apply_apply] using h
    have hy' : IsLocalMin f (ψ y) := by
      have hy₀ : IsLocalMin g (ψ.symm (ψ y)) := by simpa only [ψ.symm_apply_apply] using hy
      have h := hy₀.comp_continuous (ψ.symm.continuous.continuousAt (x := ψ y))
      simpa only [g, Function.comp_def, ψ.apply_symm_apply, ψ.symm_apply_apply] using h
    exact hdist (ψ x) (ψ y) (fun h => hxy (ψ.injective h)) hx' hy'
  have hc := (countable_adjacent_interval_minima g hg δ D hδ hδD hgdist).preimage hρ
  convert hc using 1
  ext θ
  change sInf (f '' Icc (ψ (ρ θ)) (ψ (ρ θ + δ))) =
      sInf (f '' Icc (ψ (ρ θ + δ)) (ψ (ρ θ + D))) ↔
    sInf (g '' Icc (ρ θ) (ρ θ + δ)) = sInf (g '' Icc (ρ θ + δ) (ρ θ + D))
  simp only [g, Set.image_comp, ψ.image_Icc]

/-- Matching minima on the intervals to either side of an injective phase
occur for only countably many phases, also after a change of clock. -/
theorem countable_clocked_adjacent_interval_minima_centered (f : ℝ → ℝ)
    (hf : Continuous f) (ψ : ℝ ≃o ℝ) (ρ : ℝ → ℝ) (hρ : Function.Injective ρ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hdist : ∀ x y, x ≠ y → IsLocalMin f x → IsLocalMin f y → f x ≠ f y) :
    {θ : ℝ | sInf (f '' Icc (ψ (ρ θ - a)) (ψ (ρ θ))) =
      sInf (f '' Icc (ψ (ρ θ)) (ψ (ρ θ + b)))}.Countable := by
  have hinj : Function.Injective (fun θ => ρ θ - a) := by
    intro x y hxy
    apply hρ
    linarith
  have h := countable_clocked_adjacent_interval_minima f hf ψ (fun θ => ρ θ - a)
    hinj a (a + b) ha (by linarith) hdist
  have hadd (θ : ℝ) : ρ θ - a + (a + b) = ρ θ + b := by ring
  convert h using 1
  ext θ
  simp only [sub_add_cancel, hadd]

end LatticeProb
