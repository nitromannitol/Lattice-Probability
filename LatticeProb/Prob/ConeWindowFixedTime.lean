import LatticeProb.Prob.ConeWindowWitness
import LatticeProb.Prob.StationaryWindowCoverage

/-! # Fixed-time coverage by rational cone-window witnesses -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Enlarging the window preserves a rational-start cone witness. -/
theorem coneWindowCoverage_mono {a b l r x : ℝ}
    (hl : a ≤ l) (hr : r ≤ b) (z : C(ℝ, ℝ) × C(ℝ, ℝ))
    (h : (z, x) ∈ Prod.fst '' coneWindowWitness l r) :
    (z, x) ∈ Prod.fst '' coneWindowWitness a b := by
  obtain ⟨⟨⟨z', x'⟩, t⟩, ht, heq⟩ := h
  have hz : z' = z := congrArg Prod.fst heq
  have hx : x' = x := congrArg Prod.snd heq
  subst z'
  subst x'
  refine ⟨((z, x), t), ?_, rfl⟩
  rcases ht with ⟨hlx, hxt, htr, hex, hall⟩
  refine ⟨lt_of_le_of_lt hl hlx, hxt, le_trans htr hr, hex, ?_⟩
  intro q hq
  exact hall q (lt_of_lt_of_le hq hl)

/-- Joint coverage is measurable after completion for a finite law and a bounded
window of time. -/
theorem nullMeasurableSet_coneWindowCoverage_prod
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Z : Ω → C(ℝ, ℝ) × C(ℝ, ℝ)) (hZ : Measurable Z) (l r : ℝ) :
    NullMeasurableSet {p : Ω × ℝ | (Z p.1, p.2) ∈ Prod.fst '' coneWindowWitness l r}
      (P.prod (volume.restrict (Ioo l r))) := by
  exact nullMeasurableSet_preimage_coneWindowCoverage
    (P.prod (volume.restrict (Ioo l r))) (fun p => (Z p.1, p.2))
    ((hZ.comp measurable_fst).prodMk measurable_snd) l r

/-- Almost-every-time window coverage and translation invariance of the
almost-sure coverage events imply coverage of a fixed interior time. -/
theorem ae_coneWindowCoverage_fixedTime
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Z : Ω → C(ℝ, ℝ) × C(ℝ, ℝ)) (hZ : Measurable Z)
    (hcoverage : ∀ l r : ℝ, l < r → ∀ᵐ ω ∂P,
      ∀ᵐ t ∂volume.restrict (Ioo l r), (Z ω, t) ∈ Prod.fst '' coneWindowWitness l r)
    (hshift : ∀ l r t d : ℝ,
      (∀ᵐ ω ∂P, (Z ω, t) ∈ Prod.fst '' coneWindowWitness l r) →
      ∀ᵐ ω ∂P, (Z ω, t + d) ∈ Prod.fst '' coneWindowWitness (l + d) (r + d))
    {a u b : ℝ} (hau : a < u) (hub : u < b) :
    ∀ᵐ ω ∂P, (Z ω, u) ∈ Prod.fst '' coneWindowWitness a b := by
  apply ae_fixedTime_of_stationary_window_coverage P
    (fun l r t ω => (Z ω, t) ∈ Prod.fst '' coneWindowWitness l r)
  · intro l r _
    exact nullMeasurableSet_coneWindowCoverage_prod P Z hZ l r
  · exact hcoverage
  · exact hshift
  · intro l r a b t hl hr ω h
    exact coneWindowCoverage_mono hl hr (Z ω) h
  · exact hau
  · exact hub

end LatticeProb
