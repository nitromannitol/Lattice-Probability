/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PaidDuality.AnnularRect at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PaidDuality.FiniteDuality




 



set_option autoImplicit false

namespace SupercriticalLQGUniqueness.Exponent.PaidDuality

open Set Metric
open scoped Convex ENNReal

 
def innerSquare : Set ℂ := Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (0 : ℝ) 1

 
def outerOpenSquare : Set ℂ := Set.Ioo (-1 : ℝ) 2 ×ℂ Set.Ioo (-1 : ℝ) 2

private theorem horizontal_inner {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    Set.Icc (0 : ℝ) 1 ×ℂ {y} ⊆ innerSquare := by
  intro z hz
  change z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ ({y} : Set ℝ) at hz
  change z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc (0 : ℝ) 1
  exact ⟨hz.1, by simpa only [Set.mem_singleton_iff] using hz.2 ▸ hy⟩

private theorem vertical_inner {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ({x} : Set ℝ) ×ℂ Set.Icc (0 : ℝ) 1 ⊆ innerSquare := by
  intro z hz
  change z.re ∈ ({x} : Set ℝ) ∧ z.im ∈ Set.Icc (0 : ℝ) 1 at hz
  change z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc (0 : ℝ) 1
  exact ⟨by simpa only [Set.mem_singleton_iff] using hz.1 ▸ hx, hz.2⟩

private theorem horizontal_outer {y : ℝ} (hy : y ≤ -1 ∨ 2 ≤ y) :
    Set.Icc (0 : ℝ) 1 ×ℂ {y} ⊆ outerOpenSquareᶜ := by
  intro z hz houter
  change z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ ({y} : Set ℝ) at hz
  change z.re ∈ Set.Ioo (-1 : ℝ) 2 ∧ z.im ∈ Set.Ioo (-1 : ℝ) 2 at houter
  have hzy : z.im = y := hz.2
  rcases houter.2 with ⟨hlo, hhi⟩
  rcases hy with hy | hy <;> linarith

private theorem vertical_outer {x : ℝ} (hx : x ≤ -1 ∨ 2 ≤ x) :
    ({x} : Set ℝ) ×ℂ Set.Icc (0 : ℝ) 1 ⊆ outerOpenSquareᶜ := by
  intro z hz houter
  change z.re ∈ ({x} : Set ℝ) ∧ z.im ∈ Set.Icc (0 : ℝ) 1 at hz
  change z.re ∈ Set.Ioo (-1 : ℝ) 2 ∧ z.im ∈ Set.Ioo (-1 : ℝ) 2 at houter
  have hzx : z.re = x := hz.1
  rcases houter.1 with ⟨hlo, hhi⟩
  rcases hx with hx | hx <;> linarith

 
theorem disconnects_central_radial {K : Set ℂ}
    (hK : LQGMetric.Disconnects K innerSquare outerOpenSquareᶜ)
    (k : Fin 4) :
    LQGMetric.Disconnects K (centralRadialTop k) (centralRadialBottom k) := by
  fin_cases k
  · exact hK.symm.mono Subset.rfl
      (horizontal_outer (y := 2) (Or.inr le_rfl))
      (horizontal_inner (y := 1) (by norm_num))
  · exact hK.mono Subset.rfl
      (horizontal_inner (y := 0) (by norm_num))
      (horizontal_outer (y := -1) (Or.inl le_rfl))
  · exact hK.mono Subset.rfl
      (vertical_inner (x := 0) (by norm_num))
      (vertical_outer (x := -1) (Or.inl le_rfl))
  · exact hK.symm.mono Subset.rfl
      (vertical_outer (x := 2) (Or.inr le_rfl))
      (vertical_inner (x := 1) (by norm_num))

 
theorem paid_central_rect_of_annular_segment_family {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℂ)
    (hsep : LQGMetric.Disconnects
      (⋃ i ∈ s, [a i -[ℝ] b i]) innerSquare outerOpenSquareᶜ)
    (k : Fin 4) (ξ : ℝ) (f : ℂ → ℝ) :
    ∃ P : ℝ → ℂ,
      LQGMetric.DDDF.AdmPath (centralRect k).toSet
        (centralRect k).side₁ (centralRect k).side₂ P ∧
      LQGMetric.lfppLen ξ f P ≤
        ∑ i ∈ s, LQGMetric.LFPP.segCost ξ f (a i) (b i) := by
  apply paid_central_rect_of_segment_cover k s a b
    (disconnects_central_radial hsep k) ?_ ξ f
  intro z hz
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp hz.1
  exact Set.mem_iUnion₂.mpr ⟨i, hi, ⟨hzi, hz.2⟩⟩

end SupercriticalLQGUniqueness.Exponent.PaidDuality

