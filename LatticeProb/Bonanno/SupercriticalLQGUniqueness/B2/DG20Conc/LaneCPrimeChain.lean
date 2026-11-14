/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeChain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeStep

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

theorem laneC_prime_five_chain {ξ : ℝ} {f : ℂ → ℝ}
    (side : Fin 4) (p : Fin 5 → ℝ → ℂ) (d : Fin 4 → ℝ → ℂ)
    (hp : ∀ i, AdmPath (laneCPrimeLongRect side i).toSet
      (laneCPrimeLongRect side i).side₁
      (laneCPrimeLongRect side i).side₂ (p i))
    (hd : ∀ i, AdmPath (laneCPrimeJoinRect side i).toSet
      (laneCPrimeJoinRect side i).side₁
      (laneCPrimeJoinRect side i).side₂ (d i)) :
    ∃ r : ℝ → ℂ,
      AdmPath (laneCPrimeWideRect side).toSet
        (laneCPrimeWideRect side).side₁
        (laneCPrimeWideRect side).side₂ r ∧
      lfppLen ξ f r ≤
        (((lfppLen ξ f (p 0) + lfppLen ξ f (d 0) + lfppLen ξ f (p 1)) +
          lfppLen ξ f (d 1) + lfppLen ξ f (p 2)) +
          lfppLen ξ f (d 2) + lfppLen ξ f (p 3)) +
          lfppLen ξ f (d 3) + lfppLen ξ f (p 4) := by
  have hzero : AdmPath (laneCPrimePrefixRect side 0).toSet
      (laneCPrimePrefixRect side 0).side₁
      (laneCPrimePrefixRect side 0).side₂ (p 0) := by
    simpa [laneC_prime_prefix_zero side] using hp 0
  obtain ⟨r₁, hr₁, h₁⟩ := laneC_prime_step (ξ := ξ) (f := f)
    side 0 hzero (hp 1) (hd 0)
  obtain ⟨r₂, hr₂, h₂⟩ := laneC_prime_step (ξ := ξ) (f := f)
    side 1 hr₁ (hp 2) (hd 1)
  obtain ⟨r₃, hr₃, h₃⟩ := laneC_prime_step (ξ := ξ) (f := f)
    side 2 hr₂ (hp 3) (hd 2)
  obtain ⟨r₄, hr₄, h₄⟩ := laneC_prime_step (ξ := ξ) (f := f)
    side 3 hr₃ (hp 4) (hd 3)
  refine ⟨r₄, ?_, ?_⟩
  · simpa [laneC_prime_prefix_four side] using hr₄
  · calc
      lfppLen ξ f r₄ ≤ lfppLen ξ f r₃ + lfppLen ξ f (d 3) +
          lfppLen ξ f (p 4) := h₄
      _ ≤ (lfppLen ξ f r₂ + lfppLen ξ f (d 2) + lfppLen ξ f (p 3)) +
          lfppLen ξ f (d 3) + lfppLen ξ f (p 4) :=
        by gcongr
      _ ≤ ((lfppLen ξ f r₁ + lfppLen ξ f (d 1) + lfppLen ξ f (p 2)) +
          lfppLen ξ f (d 2) + lfppLen ξ f (p 3)) +
          lfppLen ξ f (d 3) + lfppLen ξ f (p 4) :=
        by gcongr
      _ ≤ (((lfppLen ξ f (p 0) + lfppLen ξ f (d 0) + lfppLen ξ f (p 1)) +
          lfppLen ξ f (d 1) + lfppLen ξ f (p 2)) +
          lfppLen ξ f (d 2) + lfppLen ξ f (p 3)) +
          lfppLen ξ f (d 3) + lfppLen ξ f (p 4) := by
        gcongr

end SupercriticalLQGUniqueness.B2.DG20Conc
