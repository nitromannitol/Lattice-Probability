import LatticeProb.External.GreenQuantitative

/-!
# Quantitative Green values at all poles

The cited value estimates yield a uniform real-power bound on one almost-sure event
for all ambient lattice poles and all source-characterized Green columns.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal Classical

namespace LatticeProb.Percolation

/-- Rewrite the dimensional denominator as a single real power. -/
private theorem green_power_conversion (d : ℕ) (hd : 2 ≤ d) (η r C : ℝ) (hr : 0 < r) :
    C / (Real.rpow r (1 - η) * r ^ (d - 2)) =
      C * Real.rpow r (1 - (d : ℝ) + η) := by
  have hcast : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := Nat.cast_sub hd
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_natCast, ← Real.rpow_add hr, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hr)]
  congr 2
  rw [hcast]
  ring

/-- The cited Green-value estimates hold simultaneously at all ambient poles, with a
uniform real-power exponent and measurable threshold witnesses. -/
theorem exists_green_quantitative_field
    (input : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ κ : ℝ, ∃ hκ : 0 < κ, ∃ K : Vertex d → Configuration d → ℝ,
      (∀ y, Measurable (K y)) ∧
      ∀ η : ℝ, 0 < η → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧
        ∃ M : Vertex d → Configuration d → ℝ,
          (∀ y, Measurable (M y)) ∧ (∀ y ω, 0 ≤ M y ω) ∧
          (∀ (y : Vertex d) (R : ℝ), 0 ≤ R →
            latticeBondLaw d p {ω | R ≤ M y ω} ≤
              ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C))) ∧
          ∀ᵐ ω ∂latticeBondLaw d p,
            ∀ y : Vertex d, ∀ h : HasUniqueInfiniteOpenComponent ω,
              ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
                ∀ g : uniqueInfiniteComponent h → ℝ,
                  IsGreenColumn d hd (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
                  ∀ x : uniqueInfiniteComponent h,
                    ∀ z : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0},
                      z.val = latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y →
                      M y ω ≤ ‖z.val‖ →
                      |g x - continuumGreen d hd ⟨κ, hκ⟩ z - K y ω| ≤
                        C * Real.rpow ‖z.val‖ (1 - (d : ℝ) + η) := by
  obtain ⟨κ, hκ, htwo, hlarge⟩ := input d hd p hp hp1
  by_cases hdim : d = 2
  · obtain ⟨K, hK, hbound⟩ := htwo hdim
    refine ⟨κ, hκ, K, hK, ?_⟩
    intro η hη
    obtain ⟨C, s, hC, hs, hper⟩ := hbound η hη
    choose M hM hn ht he using fun y => (hper y).2
    refine ⟨C, s, hC, hs, M, hM, hn, ht, ?_⟩
    have hall := ae_all_iff.mpr he
    filter_upwards [hall] with ω hω
    intro y h hy g hg x z hz hthreshold
    have h := (hω y h hy g hg).2 x z hz hthreshold
    have hr : 0 < ‖z.val‖ := norm_pos_iff.mpr z.property
    have hc := green_power_conversion d hd η ‖z.val‖ C hr
    have hsub : d - 2 = 0 := by omega
    have hcast : (d : ℝ) = 2 := by exact_mod_cast hdim
    simp only [hsub, pow_zero, mul_one, hcast] at hc ⊢
    rw [← hc]
    exact h
  · have hdim3 : 3 ≤ d := by omega
    refine ⟨κ, hκ, fun _ _ => 0, ?_, ?_⟩
    · intro y
      exact measurable_const
    intro η hη
    obtain ⟨C, s, hC, hs, hper⟩ := hlarge hdim3 η hη
    choose M hM hn ht he using hper
    refine ⟨C, s, hC, hs, M, hM, hn, ht, ?_⟩
    have hall := ae_all_iff.mpr he
    filter_upwards [hall] with ω hω
    intro y h hy g hg x z hz hthreshold
    have hv := hω y h hy g hg x z hz hthreshold
    have hr : 0 < ‖z.val‖ := norm_pos_iff.mpr z.property
    rw [green_power_conversion d hd η ‖z.val‖ C hr] at hv
    simpa only [sub_zero] using hv

end LatticeProb.Percolation
