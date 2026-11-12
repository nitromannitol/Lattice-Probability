/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.AssociationSqrt at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.AssociationEvents
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The square-root trick

If finitely many events `A₁, …, A_k` (`k ≥ 1`) are positively associated,
`P(⋂ Aᵢ) ≥ ∏ P(Aᵢ)`, then
`max_i P(Aᵢᶜ) ≥ 1 - (1 - P(⋃ Aᵢᶜ))^{1/k}` (`LQGMetric.Pitt.sqrt_trick`,
`LQGMetric.Pitt.sqrt_trick_iSup`). This is the "square-root trick" in the form of
Ding–Dubédat–Dunlap–Falconet, *Tightness of Liouville first passage percolation for γ ∈ (0,2)*
(arXiv:1904.08021), Lemma 3.12 (`Lem:FKG`, tightness.tex lines 771–780), which cites
V. Tassion, *Crossing probabilities for Voronoi percolation* (arXiv:1410.6773), Prop. 4.1.
Proof (as in those sources): `1 - P(⋃ Aᵢᶜ) = P(⋂ Aᵢ) ≥ ∏ P(Aᵢ) ≥ (minᵢ P(Aᵢ))^k`.

`LQGMetric.Pitt.sqrt_trick_gaussian`: the case of increasing events `Aᵢ = {X ∈ Uᵢ}` of a
Gaussian vector with nonnegative covariances (DDDF's use, via Pitt's theorem).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real

namespace LQGMetric

namespace Pitt

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Square-root trick.** -/
theorem sqrt_trick [IsProbabilityMeasure P] {κ : Type*} [Fintype κ] [Nonempty κ] {A : κ → Set Ω}
    (hA : ∀ i, NullMeasurableSet (A i) P) (hass : ∏ i, P.real (A i) ≤ P.real (⋂ i, A i)) :
    ∃ i, 1 - (1 - P.real (⋃ i, (A i)ᶜ)) ^ (1 / (Fintype.card κ : ℝ)) ≤ P.real (A i)ᶜ := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => P.real (A i))
    Finset.univ_nonempty
  refine ⟨i₀, ?_⟩
  set m := P.real (A i₀)
  have hm : 0 ≤ m := measureReal_nonneg
  have hk : Fintype.card κ ≠ 0 := Fintype.card_ne_zero
  have hU : 1 - P.real (⋃ i, (A i)ᶜ) = P.real (⋂ i, A i) := by
    rw [← compl_iInter, probReal_compl_eq_one_sub₀ (NullMeasurableSet.iInter hA)]; ring
  have hprod : m ^ Fintype.card κ ≤ P.real (⋂ i, A i) := by
    refine le_trans ?_ hass
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => hm) fun i _ => hi₀ i (Finset.mem_univ _)
  have hroot : m ≤ (P.real (⋂ i, A i)) ^ (1 / (Fintype.card κ : ℝ)) := by
    calc m = (m ^ Fintype.card κ) ^ ((Fintype.card κ : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast hm hk).symm
      _ ≤ _ := by
          rw [one_div]
          exact Real.rpow_le_rpow (by positivity) hprod (by positivity)
  rw [hU, probReal_compl_eq_one_sub₀ (hA i₀)]
  linarith

end Pitt

end LQGMetric
