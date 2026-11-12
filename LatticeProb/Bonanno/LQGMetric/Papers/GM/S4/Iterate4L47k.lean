/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate4L47k at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3L47
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3Norm

/-!
# GM Lemma 4.7 per pair from Theorem 4.2 (4) (DEC-89, packet B, pair level)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.7, l. 1890–1912
(GM assume `λ₃ = 1`, l. 1611: the conditioning ball is `B_{λ₃ r}(z) = B_r(z)`); Thm 4.2 (4),
(4.2) (l. 1562–1566). Decisions D79 (condition (4) is modulo additive constants; far
normalization `h(ψ₀) = 0`, `fieldSigmaClosed_eq_fieldSigmaClosed0`) and D89b (`λ₃ ≤ 1`: the
conditioning radius `ρ = λ₃ r ≤ r`).

* `gm_h42_of_cond4`: (4.2) modulo constants gives GM's (4.12) for `σ(h|_{ℂ∖B_ρ(z)})` when the
  field is normalized far away;
* `gm_L4_7_pair_of_cond4`: (4.13) for one pair, from (4) (`gm_L4_7_final`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **(4.2) ⇒ (4.12)** under the far normalization `h(ψ₀) = 0`, `supp ψ₀ ⊆ K` (D79) -/
theorem gm_h42_of_cond4 {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    {ψ₀ : TestC} (hψ₀ : ∫ x, ψ₀ x = 1) (h0 : ∀ ω, h ω ψ₀ = 0) {K : Set ℂ}
    (hK : tsupport (ψ₀ : ℂ → ℝ) ⊆ K) {Er Ef Hit : Set Ω} {Λ : ℝ} (hΛ : 0 < Λ)
    (h4 : (fun ω => Λ⁻¹ * (P[(Er ∩ Hit).indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K]) ω)
      ≤ᵐ[P] P[(Ef ∩ Hit).indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h K]) :
    ∀ᵐ x ∂P, (P⟦Er ∩ Hit | fieldSigmaClosed h K⟧) x ≤
      Λ * (P⟦Ef ∩ Hit | fieldSigmaClosed h K⟧) x := by
  rw [fieldSigmaClosed_eq_fieldSigmaClosed0 hψ₀ h0 hK]
  filter_upwards [h4] with x hx
  have := mul_le_mul_of_nonneg_left hx hΛ.le
  rwa [← mul_assoc, mul_inv_cancel₀ hΛ.ne', one_mul] at this

/-- **GM (4.13) for one pair from Theorem 4.2 (4)** (proof of Lemma 4.7, l. 1890–1912), with the
conditioning radius `ρ ≤ r` (`ρ = λ₃ r`, `λ₃ ≤ 1`, D89b) and the far normalization (D79) -/
theorem gm_L4_7_pair_of_cond4 (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c' : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c') {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [P.IsComplete] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {𝕫 𝕨 z : ℂ} (h𝕫𝕨 : 𝕫 ≠ 𝕨) {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {ℓ 𝕣 ε β lam1 lam4 ν r ρ : ℝ} {k : ℕ} {Rads : Set ℝ} (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε)
    (ha : 0 < lam4 * ε * 𝕣) (hρr : ρ ≤ r) (hr : r < lam4 * ε * 𝕣)
    {Er Ef Hit2 : Set Ω} {R : ℝ} (hEr : MeasurableSet Er) (hEf : MeasurableSet Ef)
    (hHit2 : MeasurableSet Hit2) (hsub : Hit2 ⊆ gmHitBall D h 𝕫 𝕨 η z r)
    {Λ : ℝ} (hΛ : 0 < Λ) {ψ₀ : TestC} (hψ₀ : ∫ x, ψ₀ x = 1) (h0 : ∀ ω, h ω ψ₀ = 0)
    (hψK : tsupport (ψ₀ : ℂ → ℝ) ⊆ (Metric.ball z ρ)ᶜ)
    (h4 : (fun ω => Λ⁻¹ * (P[(Er ∩ Hit2).indicator (fun _ => (1 : ℝ)) |
        fieldSigmaClosed0 h (Metric.ball z ρ)ᶜ]) ω) ≤ᵐ[P]
      P[(Ef ∩ Hit2).indicator (fun _ => (1 : ℝ)) | fieldSigmaClosed0 h (Metric.ball z ρ)ᶜ]) :
    ∀ᵐ x ∂P, (P⟦Er ∩ gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ Hit2 |
        gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)⟧) x *
        (gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R).indicator (fun _ => (1 : ℝ)) x ≤
      Λ * ((P⟦Ef ∩ gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ Hit2 |
        gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)⟧) x *
        (gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R).indicator (fun _ => (1 : ℝ)) x) := by
  have H := gm_h42_of_cond4 hψ₀ h0 hψK hΛ h4
  exact gm_L4_7_final h38 hC24 hC27 hC14 hγ hγ2 hD hh h𝕫𝕨 hη hℓ𝕣 hε ha hρr hr hEr hEf hHit2
    hsub hΛ (by filter_upwards [H] with x hx _; exact hx)

end LQGMetric.GM
