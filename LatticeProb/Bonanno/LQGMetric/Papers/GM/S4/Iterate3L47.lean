/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate3L47 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47MeasFinal
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Pos2

/-!
# GM Lemma 4.7, (4.12) ⇒ (4.13) per pair, without measurability hypotheses (handoff item 4)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.7, l. 1890–1912.
`gm_L4_7_complete` (P2-M2G) with its open measurability inputs discharged: `hnullGW`
(`gm_hnullGW`), `hnullGC` (`gm_hnullGC`, with a countable base `gm_exists_countable_base`) and
`hAvAn` (`gm_avoidRelAn`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **GM (4.12) ⇒ (4.13)** for one pair `(z, r)` at `𝓕_k` on a complete probability space, with
only GM's hypotheses (the comparison (4.12) on `G`) -/
theorem gm_L4_7_final (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c' : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c') {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [P.IsComplete] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {𝕫 𝕨 z : ℂ} (h𝕫𝕨 : 𝕫 ≠ 𝕨) {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {ℓ 𝕣 ε β lam1 lam4 ν r ρ : ℝ} {k : ℕ} {Rads : Set ℝ} (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε)
    (ha : 0 < lam4 * ε * 𝕣) (hρr : ρ ≤ r) (hr : r < lam4 * ε * 𝕣)
    {Er Ef Hit2 : Set Ω} {R : ℝ} (hEr : MeasurableSet Er) (hEf : MeasurableSet Ef)
    (hHit2 : MeasurableSet Hit2) (hsub : Hit2 ⊆ gmHitBall D h 𝕫 𝕨 η z r)
    {Λ : ℝ} (hΛ : 0 < Λ)
    (h42 : ∀ᵐ x ∂P, x ∈ gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R →
      (P⟦Er ∩ Hit2 | fieldSigmaClosed h (Metric.ball z ρ)ᶜ⟧) x ≤
      Λ * (P⟦Ef ∩ Hit2 | fieldSigmaClosed h (Metric.ball z ρ)ᶜ⟧) x) :
    ∀ᵐ x ∂P, (P⟦Er ∩ gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ Hit2 |
        gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)⟧) x *
        (gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R).indicator (fun _ => (1 : ℝ)) x ≤
      Λ * ((P⟦Ef ∩ gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ Hit2 |
        gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)⟧) x *
        (gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R).indicator (fun _ => (1 : ℝ)) x) := by
  obtain ⟨V, hVo, hV⟩ := gm_exists_countable_base
  have h1 : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
  have h2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hc₀ : 0 < 1 + k * ε ^ β := by positivity
  have hc : 1 + k * ε ^ β < 1 + k * ε ^ β + ε ^ (2 * β) := by linarith
  exact gm_L4_7_complete h38 hC24 hC27 hC14 hγ hγ2 hD hh h𝕫𝕨 hη hℓ𝕣 hε ha hρr hr hVo hV
    (fun u j n s => gm_hnullGW h38 hγ hγ2 hD P h hh 𝕫 𝕨 _ _ _ u j n s)
    (fun u i n s => gm_hnullGC h38 hC24 hC27 hC14 hγ hγ2 hD P h hh 𝕫 hℓ𝕣 hc₀ hc hVo u i n s)
    (gm_avoidRelAn 𝕫 z r) hEr hEf hHit2 hsub hΛ h42

end LQGMetric.GM
