/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L47MeasFinal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47Final
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47MeasF
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47MeasG

/-!
# GM Lemma 4.7, (4.12) ⇒ (4.13), on a complete probability space (D70, `decisions/DEC-47.md`)

GM, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 4.7, l. 1890–1912.
`gm_L4_7_complete` is `gm_L4_7_of_null_G` (P2-L47) with the four measurability inputs that the
non-complete model could not supply discharged under `[P.IsComplete]` (decision D70):

* `hF : 𝓕_k ≤ mΩ` — `gm_sigF_le` (`L47MeasF.lean`), with `η` measurable by
  `gm_measurable_geod_of_complete` (no hypothesis on `η` beyond GM's "a.s. the unique geodesic");
* `hStab` — `gm_measurableSet_stabEv`; `hHit` — `gm_measurableSet_hitBall` (`L47MeasA.lean`);
* `hG₀F : G ∈ 𝓕_k` — `gm_G0_measurableSet_sigF` (`L47MeasG.lean`), surely.

`hHit2` (the caller's sub-event of `Hit`) stays a hypothesis; for hit events of `η` with open sets
it is `gm_measurableSet_hitOpen` + `gm_measurable_geod_of_complete`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **GM (4.12) ⇒ (4.13)** for one pair `(z, r)` at `𝓕_k` on a complete probability space -/
theorem gm_L4_7_complete (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4) (hC27 : CONFLem2_7)
    (hC14 : CONFThm1_4) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c' : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c') {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [P.IsComplete] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {𝕫 𝕨 z : ℂ}
    (h𝕫𝕨 : 𝕫 ≠ 𝕨) {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {ℓ 𝕣 ε β lam1 lam4 ν r ρ : ℝ} {k : ℕ} {Rads : Set ℝ} (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε)
    (ha : 0 < lam4 * ε * 𝕣) (hρr : ρ ≤ r) (hr : r < lam4 * ε * 𝕣)
    {V : ℕ → Set ℂ} (hVo : ∀ n, IsOpen (V n))
    (hV : ∀ (x : ℂ) (O : Set ℂ), IsOpen O → x ∈ O → ∃ n, x ∈ V n ∧ V n ⊆ O)
    (hnullGW : ∀ (u : unitInterval) (j : Bool × ℚ) (n : ℕ) (s : Finset (ℤ × ℤ)),
      NullMeasurableSet
        (gmGeodWSet D 𝕫 𝕨 (ℓ * 𝕣) (1 + k * ε ^ β) (1 + k * ε ^ β + ε ^ (2 * β)) u j ∩
        {g | dyadicHull n (gmKt D 𝕫 (ℓ * 𝕣) (1 + k * ε ^ β + ε ^ (2 * β)) g) =
          LocalEvent.hullFin n s}) (P.map h))
    (hnullGC : ∀ (u : unitInterval) (i : (Bool × ℚ) × Finset ℕ × Finset ℕ) (n : ℕ)
      (s : Finset (ℤ × ℤ)),
      NullMeasurableSet ({g | gmGeodCEv V (D g) 𝕫 (tauD (D g) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β))
        (tauD (D g) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β + ε ^ (2 * β))) u i} ∩
        {g | dyadicHull n (gmKt D 𝕫 (ℓ * 𝕣) (1 + k * ε ^ β + ε ^ (2 * β)) g) =
          LocalEvent.hullFin n s}) (P.map h))
    (hAvAn : GMAvoidRelAn 𝕫 z r)
    {Er Ef Hit2 : Set Ω} {R : ℝ} (hEr : MeasurableSet Er) (hEf : MeasurableSet Ef)
    (hHit2 : MeasurableSet Hit2)
    (hsub : Hit2 ⊆ gmHitBall D h 𝕫 𝕨 η z r)
    {Λ : ℝ} (hΛ : 0 < Λ)
    (h42 : ∀ᵐ x ∂P, x ∈ gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R →
      (P⟦Er ∩ Hit2 | fieldSigmaClosed h (Metric.ball z ρ)ᶜ⟧) x ≤
      Λ * (P⟦Ef ∩ Hit2 | fieldSigmaClosed h (Metric.ball z ρ)ᶜ⟧) x) :
    ∀ᵐ x ∂P, (P⟦Er ∩ gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ Hit2 |
        gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)⟧) x *
        (gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R).indicator (fun _ => (1 : ℝ)) x ≤
      Λ * ((P⟦Ef ∩ gmStabEv D h 𝕫 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r ∩ Hit2 |
        gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)⟧) x *
        (gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R).indicator (fun _ => (1 : ℝ)) x) :=
  gm_L4_7_of_null_G h38 hC24 hC27 hC14 hγ hγ2 hD hh h𝕫𝕨 hη hℓ𝕣 hε ha hρr hr hVo hV hnullGW hnullGC
    hAvAn (gm_sigF_le h38 hγ hγ2 hD hh hη ℓ 𝕣 ε β k) hEr hEf
    (gm_measurableSet_stabEv h38 hC24 hC27 hC14 hγ hγ2 hD hh hAvAn hε ha)
    (gm_measurableSet_hitBall D h h𝕫𝕨 (gm_measurable_geod_of_complete hD hh hη) z r) hHit2 hsub
    (gm_G0_measurableSet_sigF D h 𝕫 𝕨 η ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R ha) hΛ h42

end LQGMetric.GM
