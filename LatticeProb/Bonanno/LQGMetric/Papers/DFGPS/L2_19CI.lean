/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_19CI at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.BilipLocal
import LatticeProb.Bonanno.LQGMetric.Prob.CondIndepUnion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.19: the conditional-independence step (weak union up to null events)

The proof of DFGPS Lemma 2.19 (`lem-inside-circle`, arXiv:1905.00380,
`lqg-metric-estimates-final.tex` T:1182–1206) passes from conditioning on `h|_{cl V}` to
conditioning on `h̃|_{cl V}` (T:1196–1198: "our assumption implies that `D_h(·,·;V)` is
conditionally independent from the pair … given `h̃|_{cl V}` (instead of just `h|_{cl V}`)") and
then enlarges both sides by `σ(h̃|_{cl V})`-measurable data (T:1200–1204). The abstract statement
is the weak-union property of conditional independence (Kallenberg, *Foundations of Modern
Probability*, 2nd ed., Prop. 6.8; not in `literature/`, cited for the statement), here up to null
events (`GM.Bilip.aeClosure`), since in our setting the relations between `h`, `h̃` and the circle
averages hold only almost surely.

* `condExp_sandwich`: `G ≤ H ≤ K` up to null events and `E[f|K] = E[f|G]` give `E[f|H] = E[f|G]`.
* `condIndepEv_sup_cond`: `A ⟂ B | G ⟹ A ∨ G ⟂ B ∨ G | G` (from `condIndepEv_sup_of_condIndepEv`).
* `condIndepEv_transfer`: the weak-union transfer used at T:1196–1204.

Proofs: own elementary arguments (set integrals of conditional expectations; DEVIATIONS entry
DFB9-1).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric.DFGPS.L219

open GM.Bilip

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- if `G ≤ H` and every event of `H` is a.s. an event of `K`, and `E[f | K] = E[f | G]`, then
`E[f | H] = E[f | G]` -/
lemma condExp_sandwich [IsFiniteMeasure μ] {G H K : MeasurableSpace Ω} (hGH : G ≤ H)
    (hH : H ≤ mΩ) (hK : K ≤ mΩ) (hHK : H ≤ aeClosure μ K) {f : Ω → ℝ} (hf : Integrable f μ)
    (hKG : μ[f|K] =ᵐ[μ] μ[f|G]) : μ[f|H] =ᵐ[μ] μ[f|G] := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq hH hf
    (fun s _ _ => integrable_condExp.integrableOn) ?_
    ((stronglyMeasurable_condExp.mono hGH).aestronglyMeasurable)).symm
  intro s hs _
  obtain ⟨t, ht, hst⟩ := hHK s hs
  rw [setIntegral_congr_set hst, setIntegral_congr_set hst, ← setIntegral_condExp hK hf ht]
  exact setIntegral_congr_ae (hK t ht) (hKG.mono fun x hx _ => hx.symm)

/-- `A ⟂ C | K` when `C ≤ K` -/
lemma condIndepEv_of_le_cond [IsFiniteMeasure μ] {K A C : MeasurableSpace Ω} (hK : K ≤ mΩ)
    (hA : A ≤ mΩ) (hC : C ≤ K) : CondIndepEv K A C μ :=
  (condIndepEv_of_le_aeClosure hK (hC.trans (le_aeClosure K))
    (hA.trans (le_aeClosure mΩ))).symm

/-- `A ⟂ B | G ⟹ A ∨ G ⟂ B ∨ G | G` -/
lemma condIndepEv_sup_cond [IsProbabilityMeasure μ] {G A B : MeasurableSpace Ω} (hG : G ≤ mΩ)
    (hA : A ≤ mΩ) (hB : B ≤ mΩ) (h : CondIndepEv G A B μ) :
    CondIndepEv G (A ⊔ G) (B ⊔ G) μ := by
  have h1 : CondIndepEv G A (B ⊔ G) μ :=
    condIndepEv_sup_of_condIndepEv hG hA hB hG h (condIndepEv_of_le_cond hG hA le_rfl)
      (condIndepEv_of_le_cond (sup_le hA hG) hB le_sup_right)
  have h2 : CondIndepEv G (B ⊔ G) (A ⊔ G) μ :=
    condIndepEv_sup_of_condIndepEv hG (sup_le hB hG) hA hG h1.symm
      (condIndepEv_of_le_cond hG (sup_le hB hG) le_rfl)
      (condIndepEv_of_le_cond (sup_le (sup_le hB hG) hG) hA le_sup_right)
  exact h2.symm

/-- **Weak union, up to null events** (Kallenberg, *Foundations of Modern Probability*, Prop. 6.8
in the form used at DFGPS T:1196–1198): if `A ⟂ B | G` and, up to null events,
`G ≤ G' ≤ B ∨ G`, `A' ≤ A ∨ G'`, `B' ≤ B ∨ G'`, then `A' ⟂ B' | G'`. -/
theorem condIndepEv_transfer [IsProbabilityMeasure μ] {G A B G' A' B' : MeasurableSpace Ω}
    (hG : G ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ) (hG' : G' ≤ mΩ)
    (h : CondIndepEv G A B μ) (h1 : G ≤ aeClosure μ G') (h2 : G' ≤ aeClosure μ (B ⊔ G))
    (h3 : A' ≤ aeClosure μ (A ⊔ G')) (h4 : B' ≤ aeClosure μ (B ⊔ G')) :
    CondIndepEv G' A' B' μ := by
  have hK : B ⊔ G ≤ mΩ := sup_le hB hG
  have hBG' : B ⊔ G' ≤ mΩ := sup_le hB hG'
  -- Markov form at `G`
  have hM : ∀ a, MeasurableSet[A] a → μ⟦a | B ⊔ G⟧ =ᵐ[μ] μ⟦a | G⟧ := by
    intro a ha
    have := condExp_sup_eq_of_condIndepEv hG hK hA
      ((condIndepEv_sup_cond hG hA hB h).symm.mono le_rfl le_sup_left) ha
    rwa [sup_assoc, sup_idem] at this
  have hAB : CondIndepEv G' A B μ := by
    refine condIndepEv_of_condExp_sup_eq hG' hA hB fun a ha => ?_
    have hi := integrable_indOne (μ := μ) (hA a ha)
    -- `E[a | G ∨ G'] = E[a | G]` and `= E[a | G']`
    have e1 : μ⟦a | G ⊔ G'⟧ =ᵐ[μ] μ⟦a | G⟧ :=
      condExp_sandwich le_sup_left (sup_le hG hG') hK
        (sup_le ((le_sup_right : G ≤ B ⊔ G).trans (le_aeClosure _)) h2) hi (hM a ha)
    have e2 : μ⟦a | G ⊔ G'⟧ =ᵐ[μ] μ⟦a | G'⟧ :=
      condExp_sandwich le_sup_right (sup_le hG hG') hG' (sup_le h1 (le_aeClosure _)) hi
        EventuallyEq.rfl
    -- `E[a | B ∨ G ∨ G'] = E[a | G]` and `= E[a | B ∨ G']`
    have e3 : μ⟦a | (B ⊔ G) ⊔ G'⟧ =ᵐ[μ] μ⟦a | G⟧ :=
      (condExp_sandwich le_sup_left (sup_le hK hG') hK (sup_le (le_aeClosure _) h2) hi
        EventuallyEq.rfl).trans (hM a ha)
    have e4 : μ⟦a | (B ⊔ G) ⊔ G'⟧ =ᵐ[μ] μ⟦a | B ⊔ G'⟧ :=
      condExp_sandwich (sup_le (le_sup_left.trans le_sup_left) le_sup_right) (sup_le hK hG') hBG'
        (sup_le (sup_le ((le_sup_left : B ≤ B ⊔ G').trans (le_aeClosure _))
          (h1.trans (aeClosure_mono le_sup_right))) ((le_sup_right : G' ≤ B ⊔ G').trans
            (le_aeClosure _))) hi EventuallyEq.rfl
    exact e4.symm.trans (e3.trans (e1.symm.trans e2))
  exact GM.Bilip.CondIndepEv.of_le_aeClosure (condIndepEv_sup_cond hG' hA hB hAB) h3 h4

end LQGMetric.DFGPS.L219
