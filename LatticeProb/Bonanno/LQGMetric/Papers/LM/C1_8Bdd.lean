/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.C1_8Bdd at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.LocJoint
import LatticeProb.Bonanno.LQGMetric.Field.GermSplitA

/-!
# LM Lemma 1.4 at bounded open sets, from `GermSplit.locGermSplitBdd` (task P2-LMC18)

The proofs of `LM.locForm2_of_isLocal`, `LM.condIndepEv_internal_of_local`,
`LM.condIndepEv_internal_pair` and `LM.lmLem1_4_of` (Papers/LM/LocEquiv.lean,
Papers/LM/LocJoint.lean, task P2-LMLOC; LM = arXiv:1905.00379, Lemma 1.4, l. 253–274) use
`LocGermSplit` only at the open set `V` under consideration. Copied here verbatim with the
hypothesis `GermSplit.LocGermSplitBdd` (LM l. 534 for bounded `V`, proved) and `V` bounded.
Main result: `c18_jointlyLocalAt_bdd`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM.Bilip DFGPS.L219

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **(1) ⟹ (2)** (LM l. 534), from `LocGermSplit` -/
theorem c18b_locForm2 (hgerm : GermSplit.LocGermSplitBdd) {h : Ω → DistC} {D : Ω → ContMetric}
    (hh : IsWholePlaneGFF h P) (hD : Measurable D) (hlen : ∀ᵐ ω ∂P, (D ω).IsLength)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    (h1 : CondIndepEv (fieldSigma h V) (famSigma (internalFam D) V)
      (fieldSigmaClosed h (V : Set ℂ)ᶜ ⊔ famSigma (internalFam D) (closure (V : Set ℂ))ᶜ) P) :
    LocForm2 P h D V := by
  have hm := hh.measurable
  have hV := V.isOpen
  have hW : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  have h1' : CondIndepEv (fieldSigma h V) (chainSigma D V)
      (fieldSigmaClosed h (V : Set ℂ)ᶜ ⊔ chainSigma D (closure (V : Set ℂ))ᶜ) P :=
    GM.Bilip.CondIndepEv.of_le_aeClosure h1 (chainSigma_le_famSigma hlen hV)
      (sup_le (le_sup_left.trans (le_aeClosure _))
        ((chainSigma_le_famSigma hlen hW).trans (aeClosure_mono le_sup_right)))
  refine condIndepEv_transfer (fieldSigma_le hm V) (chainSigma_le hD _)
    (sup_le (fieldSigmaClosed_le hm _) (chainSigma_le hD _)) (fieldSigma_le hm V) h1'
    (le_aeClosure _) (le_sup_right.trans (le_aeClosure _)) ?_ ?_
  · exact (famSigma_le_chainSigma hlen hV).trans (aeClosure_mono le_sup_left)
  · exact sup_le ((hgerm P h hh V hVb).trans
      (aeClosure_mono (sup_le le_sup_right (le_sup_left.trans le_sup_left))))
      ((famSigma_le_chainSigma hlen hW).trans (aeClosure_mono (le_sup_right.trans le_sup_left)))



/-- `D(·,·;V) ⟂ (h, D(·,·;ℂ∖V̄), D'(·,·;ℂ∖V̄)) | h|_V` (LM l. 264–267), Borel versions -/
theorem c18b_internal_of_local (hgerm : GermSplit.LocGermSplitBdd) {h : Ω → DistC}
    {D D' : Ω → ContMetric} (hh : IsWholePlaneGFF h P) (hl : IsLocalMetric P h D)
    (hD' : Measurable D')
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap D' inferInstance) (MeasurableSpace.comap D inferInstance) P)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ)) :
    CondIndepEv (fieldSigma h V) (chainSigma D V)
      (MeasurableSpace.comap h inferInstance ⊔ chainSigma D (closure (V : Set ℂ))ᶜ ⊔
        chainSigma D' (closure (V : Set ℂ))ᶜ) P := by
  obtain ⟨hD, hlen, hloc⟩ := hl
  have hm := hh.measurable
  have hV := V.isOpen
  have hW : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  have h2 : CondIndepEv (fieldSigma h V) (chainSigma D V)
      (MeasurableSpace.comap h inferInstance ⊔ chainSigma D (closure (V : Set ℂ))ᶜ) P :=
    GM.Bilip.CondIndepEv.of_le_aeClosure (c18b_locForm2 hgerm hh hD hlen V hVb (hloc V))
      (chainSigma_le_famSigma hlen hV) (sup_le (le_sup_left.trans (le_aeClosure _))
        ((chainSigma_le_famSigma hlen hW).trans (aeClosure_mono le_sup_right)))
  have hstep : CondIndepEv ((MeasurableSpace.comap h inferInstance ⊔
      chainSigma D (closure (V : Set ℂ))ᶜ) ⊔ fieldSigma h V) (chainSigma D V)
      (chainSigma D' (closure (V : Set ℂ))ᶜ) P := by
    refine CondIndepEv.symm (condIndepEv_transfer hm.comap_le hD'.comap_le hD.comap_le
      (sup_le (sup_le hm.comap_le (chainSigma_le hD _)) (fieldSigma_le hm V)) hci ?_ ?_ ?_ ?_)
    · exact (le_sup_left.trans le_sup_left).trans (le_aeClosure _)
    · exact (sup_le (sup_le le_sup_right ((chainSigma_le_comap D _).trans le_sup_left))
        ((fieldSigma_le_comapH h V).trans le_sup_right)).trans (le_aeClosure _)
    · exact ((chainSigma_le_comap D' _).trans le_sup_left).trans (le_aeClosure _)
    · exact ((chainSigma_le_comap D _).trans le_sup_left).trans (le_aeClosure _)
  exact condIndepEv_contraction (fieldSigma_le hm V) (chainSigma_le hD _)
    (sup_le hm.comap_le (chainSigma_le hD _)) (chainSigma_le hD' _) h2 hstep

/-- `D₁(·,·;V) ⟂ D₂(·,·;V) | (h|_{ℂ∖V}, D₁(·,·;ℂ∖V̄), D₂(·,·;ℂ∖V̄), h|_V)` (LM l. 269), Borel
versions -/
theorem c18b_internal_pair (hgerm : GermSplit.LocGermSplitBdd) {h : Ω → DistC}
    {D₁ D₂ : Ω → ContMetric} (hh : IsWholePlaneGFF h P) (hD₁ : Measurable D₁)
    (hD₂ : Measurable D₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap D₁ inferInstance) (MeasurableSpace.comap D₂ inferInstance) P)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ)) :
    CondIndepEv (fieldSigmaClosed h (V : Set ℂ)ᶜ ⊔ chainSigma D₁ (closure (V : Set ℂ))ᶜ ⊔
        chainSigma D₂ (closure (V : Set ℂ))ᶜ ⊔ fieldSigma h V)
      (chainSigma D₁ V) (chainSigma D₂ V) P := by
  have hm := hh.measurable
  have hX : fieldSigmaClosed h (V : Set ℂ)ᶜ ⊔ chainSigma D₁ (closure (V : Set ℂ))ᶜ ⊔
      chainSigma D₂ (closure (V : Set ℂ))ᶜ ⊔ fieldSigma h V ≤ mΩ :=
    sup_le (sup_le (sup_le (fieldSigmaClosed_le hm _) (chainSigma_le hD₁ _))
      (chainSigma_le hD₂ _)) (fieldSigma_le hm V)
  -- add `D₂(·,·;ℂ∖V̄)` to the conditioning
  have s1 : CondIndepEv (MeasurableSpace.comap h inferInstance ⊔
      chainSigma D₂ (closure (V : Set ℂ))ᶜ) (MeasurableSpace.comap D₂ inferInstance)
      (MeasurableSpace.comap D₁ inferInstance) P := by
    refine CondIndepEv.symm (condIndepEv_transfer hm.comap_le hD₁.comap_le hD₂.comap_le
      (sup_le hm.comap_le (chainSigma_le hD₂ _)) hci (le_sup_left.trans (le_aeClosure _)) ?_
      (le_sup_left.trans (le_aeClosure _)) (le_sup_left.trans (le_aeClosure _)))
    exact (sup_le le_sup_right ((chainSigma_le_comap D₂ _).trans le_sup_left)).trans
      (le_aeClosure _)
  -- add `D₁(·,·;ℂ∖V̄)` and pass to `(h|_{ℂ∖V}, h|_V)` (LM l. 534)
  refine CondIndepEv.symm (condIndepEv_transfer
    (sup_le hm.comap_le (chainSigma_le hD₂ _)) hD₂.comap_le hD₁.comap_le hX s1 ?_ ?_ ?_ ?_)
  · refine sup_le ((hgerm P h hh V hVb).trans (aeClosure_mono (sup_le le_sup_right
      ((le_sup_left.trans le_sup_left).trans le_sup_left)))) ?_
    exact (le_sup_right.trans le_sup_left).trans (le_aeClosure _)
  · refine (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_).trans (le_aeClosure _)
    · exact (fieldSigmaClosed_le_comapH h _).trans (le_sup_left.trans le_sup_right)
    · exact (chainSigma_le_comap D₁ _).trans le_sup_left
    · exact le_sup_right.trans le_sup_right
    · exact (fieldSigma_le_comapH h V).trans (le_sup_left.trans le_sup_right)
  · exact ((chainSigma_le_comap D₂ _).trans le_sup_left).trans (le_aeClosure _)
  · exact ((chainSigma_le_comap D₁ _).trans le_sup_left).trans (le_aeClosure _)


/-- **LM Lemma 1.4** (`n = 2`, l. 253–274) at a bounded open set `V`: the joint-locality
conditional independence at `V`, from `GermSplit.LocGermSplitBdd` (proof of `LM.lmLem1_4_of`) -/
theorem c18_jointlyLocalAt_bdd (hgerm : GermSplit.LocGermSplitBdd) {h : Ω → DistC}
    {D₁ D₂ : Ω → ContMetric} (hh : IsWholePlaneGFF h P) (hl₁ : IsLocalMetric P h D₁)
    (hl₂ : IsLocalMetric P h D₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap D₁ inferInstance) (MeasurableSpace.comap D₂ inferInstance) P)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ)) :
    CondIndepEv (fieldSigma h V) (famSigma (internalFam D₁) V ⊔ famSigma (internalFam D₂) V)
      (fieldSigmaClosed h (V : Set ℂ)ᶜ ⊔ famSigma (internalFam D₁) (closure (V : Set ℂ))ᶜ ⊔
        famSigma (internalFam D₂) (closure (V : Set ℂ))ᶜ) P := by
  have hm := hh.measurable
  have hD₁ := hl₁.1
  have hD₂ := hl₂.1
  have hV := V.isOpen
  have hW : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  have hX : fieldSigmaClosed h (V : Set ℂ)ᶜ ⊔ chainSigma D₁ (closure (V : Set ℂ))ᶜ ⊔
      chainSigma D₂ (closure (V : Set ℂ))ᶜ ≤ _ :=
    sup_le (sup_le (fieldSigmaClosed_le hm _) (chainSigma_le hD₁ _)) (chainSigma_le hD₂ _)
  have hXY : CondIndepEv (fieldSigma h V) (fieldSigmaClosed h (V : Set ℂ)ᶜ ⊔
      chainSigma D₁ (closure (V : Set ℂ))ᶜ ⊔ chainSigma D₂ (closure (V : Set ℂ))ᶜ)
      (chainSigma D₁ V) P :=
    ((c18b_internal_of_local hgerm hh hl₁ hD₂ hci.symm V hVb).mono le_rfl
      (sup_le_sup_right (sup_le_sup_right (fieldSigmaClosed_le_comapH h _) _) _)).symm
  have hXZ : CondIndepEv (fieldSigma h V) (fieldSigmaClosed h (V : Set ℂ)ᶜ ⊔
      chainSigma D₁ (closure (V : Set ℂ))ᶜ ⊔ chainSigma D₂ (closure (V : Set ℂ))ᶜ)
      (chainSigma D₂ V) P :=
    ((c18b_internal_of_local hgerm hh hl₂ hD₁ hci V hVb).mono le_rfl
      (sup_le (sup_le ((fieldSigmaClosed_le_comapH h _).trans (le_sup_left.trans le_sup_left))
        le_sup_right) (le_sup_right.trans le_sup_left))).symm
  have hYZ := c18b_internal_pair hgerm hh hD₁ hD₂ hci V hVb
  have hfin := condIndepEv_sup_of_condIndepEv (fieldSigma_le hm V) hX (chainSigma_le hD₁ _)
    (chainSigma_le hD₂ _) hXY hXZ hYZ
  refine GM.Bilip.CondIndepEv.of_le_aeClosure hfin.symm ?_ ?_
  · exact sup_le ((famSigma_le_chainSigma hl₁.2.1 hV).trans (aeClosure_mono le_sup_left))
      ((famSigma_le_chainSigma hl₂.2.1 hV).trans (aeClosure_mono le_sup_right))
  · refine sup_le (sup_le ((le_sup_left.trans le_sup_left).trans (le_aeClosure _)) ?_) ?_
    · exact (famSigma_le_chainSigma hl₁.2.1 hW).trans
        (aeClosure_mono (le_sup_right.trans le_sup_left))
    · exact (famSigma_le_chainSigma hl₂.2.1 hW).trans (aeClosure_mono le_sup_right)

end LQGMetric.LM
