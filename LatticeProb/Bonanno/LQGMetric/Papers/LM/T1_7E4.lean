/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7E4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7E3
import LatticeProb.Bonanno.LQGMetric.Papers.LM.C1_8Bdd
import LatticeProb.Bonanno.LQGMetric.Papers.LM.LocNest

/-!
# LM Lemma 2.4 for finitely many bounded open sets, and LM Lemma 5.4 (kernel form)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), Lemma 2.4 (`lem-open-ind`, l. 548–560) and Lemma 5.4
(`lem-square-ind`, l. 992–997). LM's proof of Lemma 2.4: "By further conditioning on `h|_{U∖V}`
in Definition 1.2, we get that if `V` is an open set, then `D(·,·;V)` and `D(·,·;U∖cl V)` are
conditionally independent given `h`. We now apply this in the case when `V` is a countable union
of sets in `𝒲` … if `W ⊄ V`, equivalently `W ∩ cl V = ∅`, then `D(·,·;W)` is the internal metric
of `D(·,·;U∖cl V)` on `W`. Applying these observations with `V` ranging over all finite unions of
sets in `𝒲` gives the lemma statement."

* `t17e_condIndep_compl` — the first sentence, for bounded open `V` (LM l. 554; "further
  conditioning on `h|_{U∖V}`" is form (2) of locality, `c18b_locForm2` from the bounded germ split
  `GermSplit.locGermSplitBdd`, followed by weak union `condIndepEv_transfer`), with the Borel
  versions `chainSigma` of the internal-metric σ-algebras.
* `t17eEnc W d` — the internal metric `d(·,·;W)` (chain formula `chainInf`, equal to it for length
  metrics) on the dense sequence of pairs, a variable in the standard Borel space `ℕ → [0,∞]`.
* `t17e_seqIndep` — for pairwise disjoint bounded open `W_i` (`i ∈ ι` finite): the iterated
  two-set conditional independence `T17eSeqIndep` (LM l. 555–559, `V = ⋃_{i∈T} W_i`).
* `t17e_lem5_4` — **LM Lemma 5.4 / 2.4, kernel form**: for `law(h)`-a.e. `g`, under
  `κ_g = condDistrib D h P g` the internal metrics on the `W_i` are independent:
  `(κ_g).map (t17eEnc W_i)_i = ⨂_i (κ_g).map (t17eEnc W_i)`. For a fixed shift `θ` and mesh `ε`,
  apply it to the grid squares `W_i = S_i` meeting a ball (finitely many).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open Function (onFun)

namespace LQGMetric.LM

open Blueprint GM.Bilip DFGPS.L219

/-- `d(·,·;W)` (chain formula) on the dense sequence of pairs -/
def t17eEnc (W : Set ℂ) (d : ContMetric) : ℕ → ℝ≥0∞ := fun n =>
  d.chainInf W (TopologicalSpace.denseSeq (ℂ × ℂ) n).1 (TopologicalSpace.denseSeq (ℂ × ℂ) n).2

lemma measurable_t17eEnc (W : Set ℂ) : Measurable (t17eEnc W) :=
  Measurable.of_eval fun _ => (ContMetric.measurable_chainInf W).comp
    (measurable_id.prodMk (measurable_const.prodMk measurable_const))

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit mΩ in
lemma t17e_comap_enc_le (D : Ω → ContMetric) (W : Set ℂ) :
    MeasurableSpace.comap (t17eEnc W ∘ D) inferInstance ≤ chainSigma D W := by
  set G : (ℂ → ℂ → ℝ≥0∞) → ℕ → ℝ≥0∞ := fun ρ n =>
    ρ (TopologicalSpace.denseSeq (ℂ × ℂ) n).1 (TopologicalSpace.denseSeq (ℂ × ℂ) n).2
  have hG : Measurable G := Measurable.of_eval fun n =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)
  rw [show t17eEnc W ∘ D = G ∘ fun ω (u v : ℂ) => (D ω).chainInf W u v from rfl,
    ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hG.comap_le

/-- **LM l. 554**, bounded `V`: `D(·,·;V) ⟂ D(·,·;ℂ∖cl V) | h` (Borel versions) -/
theorem t17e_condIndep_compl {h : Ω → DistC} {D : Ω → ContMetric} (hh : IsWholePlaneGFF h P)
    (hloc : IsLocalMetric P h D) (V : TopologicalSpace.Opens ℂ)
    (hVb : Bornology.IsBounded (V : Set ℂ)) :
    CondIndepEv (MeasurableSpace.comap h inferInstance) (chainSigma D V)
      (chainSigma D (closure (V : Set ℂ))ᶜ) P := by
  have hm := hh.measurable
  have hD := hloc.1
  have hlen := hloc.2.1
  have hW : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  have h2 := c18b_locForm2 GermSplit.locGermSplitBdd hh hD hlen V hVb (hloc.2.2 V)
  have h2' : CondIndepEv (fieldSigma h V) (chainSigma D V)
      (MeasurableSpace.comap h inferInstance ⊔ chainSigma D (closure (V : Set ℂ))ᶜ) P :=
    CondIndepEv.of_le_aeClosure h2 (chainSigma_le_famSigma hlen V.isOpen)
      (sup_le (le_sup_left.trans (le_aeClosure _))
        (le_aeClosure_trans (chainSigma_le_famSigma hlen hW)
          (le_sup_right.trans (le_aeClosure _))))
  refine condIndepEv_transfer ((fieldSigma_le_comapH h V).trans hm.comap_le)
    (chainSigma_le hD _) (sup_le hm.comap_le (chainSigma_le hD _)) hm.comap_le h2'
    ((fieldSigma_le_comapH h V).trans (le_aeClosure _))
    ((le_sup_left.trans le_sup_left).trans (le_aeClosure _))
    (le_sup_left.trans (le_aeClosure _))
    ((le_sup_right.trans le_sup_left).trans (le_aeClosure _))

/-- **LM Lemma 2.4** (l. 553–559), finitely many disjoint bounded open sets: the iterated two-set
conditional independence of their internal metrics given `h`. -/
theorem t17e_seqIndep {ι : Type*} {h : Ω → DistC} {D : Ω → ContMetric}
    (hh : IsWholePlaneGFF h P) (hloc : IsLocalMetric P h D) (W : ι → Set ℂ)
    (hWo : ∀ i, IsOpen (W i)) (hWb : ∀ i, Bornology.IsBounded (W i))
    (hWd : Pairwise (onFun Disjoint W)) :
    T17eSeqIndep h D (fun i => t17eEnc (W i)) P := by
  intro T j hj
  have hD := hloc.1
  have hlen := hloc.2.1
  set V : TopologicalSpace.Opens ℂ := ⟨⋃ i ∈ T, W i, isOpen_biUnion fun i _ => hWo i⟩
  have hVb : Bornology.IsBounded (V : Set ℂ) :=
    (Bornology.isBounded_biUnion_finset T).2 fun i _ => hWb i
  have hsub : ∀ i ∈ T, W i ⊆ V := fun i hi => subset_biUnion_of_mem (u := W) hi
  have hdisj : Disjoint (W j) (V : Set ℂ) := by
    refine disjoint_iUnion₂_right.2 fun i hi => hWd ?_
    rintro rfl; exact hj hi
  have hsubc : W j ⊆ (closure (V : Set ℂ))ᶜ :=
    (hdisj.closure_right (hWo j)).subset_compl_right
  have hW : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  have H := t17e_condIndep_compl hh hloc V hVb
  refine CondIndepEv.of_le_aeClosure H ?_ ?_
  · refine iSup₂_le fun i hi => ?_
    exact (t17e_comap_enc_le D (W i)).trans (le_aeClosure_trans
      (chainSigma_le_famSigma hlen (hWo i)) (le_aeClosure_trans
        (locInternalNest P D hD hlen _ _ (hWo i) V.isOpen (hsub i hi))
        (famSigma_le_chainSigma hlen V.isOpen)))
  · exact (t17e_comap_enc_le D (W j)).trans (le_aeClosure_trans
      (chainSigma_le_famSigma hlen (hWo j)) (le_aeClosure_trans
        (locInternalNest P D hD hlen _ _ (hWo j) hW hsubc)
        (famSigma_le_chainSigma hlen hW)))

/-- **LM Lemma 5.4** (l. 992–997) via Lemma 2.4, kernel form: for pairwise disjoint bounded open
`W_i` (finitely many), for `law(h)`-a.e. `g` the internal metrics on the `W_i` are independent
under the conditional law `κ_g` of `D` given `h = g`. -/
theorem t17e_lem5_4 {ι : Type*} [Fintype ι] [DecidableEq ι] {h : Ω → DistC} {D : Ω → ContMetric}
    (hh : IsWholePlaneGFF h P) (hloc : IsLocalMetric P h D) (W : ι → Set ℂ)
    (hWo : ∀ i, IsOpen (W i)) (hWb : ∀ i, Bornology.IsBounded (W i))
    (hWd : Pairwise (onFun Disjoint W)) :
    ∀ᵐ g ∂P.map h, (condDistrib D h P g).map (fun d i => t17eEnc (W i) d) =
      Measure.pi fun i => (condDistrib D h P g).map (t17eEnc (W i)) :=
  t17e_condDistrib_pi hh.measurable hloc.1 (fun i => measurable_t17eEnc (W i))
    (t17e_seqIndep hh hloc W hWo hWb hWd)

end LQGMetric.LM
