/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L33 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFResults
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# CONF Lemma 3.3 (conditional diameter): statement and the conditioning argument

Gwynne–Miller, *Confluence of geodesics in Liouville quantum gravity for γ ∈ (0,2)*
(arXiv:1905.00381), `literature/src/1905.00381/confluence-final.tex`, Lemma 3.3
(`lem-cond-diam-small`, C:1176–1186), proof C:1187–1244.

* `CONFLem3_3` : **CONF Lemma 3.3**. The conditional probability "`P[· | h|_{ℂ∖U}, E^U_r(z)] ≥ 𝔭`
  a.s." is stated in its integrated (defining) form: for every event `B` of `σ(h|_{ℂ∖U})`,
  `𝔭 · P[B ∩ E^U_r(z)] ≤ P[B ∩ E^U_r(z) ∩ {diameter event}]`. The components `V ∈ 𝒱(U)` are the
  `connectedComponentIn U x`, `x ∈ U`.
* `condFKG_freeze` : the conditioning argument of Step 3 (C:1236–1243) together with the
  reduction at the end of Step 1 (C:1213–1215), in abstract form: if `X` (the zero-boundary part
  `h̊^U`) is independent of `𝒢` (`= σ(h|_{ℂ∖U})`, LM Lemma 2.1), `G = {X ∈ S_G}` and
  `F = {(ω, X ω) ∈ S_F}` with `S_F` jointly measurable (`F` depends on the frozen outside field
  and on `X`), and for a.e. frozen realization `ω` the events `S_G` and `S_F(ω)` are positively
  correlated under the law of `X` (CONF: FKG, Proposition 2.8), then for every `B ∈ 𝒢`,
  `P[G] · P[B ∩ F] ≤ P[B ∩ F ∩ G]`.
* `SigOmega`, `toSig` : `Ω` with a sub-σ-algebra, as the codomain of the "outside field".
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- `σ((h − h_ρ(w))|_K)`: the field on `K` normalized at the circle `∂B_ρ(w)` -/
def recSigma {Ω : Type} (h : Ω → DistC) (ρ : ℝ) (w : ℂ) (K : Set ℂ) : MeasurableSpace Ω :=
  fieldSigmaClosed (fun ω => addConst (h ω) (-circleAvg (h ω) ρ w)) K

/-! ## The conditioning argument (CONF Step 3, C:1236–1243) -/

section Freeze

variable {Ω α β : Type} [mΩ : MeasurableSpace Ω] [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- `P{(W, X) ∈ S} = ∫ P[X ∈ S_w] dP_W(w)` for independent `W`, `X` and measurable `S` -/
lemma measure_pair_eq_lintegral {W : Ω → β} {X : Ω → α} (hW : Measurable W) (hX : Measurable X)
    (hind : IndepFun W X P) {S : Set (β × α)} (hS : MeasurableSet S) :
    P {ω | (W ω, X ω) ∈ S} = ∫⁻ w, P.map X (Prod.mk w ⁻¹' S) ∂(P.map W) := by
  have h1 := Measure.map_apply (μ := P) (hW.prodMk hX) hS
  rw [(indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hX.aemeasurable).1 hind] at h1
  rw [show {ω | (W ω, X ω) ∈ S} = (fun ω => (W ω, X ω)) ⁻¹' S from rfl, ← h1]
  exact Measure.prod_apply hS

/-- **Conditioning argument of CONF Lemma 3.3** (C:1213–1215 and C:1236–1243), abstract form:
`W` the outside data, `X ⊥ W`, `G = {X ∈ S_G}`, `F = {(W, X) ∈ S_F}`, frozen positive
correlation for a.e. `w`; then `P[G] · P[{W ∈ B} ∩ F] ≤ P[{W ∈ B} ∩ F ∩ G]`. -/
theorem condFKG_freeze {W : Ω → β} {X : Ω → α} (hW : Measurable W) (hX : Measurable X)
    (hind : IndepFun W X P) {SG : Set α} (hSG : MeasurableSet SG)
    {SF : Set (β × α)} (hSF : MeasurableSet SF)
    (hfkg : ∀ᵐ w ∂(P.map W),
      P.map X SG * P.map X (Prod.mk w ⁻¹' SF) ≤ P.map X (SG ∩ Prod.mk w ⁻¹' SF))
    {B : Set β} (hB : MeasurableSet B) :
    P (X ⁻¹' SG) * P (W ⁻¹' B ∩ {ω | (W ω, X ω) ∈ SF}) ≤
      P (W ⁻¹' B ∩ {ω | (W ω, X ω) ∈ SF} ∩ X ⁻¹' SG) := by
  have e1 : W ⁻¹' B ∩ {ω | (W ω, X ω) ∈ SF} = {ω | (W ω, X ω) ∈ (B ×ˢ univ) ∩ SF} := by
    ext ω; simp
  have e2 : W ⁻¹' B ∩ {ω | (W ω, X ω) ∈ SF} ∩ X ⁻¹' SG =
      {ω | (W ω, X ω) ∈ (B ×ˢ SG) ∩ SF} := by
    ext ω; simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, mem_prod]; tauto
  rw [e2, e1, measure_pair_eq_lintegral hW hX hind ((hB.prod MeasurableSet.univ).inter hSF),
    measure_pair_eq_lintegral hW hX hind ((hB.prod hSG).inter hSF), ← Measure.map_apply hX hSG,
    ← lintegral_const_mul' _ _ (measure_ne_top _ _)]
  refine lintegral_mono_ae ?_
  filter_upwards [hfkg] with w hw
  by_cases hwB : w ∈ B
  · have a1 : Prod.mk w ⁻¹' ((B ×ˢ univ) ∩ SF) = Prod.mk w ⁻¹' SF := by ext x; simp [hwB]
    have a2 : Prod.mk w ⁻¹' ((B ×ˢ SG) ∩ SF) = SG ∩ Prod.mk w ⁻¹' SF := by ext x; simp [hwB]
    rw [a1, a2]; exact hw
  · have a1 : Prod.mk w ⁻¹' ((B ×ˢ univ) ∩ SF) = ∅ := by ext x; simp [hwB]
    rw [a1]; simp

end Freeze

/-! ## The outside field as a random element -/

/-- `Ω` with the σ-algebra `𝒢` (the outside field `h|_{ℂ∖U}` read as a random element) -/
structure SigOmega (Ω : Type) (_𝒢 : MeasurableSpace Ω) : Type where
  /-- the underlying outcome -/
  val : Ω

instance (Ω : Type) (𝒢 : MeasurableSpace Ω) : MeasurableSpace (SigOmega Ω 𝒢) :=
  MeasurableSpace.comap SigOmega.val 𝒢

/-- the identity `Ω → (Ω, 𝒢)` -/
def toSig {Ω : Type} (𝒢 : MeasurableSpace Ω) : Ω → SigOmega Ω 𝒢 := fun ω => ⟨ω⟩

lemma measurable_toSig {Ω : Type} [mΩ : MeasurableSpace Ω] {𝒢 : MeasurableSpace Ω}
    (h𝒢 : 𝒢 ≤ mΩ) : @Measurable Ω (SigOmega Ω 𝒢) mΩ _ (toSig 𝒢) := by
  rintro _ ⟨s, hs, rfl⟩
  exact h𝒢 _ hs

lemma measurableSet_val_preimage {Ω : Type} {𝒢 : MeasurableSpace Ω} {B : Set Ω}
    (hB : MeasurableSet[𝒢] B) : MeasurableSet (SigOmega.val ⁻¹' B : Set (SigOmega Ω 𝒢)) :=
  ⟨B, hB, rfl⟩

end LQGMetric.CONF
