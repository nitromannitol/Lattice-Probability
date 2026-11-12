/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L33M at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L33
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.MarkovNorm
import LatticeProb.Bonanno.LQGMetric.Field.MarkovFinal
import LatticeProb.Bonanno.LQGMetric.Field.MarkovAsmB
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-!
# CONF Lemma 3.3: the Markov decomposition and the reduction to Steps 1–3

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381, proof of Lemma 3.3,
C:1187–1190: "we can assume … that `h` is normalized so that `h_{r₀}(z₀) = 0` for some `z₀ ∈ ℂ`
and `r₀ > 0` such that `B_{r₀}(z₀) ∩ U = ∅` … By the Markov property of the field (see, e.g.,
[LM, Lemma 2.2]) we can write `h|_U = h̊^U + 𝔥^U`, where `h̊^U` is a zero-boundary GFF in `U` which
is independent from `h|_{ℂ∖U}`." ([LM, Lemma 2.2] is LM Lemma 2.1 in arXiv-final; we use the
project's `MarkovFinal.lmLem2_1` at the normalization circle `∂B_ρ(w)` via
`DFGPS.markov_normAt`; only `∂B_ρ(w) ∩ U = ∅` is needed.)

* `isOpen_confU` : `U ∈ 𝒰_r(z;δ)` is open.
* `IsL33ZBPart` : `X` is (an a.s. modification of) the zero-boundary part `h̊^U` of the
  normalized field `h − h_ρ(w)`, measurable and independent of `σ((h − h_ρ(w))|_{ℂ∖U})`.
* `exists_isL33ZBPart` : such an `X` exists (proved; LM Lemma 2.1).
* `CONFLem3_3Steps` : Steps 1–3 of CONF's proof for every such `X` (open).
* `confLem3_3_of_steps` : **CONF Lemma 3.3** from `CONFLem3_3Steps`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

lemma isClosed_confSq (ε : ℝ) (z : ℂ) (k : ℤ × ℤ) : IsClosed (confSq ε z k) := by
  have e : confSq ε z k = ({w : ℂ | z.re + k.1 * ε ≤ w.re} ∩ {w | w.re ≤ z.re + (k.1 + 1) * ε}) ∩
      ({w | z.im + k.2 * ε ≤ w.im} ∩ {w | w.im ≤ z.im + (k.2 + 1) * ε}) := by
    ext w; simp only [confSq, mem_inter_iff, mem_setOf_eq, and_assoc]
  rw [e]
  exact ((isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le Complex.continuous_re continuous_const)).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le Complex.continuous_im continuous_const))

lemma isOpen_confU (r δ : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)) : IsOpen (confU r δ z T) :=
  (annulus z (3 * r) (4 * r)).isOpen.sdiff
    (isClosed_biUnion_finset fun k _ => isClosed_confSq (δ * r) z k)

section Markov

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- the field normalized at `∂B_ρ(w)` -/
def recField (h : Ω → DistC) (ρ : ℝ) (w : ℂ) : Ω → DistC :=
  fun ω => addConst (h ω) (-circleAvg (h ω) ρ w)

omit [IsProbabilityMeasure P] in
lemma isWholePlaneGFF_recField (hh : IsWholePlaneGFF h P) (ρ : ℝ) (w : ℂ) :
    IsWholePlaneGFF (recField h ρ w) P :=
  hh.addConst ((measurable_circleAvg_left ρ w).comp hh.measurable).neg

omit [IsProbabilityMeasure P] in
lemma recSigma_le (hh : IsWholePlaneGFF h P) (ρ : ℝ) (w : ℂ) (K : Set ℂ) :
    recSigma h ρ w K ≤ mΩ :=
  MarkovZBIndep.fieldSigmaClosed_le (isWholePlaneGFF_recField hh ρ w) K

omit mΩ in
lemma comap_toSig (𝒢 : MeasurableSpace Ω) :
    MeasurableSpace.comap (toSig 𝒢) (inferInstance : MeasurableSpace (SigOmega Ω 𝒢)) = 𝒢 := by
  show MeasurableSpace.comap (toSig 𝒢) (MeasurableSpace.comap SigOmega.val 𝒢) = 𝒢
  rw [MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_id

variable (P) in
/-- `X` is the zero-boundary part `h̊^U` of `h − h_ρ(w)` on the open set `U` (LM Lemma 2.1),
up to an a.s. modification, measurable and independent of `σ((h − h_ρ(w))|_{ℂ∖U})` -/
def IsL33ZBPart (h : Ω → DistC) (ρ : ℝ) (w : ℂ) (U : Set ℂ) (hU : IsOpen U) (X : Ω → DistC) :
    Prop :=
  Measurable X ∧ IndepFun (toSig (recSigma h ρ w Uᶜ)) X P ∧
  ∃ hh₀ hz : Ω → DistC, (∀ ω, recField h ρ w ω = hh₀ ω + hz ω) ∧ X =ᵐ[P] hz ∧
    (∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g U ∧
      ∀ φ : TestOn (toOpens U hU), restrictTo (toOpens U hU) (hh₀ ω) φ = ∫ x, g x * φ x) ∧
    IsZeroBoundaryGFF (toOpens U hU) (fun ω => restrictTo (toOpens U hU) (hz ω)) P ∧
    (∀ ω, restrictTo (toOpens (closure U)ᶜ isClosed_closure.isOpen_compl) (hz ω) = 0)

end Markov

end LQGMetric.CONF
