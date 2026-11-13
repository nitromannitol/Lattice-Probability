/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase.IGData at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.Defs
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OPositiveRadii
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeasJoint

/-!
# The Case 4 law of the full imaginary-geometry data

Source: (`[18]:N`), §2.1.3 (`[18]`: the IG field is a
whole-plane GFF modulo `2πχ`, `η_L` is a measurable function of it) and Proposition 4.10, Case 4
(`[18]`: `h⁴ = h³(·/2 + z₀)`); on the
frozen bundle the IG field is `hIG₀ + U` (normalized field plus uniform phase), and every local
observation must carry the phase.

Under `ψ(u) = u/2 + z₀` the IG field `hIG₀ + U` becomes `(hIG₀ + U) ∘ ψ`; renormalizing its
unit-circle average gives the normalized field `hIG₀(·/2 + z₀) − (hIG₀)_{1/2}(z₀)` and the phase
`(hIG₀)_{1/2}(z₀) + U`, reduced modulo `2πχ` (the curve only sees the field modulo `2πχ`). This is
`igCase4 r z₀`. The re-rooted Lebesgue curve is `case4Curve z₀ ηL`.

Main theorem (`map_igTransform_ηL`, frozen bundle v4, fixed root `z₀`):

  `law((igCase4 r z₀ (hIG₀, U), case4Curve z₀ ηL)) = law(((hIG₀, U), ηL))`.

This is the joint field/phase/curve version of IGCO's curve law
`IGLaw.IsMatingOfTreesCoupling.map_affineReroot_ηL` (whose proof, `IGLaw.map_affineReroot_of_ccPos`,
is followed here with the joint law kept): the transformed IG input agrees coordinatewise a.s.
with the input of `(igCase4 r z₀ (hIG₀, U))` up to an integer multiple of `2πχ`, the reduced pair
has the law of `(hIG₀, U)` (IGCO's `map_pair_shift_mod`), and `Φ` is `2πχ`-periodic. A new
measure-theoretic lemma (`map_prod_eq_of_forall_ae_eq`) transports coordinatewise a.s. equality of
two processes **jointly with a common coordinate**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace MatedCRTHarmonic.GMSCase

open LQGMetric MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.IGLaw

/-! ## Laws of pairs with a common coordinate -/

/-- Processes that agree coordinatewise almost surely have the same joint law with any common
coordinate `Z`. -/
theorem map_prod_eq_of_forall_ae_eq_pi {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} [IsFiniteMeasure P] {Z : Ω → α} {X Y : Ω → ι → ℝ}
    (hZ : AEMeasurable Z P) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hXY : ∀ i, (fun ω => X ω i) =ᵐ[P] fun ω => Y ω i) :
    P.map (fun ω => (Z ω, X ω)) = P.map (fun ω => (Z ω, Y ω)) := by
  set Z' := hZ.mk Z
  set X' := hX.mk X
  set Y' := hY.mk Y
  have hZ' : Measurable Z' := hZ.measurable_mk
  have hX' : Measurable X' := hX.measurable_mk
  have hY' : Measurable Y' := hY.measurable_mk
  have e1 : P.map (fun ω => (Z ω, X ω)) = P.map (fun ω => (Z' ω, X' ω)) :=
    Measure.map_congr (by filter_upwards [hZ.ae_eq_mk, hX.ae_eq_mk] with ω h1 h2; rw [h1, h2])
  have e2 : P.map (fun ω => (Z ω, Y ω)) = P.map (fun ω => (Z' ω, Y' ω)) :=
    Measure.map_congr (by filter_upwards [hZ.ae_eq_mk, hY.ae_eq_mk] with ω h1 h2; rw [h1, h2])
  have hXY' : ∀ i, (fun ω => X' ω i) =ᵐ[P] fun ω => Y' ω i := by
    intro i
    filter_upwards [hX.ae_eq_mk, hY.ae_eq_mk, hXY i] with ω h1 h2 h3
    change hX.mk X ω i = hY.mk Y ω i
    rw [← h1, ← h2]
    exact h3
  rw [e1, e2]
  have hm1 : Measurable fun ω => (Z' ω, X' ω) := hZ'.prodMk hX'
  have hm2 : Measurable fun ω => (Z' ω, Y' ω) := hZ'.prodMk hY'
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, T, hT, rfl⟩
    rw [Measure.map_apply hm1 (MeasurableSet.prod hA hT),
      Measure.map_apply hm2 (MeasurableSet.prod hA hT)]
    have hres : (P.restrict (Z' ⁻¹' A)).map X' = (P.restrict (Z' ⁻¹' A)).map Y' :=
      map_eq_of_forall_ae_eq_pi hX'.aemeasurable hY'.aemeasurable
        fun i => ae_restrict_of_ae (hXY' i)
    have h1 : (P.restrict (Z' ⁻¹' A)).map X' T = P ((fun ω => (Z' ω, X' ω)) ⁻¹' (A ×ˢ T)) := by
      rw [Measure.map_apply hX' hT, Measure.restrict_apply (hX' hT)]
      congr 1
      ext ω
      simp [and_comm]
    have h2 : (P.restrict (Z' ⁻¹' A)).map Y' T = P ((fun ω => (Z' ω, Y' ω)) ⁻¹' (A ×ˢ T)) := by
      rw [Measure.map_apply hY' hT, Measure.restrict_apply (hY' hT)]
      congr 1
      ext ω
      simp [and_comm]
    rw [← h1, ← h2, hres]
  · rw [Measure.map_apply hm1 MeasurableSet.univ, Measure.map_apply hm2 MeasurableSet.univ]
    simp

/-- The circle-average-process version (`ℝ → ℂ → ℝ`, product σ-algebra). -/
theorem map_prod_eq_of_forall_ae_eq {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} [IsFiniteMeasure P] {Z : Ω → α} {X Y : Ω → ℝ → ℂ → ℝ}
    (hZ : AEMeasurable Z P) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hXY : ∀ ρ w, (fun ω => X ω ρ w) =ᵐ[P] fun ω => Y ω ρ w) :
    P.map (fun ω => (Z ω, X ω)) = P.map (fun ω => (Z ω, Y ω)) := by
  have hUX : AEMeasurable (fun ω => uncurryProc (X ω)) P :=
    measurable_uncurryProc.comp_aemeasurable hX
  have hUY : AEMeasurable (fun ω => uncurryProc (Y ω)) P :=
    measurable_uncurryProc.comp_aemeasurable hY
  have hU : P.map (fun ω => (Z ω, uncurryProc (X ω))) =
      P.map (fun ω => (Z ω, uncurryProc (Y ω))) :=
    map_prod_eq_of_forall_ae_eq_pi hZ hUX hUY fun p => hXY p.1 p.2
  have hc : Measurable fun q : α × (ℝ × ℂ → ℝ) => (q.1, curryProc q.2) :=
    measurable_fst.prodMk (measurable_curryProc.comp measurable_snd)
  calc P.map (fun ω => (Z ω, X ω)) =
        P.map (fun ω => (Z ω, curryProc (uncurryProc (X ω)))) := rfl
    _ = (P.map (fun ω => (Z ω, uncurryProc (X ω)))).map
          (fun q : α × (ℝ × ℂ → ℝ) => (q.1, curryProc q.2)) :=
        (AEMeasurable.map_map_of_aemeasurable hc.aemeasurable (hZ.prodMk hUX)).symm
    _ = (P.map (fun ω => (Z ω, uncurryProc (Y ω)))).map
          (fun q : α × (ℝ × ℂ → ℝ) => (q.1, curryProc q.2)) := by rw [hU]
    _ = P.map (fun ω => (Z ω, curryProc (uncurryProc (Y ω)))) :=
        AEMeasurable.map_map_of_aemeasurable hc.aemeasurable (hZ.prodMk hUY)
    _ = P.map (fun ω => (Z ω, Y ω)) := rfl

/-! ## The Case 4 transformation of the IG data -/

/-- `(z₀, x) ↦ x(·/2 + z₀) − x_{1/2}(z₀)` (IGCO's `affField` at angle `0`) is measurable. -/
theorem measurable_affField_center (s φ : ℝ) :
    Measurable fun p : ℂ × DistC => affField s φ p.1 p.2 := by
  have hrot : Measurable (MoTPort.rotateField φ) :=
    MoTPort.ConeMeas.measurable_rotateField_joint.comp (measurable_const.prodMk measurable_id)
  have h1 : Measurable fun p : ℂ × DistC => MoTPort.rotateField φ (affineComp s p.1 p.2) :=
    hrot.comp ((measurable_affineComp_center s).comp measurable_swap)
  have h2 : Measurable fun p : ℂ × DistC => circleAvg p.2 s p.1 := by
    have hf : Measurable fun p : ℂ × DistC => ((p.2, (s, p.1)) : DistC × ℝ × ℂ) :=
      measurable_snd.prodMk (measurable_const.prodMk measurable_fst)
    have e : Measurable ((fun q : DistC × ℝ × ℂ => circleAvg q.1 q.2.1 q.2.2) ∘
        (fun p : ℂ × DistC => ((p.2, (s, p.1)) : DistC × ℝ × ℂ))) :=
      measurable_circleAvg.comp hf
    exact e
  have e := DFGPS.L219.measurable_addConst_of h1 h2.neg
  exact e

/-! ## General scale -/

/-- **The IG data under `w ↦ (w − z₀)/s`**: the normalized pulled-back field `x(s · + z₀) − x_s(z₀)`
and the phase `x_s(z₀) + u` reduced modulo `r = 2πχ`. -/
def igCaseS (r : ℝ) [Fact (0 < r)] (s : ℝ) (z₀ : ℂ) (p : DistC × ℝ) : DistC × ℝ :=
  (affField s 0 z₀ p.1, modRep r (circleAvg p.1 s z₀ + p.2))

/-- The general-scale transformation of the full observation `((hIG₀, U), ηL)`. -/
def igTransformS (r : ℝ) [Fact (0 < r)] (s : ℝ) (z₀ : ℂ) (y : (DistC × ℝ) × C(ℝ, ℂ)) :
    (DistC × ℝ) × C(ℝ, ℂ) :=
  (igCaseS r s z₀ y.1, caseCurve s z₀ y.2)

theorem measurable_igCaseS (r : ℝ) [Fact (0 < r)] (s : ℝ) :
    Measurable fun q : ℂ × (DistC × ℝ) => igCaseS r s q.1 q.2 := by
  have hA : Measurable fun q : ℂ × (DistC × ℝ) => affField s 0 q.1 q.2.1 := by
    have hf : Measurable fun q : ℂ × (DistC × ℝ) => ((q.1, q.2.1) : ℂ × DistC) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have e : Measurable ((fun p : ℂ × DistC => affField s 0 p.1 p.2) ∘
        (fun q : ℂ × (DistC × ℝ) => ((q.1, q.2.1) : ℂ × DistC))) :=
      (measurable_affField_center s 0).comp hf
    exact e
  have hB : Measurable fun q : ℂ × (DistC × ℝ) => circleAvg q.2.1 s q.1 := by
    have hf : Measurable fun q : ℂ × (DistC × ℝ) => ((q.2.1, (s, q.1)) : DistC × ℝ × ℂ) :=
      (measurable_fst.comp measurable_snd).prodMk (measurable_const.prodMk measurable_fst)
    have e : Measurable ((fun q : DistC × ℝ × ℂ => circleAvg q.1 q.2.1 q.2.2) ∘
        (fun q : ℂ × (DistC × ℝ) => ((q.2.1, (s, q.1)) : DistC × ℝ × ℂ))) :=
      measurable_circleAvg.comp hf
    exact e
  have hC : Measurable fun q : ℂ × (DistC × ℝ) => modRep r (circleAvg q.2.1 s q.1 + q.2.2) := by
    have hf : Measurable fun q : ℂ × (DistC × ℝ) => circleAvg q.2.1 s q.1 + q.2.2 :=
      hB.add (measurable_snd.comp measurable_snd)
    have e : Measurable (modRep r ∘
        (fun q : ℂ × (DistC × ℝ) => circleAvg q.2.1 s q.1 + q.2.2)) :=
      (measurable_modRep r).comp hf
    exact e
  exact hA.prodMk hC

theorem measurable_igTransformS (r : ℝ) [Fact (0 < r)] (s : ℝ) :
    Measurable fun q : ℂ × ((DistC × ℝ) × C(ℝ, ℂ)) => igTransformS r s q.1 q.2 := by
  have h1 : Measurable fun q : ℂ × ((DistC × ℝ) × C(ℝ, ℂ)) => igCaseS r s q.1 q.2.1 := by
    have hf : Measurable fun q : ℂ × ((DistC × ℝ) × C(ℝ, ℂ)) => ((q.1, q.2.1) : ℂ × (DistC × ℝ)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have e : Measurable ((fun q : ℂ × (DistC × ℝ) => igCaseS r s q.1 q.2) ∘
        (fun q : ℂ × ((DistC × ℝ) × C(ℝ, ℂ)) => ((q.1, q.2.1) : ℂ × (DistC × ℝ)))) :=
      (measurable_igCaseS r s).comp hf
    exact e
  have h2 : Measurable fun q : ℂ × ((DistC × ℝ) × C(ℝ, ℂ)) => caseCurve s q.1 q.2.2 := by
    have hf : Measurable fun q : ℂ × ((DistC × ℝ) × C(ℝ, ℂ)) => ((q.1, q.2.2) : ℂ × C(ℝ, ℂ)) :=
      measurable_fst.prodMk (measurable_snd.comp measurable_snd)
    have e : Measurable ((fun p : ℂ × C(ℝ, ℂ) => caseCurve s p.1 p.2) ∘
        (fun q : ℂ × ((DistC × ℝ) × C(ℝ, ℂ)) => ((q.1, q.2.2) : ℂ × C(ℝ, ℂ)))) :=
      (measurable_caseCurve s).comp hf
    exact e
  exact h1.prodMk h2

/-! ## The joint law -/

section Core

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → Field} {U : Ω → ℝ} {ηL : Ω → C(ℝ, ℂ)} {Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ)}

/-- **Joint law of the IG data and the curve under `w ↦ (w − z₀)/s`** (general scale `s > 0`;
IGCO's `map_affineReroot_of_ccPos` with the joint law kept, `φ = 0`). -/
theorem map_igTransformS_of_ccPos (hh : IsNormalizedWPGFF h P)
    {r : ℝ} [Fact (0 < r)] (hr : r = 2 * Real.pi * igChi γ)
    (hUlaw : P.map U = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)]) (hind : IndepFun h U P)
    (hΦ : Measurable Φ)
    (hroot : ∀ᵐ ω ∂P, ηL ω = Φ (posIn (igCircleAvgInput (h ω, U ω))))
    (hcc : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → ∀ᵐ ω ∂P,
      Φ (posIn (igPullback γ z₀ s φ (igCircleAvgInput (h ω, U ω)))) = affineReroot z₀ s φ (ηL ω))
    (htr : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ))
    {s : ℝ} (hs : 0 < s) (z₀ : ℂ) :
    P.map (fun ω => igTransformS r s z₀ ((h ω, U ω), ηL ω)) = P.map (fun ω => ((h ω, U ω), ηL ω)) := by
  subst hr
  set r : ℝ := 2 * Real.pi * igChi γ with hrdef
  have hUm : AEMeasurable U P := MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif Fact.out hUlaw
  have hτ := ae_firstHit_zero_of_ccPos hroot hcc htr
  have hper := ae_periodic_of_ccPos hroot hcc hτ
  set H : Ω → ℝ → ℂ → ℝ := fun ω => igCircleAvgInput (h ω, U ω) with hHdef
  have hp : AEMeasurable (fun ω => (h ω, U ω)) P := hh.1.measurable.aemeasurable.prodMk hUm
  have hH : AEMeasurable H P := measurable_igCircleAvgInput.comp_aemeasurable hp
  -- the model field
  set h'' : Ω → Field := fun ω => affField s 0 z₀ (h ω) with hh''def
  have hcm : Measurable fun ω => circleAvg (h ω) s z₀ :=
    (LQGMetric.measurable_circleAvg_left s z₀).comp hh.1.measurable
  have hh'gff : IsWholePlaneGFF (fun ω => MoTPort.rotateField 0 (affineComp s z₀ (h ω))) P :=
    IsWholePlaneGFF.rotateField (hh.1.affineComp hs z₀) 0
  have hh''gff : IsWholePlaneGFF h'' P := hh'gff.addConst hcm.neg
  have hcov : ∀ᵐ ω ∂P, ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ,
      circleAvg (MoTPort.rotateField 0 (affineComp s z₀ (h ω))) ρ w =
        circleAvg (h ω) (s * ρ) ((s : ℂ) * Complex.exp ((0 : ℝ) * Complex.I) * w + z₀) :=
    ae_circleAvg_affineRotate_all hh.1 0 hs z₀
  have hadd : ∀ w : ℂ, ∀ ρ : ℝ, 0 < ρ → ∀ᵐ ω ∂P, ∀ a : ℝ,
      circleAvg (addConst (MoTPort.rotateField 0 (affineComp s z₀ (h ω))) a) ρ w =
        circleAvg (MoTPort.rotateField 0 (affineComp s z₀ (h ω))) ρ w + a :=
    fun w ρ hρ => CircleAvg.ae_circleAvg_addConst hh'gff w hρ
  have hh''norm : IsNormalizedWPGFF h'' P := by
    refine ⟨hh''gff, ?_⟩
    filter_upwards [hcov, hadd 0 1 one_pos] with ω hω hadd1
    show circleAvg (addConst (MoTPort.rotateField 0 (affineComp s z₀ (h ω)))
      (-(circleAvg (h ω) s z₀))) 1 0 = 0
    rw [hadd1, hω 1 one_pos 0]
    simp
  -- the reduced scalar
  set Vf : Field → ℝ := fun x => circleAvg x s z₀ with hVf
  have hVfm : Measurable Vf := LQGMetric.measurable_circleAvg_left s z₀
  set U' : Ω → ℝ := fun ω => modRep r (Vf (h ω) + U ω) with hU'def
  have hU'm : AEMeasurable U' P :=
    (measurable_modRep r).comp_aemeasurable ((hVfm.comp hh.1.measurable).aemeasurable.add hUm)
  have hpairU' : P.map (fun ω => (h ω, U' ω)) = P.map (fun ω => (h ω, U ω)) :=
    map_pair_shift_mod hh.1.measurable hUlaw hind hVfm
  have hGm : Measurable fun p : Field × ℝ => (affField s 0 z₀ p.1, p.2) :=
    ((measurable_affField s 0 z₀).comp measurable_fst).prodMk measurable_snd
  have hp' : AEMeasurable (fun ω => (h ω, U' ω)) P := hh.1.measurable.aemeasurable.prodMk hU'm
  have hp'' : AEMeasurable (fun ω => (h'' ω, U' ω)) P :=
    hh''gff.measurable.aemeasurable.prodMk hU'm
  have hlaw'' : P.map (fun ω => (h'' ω, U' ω)) = P.map (fun ω => (h ω, U ω)) := by
    have e1 : P.map (fun ω => (h'' ω, U' ω)) = P.map (fun ω => (h'' ω, U ω)) := by
      calc P.map (fun ω => (h'' ω, U' ω)) =
          (P.map (fun ω => (h ω, U' ω))).map fun p => (affField s 0 z₀ p.1, p.2) :=
            (AEMeasurable.map_map_of_aemeasurable hGm.aemeasurable hp').symm
        _ = (P.map (fun ω => (h ω, U ω))).map fun p => (affField s 0 z₀ p.1, p.2) := by
            rw [hpairU']
        _ = P.map (fun ω => (h'' ω, U ω)) :=
            AEMeasurable.map_map_of_aemeasurable hGm.aemeasurable hp
    have hind'' : IndepFun h'' U P := hind.comp (measurable_affField s 0 z₀) measurable_id
    rw [e1, (indepFun_iff_map_prod_eq_prod_map_map hh''gff.measurable.aemeasurable hUm).1 hind'',
      (indepFun_iff_map_prod_eq_prod_map_map hh.1.measurable.aemeasurable hUm).1 hind,
      CircleAvg.map_eq_of_isNormalizedWPGFF hh''norm hh]
  -- the transformed input agrees coordinatewise with the model process
  set Kp : Ω → ℝ → ℂ → ℝ := fun ω => posIn (igPullback γ z₀ s 0 (H ω)) with hKpdef
  set M : Ω → ℝ → ℂ → ℝ := fun ω => posIn (igCircleAvgInput (h'' ω, Vf (h ω) + U ω)) with hMdef
  have hKpm : AEMeasurable Kp P :=
    (measurable_posIn.comp (measurable_igPullback γ z₀ s 0)).comp_aemeasurable hH
  have hMm : AEMeasurable M P :=
    (measurable_posIn.comp measurable_igCircleAvgInput).comp_aemeasurable
      (hh''gff.measurable.aemeasurable.prodMk ((hVfm.comp hh.1.measurable).aemeasurable.add hUm))
  have hKM : ∀ ρ w, (fun ω => Kp ω ρ w) =ᵐ[P] fun ω => M ω ρ w := by
    intro ρ w
    rcases le_or_gt ρ 0 with hρ | hρ
    · refine Eventually.of_forall fun ω => ?_
      change posIn _ ρ w = posIn _ ρ w
      rw [posIn_apply_of_nonpos hρ, posIn_apply_of_nonpos hρ]
    · filter_upwards [hcov, hadd w ρ hρ] with ω hω haddω
      change posIn _ ρ w = posIn _ ρ w
      rw [posIn_apply_of_pos hρ, posIn_apply_of_pos hρ]
      change circleAvg (h ω) (s * ρ)
          (z₀ + (s : ℂ) * Complex.exp ((0 : ℝ) * Complex.I) * w) + U ω -
          igChi γ * 0 =
        circleAvg (addConst (MoTPort.rotateField 0 (affineComp s z₀ (h ω)))
          (-(circleAvg (h ω) s z₀))) ρ w + (circleAvg (h ω) s z₀ + U ω)
      rw [haddω, hω ρ hρ w, add_comm z₀]
      ring
  have hZ : AEMeasurable (fun ω => (h'' ω, U' ω)) P := hp''
  have hjoint : P.map (fun ω => ((h'' ω, U' ω), Kp ω)) = P.map (fun ω => ((h'' ω, U' ω), M ω)) :=
    map_prod_eq_of_forall_ae_eq hZ hKpm hMm hKM
  -- periodicity transferred to the model scalar
  have hper' : ∀ᵐ ω ∂P, (h'' ω, U' ω) ∈ {x : Field × ℝ | ∀ k : ℤ,
      Φ (posIn (addIn (r * k) (igCircleAvgInput x))) = Φ (posIn (igCircleAvgInput x))} :=
    ae_of_map_eq hp hp'' hlaw''.symm (measurableSet_periodicPos hΦ r) hper
  have hMred : ∀ᵐ ω ∂P, Φ (M ω) = Φ (posIn (igCircleAvgInput (h'' ω, U' ω))) := by
    filter_upwards [hper'] with ω hω
    obtain ⟨k, hk⟩ := exists_int_eq_modRep_add r (Vf (h ω) + U ω)
    have e : M ω = posIn (addIn (r * k) (igCircleAvgInput (h'' ω, U' ω))) := by
      have hk' : Vf (h ω) + U ω = U' ω + r * k := hk
      show posIn (igCircleAvgInput (h'' ω, Vf (h ω) + U ω)) = _
      rw [hk', igCircleAvgInput_add]
    rw [e]
    exact hω k
  -- assemble
  have hΦP : Measurable fun x : Field × ℝ => (x, Φ (posIn (igCircleAvgInput x))) :=
    measurable_id.prodMk (hΦ.comp (measurable_posIn.comp measurable_igCircleAvgInput))
  have hΦ2 : Measurable fun q : (Field × ℝ) × (ℝ → ℂ → ℝ) => (q.1, Φ q.2) :=
    measurable_fst.prodMk (hΦ.comp measurable_snd)
  have hcurve : ∀ᵐ ω ∂P, caseCurve s z₀ (ηL ω) = Φ (Kp ω) := by
    filter_upwards [hcc z₀ s 0 hs] with ω hω
    exact hω.symm
  calc P.map (fun ω => igTransformS r s z₀ ((h ω, U ω), ηL ω))
      = P.map (fun ω => ((h'' ω, U' ω), caseCurve s z₀ (ηL ω))) := rfl
    _ = P.map (fun ω => ((h'' ω, U' ω), Φ (Kp ω))) :=
        Measure.map_congr (by filter_upwards [hcurve] with ω hω; rw [hω])
    _ = (P.map (fun ω => ((h'' ω, U' ω), Kp ω))).map fun q => (q.1, Φ q.2) :=
        (AEMeasurable.map_map_of_aemeasurable hΦ2.aemeasurable (hZ.prodMk hKpm)).symm
    _ = (P.map (fun ω => ((h'' ω, U' ω), M ω))).map fun q => (q.1, Φ q.2) := by rw [hjoint]
    _ = P.map (fun ω => ((h'' ω, U' ω), Φ (M ω))) :=
        AEMeasurable.map_map_of_aemeasurable hΦ2.aemeasurable (hZ.prodMk hMm)
    _ = P.map (fun ω => ((h'' ω, U' ω), Φ (posIn (igCircleAvgInput (h'' ω, U' ω))))) :=
        Measure.map_congr (by filter_upwards [hMred] with ω hω; rw [hω])
    _ = (P.map (fun ω => (h'' ω, U' ω))).map
          fun x => (x, Φ (posIn (igCircleAvgInput x))) :=
        (AEMeasurable.map_map_of_aemeasurable hΦP.aemeasurable hp'').symm
    _ = (P.map (fun ω => (h ω, U ω))).map fun x => (x, Φ (posIn (igCircleAvgInput x))) := by
        rw [hlaw'']
    _ = P.map (fun ω => ((h ω, U ω), Φ (posIn (igCircleAvgInput (h ω, U ω))))) :=
        AEMeasurable.map_map_of_aemeasurable hΦP.aemeasurable hp
    _ = P.map (fun ω => ((h ω, U ω), ηL ω)) :=
        Measure.map_congr (by filter_upwards [hroot] with ω hω; rw [hω])

end Core

end MatedCRTHarmonic.GMSCase
