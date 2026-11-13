/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.IGNorm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OAffinePos

/-!
# The IG input renormalized at the unit circle

Source: [18] Lemma 2.4 with the imaginary-geometry coordinate
change (IG1; the frozen `igMap`, clauses (S6)/(S7)) and the definition of the IG field modulo `2πχ`
(IG4, [18]).

The local IG data on a small disk do not see the global normalization of `h^IG` or the phase `U`. Pulling the
input back by `ψ(v) = z + s v` and reducing it at the image of the unit circle,
`l43pNorm r K = (K − K(1,0) + (K(1,0) mod r))` on positive radii (`r = 2πχ`), produces an input with the
**same law** as the bundle's (`map_l43pNorm_igPullback`). This uses IGCO's argument for the affine invariance of
The curve law (`IGLaw.map_affineReroot_of_ccPos`) at the level of the input process: `h ∘ ψ − h_s(z)` is a
normalized whole-plane GFF and `(h_s(z) + U) mod r` is an independent uniform phase.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open LQGMetric MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.IGLaw

namespace MatedCRTHarmonic.GMS4cP

/-- Reduction of an input process at the unit circle about `0`, modulo the period `r`, on positive radii. -/
def l43pNorm (r : ℝ) [Fact (0 < r)] (K : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  posIn fun ρ v => K ρ v - K 1 0 + modRep r (K 1 0)

section norm

variable (r : ℝ) [Fact (0 < r)]

theorem measurable_l43pNorm : Measurable (l43pNorm r) := by
  have h10 : Measurable fun K : ℝ → ℂ → ℝ => K 1 0 :=
    (measurable_pi_apply (0 : ℂ)).comp (measurable_pi_apply (1 : ℝ))
  refine measurable_posIn.comp (measurable_pi_iff.2 fun ρ => measurable_pi_iff.2 fun v => ?_)
  have h1 : Measurable fun K : ℝ → ℂ → ℝ => K ρ v :=
    (measurable_pi_apply v).comp (measurable_pi_apply ρ)
  have h2 : Measurable fun K : ℝ → ℂ → ℝ => modRep r (K 1 0) := (measurable_modRep r).comp h10
  exact (h1.sub h10).add h2

theorem modRep_add_int_mul (x : ℝ) (k : ℤ) : modRep r (x + r * k) = modRep r x := by
  have h0 : ((r * k : ℝ) : AddCircle r) = 0 :=
    (AddCircle.coe_eq_zero_iff r).2 ⟨k, by rw [zsmul_eq_mul, mul_comm]⟩
  unfold modRep
  rw [AddCircle.coe_add, h0, add_zero]

theorem modRep_of_mem {x : ℝ} (hx : x ∈ Ico 0 r) : modRep r x = x := by
  unfold modRep addCircleRepresentative
  exact AddCircle.equivIco_coe_of_mem (by simpa using hx)

theorem l43pNorm_addIn (K : ℝ → ℂ → ℝ) (k : ℤ) :
    l43pNorm r (addIn (r * k) K) = l43pNorm r K := by
  unfold l43pNorm
  congr 1
  funext ρ v
  simp only [addIn, modRep_add_int_mul]
  ring

theorem l43pNorm_posIn (K : ℝ → ℂ → ℝ) : l43pNorm r (posIn K) = l43pNorm r K := by
  unfold l43pNorm
  funext ρ v
  rcases le_or_gt ρ 0 with hρ | hρ
  · rw [posIn_apply_of_nonpos hρ, posIn_apply_of_nonpos hρ]
  · rw [posIn_apply_of_pos hρ, posIn_apply_of_pos hρ, posIn_apply_of_pos hρ,
      posIn_apply_of_pos one_pos]

theorem l43pNorm_of_mem (K : ℝ → ℂ → ℝ) (h : K 1 0 ∈ Ico 0 r) : l43pNorm r K = posIn K := by
  unfold l43pNorm
  congr 1
  funext ρ v
  rw [modRep_of_mem r h]
  ring

theorem exists_l43pNorm_eq (K : ℝ → ℂ → ℝ) : ∃ k : ℤ, l43pNorm r K = posIn (addIn (r * k) K) := by
  obtain ⟨k, hk⟩ := exists_int_eq_modRep_add r (K 1 0)
  refine ⟨-k, ?_⟩
  unfold l43pNorm
  congr 1
  funext ρ v
  simp only [addIn]
  push_cast
  linarith

end norm

/-- **The renormalized pulled-back input has the law of the input.** For a normalized whole-plane GFF `h` and
an independent uniform phase `U` on `[0, r)`, the reduction at the unit circle of the pullback of
`circleAvg h + U` by `ψ(v) = z + s v` has the law of the positive-radius part of `circleAvg h + U`. -/
theorem map_l43pNorm_igPullback {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → Field} {U : Ω → ℝ} {r : ℝ} [Fact (0 < r)]
    (hh : IsNormalizedWPGFF h P) (hUlaw : P.map U = volume[|Ico (0 : ℝ) r])
    (hind : IndepFun h U P) (z : ℂ) {s : ℝ} (hs : 0 < s) :
    P.map (fun ω => l43pNorm r (igPullback γ z s 0 (igCircleAvgInput (h ω, U ω)))) =
      P.map (fun ω => posIn (igCircleAvgInput (h ω, U ω))) := by
  have hUm : AEMeasurable U P := MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif Fact.out hUlaw
  set H : Ω → ℝ → ℂ → ℝ := fun ω => igCircleAvgInput (h ω, U ω) with hHdef
  have hp : AEMeasurable (fun ω => (h ω, U ω)) P := hh.1.measurable.aemeasurable.prodMk hUm
  have hH : AEMeasurable H P := measurable_igCircleAvgInput.comp_aemeasurable hp
  -- the model field and scalars (IGCO's construction at rotation angle `0`)
  set h'' : Ω → Field := fun ω => affField s 0 z (h ω) with hh''def
  have hcm : Measurable fun ω => circleAvg (h ω) s z :=
    (LQGMetric.measurable_circleAvg_left s z).comp hh.1.measurable
  have hh'gff : IsWholePlaneGFF (fun ω => MoTPort.rotateField 0 (affineComp s z (h ω))) P :=
    IsWholePlaneGFF.rotateField (hh.1.affineComp hs z) 0
  have hh''gff : IsWholePlaneGFF h'' P := hh'gff.addConst hcm.neg
  have hcov : ∀ᵐ ω ∂P, ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ,
      circleAvg (MoTPort.rotateField 0 (affineComp s z (h ω))) ρ w =
        circleAvg (h ω) (s * ρ) ((s : ℂ) * Complex.exp ((0 : ℝ) * Complex.I) * w + z) :=
    ae_circleAvg_affineRotate_all hh.1 0 hs z
  have hadd : ∀ w : ℂ, ∀ ρ : ℝ, 0 < ρ → ∀ᵐ ω ∂P, ∀ a : ℝ,
      circleAvg (addConst (MoTPort.rotateField 0 (affineComp s z (h ω))) a) ρ w =
        circleAvg (MoTPort.rotateField 0 (affineComp s z (h ω))) ρ w + a :=
    fun w ρ hρ => CircleAvg.ae_circleAvg_addConst hh'gff w hρ
  have hh''norm : IsNormalizedWPGFF h'' P := by
    refine ⟨hh''gff, ?_⟩
    filter_upwards [hcov, hadd 0 1 one_pos] with ω hω hadd1
    show circleAvg (addConst (MoTPort.rotateField 0 (affineComp s z (h ω)))
      (-(circleAvg (h ω) s z))) 1 0 = 0
    rw [hadd1, hω 1 one_pos 0]
    simp
  set Vf : Field → ℝ := fun x => circleAvg x s z - igChi γ * 0 with hVf
  have hVfm : Measurable Vf := (LQGMetric.measurable_circleAvg_left s z).sub_const _
  set U' : Ω → ℝ := fun ω => modRep r (Vf (h ω) + U ω) with hU'def
  have hU'm : AEMeasurable U' P :=
    (measurable_modRep r).comp_aemeasurable ((hVfm.comp hh.1.measurable).aemeasurable.add hUm)
  have hpairU' : P.map (fun ω => (h ω, U' ω)) = P.map (fun ω => (h ω, U ω)) :=
    map_pair_shift_mod hh.1.measurable hUlaw hind hVfm
  have hGm : Measurable fun p : Field × ℝ => (affField s 0 z p.1, p.2) :=
    ((measurable_affField s 0 z).comp measurable_fst).prodMk measurable_snd
  have hp' : AEMeasurable (fun ω => (h ω, U' ω)) P := hh.1.measurable.aemeasurable.prodMk hU'm
  have hp'' : AEMeasurable (fun ω => (h'' ω, U' ω)) P :=
    hh''gff.measurable.aemeasurable.prodMk hU'm
  have hlaw'' : P.map (fun ω => (h'' ω, U' ω)) = P.map (fun ω => (h ω, U ω)) := by
    have e1 : P.map (fun ω => (h'' ω, U' ω)) = P.map (fun ω => (h'' ω, U ω)) := by
      calc P.map (fun ω => (h'' ω, U' ω)) =
          (P.map (fun ω => (h ω, U' ω))).map fun p => (affField s 0 z p.1, p.2) :=
            (AEMeasurable.map_map_of_aemeasurable hGm.aemeasurable hp').symm
        _ = (P.map (fun ω => (h ω, U ω))).map fun p => (affField s 0 z p.1, p.2) := by
            rw [hpairU']
        _ = P.map (fun ω => (h'' ω, U ω)) :=
            AEMeasurable.map_map_of_aemeasurable hGm.aemeasurable hp
    have hind'' : IndepFun h'' U P := hind.comp (measurable_affField s 0 z) measurable_id
    rw [e1, (indepFun_iff_map_prod_eq_prod_map_map hh''gff.measurable.aemeasurable hUm).1 hind'',
      (indepFun_iff_map_prod_eq_prod_map_map hh.1.measurable.aemeasurable hUm).1 hind,
      CircleAvg.map_eq_of_isNormalizedWPGFF hh''norm hh]
  -- the transformed input agrees coordinatewise with the model process
  set Kp : Ω → ℝ → ℂ → ℝ := fun ω => posIn (igPullback γ z s 0 (H ω)) with hKpdef
  set M : Ω → ℝ → ℂ → ℝ := fun ω => posIn (igCircleAvgInput (h'' ω, Vf (h ω) + U ω)) with hMdef
  have hKpm : AEMeasurable Kp P :=
    (measurable_posIn.comp (measurable_igPullback γ z s 0)).comp_aemeasurable hH
  have hMm : AEMeasurable M P :=
    (measurable_posIn.comp measurable_igCircleAvgInput).comp_aemeasurable
      (hh''gff.measurable.aemeasurable.prodMk ((hVfm.comp hh.1.measurable).aemeasurable.add hUm))
  have hKM : P.map Kp = P.map M := by
    refine map_eq_of_forall_ae_eq hKpm hMm fun ρ w => ?_
    rcases le_or_gt ρ 0 with hρ | hρ
    · refine Eventually.of_forall fun ω => ?_
      change posIn _ ρ w = posIn _ ρ w
      rw [posIn_apply_of_nonpos hρ, posIn_apply_of_nonpos hρ]
    · filter_upwards [hcov, hadd w ρ hρ] with ω hω haddω
      change posIn _ ρ w = posIn _ ρ w
      rw [posIn_apply_of_pos hρ, posIn_apply_of_pos hρ]
      change circleAvg (h ω) (s * ρ) (z + (s : ℂ) * Complex.exp ((0 : ℝ) * Complex.I) * w) +
          U ω - igChi γ * 0 =
        circleAvg (addConst (MoTPort.rotateField 0 (affineComp s z (h ω)))
          (-(circleAvg (h ω) s z))) ρ w + (circleAvg (h ω) s z - igChi γ * 0 + U ω)
      rw [haddω, hω ρ hρ w, add_comm z]
      ring
  -- the model process, reduced
  have hMred : ∀ ω, l43pNorm r (M ω) = l43pNorm r (igCircleAvgInput (h'' ω, U' ω)) := by
    intro ω
    obtain ⟨k, hk⟩ := exists_int_eq_modRep_add r (Vf (h ω) + U ω)
    have e : M ω = posIn (addIn (r * k) (igCircleAvgInput (h'' ω, U' ω))) := by
      have hk' : Vf (h ω) + U ω = U' ω + r * k := hk
      show posIn (igCircleAvgInput (h'' ω, Vf (h ω) + U ω)) = _
      rw [hk', igCircleAvgInput_add]
    rw [e, l43pNorm_posIn, l43pNorm_addIn]
  -- the bundle input is already reduced
  have hUmem : ∀ᵐ ω ∂P, U ω ∈ Ico (0 : ℝ) r := by
    have hcond : ∀ᵐ x ∂(volume[|Ico (0 : ℝ) r]), x ∈ Ico (0 : ℝ) r :=
      ae_cond_mem measurableSet_Ico
    rw [← hUlaw] at hcond
    exact ae_of_ae_map hUm hcond
  have hfin : (fun ω => l43pNorm r (igCircleAvgInput (h ω, U ω))) =ᵐ[P]
      fun ω => posIn (igCircleAvgInput (h ω, U ω)) := by
    filter_upwards [hh.2, hUmem] with ω h0 hU
    apply l43pNorm_of_mem
    change circleAvg (h ω) 1 0 + U ω ∈ Ico (0 : ℝ) r
    rw [h0, zero_add]
    exact hU
  have hNm : Measurable fun x : Field × ℝ => l43pNorm r (igCircleAvgInput x) :=
    (measurable_l43pNorm r).comp measurable_igCircleAvgInput
  calc P.map (fun ω => l43pNorm r (igPullback γ z s 0 (H ω)))
      = P.map (fun ω => l43pNorm r (Kp ω)) := by
        congr 1
        funext ω
        exact (l43pNorm_posIn r _).symm
    _ = (P.map Kp).map (l43pNorm r) :=
        (AEMeasurable.map_map_of_aemeasurable (measurable_l43pNorm r).aemeasurable hKpm).symm
    _ = (P.map M).map (l43pNorm r) := by rw [hKM]
    _ = P.map (fun ω => l43pNorm r (M ω)) :=
        AEMeasurable.map_map_of_aemeasurable (measurable_l43pNorm r).aemeasurable hMm
    _ = P.map (fun ω => l43pNorm r (igCircleAvgInput (h'' ω, U' ω))) := by
        congr 1
        funext ω
        exact hMred ω
    _ = (P.map (fun ω => (h'' ω, U' ω))).map fun x => l43pNorm r (igCircleAvgInput x) :=
        (AEMeasurable.map_map_of_aemeasurable hNm.aemeasurable hp'').symm
    _ = (P.map (fun ω => (h ω, U ω))).map fun x => l43pNorm r (igCircleAvgInput x) := by
        rw [hlaw'']
    _ = P.map (fun ω => l43pNorm r (igCircleAvgInput (h ω, U ω))) :=
        AEMeasurable.map_map_of_aemeasurable hNm.aemeasurable hp
    _ = P.map (fun ω => posIn (H ω)) := Measure.map_congr hfin

end MatedCRTHarmonic.GMS4cP
