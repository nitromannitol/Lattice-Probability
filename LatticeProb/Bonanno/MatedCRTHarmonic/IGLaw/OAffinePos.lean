/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.IGLaw.OAffinePos at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OCounter

/-!
# Affine invariance of the curve law under the corrected (positive-radius) `igMap` clause

`OCounter` shows that the frozen bundle's `igMap`, whose `Φ` reads the full circle-average process including
the junk radius `0`, does not transport the law of the IG input under dilations or translations. The proposed
v3.1 correction makes `Φ` read only positive radii: the input is `restrictCircles univ H` (zero for `ρ ≤ 0`),
where `H = circleAvg hIG₀ + U` (the locality clause already uses `restrictCircles`). This is `IGMapPos`.

Under `IGMapPos` we prove the full affine invariance of the imaginary-geometry covariance statement
(`map_affineReroot_of_ccPos`, `IsMatingOfTreesCoupling.map_affineReroot_of_igMapPos`):

`P.map (affineReroot z₀ s φ ∘ ηL) = P.map ηL` for all `z₀ ∈ ℂ`, `s > 0`, `φ ∈ ℝ`.

Proof. The coordinate clause at full turns gives `Φ`'s integer-period invariance, and at the identity it gives
`firstHit ηL 0 = 0` (with transience). For `ψ w = z₀ + s e^{iφ} w`, the field `h' = hIG₀ ∘ ψ`
(`rotateField φ (affineComp s z₀ hIG₀)`) recentred by `c = circleAvg hIG₀ s z₀` is a normalized whole-plane GFF
`h''`, and the scalar `(c − χφ + U) mod 2πχ` is uniform and independent of `hIG₀` (`map_pair_shift_mod`), so
`(h'', (c − χφ + U) mod 2πχ)` has the law of `(hIG₀, U)`. At every positive radius the transformed input is a.s.
`circleAvg h'' + (c − χφ + U)`, and at radii `≤ 0` both processes vanish, so the two positive-radius processes have
the same law (`map_eq_of_forall_ae_eq`); periodicity removes the integer multiple of `2πχ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace MatedCRTHarmonic.IGLaw

open LQGMetric MatedCRTHarmonic.MatedCRT

/-! ## The positive-radius input -/

/-- The circle-average process read at positive radii only (`restrictCircles univ`: zero for `ρ ≤ 0`). -/
abbrev posIn (K : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ := restrictCircles univ K

lemma posIn_apply_of_pos {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) (K : ℝ → ℂ → ℝ) :
    posIn K ρ w = K ρ w := by
  simp [restrictCircles, hρ]

lemma posIn_apply_of_nonpos {ρ : ℝ} (hρ : ρ ≤ 0) (w : ℂ) (K : ℝ → ℂ → ℝ) :
    posIn K ρ w = 0 := by
  simp [restrictCircles, not_lt.2 hρ]

lemma measurable_posIn : Measurable posIn :=
  measurable_pi_iff.2 fun ρ => measurable_pi_iff.2 fun w => by
    rcases le_or_gt ρ 0 with hρ | hρ
    · have e : (fun K : ℝ → ℂ → ℝ => posIn K ρ w) = fun _ => 0 :=
        funext fun K => posIn_apply_of_nonpos hρ w K
      rw [e]
      exact measurable_const
    · have e : (fun K : ℝ → ℂ → ℝ => posIn K ρ w) = fun K => K ρ w :=
        funext fun K => posIn_apply_of_pos hρ w K
      rw [e]
      have h1 : Measurable fun K : ℝ → ℂ → ℝ => K ρ := measurable_pi_apply ρ
      have h2 : Measurable fun f : ℂ → ℝ => f w := measurable_pi_apply w
      exact h2.comp h1

lemma posIn_igPullback_id (γ : ℝ) (K : ℝ → ℂ → ℝ) : posIn (igPullback γ 0 1 0 K) = posIn K := by
  rw [igPullback_one_zero]

/-- **The corrected (positive-radius) `igMap` clause** (replacement of the factorization and
coordinate-change parts of the bundle field `igMap`, same sources: [18], IG1, IG4): a
measurable `Φ` reading the IG circle-average process at positive radii only, with `ηL = Φ(H⁺)` and the
coordinate change `Φ((igPullback γ z₀ s φ H)⁺) = affineReroot z₀ s φ ηL`, where `K⁺ = restrictCircles univ K`. -/
def IGMapPos (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (hIG₀ : Ω → Field) (U : Ω → ℝ)
    (ηL : Ω → C(ℝ, ℂ)) : Prop :=
  ∃ Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ), Measurable Φ ∧
    (∀ᵐ ω ∂P, ηL ω = Φ (restrictCircles univ (fun ρ w => circleAvg (hIG₀ ω) ρ w + U ω))) ∧
    ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → ∀ᵐ ω ∂P,
      Φ (restrictCircles univ (igPullback γ z₀ s φ (fun ρ w => circleAvg (hIG₀ ω) ρ w + U ω))) =
        affineReroot z₀ s φ (ηL ω)

/-! ## The model field -/

/-- The normalized pullback field `x ∘ ψ − x_s(z₀)`, `ψ w = z₀ + s e^{iφ} w`. -/
def affField (s φ : ℝ) (z₀ : ℂ) (x : Field) : Field :=
  addConst (MoTPort.rotateField φ (affineComp s z₀ x)) (-(circleAvg x s z₀))

lemma measurable_affField (s φ : ℝ) (z₀ : ℂ) : Measurable (affField s φ z₀) := by
  refine GFFInv.measurable_distC_iff.2 fun f => ?_
  simp only [affField, GFFInv.addConst_apply, MoTPort.rotateField_apply, GFFInv.affineComp_apply]
  exact ((GFFInv.measurable_pair _).const_mul _).add
    ((LQGMetric.measurable_circleAvg_left s z₀).neg.const_mul _)

/-! ## The generic core -/

section Core

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → Field} {U : Ω → ℝ} {ηL : Ω → C(ℝ, ℂ)} {Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ)}

omit [IsProbabilityMeasure P] in
/-- The root time is `0`, from the identity coordinate clause and transience. -/
theorem ae_firstHit_zero_of_ccPos
    (hroot : ∀ᵐ ω ∂P, ηL ω = Φ (posIn (igCircleAvgInput (h ω, U ω))))
    (hcc : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → ∀ᵐ ω ∂P,
      Φ (posIn (igPullback γ z₀ s φ (igCircleAvgInput (h ω, U ω)))) = affineReroot z₀ s φ (ηL ω))
    (htr : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ)) :
    ∀ᵐ ω ∂P, firstHit (ηL ω) 0 = 0 := by
  filter_upwards [hroot, hcc 0 1 0 one_pos, htr] with ω hr hc ht
  rw [posIn_igPullback_id] at hc
  have hfix : ∀ t, ηL ω t = ηL ω (firstHit (ηL ω) 0 + t) := by
    intro t
    have e := congrArg (fun c : C(ℝ, ℂ) => c t) (hr.trans hc)
    simpa [affineReroot] using e
  exact time_shift_eq_zero_of_transient (ηL ω) _ ht hfix

omit [IsProbabilityMeasure P] in
/-- Integer-period invariance of `Φ` on the positive-radius input. -/
theorem ae_periodic_of_ccPos
    (hroot : ∀ᵐ ω ∂P, ηL ω = Φ (posIn (igCircleAvgInput (h ω, U ω))))
    (hcc : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → ∀ᵐ ω ∂P,
      Φ (posIn (igPullback γ z₀ s φ (igCircleAvgInput (h ω, U ω)))) = affineReroot z₀ s φ (ηL ω))
    (hτ : ∀ᵐ ω ∂P, firstHit (ηL ω) 0 = 0) :
    ∀ᵐ ω ∂P, ∀ k : ℤ,
      Φ (posIn (addIn (2 * Real.pi * igChi γ * k) (igCircleAvgInput (h ω, U ω)))) =
        Φ (posIn (igCircleAvgInput (h ω, U ω))) := by
  refine ae_all_iff.2 fun k => ?_
  filter_upwards [hroot, hcc 0 1 (2 * Real.pi * ((-k : ℤ) : ℝ)) one_pos, hτ] with ω hr hc ht
  rw [igPullback_period_neg, affineReroot_zero_one_of_firstHit _ _ ht,
    show -(2 * Real.pi * ((-k : ℤ) : ℝ)) = 2 * Real.pi * (k : ℝ) by push_cast; ring,
    rotCurve_two_pi_int] at hc
  rw [hc, hr]

lemma measurableSet_periodicPos (hΦ : Measurable Φ) (r : ℝ) :
    MeasurableSet {x : Field × ℝ | ∀ k : ℤ, Φ (posIn (addIn (r * k) (igCircleAvgInput x))) =
      Φ (posIn (igCircleAvgInput x))} := by
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => measurableSet_eq_curve
    (hΦ.comp (measurable_posIn.comp ((measurable_addIn _).comp measurable_igCircleAvgInput)))
    (hΦ.comp (measurable_posIn.comp measurable_igCircleAvgInput))

/-- **Affine invariance of the curve law** from the corrected (positive-radius) `igMap` clauses. -/
theorem map_affineReroot_of_ccPos (hh : IsNormalizedWPGFF h P)
    (hUlaw : P.map U = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)]) (hind : IndepFun h U P)
    (hΦ : Measurable Φ)
    (hroot : ∀ᵐ ω ∂P, ηL ω = Φ (posIn (igCircleAvgInput (h ω, U ω))))
    (hcc : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → ∀ᵐ ω ∂P,
      Φ (posIn (igPullback γ z₀ s φ (igCircleAvgInput (h ω, U ω)))) = affineReroot z₀ s φ (ηL ω))
    (htr : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ))
    (z₀ : ℂ) {s : ℝ} (hs : 0 < s) (φ : ℝ) :
    P.map (fun ω => affineReroot z₀ s φ (ηL ω)) = P.map ηL := by
  set r : ℝ := 2 * Real.pi * igChi γ with hr
  have hrpos : 0 < r := period_pos_of_uniform hUlaw
  have : Fact (0 < r) := ⟨hrpos⟩
  have hUm : AEMeasurable U P := MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif hrpos hUlaw
  have hτ := ae_firstHit_zero_of_ccPos hroot hcc htr
  have hper := ae_periodic_of_ccPos hroot hcc hτ
  set H : Ω → ℝ → ℂ → ℝ := fun ω => igCircleAvgInput (h ω, U ω) with hHdef
  have hp : AEMeasurable (fun ω => (h ω, U ω)) P := hh.1.measurable.aemeasurable.prodMk hUm
  have hH : AEMeasurable H P := measurable_igCircleAvgInput.comp_aemeasurable hp
  -- the model field and scalars
  set h'' : Ω → Field := fun ω => affField s φ z₀ (h ω) with hh''def
  have hcm : Measurable fun ω => circleAvg (h ω) s z₀ :=
    (LQGMetric.measurable_circleAvg_left s z₀).comp hh.1.measurable
  have hh'gff : IsWholePlaneGFF (fun ω => MoTPort.rotateField φ (affineComp s z₀ (h ω))) P :=
    IsWholePlaneGFF.rotateField (hh.1.affineComp hs z₀) φ
  have hh''gff : IsWholePlaneGFF h'' P := hh'gff.addConst hcm.neg
  have hcov : ∀ᵐ ω ∂P, ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ,
      circleAvg (MoTPort.rotateField φ (affineComp s z₀ (h ω))) ρ w =
        circleAvg (h ω) (s * ρ) ((s : ℂ) * Complex.exp (φ * Complex.I) * w + z₀) :=
    ae_circleAvg_affineRotate_all hh.1 φ hs z₀
  have hadd : ∀ w : ℂ, ∀ ρ : ℝ, 0 < ρ → ∀ᵐ ω ∂P, ∀ a : ℝ,
      circleAvg (addConst (MoTPort.rotateField φ (affineComp s z₀ (h ω))) a) ρ w =
        circleAvg (MoTPort.rotateField φ (affineComp s z₀ (h ω))) ρ w + a :=
    fun w ρ hρ => CircleAvg.ae_circleAvg_addConst hh'gff w hρ
  have hh''norm : IsNormalizedWPGFF h'' P := by
    refine ⟨hh''gff, ?_⟩
    filter_upwards [hcov, hadd 0 1 one_pos] with ω hω hadd1
    show circleAvg (addConst (MoTPort.rotateField φ (affineComp s z₀ (h ω)))
      (-(circleAvg (h ω) s z₀))) 1 0 = 0
    rw [hadd1, hω 1 one_pos 0]
    simp
  -- the reduced scalar
  set Vf : Field → ℝ := fun x => circleAvg x s z₀ - igChi γ * φ with hVf
  have hVfm : Measurable Vf := (LQGMetric.measurable_circleAvg_left s z₀).sub_const _
  set U' : Ω → ℝ := fun ω => modRep r (Vf (h ω) + U ω) with hU'def
  have hU'm : AEMeasurable U' P :=
    (measurable_modRep r).comp_aemeasurable ((hVfm.comp hh.1.measurable).aemeasurable.add hUm)
  have hpairU' : P.map (fun ω => (h ω, U' ω)) = P.map (fun ω => (h ω, U ω)) :=
    map_pair_shift_mod hh.1.measurable hUlaw hind hVfm
  -- the law of `(h'', U')`
  have hGm : Measurable fun p : Field × ℝ => (affField s φ z₀ p.1, p.2) :=
    ((measurable_affField s φ z₀).comp measurable_fst).prodMk measurable_snd
  have hp' : AEMeasurable (fun ω => (h ω, U' ω)) P := hh.1.measurable.aemeasurable.prodMk hU'm
  have hp'' : AEMeasurable (fun ω => (h'' ω, U' ω)) P := hh''gff.measurable.aemeasurable.prodMk hU'm
  have hlaw'' : P.map (fun ω => (h'' ω, U' ω)) = P.map (fun ω => (h ω, U ω)) := by
    have e1 : P.map (fun ω => (h'' ω, U' ω)) = P.map (fun ω => (h'' ω, U ω)) := by
      calc P.map (fun ω => (h'' ω, U' ω)) =
          (P.map (fun ω => (h ω, U' ω))).map fun p => (affField s φ z₀ p.1, p.2) :=
            (AEMeasurable.map_map_of_aemeasurable hGm.aemeasurable hp').symm
        _ = (P.map (fun ω => (h ω, U ω))).map fun p => (affField s φ z₀ p.1, p.2) := by
            rw [hpairU']
        _ = P.map (fun ω => (h'' ω, U ω)) :=
            AEMeasurable.map_map_of_aemeasurable hGm.aemeasurable hp
    have hind'' : IndepFun h'' U P := hind.comp (measurable_affField s φ z₀) measurable_id
    rw [e1, (indepFun_iff_map_prod_eq_prod_map_map hh''gff.measurable.aemeasurable hUm).1 hind'',
      (indepFun_iff_map_prod_eq_prod_map_map hh.1.measurable.aemeasurable hUm).1 hind,
      CircleAvg.map_eq_of_isNormalizedWPGFF hh''norm hh]
  -- the transformed input agrees coordinatewise with the model process
  set Kp : Ω → ℝ → ℂ → ℝ := fun ω => posIn (igPullback γ z₀ s φ (H ω)) with hKpdef
  set M : Ω → ℝ → ℂ → ℝ := fun ω => posIn (igCircleAvgInput (h'' ω, Vf (h ω) + U ω)) with hMdef
  have hKpm : AEMeasurable Kp P :=
    (measurable_posIn.comp (measurable_igPullback γ z₀ s φ)).comp_aemeasurable hH
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
      change circleAvg (h ω) (s * ρ) (z₀ + (s : ℂ) * Complex.exp (φ * Complex.I) * w) + U ω -
          igChi γ * φ =
        circleAvg (addConst (MoTPort.rotateField φ (affineComp s z₀ (h ω)))
          (-(circleAvg (h ω) s z₀))) ρ w + (circleAvg (h ω) s z₀ - igChi γ * φ + U ω)
      rw [haddω, hω ρ hρ w, add_comm z₀]
      ring
  -- periodicity transferred to the model scalar
  have hper' : ∀ᵐ ω ∂P, (h'' ω, U' ω) ∈ {x : Field × ℝ | ∀ k : ℤ,
      Φ (posIn (addIn (r * k) (igCircleAvgInput x))) = Φ (posIn (igCircleAvgInput x))} :=
    ae_of_map_eq hp hp'' hlaw''.symm (measurableSet_periodicPos hΦ r) hper
  have hMred : (fun ω => Φ (M ω)) =ᵐ[P] fun ω => Φ (posIn (igCircleAvgInput (h'' ω, U' ω))) := by
    filter_upwards [hper'] with ω hω
    obtain ⟨k, hk⟩ := exists_int_eq_modRep_add r (Vf (h ω) + U ω)
    have e : M ω = posIn (addIn (r * k) (igCircleAvgInput (h'' ω, U' ω))) := by
      have hk' : Vf (h ω) + U ω = U' ω + r * k := hk
      show posIn (igCircleAvgInput (h'' ω, Vf (h ω) + U ω)) = _
      rw [hk', igCircleAvgInput_add]
    rw [e]
    exact hω k
  -- assemble
  have hΦP : Measurable fun x : Field × ℝ => Φ (posIn (igCircleAvgInput x)) :=
    hΦ.comp (measurable_posIn.comp measurable_igCircleAvgInput)
  calc P.map (fun ω => affineReroot z₀ s φ (ηL ω)) = P.map (fun ω => Φ (Kp ω)) :=
        Measure.map_congr (by
          filter_upwards [hcc z₀ s φ hs] with ω hω
          exact hω.symm)
    _ = (P.map Kp).map Φ := (AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hKpm).symm
    _ = (P.map M).map Φ := by rw [hKM]
    _ = P.map (fun ω => Φ (M ω)) := AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hMm
    _ = P.map (fun ω => Φ (posIn (igCircleAvgInput (h'' ω, U' ω)))) := Measure.map_congr hMred
    _ = (P.map (fun ω => (h'' ω, U' ω))).map fun x => Φ (posIn (igCircleAvgInput x)) :=
        (AEMeasurable.map_map_of_aemeasurable hΦP.aemeasurable hp'').symm
    _ = (P.map (fun ω => (h ω, U ω))).map fun x => Φ (posIn (igCircleAvgInput x)) := by
        rw [hlaw'']
    _ = P.map (fun ω => Φ (posIn (igCircleAvgInput (h ω, U ω)))) :=
        AEMeasurable.map_map_of_aemeasurable hΦP.aemeasurable hp
    _ = P.map ηL := (Measure.map_congr hroot).symm

end Core

/-! ## The bundle statements under the corrected clause -/

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
  {B B' B₀ B₀' : NNReal → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}

/-- **Affine invariance of whole-plane space-filling SLE** (the imaginary-geometry covariance statement), for a coupling satisfying the
corrected clause `IGMapPos`: `law(affineReroot z₀ s φ ηL) = law(ηL)` for all `z₀`, `s > 0`, `φ`. -/
theorem IsMatingOfTreesCoupling.map_affineReroot_of_igMapPos
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hpos : IGMapPos γ P hIG₀ U ηL) (z₀ : ℂ) {s : ℝ} (hs : 0 < s) (φ : ℝ) :
    P.map (fun ω => affineReroot z₀ s φ (ηL ω)) = P.map ηL := by
  have : IsProbabilityMeasure P := hC.isProbabilityMeasure
  obtain ⟨Φ, hΦ, hroot, hcc⟩ := hpos
  have htr : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) := by
    filter_upwards [hC.spaceFilling] with ω hω
    exact hω.2.1
  exact map_affineReroot_of_ccPos hC.igField.1 hC.igField.2.1 hC.igField.2.2 hΦ hroot hcc htr
    z₀ hs φ

/-- Under the corrected clause, the root time is `0` almost surely. -/
theorem IsMatingOfTreesCoupling.ae_firstHit_zero_of_igMapPos
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hpos : IGMapPos γ P hIG₀ U ηL) : ∀ᵐ ω ∂P, firstHit (ηL ω) 0 = 0 := by
  obtain ⟨Φ, -, hroot, hcc⟩ := hpos
  have htr : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) := by
    filter_upwards [hC.spaceFilling] with ω hω
    exact hω.2.1
  exact ae_firstHit_zero_of_ccPos hroot hcc htr

end Bundle

end MatedCRTHarmonic.IGLaw
