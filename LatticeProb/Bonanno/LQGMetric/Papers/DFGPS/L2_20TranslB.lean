/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_20TranslB at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20Transl
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenHeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.20: `Lem2_20Transl` (step 1 and assembly)

DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), T:1323–1324. Step 1 of
`L2_20Transl.lean`: the LFPP-level identity at centres `z` and `0` (translation of the heat kernel
and of paths, as in the proof of Lemma 2.6, T:847–855, and DFGPS's remark after Lemma 2.8 on
translations; Weyl scaling by a constant) and `h(· + z) − h_1(z) =ᵈ h`. Then `lem2_20Transl`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint GM.Tight LFPP

namespace L220

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

lemma affineComp_one_zero_l220 (g : DistC) : affineComp 1 0 g = g := by
  refine DFunLike.ext _ _ fun φ => ?_
  have e : testAffinePull 1 0 φ = φ := TestFunction.ext fun x => by
    rw [testAffinePull_apply _ _ one_ne_zero]; simp
  rw [GFFInv.affineComp_apply, e]; simp

/-- translation of LFPP distances, given the translation of the mollified fields -/
lemma lfppDistE_translate {ξ ε : ℝ} {g g' : DistC} {z : ℂ}
    (htr : ∀ x, heatMollify ε g' x = heatMollify ε g (x + z)) (u v : ℂ) :
    lfppDistE ξ ε g' u v = lfppDistE ξ ε g (u + z) (v + z) := by
  rw [lfppDistE_eq_lfppDOn, lfppDistE_eq_lfppDOn]
  have := lfppDOn_affine ξ (heatMollify ε g) (S := univ) (S' := univ) (b := z) (c := 1)
    one_ne_zero (fun x => by simp) u v
  rw [show z + 1 * u = u + z by ring, show z + 1 * v = v + z by ring, norm_one,
    ENNReal.ofReal_one, one_mul] at this
  rw [this]
  congr 1
  funext x
  rw [htr x, one_mul, add_comm]

omit [IsProbabilityMeasure P] in
/-- **Step 1 (identity)**: for `g = h(· + z) − h_1(z)`, a.s.
`e^{−ξ g_r(0)} 𝔞⁻¹D^ε_g(r·, r·) = e^{−ξ h_r(z)} 𝔞⁻¹D^ε_h(r· + z, r· + z)`. -/
theorem ae_lfppResc_translate (hh : IsWholePlaneGFF h P) (ξ : ℝ) {ε r : ℝ} (hε : 0 < ε)
    (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, lfppResc ξ ε r 0 (addConst (affineComp 1 z (h ω)) (-circleAvg (h ω) 1 z)) =
      lfppResc ξ ε r z (h ω) := by
  have hT := hh.affineComp one_pos z
  filter_upwards [lem2_6_ae_const hT ξ hε one_pos, ae_heatMollify_translate hh hε.ne' z,
    hT.ae_tendstoLocallyUniformly_heatMollify ε hε.ne',
    hh.ae_tendstoLocallyUniformly_heatMollify ε hε.ne',
    CircleAvg.ae_circleAvg_addConst hT 0 hr] with ω h6 htr hcT hc hca
  set c := circleAvg (h ω) 1 z
  set g := addConst (affineComp 1 z (h ω)) (-c)
  have hmg : ∀ x, heatMollify ε g x = heatMollify ε (h ω) (x + z) + -c := fun x => by
    rw [heatMollify_addConst_of_tendsto hε.ne'
      ((tendstoLocallyUniformlyOn_univ.2 hcT.1).tendsto_at (mem_univ x)), htr x]
  have hgc : Continuous (heatMollify ε g) := by
    have : heatMollify ε g = fun x => heatMollify ε (h ω) (x + z) + -c := funext hmg
    rw [this]; exact (hc.2.comp (continuous_id.add continuous_const)).add continuous_const
  have hcirc : circleAvg g r 0 = circleAvg (h ω) r z - c := by
    rw [hca, circleAvg_affineComp_one]; ring
  ext p
  simp only [lfppResc, ContinuousMap.smul_apply, ContinuousMap.comp_apply, affArgs_apply,
    smul_eq_mul]
  rw [lfppC_apply_of_continuous hgc, lfppC_apply_of_continuous hc.2]
  have hD : lfppDistE ξ ε g ((r : ℂ) * p.1 + 0) ((r : ℂ) * p.2 + 0) =
      ENNReal.ofReal (Real.exp (-ξ * c)) *
        lfppDistE ξ ε (h ω) ((r : ℂ) * p.1 + z) ((r : ℂ) * p.2 + z) := by
    have := h6 c ((r : ℂ) * p.1 + 0) ((r : ℂ) * p.2 + 0)
    rw [div_one, affineComp_one_zero_l220, inv_one, one_mul] at this
    simp only [Complex.ofReal_one, one_mul, add_zero] at this ⊢
    rw [this, lfppDistE_translate htr]
  simp only at hD ⊢
  rw [hcirc, hD, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hx : Real.exp (-ξ * (circleAvg (h ω) r z - c)) * Real.exp (-ξ * c) =
      Real.exp (-ξ * circleAvg (h ω) r z) := by
    rw [← Real.exp_add]; ring_nf
  calc Real.exp (-ξ * (circleAvg (h ω) r z - c)) * ((aEpsDF ξ ε)⁻¹ *
        (Real.exp (-ξ * c) * (lfppDistE ξ ε (h ω) (↑r * p.1 + z) (↑r * p.2 + z)).toReal))
      = (Real.exp (-ξ * (circleAvg (h ω) r z - c)) * Real.exp (-ξ * c)) * ((aEpsDF ξ ε)⁻¹ *
        (lfppDistE ξ ε (h ω) (↑r * p.1 + z) (↑r * p.2 + z)).toReal) := by ring
    _ = _ := by rw [hx]

omit [IsProbabilityMeasure P] in
/-- **Step 1 (laws)**: the LFPP laws at centres `z` and `0` coincide. -/
theorem map_lfppResc_eq (hh : IsNormalizedWPGFF h P) (ξ : ℝ) {ε r : ℝ} (hε : 0 < ε)
    (hr : 0 < r) (z : ℂ) :
    P.map (fun ω => lfppResc ξ ε r z (h ω)) = P.map (fun ω => lfppResc ξ ε r 0 (h ω)) := by
  have hT := hh.1.affineComp one_pos z
  have hnorm := map_normalize_eq hT hh.1
  simp only [circleAvg_affineComp_one] at hnorm
  have hnorm2 : P.map (fun ω => addConst (h ω) (-circleAvg (h ω) 1 0)) = P.map h :=
    Measure.map_congr (hh.2.mono fun ω hω => by
      simp only [hω, neg_zero, GFFLaw.addConst_zero'])
  set g : Ω → DistC := fun ω => addConst (affineComp 1 z (h ω)) (-circleAvg (h ω) 1 z)
  have hglaw : P.map g = P.map h := hnorm.trans hnorm2
  have hgm : Measurable g :=
    (hT.addConst (((measurable_circleAvg_left 1 z).comp hh.1.measurable).neg)).measurable
  set F : DistC → C(ℂ × ℂ, ℝ) := lfppResc ξ ε r 0
  have hF1 : AEMeasurable (lfppC ξ ε) (P.map h) :=
    aemeasurable_lfppC (h := id) (isGFFPlusBddCont_of_wp (GM.isWholePlaneGFF_id_map hh.1)) hε.ne'
  have hF : AEMeasurable F (P.map h) :=
    (Real.measurable_exp.comp (measurable_const.mul (measurable_circleAvg_left r 0))).aemeasurable.smul
      ((ContinuousMap.continuous_precomp (affArgs r 0)).measurable.comp_aemeasurable hF1)
  have hF' : AEMeasurable F (P.map g) := by rw [hglaw]; exact hF
  calc P.map (fun ω => lfppResc ξ ε r z (h ω)) = P.map (F ∘ g) :=
        Measure.map_congr ((ae_lfppResc_translate hh.1 ξ hε hr z).mono fun ω hω => hω.symm)
    _ = (P.map g).map F := (AEMeasurable.map_map_of_aemeasurable hF' hgm.aemeasurable).symm
    _ = (P.map h).map F := by rw [hglaw]
    _ = P.map (F ∘ h) := AEMeasurable.map_map_of_aemeasurable hF hh.1.measurable.aemeasurable
    _ = _ := rfl

end L220

open L220 in
/-- **Translation invariance in the proof of DFGPS Lemma 2.20** (T:1323–1324). -/
theorem lem2_20Transl : Lem2_20Transl := by
  intro γ hγ hγ2 Ω _ P _ h Dh εn hh hDm hεp hεt hconv z r hr
  have t1 := tendsto_law_lfppResc εn hεp Dh hh hDm hconv hr z
  have t0 := tendsto_law_lfppResc εn hεp Dh hh hDm hconv hr 0
  have heq : (fun n => L213.lawPM P (fun ω => lfppResc (xiGamma γ) (εn n) r z (h ω))) =
      fun n => L213.lawPM P (fun ω => lfppResc (xiGamma γ) (εn n) r 0 (h ω)) := by
    funext n; exact Subtype.ext (map_lfppResc_eq hh _ (hεp n) hr z)
  rw [heq] at t1
  exact congrArg Subtype.val (tendsto_nhds_unique (X := ProbabilityMeasure C(ℂ × ℂ, ℝ)) t1 t0)

end LQGMetric.DFGPS
