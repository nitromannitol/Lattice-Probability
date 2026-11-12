/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Thm12Sq2Fin at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm12Sq2C
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L217R
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12Blueprint
import LatticeProb.Bonanno.LQGMetric.Field.MarkovFinal
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P29SqA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinAsm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffFarA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenTrans
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenRatio
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffRed
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_13

/-!
# DFGPS Theorem 1.2 (existence) with DDDF Theorem 1 (2) on the square (task P2-DDDF6f)

`dfgps_existence_reduced_sq12`: `T12.dfgps_existence_reduced'` (Assembly/ExistenceReducedSq.lean)
with `Blueprint.DDDFThm1_2` replaced by `DDDF.DDDFThm1_2Sq` (through the `Q12` copies
`S6Thm12Sq2{A,B,C}`) and without the unused `Blueprint.DDDFProp28`.
`dfgps_existence_reduced_554`: the same with `DDDFThm1_2Sq` discharged by `DDDF.dddfThm1_2Sq_of`
(DDDF Theorem 1 (1), Proposition 29 on the square, (5.54)). Wiring only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.Q12

open Blueprint DDDF WhiteNoise T12

/-- **DFGPS Lemma 2.17** from the cited inputs, DDDF Prop 29 on the square only. -/
theorem lem2_17Sq (h11 : DDDFThm1_1) (h12 : DDDFThm1_2Sq) (h29 : DDDFProp29Sq) (hLM : LMLem2_1)
    (h699 : DDDFEq6_99) : Lem2_17 :=
  lem2_17_of_core' (lem2_8_proved' h11 h12 h29 hLM h699)
    (lem2_17Core hLM (lem2_8_proved' h11 h12 h29 hLM h699) lem2_1GffApprox)

/-- **DFGPS Lemma 2.20** from the cited inputs, DDDF Prop 29 on the square only. -/
theorem lem2_20Sq (hLM8 : LMCor1_8) (h11 : DDDFThm1_1) (h12 : DDDFThm1_2Sq)
    (h29 : DDDFProp29Sq) (hLM : LMLem2_1) (h13 : DDDFEq1_3) (h699 : DDDFEq6_99) : Lem2_20 :=
  lem2_20_of_bilip hLM8 (lem2_8_proved' h11 h12 h29 hLM h699) (lem2_17Sq h11 h12 h29 hLM h699)
    (lem2_20Bilip (lem2_13' h11 h12 h29 hLM h13 h699) lem2_20Transl)

/-- **DFGPS Theorem 1.2** (T:1339–1386) from the still-open cited inputs, with DDDF
Proposition 29 and Theorem 1 (2) only for `D = (−1,2)²` (no `DDDFProp28`). -/
theorem dfgps_existence_reduced_sq12 : DDDFThm1_1 → DDDFThm1_2Sq → DDDFEq1_3 → DDDFEq6_99 →
    DDDFProp29Sq → LMCor1_8 → DFGPSExistence := by
  intro h11 h12' h13' h699 h29 hLM8 γ hγ hγ2 ε hε hε0
  have hLM : LMLem2_1 := MarkovFinal.lmLem2_1
  have H28 := lem2_8_proved' h11 h12' h29 hLM h699
  have H20 := lem2_20Sq hLM8 h11 h12' h29 hLM h13' h699
  have H13 := lem2_13' h11 h12' h29 hLM h13' h699
  have H12 := lem2_12 H28
  have HG : Lem2_1GffApprox.{0} := lem2_1GffApprox.{0}
  obtain ⟨φ, hφ, Ω, _, P, _, h, Dh, hh, hDm, hlen, hconv, hJ⟩ :=
    exists_subseq_coupling_ae' H28 H20 hγ hγ2 ε hε hε0
  have hεs : ∀ k, 0 < ε (φ k) := fun k => hε _
  have hε0' : Tendsto (fun k => ε (φ k)) atTop (𝓝 0) := hε0.comp hφ.tendsto_atTop
  have hG : T12Good γ (fun k => ε (φ k)) hεs :=
    t12Good_of_coupling H28 HG hγ hγ2 hh hεs hε0' hlen hconv
  obtain ⟨c, hc⟩ := tightAcrossScales_patchT H13 HG H12 hγ hγ2 hεs hε0' hG hh hDm hlen hconv hJ
  refine ⟨patchT (xiGamma γ) (fun k => ε (φ k)) hεs, c,
    ⟨measurable_patchT,
      fun P _ h hh => (ae_length_weyl_isGFFPlusCont HG H12 hγ hγ2 hε0' hG hh).1,
      fun P _ h hh U => t12Locality HG H12 hγ hγ2 _ hεs hε0' hG P h hh U,
      fun P _ h hh => (ae_length_weyl_isGFFPlusCont HG H12 hγ hγ2 hε0' hG hh).2,
      fun P _ h hh z => ae_patchT_translate HG H12 hγ hγ2 hε0' hG hh z, hc⟩,
    φ, hφ, fun P _ h hh => tendstoInProbLU_patchT HG H12 hγ hγ2 hε0' hG hh⟩

/-- **DFGPS Theorem 1.2** from DDDF Theorem 1 (1), (5.54), (1.3), (6.99), Proposition 29 on
the square and LM Corollary 1.8 (neither `Blueprint.DDDFThm1_2` nor `Blueprint.DDDFProp29` nor
`Blueprint.DDDFProp28`). -/
theorem dfgps_existence_reduced_554 (h11 : DDDFThm1_1)
    (h554 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W → S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P)
    (h13 : DDDFEq1_3) (h699 : DDDFEq6_99) (h29 : DDDFProp29Sq) (hLM8 : LMCor1_8) :
    DFGPSExistence :=
  dfgps_existence_reduced_sq12 h11 (dddfThm1_2Sq_of h11 h29 h554) h13 h699 h29 hLM8

end LQGMetric.DFGPS.Q12
