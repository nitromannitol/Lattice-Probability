/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3Sec3W1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114W
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3Sec3W3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108M10
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112M2
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112M5
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112L3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112N3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108Q3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114U3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J11
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L38
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_8
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Asm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperFinal
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6

/-!
# CONF §3 (`Blueprint.CONFSection3`) from the remaining CONF leaves (task P2-CONFW)

Gwynne–Miller, *Confluence of geodesic paths and LQG metrics* (arXiv:1905.00381,
`confluence-final.tex`, C:line). `CONFSection3` bundles, at one parameter choice `p`:
* CONF Lemma 3.5 (C:1276): `confLem3_5At_delta` (proved; it also gives `δ < 1/8`, the parameter
  choice of CONF L3.2, C:1167);
* CONF Lemma 3.6 (C:1308): `conf36_lem3_6AtAE0_at` (S3Sec3W3), from CONF Lemma 3.3 for `fatG`
  (`l33Gen_fatG_lem2_10_at`, from **CONF Lemma 2.10 at the domains `confU`**,
  `CONFLem2_10AtConfU`, open, DEC-127) and DFGPS Lemma 3.8;
* CONF Lemma 3.8 (C:1493): `confLem3_8At_cited` (from LM L3.1 and DG Thm 1.5 (KU form), DG P3.21);
* CONF Theorem 3.9 (C:1506): `confThm3_9At_of_restCL` (S3T39J11), from L3.5, L3.6, DFGPS L3.8
  and **`CONFThm3_9RestCL`** (S3T39J9; open, DEC-120 §5, D130).
All four conjuncts use the same `p` (the one of `confLem3_5At_delta`).

DFGPS Lemma 3.8 is built as in the assemblies (`Assembly/MainOpenG.lean`):
`DFGPS.dfgpsLem3_8_of (DFGPS.dfgpsScaling_of_lem3_6 LM.lmLem3_1a (lem3_6_of_DG hKU hP321)) LM.lmLem3_1a`.
So `CONFSection3` also uses the DG results `DGThm1_5KU`, `DGProp3_21` (as CONF L3.8 does, through
DFGPS Prop 3.18); the assembly `MainOpenL` gets them from the DZZ inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace CONFW

open Blueprint CONF

/-- the remaining CONF Theorem 3.9 node (`CONFThm3_9RestCL`, DEC-120 §5, D130) at every parameter
choice as in CONF Lemma 3.5 with `δ < 1/8` and every Hölder exponent `χ ∈ (0, ξ(Q−2))` -/
def CONFThm3_9RestAll : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ p : CONFParams, p.Valid → p.δ < 1 / 8 → CONFLem3_5At γ D c p →
      ∀ χ ∈ Ioo (0 : ℝ) (xiGamma γ * (Q γ - 2)), CONFThm3_9RestCL γ D c p χ

/-- DFGPS Lemma 3.8 from the DG results (as in `Assembly/MainOpenG.lean`) -/
theorem dfgpsLem3_8_of_DG (hKU : DGThm1_5KU) (hP321 : DGProp3_21) : DFGPSLem3_8 :=
  DFGPS.dfgpsLem3_8_of (DFGPS.dfgpsScaling_of_lem3_6 LM.lmLem3_1a
    (DFGPS.L36.lem3_6_of_DG hKU hP321)) LM.lmLem3_1a

/-- **`Blueprint.CONFSection3`** from CONF Lemma 2.10 at the domains `confU` (DEC-127), the
remaining T3.9 node and the DG results `DGThm1_5KU`, `DGProp3_21` -/
theorem confSection3_of_leaves (hL : CONFLem2_10AtConfU) (hRest : CONFThm3_9RestAll)
    (hKU : DGThm1_5KU) (hP321 : DGProp3_21) : CONFSection3 := by
  intro γ hγ hγ2 D c hD
  have h38 : DFGPSLem3_8 := dfgpsLem3_8_of_DG hKU hP321
  obtain ⟨p, hp, hδ8, h35⟩ := confLem3_5At_delta hγ hγ2 hD
  have h36 : CONFLem3_6AtAE0 γ D c p :=
    conf36_lem3_6AtAE0_at h38 hL hγ hγ2 hp hδ8 hD
  refine ⟨p, hp, h35, h36, fun χ hχ => ⟨?_, ?_⟩⟩
  · exact confLem3_8At_cited LM.lmLem3_1a hKU hP321 hγ hγ2 hD p hp h35 χ hχ
  · exact confThm3_9At_of_restCL h38 hγ hγ2 hD hχ.1 h35 hp.2.2.2.2.2 h36
      (hRest γ hγ hγ2 D c hD p hp hδ8 h35 χ hχ)

end CONFW
end LQGMetric
