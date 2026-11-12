/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L217R at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core3J
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20TranslB
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20BilipMain
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1RadialMain
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenTrans
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenRatio
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffRed
import LatticeProb.Bonanno.LQGMetric.Papers.LM.LocNest

/-!
# DFGPS Lemmas 2.17, 2.20 and Theorem 1.2 without `Blueprint.LMLem2_3`

Primed copies of `L217.isJointlyLocalFam_of_localAt`, `lem2_17_of_core`, `lem2_17`,
`lem2_20_of_core`, `lem2_20`, `T12.dfgps_existence_of_locality`: DFGPS use only the direction
(3) ⟹ (1) of LM Lemma 2.3 (T:1140), which is proved as `LM.isLocalMetric_of_form3`
(Papers/LM/LocNest.lean). Wiring only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint GM.Bilip

namespace L217

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **LM Def 1.2 for `(h', D')` from Def 2.15** via `LM.isLocalMetric_of_form3` -/
lemma isJointlyLocalFam_of_localAt' [IsProbabilityMeasure P] {h' : Ω → DistC}
    {D' : Ω → ContMetric} {I : Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞} (hh' : IsWholePlaneGFF h' P)
    (hD' : Measurable D') (hl : ∀ᵐ ω ∂P, (D' ω).IsLength) (hI : internalFam D' = I)
    (hloc : ∀ V : TopologicalSpace.Opens ℂ, LocalAt P h' I V) : IsJointlyLocalFam P h' I I := by
  have H := (LM.isLocalMetric_of_form3 hh'.measurable hD' hl
    (by subst hI; exact fun V => hloc V)).2.2
  rw [hI] at H
  intro V
  simpa only [sup_idem, sup_assoc] using H V

end L217

open L217

/-- **DFGPS Lemma 2.17** from its core case, Lemma 2.19 and Lemma 2.8 (no `LMLem2_3`). -/
theorem lem2_17_of_core' (h28 : Lem2_8) (hcore : Lem2_17Core) : Lem2_17 := by
  intro γ hγ hγ2 Ω mΩ P _ h Dh εn hh hDm hεp hε0 hconv
  set ξ := xiGamma γ
  have hlen : ∀ᵐ ω ∂P, (Dh ω).IsLength := ae_isLength_of_conv h28 hγ hγ2 hh hDm hεp hε0 hconv
  -- Lemma 2.19 removes the restriction `B_r(z) ⊂ V`
  have hloc : ∀ (z : ℂ) (r : ℝ) (V : TopologicalSpace.Opens ℂ), 0 < r →
      LocalAt P (normField h z r) (normFam ξ h Dh z r) V := fun z r V hr =>
    lem2_19 ξ hh.1 hDm hlen (fun z₀ r₀ V hr₀ hb => hcore γ hγ hγ2 P h Dh εn hh hDm hεp hε0
      hconv z₀ r₀ V hr₀ hb) z r V hr
  -- the scaled metrics `e^{−ξh_r(z)} D_h` and LM Lemma 2.3
  have hJL : ∀ (z : ℂ) (r : ℝ), 0 < r →
      IsJointlyLocalFam P (normField h z r) (normFam ξ h Dh z r) (normFam ξ h Dh z r) := by
    intro z r hr
    have hc : Measurable fun ω => -ξ * circleAvg (h ω) r z :=
      ((measurable_circleAvg_left r z).comp hh.1.measurable).const_mul _
    refine isJointlyLocalFam_of_localAt' (D' := fun ω => (Dh ω).smulPos _ (Real.exp_pos
      (-ξ * circleAvg (h ω) r z))) (hh.1.addConst ((measurable_circleAvg_left r z).comp
        hh.1.measurable).neg) (measurable_smulPos_rand hDm hc)
      (hlen.mono fun ω hω => ContMetric.isLength_smulPos _ hω) ?_ (fun V => hloc z r V hr)
    funext ω V u v
    exact ContMetric.internal_smulPos _ _ _ _ _
  refine ⟨⟨hDm, hDm, hlen.mono fun ω hω => ⟨hω, hω⟩, ?_⟩, fun z r hr => hJL z r hr⟩
  -- the base case: `h = h − h_1(0)` a.s.
  have hn : ∀ᵐ ω ∂P, normField h 0 1 ω = h ω := by
    filter_upwards [hh.2] with ω hω
    simp only [normField, hω, neg_zero, GFFLaw.addConst_zero']
  have hnI : ∀ W : Set ℂ, ∀ᵐ ω ∂P, internalFam Dh ω W = normFam ξ h Dh 0 1 ω W := fun W => by
    filter_upwards [hh.2] with ω hω
    funext u v
    simp only [normFam, internalFam, hω, mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  have hm₁ : Measurable (normField h 0 1) := L219.measurable_addConst_of hh.1.measurable
    ((measurable_circleAvg_left 1 0).comp hh.1.measurable).neg
  -- measurability of `D_h(·,·;W)` up to null events
  have hver : ∀ W : Set ℂ, IsOpen W → famSigma (internalFam Dh) W ≤ aeClosure P mΩ := by
    intro W hW
    obtain ⟨F, hF, hFe⟩ := measurable_internal hW
    refine famSigma_le_aeClosure_of_measurable (X := fun ω u v => F (Dh ω, u, v))
      (measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v =>
        hF.comp (hDm.prodMk measurable_const)) ?_
    filter_upwards [hlen] with ω hω
    funext u v
    exact hFe _ hω u v
  intro V
  have H := hJL 0 1 one_pos V
  have hOV : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  -- replace `h − h_1(0)` and `e^{−ξh_1(0)} D_h` by `h` and `D_h` on the two sides
  have H' := GM.Bilip.CondIndepEv.of_le_aeClosure H
    (sup_le ((famSigma_le_aeClosure_of_ae_eq (hnI V)).trans (aeClosure_mono le_sup_left))
      ((famSigma_le_aeClosure_of_ae_eq (hnI V)).trans (aeClosure_mono le_sup_right)))
    (sup_le (sup_le ((fieldSigmaClosed_le_aeClosure_of_ae_eq (hn.mono fun ω hω => hω.symm)
        _).trans (aeClosure_mono (le_sup_left.trans le_sup_left)))
      ((famSigma_le_aeClosure_of_ae_eq (hnI _)).trans
        (aeClosure_mono (le_sup_right.trans le_sup_left))))
      ((famSigma_le_aeClosure_of_ae_eq (hnI _)).trans (aeClosure_mono le_sup_right)))
  refine condIndepEv_congr_cond (fieldSigma_le hm₁ V) (fieldSigma_le hh.1.measurable V) ?_ ?_
    (sup_le (hver V V.isOpen) (hver V V.isOpen))
    (sup_le (sup_le ((fieldSigmaClosed_le hh.1.measurable _).trans (le_aeClosure _))
      (hver _ hOV)) (hver _ hOV)) H'
  · exact L219.comap_le_aeClosure_of_ae_eq (comap_measurable _)
      (hn.mono fun ω hω => by simp only [hω])
  · exact L219.comap_le_aeClosure_of_ae_eq (comap_measurable _)
      (hn.mono fun ω hω => by simp only [hω])

end LQGMetric.DFGPS
