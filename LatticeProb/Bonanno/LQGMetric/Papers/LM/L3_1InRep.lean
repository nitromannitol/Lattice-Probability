/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_1InRep at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1InFrz
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.MarkovNorm
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndep
import LatticeProb.Bonanno.LQGMetric.Field.MarkovFinal

/-!
# LM (3.8): the Markov decomposition at scale `r` and the good event

Source: LM = Gwynne–Miller, arXiv:1905.00379, `literature/src/1905.00379/local-metrics-final.tex`,
l. 615–621 (`(h − h_r(0))|_{B_r(0)} = 𝔥^r + h̊^r` by LM Lemma 2.1), l. 619 (`𝔐^R_r`), and the
proof of Lemma 3.3 (l. 632–643: "by the scale invariance of the law of the GFF, modulo additive
constant, it suffices to estimate this law in the case when `r = 1`").

We scale: `lmScaled h r = (h − h_r(0))(r ·)` is a whole-plane GFF with `h_1(0) = 0` a.s., and
`DFGPS.markov_normAt` (LM Lemma 2.1 at this normalization) gives its decomposition on `B_1(0)`
(`IsLMRep`). The σ-algebra of `lmScaled h r` outside `B_1(0)` is LM's `𝓕_r`
(`fieldSigmaClosed_lmScaled_le`, `lmF_le_fieldSigmaClosed_lmScaled`). The good event
`{𝔐 ≤ M}` is read off the frozen harmonic part through countably many radial pairings
(`lmGood`, GM's `goodD`); its probability is bounded uniformly in `r` and the field by GM's
L2.7 machinery at the fixed scale `1` (`prob_lmGood_compl_le`). Centring: GM's `goodD` centres
`𝔥` by the circle average `h_1(0)` of the scaled field (which is `0` a.s.), LM centre by `𝔥(0)`;
the bound `|𝔥 − c| ≤ M` with any constant `c` is what MQ Lemma 4.1 (`MQLem4_1Gen`) uses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric TopologicalSpace InnerProductSpace

namespace LQGMetric.LM

open Blueprint

variable {Ω : Type} [MeasurableSpace Ω]

/-- `(h − h_r(0))(r ·)` -/
def lmScaled (h : Ω → DistC) (r : ℝ) : Ω → DistC := fun ω => affineComp r 0 (recentre h r ω)

/-- the outputs of LM Lemma 2.1 for `lmScaled h r` on `B_1(0)` -/
def IsLMRep (P : Measure Ω) (h : Ω → DistC) (r : ℝ) (hh hz G : Ω → DistC) : Prop :=
  (∀ ω, lmScaled h r ω = hh ω + hz ω) ∧ hh =ᵐ[P] G ∧
  Measurable[fieldSigmaClosed (lmScaled h r) (ball (0 : ℂ) 1)ᶜ] G ∧
  (∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, HarmonicOnNhd g (ball (0 : ℂ) 1) ∧
    ∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) (hh ω) φ = ∫ x, g x * φ x) ∧
  IsZeroBoundaryGFF (ballO 0 1) (fun ω => restrictTo (ballO 0 1) (hz ω)) P ∧
  Indep (MeasurableSpace.comap hz inferInstance)
    (fieldSigmaClosed (lmScaled h r) (ball (0 : ℂ) 1)ᶜ) P

lemma isWholePlaneGFF_lmScaled {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {r : ℝ} (hr : 0 < r) : IsWholePlaneGFF (lmScaled h r) P :=
  (DFGPS.isNormalizedAt_recenter hh hr 0).1.affineComp hr 0

lemma ae_circleAvg_lmScaled {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {r : ℝ} (hr : 0 < r) : ∀ᵐ ω ∂P, circleAvg (lmScaled h r ω) 1 0 = 0 := by
  filter_upwards [CircleAvg.ae_circleAvg_affineComp (DFGPS.isNormalizedAt_recenter hh hr 0).1 hr 0,
    (DFGPS.isNormalizedAt_recenter hh hr 0).2] with ω h1 h2
  exact h1.trans h2

lemma preOpens_ball {r : ℝ} (hr : 0 < r) :
    ((DFGPS.preOpens r 0 (ballO 0 r) : Opens ℂ) : Set ℂ) = ball (0 : ℂ) 1 := by
  ext y
  rw [SetLike.mem_coe, DFGPS.mem_preOpens hr.ne', add_zero]
  show r • y ∈ ball (0 : ℂ) r ↔ y ∈ ball 0 1
  simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

lemma fieldSigmaClosed_lmScaled_le (h : Ω → DistC) {r : ℝ} (hr : 0 < r) :
    fieldSigmaClosed (lmScaled h r) (ball (0 : ℂ) 1)ᶜ ≤ lmF h r := by
  have := DFGPS.fieldSigmaClosed_affineComp_le (z := 0) hr (ballO 0 r) (recentre h r)
  rw [preOpens_ball hr] at this
  exact this

lemma lmF_le_fieldSigmaClosed_lmScaled (h : Ω → DistC) {r : ℝ} (hr : 0 < r) :
    lmF h r ≤ fieldSigmaClosed (lmScaled h r) (ball (0 : ℂ) 1)ᶜ := by
  have := DFGPS.fieldSigmaClosed_le_affineComp (z := 0) hr (ballO 0 r) (recentre h r)
  rw [preOpens_ball hr] at this
  exact this

/-- LM Lemma 2.1 at scale `r` (via `DFGPS.markov_normAt`) -/
theorem exists_lmRep {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) :
    ∃ hh0 hz G : Ω → DistC, IsLMRep P h r hh0 hz G := by
  have hdisj : Disjoint ((ballO (0 : ℂ) 1 : Opens ℂ) : Set ℂ) (sphere (0 : ℂ) 1) :=
    Set.disjoint_left.2 fun y hy hs => by
      have h1 : ‖y‖ < 1 := by simpa [ballO] using hy
      have h2 : ‖y‖ = 1 := by simpa using hs
      linarith
  obtain ⟨hh0, hz, hdec, hharm, ⟨G, hGF, hhG⟩, -, hzb, -, hind⟩ :=
    DFGPS.markov_normAt MarkovFinal.lmLem2_1 P (lmScaled h r) (isWholePlaneGFF_lmScaled hh hr)
      one_pos 0 (ae_circleAvg_lmScaled hh hr) (ballO 0 1) hdisj
  exact ⟨hh0, hz, G, hdec, hhG, hGF, hharm, hzb, hind⟩

/-- `σ((h − h_r(0))|_{A_{s₁r,s₂r}}) ≤ σ(lmScaled h r|_{B_{s₂}})` -/
lemma annSigma_le_lmScaled (h : Ω → DistC) {r s₁ s₂ : ℝ} (hr : 0 < r) :
    annSigma h s₁ s₂ r ≤ fieldSigma (lmScaled h r) (ballO 0 s₂) := by
  refine (GM.fieldSigma_mono (recentre h r) (W := ballO 0 (s₂ * r)) ?_).trans ?_
  · intro y hy
    have := hy.2
    show y ∈ ball (0 : ℂ) (s₂ * r)
    simpa [mem_ball, dist_zero_right] using this
  · refine GM.fieldSigma_le_affineComp hr (fun y => ?_) (recentre h r)
    show y ∈ ball (0 : ℂ) s₂ ↔ r • y + 0 ∈ ball (0 : ℂ) (s₂ * r)
    simp only [add_zero, mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith

/-- the good event `{𝔐 ≤ M}` at scale `r` (GM's `goodD` for the frozen harmonic part) -/
def lmGood (δ : ℝ) (hδ : 0 ≤ δ) (Sd : Set ℂ) (ρ₂ M : ℝ) (h G : Ω → DistC) (r : ℝ) : Set Ω :=
  {ω | GM.goodD δ hδ Sd 0 (ρ₂ * 1) M (addConst (G ω) (-circleAvg (lmScaled h r ω) 1 0))}

lemma lmGood_mono {δ : ℝ} (hδ : 0 < δ) {Sd : Set ℂ} {ρ₂ M M' : ℝ} (hMM : M ≤ M')
    (h G : Ω → DistC) (r : ℝ) : lmGood δ hδ.le Sd ρ₂ M h G r ⊆ lmGood δ hδ.le Sd ρ₂ M' h G r :=
  fun ω hω u hu hub => (hω u hu hub).trans
    (mul_le_mul_of_nonneg_right hMM (GM.integral_radProf_pos hδ).le)

lemma measurableSet_lmGood {δ : ℝ} (hδ : 0 ≤ δ) {Sd : Set ℂ} (hSd : Sd.Countable) (ρ₂ M : ℝ)
    (h G : Ω → DistC) {r : ℝ} (hr : 0 < r)
    (hG : Measurable[fieldSigmaClosed (lmScaled h r) (ball (0 : ℂ) 1)ᶜ] G) :
    MeasurableSet[lmF h r] (lmGood δ hδ Sd ρ₂ M h G r) := by
  have hc : Measurable[fieldSigmaClosed (lmScaled h r) (ball (0 : ℂ) 1)ᶜ]
      fun ω => -circleAvg (lmScaled h r ω) 1 0 :=
    (GM.measurable_circleAvg_fieldSigmaClosed _ 1 0 (fun y hy => by
      simp only [abs_one, mem_sphere_iff_norm, sub_zero] at hy
      simp [mem_ball, hy])).neg
  have hW := @GM.measurable_addConst_pi Ω (fieldSigmaClosed (lmScaled h r) (ball (0 : ℂ) 1)ᶜ)
    Unit G (fun _ ω => -circleAvg (lmScaled h r ω) 1 0) hG (fun _ => hc)
  have hW1 : Measurable[fieldSigmaClosed (lmScaled h r) (ball (0 : ℂ) 1)ᶜ]
      fun ω => addConst (G ω) (-circleAvg (lmScaled h r ω) 1 0) :=
    (measurable_pi_apply ()).comp hW
  exact fieldSigmaClosed_lmScaled_le h hr _
    (hW1 (GM.measurableSet_goodD hδ hSd 0 (ρ₂ * 1) M))

end LQGMetric.LM
