/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_1N2P2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1N2P1
import LatticeProb.Bonanno.LQGMetric.Papers.LM.LocNest
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1InScale

/-!
# LM Lemma 3.1 with `N = 2`: Borel versions of the metric σ-algebras and locality at one scale

Source: Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`): Definition 1.3/1.5 (l. 245–248, 284–287), proof of Lemma 3.3
(l. 631–637: "By `ξ`-additivity, the metrics `e^{−ξh_r(0)} D_n` are jointly local for
`h − h_r(0)`. Therefore, the metrics … are conditionally independent from `𝓕_r` given
`(h − h_r(0))|_{B_{sr}(0)}`"), Lemma 2.3 (l. 523–549; l. 534 "`h` is determined by `h|_V` and
`h|_{U∖V}`" = `LocGermSplit`; l. 545 = `locInternalNest`).

* `n2Chain ξ h D r W`: the Borel version `e^{−ξh_r(0)} · chainInf D W` of the scaled internal
  metric `e^{−ξh_r(0)} D(·,·;W)` (a.s. equal for a length metric, `ContMetric.internal_eq_chainInf`);
  `n2Sig` the σ-algebra of the pair `(n2Chain D₁, n2Chain D₂)`.
* `n2Sig_le_nest`: for `W₁ ⊆ W₂` open, `n2Sig r W₁ ≤ σ(h) ∨ n2Sig r' W₂` up to null events
  (LM l. 609–611 and l. 545).
* `n2_condIndep_scale`: for every open `V`,
  `n2Sig r V ⟂ (σ(h), n2Sig r (ℂ∖V̄)) | (h − h_r(0))|_V`: LM Def 1.5 (joint locality of the
  scaled metrics) and weak union, with `σ(h) ⊆ σ((h − h_r(0))|_V) ∨ σ((h − h_r(0))|_{ℂ∖V})`
  up to null events (`LocGermSplit`, LM l. 534; LM uses it through form (2) of LM Lemma 2.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM.Bilip

variable {Ω : Type}

/-- the scale factor `e^{−ξ h_r(0)}` -/
def n2Fac (ξ : ℝ) (h : Ω → DistC) (r : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-ξ * circleAvg (h ω) r 0))

/-- Borel version of `e^{−ξh_r(0)} D(·,·;W)` -/
def n2Chain (ξ : ℝ) (h : Ω → DistC) (D : Ω → ContMetric) (r : ℝ) (W : Set ℂ) :
    Ω → ℂ → ℂ → ℝ≥0∞ :=
  fun ω u v => n2Fac ξ h r ω * (D ω).chainInf W u v

/-- `σ(e^{−ξh_r(0)} D₁(·,·;W), e^{−ξh_r(0)} D₂(·,·;W))`, Borel version -/
def n2Sig (ξ : ℝ) (h : Ω → DistC) (D₁ D₂ : Ω → ContMetric) (r : ℝ) (W : Set ℂ) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap (n2Chain ξ h D₁ r W) inferInstance ⊔
    MeasurableSpace.comap (n2Chain ξ h D₂ r W) inferInstance

lemma measurable_n2Fac (ξ : ℝ) (h : Ω → DistC) (r : ℝ) :
    Measurable[MeasurableSpace.comap h inferInstance] (n2Fac ξ h r) := by
  have : Measurable fun T : DistC => ENNReal.ofReal (Real.exp (-ξ * circleAvg T r 0)) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_circleAvg_left r 0).const_mul (-ξ)))
  exact this.comp (comap_measurable h)

lemma measurable_mulFn :
    Measurable fun p : ℝ≥0∞ × (ℂ → ℂ → ℝ≥0∞) => fun u v => p.1 * p.2 u v :=
  measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v =>
    measurable_fst.mul ((measurable_pi_apply v).comp ((measurable_pi_apply u).comp measurable_snd))

variable [mΩ : MeasurableSpace Ω]

lemma measurable_n2Chain_sup (ξ : ℝ) (h : Ω → DistC) (D : Ω → ContMetric) (r : ℝ) (W : Set ℂ) :
    Measurable[MeasurableSpace.comap h inferInstance ⊔ chainSigma D W] (n2Chain ξ h D r W) := by
  have h1 : Measurable[MeasurableSpace.comap h inferInstance ⊔ chainSigma D W] (n2Fac ξ h r) :=
    (measurable_n2Fac ξ h r).mono le_sup_left le_rfl
  have h2 : Measurable[MeasurableSpace.comap h inferInstance ⊔ chainSigma D W]
      fun ω (u v : ℂ) => (D ω).chainInf W u v :=
    (comap_measurable (fun ω (u v : ℂ) => (D ω).chainInf W u v)).mono le_sup_right le_rfl
  exact measurable_mulFn.comp (h1.prodMk h2)

lemma n2Chain_le_sup (ξ : ℝ) (h : Ω → DistC) (D : Ω → ContMetric) (r : ℝ) (W : Set ℂ) :
    MeasurableSpace.comap (n2Chain ξ h D r W) inferInstance ≤
      MeasurableSpace.comap h inferInstance ⊔ chainSigma D W :=
  (measurable_n2Chain_sup ξ h D r W).comap_le

lemma n2Sig_le {ξ : ℝ} {h : Ω → DistC} {D₁ D₂ : Ω → ContMetric} (hh : Measurable h)
    (hD₁ : Measurable D₁) (hD₂ : Measurable D₂) (r : ℝ) (W : Set ℂ) :
    n2Sig ξ h D₁ D₂ r W ≤ mΩ := by
  have hc : MeasurableSpace.comap h inferInstance ≤ mΩ := hh.comap_le
  refine sup_le ((n2Chain_le_sup ξ h D₁ r W).trans (sup_le hc (chainSigma_le hD₁ W)))
    ((n2Chain_le_sup ξ h D₂ r W).trans (sup_le hc (chainSigma_le hD₂ W)))

/-- `D(·,·;W) = e^{ξh_r(0)} · (e^{−ξh_r(0)} D(·,·;W))` -/
lemma chainSigma_le_n2 (ξ : ℝ) (h : Ω → DistC) (D : Ω → ContMetric) (r : ℝ) (W : Set ℂ) :
    chainSigma D W ≤
      MeasurableSpace.comap h inferInstance ⊔ MeasurableSpace.comap (n2Chain ξ h D r W)
        inferInstance := by
  set m := MeasurableSpace.comap h inferInstance ⊔
    MeasurableSpace.comap (n2Chain ξ h D r W) inferInstance
  have hf : Measurable[m] fun ω => ENNReal.ofReal (Real.exp (ξ * circleAvg (h ω) r 0)) := by
    have : Measurable fun T : DistC => ENNReal.ofReal (Real.exp (ξ * circleAvg T r 0)) :=
      ENNReal.measurable_ofReal.comp
        (Real.measurable_exp.comp ((measurable_circleAvg_left r 0).const_mul ξ))
    exact (this.comp (comap_measurable h)).mono le_sup_left le_rfl
  have hn : Measurable[m] (n2Chain ξ h D r W) := (comap_measurable _).mono le_sup_right le_rfl
  have e : (fun ω (u v : ℂ) => (D ω).chainInf W u v) =
      fun ω u v => ENNReal.ofReal (Real.exp (ξ * circleAvg (h ω) r 0)) * n2Chain ξ h D r W ω u v := by
    funext ω u v
    simp only [n2Chain, n2Fac]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  have : Measurable[m] fun ω (u v : ℂ) => (D ω).chainInf W u v := by
    rw [e]
    exact measurable_mulFn.comp (hf.prodMk hn)
  exact this.comap_le

variable {P : Measure Ω}

lemma comap_le_aeClosure_of_ae_eq {α : Type*} [MeasurableSpace α] {f g : Ω → α}
    (hfg : f =ᵐ[P] g) :
    MeasurableSpace.comap f inferInstance ≤ aeClosure P (MeasurableSpace.comap g inferInstance) := by
  rintro s ⟨S, hS, rfl⟩
  refine ⟨g ⁻¹' S, ⟨S, hS, rfl⟩, ?_⟩
  filter_upwards [hfg] with ω hω
  change (f ω ∈ S) = (g ω ∈ S)
  rw [hω]

lemma sup_le_aeClosure {X Y A B : MeasurableSpace Ω} (hX : X ≤ aeClosure P A)
    (hY : Y ≤ aeClosure P B) : X ⊔ Y ≤ aeClosure P (A ⊔ B) :=
  sup_le (hX.trans (aeClosure_mono le_sup_left)) (hY.trans (aeClosure_mono le_sup_right))

/-- `n2Chain` versus the scaled internal metric (`normIntFam`) -/
lemma normIntFam_ae_eq {ξ : ℝ} {h : Ω → DistC} {D : Ω → ContMetric}
    (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) {r : ℝ} {W : Set ℂ} (hW : IsOpen W) :
    ∀ᵐ ω ∂P, normIntFam ξ h D r ω W = n2Chain ξ h D r W ω := by
  filter_upwards [hlen] with ω hω
  funext u v
  simp only [normIntFam, n2Chain, n2Fac]
  rw [(D ω).internal_eq_chainInf hω hW u v]

lemma famSigma_normInt_le {ξ : ℝ} {h : Ω → DistC} {D : Ω → ContMetric}
    (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) {r : ℝ} {W : Set ℂ} (hW : IsOpen W) :
    famSigma (normIntFam ξ h D r) W ≤
      aeClosure P (MeasurableSpace.comap (n2Chain ξ h D r W) inferInstance) :=
  famSigma_le_aeClosure_of_measurable (comap_measurable _) (normIntFam_ae_eq hlen hW)

lemma n2Chain_le_famSigma {ξ : ℝ} {h : Ω → DistC} {D : Ω → ContMetric}
    (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) {r : ℝ} {W : Set ℂ} (hW : IsOpen W) :
    MeasurableSpace.comap (n2Chain ξ h D r W) inferInstance ≤
      aeClosure P (famSigma (normIntFam ξ h D r) W) := by
  rintro s ⟨S, hS, rfl⟩
  refine ⟨(fun ω => normIntFam ξ h D r ω W) ⁻¹' S, ⟨S, hS, rfl⟩, ?_⟩
  filter_upwards [normIntFam_ae_eq (ξ := ξ) (h := h) hlen (r := r) hW] with ω hω
  change (n2Chain ξ h D r W ω ∈ S) = (normIntFam ξ h D r ω W ∈ S)
  rw [hω]

/-- LM l. 545 and l. 609–611: `e^{−ξh_r(0)} D(·,·;W₁)` is determined, up to null events, by `h`
and `e^{−ξh_{r'}(0)} D(·,·;W₂)` when `W₁ ⊆ W₂` are open. -/
lemma n2Chain_le_nest {ξ : ℝ} {h : Ω → DistC} {D : Ω → ContMetric} (hD : Measurable D)
    (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) (r r' : ℝ) {W₁ W₂ : Set ℂ} (hW₁ : IsOpen W₁)
    (hW₂ : IsOpen W₂) (hW : W₁ ⊆ W₂) :
    MeasurableSpace.comap (n2Chain ξ h D r W₁) inferInstance ≤
      aeClosure P (MeasurableSpace.comap h inferInstance ⊔
        MeasurableSpace.comap (n2Chain ξ h D r' W₂) inferInstance) := by
  refine (n2Chain_le_sup ξ h D r W₁).trans (sup_le ((le_aeClosure _).trans
    (aeClosure_mono le_sup_left)) ?_)
  have h1 : chainSigma D W₁ ≤ aeClosure P (chainSigma D W₂) :=
    le_aeClosure_trans (le_aeClosure_trans (chainSigma_le_famSigma hlen hW₁)
      (locInternalNest P D hD hlen W₁ W₂ hW₁ hW₂ hW)) (famSigma_le_chainSigma hlen hW₂)
  exact le_aeClosure_trans h1 ((chainSigma_le_n2 ξ h D r' W₂).trans (le_aeClosure _))

lemma n2Sig_le_nest {ξ : ℝ} {h : Ω → DistC} {D₁ D₂ : Ω → ContMetric} (hD₁ : Measurable D₁)
    (hD₂ : Measurable D₂) (hlen : ∀ᵐ ω ∂P, (D₁ ω).IsLength ∧ (D₂ ω).IsLength) (r r' : ℝ)
    {W₁ W₂ : Set ℂ} (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂) (hW : W₁ ⊆ W₂) :
    n2Sig ξ h D₁ D₂ r W₁ ≤
      aeClosure P (MeasurableSpace.comap h inferInstance ⊔ n2Sig ξ h D₁ D₂ r' W₂) := by
  have e : MeasurableSpace.comap h inferInstance ⊔ n2Sig ξ h D₁ D₂ r' W₂ =
      (MeasurableSpace.comap h inferInstance ⊔
        MeasurableSpace.comap (n2Chain ξ h D₁ r' W₂) inferInstance) ⊔
      (MeasurableSpace.comap h inferInstance ⊔
        MeasurableSpace.comap (n2Chain ξ h D₂ r' W₂) inferInstance) := by
    simp only [n2Sig]
    rw [sup_sup_distrib_left]
  rw [e]
  exact sup_le_aeClosure
    (n2Chain_le_nest hD₁ (hlen.mono fun _ h => h.1) r r' hW₁ hW₂ hW)
    (n2Chain_le_nest hD₂ (hlen.mono fun _ h => h.2) r r' hW₁ hW₂ hW)

/-- `h = (h − h_r(0)) − (h − h_r(0))_1(0)` a.s. for `h_1(0) = 0`, so
`σ(h) ⊆ σ(h − h_r(0))` up to null events. -/
lemma comap_h_le_recentre {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) (r : ℝ) :
    MeasurableSpace.comap h inferInstance ≤
      aeClosure P (MeasurableSpace.comap (recentre h r) inferInstance) := by
  have hae : h =ᵐ[P] recentre (recentre h r) 1 := by
    filter_upwards [recentre_ae_eq hh.1 one_pos r, hh.2] with ω hω h0
    rw [← hω]
    show h ω = addConst (h ω) (-circleAvg (h ω) 1 0)
    rw [h0, neg_zero, addConst_zero']
  have hm : Measurable[MeasurableSpace.comap (recentre h r) inferInstance]
      (recentre (recentre h r) 1) :=
    @measurable_recentre Ω (MeasurableSpace.comap (recentre h r) inferInstance) _
      (comap_measurable _) 1
  exact (comap_le_aeClosure_of_ae_eq hae).trans (aeClosure_mono hm.comap_le)

end LQGMetric.LM
