/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_4N4 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4N3
import Mathlib.Probability.ConditionalExpectation

/-!
# LM Lemma 3.4, increment input: uniqueness of the harmonic part, and the canonical nesting

The harmonic part of the Markov decomposition of LM Lemma 2.1 is a.s. unique: for two
decompositions `IsLMRep P h r hh0 hz G`, `IsLMRep P h r hh0' hz' G'` of `lmScaled h r` on `B_1(0)`,
`⟨G, ψ⟩ = E[⟨lmScaled h r, ψ⟩ | σ(h|_{ℂ∖B_1})] = ⟨G', ψ⟩` a.s. for `ψ ∈ 𝓓(B_1)` (`G` is
measurable for the outside σ-algebra and `⟨hz, ψ⟩` is centred and independent of it), hence the
harmonic representatives agree on `B_1(0)` (a countable dense family of radial bumps,
`GM.pair_radBump_of_harmonic`, and continuity). This is the standard fact that the harmonic part
is the conditional expectation given the outside (LM arXiv:1905.00379 Lemma 2.1, l. 395–410;
Miller–Sheffield IG4 arXiv:1302.4738 Prop. 2.8); the Lean write-up is our own.

* `lmRep_pair_ae_eq` — `⟨G, ψ⟩ = ⟨G', ψ⟩` a.s. for each `ψ ∈ 𝓓(B_1)`.
* `lmRep_harm_eq` — a.s. all harmonic representatives of `G` and `G'` agree on `B_1(0)`.
* `LMNestCanonLeaf` — `LMNestCoreLeaf` for one chosen family of decompositions (exact open node).
* `lmNestCoreLeaf_of_canon` — `LMNestCoreLeaf` from it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Finset Metric InnerProductSpace Topology
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM

/-- a test function on `ℂ` supported in `B_1(0)`, as a test function on `B_1(0)` -/
def testOn1 (φ : TestC) (hφ : tsupport (φ : ℂ → ℝ) ⊆ ball (0 : ℂ) 1) : TestOn (ballO 0 1) :=
  ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩

lemma restrictTo_testOn1 (T : DistC) (φ : TestC) (hφ : tsupport (φ : ℂ → ℝ) ⊆ ball (0 : ℂ) 1) :
    restrictTo (ballO 0 1) T (testOn1 φ hφ) = T φ := by
  show T (TestFunction.monoCLM ℝ (testOn1 φ hφ)) = T φ
  congr 1
  ext y
  simp [TestFunction.monoCLM_apply, testOn1]
  rfl

/-- the outside σ-algebra `σ(lmScaled h r|_{ℂ∖B_1})` -/
abbrev lmOut {Ω : Type} (h : Ω → DistC) (r : ℝ) : MeasurableSpace Ω :=
  fieldSigmaClosed (lmScaled h r) (ball (0 : ℂ) 1)ᶜ

/-- **`⟨G, ψ⟩ = ⟨G', ψ⟩` a.s.** for two decompositions and `ψ ∈ 𝓓(B_1)`. -/
theorem lmRep_pair_ae_eq {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r)
    {hh0 hz G hh0' hz' G' : Ω → DistC} (H : IsLMRep P h r hh0 hz G)
    (H' : IsLMRep P h r hh0' hz' G') (ψ : TestOn (ballO 0 1)) :
    (fun ω => restrictTo (ballO 0 1) (G ω) ψ) =ᵐ[P]
      fun ω => restrictTo (ballO 0 1) (G' ω) ψ := by
  obtain ⟨hdec, hhG, hGm, -, hzb, hind⟩ := H
  obtain ⟨hdec', hhG', hGm', -, hzb', hind'⟩ := H'
  have hm : lmOut h r ≤ mΩ :=
    MarkovZBIndep.fieldSigmaClosed_le (isWholePlaneGFF_lmScaled hh hr) _
  set e : DistC → ℝ := fun T => restrictTo (ballO 0 1) T ψ with hedef
  have he : Measurable e := (measurable_distOn_apply ψ).comp (measurable_restrictTo _)
  have hadd : ∀ a b : DistC, e (a + b) = e a + e b := fun a b => by
    rfl
  set X : Ω → ℝ := fun ω => e (hz ω)
  set X' : Ω → ℝ := fun ω => e (hz' ω)
  set Z : Ω → ℝ := fun ω => e (G ω) - e (G' ω)
  have hXm : Measurable X := hzb.process.measurable ψ
  have hX'm : Measurable X' := hzb'.process.measurable ψ
  have hXi : Integrable X P := (hzb.process.gaussian.hasGaussianLaw_eval ψ).integrable
  have hX'i : Integrable X' P := (hzb'.process.gaussian.hasGaussianLaw_eval ψ).integrable
  have hX0 : ∫ ω, X ω ∂P = 0 := hzb.process.centered ψ
  have hX'0 : ∫ ω, X' ω ∂P = 0 := hzb'.process.centered ψ
  have hZae : Z =ᵐ[P] fun ω => X' ω - X ω := by
    filter_upwards [hhG, hhG'] with ω h1 h2
    have k1 := hadd (hh0 ω) (hz ω)
    have k2 := hadd (hh0' ω) (hz' ω)
    rw [← hdec ω] at k1
    rw [← hdec' ω] at k2
    show e (G ω) - e (G' ω) = e (hz' ω) - e (hz ω)
    rw [← h1, ← h2]
    linarith
  have hZm : StronglyMeasurable[lmOut h r] Z := ((he.comp hGm).sub (he.comp hGm')).stronglyMeasurable
  have hZi : Integrable Z P := (hX'i.sub hXi).congr hZae.symm
  have h1 : P[Z|lmOut h r] = Z := condExp_of_stronglyMeasurable hm hZm hZi
  have h2 : P[Z|lmOut h r] =ᵐ[P] P[fun ω => X' ω - X ω|lmOut h r] := condExp_congr_ae hZae
  have h3 : P[fun ω => X' ω - X ω|lmOut h r] =ᵐ[P] P[X'|lmOut h r] - P[X|lmOut h r] := condExp_sub hX'i hXi (lmOut h r)
  have hcomap : ∀ Y : Ω → DistC, MeasurableSpace.comap (fun ω => e (Y ω)) inferInstance ≤
      MeasurableSpace.comap Y inferInstance := fun Y =>
    (MeasurableSpace.comap_comp (f := e) (g := Y)).symm.le.trans
      (MeasurableSpace.comap_mono he.comap_le)
  have h4 : P[X|lmOut h r] =ᵐ[P] fun _ => ∫ ω, X ω ∂P :=
    condExp_indep_eq hXm.comap_le hm (comap_measurable X).stronglyMeasurable
      (indep_of_indep_of_le_left hind (hcomap hz))
  have h4' : P[X'|lmOut h r] =ᵐ[P] fun _ => ∫ ω, X' ω ∂P :=
    condExp_indep_eq hX'm.comap_le hm (comap_measurable X').stronglyMeasurable
      (indep_of_indep_of_le_left hind' (hcomap hz'))
  filter_upwards [h2, h3, h4, h4'] with ω a b c d
  have hz0 : Z ω = 0 := by
    rw [← congrFun h1 ω, a, b, Pi.sub_apply, c, d, hX0, hX'0, sub_zero]
  exact sub_eq_zero.1 hz0

/-- **Uniqueness of the harmonic part**: a.s. all harmonic representatives on `B_1(0)` of `G`
and of `G'` agree there. -/
theorem lmRep_harm_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r)
    {hh0 hz G hh0' hz' G' : Ω → DistC} (H : IsLMRep P h r hh0 hz G)
    (H' : IsLMRep P h r hh0' hz' G') :
    ∀ᵐ ω ∂P, ∀ g g' : ℂ → ℝ, HarmonicOnNhd g (ball (0 : ℂ) 1) →
      (∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) (G ω) φ = ∫ x, g x * φ x) →
      HarmonicOnNhd g' (ball (0 : ℂ) 1) →
      (∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) (G' ω) φ = ∫ x, g' x * φ x) →
      ∀ u ∈ ball (0 : ℂ) 1, g u = g' u := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℂ
  set S' := ball (0 : ℂ) 1 ∩ S
  have hS'c : S'.Countable := hSc.mono inter_subset_right
  have hδ : ∀ v ∈ S', 0 < (1 - ‖v‖) / 2 := fun v hv => by
    have : ‖v‖ < 1 := by simpa using hv.1
    linarith
  have hB : ∀ v (hv : v ∈ S'), closedBall v ((1 - ‖v‖) / 2) ⊆ ball (0 : ℂ) 1 :=
    fun v hv w hw => by
      have : ‖v‖ < 1 := by simpa using hv.1
      rw [mem_closedBall] at hw
      rw [mem_ball, dist_zero_right]
      have := dist_triangle w v 0
      rw [dist_zero_right, dist_zero_right] at this
      linarith
  have hts : ∀ v (hv : v ∈ S'),
      tsupport (radBump ((1 - ‖v‖) / 2) (hδ v hv).le v : ℂ → ℝ) ⊆ ball (0 : ℂ) 1 :=
    fun v hv => by
      refine (closure_minimal (fun y hy => ?_) isClosed_closedBall).trans (hB v hv)
      by_contra hy'
      rw [mem_closedBall, dist_eq_norm, not_le] at hy'
      exact hy (radProf_eq_zero (hδ v hv).le hy'.le)
  filter_upwards [(ae_ball_iff hS'c).2 fun v hv => lmRep_pair_ae_eq hh hr H H'
    (testOn1 _ (hts v hv))] with ω hω g g' hg hgrep hg' hg'rep u hu
  have hval : ∀ v ∈ S', g v - g' v = 0 := fun v hv => by
    have k := hω v hv
    simp only [restrictTo_testOn1] at k
    have e1 := pair_radBump_of_harmonic (V := ballO 0 1) hg hgrep (hδ v hv) (hB v hv)
    have e2 := pair_radBump_of_harmonic (V := ballO 0 1) hg' hg'rep (hδ v hv) (hB v hv)
    rw [e1, e2] at k
    have hI := integral_radProf_pos (hδ v hv)
    rw [sub_eq_zero]
    exact mul_right_cancel₀ hI.ne' k
  have hcont : ContinuousAt (fun x => g x - g' x) u :=
    (hg u hu).1.continuousAt.sub (hg' u hu).1.continuousAt
  have hcl : u ∈ closure S' := hSd.open_subset_closure_inter isOpen_ball hu
  have hmem := mem_closure_image hcont hcl
  have himg : (fun x => g x - g' x) '' S' ⊆ {0} := by
    rintro _ ⟨v, hv, rfl⟩; exact hval v hv
  have := closure_mono himg hmem
  rw [closure_singleton, mem_singleton_iff, sub_eq_zero] at this
  exact this

/-- **The nesting of the Markov decompositions across scales, canonical form** (MQ
arXiv:1812.03913 l. 693–700), exact open statement: `LMNestCoreLeaf` for one chosen family of
decompositions (by `lmRep_harm_eq` it then holds for all). -/
def LMNestCanonLeaf (s₁ : ℝ) : Prop :=
  ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ r : ℕ → ℝ, (∀ k, 0 < r k) → Antitone r →
    (∀ k, r (k + 1) / r k ≤ s₁) →
    ∃ (F : ℕ → MeasurableSpace Ω) (D : ℕ → Ω → DistC), Monotone F ∧ (∀ j, F j ≤ mΩ) ∧
      (∀ j, Measurable[F j] (D j)) ∧
      (∀ j, Indep (MeasurableSpace.comap (D (j + 1)) inferInstance) (F j) P) ∧
      (∀ j, IndepFun (D j) (fun ω => lmScaled h (r j) ω - D j ω) P) ∧
      (∀ j (φ : TestC0), Integrable (fun ω => (lmScaled h (r j) ω - D j ω) φ.1) P ∧
        ∫ ω, (lmScaled h (r j) ω - D j ω) φ.1 ∂P = 0) ∧
      ∃ hh0 hz G : ℕ → Ω → DistC, (∀ k, IsLMRep P h (r k) (hh0 k) (hz k) (G k)) ∧
        ∀ k, ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, HarmonicOnNhd g (ball (0 : ℂ) 1) ∧
          (∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) (G k ω) φ = ∫ x, g x * φ x) ∧
          ∃ d : ℕ → ℂ → ℝ, (∀ j ≤ k, HarmonicOnNhd (d j) (ball (0 : ℂ) 1) ∧
            ∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) (D j ω) φ = ∫ x, d j x * φ x) ∧
          ∀ u ∈ ball (0 : ℂ) 1, g u - g 0 =
            ∑ j ∈ range (k + 1), (d j ((r k / r j : ℝ) • u) - d j 0)

theorem lmNestCoreLeaf_of_canon {s₁ : ℝ} (hC : LMNestCanonLeaf s₁) : LMNestCoreLeaf s₁ := by
  intro Ω mΩ P _ h hh r hr0 hrA hrs
  obtain ⟨F, D, hF, hFle, hDm, hDi, hDR, hR, hh0c, hzc, Gc, hrepc, hdec⟩ :=
    hC P h hh r hr0 hrA hrs
  refine ⟨F, D, hF, hFle, hDm, hDi, hDR, hR, fun hh0 hz G hrep k => ?_⟩
  filter_upwards [hdec k, lmRep_harm_eq hh.1 (hr0 k) (hrep k) (hrepc k), (hrep k).2.1,
    (hrep k).2.2.2.1] with ω ⟨g, hg, hgrep, d, hd, hsum⟩ huniq hGeq ⟨g', hg', hg'rep⟩
  have hg'rep' : ∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) (G k ω) φ = ∫ x, g' x * φ x :=
    fun φ => by rw [← hGeq]; exact hg'rep φ
  have he := huniq g' g hg' hg'rep' hg hgrep
  refine ⟨g', hg', hg'rep', d, hd, fun u hu => ?_⟩
  rw [he u hu, he 0 (mem_ball_self one_pos)]
  exact hsum u hu

/-- **LM Lemma 3.1 (1)** (`N = 0`) from the canonical nesting and `𝔥^r(0) = h_r(0)`. -/
theorem lmLem3_1a_of_canon (hC : ∀ s₁ : ℝ, 0 < s₁ → s₁ < 1 → LMNestCanonLeaf s₁)
    (hH : LMHarmCenterLeaf) : LMLem3_1a :=
  lmLem3_1a_of_core (fun s₁ h1 h2 => lmNestCoreLeaf_of_canon (hC s₁ h1 h2)) hH

end LQGMetric.LM
