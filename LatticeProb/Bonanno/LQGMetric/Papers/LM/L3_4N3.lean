/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_4N3 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4N2

/-!
# LM Lemma 3.4, increment input: splitting `LMNestLeaf`

`LMNestLeaf` (`L3_4N2.lean`) combines two facts, stated here separately as exact open nodes:

* `LMNestCoreLeaf s₁` — the nesting of the Markov decompositions across scales (MQ
  arXiv:1812.03913, `lqg_geodesics.tex` l. 693–700: `𝔥_{0,r_ℓ} = 𝔥_{0,1} + 𝔥̃_{0,r_ℓ}` with
  `𝔥̃_{0,r_ℓ}` independent of `𝓕_{0,1}`), with the telescoping identity centred at `g(0)`.
* `LMHarmCenterLeaf` — `𝔥^r(0) = h_r(0)`: the harmonic part on `B_r(0)` takes at the centre the
  value of the circle average on `∂B_r(0)` (the Poisson kernel of the disc at the centre is
  uniform; LM arXiv:1905.00379 Lemma 2.1, l. 395–410, and the definition of `𝔐` l. 586–590).

* `lmNestLeaf_of_core` — `LMNestLeaf s₁` from the two.
* `lmLem3_1a_of_core`, `lmLem3_1b_of_core`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Finset Metric InnerProductSpace
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM

/-- **The nesting of the Markov decompositions across scales** (MQ l. 693–700), exact open
statement: `LMNestLeaf` with the telescoping identity centred at `g(0)`. -/
def LMNestCoreLeaf (s₁ : ℝ) : Prop :=
  ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ r : ℕ → ℝ, (∀ k, 0 < r k) → Antitone r →
    (∀ k, r (k + 1) / r k ≤ s₁) →
    ∃ (F : ℕ → MeasurableSpace Ω) (D : ℕ → Ω → DistC), Monotone F ∧ (∀ j, F j ≤ mΩ) ∧
      (∀ j, Measurable[F j] (D j)) ∧
      (∀ j, Indep (MeasurableSpace.comap (D (j + 1)) inferInstance) (F j) P) ∧
      (∀ j, IndepFun (D j) (fun ω => lmScaled h (r j) ω - D j ω) P) ∧
      (∀ j (φ : TestC0), Integrable (fun ω => (lmScaled h (r j) ω - D j ω) φ.1) P ∧
        ∫ ω, (lmScaled h (r j) ω - D j ω) φ.1 ∂P = 0) ∧
      ∀ hh0 hz G : ℕ → Ω → DistC, (∀ k, IsLMRep P h (r k) (hh0 k) (hz k) (G k)) →
        ∀ k, ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, HarmonicOnNhd g (ball (0 : ℂ) 1) ∧
          (∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) (G k ω) φ = ∫ x, g x * φ x) ∧
          ∃ d : ℕ → ℂ → ℝ, (∀ j ≤ k, HarmonicOnNhd (d j) (ball (0 : ℂ) 1) ∧
            ∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) (D j ω) φ = ∫ x, d j x * φ x) ∧
          ∀ u ∈ ball (0 : ℂ) 1, g u - g 0 =
            ∑ j ∈ range (k + 1), (d j ((r k / r j : ℝ) • u) - d j 0)

/-- **`𝔥^r(0) = h_r(0)`**, exact open statement: a.s. every harmonic representative on `B_1(0)` of
the harmonic part of `lmScaled h r` takes the value `circleAvg (lmScaled h r) 1 0` at `0`. -/
def LMHarmCenterLeaf : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWPGFF h P → ∀ r : ℝ, 0 < r → ∀ hh0 hz G : Ω → DistC,
      IsLMRep P h r hh0 hz G → ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, HarmonicOnNhd g (ball (0 : ℂ) 1) →
        (∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) (G ω) φ = ∫ x, g x * φ x) →
        g 0 = circleAvg (lmScaled h r ω) 1 0

theorem lmNestLeaf_of_core {s₁ : ℝ} (hC : LMNestCoreLeaf s₁) (hH : LMHarmCenterLeaf) :
    LMNestLeaf s₁ := by
  intro Ω mΩ P _ h hh r hr0 hrA hrs
  obtain ⟨F, D, hF, hFle, hDm, hDi, hDR, hR, hdec⟩ := hC P h hh r hr0 hrA hrs
  refine ⟨F, D, hF, hFle, hDm, hDi, hDR, hR, fun hh0 hz G hrep k => ?_⟩
  filter_upwards [hdec hh0 hz G hrep k, hH P h hh (r k) (hr0 k) _ _ _ (hrep k)] with ω
    ⟨g, hg, hgrep, d, hd, hsum⟩ hc
  exact ⟨g, hg, hgrep, d, hd, fun u hu => by rw [← hc g hg hgrep]; exact hsum u hu⟩

/-- **LM Lemma 3.1 (1)** (`N = 0`) from the nesting and `𝔥^r(0) = h_r(0)`. -/
theorem lmLem3_1a_of_core (hC : ∀ s₁ : ℝ, 0 < s₁ → s₁ < 1 → LMNestCoreLeaf s₁)
    (hH : LMHarmCenterLeaf) : LMLem3_1a :=
  lmLem3_1a_of_nest fun s₁ h1 h2 => lmNestLeaf_of_core (hC s₁ h1 h2) hH

end LQGMetric.LM
