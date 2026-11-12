/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108L3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L29FKG

/-!
# CONF Lemma 2.9 with a.s. continuity along measurable approximating sequences

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF), Lemma 2.9
(`lem-fkg-cont`, C:676–709), as used in the proof of Lemma 2.10 (C:735–738): there Lemma 2.9 is
applied to the frozen functional `Φ_{h_{0,t}}`, whose continuity is known only along (random)
sequences, a.s. ("for any sequence of (possibly random) functions `fⁿ` … a.s. `Φ(h + fⁿ) → Φ(h)`",
C:717). This file proves Lemma 2.9 with exactly that hypothesis, for sequences given by measurable
maps (`fkg_continuous_gaussian_seq`); CONF's proof (C:685–708) only uses the continuity of `Φ`
along its approximations `fⁿ = Σⱼ f(xⱼⁿ) φⱼⁿ`, which are measurable. The proof is that of
`fkg_continuous_gaussian` (L29FKG) with the last step changed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric.CONF

variable {X : Type*} [MetricSpace X] [MeasurableSpace C(X, ℝ)] [BorelSpace C(X, ℝ)]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [LocallyCompactSpace X] [SigmaCompactSpace X]

/-- `Φ` is a.s. continuous at `f` along measurable random sequences (CONF C:717) -/
def AeSeqContAt (P : Measure Ω) (f : Ω → C(X, ℝ)) (Φ : C(X, ℝ) → ℝ) : Prop :=
  ∀ gn : ℕ → Ω → C(X, ℝ), (∀ n, Measurable (gn n)) →
    (∀ᵐ ω ∂P, Tendsto (fun n => gn n ω) atTop (𝓝 (f ω))) →
      ∀ᵐ ω ∂P, Tendsto (fun n => Φ (gn n ω)) atTop (𝓝 (Φ (f ω)))

/-- **CONF Lemma 2.9**, with a.s. continuity along measurable approximating sequences -/
theorem fkg_continuous_gaussian_seq {f : Ω → C(X, ℝ)} (hfm : Measurable f)
    (hG : IsGaussianProcess (fun x ω => f ω x) P)
    (hcov : ∀ x y, 0 ≤ cov[fun ω => f ω x, fun ω => f ω y; P])
    {Φ Ψ : C(X, ℝ) → ℝ} {CΦ CΨ : ℝ} (hΦmono : Monotone Φ) (hΨmono : Monotone Ψ)
    (hΦmeas : Measurable Φ) (hΨmeas : Measurable Ψ)
    (hΦb : ∀ g, |Φ g| ≤ CΦ) (hΨb : ∀ g, |Ψ g| ≤ CΨ)
    (hΦc : AeSeqContAt P f Φ) (hΨc : AeSeqContAt P f Ψ) :
    0 ≤ cov[fun ω => Φ (f ω), fun ω => Ψ (f ω); P] := by
  classical
  have hP : IsProbabilityMeasure P := (hG.hasGaussianLaw ∅).isProbabilityMeasure
  obtain ⟨t, φ, hφ, hlim⟩ := exists_fin_approx_ae_tendsto (P := P) hfm
  let Y : ∀ n, Ω → (t n → ℝ) := fun n ω j => f ω j
  have hYm : ∀ n, Measurable (Y n) := fun n =>
    measurable_pi_iff.2 fun j => (continuous_eval_const (j : X)).measurable.comp hfm
  have hYG : ∀ n, HasGaussianLaw (Y n) P := fun n => hG.hasGaussianLaw (t n)
  have hfn : ∀ n ω, l29Interp (φ n) (Y n ω) = ∑ j : t n, f ω j • φ n j := fun _ _ => rfl
  have hPitt : ∀ {F : C(X, ℝ) → ℝ} {C : ℝ}, Monotone F → Measurable F → (∀ g, |F g| ≤ C) →
      ∀ n, Monotone (F ∘ l29Interp (φ n)) ∧ Measurable (F ∘ l29Interp (φ n)) ∧
        ∀ y, |(F ∘ l29Interp (φ n)) y| ≤ C := fun hm hme hb n =>
    ⟨hm.comp (monotone_l29Interp (hφ n)), hme.comp (continuous_l29Interp (φ n)).measurable,
      fun y => hb _⟩
  have hn : ∀ n, (∫ ω, Φ (l29Interp (φ n) (Y n ω)) ∂P) * (∫ ω, Ψ (l29Interp (φ n) (Y n ω)) ∂P)
      ≤ ∫ ω, Φ (l29Interp (φ n) (Y n ω)) * Ψ (l29Interp (φ n) (Y n ω)) ∂P := fun n => by
    obtain ⟨h1, h2, h3⟩ := hPitt hΦmono hΦmeas hΦb n
    obtain ⟨h4, h5, h6⟩ := hPitt hΨmono hΨmeas hΨb n
    exact Pitt.integral_mul_le_of_monotone (hYG n) (fun i j => hcov i j) h1 h4 h2 h5 h3 h6
  have hmeasA : ∀ {F : C(X, ℝ) → ℝ}, Measurable F →
      ∀ n, AEStronglyMeasurable (fun ω => F (l29Interp (φ n) (Y n ω))) P := fun hme n =>
    (hme.comp ((continuous_l29Interp (φ n)).measurable.comp (hYm n))).aestronglyMeasurable
  have hgn : ∀ n, Measurable fun ω => l29Interp (φ n) (Y n ω) := fun n =>
    (continuous_l29Interp (φ n)).measurable.comp (hYm n)
  have hlim' : ∀ᵐ ω ∂P, Tendsto (fun n => l29Interp (φ n) (Y n ω)) atTop (𝓝 (f ω)) := by
    filter_upwards [hlim] with ω hω
    simpa only [hfn] using hω
  have hint := integral_mul_le_of_tendsto (hmeasA hΦmeas) (hmeasA hΨmeas)
    (fun n ω => hΦb _) (fun n ω => hΨb _)
    (hΦc (fun n ω => l29Interp (φ n) (Y n ω)) hgn hlim')
    (hΨc (fun n ω => l29Interp (φ n) (Y n ω)) hgn hlim') hn
  have hL2 : ∀ {F : C(X, ℝ) → ℝ} {C : ℝ}, Measurable F → (∀ g, |F g| ≤ C) →
      MemLp (fun ω => F (f ω)) 2 P := fun hme hb =>
    MemLp.of_bound (hme.comp hfm).aestronglyMeasurable _
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hb (f ω))
  rw [covariance_eq_sub (hL2 hΦmeas hΦb) (hL2 hΨmeas hΨb)]
  simp only [Pi.mul_apply]
  linarith

end LQGMetric.CONF
