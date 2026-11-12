/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcA at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.SupTailBorell

/-!
# DZZ Lemma 2.1 for continuum-indexed Gaussian processes via a finite net (P2-DZZCONC)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) apply their Lemma 2.1 (`lem-Gaussian-concentration`,
l. 326–348) in the proof of Proposition 3.17 (l. 1597–1601, 1644–1646) to the coarse field
`𝒳_δ`, a Gaussian process indexed by a continuum, with `min_{x' ∈ 𝒜'} ‖𝒳_δ − x'‖_∞`.
Lemma 2.1 is proved (finite-dimensional, Gram form) as `GaussConc.dzz_lemma21_gram`.

* `dzz_lemma21_le`: the random-vector form with `Var X_i ≤ σ²` (instead of `σ² = max Var`, as in
  `GaussConc.dzz_lemma21_strong`), for `Ω : Type*`.
* **`gauss_far_le`**: the reduction from the continuum to a finite net, done once: if every pair
  `x ∈ 𝒢`, `x' ∈ 𝒜'` satisfies `|x s − x' s| ≤ max_i |x (t i) − x' (t i)| + η` (e.g. `𝒢`
  equicontinuous and `t` an `η/2`-net), `P(X ∈ 𝒜') ≥ c` and `ℓ ≥ Cσ + η`, then
  `P(X ∈ 𝒢, X is not within ℓ of 𝒜' uniformly) ≤ exp(−(ℓ − η − Cσ)²/(2σ²))`.
  Own elementary reduction (the finite case is DZZ Lemma 2.1 applied to `(X (t i))_i`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric
open scoped RealInnerProductSpace NNReal

namespace LQGMetric
namespace DZZ

open GaussConc

universe u v

/-- DZZ Lemma 2.1 for a centered Gaussian vector with `Var X_i ≤ σ²`. -/
theorem dzz_lemma21_le (c : ℝ) (hc : 0 < c) : ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (X : Ω → Fin n → ℝ), HasGaussianLaw X P → (∀ i, ∫ ω, X ω i ∂P = 0) → ∀ σ : ℝ, 0 ≤ σ →
    (∀ i, Var[fun ω => X ω i; P] ≤ σ ^ 2) →
    ∀ B : Set (Fin n → ℝ), c ≤ P.real {ω | X ω ∈ B} → ∀ lam : ℝ, C * σ ≤ lam →
    P.real {ω | lam ≤ infDist (X ω) B} ≤ exp (-(lam - C * σ) ^ 2 / (2 * σ ^ 2)) := by
  obtain ⟨C, hC1, hC⟩ := dzz_lemma21_gram c hc
  refine ⟨C, hC1, ?_⟩
  intro Ω _ P n X hX h0 σ hσ hσ2 B hB lam hlam
  have := hX.isProbabilityMeasure
  obtain ⟨v, hv, hmap⟩ := exists_gramVec_of_centered hX h0
  have hvσ : ∀ i, ‖v i‖ ≤ ((⟨σ, hσ⟩ : ℝ≥0) : ℝ) := by
    intro i
    have h : ‖v i‖ ^ 2 ≤ σ ^ 2 := by rw [hv]; exact hσ2 i
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hσ two_ne_zero).1 h
  have hB' : c ≤ (stdGaussian (EuclideanSpace ℝ (Fin n))).real {z | gramVec v z ∈ closure B} := by
    have h1 : P.real {ω | X ω ∈ B} ≤ P.real (X ⁻¹' closure B) :=
      measureReal_mono (fun ω hω => subset_closure hω)
    rw [measureReal_preimage_eq hX hmap isClosed_closure.measurableSet] at h1
    exact hB.trans h1
  have h := hC _ n v ⟨σ, hσ⟩ hvσ (closure B) hB' lam hlam
  simp only [infDist_closure] at h
  have hmeas : MeasurableSet {x : Fin n → ℝ | lam ≤ infDist x B} :=
    measurableSet_le measurable_const (continuous_infDist_pt B).measurable
  have e := measureReal_preimage_eq hX hmap hmeas
  simp only [preimage_setOf_eq] at e
  rw [e]
  exact h

/-- **DZZ Lemma 2.1 for a continuum-indexed process, via a finite net.** -/
theorem gauss_far_le (c : ℝ) (hc : 0 < c) : ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) {T : Type v} (X : T → Ω → ℝ),
    IsGaussianProcess X P → (∀ t, ∫ ω, X t ω ∂P = 0) → ∀ σ : ℝ, 0 ≤ σ →
    (∀ t, Var[X t; P] ≤ σ ^ 2) → ∀ (𝒢 𝒜' : Set (T → ℝ)) (η : ℝ) (n : ℕ) (t : Fin n → T),
    (∀ x ∈ 𝒢, ∀ x' ∈ 𝒜', ∀ s, ∃ i, |x s - x' s| ≤ |x (t i) - x' (t i)| + η) →
    c ≤ P.real {ω | (fun s => X s ω) ∈ 𝒜'} → ∀ ℓ : ℝ, C * σ + η ≤ ℓ →
    P.real {ω | (fun s => X s ω) ∈ 𝒢 ∧ ∀ x' ∈ 𝒜', ∃ s, ℓ < |X s ω - x' s|} ≤
      exp (-(ℓ - η - C * σ) ^ 2 / (2 * σ ^ 2)) := by
  obtain ⟨C, hC1, hC⟩ := dzz_lemma21_le.{u} c hc
  refine ⟨C, hC1, ?_⟩
  intro Ω _ P T X hX h0 σ hσ hvar 𝒢 𝒜' η n t hnet hA ℓ hℓ
  set Y : Ω → Fin n → ℝ := fun ω i => X (t i) ω
  set R : (T → ℝ) → (Fin n → ℝ) := fun x i => x (t i)
  have hY : HasGaussianLaw Y P := SupTail.hasGaussianLaw_finVec hX t
  have := hY.isProbabilityMeasure
  have hB : c ≤ P.real {ω | Y ω ∈ R '' 𝒜'} :=
    hA.trans (measureReal_mono fun ω hω => ⟨_, hω, rfl⟩)
  have hne : (R '' 𝒜').Nonempty := by
    by_contra hE
    rw [not_nonempty_iff_eq_empty] at hE
    simp [hE] at hB
    linarith
  have key := hC P n Y hY (fun i => h0 (t i)) σ hσ (fun i => hvar (t i)) (R '' 𝒜') hB (ℓ - η)
    (by linarith)
  refine (measureReal_mono ?_).trans key
  · intro ω hω
    obtain ⟨hG, hfar⟩ := hω
    simp only [mem_setOf_eq]
    rw [le_infDist hne]
    rintro _ ⟨x', hx', rfl⟩
    obtain ⟨s, hs⟩ := hfar x' hx'
    obtain ⟨i, hi⟩ := hnet _ hG x' hx' s
    have h1 : dist (Y ω i) (R x' i) ≤ dist (Y ω) (R x') := dist_le_pi_dist _ _ i
    rw [Real.dist_eq] at h1
    simp only [Y, R] at h1
    linarith

end DZZ
end LQGMetric
