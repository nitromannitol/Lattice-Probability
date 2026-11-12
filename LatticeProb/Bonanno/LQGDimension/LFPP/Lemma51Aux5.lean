/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.Lemma51Aux5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.Lemma51Aux4
import LatticeProb.Bonanno.LQGDimension.LFPP.Lemma33
import LatticeProb.Bonanno.LQGDimension.Gaussian.MaxInequality

/-!
# Lemma 5.1, auxiliary file 5: the Sudakov–Fernique step

Let `Fn ⊆ V n` be a finite nonempty family with energies at most `E₀`, and let `y f` be vectors
with `‖y f - y g‖² ≥ (1 - α) · 2π ∫₀¹ |f - g| - β`.  Then (`sf_lower`)

`√(1-α) E max_f (Z_f - E(f)) - (1 - √(1-α)) E₀ - √(β log |Fn|) ≤ E max_f (⟪-y f, x⟫ - E(f))`.

Proof: take Gram vectors `U` of `zCov` on `Fn` (so `‖U f - U g‖² = 2π ∫ |f - g|`), and noise
vectors `N f = √(β/2) e_f` (orthonormal `e_f`).  The family `W f = (-y f, N f)` has
`‖W f - W g‖² = ‖y f - y g‖² + β ≥ ‖√(1-α) U f - √(1-α) U g‖²`, so Sudakov–Fernique gives
`E max (√(1-α) U, -E) ≤ E max (W, -E) ≤ E max (-y, -E) + E max_f ⟪N f, x⟫`, and the last
term is at most `√(β/2) √(2 log |Fn|)`.  Finally, pointwise,
`max_f (s ⟪U f, x⟫ - E f) ≥ s max_f (⟪U f, x⟫ - E f) - (1 - s) E₀` for `s ∈ [0,1]`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

namespace LQGDimension.L51

/-- `zCov f f - 2 zCov f g + zCov g g = 2π ∫₀¹ |f - g|`. -/
lemma zCov_comb_sf {f g : ℝ → ℝ} (hf : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hg : IntervalIntegrable g MeasureTheory.volume 0 1) :
    zCov f f - 2 * zCov f g + zCov g g = 2 * π * ∫ x in (0:ℝ)..1, |f x - g x| := by
  have hfa := hf.abs
  have hga := hg.abs
  have hfga := (hf.sub hg).abs
  have e1 : ∫ x in (0:ℝ)..1, (|f x| + |f x| - |f x - f x|) =
      (∫ x in (0:ℝ)..1, |f x|) + ∫ x in (0:ℝ)..1, |f x| := by
    simp only [sub_self, abs_zero, sub_zero]
    exact intervalIntegral.integral_add hfa hfa
  have e3 : ∫ x in (0:ℝ)..1, (|g x| + |g x| - |g x - g x|) =
      (∫ x in (0:ℝ)..1, |g x|) + ∫ x in (0:ℝ)..1, |g x| := by
    simp only [sub_self, abs_zero, sub_zero]
    exact intervalIntegral.integral_add hga hga
  have e2 : ∫ x in (0:ℝ)..1, (|f x| + |g x| - |f x - g x|) =
      (∫ x in (0:ℝ)..1, |f x|) + (∫ x in (0:ℝ)..1, |g x|) - ∫ x in (0:ℝ)..1, |f x - g x| := by
    have h1 : ∫ x in (0:ℝ)..1, (|f x| + |g x| - |f x - g x|) =
        (∫ x in (0:ℝ)..1, (|f x| + |g x|)) - ∫ x in (0:ℝ)..1, |f x - g x| :=
      intervalIntegral.integral_sub (hfa.add hga) hfga
    have h2 : ∫ x in (0:ℝ)..1, (|f x| + |g x|) =
        (∫ x in (0:ℝ)..1, |f x|) + ∫ x in (0:ℝ)..1, |g x| :=
      intervalIntegral.integral_add hfa hga
    rw [h1, h2]
  unfold zCov
  rw [e1, e2, e3]
  ring

section SF

variable {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- Scaling the Gaussian part by `s ∈ [0,1]` with a drift `-E f ≥ -E₀`:
`s E max (⟪U f, x⟫ - E f) - (1 - s) E₀ ≤ E max (s ⟪U f, x⟫ - E f)`. -/
lemma vecEM_smul_lower_sf (F : Finset ι) (hF : F.Nonempty) (u : ι → H) (en : ι → ℝ)
    {E₀ s : ℝ} (hs1 : s ≤ 1) (hE : ∀ i ∈ F, en i ≤ E₀) :
    s * vecExpectedMax F u (fun i => -en i) - (1 - s) * E₀ ≤
      vecExpectedMax F (fun i => s • u i) (fun i => -en i) := by
  have : Nonempty F := hF.to_subtype
  have hpt : ∀ x : H, s * (⨆ i : F, ⟪u i, x⟫ + -en i) - (1 - s) * E₀ ≤
      ⨆ i : F, ⟪s • u i, x⟫ + -en i := by
    intro x
    obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i : F => ⟪u i, x⟫ + -en i)
    rw [← hj]
    refine le_trans ?_ (le_ciSup (f := fun i : F => ⟪s • u i, x⟫ + -en i)
      (Finite.bddAbove_range _) j)
    simp only [real_inner_smul_left]
    nlinarith [mul_le_mul_of_nonneg_left (hE j j.2) (sub_nonneg.2 hs1)]
  unfold vecExpectedMax
  have hi1 := (integrable_iSup_inner_add F u fun i => -en i).const_mul s
  have h : ∫ x, (s * (⨆ i : F, ⟪u i, x⟫ + -en i) - (1 - s) * E₀) ∂stdGaussian H ≤
      ∫ x, (⨆ i : F, ⟪s • u i, x⟫ + -en i) ∂stdGaussian H :=
    integral_mono (hi1.sub (integrable_const _))
      (integrable_iSup_inner_add F (fun i => s • u i) fun i => -en i) fun x => hpt x
  rw [integral_sub hi1 (integrable_const _), integral_const_mul, integral_const, probReal_univ,
    one_smul] at h
  exact h

end SF

/-- **The Sudakov–Fernique step of Lemma 5.1.** -/
theorem sf_lower {n : ℕ} {Fn : Finset (ℝ → ℝ)} (hFnV : ∀ f ∈ Fn, f ∈ V n) (hne : Fn.Nonempty)
    {E₀ α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ : 0 ≤ β) (hE : ∀ f ∈ Fn, energy f ≤ E₀)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (y : (ℝ → ℝ) → E)
    (hy : ∀ f ∈ Fn, ∀ g ∈ Fn,
      (1 - α) * (2 * π * ∫ x in (0:ℝ)..1, |f x - g x|) - β ≤ ‖y f - y g‖ ^ 2) :
    √(1 - α) * gaussianExpectedMax Fn zCov (fun f => -energy f) - (1 - √(1 - α)) * E₀
      - √(β * Real.log Fn.card) ≤ vecExpectedMax Fn (fun f => -y f) (fun f => -energy f) := by
  classical
  set s : ℝ := √(1 - α) with hs
  have hs1 : s ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have hs2 : s ^ 2 = 1 - α := Real.sq_sqrt (by linarith)
  -- Gram vectors of `zCov`
  have hII : ∀ f ∈ Fn, IntervalIntegrable f MeasureTheory.volume 0 1 :=
    fun f hf => mem_V_intervalIntegrable (hFnV f hf)
  obtain ⟨U, hU⟩ := exists_gram_of_psdOn Fn zCov (zCovPSD Fn hII)
  have hG : gaussianExpectedMax Fn zCov (fun f => -energy f) =
      vecExpectedMax Fn U (fun f => -energy f) := by
    rw [← gaussianExpectedMax_gram_eq_vecExpectedMax]
    exact gaussianExpectedMax_congr Fn _ fun i hi j hj => (hU i hi j hj).symm
  have hUd : ∀ f ∈ Fn, ∀ g ∈ Fn, ‖U f - U g‖ ^ 2 = 2 * π * ∫ x in (0:ℝ)..1, |f x - g x| := by
    intro f hf g hg
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      hU f hf f hf, hU f hf g hg, hU g hg g hg]
    exact zCov_comb_sf (hII f hf) (hII g hg)
  -- scaling step
  have hscale := vecEM_smul_lower_sf Fn hne U energy hs1 hE
  -- noise vectors
  set σ : ℝ := if 1 < Fn.card then √(β / 2) else 0 with hσ
  have hσ0 : 0 ≤ σ := by rw [hσ]; split_ifs <;> positivity
  let e : (ℝ → ℝ) → EuclideanSpace ℝ Fn := fun f =>
    if h : f ∈ Fn then EuclideanSpace.single ⟨f, h⟩ 1 else 0
  have he1 : ∀ f ∈ Fn, ‖e f‖ = 1 := by
    intro f hf
    simp [e, hf]
  have he0 : ∀ f ∈ Fn, ∀ g ∈ Fn, f ≠ g → ⟪e f, e g⟫ = 0 := by
    intro f hf g hg hfg
    simp [e, hf, hg, EuclideanSpace.inner_single_left, Ne.symm hfg]
  let N : (ℝ → ℝ) → EuclideanSpace ℝ Fn := fun f => σ • e f
  have hNd : ∀ f ∈ Fn, ∀ g ∈ Fn, f ≠ g → ‖N f - N g‖ ^ 2 = β := by
    intro f hf g hg hfg
    have hcard : 1 < Fn.card := Finset.one_lt_card.2 ⟨f, hf, g, hg, hfg⟩
    have hσ2 : σ ^ 2 = β / 2 := by
      rw [hσ]
      simp only [hcard, ↓reduceIte]
      exact Real.sq_sqrt (by positivity)
    simp only [N]
    rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hσ2, norm_sub_sq_real,
      he1 f hf, he1 g hg, he0 f hf g hg hfg]
    ring
  -- the comparison family
  let W : (ℝ → ℝ) → WithLp 2 (E × EuclideanSpace ℝ Fn) := fun f => WithLp.toLp 2 (-y f, N f)
  have hSF : vecExpectedMax Fn (fun f => s • U f) (fun f => -energy f) ≤
      vecExpectedMax Fn W (fun f => -energy f) := by
    refine sudakovFernique (ℝ → ℝ) (EuclideanSpace ℝ Fn) (WithLp 2 (E × EuclideanSpace ℝ Fn))
      Fn _ W (fun f => -energy f) fun f hf g hg => ?_
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    by_cases hfg : f = g
    · subst hfg
      simp
    have hW : ‖W f - W g‖ ^ 2 = ‖y f - y g‖ ^ 2 + β := by
      simp only [W]
      rw [← WithLp.toLp_sub, WithLp.prod_norm_sq_eq_of_L2]
      simp only [WithLp.toLp_fst, WithLp.toLp_snd, Prod.fst_sub, Prod.snd_sub]
      rw [neg_sub_neg, norm_sub_rev, hNd f hf g hg hfg]
    rw [hW, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hs2, hUd f hf g hg]
    linarith [hy f hf g hg]
  -- splitting off the noise
  have hsplit : vecExpectedMax Fn W (fun f => -energy f) ≤
      vecExpectedMax Fn (fun f => -y f) (fun f => -energy f) + vecExpectedMax Fn N 0 :=
    L33.vecEM_prod_le Fn (fun f => -y f) N (fun f => -energy f)
  -- the noise term
  have hnoise : vecExpectedMax Fn N 0 ≤ √(β * Real.log Fn.card) := by
    have hNe : Nonempty Fn := hne.to_subtype
    have heq : vecExpectedMax Fn N 0 = ∫ x, (⨆ i : Fn, ⟪N i, x⟫)
        ∂stdGaussian (EuclideanSpace ℝ Fn) := by
      unfold vecExpectedMax
      simp
    rcases hσ0.eq_or_lt with h0 | hpos
    · have hN0 : ∀ f, N f = 0 := fun f => by simp [N, ← h0]
      rw [heq]
      simp only [hN0, inner_zero_left, ciSup_const, integral_zero]
      exact Real.sqrt_nonneg _
    · have hcard : 1 < Fn.card := by
        by_contra hc
        rw [hσ] at hpos
        simp only [hc, ↓reduceIte] at hpos
        exact lt_irrefl _ hpos
      have hσe : σ = √(β / 2) := by rw [hσ]; simp only [hcard, ↓reduceIte]
      have hint : Integrable (fun x => ⨆ i : Fn, ⟪N i, x⟫)
          (stdGaussian (EuclideanSpace ℝ Fn)) := by
        have := integrable_iSup_inner_add Fn N 0
        simpa using this
      have hNn : ∀ i ∈ Fn, ‖N i‖ ≤ σ := by
        intro i hi
        simp only [N]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ0, he1 i hi, mul_one]
      rw [heq]
      refine (GaussianMax.integral_iSup_inner_le_sqrt Fn hcard N hpos hNn hint).trans
        (le_of_eq ?_)
      rw [hσe, ← Real.sqrt_mul (by positivity)]
      congr 1
      ring
  have hfin := hscale.trans (hSF.trans (hsplit.trans (add_le_add le_rfl hnoise)))
  rw [hG]
  linarith

end LQGDimension.L51
