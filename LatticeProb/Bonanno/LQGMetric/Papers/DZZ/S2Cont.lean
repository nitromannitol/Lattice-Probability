/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2Cont at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Box

/-!
# DZZ Lemma 2.6, first inequality: the probabilistic core (task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 546–569, Lemma 2.6
`lem-continuity-h-eta`): uniformly in `δ > 0`, `a > 0`, `k ≥ 1`,
`sup_u P(max_{|v − u| ≤ kδ} |η_δ(v) − η_δ(u)| ≥ a log(k+1)) = O(1) e^{−Ω(a²)}`. DZZ's proof uses
only Lemma 2.5 (`Var(η_δ(u) − η_δ(v)) = O(|u − v|/δ)`), the bound
`Var(η_δ(v) − η_δ(u)) = O(log(k+1))` for `|v − u| ≤ kδ` (l. 562), Lemma 2.3 (Fernique) on boxes
of side `δ` and Lemma 2.1 (concentration) with a union bound over the `O(k²)` boxes.

`dzz_lemma26_core` is this argument for any continuous centered Gaussian field `X` on `ℂ` with
`E(X_v − X_u)² ≤ K|u − v|/δ` and `E(X_v − X_u)² ≤ K(1 + log(1 + |u − v|/δ))`; the constant
depends only on `K`. Deviation (bookkeeping only): DZZ first take the maximum over the grid
`𝔠_{⌈log₂ δ⁻¹⌉+1}` and then within `δ`-balls around grid points; we apply Lemmas 2.3 and 2.1
directly to `x ↦ X_x − X_u` on each of the `(2k+2)²` boxes of side `δ` covering the ball.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace DZZ

open SupTail

universe u

/-- `x ↦ X x − X u` is a Gaussian process. -/
lemma isGaussianProcess_sub_const {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℂ → Ω → ℝ} (hX : IsGaussianProcess X P) (u : ℂ) :
    IsGaussianProcess (fun x ω => X x ω - X u ω) P :=
  hX.of_isGaussianProcess fun x => ⟨{x, u},
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({x, u} : Finset ℂ) => ℝ) ⟨x, by simp⟩ -
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({x, u} : Finset ℂ) => ℝ) ⟨u, by simp⟩,
    fun ω => rfl⟩

/-- **DZZ Lemma 2.6, first inequality (l. 546–569), probabilistic core.** -/
theorem dzz_lemma26_core {K : ℝ} (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (X : ℂ → Ω → ℝ)
      (δ : ℝ), 0 < δ → IsGaussianProcess X P → (∀ v, ∫ ω, X v ω ∂P = 0) →
      (∀ ω, Continuous fun v => X v ω) →
      (∀ u v, ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ K * ‖u - v‖ / δ) →
      (∀ u v, ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ K * (1 + Real.log (1 + ‖u - v‖ / δ))) →
      ∀ (u : ℂ) (k : ℕ), 1 ≤ k → ∀ a : ℝ, 0 ≤ a →
        P.real {ω | ∃ v, ‖v - u‖ ≤ k * δ ∧ a * Real.log (k + 1) ≤ |X v ω - X u ω|} ≤
          C * Real.exp (-a ^ 2 / C) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set c₁ := (1 + Real.log 3 + Real.log 2) / Real.log 2 with hc₁_def
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hc₁ : 0 < c₁ := by positivity
  set A := 8 * Real.exp (ferniqueCF ^ 2 / 2) with hA_def
  have hA : 0 < A := by positivity
  set D := 8 * K * c₁ / Real.log 2 with hD_def
  have hD : 0 < D := by positivity
  obtain ⟨C, hC_def⟩ : ∃ C : ℝ, C = A + D + 32 * K * c₁ + 2 := ⟨_, rfl⟩
  have hKc : 0 < K * c₁ := mul_pos hK hc₁
  have hC0 : 0 < C := by rw [hC_def]; positivity
  have hAC : A ≤ C := by linarith only [hC_def, hD, hKc]
  have hDC : D ≤ C := by linarith only [hC_def, hA, hKc]
  have h32C : 32 * K * c₁ ≤ C := by linarith only [hC_def, hA, hD]
  have h2C : 2 ≤ C := by linarith only [hC_def, hA, hD, hKc]
  refine ⟨C, hC0, ?_⟩
  intro Ω _ P X δ hδ hX h0 hc hinc hlog u k hk a ha
  have hP : IsProbabilityMeasure P := hX.isProbabilityMeasure
  set S := {ω | ∃ v, ‖v - u‖ ≤ k * δ ∧ a * Real.log (k + 1) ≤ |X v ω - X u ω|}
  by_cases hsmall : a ^ 2 < 16 * K * c₁
  · have h1 : P.real S ≤ 1 := measureReal_le_one
    have hx : a ^ 2 / C ≤ 1 / 2 := by
      rw [div_le_iff₀ hC0]; linarith only [hsmall, h32C]
    have he : 1 / 2 ≤ Real.exp (-a ^ 2 / C) := by
      have := Real.add_one_le_exp (-a ^ 2 / C)
      rw [neg_div] at this ⊢
      linarith only [this, hx]
    have : 1 ≤ C * Real.exp (-a ^ 2 / C) := by nlinarith only [he, h2C]
    linarith only [this, h1]
  push_neg at hsmall
  -- the covering boxes
  set ℓ := Real.log (k + 1) with hℓ_def
  have hk1 : (2 : ℝ) ≤ k + 1 := by have : (1 : ℝ) ≤ k := by exact_mod_cast hk
                                   linarith
  have hℓ2 : Real.log 2 ≤ ℓ := Real.log_le_log two_pos hk1
  have hℓ : 0 < ℓ := hl2.trans_le hℓ2
  set m : ℕ := 2 * (k + 1) with hm_def
  have hm0 : 0 < m := by positivity
  set s : ℝ := 2 * (k + 1) * δ with hs_def
  have hs : 0 < s := by positivity
  set x₀ : ℂ := u - ⟨(k + 1) * δ, (k + 1) * δ⟩ with hx₀_def
  have hside : s / m = δ := by
    rw [hs_def, hm_def]; push_cast; field_simp
  -- the variance bound on the big box
  set σ := Real.sqrt (K * (1 + Real.log 3 + ℓ)) with hσ_def
  have hσ2 : σ ^ 2 = K * (1 + Real.log 3 + ℓ) := Real.sq_sqrt (by positivity)
  have hσ2' : σ ^ 2 ≤ K * c₁ * ℓ := by
    rw [hσ2, hc₁_def]
    have : 1 + Real.log 3 + ℓ ≤ (1 + Real.log 3 + Real.log 2) / Real.log 2 * ℓ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      nlinarith only [hℓ2, hl3, hl2]
    calc K * (1 + Real.log 3 + ℓ) ≤ K * ((1 + Real.log 3 + Real.log 2) / Real.log 2 * ℓ) :=
          mul_le_mul_of_nonneg_left this hK.le
      _ = _ := by ring
  have hσ0 : 0 < σ ^ 2 := by rw [hσ2]; positivity
  set Z : ℂ → Ω → ℝ := fun x ω => X x ω - X u ω
  have hZ : IsGaussianProcess Z P := isGaussianProcess_sub_const hX u
  have hZ0 : ∀ x, ∫ ω, Z x ω ∂P = 0 := fun x => by
    simp only [Z]
    rw [integral_sub (hX.hasGaussianLaw_eval x).integrable (hX.hasGaussianLaw_eval u).integrable,
      h0, h0, sub_zero]
  have hbig : ∀ x ∈ ferniqueBox x₀ s, ‖x - u‖ ≤ 2 * (k + 1) * δ := by
    rintro x ⟨⟨h1, h2⟩, h3, h4⟩
    simp only [hx₀_def, Complex.sub_re, Complex.sub_im, hs_def] at h1 h2 h3 h4
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im]
    have e1 : |x.re - u.re| ≤ (k + 1) * δ := abs_le.2 ⟨by linarith, by linarith⟩
    have e2 : |x.im - u.im| ≤ (k + 1) * δ := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hvarZ : ∀ x ∈ ferniqueBox x₀ s, Var[Z x; P] ≤ σ ^ 2 := by
    intro x hx
    rw [variance_of_integral_eq_zero (hZ.aemeasurable x) (hZ0 x)]
    refine (hlog u x).trans ?_
    rw [hσ2]
    refine mul_le_mul_of_nonneg_left ?_ hK.le
    have hd : ‖u - x‖ / δ ≤ 2 * (k + 1) := by
      rw [div_le_iff₀ hδ, norm_sub_rev]; exact hbig x hx
    have h3 : 1 + ‖u - x‖ / δ ≤ 3 * (k + 1) := by linarith
    have hpos : 0 < 1 + ‖u - x‖ / δ := by positivity
    have := Real.log_le_log hpos h3
    rw [Real.log_mul (by norm_num) (by positivity)] at this
    linarith
  -- each sub-box
  set E : Fin m × Fin m → Set Ω := fun kl =>
    {ω | a * ℓ ≤ ⨆ v : subBox x₀ s m kl.1 kl.2, |Z v ω|} with hE_def
  have hEb : ∀ kl, P.real (E kl) ≤ (A / 4) * Real.exp (-a ^ 2 * ℓ / (4 * K * c₁)) := by
    rintro ⟨k', l'⟩
    have hQ := subBox_subset (x₀ := x₀) hs k' l'
    have hM : ferniqueCF * Real.sqrt (K / δ * (s / m)) ≤ ferniqueCF * Real.sqrt K := by
      rw [hside, div_mul_cancel₀ _ hδ.ne']
    have key := dzz_box_sup_abs_tail (X := Z) hZ hZ0 (div_pos hs (Nat.cast_pos.2 hm0))
      (div_pos hK hδ) (fun ω => ((hc ω).sub continuous_const).continuousOn)
      (fun x _ y _ => by
        have e : (fun ω => (Z y ω - Z x ω) ^ 2) = fun ω => (X y ω - X x ω) ^ 2 := by
          funext ω; simp only [Z]; ring
        rw [e]; refine (hinc x y).trans (le_of_eq ?_); ring)
      (fun v hv => hvarZ v (hQ hv)) hM (mul_nonneg ha hℓ.le)
    refine key.trans ?_
    have e1 : (ferniqueCF * Real.sqrt K) ^ 2 / (2 * σ ^ 2) ≤ ferniqueCF ^ 2 / 2 := by
      rw [mul_pow, Real.sq_sqrt hK.le, div_le_div_iff₀ (by positivity) two_pos]
      have : K ≤ σ ^ 2 := by rw [hσ2]; nlinarith only [hl3, hℓ, hK]
      nlinarith only [this, sq_nonneg ferniqueCF]
    have e2 : -(a * ℓ) ^ 2 / (2 * (2 * σ ^ 2)) ≤ -a ^ 2 * ℓ / (4 * K * c₁) := by
      rw [neg_div, neg_mul, neg_div, neg_le_neg_iff,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hσ2' (by positivity : 0 ≤ a ^ 2 * ℓ * 4)
      nlinarith only [this, hℓ, sq_nonneg a]
    rw [hA_def]
    calc 2 * Real.exp ((ferniqueCF * Real.sqrt K) ^ 2 / (2 * σ ^ 2)) *
          Real.exp (-(a * ℓ) ^ 2 / (2 * (2 * σ ^ 2)))
        ≤ 2 * Real.exp (ferniqueCF ^ 2 / 2) * Real.exp (-a ^ 2 * ℓ / (4 * K * c₁)) := by
          gcongr
      _ = 8 * Real.exp (ferniqueCF ^ 2 / 2) / 4 * Real.exp (-a ^ 2 * ℓ / (4 * K * c₁)) := by ring
  -- covering
  have hsub : S ⊆ ⋃ kl, E kl := by
    rintro ω ⟨v, hv, hva⟩
    have hvB : v ∈ ferniqueBox x₀ s := by
      have h1 := (Complex.abs_re_le_norm (v - u)).trans hv
      have h2 := (Complex.abs_im_le_norm (v - u)).trans hv
      simp only [Complex.sub_re, Complex.sub_im] at h1 h2
      obtain ⟨h1a, h1b⟩ := abs_le.1 h1
      obtain ⟨h2a, h2b⟩ := abs_le.1 h2
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [hx₀_def, hs_def, Complex.sub_re, Complex.sub_im] <;>
        nlinarith only [h1a, h1b, h2a, h2b, hδ]
    obtain ⟨k', l', hkl⟩ := exists_mem_subBox hs hm0 hvB
    refine mem_iUnion.2 ⟨(k', l'), ?_⟩
    simp only [hE_def, mem_ofPred_eq]
    have : CompactSpace (subBox x₀ s m k' l') :=
      isCompact_iff_compactSpace.1 (isCompact_ferniqueBox _ _)
    refine hva.trans ?_
    exact le_ciSup (f := fun v' : subBox x₀ s m k' l' => |Z v' ω|)
      (bddAbove_range_of_continuous (X := fun (v' : subBox x₀ s m k' l') ω => |Z v' ω|)
        (fun ω' => (((hc ω').sub continuous_const).comp continuous_subtype_val).abs) ω) ⟨v, hkl⟩
  have hPS : P.real S ≤ (m : ℝ) * m * ((A / 4) * Real.exp (-a ^ 2 * ℓ / (4 * K * c₁))) := by
    calc P.real S ≤ P.real (⋃ kl, E kl) := measureReal_mono hsub
      _ ≤ ∑ kl, P.real (E kl) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _kl : Fin m × Fin m, (A / 4) * Real.exp (-a ^ 2 * ℓ / (4 * K * c₁)) :=
          Finset.sum_le_sum fun kl _ => hEb kl
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_mul, mul_assoc]
  refine hPS.trans ?_
  -- final arithmetic: `(2k+2)² e^{−a²ℓ/(4Kc₁)} ≤ 4 e^{−a²/D}`
  have hmm : (m : ℝ) * m = 4 * Real.exp (2 * ℓ) := by
    rw [hm_def, show 2 * ℓ = ℓ + ℓ by ring, Real.exp_add, hℓ_def,
      Real.exp_log (by positivity)]
    push_cast; ring
  rw [hmm]
  have hexp : Real.exp (2 * ℓ) * Real.exp (-a ^ 2 * ℓ / (4 * K * c₁)) ≤ Real.exp (-a ^ 2 / D) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : 4 ≤ a ^ 2 / (4 * K * c₁) := by
      rw [le_div_iff₀ (by positivity)]; linarith only [hsmall]
    have h2 : a ^ 2 / D ≤ a ^ 2 * ℓ / (8 * K * c₁) := by
      rw [hD_def, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hℓ2 (by positivity : 0 ≤ a ^ 2 * (8 * K * c₁))
      nlinarith only [this]
    have e : -a ^ 2 * ℓ / (4 * K * c₁) = -(a ^ 2 / (4 * K * c₁)) * ℓ := by ring
    have e' : a ^ 2 * ℓ / (8 * K * c₁) = a ^ 2 / (4 * K * c₁) * ℓ / 2 := by ring
    rw [e, neg_div]
    rw [e'] at h2
    nlinarith only [h1, h2, hℓ]
  have hDC' : Real.exp (-a ^ 2 / D) ≤ Real.exp (-a ^ 2 / C) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg a) hD hDC
  calc 4 * Real.exp (2 * ℓ) * (A / 4 * Real.exp (-a ^ 2 * ℓ / (4 * K * c₁)))
      = A * (Real.exp (2 * ℓ) * Real.exp (-a ^ 2 * ℓ / (4 * K * c₁))) := by ring
    _ ≤ C * Real.exp (-a ^ 2 / C) :=
        mul_le_mul hAC (hexp.trans hDC') (by positivity) hC0.le

end DZZ
end LQGMetric
