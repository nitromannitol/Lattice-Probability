/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L12 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L12Aux

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DDDF Lemma 12′ (decision D-B4): conformal comparison maps between rectangles

**Source.** DDDF Lemma 12 (Ding–Dubédat–Dunlap–Falconet, *Tightness of Liouville first passage
percolation for γ ∈ (0,2)*, arXiv:1904.08021, `tightness.tex` l. 744–760) = Step 1 of the proof of
DF Thm 3.1 (Dubédat–Falconet, arXiv:1809.02607, `LiouvilleMetricStarScale.tex` l. 640–660).
The paper uses ellipses and Riemann maps extended by Schwarz reflection; decision D-B4
(`decisions/DEC-B.md` §(d), deviation D-DDDF-14) replaces them by explicit maps:

* `K = α(S_ρ)`, `S_ρ = G(D̄_ρ)`, `G(ζ) = log((1+ζ)/(1−ζ))`, `α(w) = (w₀/2 + iH/2) + i(w₀/π) w`,
  `w₀ = a 2^{-p}`, `H = b 2^{-p}`; the marked sides of `K` are its two long sides
  `α(G(ρe^{±iθ}))`, `θ ∈ [θ₁, π − θ₁]`, each split into `m` pieces of equal angular length;
* `F_{ij}(z) = (a'/2 + ib'/2) + (b'/π) G(M_{ij}(G⁻¹(α⁻¹ z)))`, `M_{ij}` a Möbius automorphism of
  `D_ρ` moving the `i`-th left piece next to `−ρ` and the `j`-th right piece next to `ρ`.

**Statement (L12′).** For all `a, b, a', b' > 0` (DDDF assume `a/b < 1 < a'/b'`; the construction
does not need it) there are `p, m ≥ 1`, a compact `K` and compact pieces `A_i, B_j ⊆ K` with
(1) every left–right crossing of `[0, a2^{-p}] × [0, b2^{-p}]` has a sub-path in `K` from some
`A_i` to some `B_j`; (2) for every `(i, j)` there is `F` injective holomorphic on an open bounded
`U ⊇ K` with `1 ≤ |F'| ≤ C`, `|F''| ≤ C` on `U`, such that every path in `F(K)` from `F(A_i)` to
`F(B_j)` crosses `[0,a'] × [0,b']` from left to right.
-/

namespace LQGMetric.DDDF.L12

open Set Real Metric

lemma beta_bounds {θ₁ φ φ' : ℝ} (h0 : 0 < θ₁) (h1 : θ₁ ≤ π / 2) (hφ : φ ∈ Icc θ₁ (π - θ₁))
    (hφ' : φ' ∈ Icc θ₁ (π - θ₁)) :
    |Real.sin ((π - φ - φ') / 4)| < Real.cos ((π - φ - φ') / 4) ∧
      2 / (Real.cos ((π - φ - φ') / 4) - |Real.sin ((π - φ - φ') / 4)|) ≤
        2 / (Real.cos (π / 4 - θ₁ / 2) - Real.sin (π / 4 - θ₁ / 2)) := by
  set β := (π - φ - φ') / 4 with hβd
  set βm := π / 4 - θ₁ / 2 with hβmd
  have hπ := Real.pi_pos
  obtain ⟨k1, k2⟩ := hφ
  obtain ⟨k3, k4⟩ := hφ'
  have hβ : |β| ≤ βm := abs_le.2 ⟨by linarith, by linarith⟩
  have hcos : Real.cos βm ≤ Real.cos β := by
    rw [← Real.cos_abs β]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hβ
  have hsin : |Real.sin β| ≤ Real.sin βm := by
    have := abs_le.1 hβ
    refine abs_le.2 ⟨?_, ?_⟩
    · rw [← Real.sin_neg]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) this.1
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) this.2
  have hm : Real.sin βm < Real.cos βm := by
    rw [← Real.cos_pi_div_two_sub]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  refine ⟨by linarith, ?_⟩
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

lemma norm_rho_exp (ρ θ : ℝ) (hρ : 0 ≤ ρ) : ‖(ρ : ℂ) * Complex.exp (θ * Complex.I)‖ = ρ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ, Complex.norm_exp_ofReal_mul_I, mul_one]

lemma continuous_alphaS (w₀ H : ℝ) : Continuous (alphaS w₀ H) := by unfold alphaS; fun_prop

lemma continuous_arc {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (w₀ H : ℝ) :
    Continuous fun θ : ℝ => alphaS w₀ H (sG ((ρ : ℂ) * Complex.exp (θ * Complex.I))) := by
  rw [continuous_iff_continuousAt]; intro θ
  refine (continuous_alphaS w₀ H).continuousAt.comp ?_
  refine ContinuousAt.comp (g := sG) ?_ (by fun_prop)
  exact (differentiableAt_sG (by rw [norm_rho_exp ρ θ hρ0]; exact hρ1)).continuousAt

/-- **DDDF Lemma 12′** (decision D-B4; DDDF Lemma 12 = DF Thm 3.1 Step 1). -/
theorem lemma12' {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b') :
    ∃ (p m : ℕ) (K : Set ℂ) (A B : Fin m → Set ℂ), 1 ≤ p ∧ 1 ≤ m ∧ IsCompact K ∧
      (∀ i, IsCompact (A i) ∧ A i ⊆ K) ∧ (∀ j, IsCompact (B j) ∧ B j ⊆ K) ∧
      (∀ {z₀ z₁ : ℂ} (γ : Path z₀ z₁), (∀ τ, γ τ ∈ RectCross.rect 0 (a / 2 ^ p) 0 (b / 2 ^ p)) →
        z₀.re = 0 → z₁.re = a / 2 ^ p →
        ∃ (i j : Fin m) (s t : ℝ), 0 ≤ s ∧ s ≤ t ∧ t ≤ 1 ∧ (∀ u ∈ Icc s t, γ.extend u ∈ K) ∧
          γ.extend s ∈ A i ∧ γ.extend t ∈ B j) ∧
      ∀ i j, ∃ (F : ℂ → ℂ) (U : Set ℂ), IsOpen U ∧ Bornology.IsBounded U ∧ K ⊆ U ∧
        DifferentiableOn ℂ F U ∧ InjOn F U ∧
        (∃ C : ℝ, ∀ z ∈ U, 1 ≤ ‖deriv F z‖ ∧ ‖deriv F z‖ ≤ C ∧ ‖deriv (deriv F) z‖ ≤ C) ∧
        ∀ {z₀ z₁ : ℂ} (γ : Path z₀ z₁), (∀ τ, γ τ ∈ F '' K) → z₀ ∈ F '' A i →
          z₁ ∈ F '' B j → RectCross.CrossesLR γ 0 a' 0 b' := by
  have hπ := Real.pi_pos
  set U₀ := π * b / (2 * a) with hU₀
  set X := π * a' / (2 * b') with hX
  obtain ⟨ρ, hρ0, hρ1, hk, hc₀1, hXρ⟩ := exists_rho U₀ X
  have hc₀0 : 0 ≤ cZero ρ U₀ := by
    have : 1 ≤ Real.exp (2 * U₀) := Real.one_le_exp (by positivity)
    unfold cZero
    exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (by positivity)
  set θ₁ := Real.arccos (cZero ρ U₀) with hθ₁
  have hθ₁0 : 0 < θ₁ := Real.arccos_pos.2 hc₀1
  have hθ₁2 : θ₁ ≤ π / 2 := Real.arccos_le_pi_div_two.2 hc₀0
  set L := 2 / (Real.cos (π / 4 - θ₁ / 2) - Real.sin (π / 4 - θ₁ / 2)) with hLd
  have hL0 : 0 ≤ L := by
    have := (beta_bounds hθ₁0 hθ₁2 ⟨le_refl θ₁, by linarith⟩ ⟨le_refl θ₁, by linarith⟩).2
    refine le_trans ?_ this
    have h := (beta_bounds hθ₁0 hθ₁2 ⟨le_refl θ₁, by linarith⟩ ⟨le_refl θ₁, by linarith⟩).1
    exact (div_pos two_pos (by linarith)).le
  have hρ' : 0 < 1 - ρ := by linarith
  set m : ℕ := ⌈L * π / (2 * (1 - ρ))⌉₊ + 1 with hmd
  have hm : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set Δ := (π - 2 * θ₁) / m with hΔd
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) hmpos.le
  have hmΔ : θ₁ + m * Δ = π - θ₁ := by rw [hΔd]; field_simp; ring
  have hsmall : ρ * (L * (Δ / 2)) ≤ 1 - ρ := by
    have h1 : L * π / (2 * (1 - ρ)) ≤ m := by
      have := Nat.le_ceil (L * π / (2 * (1 - ρ))); rw [hmd]; push_cast; linarith
    rw [div_le_iff₀ (by positivity)] at h1
    have h2 : L * (Δ / 2) * m ≤ L * π / 2 := by
      rw [hΔd]; field_simp; nlinarith
    have h3 : L * (Δ / 2) ≤ 1 - ρ := by
      rw [← mul_le_mul_iff_of_pos_right hmpos]; nlinarith
    nlinarith [mul_nonneg hL0 hΔ0]
  set φ : Fin m → ℝ := fun i => θ₁ + ((i : ℕ) + 1 / 2) * Δ with hφd
  have hφ : ∀ i, φ i ∈ Icc θ₁ (π - θ₁) := by
    intro i
    have hi : ((i : ℕ) : ℝ) + 1 / 2 ≤ m := by
      have : (i : ℕ) + 1 ≤ m := i.2
      have : ((i : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast this
      linarith
    constructor
    · simp only [hφd]; nlinarith
    · rw [← hmΔ]; simp only [hφd]; nlinarith
  have hnear : ∀ (i : Fin m) θ, θ ∈ Icc (θ₁ + (i : ℕ) * Δ) (θ₁ + ((i : ℕ) + 1) * Δ) →
      |θ - φ i| ≤ Δ / 2 := by
    intro i θ hθ
    simp only [hφd]
    exact abs_le.2 ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  set β : Fin m → Fin m → ℝ := fun i j => (π - φ i - φ j) / 4 with hβd
  set κ : Fin m → Fin m → ℝ := fun i j => 2 * β i j + φ j with hκd
  have hβ : ∀ i j, |Real.sin (β i j)| < Real.cos (β i j) ∧
      2 / (Real.cos (β i j) - |Real.sin (β i j)|) ≤ L := fun i j =>
    beta_bounds hθ₁0 hθ₁2 (hφ i) (hφ j)
  have hex := fun i j => exists_nbhd_phiM (κ := κ i j) hρ0 hρ1 (hβ i j).1
  choose U' hU'o hU'b hSU _ hdiff hinj C hCpos hC using hex
  set Cs := ∑ i, ∑ j, C i j with hCsd
  have hCs : ∀ i j, C i j ≤ Cs := fun i j =>
    (Finset.single_le_sum (f := fun j => C i j) (fun j _ => (hCpos i j).le)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, C i j)
        (fun i _ => Finset.sum_nonneg fun j _ => (hCpos i j).le) (Finset.mem_univ i))
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (a * Cs / b') (by norm_num : (1 : ℝ) < 2)
  set w₀ := a / 2 ^ (n + 1) with hw₀d
  set H := b / 2 ^ (n + 1) with hHd
  have hw₀ : 0 < w₀ := by positivity
  have hH : 0 < H := by positivity
  have hw₀C : ∀ i j, 1 ≤ b' / w₀ * (C i j)⁻¹ := by
    intro i j
    have hC0 := hCpos i j
    have e : b' / w₀ * (C i j)⁻¹ = b' / (w₀ * C i j) := by field_simp
    rw [e, one_le_div (by positivity)]
    rw [div_lt_iff₀ hb'] at hn
    have h2 : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : w₀ * 2 ^ (n + 1) = a := by rw [hw₀d]; field_simp
    have h4 : w₀ * Cs < b' := by
      by_contra hcon; rw [not_lt] at hcon
      have : a * Cs ≤ 2 ^ n * b' := hn.le
      nlinarith [hCs i j, mul_le_mul_of_nonneg_left h2 hw₀.le]
    nlinarith [hCs i j]
  have hUc : π * H / (2 * w₀) ≤ U₀ := by
    rw [hU₀, hHd, hw₀d]; field_simp; rfl
  set K := alphaS w₀ H '' (sG '' closedBall 0 ρ) with hKd
  have hKimg : K = (fun ζ => alphaS w₀ H (sG ζ)) '' closedBall 0 ρ := by rw [hKd, image_image]
  have hcontK : ContinuousOn (fun ζ => alphaS w₀ H (sG ζ)) (closedBall 0 ρ) := by
    intro ζ hζ
    rw [mem_closedBall, dist_zero_right] at hζ
    exact ((continuous_alphaS w₀ H).continuousAt.comp
      (differentiableAt_sG (by linarith)).continuousAt).continuousWithinAt
  set A : Fin m → Set ℂ := fun i =>
    (fun θ : ℝ => alphaS w₀ H (sG ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) ''
      Icc (θ₁ + (i : ℕ) * Δ) (θ₁ + ((i : ℕ) + 1) * Δ) with hAd
  set B : Fin m → Set ℂ := fun j =>
    (fun θ : ℝ => alphaS w₀ H (sG ((ρ : ℂ) * Complex.exp ((-θ : ℝ) * Complex.I)))) ''
      Icc (θ₁ + (j : ℕ) * Δ) (θ₁ + ((j : ℕ) + 1) * Δ) with hBd
  have hmemK : ∀ θ : ℝ, alphaS w₀ H (sG ((ρ : ℂ) * Complex.exp (θ * Complex.I))) ∈ K :=
    fun θ => ⟨_, ⟨_, by rw [mem_closedBall, dist_zero_right, norm_rho_exp ρ θ hρ0.le], rfl⟩, rfl⟩
  refine ⟨n + 1, m, K, A, B, by omega, hm, ?_, fun i => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hKimg]; exact (isCompact_closedBall _ _).image_of_continuousOn hcontK
  · exact isCompact_Icc.image (continuous_arc hρ0.le hρ1 w₀ H)
  · rintro _ ⟨θ, -, rfl⟩; exact hmemK θ
  · exact isCompact_Icc.image ((continuous_arc hρ0.le hρ1 w₀ H).comp continuous_neg)
  · rintro _ ⟨θ, -, rfl⟩; exact hmemK (-θ)
  · intro z₀ z₁ γ hγ hp hq
    obtain ⟨s, t, θ, θ', hs0, hst, ht1, hK', hθ, hθ', hs, ht⟩ :=
      src_crossing hρ0 hρ1 hw₀ hH hUc hk γ hγ hp hq
    rw [← hθ₁, ← hmΔ] at hθ hθ'
    obtain ⟨i, hi⟩ := exists_piece hm hΔ0 hθ
    obtain ⟨j, hj⟩ := exists_piece hm hΔ0 hθ'
    exact ⟨i, j, s, t, hs0, hst, ht1, hK', ⟨θ, hi, hs.symm⟩, ⟨θ', hj, ht.symm⟩⟩
  · intro i j
    set F : ℂ → ℂ := fun z => ((a' / 2 : ℝ) + (b' / 2 : ℝ) * Complex.I) +
      ((b' / π : ℝ) : ℂ) * phiM ρ (β i j) (κ i j) (alphaInv w₀ H z) with hFdef
    obtain ⟨U, hUo, hUb, hKU, hFd, hFi, hFC⟩ := tgt_analytic (a' := a') (H := H)
      (C := C i j) hw₀ hb' (hU'o i j) (hU'b i j) (hSU i j) (hdiff i j) (hinj i j) (hC i j)
    refine ⟨F, U, hUo, hUb, hKU, hFd, hFi, ⟨max (b' / w₀ * C i j) (b' / w₀ * (π / w₀) * C i j),
      fun z hz => ⟨(hw₀C i j).trans (hFC z hz).1, (hFC z hz).2.1.trans (le_max_left _ _),
        (hFC z hz).2.2.trans (le_max_right _ _)⟩⟩, ?_⟩
    intro z₀ z₁ γ hγ h0 h1
    have hFval : ∀ ζ : ℂ, ‖ζ‖ ≤ ρ → F (alphaS w₀ H (sG ζ)) =
        ((a' / 2 : ℝ) + (b' / 2 : ℝ) * Complex.I) + ((b' / π : ℝ) : ℂ) *
          sG (mobR ρ (β i j) (κ i j) ζ) := by
      intro ζ hζ
      rw [hFdef]; dsimp only
      rw [alphaInv_alphaS hw₀, phiM, sT_sG (by linarith)]
    have hbπ : 0 < b' / π := div_pos hb' hπ
    have hXe : b' / π * X = a' / 2 := by rw [hX]; field_simp
    have hlogX : X ≤ Real.log (ρ / (1 - ρ)) :=
      (Real.le_log_iff_exp_le (div_pos hρ0 hρ')).2 hXρ
    have hlogneg : Real.log ((1 - ρ) / ρ) = -Real.log (ρ / (1 - ρ)) := by
      rw [← Real.log_inv, inv_div]
    have hξ : ∀ ζ : ℂ, ‖ζ‖ ≤ ρ → ‖mobR ρ (β i j) (κ i j) ζ‖ < 1 := fun ζ hζ =>
      lt_of_le_of_lt (norm_mobR_le hρ0 (hβ i j).1 hζ) hρ1
    refine tgt_cross ha' ?_ ?_ ?_ γ hγ h0 h1
    · intro z hz
      rw [hKd] at hz
      obtain ⟨_, ⟨ζ, hζ, rfl⟩, rfl⟩ := hz
      rw [mem_closedBall, dist_zero_right] at hζ
      rw [hFval ζ hζ, (F_parts _ _ _).2]
      have h := abs_lt.1 (abs_im_sG_lt (hξ ζ hζ))
      have e : b' / π * (π / 2) = b' / 2 := by field_simp
      have h1 := mul_lt_mul_of_pos_left h.1 hbπ
      have h2 := mul_lt_mul_of_pos_left h.2 hbπ
      rw [mul_neg, e] at h1
      rw [e] at h2
      constructor <;> linarith
    · intro z hz
      simp only [hAd, mem_image] at hz
      obtain ⟨θ, hθ, rfl⟩ := hz
      rw [hFval _ (norm_rho_exp ρ θ hρ0.le).le, (F_parts _ _ _).1]
      have hval := mob_val_neg_one (κ := κ i j) (hβ i j).1
      have harg : π - 2 * β i j - κ i j = φ i := by simp only [hκd, hβd]; ring
      rw [harg] at hval
      have hn := mobR_near (θ := θ) (φ := φ i) (κ := κ i j) hρ0 (hβ i j).1 (hβ i j).2
      rw [hval, mul_neg_one, sub_neg_eq_add] at hn
      have hn2 : ‖mobR ρ (β i j) (κ i j) ((ρ : ℂ) * Complex.exp (θ * Complex.I)) + ρ‖ ≤
          1 - ρ := by
        refine hn.trans (le_trans ?_ hsmall)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hnear i θ hθ) hL0) hρ0.le
      have := re_sG_le hρ0 hρ1 (hξ _ (norm_rho_exp ρ θ hρ0.le).le) hn2
      rw [hlogneg] at this
      have h1 := mul_le_mul_of_nonneg_left this hbπ.le
      have h2 := mul_le_mul_of_nonneg_left hlogX hbπ.le
      rw [hXe] at h2
      rw [mul_neg] at h1
      linarith
    · intro z hz
      simp only [hBd, mem_image] at hz
      obtain ⟨θ, hθ, rfl⟩ := hz
      rw [hFval _ (norm_rho_exp ρ (-θ) hρ0.le).le, (F_parts _ _ _).1]
      have hval := mob_val_one (κ := κ i j) (hβ i j).1
      have harg : 2 * β i j - κ i j = -φ j := by simp only [hκd]; ring
      rw [harg] at hval
      have hn := mobR_near (θ := -θ) (φ := -φ j) (κ := κ i j) hρ0 (hβ i j).1 (hβ i j).2
      rw [hval, mul_one] at hn
      have hab : |-θ - -φ j| = |θ - φ j| := by
        rw [show -θ - -φ j = -(θ - φ j) by ring, abs_neg]
      rw [hab] at hn
      have hn2 : ‖mobR ρ (β i j) (κ i j) ((ρ : ℂ) * Complex.exp ((-θ : ℝ) * Complex.I)) - ρ‖ ≤
          1 - ρ := by
        refine hn.trans (le_trans ?_ hsmall)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hnear j θ hθ) hL0) hρ0.le
      have := le_re_sG hρ0 hρ1 (hξ _ (norm_rho_exp ρ (-θ) hρ0.le).le) hn2
      have h1 := mul_le_mul_of_nonneg_left this hbπ.le
      have h2 := mul_le_mul_of_nonneg_left hlogX hbπ.le
      rw [hXe] at h2
      linarith

end LQGMetric.DDDF.L12
