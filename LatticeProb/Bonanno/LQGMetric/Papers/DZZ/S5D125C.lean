/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D125C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61G1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117C2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D125B

/-!
# D125 packet P-125 (C): the scale-uniform similarity coupling `DZZSimCoupleScale` (P2-DZZ125)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) (eq-scaling-invariance-approximate), l. 2474, and
the mass comparison `M^{η̌}(A) ≤ e^{(log δ⁻¹)^{0.93}} a^{−2} M^η(θA)`, l. 2501–2503 (proof
l. 2518–2548), in the quantitative form of decision D125 (DEC-125 §2, §4 D): factor `‖a‖`,
`‖a‖ = 2^{−m}`, tail `C e^{−λ²/(C(m+1))}` with `C` independent of `m` and `b`.

* `lgd_sim_upper`: the first half of `lgd_sim_sandwich` (S5D117B), from the one-sided exponent
  bound `F₂ ∘ θ ≤ c + F₁` (proof: that half of the proof of `lgd_sim_sandwich`, copied);
* `dzzSimCoupleScale_of`: the proof of `dzzSimCoupleU_of_along` (S5D117C2), copied and modified:
  `dzz_lemma29_simScale` (S5D125B) in place of `dzz_lemma29_simU`; DZZ L2.7 for the coupled noise
  along `‖a‖ 2^{-j}` by the index shift of `dzzLemma27Along_pow` inlined (constant of
  `dzz_lemma27_uncond`, uniform in `m`); the Wick shift dropped by monotonicity
  (`tildeVar_scale_ge`, S5D125A, instead of the two-sided `tildeVar_two_point_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise WNPush SupTail

section upper

variable {γ c : ℝ} {ζ₁ ζ₂ V₁ V₂ : ℝ → ℂ → ℝ} {s₁ s₂ : ℕ → ℝ} {μ₁ μ₂ : Measure ℂ}

/-- **The upper half of `lgd_sim_sandwich`** (DZZ Lemma 3.8 through a similarity, l. 1229–1232,
with lem-scaling-coupling): if `F₂ ∘ θ ≤ c + F₁` on the closed `K ⊆ 𝕍` (`θ K ⊆ 𝕍`), then
`D^{θK}_{|a|δe^{c/2}}(θx, θy)[M⁽²⁾] ≤ D^K_δ(x, y)[M⁽¹⁾]`. Proof copied from `lgd_sim_sandwich`. -/
theorem lgd_sim_upper (h₁ : IsChaosLimit γ ζ₁ V₁ s₁ μ₁) (h₂ : IsChaosLimit γ ζ₂ V₂ s₂ μ₂)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) {K : Set ℂ} (hK : IsClosed K) (hKV : K ⊆ dzzV)
    (hθK : simMap a b '' K ⊆ dzzV)
    (hpt : ∀ n : ℕ, ∀ z ∈ K,
      γ * ζ₂ (s₂ n) (simMap a b z) - γ ^ 2 / 2 * V₂ (s₂ n) (simMap a b z) ≤
        c + (γ * ζ₁ (s₁ n) z - γ ^ 2 / 2 * V₁ (s₁ n) z))
    (δ : ℝ) (x y : ℂ) :
    lgdDZZ (dzzWall (simMap a b '' K) (dzzWall dzzV μ₂)) (‖a‖ * δ * Real.exp (c / 2))
        (simMap a b x) (simMap a b y) ≤ lgdDZZ (dzzWall K (dzzWall dzzV μ₁)) δ x y := by
  set θ := simMap a b
  set θi := simMap a⁻¹ (-(a⁻¹ * b))
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  set μA := dzzWall K (dzzWall dzzV μ₁)
  set μB := dzzWall (θ '' K) (dzzWall dzzV μ₂)
  set ν := μB.map θi
  have hνθ : ν.map θ = μB := by
    rw [Measure.map_map (continuous_simMap _ _).measurable (continuous_simMap _ _).measurable]
    conv_rhs => rw [← Measure.map_id (μ := μB)]
    congr 1; funext z; exact simMap_right_inv ha b z
  have hν : ∀ S : Set ℂ, MeasurableSet S → ν S = μB (θ '' S) := fun S hS => by
    rw [Measure.map_apply (continuous_simMap _ _).measurable hS, simMap_image_eq_preimage ha b]
  have hball : ∀ (x : ℚ × ℚ) (r : ℝ),
      ν (ball (ratPt x) r) ≤ ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (‖a‖ ^ 2) *
        μA (ball (ratPt x) r) := by
    intro x r
    have hJ0 : ENNReal.ofReal (‖a‖ ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    have he0 : ENNReal.ofReal (Real.exp c) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos c
    have himB : θ '' ball (ratPt x) r = ball (θ (ratPt x)) (‖a‖ * r) := simMap_image_ball ha b _ _
    rw [hν _ measurableSet_ball]
    by_cases hBK : ball (ratPt x) r ⊆ K
    · have hθB : θ '' ball (ratPt x) r ⊆ θ '' K := image_mono hBK
      have hmB : MeasurableSet (θ '' ball (ratPt x) r) := by rw [himB]; exact measurableSet_ball
      simp only [μA, μB]
      rw [dzzWall_eq_of_subset _ hBK measurableSet_ball,
        dzzWall_eq_of_subset _ (hBK.trans hKV) measurableSet_ball,
        dzzWall_eq_of_subset _ hθB hmB, dzzWall_eq_of_subset _ (hθB.trans hθK) hmB]
      exact chaos_sim_ball_ge h₁ h₂ ha b hKV hpt x r hBK
    · simp only [μA]
      rw [dzzWall_eq_top_of_not_subset hK _ isOpen_ball hBK]
      exact le_of_eq_of_le rfl (by rw [ENNReal.mul_top (mul_ne_zero he0 hJ0)]; exact le_top)
  set L := Real.log ‖a‖
  have hL : Real.exp L = ‖a‖ := Real.exp_log hna
  have e4 : ENNReal.ofReal (Real.exp (c + 2 * L)) =
      ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (‖a‖ ^ 2) := by
    rw [show c + 2 * L = c + L + L by ring, Real.exp_add, Real.exp_add, hL, mul_assoc, ← sq,
      ENNReal.ofReal_mul (Real.exp_pos c).le]
  have hB := lgdDZZ_le_of_ball_le (c := c + 2 * L) (fun x r => by rw [e4]; exact hball x r)
    (‖a‖ * δ * Real.exp (c / 2)) x y
  have hθν : ∀ δ' : ℝ, lgdDZZ μB δ' (θ x) (θ y) = lgdDZZ ν δ' x y := fun δ' => by
    rw [← hνθ]; exact lgdDZZ_map_similarity ha b ν δ' x y
  have f2 : ‖a‖ * δ * Real.exp (c / 2) * Real.exp (-(c + 2 * L) / 2) = δ := by
    rw [show -(c + 2 * L) / 2 = -L + -(c / 2) by ring, Real.exp_add, Real.exp_neg, Real.exp_neg,
      hL, show ‖a‖ * δ * Real.exp (c / 2) * (‖a‖⁻¹ * (Real.exp (c / 2))⁻¹) =
        (‖a‖ * ‖a‖⁻¹) * δ * (Real.exp (c / 2) * (Real.exp (c / 2))⁻¹) by ring,
      mul_inv_cancel₀ hna.ne', mul_inv_cancel₀ (Real.exp_pos _).ne', one_mul, mul_one]
  rw [f2] at hB
  rw [hθν]
  exact hB

end upper

/-- **`DZZSimCoupleScale` (decision D125)**: DZZ (eq-scaling-invariance-approximate), l. 2474,
with the mass comparison of l. 2501–2503, for `θ = simMap a b`, `‖a‖ = 2^{−m}`, closed
`K ⊆ 𝕍^ξ`: outside an event of probability `≤ C e^{−λ²/(C(m+1))}` (`C` independent of `m`, `b`),
`D^{θK}_{‖a‖δe^{λ}}(θx, θy)[W₂] ≤ D^K_δ(x, y)[W₁]`. Proof: `dzzSimCoupleU_of_along`, adapted. -/
theorem dzzSimCoupleScale_of {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ)
    (hξ2 : ξ < 1 / 2) {K : Set ℂ} (hK : IsClosed K) (hKξ : K ⊆ dzzVXi ξ) :
    DZZSimCoupleScale γ ξ K := by
  obtain ⟨C29, hC29, h29⟩ := dzz_lemma29_simScale.{0} hξ hξ2
  obtain ⟨C27, hC27, h27⟩ := dzz_lemma27_uncond.{0}
  obtain ⟨Bv, hBv, hvar⟩ := tildeVar_scale_ge hξ (by linarith)
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  set lam0 := γ ^ 2 / 2 * Bv with hlam0
  have hlam00 : 0 ≤ lam0 := by positivity
  set M := max C27 C29 with hM
  have hM0 : 0 < M := lt_max_of_lt_right hC29
  set C := max (9 * γ ^ 2 * M) (3 * M) + lam0 ^ 2 + 3 with hC
  have hC0 : 0 < C := by positivity
  refine ⟨C, hC0, fun m a hma b hθK => ?_⟩
  have hpm : (0 : ℝ) < (1 / 2) ^ m := by positivity
  have ha0 : a ≠ 0 := by
    rintro rfl; rw [norm_zero] at hma; exact hpm.ne' hma.symm
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have ha1 : ‖a‖ ≤ 1 := hma ▸ pow_le_one₀ (by norm_num) (by norm_num)
  have hm1 : (1 : ℝ) ≤ m + 1 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hch : DZZWickChaosAlong ‖a‖ := hma ▸ dzzWickChaosAlong_pow m
  set θ := simMap a b
  have hKbox : K ⊆ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) := hKξ.trans dzzVXi_sub_ferniqueBox
  have hθbox : θ '' K ⊆ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) := hθK.trans dzzVXi_sub_ferniqueBox
  have hKV : K ⊆ dzzV := hKξ.trans (dzzVXi_sub_dzzV ξ)
  have hθKV : θ '' K ⊆ dzzV := hθK.trans (dzzVXi_sub_dzzV ξ)
  have hunit := ferniqueBox_xi_sub_unit hξ.le
  set P' : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := LQGDimension.ExistAsm.stdP.prod
    LQGDimension.ExistAsm.stdP
  have hW := DDDF.isWhiteNoise_fst hW₀
  have hW' := DDDF.isWhiteNoise_snd hW₀
  have hind := DDDF.indepFun_fst_snd_noise hW₀
  obtain ⟨hW₂, htail⟩ := h29 m a ha0 hma b hKbox hθbox hW hW' hind
  set W : WNSpace → (ℕ → ℝ) × (ℕ → ℝ) → ℝ := fun f ω => W₀ f ω.1
  set W₂ := coupledNoise (confHyp_simMap ha0 b) W (fun f ω => W₀ f ω.2)
  refine ⟨(ℕ → ℝ) × (ℕ → ℝ), inferInstance, P', W, W₂, hW, hW₂, fun lam hlam => ?_⟩
  have hP := hW.isProbabilityMeasure
  have hCm : C ≤ C * (m + 1) := le_mul_of_one_le_right hC0.le hm1
  by_cases hl : lam < lam0
  · -- small `λ`: the bound is `≥ 1`
    refine measureReal_le_one.trans ?_
    have hsq : lam ^ 2 / (C * (m + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : lam ^ 2 ≤ lam0 ^ 2 := pow_le_pow_left₀ hlam hl.le 2
      have : 0 ≤ max (9 * γ ^ 2 * M) (3 * M) := le_max_of_le_right (by positivity)
      linarith
    have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
    have h1 : Real.exp (-1) ≤ Real.exp (-lam ^ 2 / (C * (m + 1))) := by
      rw [Real.exp_le_exp, neg_div]; linarith
    have h2 : 1 ≤ 3 * Real.exp (-1) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos 1)]; linarith
    have h3 : (3 : ℝ) ≤ C := by
      have : 0 ≤ max (9 * γ ^ 2 * M) (3 * M) := le_max_of_le_right (by positivity)
      nlinarith [sq_nonneg lam0]
    nlinarith [Real.exp_pos (-1), Real.exp_pos (-lam ^ 2 / (C * (m + 1)))]
  push Not at hl
  -- continuous versions of `η`
  have hp : ∀ j : ℕ, (0 : ℝ) < (1 / 2) ^ j := fun j => by positivity
  choose Y1 hY1c hY1m hY1 using fun j : ℕ => exists_continuous_etaInf hW (hp j)
  choose Y2 hY2c hY2m hY2 using fun j : ℕ => exists_continuous_etaInf hW₂ (mul_pos hna (hp j))
  choose Y3 hY3c hY3m hY3 using fun j : ℕ => exists_continuous_etaInf hW₂ (hp j)
  obtain ⟨Zc, hZcc, hZce, hZch⟩ := hch hW₂ hγ hγ2
  set t := lam / (3 * γ) with ht
  have ht0 : 0 ≤ t := by positivity
  -- the three Gaussian events
  set Z1 : ℕ → ℂ → (ℕ → ℝ) × (ℕ → ℝ) → ℝ := fun j x ω =>
    wickZeta hW ((1 / 2 : ℝ) ^ j) x ω - Y1 j x ω
  set Z3 : ℕ → ℂ → (ℕ → ℝ) × (ℕ → ℝ) → ℝ := fun j x ω =>
    Zc (‖a‖ * (1 / 2 : ℝ) ^ j) x ω - Y2 j x ω
  -- DZZ L2.7 for `W₂` along `‖a‖ 2^{-j} = 2^{-(j+m)}`: the index shift of `dzzLemma27Along_pow`
  set Z3' : ℕ → ℂ → (ℕ → ℝ) × (ℕ → ℝ) → ℝ := fun k x ω =>
    if m ≤ k then Z3 (k - m) x ω else wickZeta hW₂ ((1 / 2 : ℝ) ^ k) x ω - Y3 k x ω
  have hZ3'c : ∀ k ω, Continuous fun x => Z3' k x ω := fun k ω => by
    by_cases hk : m ≤ k
    · simp only [Z3', hk, ↓reduceIte]; exact (hZcc _ ω).sub (hY2c _ ω)
    · simp only [Z3', hk, ↓reduceIte]; exact ((wickZeta_spec hW₂).1 k ω).sub (hY3c k ω)
  have hZ3' : ∀ k x, Z3' k x =ᵐ[P'] fun ω => tildeHInf W₂ ((1 / 2 : ℝ) ^ k) x ω -
      etaInf W₂ ((1 / 2 : ℝ) ^ k) x ω := fun k x => by
    by_cases hk : m ≤ k
    · simp only [Z3', hk, ↓reduceIte]
      have e : ‖a‖ * (1 / 2) ^ (k - m) = (1 / 2 : ℝ) ^ k := by
        rw [hma, ← pow_add, Nat.add_sub_cancel' hk]
      filter_upwards [hZce (k - m) x, hY2 (k - m) x] with ω h1 h2
      simp only [Z3]
      rw [h1, h2, e]
    · simp only [Z3', hk, ↓reduceIte]
      filter_upwards [(wickZeta_spec hW₂).2 k x, hY3 k x] with ω h1 h2
      rw [h1, h2]
  have hP1 := h27 hW Z1 (fun j ω => ((wickZeta_spec hW).1 j ω).sub (hY1c j ω))
    (fun j x => by
      filter_upwards [(wickZeta_spec hW).2 j x, hY1 j x] with ω h1 h2
      simp only [Z1, h1, h2]) t ht0
  have hP3 := h27 hW₂ Z3' hZ3'c hZ3' t ht0
  have hP2 := htail Y1 Y2 hY1c hY2c hY1 hY2 t ht0
  set E1 := {ω | ∃ v ∈ ferniqueBox 0 1, ∃ j : ℕ, t ≤ |Z1 j v ω|}
  set E2 := {ω | ∃ v ∈ K, ∃ j : ℕ, t ≤ |Y1 j v ω - Y2 j (θ v) ω|}
  set E3 := {ω | ∃ v ∈ ferniqueBox 0 1, ∃ j : ℕ, t ≤ |Z3' j v ω|}
  -- the bad event is contained in `E1 ∪ E2 ∪ E3` up to a null set
  have hsub : {ω | ¬ ∀ x ∈ K, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ →
      lgdDZZ (dzzWall (θ '' K) (dzzMuIn γ W₂ ω)) (‖a‖ * δ * Real.exp lam) (θ x) (θ y) ≤
        lgdDZZ (dzzWall K (dzzMuIn γ W ω)) δ x y}
      ≤ᵐ[P'] E1 ∪ E2 ∪ E3 := by
    filter_upwards [ae_isChaosLimit_wickQArea hW hγ hγ2, hZch] with ω h1 h2 hbad
    by_contra hnot
    simp only [mem_union, not_or, E1, E2, E3, mem_ofPred_eq, not_exists, not_and, not_le]
      at hnot
    obtain ⟨⟨n1, n2⟩, n3⟩ := hnot
    refine hbad fun x _ y _ δ _ => ?_
    have hc : ∀ n : ℕ, ∀ z ∈ K,
        γ * Zc (‖a‖ * (1 / 2 : ℝ) ^ n) (θ z) ω -
            γ ^ 2 / 2 * tildeVar (‖a‖ * (1 / 2 : ℝ) ^ n) (θ z) ≤
          2 * lam + (γ * wickZeta hW ((1 / 2 : ℝ) ^ n) z ω -
            γ ^ 2 / 2 * tildeVar ((1 / 2 : ℝ) ^ n) z) := by
      intro n z hz
      have hθz : θ z ∈ θ '' K := mem_image_of_mem θ hz
      have e1 := n1 z (hunit (hKbox hz)) n
      have e2 := n2 z hz n
      have e3 := n3 (θ z) (hunit (hθbox hθz)) (n + m)
      have ev := hvar n ‖a‖ hna ha1 z (θ z) (hKbox hz) (hθbox hθz)
      simp only [Z3', Nat.le_add_left m n, ↓reduceIte, Nat.add_sub_cancel] at e3
      simp only [Z1, Z3] at e1 e3
      have hf : Zc (‖a‖ * (1 / 2 : ℝ) ^ n) (θ z) ω - wickZeta hW ((1 / 2 : ℝ) ^ n) z ω ≤
          3 * t := by
        have a1 := (abs_lt.1 e1).1
        have a2 := (abs_lt.1 e2).1
        have a3 := (abs_lt.1 e3).2
        linarith
      have h3t : γ * (3 * t) = lam := by rw [ht]; field_simp
      have g1 := mul_le_mul_of_nonneg_left hf hγ.le
      have g2 := mul_le_mul_of_nonneg_left ev (by positivity : (0 : ℝ) ≤ γ ^ 2 / 2)
      linarith
    have hs := lgd_sim_upper h1 h2 ha0 b hK hKV hθKV hc δ x y
    rw [show 2 * lam / 2 = lam by ring] at hs
    exact hs
  -- the union bound
  have hexp : ∀ c d : ℝ, 0 < c → c ≤ M → 0 < d → d ≤ M * (m + 1) →
      c * Real.exp (-t ^ 2 / d) ≤ M * Real.exp (-lam ^ 2 / (C * (m + 1))) := by
    intro c d hc hcM hd hdM
    refine mul_le_mul hcM (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hM0.le
    have hC9 : 9 * γ ^ 2 * M ≤ C := by
      have := le_max_left (9 * γ ^ 2 * M) (3 * M)
      have := sq_nonneg lam0
      linarith
    have hd9 : (3 * γ) ^ 2 * d ≤ C * (m + 1) := by
      have h1 := mul_le_mul_of_nonneg_left hdM (by positivity : (0 : ℝ) ≤ 9 * γ ^ 2)
      have h2 := mul_le_mul_of_nonneg_right hC9 (by positivity : (0 : ℝ) ≤ m + 1)
      have e : (3 * γ) ^ 2 * d = 9 * γ ^ 2 * d := by ring
      have e' : 9 * γ ^ 2 * (M * (m + 1)) = 9 * γ ^ 2 * M * (m + 1) := by ring
      linarith
    rw [ht, div_pow, neg_div, neg_div, neg_le_neg_iff, div_div]
    exact div_le_div_of_nonneg_left (sq_nonneg lam) (by positivity) hd9
  have f1 := hexp C27 C27 hC27 (le_max_left _ _) hC27
    ((le_max_left _ _).trans (le_mul_of_one_le_right hM0.le hm1))
  have f2 := hexp C29 (C29 * (m + 1)) hC29 (le_max_right _ _) (by positivity)
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have h3M : 3 * M ≤ C := by
    have := le_max_right (9 * γ ^ 2 * M) (3 * M)
    have := sq_nonneg lam0
    linarith
  calc _ ≤ P'.real (E1 ∪ E2 ∪ E3) :=
        ENNReal.toReal_mono (measure_ne_top P' _) (measure_mono_ae hsub)
    _ ≤ P'.real E1 + P'.real E2 + P'.real E3 :=
        (measureReal_union_le _ _).trans (by linarith [measureReal_union_le (μ := P') E1 E2])
    _ ≤ 3 * M * Real.exp (-lam ^ 2 / (C * (m + 1))) := by linarith
    _ ≤ C * Real.exp (-lam ^ 2 / (C * (m + 1))) :=
        mul_le_mul_of_nonneg_right h3M (Real.exp_pos _).le

end DZZ
end LQGMetric
