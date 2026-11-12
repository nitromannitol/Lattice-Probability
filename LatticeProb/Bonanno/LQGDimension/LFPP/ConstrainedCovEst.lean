/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.ConstrainedCovEst at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.ConstrainedCovGeom

/-!
# Covariance estimates for the constrained configuration

Interfaces to `TwoScaleCovBound` (same-weight pairs of edge-indexed combinations), crude bounds
for weight perturbations, and the resulting error estimates:

* the replacement of the constrained polygon by the displaced graph costs `O(δ^{3/2})`
  (`clause1_err`);
* the Hölder-`1/2` modulus in the parameters (`clause3_bound`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.ConstrCov

open Blueprint.Draft GraphCov

/-! ## Good combinations and the crude pairing bound -/

/-- All edges of `X` have endpoints of norm at most `R` and length at least `ℓ`. -/
def GoodC (X : SegComb) (ℓ R : ℝ) : Prop :=
  ∀ p ∈ X, ‖p.2.1‖ ≤ R ∧ ‖p.2.2‖ ≤ R ∧ ℓ ≤ ‖p.2.2 - p.2.1‖

lemma goodC_sub {a b : SegComb} {ℓ R : ℝ} (ha : GoodC a ℓ R) (hb : GoodC b ℓ R) :
    GoodC (a.sub b) ℓ R := by
  intro p hp
  unfold SegComb.sub at hp
  rcases List.mem_append.1 hp with hp | hp
  · exact ha p hp
  · rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hb q hq

lemma goodC_wc {M : ℕ} {W : ℕ → ℝ} {V : ℕ → ℂ} {ℓ R : ℝ} (hV : ∀ i ≤ M, ‖V i‖ ≤ R)
    (hE : ∀ i < M, ℓ ≤ ‖V (i + 1) - V i‖) : GoodC (wc M W V) ℓ R := by
  intro p hp
  unfold wc at hp
  rw [List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  have hi' := List.mem_range.1 hi
  exact ⟨hV i hi'.le, hV (i + 1) hi', hE i hi'⟩

/-- The crude pairing constant for segments in the disc of radius `R` with length `≥ ℓ`. -/
def Kseg (R ℓ : ℝ) : ℝ :=
  2 * R + (|Real.log ℓ| + |Real.log (2 * R)|) +
    ∫ u in (-(2 * R / ℓ + 1))..(2 * R / ℓ + 1), |Real.log u|

lemma Kseg_nonneg {R ℓ : ℝ} (hR : 0 ≤ R) (hℓ : 0 < ℓ) : 0 ≤ Kseg R ℓ := by
  unfold Kseg
  have : 0 ≤ ∫ u in (-(2 * R / ℓ + 1))..(2 * R / ℓ + 1), |Real.log u| :=
    intervalIntegral.integral_nonneg (by have : 0 ≤ 2 * R / ℓ := by positivity
                                         linarith) fun _ _ => abs_nonneg _
  positivity

lemma segLogPair_good {a b a' b' : ℂ} {R ℓ : ℝ} (hℓ : 0 < ℓ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R)
    (ha' : ‖a'‖ ≤ R) (hb' : ‖b'‖ ≤ R) (hlen : ℓ ≤ ‖b' - a'‖) :
    |segLogPair a b a' b'| ≤ Kseg R ℓ := by
  have hne : a' ≠ b' := by
    intro h; rw [h, sub_self, norm_zero] at hlen; linarith
  exact abs_segLogPair_le hne hℓ hlen ha hb ha' hb'

lemma abs_logCov_wc_sub_left_good {M : ℕ} {W W' : ℕ → ℝ} {V : ℕ → ℂ} {X : SegComb}
    {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hV : ∀ i ≤ M, ‖V i‖ ≤ R) (hX : GoodC X ℓ R) :
    |((wc M W V).sub (wc M W' V)).logCov X| ≤
      (∑ i ∈ Finset.range M, |W i - W' i|) * tv X * Kseg R ℓ :=
  abs_logCov_wc_sub_left_le (Kseg_nonneg hR hℓ) fun i hi p' hp' =>
    segLogPair_good hℓ (hV i hi.le) (hV (i + 1) hi) (hX p' hp').1 (hX p' hp').2.1
      (hX p' hp').2.2

lemma abs_logCov_wc_sub_right_good {X : SegComb} {M : ℕ} {W W' : ℕ → ℝ} {V : ℕ → ℂ}
    {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hV : ∀ i ≤ M, ‖V i‖ ≤ R)
    (hE : ∀ i < M, ℓ ≤ ‖V (i + 1) - V i‖) (hX : GoodC X ℓ R) :
    |X.logCov ((wc M W V).sub (wc M W' V))| ≤
      tv X * (∑ i ∈ Finset.range M, |W i - W' i|) * Kseg R ℓ :=
  abs_logCov_wc_sub_right_le (Kseg_nonneg hR hℓ) fun p hp j hj =>
    segLogPair_good hℓ (hX p hp).1 (hX p hp).2.1 (hV j hj.le) (hV (j + 1) hj) (hE j hj)

/-! ## Interface to `TwoScaleCovBound` -/

lemma growth_helper {M : ℕ} (hM : 0 < M) {W : ℕ → ℝ} {V : ℕ → ℂ} (hW0 : ∀ i < M, 0 ≤ W i)
    (hsum : ∑ i ∈ Finset.range M, W i = 1) (hW : ∀ i < M, W i ≤ 5 / 4 / (M : ℝ))
    (hE : ∀ i < M, 7 / 8 / (M : ℝ) ≤ ‖V (i + 1) - V i‖) :
    GrowthBound (wc M W V).toMeasure (max 1 (2 * 2 * M)) 1 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  refine growth_wc (by norm_num) hW0 hsum.le (fun i hi => ?_) (fun i hi => ?_)
  · intro h
    have := hE i hi
    rw [h, sub_self, norm_zero] at this
    have : 0 < 7 / 8 / (M : ℝ) := by positivity
    linarith
  · have h1 := hW i hi
    have h2 := hE i hi
    have : 5 / 4 / (M : ℝ) ≤ 2 * (7 / 8 / (M : ℝ)) := by
      rw [← mul_div_assoc]; gcongr; norm_num
    linarith

/-- `TwoScaleCovBound` for pairs of edge-indexed combinations with the same weights. -/
lemma twoScale_wc (hL31 : TwoScaleCovBound) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (M₁ M₂ : ℕ) (W₁ W₂ : ℕ → ℝ) (V₁ V₁' V₂ V₂' : ℕ → ℂ) (L u v : ℝ),
      0 ≤ L → 0 ≤ u → 0 ≤ v →
      (wc M₁ W₁ V₁).IsProb → (wc M₁ W₁ V₁').IsProb → (wc M₂ W₂ V₂).IsProb →
      (wc M₂ W₂ V₂').IsProb →
      GrowthBound (wc M₁ W₁ V₁).toMeasure L 1 → GrowthBound (wc M₁ W₁ V₁').toMeasure L 1 →
      (∀ i ≤ M₁, ‖V₁ i - V₁' i‖ ≤ u) → (∀ i ≤ M₂, ‖V₂ i - V₂' i‖ ≤ v) →
      |((wc M₁ W₁ V₁).sub (wc M₁ W₁ V₁')).logCov ((wc M₂ W₂ V₂).sub (wc M₂ W₂ V₂'))| ≤
        C * L * Real.sqrt (u * v) := by
  obtain ⟨C, hC⟩ := hL31
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro M₁ M₂ W₁ W₂ V₁ V₁' V₂ V₂' L u v hL hu hv h1 h2 h3 h4 hg1 hg2 hc1 hc2
  have := (hC _ _ _ _ L 1 u v h1 h2 h3 h4 one_pos hu hv hg1 hg2 (coupled_wc hc1)
    (coupled_wc hc2)).1
  rw [div_one] at this
  refine this.trans ?_
  gcongr
  exact le_max_left _ _

lemma growth_mono {μ : Measure ℂ} {L L' R : ℝ} (hR : 0 < R) (h : GrowthBound μ L R)
    (hL : L ≤ L') : GrowthBound μ L' R := by
  intro z t ht
  refine (h z t ht).trans ?_
  have : 0 ≤ min 1 (t / R) := le_min zero_le_one (by positivity)
  exact mul_le_mul_of_nonneg_right hL this

lemma sqrt_mul_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a * b) ≤ a + b := by
  rw [show a + b = Real.sqrt ((a + b) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
  exact Real.sqrt_le_sqrt (by nlinarith)

lemma sum_const_inv (M : ℕ) (hM : 0 < M) :
    ∑ _i ∈ Finset.range M, 1 / (M : ℝ) = 1 := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-! ## Clause 1: replacing the polygon by the displaced graph -/

section Clause1

variable {n : ℕ} {B A δ : ℝ} {f : ℝ → ℝ} {p₀ p₁ : ℂ}

/-- The standing facts about one configuration, for small `δ`. -/
structure CfgFacts (n : ℕ) (B A δ : ℝ) (f : ℝ → ℝ) (p₀ p₁ : ℂ) : Prop where
  hne : xp δ p₀ ≠ yp δ p₁
  uW0 : ∀ i, 0 ≤ uW (16 ^ n) δ f i
  uWs : ∑ i ∈ Finset.range (16 ^ n), uW (16 ^ n) δ f i = 1
  uWη : ∀ i < 16 ^ n, |uW (16 ^ n) δ f i - 1 / ((16 ^ n : ℕ) : ℝ)| ≤ etaS n B δ
  uWle : ∀ i < 16 ^ n, uW (16 ^ n) δ f i ≤ 5 / 4 / ((16 ^ n : ℕ) : ℝ)
  cvB : ∀ i : ℕ, i ≤ 16 ^ n → ‖cv (16 ^ n) δ p₀ p₁ i‖ ≤ 3
  zvB : ∀ i : ℕ, i ≤ 16 ^ n → ‖zv (16 ^ n) δ f p₀ p₁ i‖ ≤ 3
  ZvB : ∀ i : ℕ, i ≤ 16 ^ n → ‖Zv (16 ^ n) δ f p₀ p₁ i‖ ≤ 3
  cvE : ∀ i < 16 ^ n, 7 / 8 / ((16 ^ n : ℕ) : ℝ) ≤
    ‖cv (16 ^ n) δ p₀ p₁ (i + 1) - cv (16 ^ n) δ p₀ p₁ i‖
  zvE : ∀ i < 16 ^ n, 7 / 8 / ((16 ^ n : ℕ) : ℝ) ≤
    ‖zv (16 ^ n) δ f p₀ p₁ (i + 1) - zv (16 ^ n) δ f p₀ p₁ i‖
  ZvE : ∀ i < 16 ^ n, 7 / 8 / ((16 ^ n : ℕ) : ℝ) ≤
    ‖Zv (16 ^ n) δ f p₀ p₁ (i + 1) - Zv (16 ^ n) δ f p₀ p₁ i‖
  czv : ∀ i : ℕ, i ≤ 16 ^ n → ‖cv (16 ^ n) δ p₀ p₁ i - zv (16 ^ n) δ f p₀ p₁ i‖ ≤ δ * B
  zZv : ∀ i : ℕ, i ≤ 16 ^ n → ‖zv (16 ^ n) δ f p₀ p₁ i - Zv (16 ^ n) δ f p₀ p₁ i‖ ≤ c₁ n B A * δ ^ 2

lemma cfgFacts (hs : Small n B A δ) (hf : f ∈ V n) (hfB : ∀ x, |f x| ≤ B) (h0 : ‖p₀‖ ≤ A)
    (h1 : ‖p₁‖ ≤ A) : CfgFacts n B A δ f p₀ p₁ := by
  obtain ⟨u0, us, uη⟩ := uW_facts hs hf hfB
  exact ⟨xp_ne_yp hs h0 h1, u0, us, uη, fun i hi => uW_le hs hf hfB hi,
    fun i hi => norm_cv_le hs h0 h1 hi, fun i hi => norm_zv_le hs h0 h1 hfB hi,
    fun i hi => norm_Zv_le hs hf hfB h0 h1 hi, fun i _ => cv_edge hs h0 h1 i,
    fun i _ => zv_edge hs h0 h1 i, fun i hi => Zv_edge hs hf hfB h0 h1 hi,
    fun i _ => norm_cv_sub_zv hs hfB i, fun i hi => norm_zv_sub_Zv hs hf hfB h0 h1 hi⟩

lemma ell_le (n : ℕ) : 1 / (2 * ((16 ^ n : ℕ) : ℝ)) ≤ 7 / 8 / ((16 ^ n : ℕ) : ℝ) := by
  have hM : (0 : ℝ) < ((16 ^ n : ℕ) : ℝ) := by exact_mod_cast M_pos n
  rw [div_le_div_iff₀ (by positivity) hM]
  nlinarith

end Clause1

lemma nondeg_of_good {X : SegComb} {ℓ R : ℝ} (hℓ : 0 < ℓ) (h : GoodC X ℓ R) :
    ∀ p ∈ X, p.2.1 ≠ p.2.2 := by
  intro p hp he
  have := (h p hp).2.2
  rw [he, sub_self, norm_zero] at this
  linarith

section Clause1b

variable {n : ℕ} {B A δ : ℝ} {f : ℝ → ℝ} {p₀ p₁ : ℂ}

lemma CfgFacts.good_cv (cf : CfgFacts n B A δ f p₀ p₁) (W : ℕ → ℝ) :
    GoodC (wc (16 ^ n) W (cv (16 ^ n) δ p₀ p₁)) (1 / (2 * ((16 ^ n : ℕ) : ℝ))) 3 :=
  goodC_wc cf.cvB fun i hi => (ell_le n).trans (cf.cvE i hi)

lemma CfgFacts.good_zv (cf : CfgFacts n B A δ f p₀ p₁) (W : ℕ → ℝ) :
    GoodC (wc (16 ^ n) W (zv (16 ^ n) δ f p₀ p₁)) (1 / (2 * ((16 ^ n : ℕ) : ℝ))) 3 :=
  goodC_wc cf.zvB fun i hi => (ell_le n).trans (cf.zvE i hi)

lemma CfgFacts.good_Zv (cf : CfgFacts n B A δ f p₀ p₁) (W : ℕ → ℝ) :
    GoodC (wc (16 ^ n) W (Zv (16 ^ n) δ f p₀ p₁)) (1 / (2 * ((16 ^ n : ℕ) : ℝ))) 3 :=
  goodC_wc cf.ZvB fun i hi => (ell_le n).trans (cf.ZvE i hi)

lemma CfgFacts.sum_abs_uW (cf : CfgFacts n B A δ f p₀ p₁) :
    ∑ i ∈ Finset.range (16 ^ n), |1 / ((16 ^ n : ℕ) : ℝ) - uW (16 ^ n) δ f i| ≤
      ((16 ^ n : ℕ) : ℝ) * etaS n B δ := by
  calc _ ≤ ∑ i ∈ Finset.range (16 ^ n), etaS n B δ := Finset.sum_le_sum fun i hi => by
        rw [abs_sub_comm]; exact cf.uWη i (Finset.mem_range.1 hi)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma CfgFacts.prob_uW (cf : CfgFacts n B A δ f p₀ p₁) (V : ℕ → ℂ) :
    (wc (16 ^ n) (uW (16 ^ n) δ f) V).IsProb :=
  isProb_wc V (fun i _ => cf.uW0 i) cf.uWs

lemma prob_unif (n : ℕ) (V : ℕ → ℂ) :
    (wc (16 ^ n) (fun _ => 1 / ((16 ^ n : ℕ) : ℝ)) V).IsProb :=
  isProb_wc V (fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _)) (sum_const_inv _ (M_pos n))

lemma tv_uW (cf : CfgFacts n B A δ f p₀ p₁) (V : ℕ → ℂ) :
    tv (wc (16 ^ n) (uW (16 ^ n) δ f) V) = 1 := tv_wc_prob V (fun i _ => cf.uW0 i) cf.uWs

lemma tv_unif (n : ℕ) (V : ℕ → ℂ) :
    tv (wc (16 ^ n) (fun _ => 1 / ((16 ^ n : ℕ) : ℝ)) V) = 1 :=
  tv_wc_prob V (fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _)) (sum_const_inv _ (M_pos n))

lemma CfgFacts.growth_uW_zv (cf : CfgFacts n B A δ f p₀ p₁) :
    GrowthBound (wc (16 ^ n) (uW (16 ^ n) δ f) (zv (16 ^ n) δ f p₀ p₁)).toMeasure
      (max 1 (2 * 2 * ((16 ^ n : ℕ) : ℝ))) 1 :=
  growth_helper (M_pos n) (fun i _ => cf.uW0 i) cf.uWs cf.uWle cf.zvE

lemma CfgFacts.growth_uW_Zv (cf : CfgFacts n B A δ f p₀ p₁) :
    GrowthBound (wc (16 ^ n) (uW (16 ^ n) δ f) (Zv (16 ^ n) δ f p₀ p₁)).toMeasure
      (max 1 (2 * 2 * ((16 ^ n : ℕ) : ℝ))) 1 :=
  growth_helper (M_pos n) (fun i _ => cf.uW0 i) cf.uWs cf.uWle cf.ZvE

lemma unif_le (n : ℕ) : ∀ i < 16 ^ n, 1 / ((16 ^ n : ℕ) : ℝ) ≤ 5 / 4 / ((16 ^ n : ℕ) : ℝ) :=
  fun i _ => by gcongr; norm_num

lemma CfgFacts.growth_unif_cv (cf : CfgFacts n B A δ f p₀ p₁) :
    GrowthBound (wc (16 ^ n) (fun _ => 1 / ((16 ^ n : ℕ) : ℝ)) (cv (16 ^ n) δ p₀ p₁)).toMeasure
      (max 1 (2 * 2 * ((16 ^ n : ℕ) : ℝ))) 1 :=
  growth_helper (M_pos n) (fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _)) (sum_const_inv _ (M_pos n)) (unif_le n)
    cf.cvE

lemma CfgFacts.growth_unif_zv (cf : CfgFacts n B A δ f p₀ p₁) :
    GrowthBound (wc (16 ^ n) (fun _ => 1 / ((16 ^ n : ℕ) : ℝ)) (zv (16 ^ n) δ f p₀ p₁)).toMeasure
      (max 1 (2 * 2 * ((16 ^ n : ℕ) : ℝ))) 1 :=
  growth_helper (M_pos n) (fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _)) (sum_const_inv _ (M_pos n)) (unif_le n)
    cf.zvE

end Clause1b

/-- **Clause 1, error part.**  Replacing the constrained polygon by the displaced graph (and the
one-edge chord by the chord cut into `M` edges) changes the covariance by `O(δ^{3/2})`. -/
theorem clause1_err (hL31 : TwoScaleCovBound) (n : ℕ) (B A : ℝ) : ∃ K₁ : ℝ, ∀ δ : ℝ,
    Small n B A δ → ∀ f f' : ℝ → ℝ, ∀ p₀ p₁ p₀' p₁' : ℂ, f ∈ V n → f' ∈ V n →
    (∀ x, |f x| ≤ B) → (∀ x, |f' x| ≤ B) → ‖p₀‖ ≤ A → ‖p₁‖ ≤ A → ‖p₀'‖ ≤ A → ‖p₁'‖ ≤ A →
    |(cfgComb (constrCfg (16 ^ n) δ f p₀ p₁)).logCov
        (cfgComb (constrCfg (16 ^ n) δ f' p₀' p₁')) -
      ((chordM (16 ^ n) (xp δ p₀) (yp δ p₁)).sub
          (wc (16 ^ n) (fun _ => 1 / ((16 ^ n : ℕ) : ℝ)) (zv (16 ^ n) δ f p₀ p₁))).logCov
        ((chordM (16 ^ n) (xp δ p₀') (yp δ p₁')).sub
          (wc (16 ^ n) (fun _ => 1 / ((16 ^ n : ℕ) : ℝ)) (zv (16 ^ n) δ f' p₀' p₁')))| ≤
      K₁ * (δ ^ 2 + δ * Real.sqrt δ) := by
  obtain ⟨C, hC0, hC⟩ := twoScale_wc hL31
  have hM : 0 < 16 ^ n := M_pos n
  have hMr : (0 : ℝ) < ((16 ^ n : ℕ) : ℝ) := by exact_mod_cast hM
  set Mr : ℝ := ((16 ^ n : ℕ) : ℝ) with hMr_def
  set ℓ : ℝ := 1 / (2 * Mr) with hℓ
  have hℓ0 : 0 < ℓ := by rw [hℓ]; positivity
  set K := Kseg 3 ℓ with hK
  have hK0 : 0 ≤ K := Kseg_nonneg (by norm_num) hℓ0
  set Lg : ℝ := max 1 (2 * 2 * Mr) with hLg
  have hLg0 : 0 ≤ Lg := le_trans zero_le_one (le_max_left _ _)
  set cc := c₁ n B A with hcc_def
  set η2 : ℝ := (2 * B * (16 : ℝ) ^ n) ^ 2 with hη2
  refine ⟨6 * Mr * η2 * K + C * Lg * cc + 2 * (C * Lg * Real.sqrt (cc * B)), ?_⟩
  intro δ hs f f' p₀ p₁ p₀' p₁' hf hf' hfB hf'B h0 h1 h0' h1'
  have hB : 0 ≤ B := (abs_nonneg _).trans (hfB 0)
  have hA : 0 ≤ A := (norm_nonneg _).trans h0
  have hδ := hs.pos
  have cf := cfgFacts hs hf hfB h0 h1
  have cf' := cfgFacts hs hf' hf'B h0' h1'
  have hcc : 0 ≤ cc := by rw [hcc_def]; unfold c₁; positivity
  have hη : etaS n B δ = η2 * δ ^ 2 := by unfold etaS; rw [hη2]; ring
  have hη2_0 : 0 ≤ η2 := sq_nonneg _
  -- the pieces
  set D := wc (16 ^ n) (fun _ => 1 / Mr) (zv (16 ^ n) δ f p₀ p₁) with hD
  set D' := wc (16 ^ n) (fun _ => 1 / Mr) (zv (16 ^ n) δ f' p₀' p₁') with hD'
  set Dt := wc (16 ^ n) (uW (16 ^ n) δ f) (zv (16 ^ n) δ f p₀ p₁) with hDt
  set Dt' := wc (16 ^ n) (uW (16 ^ n) δ f') (zv (16 ^ n) δ f' p₀' p₁') with hDt'
  set P := wc (16 ^ n) (uW (16 ^ n) δ f) (Zv (16 ^ n) δ f p₀ p₁) with hP
  set P' := wc (16 ^ n) (uW (16 ^ n) δ f') (Zv (16 ^ n) δ f' p₀' p₁') with hP'
  have hchM : chordM (16 ^ n) (xp δ p₀) (yp δ p₁) =
      wc (16 ^ n) (fun _ => 1 / Mr) (cv (16 ^ n) δ p₀ p₁) := rfl
  have hchM' : chordM (16 ^ n) (xp δ p₀') (yp δ p₁') =
      wc (16 ^ n) (fun _ => 1 / Mr) (cv (16 ^ n) δ p₀' p₁') := rfl
  set chM := wc (16 ^ n) (fun _ => 1 / Mr) (cv (16 ^ n) δ p₀ p₁) with hchMd
  set chM' := wc (16 ^ n) (fun _ => 1 / Mr) (cv (16 ^ n) δ p₀' p₁') with hchMd'
  rw [hchM, hchM']
  -- goodness
  have gP' : GoodC P' ℓ 3 := cf'.good_Zv _
  have gP : GoodC P ℓ 3 := cf.good_Zv _
  have gchM' : GoodC chM' ℓ 3 := cf'.good_cv _
  have gchM : GoodC chM ℓ 3 := cf.good_cv _
  have gD : GoodC D ℓ 3 := cf.good_zv _
  have gDt : GoodC Dt ℓ 3 := cf.good_zv _
  -- subdivision of the one-edge chords
  have hsubL : ∀ X : SegComb, (∀ p ∈ X, p.2.1 ≠ p.2.2) →
      SegComb.logCov [((1 : ℝ), xp δ p₀, yp δ p₁)] X = chM.logCov X :=
    fun X hX => logCov_chord_left hM _ _ X hX
  have hsubR : ∀ X : SegComb, X.logCov [((1 : ℝ), xp δ p₀', yp δ p₁')] = X.logCov chM' :=
    fun X => logCov_chord_right hM X _ _ cf'.hne
  have hch1' : ∀ p ∈ [((1 : ℝ), xp δ p₀', yp δ p₁')], p.2.1 ≠ p.2.2 := by
    intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact cf'.hne
  -- the decomposition
  have hdec : (cfgComb (constrCfg (16 ^ n) δ f p₀ p₁)).logCov
        (cfgComb (constrCfg (16 ^ n) δ f' p₀' p₁')) - (chM.sub D).logCov (chM'.sub D') =
      (D.sub Dt).logCov (chM'.sub P') + (Dt.sub P).logCov (chM'.sub D') +
      (Dt.sub P).logCov (D'.sub Dt') + (Dt.sub P).logCov (Dt'.sub P') +
      (chM.sub D).logCov (D'.sub Dt') + (chM.sub D).logCov (Dt'.sub P') := by
    rw [cfgComb_eq _ _ _ _ _ cf.hne, cfgComb_eq _ _ _ _ _ cf'.hne, ← hP, ← hP']
    simp only [logCov_sub_sub]
    rw [hsubL _ hch1', hsubR chM, hsubL P' (nondeg_of_good hℓ0 gP'), hsubR P]
    ring
  rw [hdec]
  -- the six bounds
  have hMη : ∑ i ∈ Finset.range (16 ^ n), |1 / Mr - uW (16 ^ n) δ f i| ≤ Mr * etaS n B δ :=
    cf.sum_abs_uW
  have hMη' : ∑ i ∈ Finset.range (16 ^ n), |1 / Mr - uW (16 ^ n) δ f' i| ≤ Mr * etaS n B δ :=
    cf'.sum_abs_uW
  have tvchM' : tv (chM'.sub P') = 2 := by
    rw [tv_sub, tv_unif, tv_uW cf']; norm_num
  have tvDtP : tv (Dt.sub P) = 2 := by rw [tv_sub, tv_uW cf, tv_uW cf]; norm_num
  have tvchD : tv (chM.sub D) = 2 := by rw [tv_sub, tv_unif, tv_unif]; norm_num
  have hT1 : |(D.sub Dt).logCov (chM'.sub P')| ≤ (Mr * etaS n B δ) * 2 * K := by
    have := abs_logCov_wc_sub_left_good (W := fun _ => 1 / Mr) (W' := uW (16 ^ n) δ f)
      hℓ0 (by norm_num) cf.zvB (goodC_sub gchM' gP')
    rw [tvchM'] at this
    refine this.trans ?_
    gcongr
  have hT3 : |(Dt.sub P).logCov (D'.sub Dt')| ≤ 2 * (Mr * etaS n B δ) * K := by
    have := abs_logCov_wc_sub_right_good (W := fun _ => 1 / Mr) (W' := uW (16 ^ n) δ f')
      hℓ0 (by norm_num) cf'.zvB (fun i hi => (ell_le n).trans (cf'.zvE i hi))
      (goodC_sub gDt gP)
    rw [tvDtP] at this
    refine this.trans ?_
    gcongr
  have hT5 : |(chM.sub D).logCov (D'.sub Dt')| ≤ 2 * (Mr * etaS n B δ) * K := by
    have := abs_logCov_wc_sub_right_good (W := fun _ => 1 / Mr) (W' := uW (16 ^ n) δ f')
      hℓ0 (by norm_num) cf'.zvB (fun i hi => (ell_le n).trans (cf'.zvE i hi))
      (goodC_sub gchM gD)
    rw [tvchD] at this
    refine this.trans ?_
    gcongr
  have hT2 : |(Dt.sub P).logCov (chM'.sub D')| ≤ C * Lg * Real.sqrt (cc * δ ^ 2 * (δ * B)) :=
    hC _ _ _ _ _ _ _ _ Lg (cc * δ ^ 2) (δ * B) hLg0 (by positivity) (by positivity)
      (cf.prob_uW _) (cf.prob_uW _) (prob_unif n _) (prob_unif n _) cf.growth_uW_zv
      cf.growth_uW_Zv cf.zZv cf'.czv
  have hT4 : |(Dt.sub P).logCov (Dt'.sub P')| ≤
      C * Lg * Real.sqrt (cc * δ ^ 2 * (cc * δ ^ 2)) :=
    hC _ _ _ _ _ _ _ _ Lg (cc * δ ^ 2) (cc * δ ^ 2) hLg0 (by positivity) (by positivity)
      (cf.prob_uW _) (cf.prob_uW _) (cf'.prob_uW _) (cf'.prob_uW _) cf.growth_uW_zv
      cf.growth_uW_Zv cf.zZv cf'.zZv
  have hT6 : |(chM.sub D).logCov (Dt'.sub P')| ≤ C * Lg * Real.sqrt (δ * B * (cc * δ ^ 2)) :=
    hC _ _ _ _ _ _ _ _ Lg (δ * B) (cc * δ ^ 2) hLg0 (by positivity) (by positivity)
      (prob_unif n _) (prob_unif n _) (cf'.prob_uW _) (cf'.prob_uW _) cf.growth_unif_cv
      cf.growth_unif_zv cf.czv cf'.zZv
  have hs1 : Real.sqrt (cc * δ ^ 2 * (δ * B)) = Real.sqrt (cc * B) * (δ * Real.sqrt δ) := by
    rw [show cc * δ ^ 2 * (δ * B) = (cc * B) * (δ ^ 2 * δ) by ring,
      Real.sqrt_mul (mul_nonneg hcc hB), Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ.le]
  have hs2 : Real.sqrt (δ * B * (cc * δ ^ 2)) = Real.sqrt (cc * B) * (δ * Real.sqrt δ) := by
    rw [show δ * B * (cc * δ ^ 2) = cc * δ ^ 2 * (δ * B) by ring, hs1]
  have hs3 : Real.sqrt (cc * δ ^ 2 * (cc * δ ^ 2)) = cc * δ ^ 2 :=
    Real.sqrt_mul_self (mul_nonneg hcc (sq_nonneg δ))
  rw [hs1] at hT2
  rw [hs2] at hT6
  rw [hs3] at hT4
  rw [hη] at hT1 hT3 hT5
  have hsq : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  have hCL : 0 ≤ C * Lg := mul_nonneg hC0 hLg0
  have hsq2 : 0 ≤ Real.sqrt (cc * B) := Real.sqrt_nonneg _
  calc _ ≤ |(D.sub Dt).logCov (chM'.sub P')| + |(Dt.sub P).logCov (chM'.sub D')| +
        |(Dt.sub P).logCov (D'.sub Dt')| + |(Dt.sub P).logCov (Dt'.sub P')| +
        |(chM.sub D).logCov (D'.sub Dt')| + |(chM.sub D).logCov (Dt'.sub P')| := by
        have t1 := abs_add_le ((D.sub Dt).logCov (chM'.sub P') + (Dt.sub P).logCov (chM'.sub D') +
          (Dt.sub P).logCov (D'.sub Dt') + (Dt.sub P).logCov (Dt'.sub P') +
          (chM.sub D).logCov (D'.sub Dt')) ((chM.sub D).logCov (Dt'.sub P'))
        have t2 := abs_add_le ((D.sub Dt).logCov (chM'.sub P') + (Dt.sub P).logCov (chM'.sub D') +
          (Dt.sub P).logCov (D'.sub Dt') + (Dt.sub P).logCov (Dt'.sub P'))
          ((chM.sub D).logCov (D'.sub Dt'))
        have t3 := abs_add_le ((D.sub Dt).logCov (chM'.sub P') + (Dt.sub P).logCov (chM'.sub D') +
          (Dt.sub P).logCov (D'.sub Dt')) ((Dt.sub P).logCov (Dt'.sub P'))
        have t4 := abs_add_le ((D.sub Dt).logCov (chM'.sub P') + (Dt.sub P).logCov (chM'.sub D'))
          ((Dt.sub P).logCov (D'.sub Dt'))
        have t5 := abs_add_le ((D.sub Dt).logCov (chM'.sub P')) ((Dt.sub P).logCov (chM'.sub D'))
        linarith
    _ ≤ Mr * (η2 * δ ^ 2) * 2 * K + C * Lg * (Real.sqrt (cc * B) * (δ * Real.sqrt δ)) +
        2 * (Mr * (η2 * δ ^ 2)) * K + C * Lg * (cc * δ ^ 2) + 2 * (Mr * (η2 * δ ^ 2)) * K +
        C * Lg * (Real.sqrt (cc * B) * (δ * Real.sqrt δ)) := by linarith
    _ ≤ (6 * Mr * η2 * K + C * Lg * cc + 2 * (C * Lg * Real.sqrt (cc * B))) *
        (δ ^ 2 + δ * Real.sqrt δ) := by
        have a1 : 0 ≤ δ ^ 2 := sq_nonneg δ
        have a2 : 0 ≤ δ * Real.sqrt δ := mul_nonneg hδ.le hsq
        have b1 : 0 ≤ 6 * Mr * η2 * K := by positivity
        have b2 : 0 ≤ C * Lg * cc := mul_nonneg hCL hcc
        have b3 : 0 ≤ C * Lg * Real.sqrt (cc * B) := mul_nonneg hCL hsq2
        linarith [mul_nonneg b1 a2, mul_nonneg b2 a2, mul_nonneg b3 a1]

/-! ## Clause 3: the modulus -/

lemma le_iSup_Icc {g : ℝ → ℝ} {C : ℝ} (hg : ∀ x, g x ≤ C) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    g x ≤ ⨆ y ∈ Icc (0:ℝ) 1, g y := by
  have hb : BddAbove (Set.range fun y => ⨆ (_ : y ∈ Icc (0:ℝ) 1), g y) := by
    refine ⟨max C 0, ?_⟩
    rintro _ ⟨y, rfl⟩
    by_cases hy : y ∈ Icc (0:ℝ) 1
    · show ⨆ (_ : y ∈ Icc (0:ℝ) 1), g y ≤ max C 0
      rw [ciSup_pos hy]
      exact (hg y).trans (le_max_left _ _)
    · have : IsEmpty (y ∈ Icc (0:ℝ) 1) := ⟨hy⟩
      show ⨆ (_ : y ∈ Icc (0:ℝ) 1), g y ≤ max C 0
      rw [Real.iSup_of_isEmpty]
      exact le_max_right _ _
  refine le_trans ?_ (le_ciSup hb x)
  rw [ciSup_pos hx]

/-- The one-edge chord as an edge-indexed combination. -/
def ch1 (x y : ℂ) : SegComb := wc 1 (fun _ => 1) (fun i : ℕ => chordPt x y (i : ℝ))

lemma ch1_eq (x y : ℂ) : ch1 x y = [((1 : ℝ), x, y)] := by
  simp [ch1, wc, chordPt]

section Clause3

variable {n : ℕ} {B A δ : ℝ} {f f' : ℝ → ℝ} {p₀ p₁ p₀' p₁' : ℂ}

lemma norm_Zv_sub_Zv (hs : Small n B A δ) (hf : f ∈ V n) (_hf' : f' ∈ V n)
    (hfB : ∀ x, |f x| ≤ B) (hf'B : ∀ x, |f' x| ≤ B) (_h0 : ‖p₀‖ ≤ A) (_h1 : ‖p₁‖ ≤ A)
    (h0' : ‖p₀'‖ ≤ A) (h1' : ‖p₁'‖ ≤ A) {d : ℝ}
    (hd : ∀ i : ℕ, i ≤ 16 ^ n → |f ((i : ℝ) / ((16 ^ n : ℕ) : ℝ)) - f' ((i : ℝ) / ((16 ^ n : ℕ) : ℝ))| ≤ d)
    {i : ℕ} (hi : i ≤ 16 ^ n) :
    ‖Zv (16 ^ n) δ f p₀ p₁ i - Zv (16 ^ n) δ f' p₀' p₁' i‖ ≤
      δ * (3 * ‖p₀ - p₀'‖ + 2 * ‖p₁ - p₁'‖ + 4 * ((16 ^ n : ℕ) : ℝ) * d) := by
  have hδ := hs.pos
  have hMr : (1 : ℝ) ≤ ((16 ^ n : ℕ) : ℝ) := by exact_mod_cast M_pos n
  have hd0 : 0 ≤ d := (abs_nonneg _).trans (hd 0 (Nat.zero_le _))
  have ha : ∀ j, aj (16 ^ n) δ f j ^ 2 ≤ 1 / 4 := fun j => (aj_sq_le hs hfB j).trans hs.eta_le'
  have ha' : ∀ j, aj (16 ^ n) δ f' j ^ 2 ≤ 1 / 4 := fun j => (aj_sq_le hs hf'B j).trans hs.eta_le'
  have huv := norm_uv_sub_uv_le (M_pos n) hδ.le ha ha' hd hi
  have hu := norm_uv_le2 hs hf hfB hi
  have hyx := (norm_yx_bounds hs h0' h1').2
  have e : Zv (16 ^ n) δ f p₀ p₁ i - Zv (16 ^ n) δ f' p₀' p₁' i =
      (xp δ p₀ - xp δ p₀') + ((yp δ p₁ - xp δ p₀) - (yp δ p₁' - xp δ p₀')) *
        uv (16 ^ n) δ f i + (yp δ p₁' - xp δ p₀') * (uv (16 ^ n) δ f i - uv (16 ^ n) δ f' i) := by
    unfold Zv; ring
  have e1 : ‖xp δ p₀ - xp δ p₀'‖ = δ * ‖p₀ - p₀'‖ := by
    unfold xp
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  have e2 : ‖(yp δ p₁ - xp δ p₀) - (yp δ p₁' - xp δ p₀')‖ ≤ δ * (‖p₀ - p₀'‖ + ‖p₁ - p₁'‖) := by
    unfold xp yp
    rw [show 1 + (δ : ℂ) * p₁ - (δ : ℂ) * p₀ - (1 + (δ : ℂ) * p₁' - (δ : ℂ) * p₀') =
      (δ : ℂ) * ((p₁ - p₁') - (p₀ - p₀')) by ring, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hδ]
    have := norm_sub_le (p₁ - p₁') (p₀ - p₀')
    nlinarith
  rw [e]
  calc _ ≤ ‖xp δ p₀ - xp δ p₀'‖ + ‖((yp δ p₁ - xp δ p₀) - (yp δ p₁' - xp δ p₀')) *
          uv (16 ^ n) δ f i‖ +
        ‖(yp δ p₁' - xp δ p₀') * (uv (16 ^ n) δ f i - uv (16 ^ n) δ f' i)‖ :=
        norm_add₃_le
    _ ≤ δ * ‖p₀ - p₀'‖ + δ * (‖p₀ - p₀'‖ + ‖p₁ - p₁'‖) * 2 +
        9 / 8 * (3 * ((16 ^ n : ℕ) : ℝ) * δ * d) := by
        rw [norm_mul, norm_mul, e1]
        gcongr
    _ ≤ _ := by nlinarith [mul_nonneg hδ.le hd0, norm_nonneg (p₀ - p₀'),
        norm_nonneg (p₁ - p₁')]

lemma abs_uW_sub (hs : Small n B A δ) (hf : f ∈ V n) (hf' : f' ∈ V n)
    (hfB : ∀ x, |f x| ≤ B) (hf'B : ∀ x, |f' x| ≤ B) {d : ℝ}
    (hd : ∀ i : ℕ, i ≤ 16 ^ n → |f ((i : ℝ) / ((16 ^ n : ℕ) : ℝ)) - f' ((i : ℝ) / ((16 ^ n : ℕ) : ℝ))| ≤ d)
    {i : ℕ} (hi : i < 16 ^ n) :
    |uW (16 ^ n) δ f i - uW (16 ^ n) δ f' i| ≤ 36 * ((16 ^ n : ℕ) : ℝ) ^ 2 * δ * d := by
  have ha : ∀ j, aj (16 ^ n) δ f j ^ 2 ≤ 1 / 4 := fun j => (aj_sq_le hs hfB j).trans hs.eta_le'
  have ha' : ∀ j, aj (16 ^ n) δ f' j ^ 2 ≤ 1 / 4 := fun j => (aj_sq_le hs hf'B j).trans hs.eta_le'
  obtain ⟨hL1, hLη⟩ := uLen_facts hs hf hfB
  obtain ⟨hL1', -⟩ := uLen_facts hs hf' hf'B
  refine abs_uW_sub_uW_le (M_pos n) hs.pos.le ha ha' hd hL1 hL1'
    (by linarith [hs.eta_le']) (fun k hk => ?_) hi
  calc _ ≤ ‖uv (16 ^ n) δ f (k + 1)‖ + ‖uv (16 ^ n) δ f k‖ := norm_sub_le _ _
    _ ≤ 2 + 2 := add_le_add (norm_uv_le2 hs hf hfB hk) (norm_uv_le2 hs hf hfB hk.le)
    _ = 4 := by norm_num

end Clause3

lemma nine_bound {L11 L12 L13 L21 L22 L23 L31 L32 L33 a11 a12 a13 a21 a22 a23 a31 a32 a33 : ℝ}
    (h11 : |L11| ≤ a11) (h12 : |L12| ≤ a12) (h13 : |L13| ≤ a13) (h21 : |L21| ≤ a21)
    (h22 : |L22| ≤ a22) (h23 : |L23| ≤ a23) (h31 : |L31| ≤ a31) (h32 : |L32| ≤ a32)
    (h33 : |L33| ≤ a33) :
    L11 - L12 - L13 - L21 + L22 + L23 - L31 + L32 + L33 ≤
      a11 + a12 + a13 + a21 + a22 + a23 + a31 + a32 + a33 := by
  linarith [le_abs_self L11, neg_abs_le L12, neg_abs_le L13, neg_abs_le L21, le_abs_self L22,
    le_abs_self L23, neg_abs_le L31, le_abs_self L32, le_abs_self L33]

set_option maxHeartbeats 1000000 in
/-- **Clause 3: the Hölder-`1/2` modulus.** -/
theorem clause3_bound (hL31 : TwoScaleCovBound) (n : ℕ) (B A : ℝ) : ∃ Lmod : ℝ, ∀ δ : ℝ,
    Small n B A δ → ∀ f f' : ℝ → ℝ, ∀ p₀ p₁ p₀' p₁' : ℂ, f ∈ V n → f' ∈ V n →
    (∀ x, |f x| ≤ B) → (∀ x, |f' x| ≤ B) → ‖p₀‖ ≤ A → ‖p₁‖ ≤ A → ‖p₀'‖ ≤ A → ‖p₁'‖ ≤ A →
    δ⁻¹ * ((cfgComb (constrCfg (16 ^ n) δ f p₀ p₁)).sub
          (cfgComb (constrCfg (16 ^ n) δ f' p₀' p₁'))).logCov
        ((cfgComb (constrCfg (16 ^ n) δ f p₀ p₁)).sub
          (cfgComb (constrCfg (16 ^ n) δ f' p₀' p₁'))) ≤
      Lmod * ((⨆ x ∈ Icc (0 : ℝ) 1, |f x - f' x|) + ‖p₀ - p₀'‖ + ‖p₁ - p₁'‖) := by
  obtain ⟨C, hC0, hC⟩ := twoScale_wc hL31
  have hM : 0 < 16 ^ n := M_pos n
  set Mr : ℝ := ((16 ^ n : ℕ) : ℝ) with hMr_def
  have hMr1 : (1 : ℝ) ≤ Mr := by rw [hMr_def]; exact_mod_cast hM
  have hMr0 : 0 < Mr := by linarith
  set ℓ : ℝ := 1 / (2 * Mr) with hℓ
  have hℓ0 : 0 < ℓ := by rw [hℓ]; positivity
  set K := Kseg 3 ℓ with hK
  have hK0 : 0 ≤ K := Kseg_nonneg (by norm_num) hℓ0
  set Lg : ℝ := max 1 (2 * 2 * Mr) with hLg
  have hLg0 : 0 ≤ Lg := le_trans zero_le_one (le_max_left _ _)
  refine ⟨12 * C * Lg * Mr + 360 * Mr ^ 3 * K, ?_⟩
  intro δ hs f f' p₀ p₁ p₀' p₁' hf hf' hfB hf'B h0 h1 h0' h1'
  have hB : 0 ≤ B := (abs_nonneg _).trans (hfB 0)
  have hδ := hs.pos
  have cf := cfgFacts hs hf hfB h0 h1
  have cf' := cfgFacts hs hf' hf'B h0' h1'
  set d := ⨆ x ∈ Icc (0 : ℝ) 1, |f x - f' x| with hd_def
  have hdle : ∀ x ∈ Icc (0:ℝ) 1, |f x - f' x| ≤ d := fun x hx =>
    le_iSup_Icc (C := 2 * B) (fun y => (abs_sub _ _).trans (by linarith [hfB y, hf'B y])) hx
  have hd : ∀ i : ℕ, i ≤ 16 ^ n → |f ((i : ℝ) / Mr) - f' ((i : ℝ) / Mr)| ≤ d :=
    fun i hi => hdle _ (t_mem n i hi)
  have hd0 : 0 ≤ d := (abs_nonneg _).trans (hdle 0 ⟨le_rfl, zero_le_one⟩)
  set u₁ := δ * (‖p₀ - p₀'‖ + ‖p₁ - p₁'‖) with hu₁
  set u₂ := δ * (3 * ‖p₀ - p₀'‖ + 2 * ‖p₁ - p₁'‖ + 4 * Mr * d) with hu₂
  have hu₁0 : 0 ≤ u₁ := by rw [hu₁]; positivity
  have hu₂0 : 0 ≤ u₂ := by rw [hu₂]; positivity
  -- pieces
  set c1 := ch1 (xp δ p₀) (yp δ p₁) with hc1
  set c1' := ch1 (xp δ p₀') (yp δ p₁') with hc1'
  set P := wc (16 ^ n) (uW (16 ^ n) δ f) (Zv (16 ^ n) δ f p₀ p₁) with hP
  set P' := wc (16 ^ n) (uW (16 ^ n) δ f') (Zv (16 ^ n) δ f' p₀' p₁') with hP'
  set Pt := wc (16 ^ n) (uW (16 ^ n) δ f) (Zv (16 ^ n) δ f' p₀' p₁') with hPt
  have hcfg : cfgComb (constrCfg (16 ^ n) δ f p₀ p₁) = c1.sub P := by
    rw [cfgComb_eq _ _ _ _ _ cf.hne, hc1, ch1_eq]
  have hcfg' : cfgComb (constrCfg (16 ^ n) δ f' p₀' p₁') = c1'.sub P' := by
    rw [cfgComb_eq _ _ _ _ _ cf'.hne, hc1', ch1_eq]
  rw [hcfg, hcfg']
  have hdec : ((c1.sub P).sub (c1'.sub P')).logCov ((c1.sub P).sub (c1'.sub P')) =
      (c1.sub c1').logCov (c1.sub c1') - (c1.sub c1').logCov (P.sub Pt) -
      (c1.sub c1').logCov (Pt.sub P') - (P.sub Pt).logCov (c1.sub c1') +
      (P.sub Pt).logCov (P.sub Pt) + (P.sub Pt).logCov (Pt.sub P') -
      (Pt.sub P').logCov (c1.sub c1') + (Pt.sub P').logCov (P.sub Pt) +
      (Pt.sub P').logCov (Pt.sub P') := by
    simp only [logCov_sub_sub]; ring
  rw [hdec]
  -- chord facts
  have hx := norm_xp_le hs h0
  have hx' := norm_xp_le hs h0'
  have hyx := norm_yx_bounds hs h0 h1
  have hyx' := norm_yx_bounds hs h0' h1'
  have hc1pt : ∀ i : ℕ, i ≤ 1 → ‖chordPt (xp δ p₀) (yp δ p₁) (i : ℝ)‖ ≤ 3 := by
    intro i hi
    interval_cases i
    · simp only [Nat.cast_zero, chordPt_zero]; linarith
    · simp only [Nat.cast_one, chordPt_one]
      calc ‖yp δ p₁‖ = ‖xp δ p₀ + (yp δ p₁ - xp δ p₀)‖ := by congr 1; ring
        _ ≤ ‖xp δ p₀‖ + ‖yp δ p₁ - xp δ p₀‖ := norm_add_le _ _
        _ ≤ 3 := by linarith [hyx.2]
  have hc1pt' : ∀ i : ℕ, i ≤ 1 → ‖chordPt (xp δ p₀') (yp δ p₁') (i : ℝ)‖ ≤ 3 := by
    intro i hi
    interval_cases i
    · simp only [Nat.cast_zero, chordPt_zero]; linarith
    · simp only [Nat.cast_one, chordPt_one]
      calc ‖yp δ p₁'‖ = ‖xp δ p₀' + (yp δ p₁' - xp δ p₀')‖ := by congr 1; ring
        _ ≤ ‖xp δ p₀'‖ + ‖yp δ p₁' - xp δ p₀'‖ := norm_add_le _ _
        _ ≤ 3 := by linarith [hyx'.2]
  have hc1E : ∀ i : ℕ, i < 1 → 7 / 8 / ((1 : ℕ) : ℝ) ≤
      ‖chordPt (xp δ p₀) (yp δ p₁) ((i + 1 : ℕ) : ℝ) - chordPt (xp δ p₀) (yp δ p₁) (i : ℝ)‖ := by
    intro i hi
    interval_cases i
    simp only [Nat.cast_zero, zero_add, Nat.cast_one, chordPt_zero, chordPt_one, div_one]
    exact hyx.1
  have hc1E' : ∀ i : ℕ, i < 1 → 7 / 8 / ((1 : ℕ) : ℝ) ≤
      ‖chordPt (xp δ p₀') (yp δ p₁') ((i + 1 : ℕ) : ℝ) -
        chordPt (xp δ p₀') (yp δ p₁') (i : ℝ)‖ := by
    intro i hi
    interval_cases i
    simp only [Nat.cast_zero, zero_add, Nat.cast_one, chordPt_zero, chordPt_one, div_one]
    exact hyx'.1
  have hprob1 : ∀ x y : ℂ, (ch1 x y).IsProb := fun x y =>
    isProb_wc _ (fun _ _ => zero_le_one) (by simp)
  have hgrow1 : ∀ x y : ℂ, (∀ i : ℕ, i < 1 → 7 / 8 / ((1 : ℕ) : ℝ) ≤
      ‖chordPt x y ((i + 1 : ℕ) : ℝ) - chordPt x y (i : ℝ)‖) →
      GrowthBound (ch1 x y).toMeasure Lg 1 := by
    intro x y hE
    refine growth_mono one_pos (growth_helper one_pos (fun _ _ => zero_le_one) (by simp)
      (fun _ _ => by norm_num) hE) ?_
    rw [hLg]
    apply max_le_max le_rfl
    push_cast; linarith
  have hcoup1 : ∀ i : ℕ, i ≤ 1 → ‖chordPt (xp δ p₀) (yp δ p₁) (i : ℝ) -
      chordPt (xp δ p₀') (yp δ p₁') (i : ℝ)‖ ≤ u₁ := by
    intro i hi
    interval_cases i
    · simp only [Nat.cast_zero, chordPt_zero]
      unfold xp
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ, hu₁]
      have := norm_nonneg (p₁ - p₁')
      nlinarith
    · simp only [Nat.cast_one, chordPt_one]
      unfold yp
      rw [add_sub_add_left_eq_sub, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hδ, hu₁]
      have := norm_nonneg (p₀ - p₀')
      nlinarith
  have hcoup2 : ∀ i : ℕ, i ≤ 16 ^ n → ‖Zv (16 ^ n) δ f p₀ p₁ i - Zv (16 ^ n) δ f' p₀' p₁' i‖ ≤ u₂ :=
    fun i hi => norm_Zv_sub_Zv hs hf hf' hfB hf'B h0 h1 h0' h1' hd hi
  have hgP : GrowthBound P.toMeasure Lg 1 := cf.growth_uW_Zv
  have hgPt : GrowthBound Pt.toMeasure Lg 1 :=
    growth_helper hM (fun i _ => cf.uW0 i) cf.uWs cf.uWle cf'.ZvE
  -- two-scale bounds
  have t11 : |(c1.sub c1').logCov (c1.sub c1')| ≤ C * Lg * u₁ := by
    have := hC _ _ _ _ _ _ _ _ Lg u₁ u₁ hLg0 hu₁0 hu₁0 (hprob1 _ _) (hprob1 _ _) (hprob1 _ _)
      (hprob1 _ _) (hgrow1 _ _ hc1E) (hgrow1 _ _ hc1E') hcoup1 hcoup1
    rwa [Real.sqrt_mul_self hu₁0] at this
  have t12 : |(c1.sub c1').logCov (P.sub Pt)| ≤ C * Lg * (u₁ + u₂) := by
    have := hC _ _ _ _ _ _ _ _ Lg u₁ u₂ hLg0 hu₁0 hu₂0 (hprob1 _ _) (hprob1 _ _)
      (cf.prob_uW _) (cf.prob_uW _) (hgrow1 _ _ hc1E) (hgrow1 _ _ hc1E') hcoup1 hcoup2
    refine this.trans ?_
    gcongr
    exact sqrt_mul_le_add hu₁0 hu₂0
  have t21 : |(P.sub Pt).logCov (c1.sub c1')| ≤ C * Lg * (u₁ + u₂) := by
    have := hC _ _ _ _ _ _ _ _ Lg u₂ u₁ hLg0 hu₂0 hu₁0 (cf.prob_uW _) (cf.prob_uW _)
      (hprob1 _ _) (hprob1 _ _) hgP hgPt hcoup2 hcoup1
    refine this.trans ?_
    gcongr
    rw [add_comm]
    exact sqrt_mul_le_add hu₂0 hu₁0
  have t22 : |(P.sub Pt).logCov (P.sub Pt)| ≤ C * Lg * u₂ := by
    have := hC _ _ _ _ _ _ _ _ Lg u₂ u₂ hLg0 hu₂0 hu₂0 (cf.prob_uW _) (cf.prob_uW _)
      (cf.prob_uW _) (cf.prob_uW _) hgP hgPt hcoup2 hcoup2
    rwa [Real.sqrt_mul_self hu₂0] at this
  -- weight perturbation bounds
  have hW : ∑ i ∈ Finset.range (16 ^ n), |uW (16 ^ n) δ f i - uW (16 ^ n) δ f' i| ≤
      Mr * (36 * Mr ^ 2 * δ * d) := by
    calc _ ≤ ∑ i ∈ Finset.range (16 ^ n), 36 * Mr ^ 2 * δ * d := Finset.sum_le_sum fun i hi =>
          abs_uW_sub hs hf hf' hfB hf'B hd (Finset.mem_range.1 hi)
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hℓ1 : ℓ ≤ 7 / 8 / ((1 : ℕ) : ℝ) := by
    rw [hℓ, Nat.cast_one, div_one, div_le_iff₀ (by positivity)]; nlinarith
  have gc1 : GoodC (c1.sub c1') ℓ 3 := goodC_sub
    (goodC_wc hc1pt fun i hi => le_trans hℓ1 (hc1E i hi))
    (goodC_wc hc1pt' fun i hi => le_trans hℓ1 (hc1E' i hi))
  have gPPt : GoodC (P.sub Pt) ℓ 3 := goodC_sub (cf.good_Zv _) (cf'.good_Zv _)
  have gPtP' : GoodC (Pt.sub P') ℓ 3 := goodC_sub (cf'.good_Zv _) (cf'.good_Zv _)
  have tvc1 : tv (c1.sub c1') = 2 := by
    rw [tv_sub, hc1, hc1', ch1, ch1, tv_wc, tv_wc]; norm_num
  have tvPPt : tv (P.sub Pt) = 2 := by rw [tv_sub, tv_uW cf, tv_uW cf]; norm_num
  have tvPtP' : tv (Pt.sub P') = 2 := by rw [tv_sub, tv_uW cf, tv_uW cf']; norm_num
  have hZ'B := cf'.ZvB
  have hZ'E : ∀ i < 16 ^ n, ℓ ≤ ‖Zv (16 ^ n) δ f' p₀' p₁' (i + 1) - Zv (16 ^ n) δ f' p₀' p₁' i‖ :=
    fun i hi => (ell_le n).trans (cf'.ZvE i hi)
  have s1 : |(c1.sub c1').logCov (Pt.sub P')| ≤ 2 * (Mr * (36 * Mr ^ 2 * δ * d)) * K := by
    have := abs_logCov_wc_sub_right_good hℓ0 (by norm_num) hZ'B hZ'E gc1
      (W := uW (16 ^ n) δ f) (W' := uW (16 ^ n) δ f')
    rw [tvc1] at this
    refine this.trans ?_; gcongr
  have s2 : |(P.sub Pt).logCov (Pt.sub P')| ≤ 2 * (Mr * (36 * Mr ^ 2 * δ * d)) * K := by
    have := abs_logCov_wc_sub_right_good hℓ0 (by norm_num) hZ'B hZ'E gPPt
      (W := uW (16 ^ n) δ f) (W' := uW (16 ^ n) δ f')
    rw [tvPPt] at this
    refine this.trans ?_; gcongr
  have s3 : |(Pt.sub P').logCov (c1.sub c1')| ≤ Mr * (36 * Mr ^ 2 * δ * d) * 2 * K := by
    have := abs_logCov_wc_sub_left_good hℓ0 (by norm_num) hZ'B gc1
      (W := uW (16 ^ n) δ f) (W' := uW (16 ^ n) δ f')
    rw [tvc1] at this
    refine this.trans ?_; gcongr
  have s4 : |(Pt.sub P').logCov (P.sub Pt)| ≤ Mr * (36 * Mr ^ 2 * δ * d) * 2 * K := by
    have := abs_logCov_wc_sub_left_good hℓ0 (by norm_num) hZ'B gPPt
      (W := uW (16 ^ n) δ f) (W' := uW (16 ^ n) δ f')
    rw [tvPPt] at this
    refine this.trans ?_; gcongr
  have s5 : |(Pt.sub P').logCov (Pt.sub P')| ≤ Mr * (36 * Mr ^ 2 * δ * d) * 2 * K := by
    have := abs_logCov_wc_sub_left_good hℓ0 (by norm_num) hZ'B gPtP'
      (W := uW (16 ^ n) δ f) (W' := uW (16 ^ n) δ f')
    rw [tvPtP'] at this
    refine this.trans ?_; gcongr
  -- conclusion
  have hsum : u₁ + u₂ ≤ δ * (4 * Mr) * (d + ‖p₀ - p₀'‖ + ‖p₁ - p₁'‖) := by
    rw [hu₁, hu₂]
    have e1 := norm_nonneg (p₀ - p₀')
    have e2 := norm_nonneg (p₁ - p₁')
    nlinarith [mul_nonneg hδ.le hd0, mul_nonneg hδ.le e1, mul_nonneg hδ.le e2]
  have hdist : 0 ≤ d + ‖p₀ - p₀'‖ + ‖p₁ - p₁'‖ := by positivity
  have hCL : 0 ≤ C * Lg := mul_nonneg hC0 hLg0
  have h1 : 3 * (C * Lg) * (u₁ + u₂) ≤
      3 * (C * Lg) * (δ * (4 * Mr) * (d + ‖p₀ - p₀'‖ + ‖p₁ - p₁'‖)) := by gcongr
  have h2 : 5 * (2 * (Mr * (36 * Mr ^ 2 * δ * d)) * K) ≤
      360 * Mr ^ 3 * K * δ * (d + ‖p₀ - p₀'‖ + ‖p₁ - p₁'‖) := by
    have : 0 ≤ 360 * Mr ^ 3 * K * δ := by positivity
    have e1 := norm_nonneg (p₀ - p₀')
    have e2 := norm_nonneg (p₁ - p₁')
    nlinarith
  rw [inv_mul_le_iff₀ hδ]
  refine (nine_bound t11 t12 s1 t21 t22 s2 s3 s4 s5).trans ?_
  linarith

end LQGDimension.ConstrCov
