/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_10TailMain at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_10TailGood
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_9Final

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Propositions 3.10 and 3.9

Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
proof of Proposition 3.10, Steps 1–3 (T:1875–1912): the probability estimates.
For `C` large, outside an event of probability `≤ (1 + 6C_p) C^{-(q + √(q²-4)) + (Q-q)}`
(Lemma 3.11 at all dyadic corners; Proposition 3.1 at all dyadic squares and all levels, union
bound; Axiom I) the deterministic bound `diam_le_on_good` holds; with `C̃ = K₁ C^{ξ + ζ}`
this is the display T:1909–1912 (`DiamTailRS`). Then `prop3_10_of`, `prop3_9_of`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology Complex
open scoped ENNReal ComplexOrder

namespace LQGMetric.DFGPS
open Blueprint MetricGeometry

/-- the good event of Prop 3.1 for the horizontal configuration at height `e` -/
def GoodH (D : DistC → ContMetric) (ξ : ℝ) (c : ℝ → ℝ) (A s : ℝ) (w : ℂ) (e : ℝ) : Set DistC :=
  {g | ENNReal.ofReal (A⁻¹ * scaleFac ξ c g s w) ≤
      setDistIn (D g) (scaleSet s w (Icc (1 / 16) (1 / 16) ×ℂ Icc (3 / 16 + e) (5 / 16 + e)))
        (scaleSet s w (Icc (15 / 16) (15 / 16) ×ℂ Icc (3 / 16 + e) (5 / 16 + e)))
        (scaleSet s w (Ioo 0 1 ×ℂ Ioo (1 / 8 + e) (3 / 8 + e))) ∧
    setDistIn (D g) (scaleSet s w (Icc (1 / 16) (1 / 16) ×ℂ Icc (3 / 16 + e) (5 / 16 + e)))
        (scaleSet s w (Icc (15 / 16) (15 / 16) ×ℂ Icc (3 / 16 + e) (5 / 16 + e)))
        (scaleSet s w (Ioo 0 1 ×ℂ Ioo (1 / 8 + e) (3 / 8 + e))) ≤
      ENNReal.ofReal (A * scaleFac ξ c g s w)}

/-- the good event of Prop 3.1 for the vertical configuration -/
def GoodV (D : DistC → ContMetric) (ξ : ℝ) (c : ℝ → ℝ) (A s : ℝ) (w : ℂ) : Set DistC :=
  {g | ENNReal.ofReal (A⁻¹ * scaleFac ξ c g s w) ≤
      setDistIn (D g) (scaleSet s w (Icc (3 / 16) (5 / 16) ×ℂ Icc (1 / 16) (1 / 16)))
        (scaleSet s w (Icc (3 / 16) (5 / 16) ×ℂ Icc (15 / 16) (15 / 16)))
        (scaleSet s w (Ioo (1 / 8) (3 / 8) ×ℂ Ioo 0 1)) ∧
    setDistIn (D g) (scaleSet s w (Icc (3 / 16) (5 / 16) ×ℂ Icc (1 / 16) (1 / 16)))
        (scaleSet s w (Icc (3 / 16) (5 / 16) ×ℂ Icc (15 / 16) (15 / 16)))
        (scaleSet s w (Ioo (1 / 8) (3 / 8) ×ℂ Ioo 0 1)) ≤
      ENNReal.ofReal (A * scaleFac ξ c g s w)}

section
variable (h31 : Prop3_1) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
  {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {μ : Measure DistC} [IsProbabilityMeasure μ]
  (hμ : IsNormalizedWPGFF id μ)
include h31 hγ0 hγ2 hD hμ

lemma goodH_tail {e : ℝ} {p : ℝ} (hp : 0 < p) :
    ∃ C A₀ : ℝ, ∀ A, A₀ < A → ∀ s : ℝ, 0 < s → ∀ w : ℂ,
      μ (GoodH D (xiGamma γ) c A s w e)ᶜ ≤ ENNReal.ofReal (C * A ^ (-p)) :=
  prop3_1_centre_box h31 hγ0 hγ2 hD le_rfl (by linarith) le_rfl (by linarith)
    (Or.inr (by linarith)) (Or.inr (by linarith)) (Or.inl (by norm_num))
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    ⟨by linarith, by linarith, by linarith, by linarith⟩ hμ p hp

lemma goodV_tail {p : ℝ} (hp : 0 < p) :
    ∃ C A₀ : ℝ, ∀ A, A₀ < A → ∀ s : ℝ, 0 < s → ∀ w : ℂ,
      μ (GoodV D (xiGamma γ) c A s w)ᶜ ≤ ENNReal.ofReal (C * A ^ (-p)) :=
  prop3_1_centre_box h31 hγ0 hγ2 hD (by norm_num) le_rfl (by norm_num) le_rfl
    (Or.inl (by norm_num)) (Or.inl (by norm_num)) (Or.inr (by norm_num))
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩ hμ p hp

end

/-- a countable union with geometrically decaying measures -/
lemma measure_iUnion_le_geom {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {s : ℕ → Set Ω}
    {K : ℝ} (hK : 0 ≤ K) (h : ∀ n, P (s n) ≤ ENNReal.ofReal (K * (1 / 2) ^ n)) :
    P (⋃ n, s n) ≤ ENNReal.ofReal (2 * K) := by
  refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum h).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    ((summable_geometric_two).mul_left K), tsum_mul_left, tsum_geometric_two, mul_comm]

/-- dyadic corners are grid points of mesh `2^{-n-1}𝕣` in `B_{2𝕣}(0)` (for Lemma 3.11) -/
lemma dyCorner_mem {𝕣 : ℝ} (h𝕣 : 0 < 𝕣) {n j k : ℕ} (hj : j < 2 ^ n) (hk : k < 2 ^ n) :
    dyCorner 𝕣 n j k ∈ Metric.ball (0 : ℂ) (2 * 𝕣) ∩ gridPts (((2 : ℝ) ^ (n + 1))⁻¹ * 𝕣) := by
  have hs : 0 < 𝕣 / 2 ^ n := by positivity
  have hj' : (j : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast hj
  have hk' : (k : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast hk
  have e : (2 : ℝ) ^ n * (𝕣 / 2 ^ n) = 𝕣 := by field_simp
  refine ⟨?_, ⟨2 * j, 2 * k, ?_⟩⟩
  · rw [mem_ball, dist_zero_right]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
    simp only [dyCorner]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    nlinarith
  · apply Complex.ext <;> simp only [dyCorner] <;> push_cast <;> rw [pow_succ] <;> field_simp

/-- **DFGPS Prop 3.10, Steps 1–3** (T:1875–1912), canonical space. -/
theorem diam_rS_upper_tail (h31 : Prop3_1) (hS : DFGPSScaling) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {μ : Measure DistC} [IsProbabilityMeasure μ] (hμ : IsNormalizedWPGFF id μ) {a : ℝ}
    (ha : a < 4 * dGamma γ / γ ^ 2) :
    ∃ C' t₀ : ℝ, ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ t : ℝ, t₀ ≤ t →
      μ {g | ENNReal.ofReal t < ENNReal.ofReal (scaleFac (xiGamma γ) c g 𝕣 0)⁻¹ *
          internalDiam (D g) (rS 𝕣) (rS 𝕣)} ≤ ENNReal.ofReal (C' * t ^ (-a)) := by
  obtain ⟨q, hq2, hqQ, hqa⟩ := exists_q_exponent hγ0 hγ2 ha
  set ξ := xiGamma γ with hξdef
  have hξ : 0 < ξ := DG.xiGamma_pos hγ0
  set Q := Q γ with hQdef
  set ζ := ξ * (Q - q) / 4 with hζ
  have hQq : 0 < Q - q := sub_pos.2 hqQ
  have hζ0 : 0 < ζ := by rw [hζ]; positivity
  set e₁ := q + Real.sqrt (q ^ 2 - 4) - (Q - q) with he₁
  have hf : a < e₁ / (ξ + ζ) := hqa
  set θ := (1 / 2 : ℝ) ^ (ξ * (Q - q) / 2) with hθ
  have hθ1 : θ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  -- Theorem 1.5 at all dyadic scales
  obtain ⟨K₀, hK₀1, hK₀⟩ := scale_ratio_dyadic hγ0 hγ2 hD hS hζ0 (by
    have := Q_pos hγ0; rw [hζ]; nlinarith)
  -- Lemma 3.11
  obtain ⟨C₀, hC₀⟩ := lem3_11 hμ.1 (R := 2) two_pos hq2 (Q - q) hQq
  -- Prop 3.1 at the three configurations
  set p := (|e₁| + 3) / ζ with hp
  have hp0 : 0 < p := by positivity
  have hζp : ζ * p = |e₁| + 3 := by rw [hp]; field_simp
  obtain ⟨CH0, AH0, hH0⟩ := goodH_tail h31 hγ0 hγ2 hD hμ (e := ((0 : ℕ) : ℝ) / 2) hp0
  obtain ⟨CH1, AH1, hH1⟩ := goodH_tail h31 hγ0 hγ2 hD hμ (e := ((1 : ℕ) : ℝ) / 2) hp0
  obtain ⟨CV, AV, hV⟩ := goodV_tail h31 hγ0 hγ2 hD hμ hp0
  set Cp := max (max CH0 CH1) (max CV 0) with hCp
  have hCp0 : 0 ≤ Cp := le_max_of_le_right (le_max_right _ _)
  set Ap := max (max AH0 AH1) (max AV 0) with hAp
  have hAp0 : 0 ≤ Ap := le_max_of_le_right (le_max_right _ _)
  have hHb : ∀ b : ℕ, b ≤ 1 → ∀ A, Ap < A → ∀ s : ℝ, 0 < s → ∀ w : ℂ,
      μ (GoodH D ξ c A s w ((b : ℝ) / 2))ᶜ ≤ ENNReal.ofReal (Cp * A ^ (-p)) := by
    intro b hb A hA s hs w
    have hA0 : 0 < A := hAp0.trans_lt hA
    interval_cases b
    · exact (hH0 A (lt_of_le_of_lt ((le_max_left AH0 AH1).trans (le_max_left _ _)) hA) s hs w).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          ((le_max_left _ _).trans (le_max_left _ _)) (by positivity)))
    · exact (hH1 A (lt_of_le_of_lt ((le_max_right AH0 AH1).trans (le_max_left _ _)) hA) s hs w).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          ((le_max_right _ _).trans (le_max_left _ _)) (by positivity)))
  have hVb : ∀ A, Ap < A → ∀ s : ℝ, 0 < s → ∀ w : ℂ,
      μ (GoodV D ξ c A s w)ᶜ ≤ ENNReal.ofReal (Cp * A ^ (-p)) := by
    intro A hA s hs w
    have hA0 : 0 < A := hAp0.trans_lt hA
    exact (hV A (lt_of_le_of_lt ((le_max_left AV 0).trans (le_max_right _ _)) hA) s hs w).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) (by positivity)))
  -- constants
  set K₁ := 2 * (5 * (2 * K₀) / (1 - θ)) with hK₁
  have hθ1' : 0 < 1 - θ := by linarith
  have hK₁0 : 0 < K₁ := by rw [hK₁]; positivity
  set M := max (max C₀ 1) (Ap ^ (1 / ζ)) + 1 with hM
  have hM1 : 1 < M := by
    have h1 := le_max_left (max C₀ 1) (Ap ^ (1 / ζ))
    have h2 := le_max_right C₀ 1
    rw [hM]; linarith
  refine ⟨(1 + 6 * Cp) * K₁ ^ a, K₁ * M ^ (ζ + ξ), fun 𝕣 h𝕣 t ht => ?_⟩
  have hM0 : 0 < M := by linarith
  have htK : M ^ (ζ + ξ) ≤ t / K₁ := by rw [le_div_iff₀ hK₁0, mul_comm]; exact ht
  have htK1 : 1 ≤ t / K₁ := (Real.one_le_rpow hM1.le (by positivity)).trans htK
  have ht0 : 0 < t := by have := (div_pos_iff_of_pos_right hK₁0).1 (by linarith : 0 < t / K₁); exact this
  set C := (t / K₁) ^ (1 / (ζ + ξ)) with hCdef
  have hCM : M ≤ C := by
    have h := Real.rpow_le_rpow (by positivity) htK (by positivity : 0 ≤ 1 / (ζ + ξ))
    rwa [← Real.rpow_mul hM0.le, mul_one_div_cancel (by positivity), Real.rpow_one] at h
  have hC1 : 1 ≤ C := by linarith
  have hC0 : 0 < C := by linarith
  have hCC₀ : C₀ < C := by
    have := le_max_left C₀ 1; have := le_max_left (max C₀ 1) (Ap ^ (1 / ζ)); linarith
  have hCA : Ap < C ^ ζ := by
    have h1 : Ap ^ (1 / ζ) < C := by have := le_max_right (max C₀ 1) (Ap ^ (1 / ζ)); linarith
    have h2 := Real.rpow_lt_rpow (by positivity) h1 hζ0
    rwa [← Real.rpow_mul hAp0, one_div_mul_cancel hζ0.ne', Real.rpow_one] at h2
  have hKC : K₁ * C ^ (ζ + ξ) = t := by
    rw [hCdef, ← Real.rpow_mul (by positivity), one_div_mul_cancel (by positivity),
      Real.rpow_one]; field_simp
  -- the levels
  set A : ℕ → ℝ := fun n => C ^ ζ * ((2 : ℝ) ^ n) ^ ζ with hAdef
  have hAn : ∀ n, Ap < A n := fun n => hCA.trans_le (le_mul_of_one_le_right (by positivity)
    (Real.one_le_rpow (one_le_pow₀ (by norm_num)) hζ0.le))
  -- the bad events
  set E0 : Set DistC := {g | ¬ (D g).IsLength}
  set E1 : Set DistC := {g | ∃ n : ℕ, ∃ w ∈ Metric.ball (0 : ℂ) (2 * 𝕣) ∩
      gridPts (((2 : ℝ) ^ (n + 1))⁻¹ * 𝕣), Real.log (C * (2 : ℝ) ^ (q * n)) <
        |circleAvg g (((2 : ℝ) ^ n)⁻¹ * 𝕣) w - circleAvg g 𝕣 0|}
  set E2 : ℕ → Set DistC := fun n => ⋃ j ∈ Finset.range (2 ^ n), ⋃ k ∈ Finset.range (2 ^ n),
    ((⋃ b ∈ Finset.range 2, (GoodH D ξ c (A n) (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k) ((b : ℝ) / 2))ᶜ) ∪
      (GoodV D ξ c (A n) (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k))ᶜ)
  have hincl : {g | ENNReal.ofReal t < ENNReal.ofReal (scaleFac ξ c g 𝕣 0)⁻¹ *
      internalDiam (D g) (rS 𝕣) (rS 𝕣)} ⊆ E0 ∪ E1 ∪ ⋃ n, E2 n := by
    intro g hg
    by_contra hne
    simp only [mem_union, not_or, mem_iUnion, not_exists] at hne
    obtain ⟨⟨hl, h1⟩, h2⟩ := hne
    simp only [E0, mem_ofPred_eq, not_not] at hl
    have h1' : ∀ n : ℕ, ∀ w ∈ Metric.ball (0 : ℂ) (2 * 𝕣) ∩ gridPts (((2 : ℝ) ^ (n + 1))⁻¹ * 𝕣),
        |circleAvg g (((2 : ℝ) ^ n)⁻¹ * 𝕣) w - circleAvg g 𝕣 0| ≤
          Real.log (C * (2 : ℝ) ^ (q * n)) :=
      fun n w hw => not_lt.1 fun hlt => h1 ⟨n, w, hw, hlt⟩
    simp only [E2, mem_iUnion, mem_union, mem_compl_iff, not_exists, not_or, not_not,
      Finset.mem_range] at h2
    have hN : 0 < scaleFac ξ c g 𝕣 0 := mul_pos (hD.tightness.1 𝕣 h𝕣) (Real.exp_pos _)
    have hdiam := diam_le_on_good (D' := D g) (c := c) (g := g) hl hξ hqQ hC1 hK₀1 h𝕣
      hD.tightness.1 (fun n => hK₀ n 𝕣 h𝕣)
      (fun n j k hj hk => by
        have := h1' n (dyCorner 𝕣 n j k) (dyCorner_mem h𝕣 hj hk)
        rw [inv_mul_eq_div] at this
        exact (le_abs_self _).trans this)
      (fun n j k hj hk b hb => ((h2 n j hj k hk).1 b (by omega)).2)
      (fun n j k hj hk => ((h2 n j hj k hk).2).2)
    have hb : ENNReal.ofReal (scaleFac ξ c g 𝕣 0)⁻¹ * internalDiam (D g) (rS 𝕣) (rS 𝕣) ≤
        ENNReal.ofReal t := by
      refine (mul_le_mul' le_rfl hdiam).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity), ← hKC]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [hK₁, ← hζ, ← hθ]; field_simp
    exact absurd hg (not_lt.2 hb)
  -- probability of the bad events
  have hE0 : μ E0 = 0 := by
    have h := hD.length μ id (GM.Tight.isGFFPlusCont_of_wp hμ.1)
    exact measure_mono_null (fun g hg => hg) (ae_iff.1 h)
  have hE1 : μ E1 ≤ ENNReal.ofReal (C ^ (-e₁)) := by
    have h := hC₀ C hCC₀ 𝕣 h𝕣
    have e : -(q + Real.sqrt (q ^ 2 - 4)) + (Q - q) = -e₁ := by rw [he₁]; ring
    rw [e] at h
    exact h
  have hApow : ∀ n : ℕ, A n ^ (-p) = C ^ (-(ζ * p)) * ((2 : ℝ) ^ n) ^ (-(ζ * p)) := by
    intro n
    simp only [hAdef]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (x := C) hC0.le,
      ← Real.rpow_mul (x := (2 : ℝ) ^ n) (by positivity), mul_neg]
  have hE2 : ∀ n, μ (E2 n) ≤ ENNReal.ofReal (3 * Cp * C ^ (-(ζ * p)) * (1 / 2) ^ n) := by
    intro n
    have hs : (0 : ℝ) < 𝕣 / 2 ^ n := by positivity
    set x := ENNReal.ofReal (Cp * A n ^ (-p)) with hx
    have hjk : ∀ j k : ℕ, μ ((⋃ b ∈ Finset.range 2,
        (GoodH D ξ c (A n) (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k) ((b : ℝ) / 2))ᶜ) ∪
          (GoodV D ξ c (A n) (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k))ᶜ) ≤ 3 * x := by
      intro j k
      refine (measure_union_le _ _).trans ?_
      calc _ ≤ (∑ b ∈ Finset.range 2, x) + x := by
            refine add_le_add ((measure_biUnion_finset_le _ _).trans
              (Finset.sum_le_sum fun b hb => ?_)) (hVb (A n) (hAn n) _ hs _)
            exact hHb b (by have := Finset.mem_range.1 hb; omega) (A n) (hAn n) _ hs _
        _ = 3 * x := by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; ring
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc _ ≤ ∑ j ∈ Finset.range (2 ^ n), ∑ k ∈ Finset.range (2 ^ n), 3 * x :=
          Finset.sum_le_sum fun j _ => (measure_biUnion_finset_le _ _).trans
            (Finset.sum_le_sum fun k _ => hjk j k)
      _ = ENNReal.ofReal ((2 : ℝ) ^ n * ((2 : ℝ) ^ n * (3 * (Cp * A n ^ (-p))))) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul,
            hx, ← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          push_cast; rfl
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h3 : ((2 : ℝ) ^ n) ^ (-(ζ * p)) ≤ (((2 : ℝ) ^ n) ^ 3)⁻¹ := by
            refine (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
              (by rw [hζp]; linarith [abs_nonneg e₁] : -(ζ * p) ≤ -3)).trans (le_of_eq ?_)
            rw [Real.rpow_neg (by positivity)]; norm_num
          calc _ = 3 * Cp * C ^ (-(ζ * p)) * ((2 : ℝ) ^ n * (2 : ℝ) ^ n *
                ((2 : ℝ) ^ n) ^ (-(ζ * p))) := by rw [hApow]; ring
            _ ≤ 3 * Cp * C ^ (-(ζ * p)) * ((2 : ℝ) ^ n * (2 : ℝ) ^ n *
                (((2 : ℝ) ^ n) ^ 3)⁻¹) := by gcongr
            _ = _ := by rw [one_div, inv_pow]; field_simp
  have hE2' := measure_iUnion_le_geom μ (by positivity) hE2
  have r1 : C ^ (-(ζ * p)) ≤ C ^ (-e₁) := Real.rpow_le_rpow_of_exponent_le hC1
    (by rw [hζp]; linarith [le_abs_self e₁])
  have r2 : C ^ (-e₁) ≤ K₁ ^ a * t ^ (-a) := by
    rw [hCdef, ← Real.rpow_mul (by positivity)]
    have hf' : a < e₁ / (ζ + ξ) := by rwa [add_comm]
    have e : 1 / (ζ + ξ) * -e₁ = -(e₁ / (ζ + ξ)) := by ring
    calc (t / K₁) ^ (1 / (ζ + ξ) * -e₁) ≤ (t / K₁) ^ (-a) :=
          Real.rpow_le_rpow_of_exponent_le htK1 (by rw [e]; linarith)
      _ = K₁ ^ a * t ^ (-a) := by
          rw [Real.div_rpow ht0.le hK₁0.le, Real.rpow_neg hK₁0.le]; field_simp
  calc _ ≤ μ (E0 ∪ E1 ∪ ⋃ n, E2 n) := measure_mono hincl
    _ ≤ μ E0 + μ E1 + μ (⋃ n, E2 n) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ 0 + ENNReal.ofReal (C ^ (-e₁)) + ENNReal.ofReal (2 * (3 * Cp * C ^ (-(ζ * p)))) :=
        add_le_add (add_le_add hE0.le hE1) hE2'
    _ ≤ _ := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hKt : 0 ≤ K₁ ^ a * t ^ (-a) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left r1 hCp0]

/-- **DFGPS Prop 3.10, Steps 1–3** (T:1875–1912): the tail bound `DiamTailRS`. -/
theorem diamTailRS_of (h31 : Prop3_1) (hS : DFGPSScaling) : DiamTailRS := by
  intro γ hγ0 hγ2 D c hD a ha
  obtain ⟨μ, hμP, hμ⟩ := exists_canonical_normGFF
  obtain ⟨C, t₀, hC⟩ := diam_rS_upper_tail h31 hS hγ0 hγ2 hD hμ ha
  exact ⟨C, t₀, fun P _ h hh 𝕣 h𝕣 t ht =>
    (prob_le_canonical hμ P h hh _).trans (hC 𝕣 h𝕣 t ht)⟩

/-- **DFGPS Proposition 3.10** (T:1757–1762) from Proposition 3.1 and Theorem 1.5. -/
theorem prop3_10_of (h31 : Prop3_1) (hS : DFGPSScaling) : Prop3_10 :=
  prop3_10_of_tail h31 (diamTailRS_of h31 hS)

/-- **DFGPS Proposition 3.9** (T:1747–1755) from Proposition 3.1 and Theorem 1.5. -/
theorem prop3_9_of (h31 : Prop3_1) (hS : DFGPSScaling) : Prop3_9 :=
  prop3_9_of_tail h31 (diamTailRS_of h31 hS)

end LQGMetric.DFGPS
