/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_9Final at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_9Ratio
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_9Neg
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
proof of Proposition 3.9 assuming Proposition 3.10 (T:1766–1775):

* `p ≤ 0`: the lower bound of Proposition 3.1 (`prop3_9_nonpos`);
* `p > 0`: "cover `K` by finitely many Euclidean squares `S_1, …, S_n` contained in `U`" with
  bottom-left corners `u_k` and side lengths `ρ_k` (`exists_square_cover`); Proposition 3.10 and
  Axiom IV′ for each `𝕣S_k` (`diam_square_tail`); the Gaussian tail of `h_{𝕣ρ_k}(𝕣u_k) − h_𝕣(0)`
  and the comparison of `𝔠_{𝕣ρ_k}` with `𝔠_𝕣` (`ratio_upper_tail`). The paper combines these
  at the level of moments; we combine them at the level of tails (union bound) and then integrate
  the tail (`lintegral_rpow_le_of_tail`), the same route as Proposition 3.10 (T:1914–1915).
  The chaining over the cover is `internalDiam_le_two_sum` (the paper leaves it implicit).
-/

noncomputable section

open MeasureTheory Set Metric Complex
open scoped ENNReal ComplexOrder

namespace LQGMetric.DFGPS
open Blueprint

lemma unitSq_eq_box : unitSq = Ioo (0 : ℝ) 1 ×ℂ Ioo (0 : ℝ) 1 := by
  rw [unitSq_eq]; rfl

lemma isOpen_unitSq : IsOpen unitSq := by
  rw [unitSq_eq_box]; exact isOpen_Ioo.reProdIm isOpen_Ioo

lemma isOpen_scaleSet_of {r : ℝ} (hr : 0 < r) (z : ℂ) {A : Set ℂ} (hA : IsOpen A) :
    IsOpen (scaleSet r z A) := by
  have : scaleSet r z A = (fun w => (w - z) / (r : ℂ)) ⁻¹' A := by
    ext w; rw [mem_scaleSet_iff hr]; rfl
  rw [this]
  exact hA.preimage ((continuous_id.sub continuous_const).div_const _)

lemma scaleSet_scaleSet_zero (𝕣 ρ : ℝ) (u : ℂ) (A : Set ℂ) :
    scaleSet 𝕣 0 (scaleSet ρ u A) = scaleSet (𝕣 * ρ) ((𝕣 : ℂ) * u) A := by
  unfold scaleSet
  rw [image_image]
  congr 1
  funext x
  push_cast
  ring

/-- **Finite cover by squares** (T:1767): a compact `K ⊆ U` is covered by finitely many open
squares `u + ρ𝕊 ⊆ U` with `ρ ∈ (0,1)`. -/
lemma exists_square_cover {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (s : Finset K) (ρ : K → ℝ) (u : K → ℂ), (∀ i, 0 < ρ i ∧ ρ i < 1) ∧
      (∀ i, scaleSet (ρ i) (u i) unitSq ⊆ U) ∧ K ⊆ ⋃ i ∈ s, scaleSet (ρ i) (u i) unitSq := by
  have hx : ∀ x : K, ∃ ρ : ℝ, (0 < ρ ∧ ρ < 1) ∧
      scaleSet ρ ((x : ℂ) - ((ρ / 2 : ℝ) + (ρ / 2 : ℝ) * I)) unitSq ⊆ U ∧
      (x : ℂ) ∈ scaleSet ρ ((x : ℂ) - ((ρ / 2 : ℝ) + (ρ / 2 : ℝ) * I)) unitSq := by
    intro x
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x (hKU x.2)
    set ρ := min (δ / 2) (1 / 2) with hρ
    have hρ0 : 0 < ρ := lt_min (by linarith) (by norm_num)
    have hρδ : ρ ≤ δ / 2 := min_le_left _ _
    refine ⟨ρ, ⟨hρ0, (min_le_right _ _).trans_lt (by norm_num)⟩, fun w hw => hball ?_, ?_⟩
    · rw [unitSq_eq_box, mem_scaleSet_Ioo hρ0] at hw
      simp only [sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re,
        I_im] at hw
      rw [mem_ball, dist_eq_norm]
      refine (norm_le_abs_re_add_abs_im _).trans_lt ?_
      simp only [sub_re, sub_im]
      have h1 : |w.re - (x : ℂ).re| < ρ / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
      have h2 : |w.im - (x : ℂ).im| < ρ / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
      linarith
    · rw [unitSq_eq_box, mem_scaleSet_Ioo hρ0]
      simp only [sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re,
        I_im]
      refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  choose ρ hρ hsub hmem using hx
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun i : K => scaleSet (ρ i) ((i : ℂ) - ((ρ i / 2 : ℝ) + (ρ i / 2 : ℝ) * I)) unitSq)
    (fun i => isOpen_scaleSet_of (hρ i).1 _ isOpen_unitSq)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩)
  exact ⟨s, ρ, _, hρ, hsub, hs⟩

/-- `𝔠_𝕣⁻¹ e^{-ξh_𝕣(0)} = (𝔠_{𝕣ρ} e^{ξh_{𝕣ρ}(𝕣u)} / 𝔠_𝕣 e^{ξh_𝕣(0)}) · (𝔠_{𝕣ρ} e^{ξh_{𝕣ρ}(𝕣u)})⁻¹` -/
lemma ofReal_inv_eq_ratio_mul {N N' : ℝ} (hN : 0 < N) (hN' : 0 < N') :
    ENNReal.ofReal N⁻¹ = ENNReal.ofReal (N' / N) * ENNReal.ofReal N'⁻¹ := by
  rw [← ENNReal.ofReal_mul (div_pos hN' hN).le]
  congr 1
  field_simp

/-- **Tail of the normalized internal diameter of `𝕣K` in `𝕣U`** (proof of Prop 3.9,
T:1767–1775), canonical space, uniformly in `𝕣`, every exponent `a < 4d_γ/γ²`. -/
theorem diam_K_upper_tail (hT : DiamTailRS) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {μ : Measure DistC} [IsProbabilityMeasure μ] (hμ : IsNormalizedWPGFF id μ) {U K : Set ℂ}
    (hU : IsOpen U) (hK : IsCompact K) (hKc : IsConnected K) (hKU : K ⊆ U) {a : ℝ} (ha0 : 0 < a)
    (ha : a < 4 * dGamma γ / γ ^ 2) :
    ∃ C t₀ : ℝ, 1 ≤ t₀ ∧ 0 ≤ C ∧ ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ t : ℝ, t₀ ≤ t →
      μ {g | ENNReal.ofReal t < ENNReal.ofReal (scaleFac (xiGamma γ) c g 𝕣 0)⁻¹ *
          internalDiam (D g) (scaleSet 𝕣 0 K) (scaleSet 𝕣 0 U)} ≤ ENNReal.ofReal (C * t ^ (-a)) := by
  obtain ⟨s, ρ, u, hρ, hsub, hcov⟩ := exists_square_cover hU hK hKU
  set M := 4 * dGamma γ / γ ^ 2
  set a' := (a + M) / 2 with ha'
  have ha'a : a < a' := by rw [ha']; linarith
  have ha'M : a' < M := by rw [ha']; linarith
  have ha'0 : 0 < a' := by linarith
  set ε := 1 - a / a' with hε
  have hε0 : 0 < ε := by rw [hε, sub_pos, div_lt_one ha'0]; exact ha'a
  have hε1 : ε < 1 := by rw [hε]; have := div_pos ha0 ha'0; linarith
  have h1ε : (1 - ε) * a' = a := by rw [hε]; field_simp; ring
  set b := a / ε with hb
  have hb0 : 0 < b := div_pos ha0 hε0
  have hεb : ε * b = a := by rw [hb]; field_simp
  obtain ⟨C₁, t₁, hsq⟩ := diam_square_tail hT hγ0 hγ2 hD hμ ha'M
  have hrat := fun i : K => ratio_upper_tail hγ0 hD hμ (hρ i).1 (hρ i).2 (u i) hb0
  choose s₀ hs₀1 hs₀ using hrat
  set N : ℝ := (s.card : ℝ) + 1 with hN
  have hN1 : 1 ≤ N := by rw [hN]; linarith [(s.card.cast_nonneg : (0 : ℝ) ≤ s.card)]
  have hN0 : 0 < N := by linarith
  set S₀ := ∑ i ∈ s, s₀ i + 1 with hS₀
  have hS₀i : ∀ i ∈ s, s₀ i ≤ S₀ := fun i hi => by
    rw [hS₀]
    have := Finset.single_le_sum (f := s₀) (fun j _ => by linarith [hs₀1 j]) hi
    linarith
  have hS₀1 : 1 ≤ S₀ := by
    rw [hS₀]; have := Finset.sum_nonneg (s := s) fun j _ => (by linarith [hs₀1 j] : 0 ≤ s₀ j)
    linarith
  set T₁ := 2 * N * max t₁ 1 with hT₁
  have hT₁0 : 0 < T₁ := by positivity
  set t₀ := max (max (S₀ ^ (1 / ε)) (T₁ ^ (1 / (1 - ε)))) 1 with ht₀
  set C₂ := max C₁ 0 with hC₂
  refine ⟨N * (2 + C₂ * (2 * N) ^ a'), t₀, le_max_right _ _, by positivity, fun 𝕣 h𝕣 t ht => ?_⟩
  have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 < t := by linarith
  set σ := t ^ ε with hσ
  set τ := t ^ (1 - ε) / (2 * N) with hτ
  have hσ0 : 0 < σ := Real.rpow_pos_of_pos ht0 _
  have hσS : S₀ ≤ σ := by
    have h := Real.rpow_le_rpow (by positivity) ((le_max_left _ _).trans
      ((le_max_left _ _).trans ht)) hε0.le
    rwa [← Real.rpow_mul (by linarith), one_div_mul_cancel hε0.ne', Real.rpow_one] at h
  have hτt : t₁ ≤ τ := by
    have ht' : max (S₀ ^ (1 / ε)) (T₁ ^ (1 / (1 - ε))) ≤ t := (le_max_left _ _).trans ht
    have h := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans ht') (by linarith : 0 ≤ 1 - ε)
    rw [← Real.rpow_mul hT₁0.le, one_div_mul_cancel (by linarith), Real.rpow_one] at h
    rw [hτ, le_div_iff₀ (by positivity)]
    calc t₁ * (2 * N) ≤ max t₁ 1 * (2 * N) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = T₁ := by rw [hT₁]; ring
      _ ≤ _ := h
  have hστ : σ * τ = t / (2 * N) := by
    rw [hσ, hτ, mul_div_assoc', ← Real.rpow_add ht0]; norm_num
  -- the pointwise inclusion
  set R : K → DistC → ℝ := fun i g => scaleFac (xiGamma γ) c g (𝕣 * ρ i) ((𝕣 : ℂ) * u i) /
    scaleFac (xiGamma γ) c g 𝕣 0
  set Y : K → DistC → ℝ≥0∞ := fun i g =>
    ENNReal.ofReal (scaleFac (xiGamma γ) c g (𝕣 * ρ i) ((𝕣 : ℂ) * u i))⁻¹ *
      internalDiam (D g) (scaleSet (𝕣 * ρ i) ((𝕣 : ℂ) * u i) unitSq)
        (scaleSet (𝕣 * ρ i) ((𝕣 : ℂ) * u i) unitSq)
  have hincl : {g | ENNReal.ofReal t < ENNReal.ofReal (scaleFac (xiGamma γ) c g 𝕣 0)⁻¹ *
      internalDiam (D g) (scaleSet 𝕣 0 K) (scaleSet 𝕣 0 U)} ⊆
      ⋃ i ∈ s, ({g | σ < R i g} ∪ {g | ENNReal.ofReal τ < Y i g}) := by
    intro g hg
    simp only [mem_ofPred_eq] at hg
    by_contra hne
    simp only [mem_iUnion, mem_union, mem_ofPred_eq, not_exists, not_or, not_lt] at hne
    have hpos : ∀ r : ℝ, 0 < r → ∀ z : ℂ, 0 < scaleFac (xiGamma γ) c g r z :=
      fun r hr z => mul_pos (hD.tightness.1 r hr) (Real.exp_pos _)
    have hN₀ := hpos 𝕣 h𝕣 0
    have hchain := internalDiam_le_two_sum (D g) ((hKc.image _ (by fun_prop :
        Continuous fun x : ℂ => (𝕣 : ℂ) * x + 0).continuousOn).isPreconnected) s
      (fun i => scaleSet (𝕣 * ρ i) ((𝕣 : ℂ) * u i) unitSq)
      (fun i => isOpen_scaleSet_of (mul_pos h𝕣 (hρ i).1) _ isOpen_unitSq)
      (fun i _ => by rw [← scaleSet_scaleSet_zero]; exact image_mono (hsub i))
      (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := hx
        obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (hcov hy)
        refine mem_iUnion₂.2 ⟨i, hi, ?_⟩
        rw [← scaleSet_scaleSet_zero]
        exact mem_image_of_mem _ hyi)
    have hterm : ∀ i ∈ s, ENNReal.ofReal (scaleFac (xiGamma γ) c g 𝕣 0)⁻¹ *
        internalDiam (D g) (scaleSet (𝕣 * ρ i) ((𝕣 : ℂ) * u i) unitSq)
          (scaleSet (𝕣 * ρ i) ((𝕣 : ℂ) * u i) unitSq) ≤ ENNReal.ofReal (t / (2 * N)) := by
      intro i hi
      rw [ofReal_inv_eq_ratio_mul hN₀ (hpos _ (mul_pos h𝕣 (hρ i).1) ((𝕣 : ℂ) * u i)), mul_assoc,
        ← hστ, ENNReal.ofReal_mul hσ0.le]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hne i hi).1) (hne i hi).2
    have hsum : ENNReal.ofReal (scaleFac (xiGamma γ) c g 𝕣 0)⁻¹ *
        internalDiam (D g) (scaleSet 𝕣 0 K) (scaleSet 𝕣 0 U) ≤ ENNReal.ofReal t := by
      calc _ ≤ ENNReal.ofReal (scaleFac (xiGamma γ) c g 𝕣 0)⁻¹ *
            (2 * ∑ i ∈ s, internalDiam (D g) (scaleSet (𝕣 * ρ i) ((𝕣 : ℂ) * u i) unitSq)
              (scaleSet (𝕣 * ρ i) ((𝕣 : ℂ) * u i) unitSq)) := by gcongr; exact hchain
        _ = 2 * ∑ i ∈ s, ENNReal.ofReal (scaleFac (xiGamma γ) c g 𝕣 0)⁻¹ *
            internalDiam (D g) (scaleSet (𝕣 * ρ i) ((𝕣 : ℂ) * u i) unitSq)
              (scaleSet (𝕣 * ρ i) ((𝕣 : ℂ) * u i) unitSq) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        _ ≤ 2 * ∑ i ∈ s, ENNReal.ofReal (t / (2 * N)) :=
          by gcongr with i hi; exact hterm i hi
        _ = ENNReal.ofReal (2 * s.card * (t / (2 * N))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_mul (by norm_num), mul_assoc]
        _ ≤ ENNReal.ofReal t := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          have : (s.card : ℝ) ≤ N := by rw [hN]; linarith
          nlinarith
    exact absurd hg (not_lt.2 hsum)
  refine (measure_mono hincl).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hbd : ∀ i ∈ s, μ ({g | σ < R i g} ∪ {g | ENNReal.ofReal τ < Y i g}) ≤
      ENNReal.ofReal ((2 + C₂ * (2 * N) ^ a') * t ^ (-a)) := by
    intro i hi
    refine (measure_union_le _ _).trans ?_
    have h1 := hs₀ i 𝕣 h𝕣 σ ((hS₀i i hi).trans hσS)
    have h2 := hsq (𝕣 * ρ i) (mul_pos h𝕣 (hρ i).1) ((𝕣 : ℂ) * u i) τ hτt
    have e1 : σ ^ (-b) = t ^ (-a) := by
      rw [hσ, ← Real.rpow_mul ht0.le, mul_neg, hεb]
    have e2 : τ ^ (-a') = (2 * N) ^ a' * t ^ (-a) := by
      rw [hτ, Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul ht0.le,
        Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * N), mul_neg, h1ε]
      field_simp
    rw [e1] at h1
    rw [e2] at h2
    calc _ ≤ ENNReal.ofReal (2 * t ^ (-a)) + ENNReal.ofReal (C₁ * ((2 * N) ^ a' * t ^ (-a))) :=
          add_le_add h1 h2
      _ ≤ ENNReal.ofReal (2 * t ^ (-a)) + ENNReal.ofReal (C₂ * ((2 * N) ^ a' * t ^ (-a))) :=
          add_le_add le_rfl (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
            (le_max_left _ _) (by positivity)))
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
  calc _ ≤ ∑ i ∈ s, ENNReal.ofReal ((2 + C₂ * (2 * N) ^ a') * t ^ (-a)) := Finset.sum_le_sum hbd
    _ = ENNReal.ofReal (s.card * ((2 + C₂ * (2 * N) ^ a') * t ^ (-a))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hN]; linarith

/-- **DFGPS Proposition 3.9** from Proposition 3.1 and the tail bound of Proposition 3.10. -/
theorem prop3_9_of_tail (h31 : Prop3_1) (hT : DiamTailRS) : Prop3_9 := by
  intro γ hγ0 hγ2 D c hD U K hU hK hKc hKU hK1 p hp
  rcases le_or_gt p 0 with hp0 | hp0
  · exact prop3_9_nonpos h31 hγ0 hγ2 hD hK1 hp0
  obtain ⟨μ, hμP, hμ⟩ := exists_canonical_normGFF
  set a := (p + 4 * dGamma γ / γ ^ 2) / 2 with ha
  obtain ⟨C, t₀, ht₀, hC0, htail⟩ := diam_K_upper_tail hT hγ0 hγ2 hD hμ hU hK hKc hKU
    (a := a) (by rw [ha]; linarith) (by rw [ha]; linarith)
  refine ⟨momBd p a C t₀, fun P _ h hh 𝕣 h𝕣 => ?_⟩
  refine lintegral_rpow_le_of_tail P _ hp0 (by rw [ha]; linarith) hC0 ht₀ fun t ht => ?_
  exact (prob_le_canonical hμ P h hh _).trans (htail 𝕣 h𝕣 t ht)

end LQGMetric.DFGPS
