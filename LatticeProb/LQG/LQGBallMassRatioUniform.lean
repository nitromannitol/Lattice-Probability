import LatticeProb.LQG.LQGBallMassRatioTail
import LatticeProb.LQG.LQGBallMassRatioScaling
import LatticeProb.LQG.LQGBallMassGrid
import LatticeProb.LQG.GMCDyadicLimit

/-!
# A uniform lower bound for the ratio of concentric LQG ball masses

Let `μ` be the `γ`-Liouville quantum gravity measure of a whole-plane Gaussian free field, with `γ ∈ (0, 2)`.
For `c ∈ (0, 1)`, `ζ > 0` and `R > 0`, with polynomially high probability as `δ → 0`,
`δ^{γ²/2 + ζ} μ(B_δ(z)) ≤ μ(B_{cδ}(z))` for every `z ∈ B_R(0)`. This is the concentric form of
Berestycki and Gwynne (arXiv:2003.10320, Lemma A.2) for the whole-plane field.

The proof covers `B_R(0)` by a grid of spacing `c 2^{-j}/64` with `2^{-j}/16 < δ ≤ 2^{-j}/8`. For a grid point `x`
within that spacing of `z`, `B_δ(z) ⊆ B_{2^{-j}/4}(x)` and `B_{2^{-j} c/32}(x) ⊆ B_{cδ}(z)`, so a bad centre `z`
gives a bad concentric ratio at a grid point. By the exact dyadic scaling of the field, that ratio has the law of
`μ'(B(0, 1/4)) / μ'(B(0, c/32))` for the LQG measure `μ'` of a recentred whole-plane field, whose tail is
`O(t^{-p'})` for every `p' < 4/γ²`, uniformly over the models. The grid has `O(δ⁻²)` points and the choice
`t = δ^{-(γ²/2 + ζ)}` gives a failure probability `O(δ^{(γ²/2 + ζ) p' - 2})` with a positive exponent once `p'` is
close to `4/γ²`.

## Main results

* `exists_ball_grid`: a finite set of `(4R/s + 1)²` points at distance `< s` from every point of `B_R(0)`.
* `polyHighProb_ball_ratio_of_tail`: the union bound, from a concentric ratio tail at every centre and scale.
* `polyHighProb_ball_ratio`: the uniform concentric ratio bound for the whole-plane LQG measure.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal NNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LatticeProb.LQG.LQGDyadicScaling

namespace LQGBallMassRatioUniform

/-- A finite grid of `(4R/s + 1)²` points such that every point of `B_R(0)` is at distance `< s` from the grid. -/
theorem exists_ball_grid {R s : ℝ} (hR : 0 < R) (hs : 0 < s) :
    ∃ G : Finset ℂ, (G.card : ℝ) ≤ (4 * R / s + 1) ^ 2 ∧
      ∀ z ∈ ball (0 : ℂ) R, ∃ x ∈ G, dist z x < s := by
  set e : ℝ := s / 2 with he
  have he0 : 0 < e := half_pos hs
  set n : ℕ := ⌊2 * R / e⌋₊ with hn
  let g : ℕ × ℕ → ℂ := fun q => ⟨-R + q.1 * e, -R + q.2 * e⟩
  refine ⟨(Finset.range (n + 1) ×ˢ Finset.range (n + 1)).image g, ?_, ?_⟩
  · have hcard := Finset.card_image_le (s := Finset.range (n + 1) ×ˢ Finset.range (n + 1)) (f := g)
    rw [Finset.card_product, Finset.card_range] at hcard
    have hn1 : ((n : ℝ) + 1) ≤ 4 * R / s + 1 := by
      have := Nat.floor_le (a := 2 * R / e) (by positivity)
      have h2 : 2 * R / e = 4 * R / s := by rw [he]; field_simp; ring
      linarith
    calc ((Finset.image g _).card : ℝ) ≤ ((n + 1) * (n + 1) : ℕ) := by exact_mod_cast hcard
      _ = ((n : ℝ) + 1) ^ 2 := by push_cast; ring
      _ ≤ (4 * R / s + 1) ^ 2 := by gcongr
  · intro z hz
    rw [mem_ball, dist_zero_right] at hz
    have key : ∀ y : ℝ, |y| < R → ⌊(y + R) / e⌋₊ < n + 1 ∧ 0 ≤ y + R - ⌊(y + R) / e⌋₊ * e ∧
        y + R - ⌊(y + R) / e⌋₊ * e < e := by
      intro y hy
      have hy0 : 0 ≤ y + R := by linarith [neg_abs_le y]
      have hy1 : y + R ≤ 2 * R := by linarith [le_abs_self y]
      refine ⟨Nat.lt_succ_of_le (Nat.floor_le_floor (div_le_div_of_nonneg_right hy1 he0.le)), ?_, ?_⟩
      · have := Nat.floor_le (div_nonneg hy0 he0.le)
        have h2 : (⌊(y + R) / e⌋₊ : ℝ) * e ≤ (y + R) / e * e := by gcongr
        rw [div_mul_cancel₀ _ he0.ne'] at h2
        linarith
      · have := Nat.lt_floor_add_one ((y + R) / e)
        have h2 : (y + R) / e * e < ((⌊(y + R) / e⌋₊ : ℝ) + 1) * e := by gcongr
        rw [div_mul_cancel₀ _ he0.ne'] at h2
        linarith
    obtain ⟨hi, hi0, hi1⟩ := key z.re (lt_of_le_of_lt (Complex.abs_re_le_norm z) hz)
    obtain ⟨hk, hk0, hk1⟩ := key z.im (lt_of_le_of_lt (Complex.abs_im_le_norm z) hz)
    refine ⟨g (⌊(z.re + R) / e⌋₊, ⌊(z.im + R) / e⌋₊), Finset.mem_image_of_mem _ ?_, ?_⟩
    · exact Finset.mem_product.2 ⟨Finset.mem_range.2 hi, Finset.mem_range.2 hk⟩
    · rw [dist_eq_norm]
      refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
      simp only [g, Complex.sub_re, Complex.sub_im]
      have h1 : z.re - (-R + (⌊(z.re + R) / e⌋₊ : ℝ) * e) = z.re + R - ⌊(z.re + R) / e⌋₊ * e := by ring
      have h2 : z.im - (-R + (⌊(z.im + R) / e⌋₊ : ℝ) * e) = z.im + R - ⌊(z.im + R) / e⌋₊ * e := by ring
      rw [h1, h2, abs_of_nonneg hi0, abs_of_nonneg hk0]
      linarith

/-- **Union bound for the concentric ratio.** Suppose that at every centre `x` and dyadic scale `2^{-j}`,
`t μ(B(x, 2^{-j} c/32)) < μ(B(x, 2^{-j}/4))` has probability at most `C t^{-p'}` for `t ≥ 1`. If `a p' > 2`,
then with polynomially high probability as `δ → 0`, `δ^a μ(B_δ(z)) ≤ μ(B_{cδ}(z))` for every `z ∈ B_R(0)`. -/
theorem polyHighProb_ball_ratio_of_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : Ω → Measure ℂ} {a c R p' : ℝ} {C : ℝ≥0} (hc0 : 0 < c) (hc1 : c < 1) (hR : 0 < R)
    (ha : 0 ≤ a) (hap : 2 < a * p')
    (htail : ∀ (j : ℕ) (x : ℂ) (t : ℝ), 1 ≤ t →
      P {ω | ENNReal.ofReal t * μ ω (ball x (dyadicScale j * (c / 32))) <
        μ ω (ball x (dyadicScale j * (1 / 4)))} ≤ C * ENNReal.ofReal (t ^ (-p'))) :
    PolyHighProb P fun δ => {ω | ∀ z ∈ ball (0 : ℂ) R,
      ENNReal.ofReal (δ ^ a) * μ ω (ball z δ) ≤ μ ω (ball z (c * δ))} := by
  refine ⟨a * p' - 2, by linarith, (32 * R / c + 1) ^ 2 * C, 1 / 8, by norm_num, ?_⟩
  intro δ hδ hδ8
  have hδ1 : δ ≤ 1 := by linarith
  -- the dyadic scale `D = 2^{-n}` with `D/16 < δ ≤ D/8`
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one (x := 8 * δ) (y := (2 : ℝ)⁻¹)
    (by positivity) (by linarith) (by norm_num) (by norm_num)
  set D : ℝ := dyadicScale n with hD
  have hDdef : D = (2 : ℝ)⁻¹ ^ n := rfl
  have hD0 : 0 < D := by rw [hDdef]; positivity
  have h8 : 8 * δ ≤ D := by rw [hDdef]; exact hn2
  have h16 : D < 16 * δ := by
    have h' : D * (2 : ℝ)⁻¹ < 8 * δ := by rw [hDdef, ← pow_succ]; exact hn1
    have h'' : D * (2 : ℝ)⁻¹ = D / 2 := by ring
    linarith
  set s : ℝ := c * D / 64 with hs
  have hs0 : 0 < s := by positivity
  obtain ⟨G, hGcard, hGcov⟩ := exists_ball_grid hR hs0
  set t : ℝ := δ ^ (-a) with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hta : ENNReal.ofReal (δ ^ a) * ENNReal.ofReal t = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ht, Real.rpow_neg hδ.le,
      mul_inv_cancel₀ (Real.rpow_pos_of_pos hδ a).ne', ENNReal.ofReal_one]
  have hsub : {ω | ∀ z ∈ ball (0 : ℂ) R,
      ENNReal.ofReal (δ ^ a) * μ ω (ball z δ) ≤ μ ω (ball z (c * δ))}ᶜ ⊆
      ⋃ x ∈ G, {ω | ENNReal.ofReal t * μ ω (ball x (dyadicScale n * (c / 32))) <
        μ ω (ball x (dyadicScale n * (1 / 4)))} := by
    intro ω hω
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_le, exists_prop] at hω
    obtain ⟨z, hz, hlt⟩ := hω
    obtain ⟨x, hxG, hzx⟩ := hGcov z hz
    refine mem_iUnion₂.2 ⟨x, hxG, ?_⟩
    have hb1 : ball z δ ⊆ ball x (D * (1 / 4)) := by
      intro y hy
      rw [mem_ball] at hy ⊢
      have := dist_triangle y z x
      have hcD : c * D < 1 * D := mul_lt_mul_of_pos_right hc1 hD0
      have hsD : s < D / 64 := by rw [hs]; linarith
      linarith
    have hb2 : ball x (D * (c / 32)) ⊆ ball z (c * δ) := by
      intro y hy
      rw [mem_ball] at hy ⊢
      have := dist_triangle y x z
      rw [dist_comm x z] at this
      have hcD : c * D < c * (16 * δ) := mul_lt_mul_of_pos_left h16 hc0
      nlinarith
    by_contra hnot
    have hge := not_lt.1 (show ¬(ENNReal.ofReal t * μ ω (ball x (dyadicScale n * (c / 32))) <
      μ ω (ball x (dyadicScale n * (1 / 4)))) from hnot)
    have hcalc : ENNReal.ofReal (δ ^ a) * μ ω (ball z δ) ≤ μ ω (ball z (c * δ)) :=
      calc ENNReal.ofReal (δ ^ a) * μ ω (ball z δ)
          ≤ ENNReal.ofReal (δ ^ a) * μ ω (ball x (D * (1 / 4))) := mul_le_mul' le_rfl (measure_mono hb1)
        _ ≤ ENNReal.ofReal (δ ^ a) * (ENNReal.ofReal t * μ ω (ball x (D * (c / 32)))) :=
            mul_le_mul' le_rfl hge
        _ = μ ω (ball x (D * (c / 32))) := by rw [← mul_assoc, hta, one_mul]
        _ ≤ μ ω (ball z (c * δ)) := measure_mono hb2
    exact absurd hcalc (not_le.2 hlt)
  -- the real bound
  have htp : t ^ (-p') = δ ^ (a * p') := by
    rw [ht, ← Real.rpow_mul hδ.le, neg_mul_neg]
  have hsplit : δ ^ (a * p') = δ ^ (a * p' - 2) * δ ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hδ]
    congr 1
    ring
  have hcardδ : (G.card : ℝ) * δ ^ 2 ≤ (32 * R / c + 1) ^ 2 := by
    have hsge : c * δ / 8 ≤ s := by
      rw [hs]
      have := mul_le_mul_of_nonneg_left h8 hc0.le
      linarith
    have h4 : 4 * R / s ≤ 32 * R / (c * δ) := by
      rw [div_le_div_iff₀ hs0 (by positivity)]
      have := mul_le_mul_of_nonneg_left hsge (by positivity : (0 : ℝ) ≤ 32 * R)
      linarith
    have h5 : (4 * R / s + 1) * δ ≤ 32 * R / c + 1 := by
      have h6 : 32 * R / (c * δ) * δ = 32 * R / c := by field_simp
      have := mul_le_mul_of_nonneg_right h4 hδ.le
      nlinarith
    calc (G.card : ℝ) * δ ^ 2 ≤ (4 * R / s + 1) ^ 2 * δ ^ 2 :=
          mul_le_mul_of_nonneg_right hGcard (by positivity)
      _ = ((4 * R / s + 1) * δ) ^ 2 := by ring
      _ ≤ (32 * R / c + 1) ^ 2 := by gcongr
  calc P {ω | ∀ z ∈ ball (0 : ℂ) R,
        ENNReal.ofReal (δ ^ a) * μ ω (ball z δ) ≤ μ ω (ball z (c * δ))}ᶜ
      ≤ P (⋃ x ∈ G, {ω | ENNReal.ofReal t * μ ω (ball x (dyadicScale n * (c / 32))) <
          μ ω (ball x (dyadicScale n * (1 / 4)))}) := measure_mono hsub
    _ ≤ ∑ x ∈ G, P {ω | ENNReal.ofReal t * μ ω (ball x (dyadicScale n * (c / 32))) <
          μ ω (ball x (dyadicScale n * (1 / 4)))} := measure_biUnion_finset_le G _
    _ ≤ ∑ _x ∈ G, (C : ℝ≥0∞) * ENNReal.ofReal (t ^ (-p')) :=
          Finset.sum_le_sum fun x _ => htail n x t ht1
    _ = ENNReal.ofReal ((G.card : ℝ) * ((C : ℝ) * t ^ (-p'))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_coe_nnreal,
            ← ENNReal.ofReal_mul C.coe_nonneg, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal ((32 * R / c + 1) ^ 2 * (C : ℝ) * δ ^ (a * p' - 2)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [htp, hsplit]
          have hC0 : (0 : ℝ) ≤ C := C.coe_nonneg
          have hq : 0 ≤ δ ^ (a * p' - 2) := Real.rpow_nonneg hδ.le _
          calc (G.card : ℝ) * ((C : ℝ) * (δ ^ (a * p' - 2) * δ ^ 2))
              = ((G.card : ℝ) * δ ^ 2) * ((C : ℝ) * δ ^ (a * p' - 2)) := by ring
            _ ≤ (32 * R / c + 1) ^ 2 * ((C : ℝ) * δ ^ (a * p' - 2)) :=
                mul_le_mul_of_nonneg_right hcardδ (by positivity)
            _ = (32 * R / c + 1) ^ 2 * (C : ℝ) * δ ^ (a * p' - 2) := by ring

/-- **Uniform concentric ratio of LQG ball masses** (whole-plane form of Berestycki-Gwynne, Lemma A.2). For the
`γ`-LQG measure `μ` of a whole-plane Gaussian free field, `γ ∈ (0, 2)`, `c ∈ (0, 1)`, `ζ > 0` and `R > 0`: with
polynomially high probability as `δ → 0`, `δ^{γ²/2 + ζ} μ(B_δ(z)) ≤ μ(B_{cδ}(z))` for every `z ∈ B_R(0)`. -/
theorem polyHighProb_ball_ratio {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ c ζ R : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hc0 : 0 < c) (hc1 : c < 1) (hζ : 0 < ζ) (hR : 0 < R)
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ) :
    PolyHighProb P fun δ => {ω | ∀ z ∈ ball (0 : ℂ) R,
      ENNReal.ofReal (δ ^ (γ ^ 2 / 2 + ζ)) * μ ω (ball z δ) ≤ μ ω (ball z (c * δ))} := by
  have hγsq : 0 < γ ^ 2 := by positivity
  have hγ4 : γ ^ 2 < 4 := by nlinarith
  have hlo : 4 / (γ ^ 2 + 2 * ζ) < 4 / γ ^ 2 :=
    div_lt_div_of_pos_left four_pos hγsq (by linarith)
  set p' : ℝ := (4 / (γ ^ 2 + 2 * ζ) + 4 / γ ^ 2) / 2 with hp'
  have hp'lo : 4 / (γ ^ 2 + 2 * ζ) < p' := by rw [hp']; linarith
  have hp'hi : p' < 4 / γ ^ 2 := by rw [hp']; linarith
  have hp'0 : 0 < p' := lt_trans (by positivity) hp'lo
  have h1 : (1 : ℝ) < 4 / γ ^ 2 := by rw [lt_div_iff₀ hγsq]; linarith
  have hmax : max p' 1 < 4 / γ ^ 2 := max_lt hp'hi h1
  set p : ℝ := (max p' 1 + 4 / γ ^ 2) / 2 with hp
  have hp1 : 1 ≤ p := by rw [hp]; linarith [le_max_right p' 1]
  have hp'p : p' < p := by rw [hp]; linarith [le_max_left p' 1]
  have hpγ : p * γ ^ 2 < 4 := by
    have : p < 4 / γ ^ 2 := by rw [hp]; linarith
    rwa [lt_div_iff₀ hγsq] at this
  have hap : 2 < (γ ^ 2 / 2 + ζ) * p' := by
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < γ ^ 2 + 2 * ζ)).1 hp'lo
    nlinarith
  obtain ⟨C, hC⟩ := LQGBallMassRatioTail.measure_mul_ball_lt_ball_le_of_lt hγ0 hγ2
    (c := c / 32) (by positivity) hp1 hpγ hp'0 hp'p
  refine polyHighProb_ball_ratio_of_tail (C := C) hc0 hc1 hR (by positivity) hap ?_
  intro j x t ht
  obtain ⟨hC', hh'⟩ := isWholePlaneGFF_recentredField hh j x
  obtain ⟨μ', hμ'⟩ := hh'.exists_isLQGMeasure hγ0 hγ2
  rw [measure_mul_ball_lt_ball_eq hγ0 hμ j x hμ' _ (by positivity) (by norm_num)]
  exact hC Ω P hC' (recentredField hcirc j x) μ' hh' hμ' t ht

end LQGBallMassRatioUniform

end LatticeProb.LQG
