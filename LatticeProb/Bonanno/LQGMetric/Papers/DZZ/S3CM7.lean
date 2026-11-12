/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3CM7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P317B

/-!
# DZZ Proposition 3.17 from crude moments for small `δ` (P2-DZZCM)

`DZZCrudeMoments` (S3P317A) asks the second-moment bounds `E X² ≤ K (log δ⁻¹)²` for **all**
`δ ∈ (0,1)`. This is false as `δ → 1`: the right side tends to `0`, while e.g. for the constant
pair `{(1/4,1/4)}, {(3/4,3/4)}` the root box `𝕍` splits with probability
`≥ P(M_{γ,1}(𝕍) ≥ 1) > 0`, and then `D' ≥ 2`, `log D' ≥ log 2`; likewise `D ≥ 2` when the
mass of the region between `u` and `v` exceeds `δ²` (positive probability). DZZ
(l. 849–857) state the bounds as `O_γ(1)` for `(log D / log δ⁻¹)²`, i.e. for small `δ` only,
which is all that Corollary 3.3 and Proposition 3.17 use. We therefore use

* **`DZZCrudeMomentsEv`**: the same bounds for `δ ∈ (0, δ₁)`, `δ₁ > 0` depending on the pair;
* `abs_integral_sub_le_of_highProb_ev`: `abs_integral_sub_le_of_highProb` (S3L12Cor33) under
  these hypotheses (cut-off `X δ = 0` for `δ ≥ δ₁`);
* **`dzzProp317_of_approxEv`**: `dzzProp317_of_approx` (S3P317B) with `DZZCrudeMomentsEv`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **(eq-very-crude), (eq-very-crude-prime)** (DZZ l. 849–857) for `ξ`-admissible pairs, for
small `δ` (the corrected form of `DZZCrudeMoments`). -/
def DZZCrudeMomentsEv (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ)
    (ξ : ℝ) : Prop :=
  ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B → ∃ K δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₁,
    (MemLp (fun ω => logMinLGD (μ ω) δ (A δ) (B δ)) 2 P ∧
      ∫ ω, logMinLGD (μ ω) δ (A δ) (B δ) ^ 2 ∂P ≤ K * Real.log δ⁻¹ ^ 2) ∧
    (MemLp (fun ω => logApproxLGD γ W δ (A δ) (B δ) ω) 2 P ∧
      ∫ ω, logApproxLGD γ W δ (A δ) (B δ) ω ^ 2 ∂P ≤ K * Real.log δ⁻¹ ^ 2)

/-- **`abs_integral_sub_le_of_highProb` with moment bounds for `δ < δ₁` only** -/
theorem abs_integral_sub_le_of_highProb_ev {P : Measure Ω} [IsProbabilityMeasure P]
    {E : ℝ → Set Ω} {X Y : ℝ → Ω → ℝ} {C K δ₁ : ℝ} (hC : 0 ≤ C) (hgood : HighProb P E)
    (hE : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ ω ∈ E δ, |X δ ω - Y δ ω| ≤ C * Real.log δ⁻¹ ^ (0.9 : ℝ))
    (hδ₁ : 0 < δ₁)
    (hX : ∀ δ ∈ Ioo (0 : ℝ) δ₁, MemLp (X δ) 2 P ∧ ∫ ω, X δ ω ^ 2 ∂P ≤ K * Real.log δ⁻¹ ^ 2)
    (hY : ∀ δ ∈ Ioo (0 : ℝ) δ₁, MemLp (Y δ) 2 P ∧ ∫ ω, Y δ ω ^ 2 ∂P ≤ K * Real.log δ⁻¹ ^ 2) :
    ∃ K' δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      |(∫ ω, X δ ω ∂P) - ∫ ω, Y δ ω ∂P| ≤ K' * Real.log δ⁻¹ ^ (0.9 : ℝ) := by
  classical
  set X' : ℝ → Ω → ℝ := fun δ => if δ < δ₁ then X δ else 0 with hX'
  set Y' : ℝ → Ω → ℝ := fun δ => if δ < δ₁ then Y δ else 0 with hY'
  have hL : ∀ δ ∈ Ioo (0 : ℝ) 1, 0 ≤ Real.log δ⁻¹ := fun δ hδ =>
    Real.log_nonneg ((one_le_inv₀ hδ.1).2 hδ.2.le)
  have hmom : ∀ (Z : ℝ → Ω → ℝ), (∀ δ ∈ Ioo (0 : ℝ) δ₁, MemLp (Z δ) 2 P ∧
      ∫ ω, Z δ ω ^ 2 ∂P ≤ K * Real.log δ⁻¹ ^ 2) → ∀ δ ∈ Ioo (0 : ℝ) 1,
      MemLp ((fun δ => if δ < δ₁ then Z δ else 0) δ) 2 P ∧
      ∫ ω, (fun δ => if δ < δ₁ then Z δ else 0) δ ω ^ 2 ∂P ≤ max K 0 * Real.log δ⁻¹ ^ 2 := by
    intro Z hZ δ hδ
    by_cases h : δ < δ₁
    · simp only [if_pos h]
      exact ⟨(hZ δ ⟨hδ.1, h⟩).1, (hZ δ ⟨hδ.1, h⟩).2.trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩
    · simp only [if_neg h]
      refine ⟨MemLp.zero, ?_⟩
      simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        integral_zero]
      exact mul_nonneg (le_max_right _ _) (sq_nonneg _)
  have hE' : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ ω ∈ E δ, |X' δ ω - Y' δ ω| ≤
      C * Real.log δ⁻¹ ^ (0.9 : ℝ) := by
    intro δ hδ ω hω
    by_cases h : δ < δ₁
    · simp only [hX', hY', if_pos h]; exact hE δ hδ ω hω
    · simp only [hX', hY', if_neg h, Pi.zero_apply, sub_zero, abs_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (hL δ hδ) _)
  obtain ⟨K', δ₀, hδ₀, hK'⟩ := abs_integral_sub_le_of_highProb hC hgood hE' (hmom X hX)
    (hmom Y hY)
  refine ⟨K', min δ₀ δ₁, lt_min hδ₀ hδ₁, fun δ hδ => ?_⟩
  have h := hK' δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩
  have hlt : δ < δ₁ := hδ.2.trans_le (min_le_right _ _)
  simpa only [hX', hY', if_pos hlt] using h

set_option maxHeartbeats 1000000 in
/-- **DZZ Proposition 3.17 from Proposition 3.2, the crude moments for small `δ` and the
concentration of `D'`** (DZZ l. 1526–1530, 1627–1630): `dzzProp317_of_approx` (P2-DZZ32G,
S3P317B) with `DZZCrudeMoments` weakened to `DZZCrudeMomentsEv`; the proof is a copy of it. -/
theorem dzzProp317_of_approxEv {P : Measure Ω} [IsProbabilityMeasure P] {γ ξ : ℝ}
    {W : WNSpace → Ω → ℝ} {μ : Ω → Measure ℂ} (h32 : DZZProp32U P γ W μ ξ ξ)
    (hmom : DZZCrudeMomentsEv P γ W μ ξ) (hconc : DZZConcApprox P γ W ξ) :
    DZZProp317 P μ ξ := by
  obtain ⟨c₃, hc₃, δ₁, hδ₁, hb⟩ := h32
  obtain ⟨c, hc, hcA⟩ := hconc
  set c' := min (c / 4) c₃ with hc'
  have hc'0 : 0 < c' := lt_min (by positivity) hc₃
  refine ⟨c' / 2, by positivity, fun A B hAB => ?_⟩
  have hAB' := isXiAdmissible_iff.1 hAB
  -- Prop 3.2 and the Cor 3.3 step for the pair
  have hclose : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ ω ∈ prop32Event γ W μ δ (A δ) (B δ),
      |logMinLGD (μ ω) δ (A δ) (B δ) - logApproxLGD γ W δ (A δ) (B δ) ω| ≤
        1 * Real.log δ⁻¹ ^ (0.9 : ℝ) := fun δ hδ ω hω => by
    simpa [logMinLGD, logApproxLGD] using abs_log_toNat_sub_le (Real.rpow_nonneg (Real.log_nonneg
      ((one_le_inv₀ hδ.1).mpr hδ.2.le)) _) hω.1 hω.2
  have hP32 : ∀ δ ∈ Ioo (0 : ℝ) (min δ₁ 1),
      P (prop32Event γ W μ δ (A δ) (B δ))ᶜ ≤ ENNReal.ofReal (δ ^ c₃) := fun δ hδ =>
    hb δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩ _ _
      (hAB' δ ⟨hδ.1, hδ.2.trans_le (min_le_right _ _)⟩)
  have hgood : HighProb P (fun δ => prop32Event γ W μ δ (A δ) (B δ)) :=
    ⟨c₃, hc₃, min δ₁ 1, by positivity, hP32⟩
  obtain ⟨K, δ₆, hδ₆, hK⟩ := hmom A B hAB
  obtain ⟨K', δ₂, hδ₂, hK'⟩ := abs_integral_sub_le_of_highProb_ev
    (X := fun δ ω => logMinLGD (μ ω) δ (A δ) (B δ))
    (Y := fun δ ω => logApproxLGD γ W δ (A δ) (B δ) ω) zero_le_one hgood hclose hδ₆
    (fun δ hδ => (hK δ hδ).1) (fun δ hδ => (hK δ hδ).2)
  set K₀ := max K' 0 with hK₀
  obtain ⟨h1, c₂, hc₂, δ₅, hδ₅, h2⟩ := hcA A B hAB
  refine ⟨fun ι hι => ?_, ?_⟩
  · -- (eq-concentration-1)
    obtain ⟨δ₃, hδ₃, h3⟩ := h1 (ι / 2) ⟨by linarith [hι.1], by linarith [hι.2]⟩
    obtain ⟨δ₄, hδ₄, h4⟩ := exists_delta_of_eventually
      (ev_rpow_le (show (0.9 : ℝ) < 1 by norm_num) (show 0 < ι / 2 by linarith [hι.1]) (1 + K₀))
    have hι2 : 0 < c' * ι ^ 2 := by have := hι.1; positivity
    refine ⟨min (min (min δ₁ 1) δ₂) (min (min δ₃ δ₄) ((1 / 2) ^ (2 / (c' * ι ^ 2)))),
      by positivity, fun δ hδ => ?_⟩
    have hδ0 : 0 < δ := hδ.1
    have hm := hδ.2
    simp only [lt_min_iff] at hm
    obtain ⟨⟨⟨hδa, hδb⟩, hδc⟩, ⟨hδd, hδe⟩, hδf⟩ := hm
    have hδ1 : δ < 1 := hδb
    set L := Real.log δ⁻¹ with hL
    have hsub : (conc1Event μ P δ ι (A δ) (B δ))ᶜ ⊆ (prop32Event γ W μ δ (A δ) (B δ))ᶜ ∪
        {ω | |logApproxLGD γ W δ (A δ) (B δ) ω -
          ∫ ω', logApproxLGD γ W δ (A δ) (B δ) ω' ∂P| ≤ ι / 2 * L}ᶜ := by
      intro ω hω
      by_contra hc
      simp only [mem_union, mem_compl_iff, not_or, not_not] at hc
      apply hω
      have e1 := hclose δ ⟨hδ0, hδ1⟩ ω hc.1
      have e3 : |(∫ ω', logMinLGD (μ ω') δ (A δ) (B δ) ∂P) -
          ∫ ω', logApproxLGD γ W δ (A δ) (B δ) ω' ∂P| ≤ K₀ * L ^ (0.9 : ℝ) :=
        (hK' δ ⟨hδ0, hδc⟩).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (Real.log_nonneg ((one_le_inv₀ hδ0).mpr hδ1.le)) _))
      have e4 := h4 δ ⟨hδ0, hδe⟩
      rw [Real.rpow_one] at e4
      have := abs_sub_int_le e1 hc.2 e3
      show |logMinLGD (μ ω) δ (A δ) (B δ) - ∫ ω', logMinLGD (μ ω') δ (A δ) (B δ) ∂P| ≤ ι * L
      linarith
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add (hP32 δ ⟨hδ0, lt_min hδa hδb⟩) (h3 δ ⟨hδ0, hδd⟩)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hι1 : ι ^ 2 ≤ 1 := by
      have := hι.1; have := hι.2; nlinarith
    have m1 : δ ^ c₃ ≤ δ ^ (c' * ι ^ 2) := by
      refine Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le ?_
      calc c' * ι ^ 2 ≤ c' * 1 := mul_le_mul_of_nonneg_left hι1 hc'0.le
        _ ≤ c₃ := by rw [mul_one]; exact min_le_right _ _
    have m2 : δ ^ (c * (ι / 2) ^ 2) ≤ δ ^ (c' * ι ^ 2) := by
      refine Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le ?_
      have : c' ≤ c / 4 := min_le_left _ _
      have : 0 ≤ ι ^ 2 := sq_nonneg _
      nlinarith
    have hhalf : δ ^ (c' * ι ^ 2 / 2) ≤ 1 / 2 := by
      have := Real.rpow_le_rpow hδ0.le hδf.le (by positivity : 0 ≤ c' * ι ^ 2 / 2)
      rwa [← Real.rpow_mul (by norm_num), show 2 / (c' * ι ^ 2) * (c' * ι ^ 2 / 2) = 1 by
        rw [div_mul_div_comm, mul_comm 2 (c' * ι ^ 2), div_self (by positivity)],
        Real.rpow_one] at this
    have hsplit : δ ^ (c' * ι ^ 2) = δ ^ (c' * ι ^ 2 / 2) * δ ^ (c' * ι ^ 2 / 2) := by
      rw [← Real.rpow_add hδ0]; ring_nf
    have e : c' / 2 * ι ^ 2 = c' * ι ^ 2 / 2 := by ring
    rw [e]
    have : 0 ≤ δ ^ (c' * ι ^ 2 / 2) := by positivity
    nlinarith
  · -- (eq-concentration-2)
    have ev1 := ev_rpow_le (show (0.94 : ℝ) < 0.95 by norm_num) one_pos (2 + K₀)
    have ev2 := ev_rpow_le (show (0.7 : ℝ) < 1 by norm_num) (show 0 < c₃ / 2 by positivity) 1
    have ev3 := ev_rpow_le (show (0 : ℝ) < 1 by norm_num) (show 0 < c₃ / 2 by positivity) 1
    have ev4 := ev_rpow_le (show (0.7 : ℝ) < 0.8 by norm_num) (show 0 < c₂ / 2 by positivity) 1
    have ev5 := ev_rpow_le (show (0 : ℝ) < 0.8 by norm_num) (show 0 < c₂ / 2 by positivity) 1
    obtain ⟨δ₄, hδ₄, h4⟩ := exists_delta_of_eventually
      (ev1.and (ev2.and (ev3.and (ev4.and (ev5.and (eventually_ge_atTop (1 : ℝ)))))))
    refine ⟨min (min (min δ₁ 1) δ₂) (min δ₅ δ₄), by positivity, fun δ hδ => ?_⟩
    have hδ0 : 0 < δ := hδ.1
    have hm := hδ.2
    simp only [lt_min_iff] at hm
    obtain ⟨⟨⟨hδa, hδb⟩, hδc⟩, hδd, hδe⟩ := hm
    have hδ1 : δ < 1 := hδb
    set L := Real.log δ⁻¹ with hL
    obtain ⟨f1, f2, f3, f4, f5, hL1⟩ := h4 δ ⟨hδ0, hδe⟩
    rw [Real.rpow_zero] at f3 f5
    rw [Real.rpow_one] at f2 f3
    have hL0 : 0 ≤ L := by linarith
    have hsub : (conc2Event μ P δ (A δ) (B δ))ᶜ ⊆ (prop32Event γ W μ δ (A δ) (B δ))ᶜ ∪
        {ω | |logApproxLGD γ W δ (A δ) (B δ) ω -
          ∫ ω', logApproxLGD γ W δ (A δ) (B δ) ω' ∂P| ≤ L ^ (0.94 : ℝ)}ᶜ := by
      intro ω hω
      by_contra hc
      simp only [mem_union, mem_compl_iff, not_or, not_not] at hc
      apply hω
      have e1 := hclose δ ⟨hδ0, hδ1⟩ ω hc.1
      have e3 : |(∫ ω', logMinLGD (μ ω') δ (A δ) (B δ) ∂P) -
          ∫ ω', logApproxLGD γ W δ (A δ) (B δ) ω' ∂P| ≤ K₀ * L ^ (0.9 : ℝ) :=
        (hK' δ ⟨hδ0, hδc⟩).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg hL0 _))
      have hmono : L ^ (0.9 : ℝ) ≤ L ^ (0.94 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      have hK0 : 0 ≤ K₀ := le_max_right _ _
      have := abs_sub_int_le e1 hc.2 e3
      show |logMinLGD (μ ω) δ (A δ) (B δ) - ∫ ω', logMinLGD (μ ω') δ (A δ) (B δ) ∂P| ≤
        L ^ (0.95 : ℝ)
      nlinarith
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add (hP32 δ ⟨hδ0, lt_min hδa hδb⟩) (h2 δ ⟨hδ0, hδd⟩)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [rpow_eq_exp_log_inv hδ0, ← hL]
    have hlog2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have g1 : Real.exp (-(c₃ * L)) ≤ Real.exp (-(L ^ (0.7 : ℝ))) / 2 := by
      rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_sub]
      exact Real.exp_le_exp.2 (by linarith)
    have g2 : Real.exp (-(c₂ * L ^ (0.8 : ℝ))) ≤ Real.exp (-(L ^ (0.7 : ℝ))) / 2 := by
      rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_sub]
      exact Real.exp_le_exp.2 (by linarith)
    linarith

end DZZ
end LQGMetric
