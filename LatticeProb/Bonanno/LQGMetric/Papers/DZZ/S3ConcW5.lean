/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcW5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcW4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcL4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P317E

/-!
# Walled concentration of `D'`: `DZZConcApproxOn` at a dyadic wall from the Lipschitz data
(P2-DZZCONCW)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`), proof of Prop 3.17, l. 1595–1613 and 1640–1651
(the Gaussian concentration step), for `D'_S`, `S = cellsInside B`.

* `lipDataOn_tail`: copy of `lipData_tail` (S3ConcD) for `DZZLipDataOn`;
* `dzzConcApprox1_ofEvIn`, `dzzConcApprox2_ofEvIn`, **`dzzConcApprox_ofEvIn`**: copies of
  `dzzConcApprox{1,2}_ofEv`, `dzzConcApprox_ofEv` (S3ConcL4) with `logApproxLGDOn (cellsInside B)`,
  the pairs inside `B̄^ξ` and the walled crude moments `DZZCrudeMomentsEvOn` (S3P317E).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric

namespace LQGMetric
namespace DZZ

open WhiteNoise

universe u

/-- `conc_of_lip` for `DZZLipDataOn` (copy of `lipData_tail`, S3ConcD). -/
theorem lipDataOn_tail : ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (γ : ℝ) (W : WNSpace → Ω → ℝ) (S : Set DyBox) (δ : ℝ) (A B : Set ℂ)
    (σ ℓ τ ε : ℝ), 0 ≤ σ → 0 ≤ τ → DZZLipDataOn P γ W S δ A B σ ℓ τ ε →
    MemLp (logApproxLGDOn S γ W δ A B) 2 P → ∀ V : ℝ, ∫ ω, logApproxLGDOn S γ W δ A B ω ^ 2 ∂P ≤ V →
    ε ≤ 4⁻¹ → C * σ + 1 ≤ ℓ → ∀ M : ℝ, 0 < M →
    P.real {ω | 2 * τ + 3 * V / M +
        2 * M * (2 * ε + 2 * exp (-(ℓ - 1 - C * σ) ^ 2 / (2 * σ ^ 2))) <
          |logApproxLGDOn S γ W δ A B ω - ∫ ω', logApproxLGDOn S γ W δ A B ω' ∂P|} ≤
      2 * ε + 2 * exp (-(ℓ - 1 - C * σ) ^ 2 / (2 * σ ^ 2)) := by
  obtain ⟨C, hC1, hC⟩ := conc_of_lip.{u, 0}
  refine ⟨C, hC1, ?_⟩
  intro Ω _ P _ γ W S δ A B σ ℓ τ ε hσ hτ hD hY V hV hε4 hℓ M hM
  obtain ⟨T, X, hX, h0, hvar, 𝒜, F, hYF, hε, hlip, n, t, hnet⟩ := hD
  exact hC P X hX h0 σ hσ hvar _ hY V hV 𝒜 F hYF ε hε ℓ τ hτ hlip 1 n t hnet hε4 hℓ M hM


/-- `dzzConcApprox1_of` (S3ConcD) with `DZZCrudeMomentsEv` (copied proof). -/
theorem dzzConcApprox1_ofEvIn {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ ξ : ℝ} {W : WNSpace → Ω → ℝ} {μ : Ω → Measure ℂ} {Bw : DyBox}
    (h1 : DZZDistLip1In P γ W Bw ξ)
    (hmom : DZZCrudeMomentsEvOn P γ W Bw.closedBox (cellsInside Bw) μ ξ) :
    ∃ c : ℝ, 0 < c ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B → InsideXi Bw ξ A B →
      ∀ ι ∈ Ioo (0 : ℝ) 1, AlphaHighProb P (c * ι ^ 2) fun δ =>
        {ω | |logApproxLGDOn (cellsInside Bw) γ W δ (A δ) (B δ) ω -
          ∫ ω', logApproxLGDOn (cellsInside Bw) γ W δ (A δ) (B δ) ω' ∂P| ≤
          ι * Real.log δ⁻¹} := by
  obtain ⟨C, hC1, hC⟩ := lipDataOn_tail.{u}
  obtain ⟨a, K, ha, hK, h1⟩ := h1
  set c := min (a / 6) (a ^ 2 / (144 * K))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hc1 : 2 * c ≤ a / 3 := by have := min_le_left (a / 6) (a ^ 2 / (144 * K)); linarith
  have hc2 : 2 * c ≤ a ^ 2 / (72 * K) := by
    have := min_le_right (a / 6) (a ^ 2 / (144 * K))
    have e : a ^ 2 / (72 * K) = 2 * (a ^ 2 / (144 * K)) := by field_simp; ring
    linarith
  refine ⟨c, hc, fun A B hAB hin ι hι => ?_⟩
  obtain ⟨K', δm, hδm, hK'⟩ := hmom A B hAB hin
  set K₀ := max K' 1
  have hK₀ : 0 < K₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hι0 := hι.1
  obtain ⟨δ₁, hδ₁, hD⟩ := h1 A B hAB hin (ι / 3) ⟨by linarith, by linarith [hι.2]⟩
  have ev : ∀ᶠ L : ℝ in atTop, 0 < L ∧
      C * √K * L ^ (1 / 2 : ℝ) + 1 ≤ a * (ι / 3) / 2 * L ^ (1 : ℝ) ∧
      exp (-(c * ι ^ 2 * L)) ≤ 4⁻¹ ∧ exp (-(a * (ι / 3) * L)) ≤ 4⁻¹ ∧
      exp (-(2 * c * ι ^ 2 * L)) ≤ ι ^ 2 / (864 * K₀) := by
    filter_upwards [eventually_gt_atTop 0,
      ev_sqrt_add_le (p := 1 / 2) (q := 1) (a := a * (ι / 3) / 2) (by norm_num) (by norm_num)
        (by positivity) (C * √K),
      ev_exp_neg_le (k := c * ι ^ 2) (by positivity) (by norm_num : (0 : ℝ) < 4⁻¹),
      ev_exp_neg_le (k := a * (ι / 3)) (by positivity) (by norm_num : (0 : ℝ) < 4⁻¹),
      ev_exp_neg_le (k := 2 * c * ι ^ 2) (by positivity)
        (by positivity : (0 : ℝ) < ι ^ 2 / (864 * K₀))] with L h0 h1 h2 h3 h4
    exact ⟨h0, h1, h2, h3, h4⟩
  obtain ⟨δ₀, hδ₀, hev⟩ := exists_delta_of_eventually ev
  refine ⟨min δ₀ (min δ₁ (min δm 1)), lt_min hδ₀ (lt_min hδ₁ (lt_min hδm one_pos)),
    fun δ hδ => ?_⟩
  have hδ0 := hδ.1
  have hδa : δ < δ₀ := hδ.2.trans_le (min_le_left _ _)
  have hδb : δ < δ₁ := hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ < 1 :=
    hδ.2.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδm' : δ < δm :=
    hδ.2.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨hL0, hE1, hE2, hE3, hE4⟩ := hev δ ⟨hδ0, hδa⟩
  set L := Real.log δ⁻¹
  rw [Real.rpow_one] at hE1
  obtain ⟨hYm, hY2⟩ := (hK' δ ⟨hδ0, hδm'⟩).2
  have hV : ∫ ω, logApproxLGDOn (cellsInside Bw) γ W δ (A δ) (B δ) ω ^ 2 ∂P ≤ K₀ * L ^ 2 :=
    hY2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  set σ := √(K * L)
  have hσ : σ = √K * L ^ (1 / 2 : ℝ) := sqrt_mul_eq_rpow hK.le hL0.le
  have hσ2 : σ ^ 2 = K * L := Real.sq_sqrt (by positivity)
  set ℓ := a * (ι / 3) * L
  have hε : δ ^ (a * (ι / 3)) = exp (-(a * (ι / 3) * L)) := rpow_eq_exp_log_inv hδ0
  have hg : C * σ + 1 ≤ ℓ / 2 := by
    have : C * σ = C * √K * L ^ (1 / 2 : ℝ) := by rw [hσ]; ring
    have e : ℓ / 2 = a * (ι / 3) / 2 * L := by simp only [ℓ]; ring
    linarith
  have hCσ : 0 ≤ C * σ := by positivity
  set M := 18 * K₀ * L / ι
  have hM : 0 < M := by positivity
  have h := hC P γ W (cellsInside Bw) δ (A δ) (B δ) σ ℓ ((ι / 3) * L) (δ ^ (a * (ι / 3)))
    (Real.sqrt_nonneg _)
    (by positivity) (hD δ ⟨hδ0, hδb⟩) hYm (K₀ * L ^ 2) hV (by rw [hε]; exact hE3)
    (by linarith) M hM
  -- the Gaussian term
  have hgau : exp (-(ℓ - 1 - C * σ) ^ 2 / (2 * σ ^ 2)) ≤ exp (-(2 * c * ι ^ 2 * L)) := by
    rw [show ℓ - 1 - C * σ = ℓ - (1 + C * σ) by ring]
    refine (exp_gauss_le (by positivity) (by linarith) (by linarith)).trans (exp_le_exp.2 ?_)
    rw [hσ2, neg_le_neg_iff]
    have e : ℓ ^ 2 / (8 * (K * L)) = a ^ 2 / (72 * K) * ι ^ 2 * L := by
      simp only [ℓ]; field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 (sq_nonneg _)) hL0.le
  have hεb : exp (-(a * (ι / 3) * L)) ≤ exp (-(2 * c * ι ^ 2 * L)) := by
    refine exp_le_exp.2 (neg_le_neg ?_)
    have hι2 : ι ^ 2 ≤ ι := by nlinarith [hι.2]
    have : 2 * c * ι ^ 2 ≤ a * (ι / 3) := by nlinarith
    exact mul_le_mul_of_nonneg_right this hL0.le
  set q := exp (-(2 * c * ι ^ 2 * L))
  have hp : 2 * δ ^ (a * (ι / 3)) + 2 * exp (-(ℓ - 1 - C * σ) ^ 2 / (2 * σ ^ 2)) ≤ 4 * q := by
    rw [hε]; linarith
  have hq : 4 * q ≤ δ ^ (c * ι ^ 2) := by
    rw [rpow_eq_exp_log_inv hδ0]
    have e : q = exp (-(c * ι ^ 2 * L)) * exp (-(c * ι ^ 2 * L)) := by
      simp only [q]; rw [← exp_add]; ring_nf
    rw [e]
    have := exp_pos (-(c * ι ^ 2 * L))
    nlinarith
  have hthr : 2 * ((ι / 3) * L) + 3 * (K₀ * L ^ 2) / M +
      2 * M * (2 * δ ^ (a * (ι / 3)) + 2 * exp (-(ℓ - 1 - C * σ) ^ 2 / (2 * σ ^ 2))) ≤ ι * L := by
    have e1 : 3 * (K₀ * L ^ 2) / M = ι * L / 6 := by simp only [M]; field_simp; ring
    have e2 : 2 * M * (4 * q) ≤ ι * L / 6 := by
      have : 2 * M * (4 * q) = 144 * K₀ * L / ι * q := by simp only [M]; field_simp; ring
      rw [this]
      calc 144 * K₀ * L / ι * q ≤ 144 * K₀ * L / ι * (ι ^ 2 / (864 * K₀)) :=
            mul_le_mul_of_nonneg_left hE4 (by positivity)
        _ = ι * L / 6 := by field_simp; ring
    have := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 2 * M)
    linarith
  refine prob_compl_le (fun ω hω => ?_) (h.trans (hp.trans hq))
  simp only [mem_compl_iff, mem_setOf_eq, not_le] at hω ⊢
  linarith

/-- `dzzConcApprox2_of` (S3ConcE) with `DZZCrudeMomentsEv` (copied proof). -/
theorem dzzConcApprox2_ofEvIn {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ ξ : ℝ} {W : WNSpace → Ω → ℝ} {μ : Ω → Measure ℂ} {Bw : DyBox}
    (h2 : DZZDistLip2In P γ W Bw ξ)
    (hmom : DZZCrudeMomentsEvOn P γ W Bw.closedBox (cellsInside Bw) μ ξ)
    (A B : ℝ → Set ℂ) (hAB : IsXiAdmissible ξ A B) (hin : InsideXi Bw ξ A B) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | |logApproxLGDOn (cellsInside Bw) γ W δ (A δ) (B δ) ω -
          ∫ ω', logApproxLGDOn (cellsInside Bw) γ W δ (A δ) (B δ) ω' ∂P| ≤
        Real.log δ⁻¹ ^ (0.94 : ℝ)}ᶜ ≤
        ENNReal.ofReal (Real.exp (-(c₂ * Real.log δ⁻¹ ^ (0.8 : ℝ)))) := by
  obtain ⟨C, hC1, hC⟩ := lipDataOn_tail.{u}
  obtain ⟨a, K, ha, hK, h2⟩ := h2
  obtain ⟨K', δm, hδm, hK'⟩ := hmom A B hAB hin
  set K₀ := max K' 1
  have hK₀ : 0 < K₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  set c₂ := 1 / (16 * K)
  have hc₂ : 0 < c₂ := by positivity
  refine ⟨c₂, hc₂, ?_⟩
  obtain ⟨δ₁, hδ₁, hD⟩ := h2 A B hAB hin
  have ev : ∀ᶠ L : ℝ in atTop, 0 < L ∧
      C * √K * L ^ (1 / 2 : ℝ) + 1 ≤ 1 / 2 * L ^ (0.9 : ℝ) ∧
      1 / (8 * K) * L ^ (0.8 : ℝ) ≤ a * L ^ (1 : ℝ) ∧
      exp (-(c₂ * L ^ (0.8 : ℝ))) ≤ 4⁻¹ ∧ exp (-(a * L)) ≤ 4⁻¹ ∧
      2 * L ^ (0.93 : ℝ) ≤ 1 / 3 * L ^ (0.94 : ℝ) ∧
      3 * K₀ * L ^ (0.9 : ℝ) ≤ 1 / 3 * L ^ (0.94 : ℝ) ∧
      L ^ (1.1 : ℝ) * exp (-(c₂ * L ^ (0.8 : ℝ))) ≤ 1 ∧
      2 * L ^ (0 : ℝ) ≤ 1 / 3 * L ^ (0.94 : ℝ) := by
    filter_upwards [eventually_gt_atTop 0,
      ev_sqrt_add_le (p := 1 / 2) (q := 0.9) (a := 1 / 2) (by norm_num) (by norm_num)
        (by norm_num) (C * √K),
      ev_rpow_le (p := 0.8) (q := 1) (by norm_num) ha (1 / (8 * K)),
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.8)).eventually
        (ev_exp_neg_le (k := c₂) hc₂ (by norm_num : (0 : ℝ) < 4⁻¹)),
      ev_exp_neg_le (k := a) ha (by norm_num : (0 : ℝ) < 4⁻¹),
      ev_rpow_le (p := 0.93) (q := 0.94) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 3) 2,
      ev_rpow_le (p := 0.9) (q := 0.94) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 3) (3 * K₀),
      ev_rpow_mul_exp_le (r := 1.1) (q := 0.8) hc₂ (by norm_num),
      ev_rpow_le (p := 0) (q := 0.94) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 3) 2]
      with L h0 h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  obtain ⟨δ₀, hδ₀, hev⟩ := exists_delta_of_eventually ev
  refine ⟨min δ₀ (min δ₁ (min δm 1)), lt_min hδ₀ (lt_min hδ₁ (lt_min hδm one_pos)),
    fun δ hδ => ?_⟩
  have hδ0 := hδ.1
  have hδa : δ < δ₀ := hδ.2.trans_le (min_le_left _ _)
  have hδb : δ < δ₁ := hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ < 1 :=
    hδ.2.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδm' : δ < δm :=
    hδ.2.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨hL0, hE1, hE2, hE3, hE4, hE5, hE6, hE7, hE8⟩ := hev δ ⟨hδ0, hδa⟩
  set L := Real.log δ⁻¹
  rw [Real.rpow_one] at hE2
  rw [Real.rpow_zero] at hE8
  obtain ⟨hYm, hY2⟩ := (hK' δ ⟨hδ0, hδm'⟩).2
  have hV : ∫ ω, logApproxLGDOn (cellsInside Bw) γ W δ (A δ) (B δ) ω ^ 2 ∂P ≤ K₀ * L ^ 2 :=
    hY2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  set σ := √(K * L)
  have hσ : σ = √K * L ^ (1 / 2 : ℝ) := sqrt_mul_eq_rpow hK.le hL0.le
  have hσ2 : σ ^ 2 = K * L := Real.sq_sqrt (by positivity)
  set ℓ := L ^ (0.9 : ℝ)
  have hε : δ ^ a = exp (-(a * L)) := rpow_eq_exp_log_inv hδ0
  have hg : C * σ + 1 ≤ ℓ / 2 := by
    have : C * σ = C * √K * L ^ (1 / 2 : ℝ) := by rw [hσ]; ring
    linarith
  have hCσ : 0 ≤ C * σ := by positivity
  set M := L ^ (1.1 : ℝ)
  have hM : 0 < M := Real.rpow_pos_of_pos hL0 _
  have h := hC P γ W (cellsInside Bw) δ (A δ) (B δ) σ ℓ (L ^ (0.93 : ℝ)) (δ ^ a)
    (Real.sqrt_nonneg _)
    (by positivity) (hD δ ⟨hδ0, hδb⟩) hYm (K₀ * L ^ 2) hV (by rw [hε]; exact hE4)
    (by linarith) M hM
  set q := exp (-(c₂ * L ^ (0.8 : ℝ)))
  have hgau : exp (-(ℓ - 1 - C * σ) ^ 2 / (2 * σ ^ 2)) ≤ q * q := by
    rw [show ℓ - 1 - C * σ = ℓ - (1 + C * σ) by ring]
    refine (exp_gauss_le (by positivity) (by linarith) (by linarith)).trans ?_
    rw [← exp_add, hσ2]
    refine exp_le_exp.2 ?_
    have e : ℓ ^ 2 = L ^ (0.8 : ℝ) * L := by
      have h1 : ℓ ^ 2 = L ^ (1.8 : ℝ) := by
        simp only [ℓ]; rw [sq, rpow_mul_rpow' hL0]; norm_num
      rw [h1, show (1.8 : ℝ) = 0.8 + 1 by norm_num, Real.rpow_add hL0, Real.rpow_one]
    rw [e]
    have : L ^ (0.8 : ℝ) * L / (8 * (K * L)) = 2 * c₂ * L ^ (0.8 : ℝ) := by
      simp only [c₂]; field_simp; ring
    rw [this]; linarith
  have hεb : exp (-(a * L)) ≤ q * q := by
    rw [← exp_add]
    refine exp_le_exp.2 ?_
    have : c₂ * L ^ (0.8 : ℝ) + c₂ * L ^ (0.8 : ℝ) = 1 / (8 * K) * L ^ (0.8 : ℝ) := by
      simp only [c₂]; field_simp; ring
    linarith
  have hq0 : 0 < q := exp_pos _
  have hp : 2 * δ ^ a + 2 * exp (-(ℓ - 1 - C * σ) ^ 2 / (2 * σ ^ 2)) ≤ q := by
    rw [hε]; nlinarith
  have hthr : 2 * L ^ (0.93 : ℝ) + 3 * (K₀ * L ^ 2) / M +
      2 * M * (2 * δ ^ a + 2 * exp (-(ℓ - 1 - C * σ) ^ 2 / (2 * σ ^ 2))) ≤ L ^ (0.94 : ℝ) := by
    have e1 : 3 * (K₀ * L ^ 2) / M = 3 * K₀ * ℓ := by
      have : L ^ 2 = ℓ * M := by
        simp only [M, ℓ]; rw [rpow_mul_rpow' hL0]; norm_num
      rw [this]; field_simp
    have e2 : 2 * M * (2 * δ ^ a + 2 * exp (-(ℓ - 1 - C * σ) ^ 2 / (2 * σ ^ 2))) ≤ 2 :=
      calc _ ≤ 2 * M * q := mul_le_mul_of_nonneg_left hp (by positivity)
        _ ≤ 2 := by linarith
    linarith
  refine prob_compl_le (fun ω hω => ?_) (h.trans hp)
  simp only [mem_compl_iff, mem_setOf_eq, not_le] at hω ⊢
  linarith

/-- **`DZZConcApprox`** from `DZZDistLip1`, `DZZDistLip2` and the small-`δ` crude moments
(`dzzConcApprox_of` with `DZZCrudeMomentsEv`). -/
theorem dzzConcApprox_ofEvIn {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ ξ : ℝ} {W : WNSpace → Ω → ℝ} {μ : Ω → Measure ℂ} {Bw : DyBox}
    (h1 : DZZDistLip1In P γ W Bw ξ) (h2 : DZZDistLip2In P γ W Bw ξ)
    (hmom : DZZCrudeMomentsEvOn P γ W Bw.closedBox (cellsInside Bw) μ ξ) :
    DZZConcApproxOn P γ W Bw.closedBox (cellsInside Bw) ξ := by
  obtain ⟨c, hc, h⟩ := dzzConcApprox1_ofEvIn h1 hmom
  exact ⟨c, hc, fun A B hAB hin => ⟨h A B hAB hin, dzzConcApprox2_ofEvIn h2 hmom A B hAB hin⟩⟩

end DZZ
end LQGMetric
