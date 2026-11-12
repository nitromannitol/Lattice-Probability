/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53Z2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Z1

/-!
# DZZ Lemma 5.3 part 1, R2: the field event of `𝓔₄` at the sub-box scales (P2-DZZ53Z, P-131R)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, `𝓔₄` (l. 2440–2443) and (eq-M-A-upper-bound-bis)
(l. 2455): the domination needs the η-comparison between the cell scale `s_𝖢` and the sub-box
proxy scale `s' = s_b/(K 2^ℓ)`, `s_b = ε*² s_𝖢`, `K = 2^{⌊L^{0.51}⌋}`, i.e. `2^j = ε*^{-2} K 2^ℓ`,
which is `e^{O(L^{0.52})}` (decision D131 §3: "the band sup").

* **`l53_nbrFineGen_prob`**: `P(nbrFineGen W δ^{-C} e^{L^{0.55}} L^{0.8})ᶜ ≤ 2δ` for small `δ`.
  Proof: the proof of `nbrFineEvent_highProb` (S3L4FineHP) with the parameters changed
  (near-miss reuse, preference (c), copied and modified): `nbrFineGen_compl_le` (union bound and
  DZZ Lemma 2.6) and `nbrEventGen_compl_le` (Gaussian tail, variance `≤ 1076·9 + 1 + log Y`);
  the tail `exp(−L^{1.6}/(C L^{0.55}))` beats the `e^{O(L)}` boxes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `K L^p ≤ L^q` eventually (copy of `l53_ev_mul_rpow_le`, S5L53F2) -/
lemma l53z_ev_mul_rpow_le (K : ℝ) {p q : ℝ} (hpq : p < q) :
    ∀ᶠ L : ℝ in atTop, K * L ^ p ≤ L ^ q := by
  have h := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < q - p)).eventually (eventually_ge_atTop K)
  filter_upwards [h, eventually_gt_atTop 0] with L hL hL0
  have : L ^ q = L ^ p * L ^ (q - p) := by rw [← Real.rpow_add hL0]; ring_nf
  rw [this, mul_comm K]
  exact mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hL0.le _)

/-- `16 e^{a} e^{-q} ≤ e^{-L}` from `3 + a + L ≤ q` -/
lemma l53z_exp_le16 {a q L : ℝ} (h : 3 + a + L ≤ q) :
    16 * (Real.exp a * Real.exp (-q)) ≤ Real.exp (-L) := by
  have h16 : (16 : ℝ) ≤ Real.exp 3 := by
    have := Real.add_one_le_exp 3
    have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have h4 : (2.7 : ℝ) ^ 3 < Real.exp 1 ^ 3 := pow_lt_pow_left₀ h3 (by norm_num) (by norm_num)
    rw [h2]; norm_num at h4; linarith
  calc 16 * (Real.exp a * Real.exp (-q)) ≤ Real.exp 3 * (Real.exp a * Real.exp (-q)) :=
        mul_le_mul_of_nonneg_right h16 (by positivity)
    _ = Real.exp (3 + a - q) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-L) := Real.exp_le_exp.2 (by linarith)

set_option maxHeartbeats 800000 in
/-- **the band comparison event at the sub-box scales holds w.h.p.**:
`P(nbrFineGen W δ^{-C} e^{L^{0.55}} L^{0.8})ᶜ ≤ 2δ` for all small `δ` (`L = log δ⁻¹`). -/
theorem l53_nbrFineGen_prob (hW : IsWhiteNoise P W) {Cm : ℝ} (hCm : 0 ≤ Cm) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P.real (nbrFineGen W (δ ^ (-Cm)) (Real.exp (Real.log δ⁻¹ ^ (0.55 : ℝ)))
        (Real.log δ⁻¹ ^ (0.8 : ℝ)))ᶜ ≤ 2 * δ := by
  have := hW.isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := dzz_lemma26_eta
  choose Ys hYc _ hYae using fun n : ℕ =>
    exists_continuous_etaInf hW (δ := (2 : ℝ)⁻¹ ^ n) (by positivity)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set D : ℝ := 9 * Real.log 2 ^ 2 * C with hD
  have hD0 : 0 < D := by positivity
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 ((eventually_ge_atTop (3 : ℝ)).and
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.55)).eventually
      (eventually_ge_atTop (9685 : ℝ))).and
    ((l53z_ev_mul_rpow_le (36 * (5 * Cm + 5)) (by norm_num : (1 : ℝ) < 1.05)).and
      (l53z_ev_mul_rpow_le (D * (|Real.log (2 * C)| + 3 * Cm + 4))
        (by norm_num : (1 : ℝ) < 1.6)))))
  refine ⟨Real.exp (-max L₀ 3), Real.exp_pos _, fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδ1⟩ := hδ
  set L := Real.log δ⁻¹ with hLdef
  have hLgt : max L₀ 3 < L := by
    rw [hLdef, Real.log_inv, lt_neg]
    exact (Real.log_lt_iff_lt_exp hδ0).2 hδ1
  obtain ⟨hL3, hL55, hc1, hc2⟩ := hL₀ L ((le_max_left _ _).trans hLgt.le)
  have hL0 : 0 < L := by linarith
  have hδL : δ = Real.exp (-L) := by
    rw [hLdef, Real.log_inv, neg_neg, Real.exp_log hδ0]
  have hX : δ ^ (-Cm) = Real.exp (Cm * L) := by
    rw [Real.rpow_def_of_pos hδ0, hLdef, Real.log_inv]; ring_nf
  set E := Real.exp (Cm * L) with hEdef
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  set l55 := L ^ (0.55 : ℝ) with hl55
  set Y := Real.exp l55 with hYdef
  have hl55_0 : 0 ≤ l55 := Real.rpow_nonneg hL0.le _
  have hY1 : 1 ≤ Y := Real.one_le_exp hl55_0
  have hlogY : Real.log Y = l55 := Real.log_exp _
  have hl55L : l55 ≤ L := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ L)
      (by norm_num : (0.55 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at this
  set T := L ^ (0.8 : ℝ) with hTdef
  have hT : 0 ≤ T := Real.rpow_nonneg hL0.le _
  have hT2 : T ^ 2 = L ^ (1.05 : ℝ) * l55 := by
    rw [hTdef, hl55, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
    norm_num
  have hfine := nbrFineGen_compl_le (P := P) (X := δ ^ (-Cm)) (Y := Y) (T := T) hW (by rw [hX]; exact hE1) hY1 hT Ys hYae hC0.le
    (fun n u hu => by
      have h := hC hW ((2 : ℝ)⁻¹ ^ n) (by positivity) (Ys n) (hYc n) (hYae n) u hu 1 le_rfl
        (T / (3 * Real.log 2)) (by positivity)
      simpa using h)
  have h9 := nbrEventGen_compl_le (P := P) (X := δ ^ (-Cm)) (Y := Y) hW (K := 9) (by norm_num) (by rw [hX]; exact hE1) hY1
    (by positivity : 0 ≤ 2 * T / 3)
  rw [hX] at hfine h9
  -- the powers of `E` and `Y`
  have hpow : ∀ a b : ℕ, E ^ a * Y ^ b = Real.exp (a * (Cm * L) + b * l55) := by
    intro a b
    rw [hEdef, hYdef, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  -- first term
  set V := 1076 * 9 + 1 + Real.log Y with hV
  have hV0 : 0 < V := by rw [hV, hlogY]; linarith
  have hV2 : V ≤ 2 * l55 := by rw [hV, hlogY]; linarith
  have hq1 : L ^ (1.05 : ℝ) / 36 ≤ (2 * T / 3 / 2) ^ 2 / (2 * V) := by
    have e : (2 * T / 3 / 2) ^ 2 / (2 * V) = T ^ 2 / (18 * V) := by
      field_simp; ring
    rw [e, hT2, div_le_div_iff₀ (by norm_num) (by positivity)]
    have : 0 ≤ L ^ (1.05 : ℝ) := Real.rpow_nonneg hL0.le _
    nlinarith
  have hterm1 : (E + 1) * (Y + 1) * (2 * (E ^ 4 * Y ^ 2) *
      (2 * Real.exp (-(2 * T / 3 / 2) ^ 2 / (2 * V)))) ≤ δ := by
    calc (E + 1) * (Y + 1) * (2 * (E ^ 4 * Y ^ 2) *
          (2 * Real.exp (-(2 * T / 3 / 2) ^ 2 / (2 * V))))
        ≤ (E + E) * (Y + Y) * (2 * (E ^ 4 * Y ^ 2) *
          (2 * Real.exp (-(2 * T / 3 / 2) ^ 2 / (2 * V)))) := by gcongr
      _ = 16 * ((E ^ 5 * Y ^ 3) * Real.exp (-((2 * T / 3 / 2) ^ 2 / (2 * V)))) := by
          rw [neg_div]; ring
      _ ≤ δ := by
          rw [hpow, hδL]
          refine l53z_exp_le16 ?_
          have : (1 : ℝ) * L ≤ L ^ (1 : ℝ) := by rw [Real.rpow_one, one_mul]
          push_cast
          rw [Real.rpow_one] at hc1
          nlinarith
  -- second term
  have hq2 : L ^ (1.05 : ℝ) * l55 / D ≤ (T / (3 * Real.log 2)) ^ 2 / C := by
    rw [div_pow, ← hT2, div_div, hD]
    apply le_of_eq; ring
  have hL16 : L ^ (1.6 : ℝ) = L ^ (1.05 : ℝ) * l55 := by
    rw [hl55, ← Real.rpow_add hL0]; norm_num
  have hlogC : Real.log (2 * C) ≤ |Real.log (2 * C)| * L := by
    have := le_abs_self (Real.log (2 * C))
    nlinarith [abs_nonneg (Real.log (2 * C))]
  have hterm2 : (E * Y + 1) * ((E * Y) ^ 2 * (C * Real.exp (-(T / (3 * Real.log 2)) ^ 2 / C)))
      ≤ δ := by
    have hEY : 1 ≤ E * Y := by nlinarith
    calc (E * Y + 1) * ((E * Y) ^ 2 * (C * Real.exp (-(T / (3 * Real.log 2)) ^ 2 / C)))
        ≤ (E * Y + E * Y) * ((E * Y) ^ 2 * (C * Real.exp (-(T / (3 * Real.log 2)) ^ 2 / C))) := by
          gcongr
      _ = Real.exp (Real.log (2 * C)) * ((E ^ 3 * Y ^ 3) *
            Real.exp (-((T / (3 * Real.log 2)) ^ 2 / C))) := by
          rw [Real.exp_log (by positivity), neg_div]; ring
      _ ≤ δ := by
          rw [hpow, hδL, ← Real.exp_add, ← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          have h1 : L ^ (1.05 : ℝ) * l55 / D * D = L ^ (1.05 : ℝ) * l55 := div_mul_cancel₀ _ hD0.ne'
          rw [Real.rpow_one] at hc2
          push_cast
          have h2 : (|Real.log (2 * C)| + 3 * Cm + 4) * L ≤ L ^ (1.05 : ℝ) * l55 / D := by
            rw [le_div_iff₀ hD0, ← hL16]; linarith
          nlinarith
  have := h9.trans hterm1
  rw [hX]
  linarith

end DZZ
end LQGMetric
