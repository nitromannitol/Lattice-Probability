/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5WallSim6B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim6A

/-!
# P-317K-SIM, part 6B: (eq-concentration-1) at a similar image of `B̄₀`

DZZ Proposition 3.17, (eq-concentration-1) (l. 1505–1517), at the wall `θB̄₀`, following DZZ's
proof (l. 1526–1530) through the similarity coupling (lem-scaling-coupling, l. 611–624):
`wsim_conc1`. The inputs at the dyadic box `B̄₀` (on the coupling space) are the walled P3.2
at `δ₂` (`h32b`), the walled Cor 3.9 between `δ₁, δ₂` (`hcor`), the concentration of
`log D'_{δ₂}` (`hconc1`, from `DZZConcApproxOn` for the reindexed pairs `wsimPull`); the target's
crude moments (`hK₁`) recentre the window (`wsim_step`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- The pulled-back pair at one scale: admissible at `δ'` and nonempty. -/
lemma wsim_pair_at {a b : ℂ} (ha : a ≠ 0) (ha1 : ‖a‖ ≤ 1) {ξ : ℝ} (hξ : 0 < ξ)
    (hξ1 : ξ ≤ 1 / 80) {A B : ℝ → Set ℂ} (hAB : IsXiAdmissible ξ A B)
    (hKin : ∀ δ ∈ Ioo (0 : ℝ) 1, A δ ⊆ kXi (simMap a b '' wsimB₀.closedBox) ξ ∧
      B δ ⊆ kXi (simMap a b '' wsimB₀.closedBox) ξ) {δ δ' ξd : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (h : δ' ^ ξd ≤ δ ^ ξ / ‖a‖) :
    IsXiAdmissibleAtIn wsimB₀.closedBox ξ ξd δ' (simMap a b ⁻¹' A δ) (simMap a b ⁻¹' B δ) ∧
      (simMap a b ⁻¹' A δ).Nonempty ∧ (simMap a b ⁻¹' B δ).Nonempty :=
  ⟨wsim_preimage_admAtIn ha ha1 hξ (by linarith) h (hKin δ hδ).1 (hKin δ hδ).2
      ((hAB.subset_left δ hδ).trans (dzzVXi_sub_dzzV ξ))
      ((hAB.subset_right δ hδ).trans (dzzVXi_sub_dzzV ξ)) (hAB.adm_left δ hδ)
      (hAB.adm_right δ hδ) (hAB.dist_ge δ hδ),
    (cm_nonempty_of_adm (hAB.adm_left δ hδ)).preimage (simMap_surjective ha b),
    (cm_nonempty_of_adm (hAB.adm_right δ hδ)).preimage (simMap_surjective ha b)⟩

lemma wsim_rpow_exp_le {x c L' β L : ℝ} (hx : 0 < x) (e : Real.log x⁻¹ = L')
    (h : β * L ≤ c * L') : x ^ c ≤ Real.exp (-(β * L)) := by
  rw [rpow_eq_exp_log_inv hx, e]; exact Real.exp_le_exp.2 (by linarith)

lemma wsim_exp_neg_D_lt {m : ℝ} (hm : 0 < m) :
    Real.exp (-(max 0 (Real.log m⁻¹ + 1))) < m ∧ Real.exp (-(max 0 (Real.log m⁻¹ + 1))) ≤ 1 := by
  refine ⟨?_, Real.exp_le_one_iff.2 (by linarith [le_max_left 0 (Real.log m⁻¹ + 1)])⟩
  have h1 : Real.exp (-(Real.log m⁻¹ + 1)) < m := by
    rw [Real.log_inv, neg_add, neg_neg, Real.exp_add, Real.exp_log hm]
    have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    nlinarith
  exact lt_of_le_of_lt (Real.exp_le_exp.2 (by linarith [le_max_right 0 (Real.log m⁻¹ + 1)])) h1

/-- The coupling bound term: `C e^{−λ²/C} ≤ e^{−βL}` for `λ = L^{0.6}`. -/
lemma wsim_coupling_term_le {C L β c₀ : ℝ} (hC : 0 < C) (hL : 1 ≤ L) (hβ : β ≤ c₀)
    (h : (|Real.log C| + c₀) * L ^ (1 : ℝ) ≤ 1 / C * L ^ (1.2 : ℝ)) :
    C * Real.exp (-(L ^ (0.6 : ℝ)) ^ 2 / C) ≤ Real.exp (-(β * L)) := by
  rw [wsim_lam_sq (by linarith), Real.rpow_one] at *
  rw [← Real.exp_log hC, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : Real.log C ≤ |Real.log C| * L := by
    nlinarith [le_abs_self (Real.log C), abs_nonneg (Real.log C)]
  have h2 : β * L ≤ c₀ * L := by nlinarith
  have h3 : -L ^ (1.2 : ℝ) / C = -(1 / C * L ^ (1.2 : ℝ)) := by ring
  rw [Real.exp_log hC, h3]
  linarith

/-- **(eq-concentration-1) at `θB̄₀`** from the dyadic inputs at `B̄₀` on the coupling space. -/
theorem wsim_conc1 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {W : WNSpace → Ω → ℝ} {W₁ W₂ : WNSpace → Ω' → ℝ}
    (hW : IsWhiteNoise P W) (hW₁ : IsWhiteNoise P' W₁) (hW₂ : IsWhiteNoise P' W₂) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {a b : ℂ} (ha : a ≠ 0) (ha1 : ‖a‖ ≤ 1) {C : ℝ} (hC : 0 < C)
    (hcp : ∀ lam : ℝ, 0 ≤ lam → P'.real {ω | ¬ ∀ x ∈ wsimB₀.closedBox,
        ∀ y ∈ wsimB₀.closedBox, ∀ δ : ℝ, 0 < δ →
          lgdDZZ (dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W₂ ω))
              (‖a‖ * δ * Real.exp lam) (simMap a b x) (simMap a b y) ≤
            lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W₁ ω)) δ x y ∧
          lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W₁ ω)) δ x y ≤
            lgdDZZ (dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W₂ ω))
              (‖a‖ * δ * Real.exp (-lam)) (simMap a b x) (simMap a b y)} ≤
        C * Real.exp (-lam ^ 2 / C))
    {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 80) {c₃ δ3 c' δc c K₁ δ6 : ℝ} (hc₃ : 0 < c₃)
    (hc' : 0 < c') (hc : 0 < c) (hδ3 : 0 < δ3) (hδc : 0 < δc) (hδ6 : 0 < δ6)
    (h32b : ∀ δ ∈ Ioo (0 : ℝ) δ3, ∀ A B : Set ℂ,
      IsXiAdmissibleAtIn wsimB₀.closedBox ξ (2 * ξ) δ A B →
      P' (prop32EventOn (cellsInside wsimB₀) γ W₁
        (fun ω => dzzWall wsimB₀.closedBox (dzzMuIn γ W₁ ω)) δ A B)ᶜ ≤ ENNReal.ofReal (δ ^ c₃))
    (hcor : ∀ δ ∈ Ioo (0 : ℝ) δc, ∀ δ' ∈ Ioo (0 : ℝ) δ, ∀ A B : Set ℂ,
      IsXiAdmissibleAtIn wsimB₀.closedBox ξ (2 * ξ) δ A B →
      P' (cor39Event (fun ω => dzzWall wsimB₀.closedBox (dzzMuIn γ W₁ ω)) δ δ' A B)ᶜ ≤
        ENNReal.ofReal (3 * δ ^ c'))
    {A B : ℝ → Set ℂ} (hAB : IsXiAdmissible ξ A B)
    (hKin : ∀ δ ∈ Ioo (0 : ℝ) 1, A δ ⊆ kXi (simMap a b '' wsimB₀.closedBox) ξ ∧
      B δ ⊆ kXi (simMap a b '' wsimB₀.closedBox) ξ)
    (hK₁ : ∀ δ ∈ Ioo (0 : ℝ) δ6,
      MemLp (fun ω => logMinLGD (dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W ω)) δ
        (A δ) (B δ)) 2 P ∧
      ∫ ω, logMinLGD (dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W ω)) δ (A δ) (B δ) ^ 2
        ∂P ≤ K₁ * Real.log δ⁻¹ ^ 2)
    (hconc1 : ∀ ι ∈ Ioo (0 : ℝ) 1, AlphaHighProb P' (c * ι ^ 2) fun r =>
      {ω | |logApproxLGDOn (cellsInside wsimB₀) γ W₁ r (wsimPull ‖a‖ a b A wsimP₁ r)
          (wsimPull ‖a‖ a b B wsimP₂ r) ω -
        ∫ ω', logApproxLGDOn (cellsInside wsimB₀) γ W₁ r (wsimPull ‖a‖ a b A wsimP₁ r)
          (wsimPull ‖a‖ a b B wsimP₂ r) ω' ∂P'| ≤ ι * Real.log r⁻¹}) :
    ∀ ι ∈ Ioo (0 : ℝ) 1, AlphaHighProb P (min (min c₃ (c / 64)) c' / 2 / 2 * ι ^ 2) fun δ =>
      conc1Event (fun ω => dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W ω)) P δ ι
        (A δ) (B δ) := by
  intro ι hι
  have := hW.isProbabilityMeasure
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  set c₀ := min (min c₃ (c / 64)) c' / 2 with hc₀d
  have hc₀ : 0 < c₀ := by positivity
  have hc₀3 : c₀ ≤ c₃ / 2 := by
    have := min_le_left (min c₃ (c / 64)) c'; have := min_le_left c₃ (c / 64); linarith
  have hc₀c : c₀ ≤ c / 128 := by
    have := min_le_left (min c₃ (c / 64)) c'; have := min_le_right c₃ (c / 64); linarith
  have hc₀' : c₀ ≤ c' / 2 := by have := min_le_right (min c₃ (c / 64)) c'; linarith
  have hι0 := hι.1
  have hι2 : ι ^ 2 ≤ 1 := pow_le_one₀ hι0.le hι.2.le
  obtain ⟨δι, hδι, h3⟩ := hconc1 (ι / 8) ⟨by linarith, by linarith [hι.2]⟩
  set β := c₀ * ι ^ 2 with hβd
  have hβ : 0 < β := by positivity
  have hβc : β ≤ c₀ := mul_le_of_le_one_right hc₀.le hι2
  set M₀ := |K₁| + 1 with hM₀d
  have hM₀ : 0 < M₀ := by positivity
  set m := min (min δ3 δι) δc with hmd
  have hm0 : 0 < m := by positivity
  set D := max 0 (Real.log m⁻¹ + 1) with hDd
  have hD0 : 0 ≤ D := le_max_left _ _
  obtain ⟨hDm, hD1⟩ := wsim_exp_neg_D_lt hm0
  obtain ⟨δ₀, hδ₀, hev⟩ := exists_delta_of_eventually ((wsim_ev_basic hna ha1 D).and
    ((ev_rpow_le (show (0.9 : ℝ) < 1 by norm_num) (show 0 < ι / 2 by positivity) 24).and
    ((ev_rpow_le (show (1 : ℝ) < 1.2 by norm_num) (show 0 < 1 / C by positivity)
      (|Real.log C| + c₀)).and
    (eventually_ge_atTop (max (max (2 * Real.log 6 / β) (Real.log 24 / β))
      (36 * M₀ ^ 2 / β ^ 3))))))
  refine ⟨min (min δ₀ δ6) 1, by positivity, fun δ hδ => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hm := hδ.2
  simp only [lt_min_iff] at hm
  obtain ⟨⟨hδa, hδb⟩, hδ1⟩ := hm
  have hδI : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ0, hδ1⟩
  obtain ⟨hb, g1, g2, g3⟩ := hev δ ⟨hδ0, hδa⟩
  obtain ⟨e1, e2, hδ₂0, hδ₂₁, hδ₁D, hadm⟩ := wsim_scale hna ha1 hξ (by linarith) hD0 hδI hb
  obtain ⟨hL1, hDL, hl0, hl4, h1, h12, h2⟩ := hb
  set L := Real.log δ⁻¹ with hL
  set l := L ^ (0.6 : ℝ) with hl
  set δ₁ := δ * Real.exp l / ‖a‖ with hδ₁d
  set δ₂ := δ * Real.exp (-l) / ‖a‖ with hδ₂d
  set L₁ := L - l + Real.log ‖a‖
  set L₂ := L + l + Real.log ‖a‖
  have g3a : 2 * Real.log 6 / β ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans g3)
  have g3b : Real.log 24 / β ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans g3)
  have g3c : 36 * M₀ ^ 2 / β ^ 3 ≤ L := (le_max_right _ _).trans g3
  rw [div_le_iff₀ hβ] at g3a g3b
  rw [div_le_iff₀ (by positivity)] at g3c
  have hδ₁m : δ₁ < m := hδ₁D.trans_lt hDm
  have hδ₁3 : δ₁ < δ3 := hδ₁m.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ₁ι : δ₁ < δι := hδ₁m.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ₁c : δ₁ < δc := hδ₁m.trans_le (min_le_right _ _)
  have hδ₁1 : δ₁ ≤ 1 := hδ₁D.trans hD1
  have hδ₁0 : 0 < δ₁ := hδ₂0.trans hδ₂₁
  obtain ⟨hp1, hAne, hBne⟩ := wsim_pair_at ha ha1 hξ hξ1 hAB hKin hδI hadm
  have hp2 := hp1.of_rpow_le (Real.rpow_le_rpow hδ₂0.le hδ₂₁.le (by positivity))
  -- the four exceptional probabilities
  have t2 := h32b δ₂ ⟨hδ₂0, hδ₂₁.trans hδ₁3⟩ _ _ hp2
  have t3 := h3 (wsimPhi ‖a‖ δ) ⟨wsimPhi_pos hna hδ0, hδ₂₁.trans hδ₁ι⟩
  beta_reduce at t3
  rw [wsimPull_phi hna a b A wsimP₁ hδI, wsimPull_phi hna a b B wsimP₂ hδI] at t3
  have t4 := hcor δ₁ ⟨hδ₁0, hδ₁c⟩ δ₂ ⟨hδ₂0, hδ₂₁⟩ _ _ hp1
  have hL0 : 0 ≤ L := by linarith
  have b1 : C * Real.exp (-l ^ 2 / C) ≤ Real.exp (-(β * L)) :=
    wsim_coupling_term_le hC hL1 hβc g2
  have b2 : δ₂ ^ c₃ ≤ Real.exp (-(β * L)) := wsim_rpow_exp_le hδ₂0 e2 (by
    have := mul_le_mul_of_nonneg_right hβc hL0
    have := mul_le_mul_of_nonneg_right hc₀3 hL0
    have := mul_le_mul_of_nonneg_left (h1.trans h12.le) hc₃.le
    linarith)
  have b3 : δ₂ ^ (c * (ι / 8) ^ 2) ≤ Real.exp (-(β * L)) := wsim_rpow_exp_le hδ₂0 e2 (by
    have k1 : β * L ≤ c / 128 * ι ^ 2 * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₀c (sq_nonneg ι)) hL0
    have hcι : 0 ≤ c * (ι / 8) ^ 2 := by positivity
    have k2 := mul_le_mul_of_nonneg_left (h1.trans h12.le) hcι
    have k3 : c / 128 * ι ^ 2 * L = c * (ι / 8) ^ 2 * (L / 2) := by ring
    linarith)
  have b4 : δ₁ ^ c' ≤ Real.exp (-(β * L)) := wsim_rpow_exp_le hδ₁0 e1 (by
    have := mul_le_mul_of_nonneg_right hβc hL0
    have := mul_le_mul_of_nonneg_right hc₀' hL0
    have := mul_le_mul_of_nonneg_left h1 hc'.le
    linarith)
  have hE := Real.exp_pos (-(β * L))
  set p := 6 * Real.exp (-(β * L)) with hpd
  have hp : 0 < p := by positivity
  have hp4 : p ≤ 1 / 4 := by
    have : 24 * Real.exp (-(β * L)) ≤ 1 := by
      rw [← Real.exp_log (show (0 : ℝ) < 24 by norm_num), ← Real.exp_add]
      exact Real.exp_le_one_iff.2 (by linarith)
    linarith
  have hMp : (M₀ * L) ^ 2 * p ≤ 1 := by
    have := wsim_sq_exp_le_one (c := 6 * M₀ ^ 2 * L ^ 2) (y := β * L) (by positivity) (by
      calc 6 * (6 * M₀ ^ 2 * L ^ 2) = 36 * M₀ ^ 2 * L ^ 2 := by ring
        _ ≤ L * β ^ 3 * L ^ 2 := mul_le_mul_of_nonneg_right g3c (sq_nonneg L)
        _ = (β * L) ^ 3 := by ring)
    calc (M₀ * L) ^ 2 * p = 6 * M₀ ^ 2 * L ^ 2 * Real.exp (-(β * L)) := by rw [hpd]; ring
      _ ≤ 1 := this
  obtain ⟨hXm, hXK⟩ := hK₁ δ ⟨hδ0, hδb⟩
  have hXM : ∫ ω, logMinLGD (dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W ω)) δ
      (A δ) (B δ) ^ 2 ∂P ≤ (M₀ * L) ^ 2 := by
    refine hXK.trans ?_
    have : K₁ ≤ M₀ ^ 2 := by
      rw [hM₀d]; nlinarith only [le_abs_self K₁, abs_nonneg K₁]
    calc K₁ * L ^ 2 ≤ M₀ ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg L)
      _ = (M₀ * L) ^ 2 := by ring
  have hWd : 2 * (ι / 8 * Real.log δ₂⁻¹) + 2 * Real.log δ₂⁻¹ ^ (0.9 : ℝ) +
      Real.log (cor39Fac δ₁ δ₂) + 4 ≤ ι * L := by
    rw [wsim_log_cor39Fac hδ₁0 hδ₂0, e1, e2]
    have k1 := wsim_err_le hL1 h1 h12.le h2
    rw [Real.rpow_one] at g1
    have k2 : ι / 8 * L₂ ≤ ι / 4 * L := by
      have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ ι / 8 by positivity); linarith
    have k3 : 3 * (L₂ - L₁) = 6 * l := by simp only [L₁, L₂]; ring
    linarith
  have key := wsim_step (S := cellsInside wsimB₀) (A := A δ) (B := B δ) hW hW₁ hW₂ hγ hγ2 ha
    (hcp l hl0.le) hξ hp1.2.1 hp1.2.2 hAne hBne hδ0 rfl rfl ⟨hδ₂0, hδ₂₁.trans_le hδ₁1⟩
    hδ₂₁.le hδ₁1 t2 t3 t4 (by positivity) (by positivity) (by positivity) (by positivity)
    (by rw [hpd, show wsimPhi ‖a‖ δ = δ₂ from rfl]; linarith only [b1, b2, b3, b4]) hp hp4 (by positivity) hMp hXm hXM hWd
  simp only [conc1Event, compl_ofPred]
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [rpow_eq_exp_log_inv hδ0, ← hL, hpd, ← Real.exp_log (show (0 : ℝ) < 6 by norm_num),
    ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : c₀ / 2 * ι ^ 2 * L = β * L / 2 := by rw [hβd]; ring
  linarith

end DZZ
end LQGMetric
