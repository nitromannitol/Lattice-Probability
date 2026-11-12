/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5WallSim6C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim6B

/-!
# P-317K-SIM, part 6C: (eq-concentration-2) at a similar image of `B̄₀`

DZZ Proposition 3.17, (eq-concentration-2) (l. 1505–1517), at the wall `θB̄₀`, following DZZ's
proof (l. 1526–1530, 1627–1630) through the similarity coupling (lem-scaling-coupling,
l. 611–624): `wsim_conc2`, with the window `(log δ₂⁻¹)^{0.94}` of the concentration of
`log D'_{δ₂}` at `B̄₀` (`hconc2`, from `DZZConcApproxOn`), the walled P3.2 and Cor 3.9 at `B̄₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- **(eq-concentration-2) at `θB̄₀`** from the dyadic inputs at `B̄₀` on the coupling space. -/
theorem wsim_conc2 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
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
    {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 80) {c₃ δ3 c' δc c₂ δ5 K₁ δ6 : ℝ} (hc₃ : 0 < c₃)
    (hc' : 0 < c') (hc₂ : 0 < c₂) (hδ3 : 0 < δ3) (hδ5 : 0 < δ5) (hδc : 0 < δc) (hδ6 : 0 < δ6)
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
    (hconc2 : ∀ r ∈ Ioo (0 : ℝ) δ5,
      P' {ω | |logApproxLGDOn (cellsInside wsimB₀) γ W₁ r (wsimPull ‖a‖ a b A wsimP₁ r)
          (wsimPull ‖a‖ a b B wsimP₂ r) ω -
        ∫ ω', logApproxLGDOn (cellsInside wsimB₀) γ W₁ r (wsimPull ‖a‖ a b A wsimP₁ r)
          (wsimPull ‖a‖ a b B wsimP₂ r) ω' ∂P'| ≤ Real.log r⁻¹ ^ (0.94 : ℝ)}ᶜ ≤
        ENNReal.ofReal (Real.exp (-(c₂ * Real.log r⁻¹ ^ (0.8 : ℝ))))) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P (conc2Event (fun ω => dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W ω)) P δ
        (A δ) (B δ))ᶜ ≤ ENNReal.ofReal (Real.exp (-(Real.log δ⁻¹ ^ (0.7 : ℝ)))) := by
  have := hW.isProbabilityMeasure
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  set M₀ := |K₁| + 1 with hM₀d
  have hM₀ : 0 < M₀ := by positivity
  set m := min (min δ3 δ5) δc with hmd
  have hm0 : 0 < m := by positivity
  set D := max 0 (Real.log m⁻¹ + 1) with hDd
  have hD0 : 0 ≤ D := le_max_left _ _
  obtain ⟨hDm, hD1⟩ := wsim_exp_neg_D_lt hm0
  obtain ⟨δ₀, hδ₀, hev⟩ := exists_delta_of_eventually ((wsim_ev_basic hna ha1 D).and
    ((wsim_ev_exp_le (show 0 < 1 / C by positivity) (show (0.7 : ℝ) < 1.2 by norm_num) (4 * C)
      (by positivity)).and
    ((wsim_ev_exp_le (show 0 < c₃ / 2 by positivity) (show (0.7 : ℝ) < 1 by norm_num) 4
      (by norm_num)).and
    ((wsim_ev_exp_le (show 0 < c₂ / 2 by positivity) (show (0.7 : ℝ) < 0.8 by norm_num) 4
      (by norm_num)).and
    ((wsim_ev_exp_le (show 0 < c' / 2 by positivity) (show (0.7 : ℝ) < 1 by norm_num) 12
      (by norm_num)).and
    ((ev_rpow_le (show (0 : ℝ) < 0.7 by norm_num) one_pos (Real.log 4)).and
    ((ev_rpow_le (show (2 : ℝ) < 2.1 by norm_num) one_pos (6 * M₀ ^ 2)).and
    (ev_rpow_le (show (0.94 : ℝ) < 0.95 by norm_num) one_pos 28))))))))
  refine ⟨min (min δ₀ δ6) 1, by positivity, fun δ hδ => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hm := hδ.2
  simp only [lt_min_iff] at hm
  obtain ⟨⟨hδa, hδb⟩, hδ1⟩ := hm
  have hδI : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ0, hδ1⟩
  obtain ⟨hb, f1, f2, f3, f4, f5, f6, f7⟩ := hev δ ⟨hδ0, hδa⟩
  obtain ⟨e1, e2, hδ₂0, hδ₂₁, hδ₁D, hadm⟩ := wsim_scale hna ha1 hξ (by linarith) hD0 hδI hb
  obtain ⟨hL1, hDL, hl0, hl4, h1, h12, h2⟩ := hb
  set L := Real.log δ⁻¹ with hL
  set l := L ^ (0.6 : ℝ) with hl
  set δ₁ := δ * Real.exp l / ‖a‖ with hδ₁d
  set δ₂ := δ * Real.exp (-l) / ‖a‖ with hδ₂d
  set L₁ := L - l + Real.log ‖a‖
  set L₂ := L + l + Real.log ‖a‖
  have hL0 : 0 ≤ L := by linarith
  rw [Real.rpow_one] at f2 f4
  rw [Real.rpow_zero, mul_one, one_mul] at f5
  rw [one_mul, Real.rpow_two] at f6
  rw [one_mul] at f7
  have hδ₁m : δ₁ < m := hδ₁D.trans_lt hDm
  have hδ₁3 : δ₁ < δ3 := hδ₁m.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ₁5 : δ₁ < δ5 := hδ₁m.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ₁c : δ₁ < δc := hδ₁m.trans_le (min_le_right _ _)
  have hδ₁1 : δ₁ ≤ 1 := hδ₁D.trans hD1
  have hδ₁0 : 0 < δ₁ := hδ₂0.trans hδ₂₁
  obtain ⟨hp1, hAne, hBne⟩ := wsim_pair_at ha ha1 hξ hξ1 hAB hKin hδI hadm
  have hp2 := hp1.of_rpow_le (Real.rpow_le_rpow hδ₂0.le hδ₂₁.le (by positivity))
  have t2 := h32b δ₂ ⟨hδ₂0, hδ₂₁.trans hδ₁3⟩ _ _ hp2
  have t3 := hconc2 (wsimPhi ‖a‖ δ) ⟨wsimPhi_pos hna hδ0, hδ₂₁.trans hδ₁5⟩
  rw [wsimPull_phi hna a b A wsimP₁ hδI, wsimPull_phi hna a b B wsimP₂ hδI] at t3
  have t4 := hcor δ₁ ⟨hδ₁0, hδ₁c⟩ δ₂ ⟨hδ₂0, hδ₂₁⟩ _ _ hp1
  set E := Real.exp (-(L ^ (0.7 : ℝ))) with hEd
  have hE : 0 < E := Real.exp_pos _
  have b1 : C * Real.exp (-l ^ 2 / C) ≤ E / 4 := by
    have : -l ^ 2 / C = -(1 / C * L ^ (1.2 : ℝ)) := by rw [hl, wsim_lam_sq hL0]; ring
    rw [this]; linarith
  have b2 : δ₂ ^ c₃ ≤ E / 4 := by
    have := wsim_rpow_exp_le (c := c₃) (β := c₃ / 2) (L := L) hδ₂0 e2 (by
      have := mul_le_mul_of_nonneg_left (h1.trans h12.le) hc₃.le; linarith)
    linarith
  have b3 : Real.exp (-(c₂ * Real.log δ₂⁻¹ ^ (0.8 : ℝ))) ≤ E / 4 := by
    rw [e2]
    have k1 : (L / 2) ^ (0.8 : ℝ) ≤ L₂ ^ (0.8 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (h1.trans h12.le) (by norm_num)
    have k2 : L ^ (0.8 : ℝ) / 2 ≤ (L / 2) ^ (0.8 : ℝ) := by
      rw [Real.div_rpow hL0 (by norm_num)]
      have : (2 : ℝ) ^ (0.8 : ℝ) ≤ 2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
          (show (0.8 : ℝ) ≤ 1 by norm_num)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hL0 _) (by positivity) this
    have k3 : Real.exp (-(c₂ * L₂ ^ (0.8 : ℝ))) ≤ Real.exp (-(c₂ / 2 * L ^ (0.8 : ℝ))) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left (k2.trans k1) hc₂.le
      linarith
    linarith
  have b4 : 3 * δ₁ ^ c' ≤ E / 4 := by
    have := wsim_rpow_exp_le (c := c') (β := c' / 2) (L := L) hδ₁0 e1 (by
      have := mul_le_mul_of_nonneg_left h1 hc'.le; linarith)
    linarith
  have hp4 : E ≤ 1 / 4 := by
    rw [hEd, show (1 / 4 : ℝ) = Real.exp (-Real.log 4) by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num]
    exact Real.exp_le_exp.2 (by linarith)
  have hMp : (M₀ * L) ^ 2 * E ≤ 1 := by
    have := wsim_sq_exp_le_one (c := M₀ ^ 2 * L ^ 2) (y := L ^ (0.7 : ℝ))
      (Real.rpow_nonneg hL0 _) (by
        have h3 : (L ^ (0.7 : ℝ)) ^ 3 = L ^ (2.1 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num
        rw [h3]; linarith)
    calc (M₀ * L) ^ 2 * E = M₀ ^ 2 * L ^ 2 * E := by ring
      _ ≤ 1 := this
  obtain ⟨hXm, hXK⟩ := hK₁ δ ⟨hδ0, hδb⟩
  have hXM : ∫ ω, logMinLGD (dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W ω)) δ
      (A δ) (B δ) ^ 2 ∂P ≤ (M₀ * L) ^ 2 := by
    refine hXK.trans ?_
    have : K₁ ≤ M₀ ^ 2 := by
      rw [hM₀d]; nlinarith only [le_abs_self K₁, abs_nonneg K₁]
    calc K₁ * L ^ 2 ≤ M₀ ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg L)
      _ = (M₀ * L) ^ 2 := by ring
  have hWd : 2 * Real.log δ₂⁻¹ ^ (0.94 : ℝ) + 2 * Real.log δ₂⁻¹ ^ (0.9 : ℝ) +
      Real.log (cor39Fac δ₁ δ₂) + 4 ≤ L ^ (0.95 : ℝ) := by
    rw [wsim_log_cor39Fac hδ₁0 hδ₂0, e1, e2]
    have k1 := wsim_err_le hL1 h1 h12.le h2
    have k2 := wsim_rpow_le_two_mul (q := 0.94) (by linarith) h2 (by norm_num) (by norm_num)
    have k3 : L ^ (0.9 : ℝ) ≤ L ^ (0.94 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have k4 : 3 * (L₂ - L₁) = 6 * l := by simp only [L₁, L₂]; ring
    linarith
  have key := wsim_step (S := cellsInside wsimB₀) (A := A δ) (B := B δ) hW hW₁ hW₂ hγ hγ2 ha
    (hcp l hl0.le) hξ hp1.2.1 hp1.2.2 hAne hBne hδ0 rfl rfl ⟨hδ₂0, hδ₂₁.trans_le hδ₁1⟩
    hδ₂₁.le hδ₁1 t2 t3 t4 (by positivity) (by positivity) (by positivity) (by positivity)
    (by rw [show wsimPhi ‖a‖ δ = δ₂ from rfl]; linarith only [b1, b2, b3, b4]) hE hp4
    (by positivity) hMp hXm hXM hWd
  simp only [conc2Event, compl_ofPred]
  exact key

end DZZ
end LQGMetric
