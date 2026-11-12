/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcW1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcJ2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32K4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5W8
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32K5

/-!
# Walled `𝓔*`, part 1: the probability of the walled `𝓔*` for one white noise (P2-DZZCONCW)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`), proof of Prop 3.17, l. 1577–1579 and 1637–1639
("by Proposition 3.2 and Lemmas 3.1 and 3.5"), for the walled LGD `D^K` and the walled
approximate distance `D'_S` (Remark 5.2, l. 2281–2284; D117, D123).

* `eStar_of_eventsOn`: copy of `eStar_of_events` (S3ConcJ1) for the walled events
  `prop32EventOn`, `lem35EventOn` (S3P32K3);
* **`eStar_coreOn`**: copy of `eStar_core` (S3ConcJ2) from the walled P3.2 `DZZProp32UOn`, the
  walled L3.5 `DZZLemma35UOn` and the finiteness of `D'_S` on DZZ Lemma 3.1's event;
* `approxLGDSetOn_inside_ne_top`: for a dyadic wall `B̄`, `D'_{cellsInside B}(A, A') < ∞` on
  Lemma 3.1's event when the cells are smaller than `B` (pull back to `𝕍` by
  `approxDistSetOn_wHom`, S3L5W2, and `approxDist_ne_top_of`, S3ConcJ1);
* **`eStar_core_inside`**: `eStar_coreOn` at `K = B̄`, `S = cellsInside B`, `μ = dzzWall B̄ μIn`,
  from the walled (Eq.boundDprime) `L32UpperCrossOn` (hypothesis) and the proved
  `l32BallCoverOn_inside_dzzMuIn` (S3P32K5), `dzz_lemma35UOn_wall` (S3L5W8).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- **The chain of DZZ l. 1577–1579, walled** (copy of `eStar_of_events`, S3ConcJ1). -/
lemma eStar_of_eventsOn {Ω' : Type*} [MeasurableSpace Ω'] {S : Set DyBox} {γ : ℝ}
    {W' : WNSpace → Ω' → ℝ} {μ' : Ω' → Measure ℂ} {δ r τ : ℝ} {A B : Set ℂ} {ω : Ω'}
    (hδ : 0 < δ) (hτ0 : 0 ≤ τ)
    (hτm : 3 * r + Real.log (δ * Real.exp (-r))⁻¹ ^ (0.9 : ℝ) + Real.log δ⁻¹ ^ (0.8 : ℝ) ≤ τ)
    (hτp : 3 * r + Real.log (δ * Real.exp r)⁻¹ ^ (0.9 : ℝ) +
      Real.log (δ * Real.exp r)⁻¹ ^ (0.8 : ℝ) ≤ τ)
    (hfin : approxLGDSetOn S γ W' δ A B ω ≠ ⊤)
    (E1 : ω ∈ prop32EventOn S γ W' μ' (δ * Real.exp (-r)) A B)
    (E2 : ω ∈ prop32EventOn S γ W' μ' (δ * Real.exp r) A B)
    (E3 : ω ∈ lem35EventOn S γ W' δ (δ * Real.exp (-r)) A B)
    (E4 : ω ∈ lem35EventOn S γ W' (δ * Real.exp r) δ A B) :
    ω ∈ eStarEvent S γ W' μ' δ r τ A B := by
  have hm0 : 0 ≤ δ * Real.exp (-r) := by positivity
  refine eStar_mem_of hfin hτ0 (fun δ' hδ' => ?_) (fun δ' hδ' => ?_)
  · have hmono : ((lgdMinSet (μ' ω) δ' A B : ℕ∞) : ℝ≥0∞) ≤
        ((lgdMinSet (μ' ω) (δ * Real.exp (-r)) A B : ℕ∞) : ℝ≥0∞) :=
      ENat.toENNReal_le.2 (lgdMinSet_anti _ hm0 hδ'.1 A B)
    have E0 : ((approxLGDSetOn S γ W' δ A B ω : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-0)) ≤
        ((approxLGDSetOn S γ W' δ A B ω : ℕ∞) : ℝ≥0∞) := by simp
    have h := cor39_chain (pow_nonneg (div_nonneg hδ.le hm0) 3) E0 E1.2 E3
    refine (hmono.trans h).trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
    rw [div_mul_exp_neg_dzzC hδ, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  · have hmono : ((lgdMinSet (μ' ω) (δ * Real.exp r) A B : ℕ∞) : ℝ≥0∞) ≤
        ((lgdMinSet (μ' ω) δ' A B : ℕ∞) : ℝ≥0∞) :=
      ENat.toENNReal_le.2 (lgdMinSet_anti _ (hm0.trans hδ'.1) hδ'.2 A B)
    have E0 : ((approxLGDSetOn S γ W' δ A B ω : ℕ∞) : ℝ≥0∞) ≤
        ((approxLGDSetOn S γ W' δ A B ω : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (Real.exp 0) := by simp
    have h := cor39_chain (pow_nonneg (div_nonneg (by positivity) hδ.le) 3) E2.1 E0 E4
    refine h.trans (mul_le_mul' hmono (ENNReal.ofReal_le_ofReal ?_))
    rw [mul_exp_div_dzzC hδ, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **The probability of the walled `𝓔*`** (DZZ l. 1577–1579 + Remark 5.2): copy of `eStar_core`
(S3ConcJ2) with the walled P3.2 and L3.5 and the finiteness of `D'_S` on Lemma 3.1's event as
inputs. -/
theorem eStar_coreOn (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ξ : ℝ}
    (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) {K : Set ℂ} {S : Set DyBox} {μ : Ω → Measure ℂ}
    (h32 : ∀ ξd : ℝ, ξd < dzzCMc γ → DZZProp32UOn P γ W K S μ ξ ξd)
    (h35 : ∀ ξd : ℝ, ξd < dzzCMc γ → DZZLemma35UOn P γ W K S ξ ξd)
    (hfin : ∃ δf : ℝ, 0 < δf ∧ ∀ δ ∈ Ioo (0 : ℝ) δf, ∀ A B : Set ℂ,
      IsXiAdmissibleAtIn K ξ ξ δ A B → ∀ ω ∈ cellSizeEvent γ W δ,
        approxLGDSetOn S γ W δ A B ω ≠ ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ A B : Set ℂ,
      IsXiAdmissibleAtIn K ξ ξ δ A B → ∀ r τ : ℝ, 0 < r → r ≤ eStarS γ ξ * Real.log δ⁻¹ →
        3 * r + 3 * Real.log δ⁻¹ ^ (0.9 : ℝ) ≤ τ →
        P (eStarEvent S γ W μ δ r τ A B)ᶜ ≤ ENNReal.ofReal (δ ^ c) := by
  have := hW.isProbabilityMeasure
  obtain ⟨ξd, hξd_def⟩ : ∃ x : ℝ, x = (ξ + dzzCMc γ) / 2 := ⟨_, rfl⟩
  have hξd : ξd < dzzCMc γ := by rw [hξd_def]; linarith
  have hξξd : ξ ≤ ξd := by rw [hξd_def]; linarith
  have hξd0 : 0 ≤ ξd := by linarith
  obtain ⟨c₁, hc₁, δ₁, hδ₁, h₁⟩ := h32 ξd hξd
  obtain ⟨c₂, hc₂, δ₂, hδ₂, h₂⟩ := h35 ξd hξd
  obtain ⟨c₃, hc₃, δ₃', hδ₃', h₃⟩ := dzz_lemma31 hW hγ hγ2
  obtain ⟨δf, hδf, hfin⟩ := hfin
  set δ₃ := min δ₃' δf with hδ₃def
  have hδ₃ : 0 < δ₃ := lt_min hδ₃' hδf
  obtain ⟨c', hc'_def⟩ : ∃ x : ℝ, x = min (min c₁ c₂) c₃ / 2 := ⟨_, rfl⟩
  have hc'0 : 0 < c' := by rw [hc'_def]; positivity
  have hc'1 : c' ≤ c₁ / 2 := by
    rw [hc'_def]; linarith [min_le_left (min c₁ c₂) c₃, min_le_left c₁ c₂]
  have hc'2 : c' ≤ c₂ / 2 := by
    rw [hc'_def]; linarith [min_le_left (min c₁ c₂) c₃, min_le_right c₁ c₂]
  have hc'3 : c' ≤ c₃ := by rw [hc'_def]; linarith [min_le_right (min c₁ c₂) c₃]
  obtain ⟨δm, hδm_def⟩ : ∃ x : ℝ, x = min (min δ₁ δ₂) 1 := ⟨_, rfl⟩
  have hδm0 : 0 < δm := by rw [hδm_def]; positivity
  have hδm1 : δm ≤ 1 := by rw [hδm_def]; exact min_le_right _ _
  have hδm₁ : δm ≤ δ₁ := by rw [hδm_def]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hδm₂ : δm ≤ δ₂ := by rw [hδm_def]; exact (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨c' / 2, by positivity, min (min (δm ^ 2) δ₃) (min (Real.exp (-1))
    ((1 / (5 + 1)) ^ (2 / c'))), by positivity, ?_⟩
  intro δ hδ A B hAB r τ hr hrL hτ
  have hδ0 : 0 < δ := hδ.1
  have hδa : δ < δm ^ 2 := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ3 : δ < δ₃ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ3' : δ < δ₃' := hδ3.trans_le (min_le_left _ _)
  have hδf' : δ < δf := hδ3.trans_le (min_le_right _ _)
  have hδe : δ < Real.exp (-1) := hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ5 : δ < (1 / (5 + 1)) ^ (2 / c') :=
    hδ.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hδm' : δ < δm := hδa.trans_le (by nlinarith)
  have hδ1 : δ < 1 := hδm'.trans_le hδm1
  obtain ⟨L, hL⟩ : ∃ x : ℝ, x = Real.log δ⁻¹ := ⟨_, rfl⟩
  have hlogδ : Real.log δ = -L := by rw [hL, Real.log_inv]; ring
  have hL1 : 1 ≤ L := by
    have := Real.log_lt_log hδ0 hδe
    rw [Real.log_exp] at this; linarith
  rw [← hL] at hrL hτ
  have hs := eStarS_le_half γ ξ
  have hs0 := eStarS_pos hξ hξc (γ := γ)
  have hrL2 : r ≤ L / 2 := hrL.trans (by nlinarith)
  have hm0 : 0 < δ * Real.exp (-r) := by positivity
  have hp0 : 0 < δ * Real.exp r := by positivity
  have hm_lt : δ * Real.exp (-r) < δ :=
    mul_lt_of_lt_one_right hδ0 (Real.exp_lt_one_iff.2 (by linarith))
  have hp_gt : δ < δ * Real.exp r := lt_mul_of_one_lt_right hδ0 (Real.one_lt_exp_iff.2 hr)
  have hp_sq : (δ * Real.exp r) ^ 2 ≤ δ := by
    have h1 : Real.exp (2 * r) ≤ Real.exp L := Real.exp_le_exp.2 (by linarith)
    rw [hL, Real.exp_log (inv_pos.2 hδ0)] at h1
    calc (δ * Real.exp r) ^ 2 = δ ^ 2 * Real.exp (2 * r) := by
          rw [mul_pow, ← Real.exp_nat_mul]; norm_num
      _ ≤ δ ^ 2 * δ⁻¹ := by gcongr
      _ = δ := by field_simp
  have hpm : δ * Real.exp r < δm := lt_of_pow_lt_pow_left₀ 2 hδm0.le (hp_sq.trans_lt hδa)
  -- admissibility, all with the diameter exponent `ξd`
  have hAδ : IsXiAdmissibleAtIn K ξ ξd δ A B :=
    hAB.of_rpow_le (Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le hξξd)
  have hAm : IsXiAdmissibleAtIn K ξ ξd (δ * Real.exp (-r)) A B :=
    ⟨hAδ.1.mono hξd0 hm0.le hm_lt.le, hAδ.2⟩
  have hAp : IsXiAdmissibleAtIn K ξ ξd (δ * Real.exp r) A B := by
    refine hAB.of_rpow_le ?_
    rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hδ0, Real.exp_le_exp,
      Real.log_mul hδ0.ne' (Real.exp_pos r).ne', Real.log_exp, hlogδ]
    have h1 := eStarS_mul_le hξ hξc (γ := γ)
    have h2 : r * ξd ≤ eStarS γ ξ * L * ξd := mul_le_mul_of_nonneg_right hrL hξd0
    have h3 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ L)
    rw [hξd_def] at h2 ⊢
    nlinarith
  have hL9 : 0 ≤ L ^ (0.9 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hL89 : L ^ (0.8 : ℝ) ≤ L ^ (0.9 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hτ0 : 0 ≤ τ := by linarith
  have hτm : 3 * r + Real.log (δ * Real.exp (-r))⁻¹ ^ (0.9 : ℝ) + Real.log δ⁻¹ ^ (0.8 : ℝ) ≤ τ := by
    rw [log_inv_mul_exp_dzzC hδ0, ← hL]
    have a1 : (L - -r) ^ (0.9 : ℝ) ≤ 2 * L ^ (0.9 : ℝ) := by
      calc (L - -r) ^ (0.9 : ℝ) ≤ (2 * L) ^ (0.9 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        _ = (2 : ℝ) ^ (0.9 : ℝ) * L ^ (0.9 : ℝ) := Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ 2 * L ^ (0.9 : ℝ) := by
          gcongr
          calc (2 : ℝ) ^ (0.9 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
    linarith
  have hτp : 3 * r + Real.log (δ * Real.exp r)⁻¹ ^ (0.9 : ℝ) +
      Real.log (δ * Real.exp r)⁻¹ ^ (0.8 : ℝ) ≤ τ := by
    rw [log_inv_mul_exp_dzzC hδ0, ← hL]
    have b1 : (L - r) ^ (0.9 : ℝ) ≤ L ^ (0.9 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have b2 : (L - r) ^ (0.8 : ℝ) ≤ L ^ (0.8 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    linarith
  have hsub : cellSizeEvent γ W δ ∩ prop32EventOn S γ W μ (δ * Real.exp (-r)) A B ∩
      prop32EventOn S γ W μ (δ * Real.exp r) A B ∩
      lem35EventOn S γ W δ (δ * Real.exp (-r)) A B ∩ lem35EventOn S γ W (δ * Real.exp r) δ A B ⊆
      eStarEvent S γ W μ δ r τ A B := by
    rintro ω ⟨⟨⟨⟨h5, E1⟩, E2⟩, E3⟩, E4⟩
    exact eStar_of_eventsOn hδ0 hτ0 hτm hτp (hfin δ ⟨hδ0, hδf'⟩ A B hAB ω h5) E1 E2 E3 E4
  refine (measure_mono (compl_subset_compl.2 hsub)).trans
    ((measure_compl_inter5_le _ _ _ _ _ _).trans ?_)
  have hle : ∀ {c₀ : ℝ}, c' ≤ c₀ → ENNReal.ofReal (δ ^ c₀) ≤ ENNReal.ofReal (δ ^ c') :=
    fun h => ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le h)
  have e5 := (h₃ δ ⟨hδ0, hδ3'⟩).trans (hle hc'3)
  have e1 := (h₁ (δ * Real.exp (-r)) ⟨hm0, hm_lt.trans (hδm'.trans_le hδm₁)⟩ A B hAm).trans
    ((ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hm0.le hm_lt.le hc₁.le)).trans
      (hle (by linarith)))
  have e2 := (h₁ (δ * Real.exp r) ⟨hp0, hpm.trans_le hδm₁⟩ A B hAp).trans
    ((ENNReal.ofReal_le_ofReal (rpow_le_of_sq_le_dzzC hp0.le hp_sq hc₁.le)).trans (hle hc'1))
  have e3 := (h₂ δ ⟨hδ0, hδm'.trans_le hδm₂⟩ (δ * Real.exp (-r)) ⟨hm0, hm_lt⟩ A B hAδ).trans
    (hle (by linarith))
  have e4 := (h₂ (δ * Real.exp r) ⟨hp0, hpm.trans_le hδm₂⟩ δ ⟨hδ0, hp_gt⟩ A B hAp).trans
    ((ENNReal.ofReal_le_ofReal (rpow_le_of_sq_le_dzzC hp0.le hp_sq hc₂.le)).trans (hle hc'2))
  have h5x : ENNReal.ofReal (5 * δ ^ c') = 5 * ENNReal.ofReal (δ ^ c') := by
    rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
  calc _ ≤ ENNReal.ofReal (δ ^ c') + ENNReal.ofReal (δ ^ c') + ENNReal.ofReal (δ ^ c') +
        ENNReal.ofReal (δ ^ c') + ENNReal.ofReal (δ ^ c') :=
        add_le_add (add_le_add (add_le_add (add_le_add e5 e1) e2) e3) e4
    _ = ENNReal.ofReal (5 * δ ^ c') := by rw [h5x]; ring
    _ ≤ ENNReal.ofReal (δ ^ (c' / 2)) :=
        ENNReal.ofReal_le_ofReal (mul_rpow_le_rpow_half_dzzC (by norm_num) hc'0 hδ0 hδ5)

omit [MeasurableSpace Ω] in
/-- **`D'_{cellsInside B} < ∞` on DZZ Lemma 3.1's event** when the cells are smaller than `B`
(DZZ Lemma 3.1, l. 800–805; the cells inside `B̄` are a rescaled cell partition of `𝕍`,
`approxDistSetOn_wHom`, S3L5W2). -/
lemma approxLGDSetOn_inside_ne_top {γ δ : ℝ} {ω : Ω} {Bw : DyBox} (hδ : 0 < δ)
    (hside : δ ^ dzzCMc γ < Bw.side) (hω : ω ∈ cellSizeEvent γ W δ) {A A' : Set ℂ}
    (hA : A ⊆ interior Bw.closedBox) (hA' : A' ⊆ interior Bw.closedBox) {a b : ℂ} (ha : a ∈ A)
    (hb : b ∈ A') : approxLGDSetOn (cellsInside Bw) γ W δ A A' ω ≠ ⊤ := by
  set m := approxLQG γ W ω
  have hs : WSplit m δ Bw := wsplit_of_side hω.1 (fun c hc => (hω.2 c hc).2.trans_lt hside)
  obtain ⟨N₀, hN₀⟩ := exists_level_bound (Real.rpow_pos_of_pos hδ (dzzCmc γ))
    (fun c hc => (hω.2 c hc).1)
  have hpart := hpart_wEmb hs hω.1 hN₀
  have hlev : ∀ c, IsCell (fun c => m (wEmb Bw c)) δ c → c.n ≤ N₀ := fun c hc => by
    have := hN₀ _ ((isCell_wEmb_iff hs).2 hc)
    simp only [wEmb] at this; omega
  have hu : (wHom Bw).symm a ∈ dzzV := wHom_symm_mem_dzzV (interior_subset (hA ha))
  have hv : (wHom Bw).symm b ∈ dzzV := wHom_symm_mem_dzzV (interior_subset (hA' hb))
  have h := approxDist_ne_top_of hpart hlev hu hv
  unfold approxLGDSetOn
  rw [approxDistSetOn_wHom hs hA hA']
  refine ne_top_of_le_ne_top h ?_
  refine iInf₂_le_of_le ((wHom Bw).symm a) (by simpa using ha)
    (iInf₂_le ((wHom Bw).symm b) (by simpa using hb))

/-- **The walled `𝓔*` at a dyadic wall** (`K = B̄`, `S = cellsInside B`, `μ = dzzWall B̄ μIn`) for
one white noise, from the walled (Eq.boundDprime) for that white noise. -/
theorem eStar_core_inside (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (B : DyBox) {ξ : ℝ} (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ)
    (hX : ∀ ξd : ℝ, ξd < dzzCMc γ → L32UpperCrossOn P γ W B.closedBox (cellsInside B)
      (fun ω => dzzWall B.closedBox (dzzMuIn γ W ω)) ξ ξd) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ A A' : Set ℂ,
      IsXiAdmissibleAtIn B.closedBox ξ ξ δ A A' → ∀ r τ : ℝ, 0 < r →
        r ≤ eStarS γ ξ * Real.log δ⁻¹ → 3 * r + 3 * Real.log δ⁻¹ ^ (0.9 : ℝ) ≤ τ →
        P (eStarEvent (cellsInside B) γ W (fun ω => dzzWall B.closedBox (dzzMuIn γ W ω))
          δ r τ A A')ᶜ ≤ ENNReal.ofReal (δ ^ c) := by
  refine eStar_coreOn hW hγ hγ2 hξ hξc
    (fun ξd hξd => dzz_prop32UOn_of hW hγ hγ2 hξ hξd (l32BallCoverOn_inside_dzzMuIn hW hγ hγ2 B)
      (hX ξd hξd) (fun ξd' h => dzz_lemma35UOn_wall hW hγ hγ2 B hξ h))
    (fun ξd hξd => dzz_lemma35UOn_wall hW hγ hγ2 B hξ hξd) ?_
  have hc := dzzCMc_pos γ
  have hBs := wside_pos B
  refine ⟨(B.side / 2) ^ (1 / dzzCMc γ), by positivity, fun δ hδ A A' hAA ω hω => ?_⟩
  have hside : δ ^ dzzCMc γ < B.side := by
    have h1 := Real.rpow_lt_rpow hδ.1.le hδ.2 hc
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hc.ne', Real.rpow_one] at h1
    linarith
  obtain ⟨a, ha⟩ := hAA.1.adm_left.nonempty_dzzC
  obtain ⟨b, hb⟩ := hAA.1.adm_right.nonempty_dzzC
  exact approxLGDSetOn_inside_ne_top hδ.1 hside hω (hAA.2.1.trans (kXi_sub_interior hξ))
    (hAA.2.2.trans (kXi_sub_interior hξ)) ha hb

end DZZ
end LQGMetric
