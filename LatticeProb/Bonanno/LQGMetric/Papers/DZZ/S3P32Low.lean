/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32Low at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5YLemma

/-!
# DZZ Proposition 3.2, lower bound (P2-DZZ32)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Proposition 3.2
(`prop-approximate-LGD`), lower bound, l. 1159–1169. With `δ' = δ e^{(log δ⁻¹)^{0.8}}` DZZ claim
(eq-Euclidean-Ball-covering): with high probability every Euclidean ball of LQG mass `≤ δ²` is
covered by 4 cells of `𝒱_{δ'}`, hence `D'_{γ,δ'}(u, v) ≤ 4 D_{γ,δ}(u, v)` for all `u, v ∈ 𝕍`
(l. 1167–1168); "combined with Lemma 3.5, it then yields the desired lower bound".

* `p32Up δ = δ e^{(log δ⁻¹)^{0.8}}` (DZZ's `δ'`, l. 1160).
* `L32BallCover P γ W μ`: the display of l. 1167–1168, with high probability (open; DZZ
  l. 1171–1206 prove it from (eq-cell-LQG-compare) and (Eq.LD-lowerbound-approx-LGD)).
* `prop32Lower`, `prop32Upper`: the two halves of `prop32Event`.
* **`dzz_prop32_lower`**: the lower half of P3.2, uniformly over pairs admissible at `δ`, from
  `L32BallCover` and the proved Lemma 3.5 (`dzz_lemma35U`), applied at `δ' > δ` with the
  diameter exponent `(ξd + C_Mc)/2` (decision D71).
* `p32_asym`: the exponent bookkeeping (own elementary proof).
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

/-- DZZ's `δ' = δ e^{(log δ⁻¹)^{0.8}}` in the proof of the lower bound of P3.2 (l. 1160). -/
def p32Up (δ : ℝ) : ℝ := δ * Real.exp (Real.log δ⁻¹ ^ (0.8 : ℝ))

/-- **DZZ l. 1164–1168** (consequence of (eq-Euclidean-Ball-covering)): with high probability
`D'_{γ,δ'}(u, v) ≤ 4 D_{γ,δ}(u, v)` for all `u, v ∈ 𝕍`, `δ' = δ e^{(log δ⁻¹)^{0.8}}`. -/
def L32BallCover (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) : Prop :=
  HighProb P fun δ => {ω | ∀ u ∈ dzzV, ∀ v ∈ dzzV,
    approxLGD γ W (p32Up δ) u v ω ≤ 4 * lgdDZZ (μ ω) δ u v}

/-- The lower half of the event of P3.2. -/
def prop32Lower (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (δ : ℝ) (A B : Set ℂ) :
    Set Ω :=
  {ω | ((approxLGDSet γ W δ A B ω : ℕ∞) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(Real.log δ⁻¹) ^ (0.9 : ℝ))) ≤
        ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞)}

/-- The upper half of the event of P3.2. -/
def prop32Upper (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (δ : ℝ) (A B : Set ℂ) :
    Set Ω :=
  {ω | ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞) ≤
        ((approxLGDSet γ W δ A B ω : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp ((Real.log δ⁻¹) ^ (0.9 : ℝ)))}

omit [MeasurableSpace Ω] in
lemma prop32Event_eq (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (δ : ℝ) (A B : Set ℂ) :
    prop32Event γ W μ δ A B = prop32Lower γ W μ δ A B ∩ prop32Upper γ W μ δ A B := rfl

/-- Exponent bookkeeping for `L = log δ⁻¹` large (own elementary proof). -/
lemma p32_asym {a b : ℝ} (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      Real.log δ⁻¹ ^ (0.8 : ℝ) ≤ Real.log δ⁻¹ / 2 ∧
      b * Real.log δ⁻¹ ^ (0.8 : ℝ) ≤ a * Real.log δ⁻¹ ∧
      Real.log 4 + 4 * Real.log δ⁻¹ ^ (0.8 : ℝ) ≤ Real.log δ⁻¹ ^ (0.9 : ℝ) := by
  set M : ℝ := 8 + |b| / a with hMdef
  have hba : 0 ≤ |b| / a := by positivity
  have hM8 : 8 ≤ M := by linarith
  refine ⟨Real.exp (-(M ^ 10)), Real.exp_pos _, fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδ1⟩ := hδ
  set L := Real.log δ⁻¹ with hLdef
  have hLM : M ^ 10 ≤ L := by
    have := Real.log_lt_log hδ0 hδ1
    rw [Real.log_exp] at this
    rw [hLdef, Real.log_inv]; linarith
  have hM1 : 1 ≤ M := by linarith
  have hL1 : 1 ≤ L := (one_le_pow₀ hM1).trans hLM
  have hL0 : 0 < L := by linarith
  have h01 : M ≤ L ^ (0.1 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hLM (by norm_num : (0 : ℝ) ≤ 0.1)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      show ((10 : ℕ) : ℝ) * 0.1 = 1 by norm_num, Real.rpow_one] at h
  have e9 : L ^ (0.9 : ℝ) = L ^ (0.8 : ℝ) * L ^ (0.1 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have e1 : L = L ^ (0.9 : ℝ) * L ^ (0.1 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have h8 : 1 ≤ L ^ (0.8 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have h9a : L ^ (0.8 : ℝ) * M ≤ L ^ (0.9 : ℝ) := by
    rw [e9]; exact mul_le_mul_of_nonneg_left h01 (by positivity)
  have h9b : L ^ (0.9 : ℝ) * M ≤ L := by
    conv_rhs => rw [e1]
    exact mul_le_mul_of_nonneg_left h01 (by positivity)
  have hMM : L ^ (0.8 : ℝ) * M * M ≤ L := by nlinarith
  have hbM : |b| ≤ a * M := by
    have : |b| / a ≤ M := by linarith
    rwa [div_le_iff₀ ha, mul_comm] at this
  refine ⟨?_, ?_, ?_⟩
  · have h2M : 2 ≤ M * M := by nlinarith
    have := mul_le_mul_of_nonneg_left h2M (by positivity : (0 : ℝ) ≤ L ^ (0.8 : ℝ))
    rw [← mul_assoc] at this
    linarith
  · have h1 : b * L ^ (0.8 : ℝ) ≤ |b| * L ^ (0.8 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self b) (by positivity)
    have h2 : |b| * L ^ (0.8 : ℝ) ≤ a * M * L ^ (0.8 : ℝ) :=
      mul_le_mul_of_nonneg_right hbM (by positivity)
    have h3 : a * M * L ^ (0.8 : ℝ) ≤ a * L := by
      have : M * L ^ (0.8 : ℝ) ≤ L := by nlinarith
      nlinarith
    linarith
  · have hl4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
    nlinarith

omit [MeasurableSpace Ω] in
/-- Pointwise `D'_{δ'} ≤ 4 D_δ` on `𝕍` gives the same bound for the minima over `A × B`. -/
lemma approxLGDSet_le_four_mul {γ : ℝ} {W : WNSpace → Ω → ℝ} {μ : Measure ℂ} {δ δ' : ℝ}
    {ω : Ω} {A B : Set ℂ} (hA : A ⊆ dzzV) (hB : B ⊆ dzzV)
    (h : ∀ u ∈ dzzV, ∀ v ∈ dzzV, approxLGD γ W δ' u v ω ≤ 4 * lgdDZZ μ δ u v) :
    approxLGDSet γ W δ' A B ω ≤ 4 * lgdMinSet μ δ A B := by
  unfold lgdMinSet approxLGDSet approxDistSet
  simp only [ENat.mul_iInf_of_ne (show (4 : ℕ∞) ≠ 0 by norm_num)]
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  exact (iInf₂_le x hx).trans ((iInf₂_le y hy).trans (h x (hA hx) y (hB hy)))

lemma dzzVXi_sub_dzzV (ξ : ℝ) : dzzVXi ξ ⊆ dzzV := fun _ h => h.1

set_option maxHeartbeats 1000000 in
/-- **Lower bound of DZZ Proposition 3.2** (l. 1159–1169), uniformly over pairs admissible at
`δ`, from (eq-Euclidean-Ball-covering) in the form `L32BallCover` and Lemma 3.5. -/
theorem dzz_prop32_lower {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hcov : L32BallCover P γ W μ)
    {ξ ξd : ℝ} (hξ : 0 < ξ) (hξd : ξd < dzzCMc γ) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ A B : Set ℂ,
      IsXiAdmissibleAt ξ ξd δ A B → P (prop32Lower γ W μ δ A B)ᶜ ≤ ENNReal.ofReal (δ ^ c) := by
  set ξ₂ := (ξd + dzzCMc γ) / 2 with hξ₂
  obtain ⟨c₅, hc₅, δ₅, hδ₅, h35⟩ := dzz_lemma35U hW hγ hγ2 (ξd := ξ₂) hξ (by linarith)
  obtain ⟨c₁, hc₁, δ₁, hδ₁, hcv⟩ := hcov
  obtain ⟨δa, hδa, hasym⟩ := p32_asym (a := ξ₂ - ξd) (b := ξ₂) (by linarith)
  set c := min (c₅ / 2) c₁ with hcdef
  have hc : 0 < c := lt_min (by positivity) hc₁
  refine ⟨c / 2, by positivity, min (min δa (δ₅ ^ 2)) (min δ₁ (min (1 / 2) ((1 / 2) ^ (2 / c)))),
    by positivity, fun δ hδ A B hAB => ?_⟩
  obtain ⟨hδ0, hδ⟩ := hδ
  have hδa' : δ < δa := hδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ5 : δ < δ₅ ^ 2 := hδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1' : δ < δ₁ := hδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδh : δ < 1 / 2 := hδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hδc : δ < (1 / 2) ^ (2 / c) := hδ.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hδ1 : δ < 1 := by linarith
  obtain ⟨as1, as2, as3⟩ := hasym δ ⟨hδ0, hδa'⟩
  set L := Real.log δ⁻¹ with hLdef
  have hlogδ : Real.log δ = -L := by rw [hLdef, Real.log_inv]; ring
  have hL0 : 0 < L := by have := Real.log_neg hδ0 hδ1; linarith
  have hL8 : 0 < L ^ (0.8 : ℝ) := Real.rpow_pos_of_pos hL0 _
  set δ' := p32Up δ with hδ'def
  have hδ'0 : 0 < δ' := by rw [hδ'def, p32Up]; positivity
  have hlogδ' : Real.log δ' = -L + L ^ (0.8 : ℝ) := by
    rw [hδ'def, p32Up, Real.log_mul hδ0.ne' (Real.exp_pos _).ne', Real.log_exp, hlogδ]
  have hδδ' : δ < δ' := by
    rw [← Real.log_lt_log_iff hδ0 hδ'0, hlogδ', hlogδ]; linarith
  have hδ'5 : δ' < δ₅ := by
    rw [← Real.log_lt_log_iff hδ'0 hδ₅]
    have := Real.log_lt_log hδ0 hδ5
    rw [Real.log_pow, hlogδ] at this
    push_cast at this
    linarith
  -- admissibility at `δ'` with the exponent `ξ₂`
  have hadm : IsXiAdmissibleAt ξ ξ₂ δ' A B := by
    refine hAB.of_rpow_le ?_
    rw [Real.rpow_def_of_pos hδ'0, Real.rpow_def_of_pos hδ0, hlogδ', hlogδ]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hA : A ⊆ dzzV := hAB.subset_left.trans (dzzVXi_sub_dzzV ξ)
  have hB : B ⊆ dzzV := hAB.subset_right.trans (dzzVXi_sub_dzzV ξ)
  -- the deterministic inclusion
  set Q := (δ' / δ) ^ 3 * Real.exp ((Real.log δ'⁻¹) ^ (0.8 : ℝ)) with hQdef
  have hQ0 : 0 ≤ Q := by positivity
  have hQ : 4 * Q * Real.exp (-L ^ (0.9 : ℝ)) ≤ 1 := by
    have hr : δ' / δ = Real.exp (L ^ (0.8 : ℝ)) := by
      rw [hδ'def, p32Up, mul_div_cancel_left₀ _ hδ0.ne']
    have hl' : Real.log δ'⁻¹ = L - L ^ (0.8 : ℝ) := by rw [Real.log_inv, hlogδ']; ring
    have hl'0 : 0 ≤ L - L ^ (0.8 : ℝ) := by linarith
    have hp : (Real.log δ'⁻¹) ^ (0.8 : ℝ) ≤ L ^ (0.8 : ℝ) := by
      rw [hl']; exact Real.rpow_le_rpow hl'0 (by linarith) (by norm_num)
    rw [hQdef, hr, ← Real.exp_nat_mul]
    calc 4 * (Real.exp (((3 : ℕ) : ℝ) * L ^ (0.8 : ℝ)) * Real.exp (Real.log δ'⁻¹ ^ (0.8 : ℝ))) *
          Real.exp (-L ^ (0.9 : ℝ))
        = Real.exp (Real.log 4 + ((3 : ℕ) : ℝ) * L ^ (0.8 : ℝ) + Real.log δ'⁻¹ ^ (0.8 : ℝ) +
            -L ^ (0.9 : ℝ)) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]; ring
      _ ≤ Real.exp 0 := by
          refine Real.exp_le_exp.2 ?_
          push_cast; linarith
      _ = 1 := Real.exp_zero
  have hsub : (prop32Lower γ W μ δ A B)ᶜ ⊆ (lem35Event γ W δ' δ A B)ᶜ ∪
      {ω | ∀ u ∈ dzzV, ∀ v ∈ dzzV, approxLGD γ W (p32Up δ) u v ω ≤ 4 * lgdDZZ (μ ω) δ u v}ᶜ := by
    intro ω hω
    by_contra hc'
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hc'
    obtain ⟨h1, h2⟩ := hc'
    apply hω
    have h4 : approxLGDSet γ W δ' A B ω ≤ 4 * lgdMinSet (μ ω) δ A B :=
      approxLGDSet_le_four_mul hA hB h2
    have h4' : ((approxLGDSet γ W δ' A B ω : ℕ∞) : ℝ≥0∞) ≤
        4 * ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞) := by
      have := ENat.toENNReal_le.2 h4
      rwa [ENat.toENNReal_mul, ENat.toENNReal_ofNat] at this
    rw [prop32Lower, mem_ofPred_eq]
    calc ((approxLGDSet γ W δ A B ω : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-L ^ (0.9 : ℝ)))
        ≤ ((approxLGDSet γ W δ' A B ω : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal Q *
            ENNReal.ofReal (Real.exp (-L ^ (0.9 : ℝ))) := by gcongr; exact h1
      _ ≤ 4 * ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal Q *
            ENNReal.ofReal (Real.exp (-L ^ (0.9 : ℝ))) := by gcongr
      _ = ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞) *
            ENNReal.ofReal (4 * Q * Real.exp (-L ^ (0.9 : ℝ))) := by
          rw [ENNReal.ofReal_mul (p := 4 * Q) (by positivity),
            ENNReal.ofReal_mul (p := 4) (q := Q) (by norm_num), ENNReal.ofReal_ofNat]; ring
      _ ≤ ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞) * 1 := by
          gcongr; rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hQ
      _ = _ := mul_one _
  -- the probabilities
  have hp35 := h35 δ' ⟨hδ'0, hδ'5⟩ δ ⟨hδ0, hδδ'⟩ A B hadm
  have hpcv := hcv δ ⟨hδ0, hδ1'⟩
  have hδ'c : δ' ^ c₅ ≤ δ ^ c := by
    rw [Real.rpow_def_of_pos hδ'0, Real.rpow_def_of_pos hδ0, hlogδ', hlogδ]
    refine Real.exp_le_exp.2 ?_
    have : c ≤ c₅ / 2 := min_le_left _ _
    nlinarith
  have hδc1 : δ ^ c₁ ≤ δ ^ c := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_right _ _)
  have hhalf : δ ^ (c / 2) ≤ 1 / 2 := by
    have := Real.rpow_le_rpow hδ0.le hδc.le (by positivity : 0 ≤ c / 2)
    rwa [← Real.rpow_mul (by norm_num), show 2 / c * (c / 2) = 1 by field_simp,
      Real.rpow_one] at this
  have hsplit : δ ^ c = δ ^ (c / 2) * δ ^ (c / 2) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  calc P (prop32Lower γ W μ δ A B)ᶜ
      ≤ P (lem35Event γ W δ' δ A B)ᶜ + P {ω | ∀ u ∈ dzzV, ∀ v ∈ dzzV,
          approxLGD γ W (p32Up δ) u v ω ≤ 4 * lgdDZZ (μ ω) δ u v}ᶜ :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (δ' ^ c₅) + ENNReal.ofReal (δ ^ c₁) := add_le_add hp35 hpcv
    _ ≤ ENNReal.ofReal (δ ^ c) + ENNReal.ofReal (δ ^ c) :=
        add_le_add (ENNReal.ofReal_le_ofReal hδ'c) (ENNReal.ofReal_le_ofReal hδc1)
    _ = ENNReal.ofReal (2 * δ ^ c) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    _ ≤ ENNReal.ofReal (δ ^ (c / 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hsplit]
        have : 0 ≤ δ ^ (c / 2) := by positivity
        nlinarith

end DZZ
end LQGMetric
