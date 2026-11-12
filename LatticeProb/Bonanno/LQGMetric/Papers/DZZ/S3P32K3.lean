/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32K3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32K2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32Up

/-!
# Walled P3.2, K3: the events and the two halves for `(dzzWall K μ, approxLGDSetOn S)`
(P2-DZZ317K)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) Prop 3.2 (l. 807–812, proof l. 1087–1207) for the walled
LGD `D^K` (Remark 5.2, l. 2281–2284; decision D117 §3, route R2), with the walled approximate
distance `approxLGDSetOn S` (S3P32K1; D117: `S = cellsMeeting K`). The pairs are admissible
*inside* `K`
(`IsXiAdmissibleAtIn`: as `IsXiAdmissibleAt`, and moreover at distance `≥ ξ` from `Kᶜ`), see
the doubt in `handoff/P2-DZZ317K.md`.

* `prop32EventOn`, `prop32LowerOn`, `prop32UpperOn`, `lem35EventOn`, `p32CrossEventOn`;
* `DZZLemma35UOn` (walled L3.5, OPEN), `L32UpperCrossOn` (walled (Eq.boundDprime), OPEN),
  `DZZProp32UOn` (walled P3.2);
* **`dzz_prop32_lowerOn`**: the lower half from `L32BallCoverOn` and `DZZLemma35UOn`
  (copy of `dzz_prop32_lower`, S3P32Low);
* **`dzz_prop32_upperOn`**: the upper half from `L32UpperCrossOn` (copy of `dzz_prop32_upper`,
  S3P32Up; (Eq.lowerboundforDprime) transfers since `D' ≤ D'_S`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- `K^ξ := {z : |z − Kᶜ| ≥ ξ}`, the points of `K` at distance `≥ ξ` from its complement. -/
def kXi (K : Set ℂ) (ξ : ℝ) : Set ℂ := {z | ξ ≤ Metric.infDist z Kᶜ}

/-- Pairs admissible at `δ` (`IsXiAdmissibleAt`) lying in `K^ξ`. -/
def IsXiAdmissibleAtIn (K : Set ℂ) (ξ ξd δ : ℝ) (A B : Set ℂ) : Prop :=
  IsXiAdmissibleAt ξ ξd δ A B ∧ A ⊆ kXi K ξ ∧ B ⊆ kXi K ξ

lemma IsXiAdmissibleAtIn.of_rpow_le {K : Set ℂ} {ξ ξ₁ ξ₂ δ₁ δ₂ : ℝ} (h : δ₂ ^ ξ₂ ≤ δ₁ ^ ξ₁)
    {A B : Set ℂ} (hAB : IsXiAdmissibleAtIn K ξ ξ₁ δ₁ A B) : IsXiAdmissibleAtIn K ξ ξ₂ δ₂ A B :=
  ⟨hAB.1.of_rpow_le h, hAB.2⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The event of P3.2 for `(D^K, D'^K)`. -/
def prop32EventOn (S : Set DyBox) (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (δ : ℝ)
    (A B : Set ℂ) : Set Ω :=
  {ω | ((approxLGDSetOn S γ W δ A B ω : ℕ∞) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(Real.log δ⁻¹) ^ (0.9 : ℝ))) ≤
        ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞) ∧
      ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞) ≤
        ((approxLGDSetOn S γ W δ A B ω : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp ((Real.log δ⁻¹) ^ (0.9 : ℝ)))}

/-- The lower half of `prop32EventIn`. -/
def prop32LowerOn (S : Set DyBox) (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (δ : ℝ)
    (A B : Set ℂ) : Set Ω :=
  {ω | ((approxLGDSetOn S γ W δ A B ω : ℕ∞) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(Real.log δ⁻¹) ^ (0.9 : ℝ))) ≤
        ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞)}

/-- The upper half of `prop32EventIn`. -/
def prop32UpperOn (S : Set DyBox) (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (δ : ℝ)
    (A B : Set ℂ) : Set Ω :=
  {ω | ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞) ≤
        ((approxLGDSetOn S γ W δ A B ω : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp ((Real.log δ⁻¹) ^ (0.9 : ℝ)))}

omit [MeasurableSpace Ω] in
lemma prop32EventOn_eq (S : Set DyBox) (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (δ : ℝ)
    (A B : Set ℂ) :
    prop32EventOn S γ W μ δ A B = prop32LowerOn S γ W μ δ A B ∩ prop32UpperOn S γ W μ δ A B :=
  rfl

/-- The event (eq-280318) of Lemma 3.5 for `D'^K`, `δ' < δ`. -/
def lem35EventOn (S : Set DyBox) (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ δ' : ℝ) (A B : Set ℂ) : Set Ω :=
  {ω | ((approxLGDSetOn S γ W δ' A B ω : ℕ∞) : ℝ≥0∞) ≤
      ((approxLGDSetOn S γ W δ A B ω : ℕ∞) : ℝ≥0∞) *
        ENNReal.ofReal ((δ / δ') ^ 3 * Real.exp ((Real.log δ⁻¹) ^ (0.8 : ℝ)))}

/-- **Walled DZZ Lemma 3.5** (l. 907–916 for `D'^K`, uniform form; OPEN). -/
def DZZLemma35UOn (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (K : Set ℂ) (S : Set DyBox)
    (ξ ξd : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ δ' ∈ Ioo (0 : ℝ) δ,
    ∀ A B : Set ℂ, IsXiAdmissibleAtIn K ξ ξd δ A B →
      P (lem35EventOn S γ W δ δ' A B)ᶜ ≤ ENNReal.ofReal (δ ^ c)

/-- The event of (Eq.boundDprime) for `D^K_δ` and `D'^K_δ`. -/
def p32CrossEventOn (S : Set DyBox) (γ : ℝ) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (δ : ℝ)
    (A B : Set ℂ) : Set Ω :=
  {ω | ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞) ≤
      ((approxLGDSetOn S γ W δ A B ω : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal (4 ^ (kL37 γ δ + 2) * (lamP32 δ + 1)) +
        ENNReal.ofReal (2 * (δ ^ (-(dzzCMc γ / 2)) * lamP32 δ) + 8)}

/-- **Walled (Eq.boundDprime)** (DZZ l. 1088–1103 + Remark 5.2; OPEN). -/
def L32UpperCrossOn (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (K : Set ℂ) (S : Set DyBox)
    (μ : Ω → Measure ℂ) (ξ ξd : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ A B : Set ℂ,
    IsXiAdmissibleAtIn K ξ ξd δ A B → P (p32CrossEventOn S γ W μ δ A B)ᶜ ≤ ENNReal.ofReal (δ ^ c)

/-- **Walled DZZ Proposition 3.2**, uniform form. -/
def DZZProp32UOn (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (K : Set ℂ) (S : Set DyBox)
    (μ : Ω → Measure ℂ) (ξ ξd : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ A B : Set ℂ,
    IsXiAdmissibleAtIn K ξ ξd δ A B → P (prop32EventOn S γ W μ δ A B)ᶜ ≤ ENNReal.ofReal (δ ^ c)

omit [MeasurableSpace Ω] in
/-- Pointwise `D'^K_{δ'} ≤ 4 D_δ` on `𝕍` gives the same bound for the minima over `A × B`. -/
lemma approxLGDSetOn_le_four_mul {S : Set DyBox} {γ : ℝ} {W : WNSpace → Ω → ℝ} {μ : Measure ℂ}
    {δ δ' : ℝ} {ω : Ω} {A B : Set ℂ} (hA : A ⊆ dzzV) (hB : B ⊆ dzzV)
    (h : ∀ u ∈ dzzV, ∀ v ∈ dzzV, approxLGDOn S γ W δ' u v ω ≤ 4 * lgdDZZ μ δ u v) :
    approxLGDSetOn S γ W δ' A B ω ≤ 4 * lgdMinSet μ δ A B := by
  unfold lgdMinSet approxLGDSetOn approxDistSetOn
  simp only [ENat.mul_iInf_of_ne (show (4 : ℕ∞) ≠ 0 by norm_num)]
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  exact (iInf₂_le x hx).trans ((iInf₂_le y hy).trans (h x (hA hx) y (hB hy)))

set_option maxHeartbeats 1000000 in
/-- **Lower bound of DZZ Proposition 3.2** (l. 1159–1169), uniformly over pairs admissible at
`δ`, from (eq-Euclidean-Ball-covering) in the form `L32BallCover` and Lemma 3.5. -/
theorem dzz_prop32_lowerOn {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {K : Set ℂ} {S : Set DyBox} {μ : Ω → Measure ℂ}
    (hcov : L32BallCoverOn P γ W S μ)
    {ξ ξd : ℝ} (hξ : 0 < ξ) (hξd : ξd < dzzCMc γ)
    (h35U : ∀ ξd' : ℝ, ξd' < dzzCMc γ → DZZLemma35UOn P γ W K S ξ ξd') :
    ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ A B : Set ℂ,
      IsXiAdmissibleAtIn K ξ ξd δ A B →
        P (prop32LowerOn S γ W μ δ A B)ᶜ ≤ ENNReal.ofReal (δ ^ c) := by
  set ξ₂ := (ξd + dzzCMc γ) / 2 with hξ₂
  obtain ⟨c₅, hc₅, δ₅, hδ₅, h35⟩ := h35U ξ₂ (by linarith)
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
  have hadm : IsXiAdmissibleAtIn K ξ ξ₂ δ' A B := by
    refine hAB.of_rpow_le ?_
    rw [Real.rpow_def_of_pos hδ'0, Real.rpow_def_of_pos hδ0, hlogδ', hlogδ]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hA : A ⊆ dzzV := hAB.1.subset_left.trans (dzzVXi_sub_dzzV ξ)
  have hB : B ⊆ dzzV := hAB.1.subset_right.trans (dzzVXi_sub_dzzV ξ)
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
  have hsub : (prop32LowerOn S γ W μ δ A B)ᶜ ⊆ (lem35EventOn S γ W δ' δ A B)ᶜ ∪
      {ω | ∀ u ∈ dzzV, ∀ v ∈ dzzV,
        approxLGDOn S γ W (p32Up δ) u v ω ≤ 4 * lgdDZZ (μ ω) δ u v}ᶜ := by
    intro ω hω
    by_contra hc'
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hc'
    obtain ⟨h1, h2⟩ := hc'
    apply hω
    have h4 : approxLGDSetOn S γ W δ' A B ω ≤ 4 * lgdMinSet (μ ω) δ A B :=
      approxLGDSetOn_le_four_mul hA hB h2
    have h4' : ((approxLGDSetOn S γ W δ' A B ω : ℕ∞) : ℝ≥0∞) ≤
        4 * ((lgdMinSet (μ ω) δ A B : ℕ∞) : ℝ≥0∞) := by
      have := ENat.toENNReal_le.2 h4
      rwa [ENat.toENNReal_mul, ENat.toENNReal_ofNat] at this
    rw [prop32LowerOn, mem_ofPred_eq]
    calc ((approxLGDSetOn S γ W δ A B ω : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-L ^ (0.9 : ℝ)))
        ≤ ((approxLGDSetOn S γ W δ' A B ω : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal Q *
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
  calc P (prop32LowerOn S γ W μ δ A B)ᶜ
      ≤ P (lem35EventOn S γ W δ' δ A B)ᶜ + P {ω | ∀ u ∈ dzzV, ∀ v ∈ dzzV,
          approxLGDOn S γ W (p32Up δ) u v ω ≤ 4 * lgdDZZ (μ ω) δ u v}ᶜ :=
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

set_option maxHeartbeats 1000000 in
/-- **Upper bound of DZZ Proposition 3.2** (l. 1098–1103) from (Eq.boundDprime). -/
theorem dzz_prop32_upperOn {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Kw : Set ℂ} {S : Set DyBox} {μ : Ω → Measure ℂ} {ξ ξd : ℝ}
    (hX : L32UpperCrossOn P γ W Kw S μ ξ ξd) (hξ : 0 < ξ) (hξd : ξd < dzzCMc γ) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ A B : Set ℂ,
      IsXiAdmissibleAtIn Kw ξ ξd δ A B →
        P (prop32UpperOn S γ W μ δ A B)ᶜ ≤ ENNReal.ofReal (δ ^ c) := by
  have := hW.isProbabilityMeasure
  set C := dzzCmc γ with hCdef
  set c := dzzCMc γ with hcdef
  have hC : 0 < C := by have := l31theta_pos hγ hγ2; rw [hCdef]; unfold dzzCmc; linarith
  have hc : 0 < c := dzzCMc_pos γ
  set ι := c / 2 with hιdef
  obtain ⟨c₁, hc₁, δ₁, hδ₁, hcr⟩ := hX
  obtain ⟨δ₃, hδ₃, hasym⟩ := l35_asym hC hc hξ hξd
  set K := l31const γ + 1 with hKdef
  have hK : 0 < K := by rw [hKdef]; unfold l31const; positivity
  set c0 := min c₁ 1 with hc0def
  have hc0 : 0 < c0 := lt_min hc₁ one_pos
  refine ⟨c0 / 2, by positivity, min (min δ₁ δ₃) (min (min (1 / 3) (Real.exp (-1)))
    ((1 / (1 + K)) ^ (2 / c0))), by positivity, fun δ hδ A B hAB => ?_⟩
  obtain ⟨hδ0, hδ⟩ := hδ
  have hδ1' : δ < δ₁ := hδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ3' : δ < δ₃ := hδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδh : δ < 1 / 3 := hδ.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hδe : δ < Real.exp (-1) := hδ.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hδK : δ < (1 / (1 + K)) ^ (2 / c0) :=
    hδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ < 1 := by linarith
  obtain ⟨as1, as2, -, as4⟩ := hasym δ ⟨hδ0, hδ3'⟩
  set L := Real.log δ⁻¹ with hLdef
  have hL1 : 1 ≤ L := by
    have := Real.log_lt_log hδ0 hδe
    rw [Real.log_exp] at this
    rw [hLdef, Real.log_inv]; linarith
  have hL0 : 0 < L := by linarith
  set k := kL37 γ δ with hkdef
  set lam := lamP32 δ with hlamdef
  set Q := Real.exp (L ^ (0.8 : ℝ)) with hQdef
  have hQ1 : 1 ≤ Q := Real.one_le_exp (Real.rpow_nonneg hL0.le _)
  have hlamQ : lam ≤ Q := Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have hlam1 : 1 ≤ lam := Real.one_le_exp (Real.rpow_nonneg hL0.le _)
  have hδι : 1 ≤ δ ^ (-ι) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0 hδ1.le
    (by rw [hιdef]; linarith)
  have hkx : (2 : ℝ) ^ k ≤ 4 * C * L := by
    have hfl : ⌊4 * C * L⌋₊ ≠ 0 := by
      have := Nat.floor_pos.2 (show (1 : ℝ) ≤ 4 * C * L by linarith); omega
    have h1 := Nat.pow_log_le_self 2 hfl
    have h2 : ((2 ^ k : ℕ) : ℝ) ≤ (⌊4 * C * L⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2; exact h2.trans (Nat.floor_le (by linarith))
  have ha : 4 ^ (k + 2) * (lam + 1) ≤ Q / 2 := by
    have e4 : (4 : ℝ) ^ (k + 2) = 16 * ((2 : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul, pow_add, show (4 : ℝ) ^ 2 = 16 by norm_num, mul_comm,
        show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm k 2]
    have h2k : ((2 : ℝ) ^ k) ^ 2 ≤ (4 * C * L) ^ 2 := pow_le_pow_left₀ (by positivity) hkx 2
    have hl2 : lam + 1 ≤ 2 * lam := by linarith
    calc 4 ^ (k + 2) * (lam + 1) ≤ (16 * (4 * C * L) ^ 2) * (2 * lam) := by
          rw [e4]; gcongr
      _ = 1024 * C ^ 2 * L ^ 2 * Real.exp (L ^ (0.7 : ℝ)) / 2 := by
          rw [hlamdef, lamP32]; ring
      _ ≤ Q / 2 := by rw [hQdef]; linarith
  have hb : 2 * (δ ^ (-ι) * lam) + 8 ≤ 20 * δ ^ (-ι) * (Q / 2) := by
    have h1 : δ ^ (-ι) * lam ≤ δ ^ (-ι) * Q := mul_le_mul_of_nonneg_left hlamQ (by positivity)
    have h2 : 1 ≤ δ ^ (-ι) * Q := one_le_mul_of_one_le_of_one_le hδι hQ1
    nlinarith
  -- the deterministic inclusion
  have hsub : p32CrossEventOn S γ W μ δ A B ∩ cellSizeEvent γ W δ ⊆
      prop32UpperOn S γ W μ δ A B := by
    rintro ω ⟨hD, hcs⟩
    set m := approxLQG γ W ω with hmdef
    have hside : ∀ b, IsCell m δ b → b.side ≤ δ ^ c := fun b hb => (hcs.2 b hb).2
    set n := ⌈20 * δ ^ (-ι)⌉₊ with hndef
    have hn : (n : ℝ) ≤ 20 * δ ^ (-ι) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hlow := approxDistSet_ge_of_dist (m := m) (δ := δ) (s := δ ^ c) (n := n) hside
      (A := A) (B := B) fun x hx y hy => by
        have := hAB.1.dist_ge x hx y hy
        have h2 : 2 * δ ^ c * n ≤ 2 * δ ^ c * (20 * δ ^ (-ι) + 1) :=
          mul_le_mul_of_nonneg_left hn (by positivity)
        linarith
    have hN : ENNReal.ofReal (20 * δ ^ (-ι)) ≤
        ((approxDistSet m δ A B : ℕ∞) : ℝ≥0∞) := by
      refine le_trans ?_ (ENat.toENNReal_le.2 hlow)
      rw [show (n : ℕ∞) + 1 = ((n + 1 : ℕ) : ℕ∞) by push_cast; rfl, ENat.toENNReal_coe,
        ← ENNReal.ofReal_natCast]
      refine ENNReal.ofReal_le_ofReal ?_
      push_cast
      linarith [Nat.le_ceil (20 * δ ^ (-ι))]
    have hN' : ENNReal.ofReal (20 * δ ^ (-ι)) ≤
        ((approxLGDSetOn S γ W δ A B ω : ℕ∞) : ℝ≥0∞) :=
      hN.trans (ENat.toENNReal_le.2 (approxDistSet_le_approxDistSetOn S _ _ A B))
    have hfin := ennreal_chain hD ha hb (by positivity) hN' (by positivity)
    rw [prop32UpperOn, mem_ofPred_eq]
    refine hfin.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))) _)
  -- the probability
  have p1 := hcr δ ⟨hδ0, hδ1'⟩ A B hAB
  have p2 := dzz_lemma31_bound hW hγ hγ2 hδ0 (show δ ≤ 1 / 2 by linarith)
  have p2' : P (cellSizeEvent γ W δ)ᶜ ≤ ENNReal.ofReal (l31const γ * δ) :=
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
      (by unfold l31const; positivity)).2 p2
  have hm1 : δ ^ c₁ ≤ δ ^ c0 := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_left _ _)
  have hm2 : δ ≤ δ ^ c0 := by
    have := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_right c₁ 1)
    rwa [Real.rpow_one] at this
  have hl31 : 0 ≤ l31const γ := by unfold l31const; positivity
  have hhalf : δ ^ (c0 / 2) ≤ 1 / (1 + K) := by
    have := Real.rpow_le_rpow hδ0.le hδK.le (by positivity : 0 ≤ c0 / 2)
    rwa [← Real.rpow_mul (by positivity), show 2 / c0 * (c0 / 2) = 1 by field_simp,
      Real.rpow_one] at this
  have hsplit : δ ^ c0 = δ ^ (c0 / 2) * δ ^ (c0 / 2) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  calc P (prop32UpperOn S γ W μ δ A B)ᶜ
      ≤ P ((p32CrossEventOn S γ W μ δ A B)ᶜ ∪ (cellSizeEvent γ W δ)ᶜ) := by
        refine measure_mono ?_
        rw [← compl_inter]; exact compl_subset_compl.2 hsub
    _ ≤ ENNReal.ofReal (δ ^ c₁) + ENNReal.ofReal (l31const γ * δ) :=
        (measure_union_le _ _).trans (add_le_add p1 p2')
    _ = ENNReal.ofReal (δ ^ c₁ + l31const γ * δ) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (δ ^ (c0 / 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h0 : 0 ≤ δ ^ (c0 / 2) := by positivity
        have h3 : δ ^ c₁ + l31const γ * δ ≤ (1 + K) * δ ^ c0 := by
          have : l31const γ * δ ≤ K * δ ^ c0 := by
            rw [hKdef]; nlinarith
          linarith
        have h4 : (1 + K) * δ ^ (c0 / 2) ≤ 1 := by
          rw [le_div_iff₀ (by positivity)] at hhalf; linarith
        rw [hsplit] at h3
        nlinarith
end DZZ
end LQGMetric
