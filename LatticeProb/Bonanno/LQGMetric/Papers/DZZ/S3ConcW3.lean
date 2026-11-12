/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcW3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcW2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcL3

/-!
# Walled good sets: `DZZDistLip{1,2}CoreIn` at a dyadic wall (P2-DZZCONCW)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`), proof of Prop 3.17, l. 1572–1594 (part 1) and
l. 1631–1645 (part 2), for `D'_S`, `S = cellsInside B`, and `D = D^{dzzWall B̄ μIn}`
(Remark 5.2, l. 2281–2284; D117, D123).

* `DZZGoodCoreOn`: `DZZGoodCore` (S3ConcH) with `coarseLogDOn S` (S3ConcI0);
* `DZZDistLip1CoreIn`, `DZZDistLip2CoreIn`: `DZZDistLip{1,2}Core` (S3ConcH) for the pairs inside
  `B̄^ξ`;
* **`dzzDistLip1CoreIn_of`**, **`dzzDistLip2CoreIn_of`**: copies of `dzzDistLip1Core_of_eStar`,
  `dzzDistLip2Core_of_eStar` (S3ConcL3), with the walled `𝓔*` bounds `dzzEStar{1,2}_unif_inside`
  (S3ConcW2) applied to the mixing white noise `wnMix W κ δ` (`isWhiteNoise_wnMix`, S3ConcI1)
  and the walled core `goodCoreOn_of_eStar` (S3ConcL2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- DZZ's good set `𝒜 ⊆ 𝒜_δ` with (eq-distance-Lip) for `D'_S` (walled `DZZGoodCore`). -/
def DZZGoodCoreOn (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (S : Set DyBox) (δ : ℝ)
    (A B : Set ℂ) (ℓ τ ε : ℝ) : Prop :=
  ∃ 𝒜 : Set (CoarseIdx (dzzCmc γ) δ → ℝ), 𝒜 ⊆ CoarseGood γ (dzzCmc γ) δ ∧
    P.real {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ 𝒜} ≤ ε ∧
    ∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, (∀ s, |x s - x' s| ≤ ℓ) →
      |coarseLogDOn S γ (dzzCmc γ) δ A B x - coarseLogDOn S γ (dzzCmc γ) δ A B x'| ≤ τ

/-- **DZZ l. 1572–1594, walled at `B̄`.** -/
def DZZDistLip1CoreIn (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (Bw : DyBox) (ξ : ℝ) :
    Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B → InsideXi Bw ξ A B →
    ∀ ι ∈ Ioo (0 : ℝ) 1, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      DZZGoodCoreOn P γ W (cellsInside Bw) δ (A δ) (B δ) (a * ι * Real.log δ⁻¹)
        (ι * Real.log δ⁻¹) (δ ^ (a * ι))

/-- **DZZ l. 1631–1645, walled at `B̄`.** -/
def DZZDistLip2CoreIn (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (Bw : DyBox) (ξ : ℝ) :
    Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B → InsideXi Bw ξ A B →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      DZZGoodCoreOn P γ W (cellsInside Bw) δ (A δ) (B δ) (Real.log δ⁻¹ ^ (0.9 : ℝ))
        (Real.log δ⁻¹ ^ (0.93 : ℝ)) (δ ^ a)

lemma dzzGoodCoreOn_mono {γ δ : ℝ} {S : Set DyBox} {A B : Set ℂ} {ℓ τ τ' ε ε' : ℝ}
    (h : DZZGoodCoreOn P γ W S δ A B ℓ τ ε) (hτ : τ ≤ τ') (hε : ε ≤ ε') :
    DZZGoodCoreOn P γ W S δ A B ℓ τ' ε' := by
  obtain ⟨𝒜, h1, h2, h3⟩ := h
  exact ⟨𝒜, h1, h2.trans hε, fun x hx x' hx' hxx => (h3 x hx x' hx' hxx).trans hτ⟩

/-- **DZZ Prop 3.17, l. 1572–1594, walled at `B̄`** (copy of `dzzDistLip1Core_of_eStar`). -/
theorem dzzDistLip1CoreIn_of (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (Bw : DyBox) {ξ : ℝ} (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) (hX : L32UpperCrossInside γ Bw ξ) :
    DZZDistLip1CoreIn P γ W Bw ξ := by
  obtain ⟨c, hc, hE⟩ := dzzEStar1_unif_inside.{u, u} hW hγ hγ2 Bw hξ hξc hX
  set α := max 24 (eStarS γ ξ)⁻¹ with hα_def
  have hα : 0 < α := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨c', hc', δ₁, hδ₁, hg⟩ := measureReal_not_coarseGood_le hW hγ hγ2
  set a := min (2 / (γ * α)) (min c c' / 2) with ha_def
  have hcc := lt_min hc hc'
  have ha : 0 < a := lt_min (by positivity) (by linarith)
  have ha1 : a ≤ 2 / (γ * α) := min_le_left _ _
  have ha2 : 2 * a ≤ min c c' := by
    have := min_le_right (2 / (γ * α)) (min c c' / 2); linarith
  have hγa : γ * a ≤ 2 / α := by
    calc γ * a ≤ γ * (2 / (γ * α)) := mul_le_mul_of_nonneg_left ha1 hγ.le
      _ = 2 / α := by field_simp
  refine ⟨a, ha, fun A B hAB hin ι hι => ?_⟩
  have hι0 := hι.1
  obtain ⟨δ₀, hδ₀, hD⟩ := hE α (le_max_left _ _) (le_max_right _ _) A B hAB hin ι hι
  obtain ⟨δ₂, hδ₂, hev⟩ := exists_delta_of_eventually
    (ev_exp_neg_le (k := a * ι) (by positivity) (by norm_num : (0 : ℝ) < 1 / 11))
  refine ⟨min (min δ₀ δ₁) (min δ₂ 1), lt_min (lt_min hδ₀ hδ₁) (lt_min hδ₂ one_pos),
    fun δ hδ => ?_⟩
  have hδ0 := hδ.1
  have hδa : δ < δ₀ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδb : δ < δ₁ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδc : δ < δ₂ := hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ < 1 := hδ.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hL : 0 ≤ Real.log δ⁻¹ := by rw [Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  set L := Real.log δ⁻¹
  have hEm : (P.prod P).real (eStarEvent (cellsInside Bw) γ (wnMix W (dzzCmc γ) δ)
      (fun p => dzzWall Bw.closedBox (dzzMuIn γ (wnMix W (dzzCmc γ) δ) p)) δ (ι / α * L)
        (ι / 4 * L) (A δ) (B δ))ᶜ ≤ δ ^ c :=
    ENNReal.toReal_le_of_le_ofReal (by positivity)
      (hD δ ⟨hδ0, hδa⟩ (isWhiteNoise_wnMix hW (dzzCmc γ) δ))
  have hιL : 0 ≤ ι * L := by positivity
  have hr : γ * (a * ι * L) / 2 ≤ ι / α * L := by
    calc γ * (a * ι * L) / 2 = (γ * a) * (ι * L) / 2 := by ring
      _ ≤ (2 / α) * (ι * L) / 2 := by gcongr
      _ = ι / α * L := by field_simp
  refine dzzGoodCoreOn_mono (goodCoreOn_of_eStar hW (cellsInside Bw) Bw.closedBox hγ hγ2 hδ0
    (by positivity) hr (hg δ ⟨hδ0, hδb⟩) hEm) (by nlinarith) ?_
  refine rpow_add_ten_le hδ0 hδ1 ?_ ?_ (hev δ ⟨hδ0, hδc⟩)
  · have := min_le_left c c'; nlinarith [hι.2]
  · have := min_le_right c c'; nlinarith [hι.2]

/-- **DZZ Prop 3.17, l. 1631–1645, walled at `B̄`** (copy of `dzzDistLip2Core_of_eStar`, with
the window exponent `α = 2/γ`). -/
theorem dzzDistLip2CoreIn_of (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (Bw : DyBox) {ξ : ℝ} (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) (hX : L32UpperCrossInside γ Bw ξ) :
    DZZDistLip2CoreIn P γ W Bw ξ := by
  obtain ⟨c, hc, hE⟩ := dzzEStar2_unif_inside.{u, u} hW hγ hγ2 Bw hξ hξc hX
  set α := 2 / γ with hα_def
  have hα : 0 < α := by positivity
  obtain ⟨c', hc', δ₁, hδ₁, hg⟩ := measureReal_not_coarseGood_le hW hγ hγ2
  set a := min c c' / 2 with ha_def
  have hcc := lt_min hc hc'
  have ha : 0 < a := by positivity
  have hγα : γ / 2 ≤ α⁻¹ := by rw [hα_def, inv_div]
  refine ⟨a, ha, fun A B hAB hin => ?_⟩
  obtain ⟨δ₀, hδ₀, hD⟩ := hE α hα A B hAB hin
  have ev : ∀ᶠ L : ℝ in atTop, Real.exp (-(a * L)) ≤ 1 / 11 ∧
      2 * L ^ (0.91 : ℝ) ≤ 1 * L ^ (0.93 : ℝ) := by
    filter_upwards [ev_exp_neg_le (k := a) ha (by norm_num : (0 : ℝ) < 1 / 11),
      ev_rpow_le (p := 0.91) (q := 0.93) (a := 1) (by norm_num) one_pos 2] with L h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨δ₂, hδ₂, hev⟩ := exists_delta_of_eventually ev
  refine ⟨min (min δ₀ δ₁) (min δ₂ 1), lt_min (lt_min hδ₀ hδ₁) (lt_min hδ₂ one_pos),
    fun δ hδ => ?_⟩
  have hδ0 := hδ.1
  have hδa : δ < δ₀ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδb : δ < δ₁ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδc : δ < δ₂ := hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ < 1 := hδ.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hL : 0 ≤ Real.log δ⁻¹ := by rw [Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  obtain ⟨hq, hτ⟩ := hev δ ⟨hδ0, hδc⟩
  set L := Real.log δ⁻¹
  have hEm : (P.prod P).real (eStarEvent (cellsInside Bw) γ (wnMix W (dzzCmc γ) δ)
      (fun p => dzzWall Bw.closedBox (dzzMuIn γ (wnMix W (dzzCmc γ) δ) p))
        δ (α⁻¹ * L ^ (0.9 : ℝ)) (L ^ (0.91 : ℝ)) (A δ) (B δ))ᶜ ≤ δ ^ c :=
    ENNReal.toReal_le_of_le_ofReal (by positivity)
      (hD δ ⟨hδ0, hδa⟩ (isWhiteNoise_wnMix hW (dzzCmc γ) δ))
  have hL9 : 0 ≤ L ^ (0.9 : ℝ) := by positivity
  have hr : γ * L ^ (0.9 : ℝ) / 2 ≤ α⁻¹ * L ^ (0.9 : ℝ) := by
    calc γ * L ^ (0.9 : ℝ) / 2 = γ / 2 * L ^ (0.9 : ℝ) := by ring
      _ ≤ α⁻¹ * L ^ (0.9 : ℝ) := by gcongr
  refine dzzGoodCoreOn_mono (goodCoreOn_of_eStar hW (cellsInside Bw) Bw.closedBox hγ hγ2 hδ0
    hL9 hr (hg δ ⟨hδ0, hδb⟩) hEm) (by linarith) ?_
  refine rpow_add_ten_le hδ0 hδ1 ?_ ?_ hq
  · have := min_le_left c c'; linarith
  · have := min_le_right c c'; linarith

end DZZ
end LQGMetric
