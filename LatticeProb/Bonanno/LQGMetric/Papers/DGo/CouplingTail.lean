/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.CouplingTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.GaussianTail

/-!
# Ding–Goswami Prop 3.3: from the variance bounds (3.9)–(3.10) to the tail (task P2-DGO, WP-105)

Source: Ding–Goswami, arXiv:1610.09998, `Watabiki_final.tex` (cited `DGo:`), proof of
Proposition 3.3 (`prop:coupling`, DGo:549–555), DGo:604–616: "suppose that (3.9)
`Var(Δ_δ(v) − Δ_δ(w)) = O(|v − w|/δ)` for `|v − w| ≤ δ` and (3.10) `max Var Δ_δ(v) = O(1)`.
Now subdivide `V` into rectangles of diameter at most `δ` … `|𝔑| ≤ 8δ^{-2}` … the conditions of
Lemma 3.4 are satisfied … with `C = O(1)` and `C' = O(1)`."

* `dgo_prop33_tail_of_var`: for a continuous centred Gaussian field `Δ` on the square
  `V = ferniqueBox y b` with (3.9) and (3.10),
  `P(max_V Δ ≥ √(2σ² log m²) + C_F √A + x) ≤ e^{−x²/(2σ²)}`, `m = ⌈2b/δ⌉₊`.
* `dgo_prop33_of_var`: **the conclusion of DGo Prop 3.3** from (3.9)–(3.10) holding uniformly
  in `δ ∈ (0, δ₁]`, `δ₁ < 1`: `∃ K, P(max_V Δ_δ ≥ K √(log δ⁻¹) + x) ≤ e^{−x²/(2σ²)}`.
* `dgo_prop33_abs_of_var`: the two-sided form (apply the above to `±Δ_δ`), which is the
  "uniform comparison" `max_V |ĥ^U_δ − η_δ| ≤ K √(log δ⁻¹) + x` used by DG Lemma 3.7
  (DG:1104, cited there as [DG16, Prop 3.2]); `dgo_prop33_abs_log` its superpolynomial form
  `P(max_V |Δ_δ| ≥ ζ log δ⁻¹) ≤ 2 e^{−ζ²(log δ⁻¹)²/(8σ²)}`.

Squares of side `b/m ≤ δ/2` (diameter `≤ δ/√2`) replace DGo's rectangles of diameter `≤ δ`;
`|𝔑| = m² ≤ ((2b+1)/δ)²` for `δ ≤ 1` (DGo: `≤ 8δ^{-2}`). The variance bounds (3.9)–(3.10) for
`Δ_δ = ĥ^U_δ − η_δ` are hypotheses here (they are the remaining nodes of DGo Prop 3.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Real

namespace LQGMetric
namespace DGo

open SupTail DZZ

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma norm_sub_le_of_mem_ferniqueBox {x₀ u v : ℂ} {s : ℝ} (hu : u ∈ ferniqueBox x₀ s)
    (hv : v ∈ ferniqueBox x₀ s) : ‖u - v‖ ≤ 2 * s := by
  obtain ⟨⟨hu1, hu2⟩, hu3, hu4⟩ := hu
  obtain ⟨⟨hv1, hv2⟩, hv3, hv4⟩ := hv
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]
  have h1 : |u.re - v.re| ≤ s := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have h2 : |u.im - v.im| ≤ s := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  linarith

/-- The tail step of the proof of **DGo Prop 3.3** (DGo:604–616): (3.9)–(3.10) on the square
`V = ferniqueBox y b` give `P(max_V Δ ≥ √(2σ² log m²) + C_F √A + x) ≤ e^{−x²/(2σ²)}` with
`m = ⌈2b/δ⌉₊` (so `V` is the union of `m²` squares of side `≤ δ/2`). -/
theorem dgo_prop33_tail_of_var [IsFiniteMeasure P] {Δ : ℂ → Ω → ℝ}
    (hΔ : IsGaussianProcess Δ P) (h0 : ∀ v, ∫ ω, Δ v ω ∂P = 0) {y : ℂ} {b δ A σ2 : ℝ}
    (hb : 0 < b) (hδ : 0 < δ) (hA : 0 < A) (hσ : 0 < σ2)
    (hc : ∀ ω, ContinuousOn (fun v => Δ v ω) (ferniqueBox y b))
    (hinc : ∀ u ∈ ferniqueBox y b, ∀ v ∈ ferniqueBox y b, ‖u - v‖ ≤ δ →
      ∫ ω, (Δ v ω - Δ u ω) ^ 2 ∂P ≤ A * ‖u - v‖ / δ)
    (hvar : ∀ v ∈ ferniqueBox y b, Var[Δ v; P] ≤ σ2) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | Real.sqrt (2 * σ2 * Real.log ((⌈2 * b / δ⌉₊ : ℕ) ^ 2 : ℕ)) +
      ferniqueCF * Real.sqrt A + x ≤ ⨆ v : ferniqueBox y b, Δ v ω} ≤
        Real.exp (-x ^ 2 / (2 * σ2)) := by
  set m := ⌈2 * b / δ⌉₊ with hm_def
  have hm : 0 < m := Nat.ceil_pos.2 (by positivity)
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hs : 0 < b / m := div_pos hb hm'
  have h2s : 2 * (b / m) ≤ δ := by
    have h := Nat.le_ceil (2 * b / δ)
    rw [← hm_def, div_le_iff₀ hδ] at h
    rw [← mul_div_assoc, div_le_iff₀ hm']
    linarith
  have hsδ : b / m ≤ δ := by linarith
  have : NeZero m := ⟨hm.ne'⟩
  set ι := Fin m × Fin m
  set yy : ι → ℂ := fun kl => y + ⟨kl.1 * (b / m), kl.2 * (b / m)⟩
  have hsubB : ∀ kl : ι, ferniqueBox (yy kl) (b / m) ⊆ ferniqueBox y b :=
    fun kl => subBox_subset hb kl.1 kl.2
  have h34 := dgo_lemma34 (Y := fun _ => Δ) (y := yy) (b := fun _ => b / m) (P := P)
    (fun _ => hΔ) (fun _ => h0) (fun _ => hs) hA hσ
    (fun kl ω => (hc ω).mono (hsubB kl))
    (fun kl u hu v hv => by
      have hd : ‖u - v‖ ≤ δ := (norm_sub_le_of_mem_ferniqueBox hu hv).trans h2s
      refine (hinc u (hsubB kl hu) v (hsubB kl hv) hd).trans ?_
      have : 0 ≤ A * ‖u - v‖ := by positivity
      exact div_le_div_of_nonneg_left this hs hsδ)
    (fun kl v hv => hvar v (hsubB kl hv)) hx
  have hcard : Fintype.card ι = m ^ 2 := by simp [ι, sq]
  rw [hcard] at h34
  refine (measureReal_mono fun ω hω => ?_).trans h34
  simp only [mem_ofPred_eq] at hω ⊢
  refine hω.trans ?_
  have : Nonempty (ferniqueBox y b) := ⟨⟨y, mem_ferniqueBox_self hb.le⟩⟩
  refine ciSup_le fun v => ?_
  obtain ⟨k, l, hkl⟩ := exists_mem_subBox hb hm v.2
  have hbdd : BddAbove (range fun w : ferniqueBox (yy (k, l)) (b / m) => Δ w ω) := by
    have hK := (isCompact_ferniqueBox (yy (k, l)) (b / m)).bddAbove_image
      (f := fun w => Δ w ω) ((hc ω).mono (hsubB (k, l)))
    obtain ⟨M, hM⟩ := hK
    exact ⟨M, by rintro _ ⟨w, rfl⟩; exact hM ⟨w, w.2, rfl⟩⟩
  calc Δ v ω ≤ ⨆ w : ferniqueBox (yy (k, l)) (b / m), Δ w ω :=
        le_ciSup (f := fun w : ferniqueBox (yy (k, l)) (b / m) => Δ w ω) hbdd ⟨v, hkl⟩
    _ ≤ ⨆ kl : ι, ⨆ w : ferniqueBox (yy kl) (b / m), Δ w ω :=
        le_ciSup (f := fun kl : ι => ⨆ w : ferniqueBox (yy kl) (b / m), Δ w ω)
          (Finite.bddAbove_range _) (k, l)

/-- The constant `K = √(4σ²(1 + log(2b+1)/log δ₁⁻¹)) + C_F √A / √(log δ₁⁻¹)` of DGo Prop 3.3; it
depends only on `(b, A, σ², δ₁)`, i.e. on `(𝒰, ε)` in DGo's notation. -/
def prop33K (b A σ2 δ₁ : ℝ) : ℝ :=
  Real.sqrt (4 * σ2 * (1 + Real.log (2 * b + 1) / Real.log δ₁⁻¹)) +
    ferniqueCF * Real.sqrt A / Real.sqrt (Real.log δ₁⁻¹)

/-- `√(2σ² log m²) + C_F √A ≤ K √(log δ⁻¹)` for `m = ⌈2b/δ⌉₊`, `0 < δ ≤ δ₁ < 1`. -/
lemma prop33_const_le {b A σ2 δ δ₁ : ℝ} (hb : 0 < b) (hσ : 0 < σ2) (hδ : 0 < δ)
    (hδδ₁ : δ ≤ δ₁) (hδ₁ : δ₁ < 1) :
    Real.sqrt (2 * σ2 * Real.log ((⌈2 * b / δ⌉₊ : ℕ) ^ 2 : ℕ)) + ferniqueCF * Real.sqrt A ≤
      prop33K b A σ2 δ₁ * Real.sqrt (Real.log δ⁻¹) := by
  have hδ₁0 : 0 < δ₁ := hδ.trans_le hδδ₁
  set ℓ₁ := Real.log δ₁⁻¹
  set ℓ := Real.log δ⁻¹
  have hℓ₁ : 0 < ℓ₁ := Real.log_pos (one_lt_inv_iff₀.2 ⟨hδ₁0, hδ₁⟩)
  have hℓℓ₁ : ℓ₁ ≤ ℓ := Real.log_le_log (inv_pos.2 hδ₁0) ((inv_le_inv₀ hδ₁0 hδ).2 hδδ₁)
  have hℓ : 0 < ℓ := hℓ₁.trans_le hℓℓ₁
  set m := ⌈2 * b / δ⌉₊
  have hm : 0 < m := Nat.ceil_pos.2 (by positivity)
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hmle : (m : ℝ) ≤ (2 * b + 1) / δ := by
    have h1 := (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * b / δ)).le
    have h2 : (1 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    calc (m : ℝ) ≤ 2 * b / δ + 1 := h1
      _ ≤ 2 * b / δ + 1 / δ := by linarith
      _ = (2 * b + 1) / δ := by ring
  have hlogm : Real.log m ≤ Real.log (2 * b + 1) + ℓ := by
    refine (Real.log_le_log hm' hmle).trans_eq ?_
    rw [div_eq_mul_inv, Real.log_mul (by positivity) (by positivity)]
  set c := Real.log (2 * b + 1) / ℓ₁
  have hlog0 : 0 ≤ Real.log (2 * b + 1) := Real.log_nonneg (by linarith)
  have hc : Real.log (2 * b + 1) ≤ c * ℓ := by
    have : Real.log (2 * b + 1) = c * ℓ₁ := by simp only [c]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hℓℓ₁ (div_nonneg hlog0 hℓ₁.le)
  have h1 : Real.sqrt (2 * σ2 * Real.log ((m ^ 2 : ℕ) : ℝ)) ≤
      Real.sqrt (4 * σ2 * (1 + c)) * Real.sqrt ℓ := by
    rw [← Real.sqrt_mul (by have : 0 ≤ c := div_nonneg hlog0 hℓ₁.le; positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [Nat.cast_pow, Real.log_pow]
    push_cast
    nlinarith
  have h2 : ferniqueCF * Real.sqrt A ≤
      ferniqueCF * Real.sqrt A / Real.sqrt ℓ₁ * Real.sqrt ℓ := by
    have hs1 : 0 < Real.sqrt ℓ₁ := Real.sqrt_pos.2 hℓ₁
    rw [div_mul_eq_mul_div, le_div_iff₀ hs1]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hℓℓ₁)
      (mul_nonneg ferniqueCF_pos.le (Real.sqrt_nonneg _))
  unfold prop33K
  rw [add_mul]
  exact add_le_add h1 h2

/-- **DGo Prop 3.3 from (3.9)–(3.10)** (DGo:549–555, DGo:604–616): if for `0 < δ ≤ δ₁ < 1`
the continuous centred Gaussian field `Δ` on `V = ferniqueBox y b` satisfies (3.9)
`Var(Δ(v) − Δ(w)) ≤ A |v − w|/δ` for `|v − w| ≤ δ` and (3.10) `Var Δ(v) ≤ σ²`, then
`P(max_V Δ ≥ K √(log δ⁻¹) + x) ≤ e^{−x²/(2σ²)}` for `x ≥ 0`, with `K = prop33K b A σ² δ₁`. -/
theorem dgo_prop33_of_var [IsFiniteMeasure P] {Δ : ℂ → Ω → ℝ}
    (hΔ : IsGaussianProcess Δ P) (h0 : ∀ v, ∫ ω, Δ v ω ∂P = 0) {y : ℂ} {b δ δ₁ A σ2 : ℝ}
    (hb : 0 < b) (hδ : 0 < δ) (hδδ₁ : δ ≤ δ₁) (hδ₁ : δ₁ < 1) (hA : 0 < A) (hσ : 0 < σ2)
    (hc : ∀ ω, ContinuousOn (fun v => Δ v ω) (ferniqueBox y b))
    (hinc : ∀ u ∈ ferniqueBox y b, ∀ v ∈ ferniqueBox y b, ‖u - v‖ ≤ δ →
      ∫ ω, (Δ v ω - Δ u ω) ^ 2 ∂P ≤ A * ‖u - v‖ / δ)
    (hvar : ∀ v ∈ ferniqueBox y b, Var[Δ v; P] ≤ σ2) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | prop33K b A σ2 δ₁ * Real.sqrt (Real.log δ⁻¹) + x ≤
      ⨆ v : ferniqueBox y b, Δ v ω} ≤ Real.exp (-x ^ 2 / (2 * σ2)) := by
  refine (measureReal_mono fun ω hω => ?_).trans
    (dgo_prop33_tail_of_var hΔ h0 hb hδ hA hσ hc hinc hvar hx)
  simp only [mem_ofPred_eq] at hω ⊢
  have := prop33_const_le (A := A) hb hσ hδ hδδ₁ hδ₁
  linarith

/-- **Two-sided form** (the uniform comparison used by DG Lemma 3.7, DG:1104):
`P(max_V |Δ| ≥ K √(log δ⁻¹) + x) ≤ 2 e^{−x²/(2σ²)}`. -/
theorem dgo_prop33_abs_of_var [IsFiniteMeasure P] {Δ : ℂ → Ω → ℝ}
    (hΔ : IsGaussianProcess Δ P) (h0 : ∀ v, ∫ ω, Δ v ω ∂P = 0) {y : ℂ} {b δ δ₁ A σ2 : ℝ}
    (hb : 0 < b) (hδ : 0 < δ) (hδδ₁ : δ ≤ δ₁) (hδ₁ : δ₁ < 1) (hA : 0 < A) (hσ : 0 < σ2)
    (hc : ∀ ω, ContinuousOn (fun v => Δ v ω) (ferniqueBox y b))
    (hinc : ∀ u ∈ ferniqueBox y b, ∀ v ∈ ferniqueBox y b, ‖u - v‖ ≤ δ →
      ∫ ω, (Δ v ω - Δ u ω) ^ 2 ∂P ≤ A * ‖u - v‖ / δ)
    (hvar : ∀ v ∈ ferniqueBox y b, Var[Δ v; P] ≤ σ2) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | prop33K b A σ2 δ₁ * Real.sqrt (Real.log δ⁻¹) + x ≤
      ⨆ v : ferniqueBox y b, |Δ v ω|} ≤ 2 * Real.exp (-x ^ 2 / (2 * σ2)) := by
  set t := prop33K b A σ2 δ₁ * Real.sqrt (Real.log δ⁻¹) + x
  have h1 := dgo_prop33_of_var hΔ h0 hb hδ hδδ₁ hδ₁ hA hσ hc hinc hvar hx
  have h2 := dgo_prop33_of_var (Δ := fun v ω => -Δ v ω) (isGaussianProcess_neg hΔ)
    (fun v => by simp [integral_neg, h0]) hb hδ hδδ₁ hδ₁ hA hσ (fun ω => (hc ω).neg)
    (fun u hu v hv huv => by
      refine le_of_eq_of_le ?_ (hinc u hu v hv huv)
      congr 1; funext ω; ring)
    (fun v hv => by rw [variance_fun_neg]; exact hvar v hv) hx
  have : Nonempty (ferniqueBox y b) := ⟨⟨y, mem_ferniqueBox_self hb.le⟩⟩
  have hbdd : ∀ ω (s : ℝ), s ^ 2 = 1 →
      BddAbove (range fun v : ferniqueBox y b => s * Δ v ω) := by
    intro ω s _
    obtain ⟨M, hM⟩ := (isCompact_ferniqueBox y b).bddAbove_image
      (f := fun v => s * Δ v ω) (continuousOn_const.mul (hc ω))
    exact ⟨M, by rintro _ ⟨w, rfl⟩; exact hM ⟨w, w.2, rfl⟩⟩
  have hsub : {ω | t ≤ ⨆ v : ferniqueBox y b, |Δ v ω|} ⊆
      {ω | t ≤ ⨆ v : ferniqueBox y b, Δ v ω} ∪ {ω | t ≤ ⨆ v : ferniqueBox y b, -Δ v ω} := by
    intro ω hω
    by_contra hn
    simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hn hω
    have hle : ⨆ v : ferniqueBox y b, |Δ v ω| ≤
        max (⨆ v : ferniqueBox y b, Δ v ω) (⨆ v : ferniqueBox y b, -Δ v ω) :=
      ciSup_le fun v => by
        rw [abs_eq_max_neg]
        have e1 := le_ciSup (by simpa using hbdd ω 1 (by norm_num)) v
        have e2 := le_ciSup (by simpa using hbdd ω (-1) (by norm_num)) v
        exact max_le_max e1 e2
    exact absurd hω (not_le.2 (lt_of_le_of_lt hle (max_lt hn.1 hn.2)))
  calc P.real {ω | t ≤ ⨆ v : ferniqueBox y b, |Δ v ω|}
      ≤ P.real {ω | t ≤ ⨆ v : ferniqueBox y b, Δ v ω} +
          P.real {ω | t ≤ ⨆ v : ferniqueBox y b, -Δ v ω} :=
        (measureReal_mono hsub).trans (measureReal_union_le _ _)
    _ ≤ 2 * Real.exp (-x ^ 2 / (2 * σ2)) := by linarith

/-- **Superpolynomial form** (as used by DG Lemma 3.7, DG:1096–1105, and DDDF P21, DDDF:1007):
for `ζ > 0` and `log δ⁻¹ ≥ (2K/ζ)²`, `P(max_V |Δ| ≥ ζ log δ⁻¹) ≤ 2 e^{−ζ² (log δ⁻¹)²/(8σ²)}`. -/
theorem dgo_prop33_abs_log [IsFiniteMeasure P] {Δ : ℂ → Ω → ℝ}
    (hΔ : IsGaussianProcess Δ P) (h0 : ∀ v, ∫ ω, Δ v ω ∂P = 0) {y : ℂ} {b δ δ₁ A σ2 : ℝ}
    (hb : 0 < b) (hδ : 0 < δ) (hδδ₁ : δ ≤ δ₁) (hδ₁ : δ₁ < 1) (hA : 0 < A) (hσ : 0 < σ2)
    (hc : ∀ ω, ContinuousOn (fun v => Δ v ω) (ferniqueBox y b))
    (hinc : ∀ u ∈ ferniqueBox y b, ∀ v ∈ ferniqueBox y b, ‖u - v‖ ≤ δ →
      ∫ ω, (Δ v ω - Δ u ω) ^ 2 ∂P ≤ A * ‖u - v‖ / δ)
    (hvar : ∀ v ∈ ferniqueBox y b, Var[Δ v; P] ≤ σ2) {ζ : ℝ} (hζ : 0 < ζ)
    (hℓ : (2 * prop33K b A σ2 δ₁ / ζ) ^ 2 ≤ Real.log δ⁻¹) :
    P.real {ω | ζ * Real.log δ⁻¹ ≤ ⨆ v : ferniqueBox y b, |Δ v ω|} ≤
      2 * Real.exp (-(ζ * Real.log δ⁻¹) ^ 2 / (8 * σ2)) := by
  set ℓ := Real.log δ⁻¹
  set K := prop33K b A σ2 δ₁
  have hK : 0 ≤ K := add_nonneg (Real.sqrt_nonneg _)
    (div_nonneg (mul_nonneg ferniqueCF_pos.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hℓ0 : 0 ≤ ℓ := le_trans (sq_nonneg _) hℓ
  have hsq : 2 * K / ζ ≤ Real.sqrt ℓ := Real.le_sqrt_of_sq_le hℓ
  have hKℓ : K * Real.sqrt ℓ ≤ ζ * ℓ / 2 := by
    have h1 : 2 * K ≤ ζ * Real.sqrt ℓ := by rw [div_le_iff₀ hζ] at hsq; linarith
    have h2 : Real.sqrt ℓ * Real.sqrt ℓ = ℓ := Real.mul_self_sqrt hℓ0
    nlinarith [Real.sqrt_nonneg ℓ]
  have hx : 0 ≤ ζ * ℓ / 2 := by positivity
  have h := dgo_prop33_abs_of_var hΔ h0 hb hδ hδδ₁ hδ₁ hA hσ hc hinc hvar hx
  refine (measureReal_mono fun ω hω => ?_).trans (h.trans_eq ?_)
  · simp only [mem_ofPred_eq] at hω ⊢
    linarith
  · congr 2
    field_simp
    ring

end DGo
end LQGMetric
