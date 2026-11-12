/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_10Neg at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_10Moment
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 3.10 for `p ≤ 0`

Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
proof of Proposition 3.10 (`prop-internal-moment`), first sentence (T:1872): "For `p < 0`, the
bound (eqn-internal-moment) follows from the lower bound of Proposition 3.1."

We apply Proposition 3.1 (at the centre `0`, through `prop3_1_centre_box`) to the two vertical
segments `K₁ = {1/4} × [1/4,3/4]`, `K₂ = {3/4} × [1/4,3/4]` of `U = 𝕊`; the internal diameter of
`𝕣𝕊` dominates `D_h(𝕣K₁, 𝕣K₂; 𝕣𝕊)`. Prop 3.1 gives superpolynomial (in `A`) lower tails; the
moment bound is `lintegral_rpow_neg_le_of_tail`. The constants of Prop 3.1 are those of one
realization of the field; they are made uniform over all realizations `(Ω, P, h)` by working on the
canonical space `(DistC, μ, id)` and using the uniqueness of the law of a normalized whole-plane GFF
(`CircleAvg.map_eq_of_isNormalizedWPGFF`) with `Measure.le_map_apply` (no measurability of the
events needed).
-/

noncomputable section

open MeasureTheory Set Complex
open scoped ENNReal ComplexOrder

namespace LQGMetric.DFGPS
open Blueprint

/-- **Law transfer**: probabilities of events of a normalized whole-plane GFF are bounded by the
canonical ones (any set, measurable or not). -/
lemma prob_le_canonical {μ : Measure DistC} (hμ : IsNormalizedWPGFF id μ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC) (hh : IsNormalizedWPGFF h P)
    (S : Set DistC) : P {ω | h ω ∈ S} ≤ μ S := by
  have hmap : P.map h = μ := by
    rw [CircleAvg.map_eq_of_isNormalizedWPGFF hh hμ, Measure.map_id]
  calc P {ω | h ω ∈ S} = P (h ⁻¹' S) := rfl
    _ ≤ P.map h S := Measure.le_map_apply hh.1.measurable.aemeasurable S
    _ = μ S := by rw [hmap]

/-- the unit square as a product of intervals -/
lemma unitSq_eq : Ioo (0 : ℝ) 1 ×ℂ Ioo (0 : ℝ) 1 =
    {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < 1} := by
  ext z
  simp only [mem_reProdIm, mem_Ioo, mem_ofPred_eq]
  tauto

lemma rS_eq_scaleSet_box (𝕣 : ℝ) : rS 𝕣 = scaleSet 𝕣 0 (Ioo (0 : ℝ) 1 ×ℂ Ioo (0 : ℝ) 1) := by
  rw [unitSq_eq]; rfl

/-- `D(A, B; V) ≤ sup_{u,v ∈ A'} D(u, v; V)` when `A, B ⊆ A'` and `A` is nonempty. -/
lemma setDistIn_le_internalDiam (D : ContMetric) {A B A' V : Set ℂ} {u : ℂ} (hu : u ∈ A)
    {v : ℂ} (hv : v ∈ B) (hA : A ⊆ A') (hB : B ⊆ A') :
    setDistIn D A B V ≤ internalDiam D A' V :=
  (iInf₂_le_of_le u hu (iInf₂_le_of_le v hv le_rfl)).trans
    (le_iSup₂_of_le u (hA hu) (le_iSup₂_of_le v (hB hv) le_rfl))

/-- **Lower tail of the internal diameter of `𝕣𝕊`** (Prop 3.1, lower bound), on the canonical
space: superpolynomially small probability that it is `< A⁻¹ 𝔠_𝕣 e^{ξ h_𝕣(0)}`. -/
theorem diam_rS_lower_tail (h31 : Prop3_1) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {μ : Measure DistC} [IsProbabilityMeasure μ] (hμ : IsNormalizedWPGFF id μ) :
    ∀ p : ℝ, 0 < p → ∃ C A₀ : ℝ, ∀ A, A₀ < A → ∀ 𝕣 : ℝ, 0 < 𝕣 →
      μ {g | internalDiam (D g) (rS 𝕣) (rS 𝕣) <
        ENNReal.ofReal (A⁻¹ * scaleFac (xiGamma γ) c g 𝕣 0)} ≤ ENNReal.ofReal (C * A ^ (-p)) := by
  intro p hp
  obtain ⟨C, A₀, hC⟩ := prop3_1_centre_box h31 hγ0 hγ2 hD (a₁ := 1 / 4) (b₁ := 1 / 4)
    (c₁ := 1 / 4) (d₁ := 3 / 4) (a₂ := 3 / 4) (b₂ := 3 / 4) (c₂ := 1 / 4) (d₂ := 3 / 4)
    (X₀ := 0) (X₁ := 1) (Y₀ := 0) (Y₁ := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hμ p hp
  refine ⟨C, A₀, fun A hA 𝕣 h𝕣 => le_trans (measure_mono fun g hg => ?_) (hC A hA 𝕣 h𝕣 0)⟩
  simp only [mem_ofPred_eq, mem_compl_iff] at hg ⊢
  rintro ⟨h1, -⟩
  refine absurd (h1.trans ?_) (not_le.2 hg)
  have hsub : ∀ a : ℝ, 0 < a → a < 1 → scaleSet 𝕣 0 (Icc a a ×ℂ Icc (1 / 4) (3 / 4)) ⊆ rS 𝕣 := by
    intro a ha0 ha1 w hw
    rw [rS_eq_scaleSet_box, mem_scaleSet_Ioo h𝕣]
    rw [mem_scaleSet_Icc h𝕣] at hw
    simp only [zero_re, zero_im, zero_add] at hw ⊢
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [hw.1.1, hw.1.2, hw.2.1, hw.2.2]
  have hmem : ∀ a : ℝ, (⟨𝕣 * a, 𝕣 * (1 / 4)⟩ : ℂ) ∈
      scaleSet 𝕣 0 (Icc a a ×ℂ Icc (1 / 4) (3 / 4)) := by
    intro a
    rw [mem_scaleSet_Icc h𝕣]
    simp only [zero_re, zero_im, zero_add]
    refine ⟨⟨le_rfl, le_rfl⟩, le_rfl, ?_⟩
    nlinarith
  rw [← rS_eq_scaleSet_box]
  exact setDistIn_le_internalDiam _ (hmem _) (hmem _) (hsub _ (by norm_num) (by norm_num))
    (hsub _ (by norm_num) (by norm_num))

/-- **DFGPS Prop 3.10 for `p ≤ 0`** (T:1872) -/
theorem prop3_10_nonpos (h31 : Prop3_1) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {p : ℝ} (hp : p ≤ 0) :
    ∃ Cp : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC), IsNormalizedWPGFF h P →
      ∀ 𝕣 : ℝ, 0 < 𝕣 → ∫⁻ ω, (ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) 𝕣 0)⁻¹ *
          internalDiam (D (h ω)) (rS 𝕣) (rS 𝕣)) ^ p ∂P ≤ ENNReal.ofReal Cp := by
  rcases hp.eq_or_lt with rfl | hp
  · refine ⟨1, fun P _ h _ 𝕣 _ => ?_⟩
    simp
  obtain ⟨μ, hμP, hμ⟩ := exists_canonical_normGFF
  obtain ⟨C, A₀, hC⟩ := diam_rS_lower_tail h31 hγ0 hγ2 hD hμ (1 - p) (by linarith)
  set t₀ := max 1 (A₀ + 1)
  refine ⟨momBd (-p) (1 - p) (max C 0) t₀, fun P _ h hh 𝕣 h𝕣 => ?_⟩
  refine lintegral_rpow_neg_le_of_tail P _ hp (by linarith) (le_max_right _ _) (le_max_left _ _)
    fun t ht => ?_
  have hA : A₀ < t := by have := le_max_right 1 (A₀ + 1); linarith
  have ht0 : 0 < t := by have := le_max_left 1 (A₀ + 1); linarith
  refine le_trans ?_ ((hC t hA 𝕣 h𝕣).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht0.le _))))
  refine le_trans (measure_mono fun ω hω => ?_) (prob_le_canonical hμ P h hh _)
  simp only [mem_ofPred_eq] at hω ⊢
  set s := scaleFac (xiGamma γ) c (h ω) 𝕣 0
  have hs : 0 < s := mul_pos (hD.tightness.1 𝕣 h𝕣) (Real.exp_pos _)
  by_contra hcon
  rw [not_lt] at hcon
  refine absurd hω (not_lt.2 ?_)
  calc ENNReal.ofReal t⁻¹ = ENNReal.ofReal s⁻¹ * ENNReal.ofReal (t⁻¹ * s) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
    _ ≤ _ := by
        rw [ENNReal.ofReal_inv_of_pos hs]
        exact mul_le_mul_right hcon _

end LQGMetric.DFGPS
