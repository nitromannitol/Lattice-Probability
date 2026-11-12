/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Thm11Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm11

/-!
# DDDF Theorem 1 (1) = `Blueprint.DDDFThm1_1` from (UpperHolder), (LowerHolder) (task P2-DDDF6e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 155–160, 1385–1490, 1648. See `S6Thm11` for the
plan: continuity for every `ω`, tightness by the modulus criterion (Arzelà–Ascoli), bi-Hölder
subsequential limits by Portmanteau on closed Hölder sets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace LQGMetric
namespace DDDF
namespace S6Thm

open WhiteNoise Blueprint DFGPS

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

local notation "SQ" => C(closedUnitSquare × closedUnitSquare, ℝ)

omit [IsProbabilityMeasure P] in
/-- tightness from the uniform upper Hölder bound (modulus criterion) -/
theorem tight_of_upper {I : Set ℝ} (X : ℝ → Ω → SQ) (hXm : ∀ δ ∈ I, Measurable (X δ))
    (hpm : ∀ δ ∈ I, ∀ ω, X δ ω ∈ pmetSet closedUnitSquare) {β : ℝ} (hβ : 0 < β)
    (hUp : ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ, ∀ δ ∈ I,
      P {ω | ∃ x y : closedUnitSquare, C * ‖(x : ℂ) - y‖ ^ β < X δ ω (x, y)} ≤
        ENNReal.ofReal ζ) :
    IsTightMeasureSet {μ | ∃ δ ∈ I, μ = P.map (X δ)} := by
  have : ConnectedSpace closedUnitSquare := isConnected_iff_connectedSpace.1
    (DFGPS.convex_closedUnitSquare.isConnected ⟨0, by simp [closedUnitSquare]⟩)
  refine LFPP.isTightMeasureSet_of_modulus _ ?_ ?_
  · rintro μ ⟨δ, hδ, rfl⟩
    have hms : MeasurableSet (pmetSet closedUnitSquare)ᶜ :=
      (isClosed_pmetSet _).isOpen_compl.measurableSet
    have e : {d : SQ | ¬ ((∀ x, d (x, x) = 0) ∧ ∀ x y z, d (x, z) ≤ d (x, y) + d (y, z))} =
        (pmetSet closedUnitSquare)ᶜ := rfl
    rw [e, Measure.map_apply (hXm δ hδ) hms]
    have e2 : X δ ⁻¹' (pmetSet closedUnitSquare)ᶜ = ∅ := by
      ext ω
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
      exact hpm δ hδ ω
    rw [e2, measure_empty]
  · intro ζ hζ
    obtain ⟨C, hC⟩ := hUp ζ hζ
    set C' := max C 1
    have hC' : 0 < C' := lt_max_of_lt_right one_pos
    refine ⟨(ζ / C') ^ (1 / β), by positivity, ?_⟩
    rintro μ ⟨δ, hδ, rfl⟩
    rw [show {d : SQ | ¬ ∀ z w : closedUnitSquare, dist z w ≤ (ζ / C') ^ (1 / β) → d (z, w) ≤ ζ}
      = {d : SQ | ∀ z w : closedUnitSquare, dist z w ≤ (ζ / C') ^ (1 / β) → d (z, w) ≤ ζ}ᶜ from rfl,
      Measure.map_apply (hXm δ hδ) (isClosed_modulusSet _ _ _).isOpen_compl.measurableSet]
    refine (measure_mono fun ω hω => ?_).trans (hC δ hδ)
    simp only [mem_preimage, mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨z, w, hzw, hlt⟩ := hω
    refine ⟨z, w, ?_⟩
    have hd : ‖(z : ℂ) - w‖ ≤ (ζ / C') ^ (1 / β) := by
      rwa [Subtype.dist_eq, dist_eq_norm] at hzw
    have h1 : ‖(z : ℂ) - w‖ ^ β ≤ ζ / C' := by
      calc ‖(z : ℂ) - w‖ ^ β ≤ ((ζ / C') ^ (1 / β)) ^ β :=
            Real.rpow_le_rpow (norm_nonneg _) hd hβ.le
        _ = ζ / C' := by
            rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hβ.ne', Real.rpow_one]
    have h2 : C * ‖(z : ℂ) - w‖ ^ β ≤ ζ := by
      calc C * ‖(z : ℂ) - w‖ ^ β ≤ C' * ‖(z : ℂ) - w‖ ^ β :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ C' * (ζ / C') := mul_le_mul_of_nonneg_left h1 hC'.le
        _ = ζ := by field_simp
    exact lt_of_le_of_lt h2 hlt

omit [IsProbabilityMeasure P] in
/-- bi-Hölder subsequential limits from the uniform Hölder bounds (Portmanteau) -/
theorem biHolder_of_bounds {I : Set ℝ} (X : ℝ → Ω → SQ) (hXm : ∀ δ ∈ I, Measurable (X δ))
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hUp : ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ, ∀ δ ∈ I,
      P {ω | ∃ x y : closedUnitSquare, C * ‖(x : ℂ) - y‖ ^ β < X δ ω (x, y)} ≤
        ENNReal.ofReal ζ)
    (hLow : ∀ ζ : ℝ, 0 < ζ → ∃ c : ℝ, 0 < c ∧ ∀ δ ∈ I,
      P {ω | ∃ x y : closedUnitSquare, X δ ω (x, y) < c * ‖(x : ℂ) - y‖ ^ α} ≤
        ENNReal.ofReal ζ)
    (δn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure SQ) (μ : ProbabilityMeasure SQ)
    (hν : ∀ n, δn n ∈ I ∧ (ν n : Measure SQ) = P.map (X (δn n))) (hlim : Tendsto ν atTop (𝓝 μ)) :
    ∀ᵐ d ∂(μ : Measure SQ), IsBiHolderSq d := by
  rw [ae_iff]
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  set e : ℝ := (ε : ℝ) / 2
  have he : 0 < e := by have : (0 : ℝ) < ε := hε; positivity
  obtain ⟨C, hC⟩ := hUp e he
  obtain ⟨c, hc, hc'⟩ := hLow e he
  set C' := max C 1
  set F : Set SQ := {d | ∀ x y : closedUnitSquare,
    c * ‖(x : ℂ) - y‖ ^ α ≤ d (x, y) ∧ d (x, y) ≤ C' * ‖(x : ℂ) - y‖ ^ β}
  have hF : IsClosed F := by
    have e1 : F = ⋂ x : closedUnitSquare, ⋂ y : closedUnitSquare,
        ({d : SQ | c * ‖(x : ℂ) - y‖ ^ α ≤ d (x, y)} ∩
          {d | d (x, y) ≤ C' * ‖(x : ℂ) - y‖ ^ β}) := by
      ext d; simp only [F, mem_iInter, mem_inter_iff, mem_ofPred_eq]
    rw [e1]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      (isClosed_le continuous_const (continuous_eval_const _)).inter
        (isClosed_le (continuous_eval_const _) continuous_const)
  have hνF : ∀ n, (ν n : Measure SQ) Fᶜ ≤ ENNReal.ofReal (ε : ℝ) := by
    intro n
    obtain ⟨hδ, hνn⟩ := hν n
    rw [hνn, Measure.map_apply (hXm _ hδ) hF.isOpen_compl.measurableSet]
    have hsub : X (δn n) ⁻¹' Fᶜ ⊆
        {ω | ∃ x y : closedUnitSquare, C * ‖(x : ℂ) - y‖ ^ β < X (δn n) ω (x, y)} ∪
        {ω | ∃ x y : closedUnitSquare, X (δn n) ω (x, y) < c * ‖(x : ℂ) - y‖ ^ α} := by
      intro ω hω
      simp only [mem_preimage, mem_compl_iff, F, mem_ofPred_eq, not_forall, not_and_or,
        not_le] at hω
      obtain ⟨x, y, h | h⟩ := hω
      · exact Or.inr ⟨x, y, h⟩
      · exact Or.inl ⟨x, y, lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (by positivity)) h⟩
    calc P (X (δn n) ⁻¹' Fᶜ) ≤ _ := measure_mono hsub
      _ ≤ ENNReal.ofReal e + ENNReal.ofReal e :=
        (measure_union_le _ _).trans (add_le_add (hC _ hδ) (hc' _ hδ))
      _ = ENNReal.ofReal (ε : ℝ) := by
        rw [← ENNReal.ofReal_add he.le he.le]; congr 1; simp only [e]; ring
  have hlim' := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF
  have hge : 1 - ENNReal.ofReal (ε : ℝ) ≤ (μ : Measure SQ) F := by
    refine le_trans ?_ hlim'
    refine Filter.le_limsup_of_frequently_le (Frequently.of_forall fun n => ?_)
    have := prob_compl_eq_one_sub (μ := (ν n : Measure SQ)) hF.isOpen_compl.measurableSet
    rw [compl_compl] at this
    rw [this]
    exact tsub_le_tsub_left (hνF n) _
  have hbad : {d : SQ | ¬ IsBiHolderSq d} ⊆ Fᶜ :=
    fun d hd hdF => hd ⟨c, C', α, β, hc, lt_max_of_lt_right one_pos, hα, hβ, hdF⟩
  calc (μ : Measure SQ) {d | ¬ IsBiHolderSq d} ≤ (μ : Measure SQ) Fᶜ := measure_mono hbad
    _ = 1 - (μ : Measure SQ) F := prob_compl_eq_one_sub hF.measurableSet
    _ ≤ 1 - (1 - ENNReal.ofReal (ε : ℝ)) := tsub_le_tsub_left hge _
    _ ≤ ENNReal.ofReal (ε : ℝ) := tsub_le_iff_right.2 le_add_tsub
    _ = ε := ENNReal.ofReal_coe_nnreal

end S6Thm
end DDDF
end LQGMetric
