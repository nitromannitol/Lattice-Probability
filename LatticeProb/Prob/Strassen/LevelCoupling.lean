import LatticeProb.Prob.Strassen.HallPoset
import LatticeProb.Prob.Strassen.Rounding
import LatticeProb.Prob.Strassen.DiscreteCoupling

/-!
# E. The level-`F` approximate coupling

At a finite level `F : Finset S`, domination gives (integer Strassen on the poset `F → Bool`) a
transport plan with row sums `roundLow (wt ν F) D` and column sums `roundHigh (wt μ F) D`,
supported on `{(y, x) | y ≤ x}`. The resulting discrete coupling `cplMeasure F D k` is a
probability measure supported on `couplingSupport S`, and its marginals approximate `μ` and `ν`
on every cylinder over a subset of `F` to within `card (F → Bool) / D`
(`exists_cplMeasure_of_domination`).
-/

open MeasureTheory Filter Topology

namespace LatticeProb

namespace StrassenAux

attribute [local instance 10] Classical.propDecidable

/-- At level `F`, domination gives an integer transport plan with row sums `roundLow (wt ν F) D` and
column sums `roundHigh (wt μ F) D`, supported on `{(y, x) | y ≤ x}`. -/
private theorem exists_transport_roundLow_roundHigh_of_domination {S : Type}
    (μ ν : Measure (S → Bool)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A → ν A ≤ μ A)
    (F : Finset S) (D : ℕ) :
    ∃ k : (F → Bool) → (F → Bool) → ℕ,
      (∀ y, ∑ x, k y x = roundLow (wt ν F) D y) ∧
      (∀ x, ∑ y, k y x = roundHigh (wt μ F) D x) ∧ ∀ y x, k y x ≠ 0 → y ≤ x := by
  obtain ⟨hμ0, hμ1⟩ := wt_nonneg_and_sum_wt_eq_one μ F
  obtain ⟨hν0, hν1⟩ := wt_nonneg_and_sum_wt_eq_one ν F
  refine exists_transport_of_hall_condition (m := roundHigh (wt μ F) D) (n := roundLow (wt ν F) D)
      ?_ ?_
  · rw [sum_roundHigh_eq (wt μ F) hμ0 hμ1 D, sum_roundLow_eq (wt ν F) hν0 hν1 D]
  · intro U hU
    have hA : ((∑ y ∈ U, roundLow (wt ν F) D y : ℕ) : ℝ) ≤ D * ∑ y ∈ U, wt ν F y :=
      sum_roundLow_le_mul_sum_of_isUpperSet (wt ν F) hν0 hν1 D U hU
    have hB : D * ∑ y ∈ U, wt ν F y ≤ D * ∑ y ∈ U, wt μ F y :=
      mul_le_mul_of_nonneg_left (sum_wt_le_sum_wt_of_isUpperSet μ ν hdom F U hU) (Nat.cast_nonneg D)
    have hC : D * ∑ y ∈ U, wt μ F y ≤ ((∑ y ∈ U, roundHigh (wt μ F) D y : ℕ) : ℝ) :=
      mul_sum_le_sum_roundHigh_of_isUpperSet' (wt μ F) hμ0 hμ1 D U hU
    exact_mod_cast le_trans hA (le_trans hB hC)


/-- The first marginal of the level-`F` coupling approximates `μ` on cylinders over `G ⊆ F` to
within `card (F → Bool) / D`. -/
private theorem abs_cplMeasure_prod_univ_sub_measure_le_div {S : Type} (μ : Measure (S → Bool))
    [IsProbabilityMeasure μ]
    (F G : Finset S) (hGF : G ⊆ F) (T : Set (G → Bool)) (_hT : MeasurableSet T)
    (D : ℕ) (hD : D ≠ 0) (k : (F → Bool) → (F → Bool) → ℕ)
    (hcol : ∀ x, ∑ y, k y x = roundHigh (wt μ F) D x) :
    |(cplMeasure F D k (cylinder G T ×ˢ Set.univ)).toReal - (μ (cylinder G T)).toReal|
      ≤ Fintype.card (F → Bool) / D := by
  classical
  let E : Finset (↥F → Bool) := Finset.univ.filter (fun x => ext F x ∈ G.restrict ⁻¹' T)
  have hcyl : (μ (G.restrict ⁻¹' T)).toReal = ∑ x ∈ E, wt μ F x :=
      measure_cylinder_toReal_eq_sum_wt μ F G hGF T
  have hwt := wt_nonneg_and_sum_wt_eq_one μ F
  have h24 := (abs_sum_roundLow_and_roundHigh_sub_mul_sum_le_card (wt μ F) hwt.1 hwt.2 D E).2
  have h24' : |(∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ)) - D * ∑ x ∈ E, wt μ F x|
      ≤ (Fintype.card (↥F → Bool) : ℝ) := (by simpa only [Nat.cast_sum] using h24)
  have hD0 : (0 : ℝ) < D := (by exact_mod_cast Nat.pos_of_ne_zero hD)
  have hDnz : (D : ℝ) ≠ 0 := ne_of_gt hD0
  have hDenn : (D : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (by exact_mod_cast hD)
  have hfin : ∀ x ∈ E, ((∑ y, k y x : ℕ) : ENNReal) / D ≠ ⊤ := fun x _ =>
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hDenn
  have hnum : (∑ x ∈ E, ((∑ y, k y x : ℕ) : ℝ))
      = (∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ)) :=
    Finset.sum_congr rfl (fun x _ => (by rw [hcol x]))
  have hmeas : MeasurableSet (G.restrict ⁻¹' T) :=
      (by exact measurableSet_preimage_restrict (F := G) T)
  have hmarg : (cplMeasure F D k ((G.restrict ⁻¹' T) ×ˢ Set.univ)).toReal
      = (∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ)) / (D : ℝ) := (by
    rw [cplMeasure_prod_univ_eq_sum_div F D k (G.restrict ⁻¹' T) hmeas]
    rw [ENNReal.toReal_sum hfin]
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
    rw [← Finset.sum_div, hnum])
  have hAub : (∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ)) - D * ∑ x ∈ E, wt μ F x
      ≤ (Fintype.card (↥F → Bool) : ℝ) := le_trans (le_abs_self _) h24'
  have hBub : D * ∑ x ∈ E, wt μ F x - (∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ))
      ≤ (Fintype.card (↥F → Bool) : ℝ) := (by
    have h := neg_le_abs ((∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ))
      - D * ∑ x ∈ E, wt μ F x)
    rw [neg_sub] at h
    exact le_trans h h24')
  have hkey1 : (∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ)) / (D : ℝ) - ∑ x ∈ E, wt μ F x
      = ((∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ)) - D * ∑ x ∈ E, wt μ F x) / (D : ℝ) := (by
    rw [sub_div, mul_div_cancel_left₀ _ hDnz])
  have hkey2 : ∑ x ∈ E, wt μ F x - (∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ)) / (D : ℝ)
      = (D * ∑ x ∈ E, wt μ F x - (∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ))) / (D : ℝ) := (by
    rw [sub_div, mul_div_cancel_left₀ _ hDnz])
  change |(cplMeasure F D k ((G.restrict ⁻¹' T) ×ˢ Set.univ)).toReal
      - (μ (G.restrict ⁻¹' T)).toReal| ≤ (Fintype.card (↥F → Bool) : ℝ) / (D : ℝ)
  rw [hmarg, hcyl, abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · rw [hkey1]; exact div_le_div_of_nonneg_right hAub (le_of_lt hD0)
  · rw [hkey2]; exact div_le_div_of_nonneg_right hBub (le_of_lt hD0)


/-- The second marginal of the level-`F` coupling approximates `ν` on cylinders over `G ⊆ F` to
within `card (F → Bool) / D`. -/
private theorem abs_cplMeasure_univ_prod_sub_measure_le_div {S : Type} (ν : Measure (S → Bool))
    [IsProbabilityMeasure ν]
    (F G : Finset S) (hGF : G ⊆ F) (T : Set (G → Bool)) (_hT : MeasurableSet T)
    (D : ℕ) (hD : D ≠ 0) (k : (F → Bool) → (F → Bool) → ℕ)
    (hrow : ∀ y, ∑ x, k y x = roundLow (wt ν F) D y) :
    |(cplMeasure F D k (Set.univ ×ˢ cylinder G T)).toReal - (ν (cylinder G T)).toReal|
      ≤ Fintype.card (F → Bool) / D := by
  classical
  have hDne : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  have hDpos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hD)
  have hD0 : (D : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr hD
  have hCyl : MeasurableSet (cylinder G T : Set (S → Bool)) := measurableSet_preimage_restrict
      (S := S) G T
  have h1 : (cplMeasure F D k (Set.univ ×ˢ cylinder G T)).toReal
      = ∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
          (roundLow (wt ν F) D y : ℝ) / (D : ℝ) := (by
    rw [cplMeasure_univ_prod_eq_sum_div (S := S) F D k (cylinder G T) hCyl]
    rw [ENNReal.toReal_sum (fun y _ => ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hD0)]
    refine Finset.sum_congr rfl ?_
    intro y hy
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, hrow y])
  obtain ⟨ha, ha1⟩ := wt_nonneg_and_sum_wt_eq_one (S := S) ν F
  have h24 : |(∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
        (roundLow (wt ν F) D y : ℝ))
      - (D : ℝ) * ∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
        wt ν F y| ≤ ((Fintype.card (F → Bool) : ℕ) : ℝ) := (by
    have h := (abs_sum_roundLow_and_roundHigh_sub_mul_sum_le_card (P := F → Bool) (wt ν F) ha ha1 D
      (Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T))).1
    rw [Nat.cast_sum] at h
    exact h)
  have h2 : (ν (cylinder G T)).toReal
      = ∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T), wt ν F y :=
    measure_cylinder_toReal_eq_sum_wt (S := S) ν F G hGF T
  have h3 : |(∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
        (roundLow (wt ν F) D y : ℝ) / (D : ℝ))
      - ∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T), wt ν F y|
      = |(∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
          (roundLow (wt ν F) D y : ℝ))
        - (D : ℝ) * ∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
          wt ν F y| / (D : ℝ) := (by
    rw [← Finset.sum_div]
    have hX : (∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
          (roundLow (wt ν F) D y : ℝ)) / (D : ℝ)
        - ∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T), wt ν F y
        = ((∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
            (roundLow (wt ν F) D y : ℝ))
          - (D : ℝ) * ∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
            wt ν F y) / (D : ℝ) := (by
      rw [eq_div_iff hDne, sub_mul, div_mul_cancel₀ _ hDne]
      ring)
    rw [hX, abs_div, abs_of_pos hDpos])
  rw [h1, h2, h3]
  exact div_le_div_of_nonneg_right h24 (le_of_lt hDpos)


/-- **The level-`F` approximate coupling.** Domination gives a probability measure `π`, supported
(up to null sets) on `couplingSupport S`, whose marginals approximate `μ` and `ν` on every cylinder
over a subset of `F` to within `card (F → Bool) / D`. -/
theorem exists_cplMeasure_of_domination {S : Type} [Countable S] (μ ν : Measure (S → Bool))
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A → ν A ≤ μ A)
    (F : Finset S) (D : ℕ) (hD : D ≠ 0) :
    ∃ π : Measure ((S → Bool) × (S → Bool)), IsProbabilityMeasure π ∧
      π (couplingSupport S)ᶜ = 0 ∧
      ∀ G : Finset S, G ⊆ F → ∀ T : Set (G → Bool), MeasurableSet T →
        |(π (cylinder G T ×ˢ Set.univ)).toReal - (μ (cylinder G T)).toReal|
            ≤ Fintype.card (F → Bool) / D ∧
        |(π (Set.univ ×ˢ cylinder G T)).toReal - (ν (cylinder G T)).toReal|
            ≤ Fintype.card (F → Bool) / D := by
  obtain ⟨kk, hrw, hcl, hmn⟩ := exists_transport_roundLow_roundHigh_of_domination μ ν hdom F D
  exact ⟨cplMeasure F D kk, isProbabilityMeasure_cplMeasure_of_sum_eq F D hD kk (by
      rw [Finset.sum_congr rfl (fun y _ => hrw y)]
      exact sum_roundLow_eq (wt ν F) (wt_nonneg_and_sum_wt_eq_one ν F).1
          (wt_nonneg_and_sum_wt_eq_one ν F).2 D),
    cplMeasure_compl_couplingSupport_eq_zero F D kk hmn, fun G hGF T hT =>
      ⟨abs_cplMeasure_prod_univ_sub_measure_le_div μ F G hGF T hT D hD kk hcl,
       abs_cplMeasure_univ_prod_sub_measure_le_div ν F G hGF T hT D hD kk hrw⟩⟩

end StrassenAux

end LatticeProb
