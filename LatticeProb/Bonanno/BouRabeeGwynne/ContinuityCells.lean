/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ContinuityCells at commit fdb5cad; linter settings are added. -/
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Order.Disjointed

set_option linter.unusedSectionVars false

/-!
# Common small continuity cells on a compact spatial region

Small open balls with null frontier cover the compact region. Taking finite
disjoint differences preserves null frontiers and the diameter bound. The
reference measure may be the finite sum for a whole family of exit balls.
-/

open MeasureTheory Set Metric
namespace BouRabeeGwynne

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

private lemma null_frontier_union (γ : Measure X) {S T : Set X}
    (hS : γ (frontier S) = 0) (hT : γ (frontier T) = 0) :
    γ (frontier (S ∪ T)) = 0 :=
  measure_mono_null ((frontier_union_subset S T).trans
    (union_subset_union inter_subset_left inter_subset_right)) (measure_union_null hS hT)

private lemma null_frontier_diff (γ : Measure X) {S T : Set X}
    (hS : γ (frontier S) = 0) (hT : γ (frontier T) = 0) :
    γ (frontier (S \ T)) = 0 := by
  have hsub : frontier (S \ T) ⊆ frontier S ∪ frontier T := by
    simpa only [sdiff_eq, frontier_compl] using
      (frontier_inter_subset S Tᶜ).trans
        (union_subset_union inter_subset_left inter_subset_right)
  exact measure_mono_null hsub (measure_union_null hS hT)

private lemma null_frontier_finset_sup {ι : Type*} (γ : Measure X)
    (f : ι → Set X) (hf : ∀ i, γ (frontier (f i)) = 0) (F : Finset ι) :
    γ (frontier (F.sup f)) = 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert i F hi ih =>
    rw [Finset.sup_insert]
    exact null_frontier_union γ (hf i) ih

/-- One family of disjoint measurable bounded cells covers the chosen compact
region, has arbitrarily small diameter, and has null frontier for the supplied
reference measure. It can therefore serve all laws dominated by that measure. -/
theorem exists_finite_small_nullFrontier_cells (γ : Measure X) [SFinite γ]
    {K : Set X} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (E : Fin n → Set X),
      Pairwise (fun i j ↦ Disjoint (E i) (E j)) ∧ K ⊆ ⋃ i, E i ∧
      (∀ i, MeasurableSet (E i)) ∧ (∀ i, Bornology.IsBounded (E i)) ∧
      (∀ i, γ (frontier (E i)) = 0) ∧
      ∀ i, ∀ x ∈ E i, ∀ y ∈ E i, dist x y < ε := by
  classical
  have hballs (x : X) : ∃ r : ℝ, 0 < r ∧ r < ε / 2 ∧ γ (frontier (ball x r)) = 0 := by
    obtain ⟨r, hr, hnull⟩ := exists_null_frontier_thickening γ {x} (half_pos hε)
    exact ⟨r, hr.1, hr.2, by simpa only [thickening_singleton] using hnull⟩
  let r : X → ℝ := fun x ↦ (hballs x).choose
  have hr (x : X) : 0 < r x ∧ r x < ε / 2 ∧ γ (frontier (ball x (r x))) = 0 :=
    (hballs x).choose_spec
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun x ↦ ball x (r x))
    (fun _ ↦ isOpen_ball) (fun x hx ↦ mem_iUnion.mpr ⟨x, mem_ball_self (hr x).1⟩)
  let n : ℕ := Fintype.card ↥F
  let e : ↥F ≃ Fin n := Fintype.equivFin ↥F
  let c : Fin n → X := fun i ↦ (e.symm i).val
  let B : Fin n → Set X := fun i ↦ ball (c i) (r (c i))
  let E : Fin n → Set X := disjointed B
  have hcover : K ⊆ ⋃ i, B i := by
    intro x hx
    rcases mem_iUnion.mp (hF hx) with ⟨a, ha⟩
    rcases mem_iUnion.mp ha with ⟨haF, hxa⟩
    exact mem_iUnion.mpr ⟨e ⟨a, haF⟩, by simpa only [B, c, Equiv.symm_apply_apply] using hxa⟩
  refine ⟨n, E, disjoint_disjointed B, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [E, iUnion_disjointed] using hcover
  · intro i
    change MeasurableSet (disjointed B i)
    rw [disjointed_eq_inter_compl]
    exact isOpen_ball.measurableSet.inter (MeasurableSet.iInter fun j ↦
      MeasurableSet.iInter fun hji ↦ (show MeasurableSet (B j) from isOpen_ball.measurableSet).compl)
  · intro i
    exact isBounded_ball.subset (disjointed_subset B i)
  · intro i
    change γ (frontier (disjointed B i)) = 0
    rw [disjointed_apply]
    exact null_frontier_diff γ (hr (c i)).2.2
      (null_frontier_finset_sup γ B (fun j ↦ (hr (c j)).2.2) _)
  · intro i x hx y hy
    have hx' : dist x (c i) < r (c i) := disjointed_subset B i hx
    have hy' : dist (c i) y < r (c i) := by
      simpa only [dist_comm] using (show dist y (c i) < r (c i) from disjointed_subset B i hy)
    exact (dist_triangle x (c i) y).trans_lt
      ((add_lt_add hx' hy').trans ((add_lt_add (hr (c i)).2.1 (hr (c i)).2.1).trans_eq
        (add_halves ε)))

end BouRabeeGwynne
