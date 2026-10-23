import LatticeProb.Prob.Cadlag.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The Borel measurable space of càdlàg paths

This file equips the J1 metric space with its Borel sigma algebra. Endpoint evaluations
are Lipschitz. All evaluations are Borel measurable, using right continuity and closed
conditions on the values throughout half-open time intervals.
-/

namespace LatticeProb.Cadlag

open Set Filter
open scoped Topology

noncomputable section

variable {T : ℝ} {E : Type*} [NormedAddCommGroup E]

/-- The measurable structure on càdlàg paths is the Borel structure of the J1 metric. -/
instance instMeasurableSpace : MeasurableSpace (D T E) := borel (D T E)

/-- The chosen measurable structure is the Borel structure. -/
instance instBorelSpace : BorelSpace (D T E) := ⟨rfl⟩

/-- Terminal evaluation is 1-Lipschitz for the J1 metric. -/
theorem lipschitzWith_eval_terminal (t : Icc (0 : ℝ) T) (ht : (t : ℝ) = T) :
    LipschitzWith 1 (fun x : D T E => x.1 t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_skorokhodDist]
  apply le_csInf (admissibleBounds_nonempty x y)
  rintro r ⟨_, l, _, hxy⟩
  rw [dist_eq_norm]
  simpa only [timeChange_apply_terminal l t ht] using hxy t

/-- Terminal evaluation is continuous for the J1 metric. -/
theorem continuous_eval_terminal (t : Icc (0 : ℝ) T) (ht : (t : ℝ) = T) :
    Continuous (fun x : D T E => x.1 t) :=
  (lipschitzWith_eval_terminal t ht).continuous

/-- Terminal evaluation is Borel measurable. -/
theorem measurable_eval_terminal [MeasurableSpace E] [BorelSpace E]
    (t : Icc (0 : ℝ) T) (ht : (t : ℝ) = T) :
    Measurable (fun x : D T E => x.1 t) :=
  (continuous_eval_terminal t ht).measurable

/-- Initial evaluation is 1-Lipschitz for the J1 metric. -/
theorem lipschitzWith_eval_initial (t : Icc (0 : ℝ) T) (ht : (t : ℝ) = 0) :
    LipschitzWith 1 (fun x : D T E => x.1 t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul, dist_eq_skorokhodDist, dist_eq_norm] using
    norm_eval_initial_sub_le x y t ht

/-- Initial evaluation is continuous for the J1 metric. -/
theorem continuous_eval_initial (t : Icc (0 : ℝ) T) (ht : (t : ℝ) = 0) :
    Continuous (fun x : D T E => x.1 t) :=
  (lipschitzWith_eval_initial t ht).continuous

/-- Initial evaluation is Borel measurable. -/
theorem measurable_eval_initial [MeasurableSpace E] [BorelSpace E]
    (t : Icc (0 : ℝ) T) (ht : (t : ℝ) = 0) :
    Measurable (fun x : D T E => x.1 t) :=
  (continuous_eval_initial t ht).measurable

/-- Staying in a closed spatial set on a half-open time interval is J1-closed.
The terminal time is excluded; its evaluation is separately continuous. -/
theorem isClosed_forall_eval_mem (a b : ℝ) {F : Set E} (hF : IsClosed F) :
    IsClosed {x : D T E | ∀ t : Icc (0 : ℝ) T, a ≤ (t : ℝ) → (t : ℝ) < b →
      (t : ℝ) < T → x.1 t ∈ F} := by
  rw [← closure_subset_iff_isClosed]
  intro x hx t hat htb htT
  apply (Metric.mem_of_closed' hF).mpr
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := (Metric.continuousWithinAt_iff.mp (x.2.1 t htT))
    (ε / 2) (half_pos hε)
  have hgapb : 0 < b - (t : ℝ) := sub_pos.mpr htb
  have hgapT : 0 < T - (t : ℝ) := sub_pos.mpr htT
  let η := min δ (min (b - t) (min (T - t) ε)) / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hηδ : η < δ := by
    have := min_le_left δ (min (b - t) (min (T - t) ε))
    dsimp [η] at *
    linarith
  have hηb : η < b - t := by
    have := (min_le_right δ (min (b - t) (min (T - t) ε))).trans
      (min_le_left _ _)
    dsimp [η] at *
    linarith
  have hηT : η < T - t := by
    have := (min_le_right δ (min (b - t) (min (T - t) ε))).trans
      ((min_le_right (b - t) (min (T - t) ε)).trans (min_le_left _ _))
    dsimp [η] at *
    linarith
  have hηε : η < ε := by
    have := (min_le_right δ (min (b - t) (min (T - t) ε))).trans
      ((min_le_right (b - t) (min (T - t) ε)).trans (min_le_right _ _))
    dsimp [η] at *
    linarith
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (η / 2) (half_pos hη)
  obtain ⟨r, ⟨_, l, hl, hspace⟩, hr⟩ := exists_admissibleBounds_lt hxy
  let s : Icc (0 : ℝ) T := ⟨t + η / 2, by constructor <;> linarith [t.property.1]⟩
  have hs : a ≤ (s : ℝ) ∧ (s : ℝ) < b ∧ (s : ℝ) < T := by
    dsimp [s]
    constructor
    · linarith
    constructor <;> linarith
  have hls := abs_le.mp (hl s)
  have htl : t ≤ l s := by change (t : ℝ) ≤ l s; dsimp [s] at hls; linarith
  have hld : dist (l s) t < δ := by
    rw [Subtype.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr (show (t : ℝ) ≤ (l s : ℝ) from htl))]
    dsimp [s] at hls
    linarith
  have hnear := hcont htl hld
  have hsp : dist (x.1 (l s)) (y.1 s) ≤ r := by
    rw [dist_eq_norm]
    exact hspace s
  refine ⟨y.1 s, hy s hs.1 hs.2.1 hs.2.2, ?_⟩
  have htriangle := dist_triangle (x.1 t) (x.1 (l s)) (y.1 s)
  rw [dist_comm (x.1 (l s)) (x.1 t)] at hnear
  linarith

/-- Every evaluation on the genuine J1 Borel space is measurable.
Right continuity supplies countable closed inner approximations to open preimages. -/
theorem measurable_eval [MeasurableSpace E] [BorelSpace E]
    (t : Icc (0 : ℝ) T) : Measurable (fun x : D T E => x.1 t) := by
  by_cases ht : (t : ℝ) < T
  · apply measurable_of_isOpen
    intro U hU
    by_cases hUc : Uᶜ = ∅
    · have hUall : U = univ := compl_empty_iff.mp hUc
      rw [hUall, preimage_univ]
      exact MeasurableSet.univ
    have hne : Uᶜ.Nonempty := nonempty_iff_ne_empty.mpr hUc
    let F : ℕ → Set E := fun m =>
      {z | 1 / (m + 1 : ℝ) ≤ Metric.infDist z Uᶜ}
    have hF : ∀ m, IsClosed (F m) := fun m =>
      isClosed_le continuous_const (Metric.continuous_infDist_pt Uᶜ)
    let A : ℕ → ℕ → Set (D T E) := fun m n =>
      {x | ∀ s : Icc (0 : ℝ) T, (t : ℝ) ≤ (s : ℝ) →
        (s : ℝ) < t + 1 / (n + 1 : ℝ) →
        (s : ℝ) < T → x.1 s ∈ F m}
    have hA : ∀ m n, IsClosed (A m n) := fun m n =>
      isClosed_forall_eval_mem _ _ (hF m)
    have heq : (fun x : D T E => x.1 t) ⁻¹' U = ⋃ m, ⋃ n, A m n := by
      ext x
      constructor
      · intro hx
        have hpos : 0 < Metric.infDist (x.1 t) Uᶜ :=
          (hU.isClosed_compl.notMem_iff_infDist_pos hne).mp (notMem_compl_iff.mpr hx)
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
        have hright : ContinuousWithinAt (fun s => Metric.infDist (x.1 s) Uᶜ)
            {s | t ≤ s} t :=
          (Metric.continuous_infDist_pt Uᶜ).continuousAt.comp_continuousWithinAt (x.2.1 t ht)
        obtain ⟨δ, hδ, hbound⟩ := (Metric.continuousWithinAt_iff.mp hright)
          ((Metric.infDist (x.1 t) Uᶜ - 1 / (m + 1 : ℝ)) / 2) (by linarith)
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
        refine mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨n, ?_⟩⟩
        intro s hts hsn _
        have hd : dist s t < δ := by
          rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)]
          linarith
        have hb := hbound hts hd
        rw [Real.dist_eq, abs_lt] at hb
        change 1 / (m + 1 : ℝ) ≤ Metric.infDist (x.1 s) Uᶜ
        linarith [hb.1]
      · intro hx
        obtain ⟨m, hm⟩ := mem_iUnion.mp hx
        obtain ⟨n, hn⟩ := mem_iUnion.mp hm
        have hstep : 0 < 1 / (n + 1 : ℝ) := by positivity
        have hb := hn t le_rfl (by linarith) ht
        have hp : 0 < Metric.infDist (x.1 t) Uᶜ :=
          lt_of_lt_of_le (by positivity : 0 < 1 / (m + 1 : ℝ)) hb
        exact notMem_compl_iff.mp
          ((hU.isClosed_compl.notMem_iff_infDist_pos hne).mpr hp)
    rw [heq]
    exact MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun n => (hA m n).measurableSet
  · exact measurable_eval_terminal t (le_antisymm t.property.2 (le_of_not_gt ht))

/-- Any family of evaluations is measurable into the product measurable space. -/
theorem measurable_eval_family {ι : Type*} [MeasurableSpace E] [BorelSpace E]
    (times : ι → Icc (0 : ℝ) T) :
    Measurable (fun x : D T E => fun i => x.1 (times i)) :=
  measurable_pi_lambda _ (fun i => measurable_eval (times i))

/-- The sigma algebra generated by any family of evaluations is contained in J1 Borel. -/
theorem iSup_comap_eval_le_borel [MeasurableSpace E] [BorelSpace E]
    (S : Set (Icc (0 : ℝ) T)) :
    (⨆ t : S, (inferInstance : MeasurableSpace E).comap
      (fun x : D T E => x.1 t.1)) ≤ borel (D T E) := by
  exact iSup_le fun t => (measurable_eval t.1).comap_le

end

end LatticeProb.Cadlag
