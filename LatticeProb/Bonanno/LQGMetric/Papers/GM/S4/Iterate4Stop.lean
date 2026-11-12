/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate4Stop at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.Defs
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UnitInterval

/-!
# The stopped geodesic of Thm 4.2 (2): basic facts (D89a), without the §5 imports

Copies (renamed `gm_*`, to keep the §4 chain independent of `Papers/GM/S5`) of
`lastExitTime_nonneg`, `lastExitTime_le_one`, `le_lastExitTime_of_mem`
(`Papers/GM/S5/Prop43bL53b.lean`, DEC-89 §Q1) and `lastExitTime_eq_iSup`,
`measurable_lastExitTime`, `measurable_stopLastExit_apply`, `continuous_stopLastExit`
(`Papers/GM/S5/Prop43cL53.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace LQGMetric.GM

theorem gm_lastExit_bdd (η : C(unitInterval, ℂ)) (K : Set ℂ) :
    BddAbove {s : ℝ | ∃ u : unitInterval, (u : ℝ) = s ∧ η u ∈ K} :=
  ⟨1, fun _ ⟨u, hu, _⟩ => hu ▸ u.2.2⟩

theorem gm_lastExitTime_nonneg (η : C(unitInterval, ℂ)) (K : Set ℂ) : 0 ≤ lastExitTime η K :=
  Real.sSup_nonneg (fun _ ⟨u, hu, _⟩ => hu ▸ u.2.1)

theorem gm_lastExitTime_le_one (η : C(unitInterval, ℂ)) (K : Set ℂ) : lastExitTime η K ≤ 1 :=
  Real.sSup_le (fun _ ⟨u, hu, _⟩ => hu ▸ u.2.2) zero_le_one

theorem gm_le_lastExitTime_of_mem {η : C(unitInterval, ℂ)} {K : Set ℂ} {s : unitInterval}
    (hs : η s ∈ K) : (s : ℝ) ≤ lastExitTime η K :=
  le_csSup (gm_lastExit_bdd η K) ⟨s, rfl, hs⟩

theorem gm_stopLastExit_apply (η : C(unitInterval, ℂ)) (K : Set ℂ) (u : unitInterval) :
    stopLastExit η K u = η (projIcc 0 1 zero_le_one ((u : ℝ) * lastExitTime η K)) := rfl

theorem gm_continuous_stopLastExit (η : C(unitInterval, ℂ)) (K : Set ℂ) :
    Continuous (stopLastExit η K) :=
  η.continuous.comp (continuous_projIcc.comp (continuous_subtype_val.mul continuous_const))

open Classical in
/-- for `K` open, the last time in `K` is the supremum over a dense sequence of times -/
theorem gm_lastExitTime_eq_iSup (η : C(unitInterval, ℂ)) {K : Set ℂ} (hK : IsOpen K) :
    lastExitTime η K = ⨆ k : ℕ, (if η (denseSeq unitInterval k) ∈ K then
      ((denseSeq unitInterval k : unitInterval) : ℝ) else 0) := by
  set A := {s : ℝ | ∃ u : unitInterval, (u : ℝ) = s ∧ η u ∈ K} with hA
  set f : ℕ → ℝ := fun k => if η (denseSeq unitInterval k) ∈ K then
    ((denseSeq unitInterval k : unitInterval) : ℝ) else 0 with hf
  have hf1 : ∀ k, f k ≤ 1 := fun k => by
    simp only [hf]; split_ifs
    · exact (denseSeq unitInterval k).2.2
    · exact zero_le_one
  have hbdd : BddAbove (range f) := ⟨1, by rintro _ ⟨k, rfl⟩; exact hf1 k⟩
  have hAbdd : BddAbove A := ⟨1, by rintro _ ⟨u, rfl, -⟩; exact u.2.2⟩
  show sSup A = iSup f
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · have hf0 : ∀ k, f k = 0 := fun k => by
      simp only [hf]; split_ifs with hk
      · exact absurd (show ((denseSeq unitInterval k : unitInterval) : ℝ) ∈ A from ⟨_, rfl, hk⟩)
          (hAe ▸ notMem_empty _)
      · rfl
    have hf0' : f = fun _ => 0 := funext hf0
    rw [hAe, Real.sSup_empty, hf0', ciSup_const]
  refine le_antisymm ?_ ?_
  · refine le_of_forall_lt fun c hc => ?_
    obtain ⟨s, ⟨u, rfl, hu⟩, hcs⟩ := exists_lt_of_lt_csSup hAne hc
    have hO : IsOpen {v : unitInterval | η v ∈ K ∧ c < (v : ℝ)} :=
      (hK.preimage η.continuous).inter (isOpen_lt continuous_const continuous_subtype_val)
    obtain ⟨k, hk1, hk2⟩ :=
      (denseRange_denseSeq unitInterval).exists_mem_open hO ⟨u, hu, hcs⟩
    refine lt_of_lt_of_le ?_ (le_ciSup hbdd k)
    simp only [hf, if_pos hk1]; exact hk2
  · refine ciSup_le fun k => ?_
    simp only [hf]; split_ifs with hk
    · exact le_csSup hAbdd ⟨_, rfl, hk⟩
    · obtain ⟨_, u, rfl, hu⟩ := hAne
      exact (u.2.1).trans (le_csSup hAbdd ⟨u, rfl, hu⟩)

theorem gm_measurable_lastExitTime {K : Set ℂ} (hK : IsOpen K) :
    Measurable fun η : C(unitInterval, ℂ) => lastExitTime η K := by
  classical
  simp_rw [gm_lastExitTime_eq_iSup _ hK]
  refine Measurable.iSup fun k => Measurable.ite ?_ measurable_const measurable_const
  exact (continuous_eval_const _).measurable hK.measurableSet

theorem gm_measurable_stopLastExit_apply {K : Set ℂ} (hK : IsOpen K) (t : unitInterval) :
    Measurable fun η : C(unitInterval, ℂ) => stopLastExit η K t := by
  simp_rw [gm_stopLastExit_apply]
  have hev : Measurable fun p : C(unitInterval, ℂ) × unitInterval => p.1 p.2 :=
    continuous_eval.measurable
  exact hev.comp (measurable_id.prodMk ((continuous_projIcc (a := (0 : ℝ)) (b := 1)
    (h := zero_le_one)).measurable.comp
    (measurable_const.mul (gm_measurable_lastExitTime hK))))

end LQGMetric.GM
