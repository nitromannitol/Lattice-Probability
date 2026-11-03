/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSLemma27.CellModel at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.LQGMetric.Statement.Field

/-!
# The SLE/LQG cell model of [18] §1.4 and the deterministic core of [18] Lemma 2.7

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18], §§1.4 and 2.3, Lemmas 2.7 and 2.8, using the strict mass comparison.

* `CellModel γ` is the abstract SLE/LQG cell model: a probability space carrying the field `h`, its `γ`-LQG area measure
  `μ_h`, and the space-filling curve `η` parametrized by `μ_h`-mass with `η(0) = 0`; the cells of mesh `ε` are
  `H^ε_x = η([ε(x − 1), εx])` (`CellModel.cell`; [18]:§1.4, the vertex `x ∈ ℤ` stands for `εx ∈ εℤ`). The structure
  records only what the definitions of [18] §1.4 fix; every probabilistic property of the model used by Lemmas 2.7 and
  2.8 is a named interface (`SLEInterfaces.lean`: bundle inputs; `GMCInterfaces.lean`: SLE-free inputs, to prove).
  The bundle `MatingOfTreesInput`  instantiates it.
* `diam_segment_le_of_balls` is the deterministic core of the proof of Lemma 2.7 (the deterministic cell argument, using a strict mass comparison): if every segment of `η` inside `𝔻` of diameter `≥ D` contains a ball of radius
  `≥ δ`, and every ball of radius `δ` centred in `B_{ρ'}(0)` has mass `> ε`, then every segment of time length `≤ ε`
  meeting `B_ρ(0)` has diameter `≤ 2D` (for `ρ + D ≤ ρ' ≤ 1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMSLemma27

/-- **The SLE/LQG cell model of [18] §1.4** (`[18]`; [18] §1.4). On a probability space
`(Ω, P)`:
* `field ω` is the field `h` (a random distribution, LQGMetric's `𝒟'(ℂ)`); in the quantum-cone case it is the circle
  average embedding of a `γ`-quantum cone (DMS Definition 4.10, `[14]`), as in [18] Lemma 2.7's third case;
* `area ω` is its `γ`-LQG area measure `μ_h`;
* `curve ω` is the whole-plane space-filling SLE_{κ'} from `∞` to `∞` (`κ' = 16/γ²`), independent of `h`,
  parametrized by `μ_h`-mass with `η(0) = 0` (`[18]:§1.4`): almost surely `η` is continuous, `η(0) = 0`, and
  `μ_h(η([a, b])) = b − a` for `a ≤ b`.

The data are abstract so that the bundle (`MatingOfTreesInput`) can instantiate them; the laws of
`h, μ_h, η` (quantum cone, LQG measure, space-filling SLE, independence) enter Lemmas 2.7 and 2.8 only through the named
interfaces of `SLEInterfaces.lean` and `GMCInterfaces.lean`. The parameter `γ` records the LQG parameter of `area`. -/
structure CellModel (γ : ℝ) where
  /-- The sample space. -/
  Ω : Type
  /-- Its σ-algebra. -/
  [measurableSpace : MeasurableSpace Ω]
  /-- The probability measure. -/
  P : Measure Ω
  [isProbabilityMeasure : IsProbabilityMeasure P]
  /-- The field `h`. -/
  field : Ω → LQGMetric.DistC
  /-- The `γ`-LQG area measure `μ_h`. -/
  area : Ω → Measure ℂ
  /-- The space-filling curve `η`, parametrized by `μ_h`-mass. -/
  curve : Ω → ℝ → ℂ
  ae_continuous_curve : ∀ᵐ ω ∂P, Continuous (curve ω)
  ae_curve_zero : ∀ᵐ ω ∂P, curve ω 0 = 0
  ae_area_curve : ∀ᵐ ω ∂P, ∀ a b : ℝ, a ≤ b → area ω (curve ω '' Icc a b) = ENNReal.ofReal (b - a)

variable {γ : ℝ}

instance cellModelMeasurableSpace (M : CellModel γ) : MeasurableSpace M.Ω := M.measurableSpace

instance cellModelIsProbabilityMeasure (M : CellModel γ) : IsProbabilityMeasure M.P :=
  M.isProbabilityMeasure

/-- The cell `H^ε_x = η([ε(x − 1), εx])` of mesh `ε` indexed by `x ∈ ℤ` ([18] §1.4; the same convention as the cell-family estimate's
`PeanosphereG0`). -/
def CellModel.cell (M : CellModel γ) (ε : ℝ) (ω : M.Ω) (x : ℤ) : Set ℂ :=
  M.curve ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)

/-! ### The deterministic core of Lemma 2.7 -/

/-- First exit of a continuous path from the open ball `B_D(η(s))` after time `s`: if `η(u)` is at distance `≥ D`
from `η(s)` for some `u ≥ s`, there is `t ∈ (s, u]` with `η([s, t]) ⊆ B̄_D(η(s))` and `diam η([s, t]) ≥ D`. -/
theorem exists_subsegment_exit_right {η : ℝ → ℂ} (hη : Continuous η) {s u D : ℝ} (hD : 0 < D)
    (hsu : s ≤ u) (hu : D ≤ dist (η u) (η s)) :
    ∃ t, s < t ∧ t ≤ u ∧ η '' Icc s t ⊆ closedBall (η s) D ∧ D ≤ diam (η '' Icc s t) := by
  set T : Set ℝ := Icc s u ∩ {t | D ≤ dist (η t) (η s)} with hT
  have hTc : IsClosed T :=
    isClosed_Icc.inter (isClosed_le continuous_const (hη.dist continuous_const))
  have hTn : T.Nonempty := ⟨u, ⟨hsu, le_rfl⟩, hu⟩
  have hTb : BddBelow T := ⟨s, fun t ht => ht.1.1⟩
  set t := sInf T with ht
  have htT : t ∈ T := hTc.csInf_mem hTn hTb
  have hst : s < t := by
    rcases htT.1.1.eq_or_lt with h | h
    · have h2 : D ≤ dist (η t) (η s) := htT.2
      rw [← h, dist_self] at h2
      linarith
    · exact h
  refine ⟨t, hst, htT.1.2, ?_, ?_⟩
  · -- every time in `[s, t)` is before the first exit, then pass to the closure
    have hIco : Ico s t ⊆ {v | dist (η v) (η s) ≤ D} := by
      intro v hv
      by_contra hcon
      have hcon' : ¬ dist (η v) (η s) ≤ D := hcon
      have hvT : v ∈ T := ⟨⟨hv.1, hv.2.le.trans htT.1.2⟩, (not_le.mp hcon').le⟩
      exact absurd (csInf_le hTb hvT) (not_le.mpr hv.2)
    have hcl : Icc s t ⊆ {v | dist (η v) (η s) ≤ D} := by
      rw [← closure_Ico hst.ne]
      exact (isClosed_le (hη.dist continuous_const) continuous_const).closure_subset_iff.mpr hIco
    rintro _ ⟨v, hv, rfl⟩
    exact mem_closedBall.mpr (hcl hv)
  · have hb : Bornology.IsBounded (η '' Icc s t) := (isCompact_Icc.image hη).isBounded
    exact htT.2.trans (dist_le_diam_of_mem hb (mem_image_of_mem η ⟨hst.le, le_rfl⟩)
      (mem_image_of_mem η ⟨le_rfl, hst.le⟩))

/-- The time reversal of `η` maps `Icc a b` onto the image of `Icc (−b) (−a)`. -/
theorem image_neg_Icc_comp (η : ℝ → ℂ) (a b : ℝ) :
    (fun t => η (-t)) '' Icc a b = η '' Icc (-b) (-a) := by
  rw [show (fun t => η (-t)) = η ∘ Neg.neg from rfl, image_comp, image_neg_Icc]

/-- First exit before time `s` (time reversal of `exists_subsegment_exit_right`). -/
theorem exists_subsegment_exit_left {η : ℝ → ℂ} (hη : Continuous η) {s u D : ℝ} (hD : 0 < D)
    (hus : u ≤ s) (hu : D ≤ dist (η u) (η s)) :
    ∃ t, u ≤ t ∧ t < s ∧ η '' Icc t s ⊆ closedBall (η s) D ∧ D ≤ diam (η '' Icc t s) := by
  have hη' : Continuous fun t => η (-t) := hη.comp continuous_neg
  obtain ⟨t, hst, htu, hsub, hdiam⟩ := exists_subsegment_exit_right hη' (s := -s) (u := -u) hD
    (neg_le_neg hus) (by simpa only [neg_neg] using hu)
  refine ⟨-t, by linarith, by linarith, ?_, ?_⟩
  · rw [image_neg_Icc_comp, neg_neg] at hsub
    simpa only [neg_neg] using hsub
  · rw [image_neg_Icc_comp, neg_neg] at hdiam
    exact hdiam

/-- **Deterministic core of [18] Lemma 2.7** (using the strict mass comparison). Let `η` be a
continuous curve and `μ` a measure with `μ(η([a, b])) = b − a`. Suppose that every segment `η([a, b])`, `a < b`,
contained in `𝔻` with diameter `≥ D` contains a ball of radius `≥ δ` ([GHM15, Prop. 3.4]), and that every ball of radius
`δ` centred in `B_{ρ'}(0)` has `μ`-mass `> ε` ([18] Lemma 2.8). If `ρ + D ≤ ρ' ≤ 1`, then every segment of time length
`≤ ε` that meets `B_ρ(0)` has diameter `≤ 2D`. -/
theorem diam_segment_le_of_balls {η : ℝ → ℂ} (hη : Continuous η) {μ : Measure ℂ}
    (harea : ∀ a b : ℝ, a ≤ b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {ε D δ ρ ρ' : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hρρ' : ρ + D ≤ ρ') (hρ'1 : ρ' ≤ 1)
    (hball : ∀ a b : ℝ, a < b → η '' Icc a b ⊆ ball (0 : ℂ) 1 → D ≤ diam (η '' Icc a b) →
      ∃ c : ℂ, ∃ t : ℝ, δ ≤ t ∧ ball c t ⊆ η '' Icc a b)
    (hmass : ∀ z ∈ ball (0 : ℂ) ρ', ENNReal.ofReal ε < μ (ball z δ))
    {a b : ℝ} (hbaε : b - a ≤ ε)
    (hmeet : (η '' Icc a b ∩ ball (0 : ℂ) ρ).Nonempty) :
    diam (η '' Icc a b) ≤ 2 * D := by
  obtain ⟨_, ⟨s, hs, rfl⟩, hsρ⟩ := hmeet
  rw [mem_ball_zero_iff] at hsρ
  -- a sub-segment `η([a', b'])` with `[a', b'] ⊆ [a, b]`, inside `B̄_D(η(s))`, of diameter `≥ D` is impossible
  have key : ∀ a' b' : ℝ, a ≤ a' → a' < b' → b' ≤ b → η '' Icc a' b' ⊆ closedBall (η s) D →
      D ≤ diam (η '' Icc a' b') → False := by
    intro a' b' ha' hab' hb' hsub hdiam
    have hsub1 : η '' Icc a' b' ⊆ ball (0 : ℂ) ρ' := by
      intro w hw
      have h1 := mem_closedBall.mp (hsub hw)
      rw [mem_ball_zero_iff]
      calc ‖w‖ ≤ ‖w - η s‖ + ‖η s‖ := by
            calc ‖w‖ = ‖(w - η s) + η s‖ := by rw [sub_add_cancel]
              _ ≤ ‖w - η s‖ + ‖η s‖ := norm_add_le _ _
        _ < D + ρ := by rw [← dist_eq_norm]; linarith
        _ ≤ ρ' := by linarith
    obtain ⟨c, t, hδt, hct⟩ := hball a' b' hab'
      (hsub1.trans (ball_subset_ball hρ'1)) hdiam
    have hc : c ∈ ball (0 : ℂ) ρ' := hsub1 (hct (mem_ball_self (hδ.trans_le hδt)))
    have h1 := hmass c hc
    have h2 : μ (ball c δ) ≤ ENNReal.ofReal ε :=
      calc μ (ball c δ) ≤ μ (η '' Icc a' b') := measure_mono ((ball_subset_ball hδt).trans hct)
        _ = ENNReal.ofReal (b' - a') := harea a' b' hab'.le
        _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)
    exact absurd h1 (not_lt.mpr h2)
  -- hence every point of the segment is within `D` of `η(s)`
  have hclose : ∀ u ∈ Icc a b, dist (η u) (η s) < D := by
    intro u hu
    by_contra hcon
    have hDu : D ≤ dist (η u) (η s) := not_lt.mp hcon
    rcases le_total s u with hsu | hus
    · obtain ⟨t, hst, htu, hsub, hdiam⟩ := exists_subsegment_exit_right hη hD hsu hDu
      exact key s t hs.1 hst (htu.trans hu.2) hsub hdiam
    · obtain ⟨t, hut, hts, hsub, hdiam⟩ := exists_subsegment_exit_left hη hD hus hDu
      exact key t s (hu.1.trans hut) hts hs.2 hsub hdiam
  refine diam_le_of_forall_dist_le (by linarith) ?_
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  have h1 := hclose u hu
  have h2 := hclose v hv
  calc dist (η u) (η v) ≤ dist (η u) (η s) + dist (η s) (η v) := dist_triangle _ _ _
    _ ≤ 2 * D := by rw [dist_comm (η s)]; linarith

end MatedCRTHarmonic.GMSLemma27
