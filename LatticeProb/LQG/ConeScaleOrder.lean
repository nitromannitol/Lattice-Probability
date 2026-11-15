import LatticeProb.LQG.ConeAllLevelAttainment
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OConeScale

/-! # Ordering of cone scale radii -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

namespace MatedCRTHarmonic.ConeScaling

/-- For a continuous function tending to infinity, greatest level times
are strictly increasing in the level. -/
theorem lastLevel_lt_of_tendsto {Q a b : ℝ} {w : C(ℝ, ℝ)}
    (htop : Tendsto (fun s : ℝ => w (-s) + Q * s) atTop atTop)
    (ha : IsGreatest {s : ℝ | w (-s) + Q * s = a} (lastLevel Q a w))
    (hb : IsGreatest {s : ℝ | w (-s) + Q * s = b} (lastLevel Q b w))
    (hab : a < b) : lastLevel Q a w < lastLevel Q b w := by
  let X : ℝ → ℝ := fun s => w (-s) + Q * s
  have hc : Continuous X := by dsimp [X]; fun_prop
  obtain ⟨T, hT⟩ := (tendsto_atTop_atTop.1 htop) b
  let t := max T (lastLevel Q a w + 1)
  have ht : lastLevel Q a w ≤ t := by dsimp [t]; linarith [le_max_right T (lastLevel Q a w + 1)]
  have hXt : b ≤ X t := hT t (le_max_left _ _)
  have hXa : X (lastLevel Q a w) = a := ha.1
  obtain ⟨s, hs, hXs⟩ := intermediate_value_Icc ht hc.continuousOn
    (show b ∈ Set.Icc (X (lastLevel Q a w)) (X t) from ⟨by linarith, hXt⟩)
  have hle : lastLevel Q a w ≤ lastLevel Q b w := hs.1.trans (hb.2 hXs)
  have hne : lastLevel Q a w ≠ lastLevel Q b w := by
    intro heq
    have hXb : X (lastLevel Q b w) = b := hb.1
    rw [heq] at hXa
    linarith
  exact lt_of_le_of_ne hle hne

/-- Almost surely the cone radial path has strictly ordered last-level times. -/
theorem ae_strictMono_cone_lastLevel {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α : ℝ} (hαQ : α < CellScaling.lqgQ γ)
    {B B' : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    {W : Ω → C(ℝ, ℝ)}
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α
      (fun s => B s ω) (fun s => B' s ω) t) :
    ∀ᵐ ω ∂P, StrictMono (fun a => lastLevel (CellScaling.lqgQ γ) a (W ω)) := by
  have hd : 0 < CellScaling.lqgQ γ - α := sub_pos.mpr hαQ
  filter_upwards [hW, CellScaling.ae_goodDrift (γ := γ) (α := α) hB' hd,
    ae_isGreatest_lastLevel hαQ hB hB' hW] with ω hWω hgood hgreat
  have htop : Tendsto (fun s : ℝ => W ω (-s) + CellScaling.lqgQ γ * s) atTop atTop := by
    apply tendsto_atTop_atTop.2
    intro y
    obtain ⟨T, hT⟩ := (tendsto_atTop_atTop.1 hgood.tendsto_atTop) y
    refine ⟨max 1 (T - CellScaling.lastZeroR (CellScaling.coneDrift γ α (fun t => B' t ω))), ?_⟩
    intro s hs
    have hspos : 0 < s := by linarith [le_max_left 1 (T - CellScaling.lastZeroR (CellScaling.coneDrift γ α (fun t => B' t ω)))]
    have hX : W ω (-s) + CellScaling.lqgQ γ * s =
        CellScaling.coneDrift γ α (fun t => B' t ω)
          (CellScaling.lastZeroR (CellScaling.coneDrift γ α (fun t => B' t ω)) + s) := by
      rw [hWω]
      exact CellScaling.coneLogRadial_of_pos γ α _ _ hspos
    rw [hX]
    apply hT
    linarith [le_max_right 1 (T - CellScaling.lastZeroR (CellScaling.coneDrift γ α (fun t => B' t ω)))]
  intro a b hab
  exact lastLevel_lt_of_tendsto htop (hgreat a) (hgreat b) hab

/-- Almost surely positive ordered parameters give strictly ordered cone scales. -/
theorem ae_coneScale_strictMono {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α : ℝ} (hγ : 0 < γ) (hαQ : α < CellScaling.lqgQ γ)
    {B B' : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    {W : Ω → C(ℝ, ℝ)}
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α
      (fun s => B s ω) (fun s => B' s ω) t) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ, 0 < a → a < b →
      CellScaling.coneScale γ α (fun s => B s ω) (fun s => B' s ω) a <
      CellScaling.coneScale γ α (fun s => B s ω) (fun s => B' s ω) b := by
  filter_upwards [hW, ae_strictMono_cone_lastLevel hαQ hB hB' hW] with ω hWω hmono
  intro a b ha hab
  rw [IGLaw.coneScale_eq_exp_lastLevel_alpha γ α a hWω,
    IGLaw.coneScale_eq_exp_lastLevel_alpha γ α b hWω]
  exact Real.exp_lt_exp.mpr (hmono (mul_lt_mul_of_pos_left
    (Real.log_lt_log ha hab) (inv_pos.mpr hγ)))

end MatedCRTHarmonic.ConeScaling
