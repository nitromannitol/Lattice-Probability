/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SquareCompensatorLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Function.Holder
import LatticeProb.Bonanno.ReflectedGMS.Forms.MartingaleL2Limit

/-!
# Square-compensator martingale limits

Fixed-time L2 convergence implies fixed-time L1 convergence of squares.  Thus,
after an additional fixed-time L1 limit of compensators, the existing L1
martingale closure transfers martingality of compensated squares to the limit.
-/

set_option autoImplicit false

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace ReflectedGMS

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Squaring is continuous from `L2` to `L1` for real-valued functions. -/
theorem tendsto_eLpNorm_sq_sub_sq_one_of_tendsto_eLpNorm_two
    {P : Measure Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, MemLp (f n) 2 P) (hg : MemLp g 2 P)
    (hfg : Tendsto (fun n => eLpNorm (f n - g) 2 P) atTop (𝓝 0)) :
    Tendsto
      (fun n => eLpNorm (fun ω => (f n ω) ^ 2 - (g ω) ^ 2) 1 P)
      atTop (𝓝 0) := by
  have hsum : Tendsto
      (fun n => eLpNorm (f n - g) 2 P + 2 * eLpNorm g 2 P)
      atTop (𝓝 (2 * eLpNorm g 2 P)) := by
    simpa using hfg.add_const (2 * eLpNorm g 2 P)
  have hg_top : 2 * eLpNorm g 2 P ≠ ∞ := by
    exact ENNReal.mul_ne_top (by norm_num) hg.eLpNorm_ne_top
  have hprod : Tendsto
      (fun n => eLpNorm (f n - g) 2 P *
        (eLpNorm (f n - g) 2 P + 2 * eLpNorm g 2 P))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul hfg (Or.inr hg_top) hsum
      (Or.inr ENNReal.zero_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hprod
    (fun _ => zero_le) fun n => ?_
  have hplus : eLpNorm (f n + g) 2 P ≤
      eLpNorm (f n - g) 2 P + 2 * eLpNorm g 2 P := by
    have htri := eLpNorm_add_le (f := f n - g) (g := g + g) (μ := P)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hgg := eLpNorm_add_le (f := g) (g := g) (μ := P) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    calc
      eLpNorm (f n + g) 2 P = eLpNorm ((f n - g) + (g + g)) 2 P := by
        congr 1
        funext ω
        dsimp only [Pi.sub_apply, Pi.add_apply]
        ring
      _ ≤ eLpNorm (f n - g) 2 P + eLpNorm (g + g) 2 P := htri
      _ ≤ eLpNorm (f n - g) 2 P +
          (eLpNorm g 2 P + eLpNorm g 2 P) := add_le_add_right hgg _
      _ = eLpNorm (f n - g) 2 P + 2 * eLpNorm g 2 P := by ring
  have hholder : eLpNorm
      (fun ω => (f n ω - g ω) * (f n ω + g ω)) 1 P ≤
      eLpNorm (f n - g) 2 P * eLpNorm (f n + g) 2 P := by
    have hraw := eLpNorm_le_enorm_mul_eLpNorm_mul_eLpNorm
      (p := 2) (q := 2) (r := 1) (ContinuousLinearMap.mul ℝ ℝ)
      ((hf n).sub hg).aestronglyMeasurable ((hf n).add hg).aestronglyMeasurable
    have hB : ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ ≤ 1 := by
      rw [enorm_eq_nnnorm, ← ENNReal.coe_one, ENNReal.coe_le_coe]
      exact_mod_cast ContinuousLinearMap.opNorm_mul_le (𝕜 := ℝ) (R := ℝ)
    calc
      eLpNorm (fun ω => (f n ω - g ω) * (f n ω + g ω)) 1 P =
          eLpNorm
            (fun ω => ContinuousLinearMap.mul ℝ ℝ (f n ω - g ω) (f n ω + g ω))
            1 P := by simp only [ContinuousLinearMap.mul_apply']
      _ ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ * eLpNorm (f n - g) 2 P *
          eLpNorm (f n + g) 2 P := hraw
      _ ≤ eLpNorm (f n - g) 2 P * eLpNorm (f n + g) 2 P := by
        calc
          _ ≤ 1 * eLpNorm (f n - g) 2 P * eLpNorm (f n + g) 2 P := by gcongr
          _ = _ := by simp
  calc
    eLpNorm (fun ω => (f n ω) ^ 2 - (g ω) ^ 2) 1 P =
        eLpNorm (fun ω => (f n ω - g ω) * (f n ω + g ω)) 1 P := by
          congr 1
          funext ω
          ring
    _ ≤ eLpNorm (f n - g) 2 P * eLpNorm (f n + g) 2 P := hholder
    _ ≤ eLpNorm (f n - g) 2 P *
        (eLpNorm (f n - g) 2 P + 2 * eLpNorm g 2 P) :=
      by gcongr

/-- A fixed-time L2/L1 limit of compensated-square martingales is again a
compensated-square martingale. Exact strong adaptedness of the limit is kept
as a hypothesis. -/
theorem squareCompensator_martingale_of_tendsto
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 m}
    [SigmaFiniteFiltration P F]
    {M : ℝ≥0 → Ω → ℝ} {Mn : ℕ → ℝ≥0 → Ω → ℝ}
    {A : ℝ≥0 → Ω → ℝ} {An : ℕ → ℝ≥0 → Ω → ℝ}
    (hMn2 : ∀ n t, MemLp (Mn n t) 2 P)
    (hM2 : ∀ t, MemLp (M t) 2 P)
    (hL2 : ∀ t,
      Tendsto (fun n => eLpNorm (Mn n t - M t) 2 P) atTop (𝓝 0))
    (hAn : ∀ n, Martingale (fun t ω => (Mn n t ω) ^ 2 - An n t ω) F P)
    (hadapt : StronglyAdapted F (fun t ω => (M t ω) ^ 2 - A t ω))
    (hAint : ∀ t, Integrable (A t) P)
    (hAL1 : ∀ t,
      Tendsto (fun n => eLpNorm (An n t - A t) 1 P) atTop (𝓝 0)) :
    Martingale (fun t ω => (M t ω) ^ 2 - A t ω) F P := by
  apply martingale_of_tendsto_eLpNorm_one hAn hadapt
      (fun t => (hM2 t).integrable_sq.sub (hAint t))
  intro t
  have hsq := tendsto_eLpNorm_sq_sub_sq_one_of_tendsto_eLpNorm_two
    (fun n => hMn2 n t) (hM2 t) (hL2 t)
  have hupper : Tendsto
      (fun n =>
        eLpNorm (fun ω => (Mn n t ω) ^ 2 - (M t ω) ^ 2) 1 P +
          eLpNorm (An n t - A t) 1 P)
      atTop (𝓝 0) := by
    simpa using hsq.add (hAL1 t)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le) fun n => ?_
  have hsquareMeas : AEStronglyMeasurable
      (fun ω => (Mn n t ω) ^ 2 - (M t ω) ^ 2) P :=
    ((hMn2 n t).aestronglyMeasurable.pow 2).sub ((hM2 t).aestronglyMeasurable.pow 2)
  have hcompMeas : AEStronglyMeasurable (An n t - A t) P := by
    have hAnInt : Integrable (An n t) P := by
      have hNint := (hAn n).integrable t
      have hsquareInt := (hMn2 n t).integrable_sq
      refine (hsquareInt.sub hNint).congr (Filter.Eventually.of_forall fun ω => ?_)
      dsimp only [Pi.sub_apply]
      ring
    exact hAnInt.1.sub (hAint t).1
  have htri := eLpNorm_sub_le (f := fun ω => (Mn n t ω) ^ 2 - (M t ω) ^ 2) (g := An n t - A t)
    (μ := P)
    (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  calc
    eLpNorm
        ((fun ω => (Mn n t ω) ^ 2 - An n t ω) -
          fun ω => (M t ω) ^ 2 - A t ω) 1 P =
        eLpNorm
          ((fun ω => (Mn n t ω) ^ 2 - (M t ω) ^ 2) - (An n t - A t)) 1 P := by
      congr 1
      funext ω
      dsimp only [Pi.sub_apply]
      ring
    _ ≤ _ := htri

end ReflectedGMS
