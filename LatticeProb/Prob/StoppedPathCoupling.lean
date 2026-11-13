import Mathlib
import LatticeProb.Prob.PathSpaceDUnif
import LatticeProb.Prob.CoupledStoppedPaths

/-!
# Lévy–Prokhorov distance between laws of coupled stopped paths

Let `U, V : Ω → X` be measurable maps from a measurable space `Ω` with a measure `P` into a
pseudo-emetric space `X` with its Borel structure.  If `P {ω | r ≤ edist (U ω) (V ω)} ≤ r`, then the
Lévy–Prokhorov edistance between the laws `P.map U` and `P.map V` is at most `r`
(`levyProkhorovEDist_map_le_of_bad`).  This is the form of the coupling bound used when both laws
are the laws of functions of one underlying sample point.

For stopped continuous paths with the local uniform metric `dUnif` (`stopPath`), the
Lévy–Prokhorov edistance between the laws of two stopped random paths is bounded by `r` as soon as,
outside an event of probability at most `r`, the two paths agree after random time shifts of at most
`ρ`, oscillate by at most `ε` over windows of length at most `ρ` before their stopping times, and
start within `η` of each other, with `T0 * (2 ε + η) + exp (-T0) < r` for some horizon `T0`
(`levyProkhorovEDist_stopPath_le`).  The deterministic comparison of paths is
`dUnif_stopPath_le_of_shift_coupled`.
-/

open MeasureTheory Set Metric

open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

section Generic

variable {Ω X : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- **Coupling bound on the underlying space.**  If the measurable maps `U, V : Ω → X` satisfy
`P {ω | r ≤ edist (U ω) (V ω)} ≤ r`, then the Lévy–Prokhorov edistance between the laws `P.map U`
and `P.map V` is at most `r`. -/
theorem levyProkhorovEDist_map_le_of_bad (P : Measure Ω) {U V : Ω → X}
    (hU : Measurable U) (hV : Measurable V) (r : ℝ≥0)
    (hbad : P {ω | (r : ℝ≥0∞) ≤ edist (U ω) (V ω)} ≤ r) :
    levyProkhorovEDist (P.map U) (P.map V) ≤ r := by
  apply sInf_le
  intro A hA
  have hleft : U ⁻¹' A ⊆
      (V ⁻¹' thickening (r : ℝ) A) ∪ {ω | (r : ℝ≥0∞) ≤ edist (U ω) (V ω)} := by
    intro ω hω
    by_cases h : (r : ℝ≥0∞) ≤ edist (U ω) (V ω)
    · exact Or.inr h
    · apply Or.inl
      apply (mem_thickening_iff_exists_edist_lt _ _).mpr
      refine ⟨U ω, hω, ?_⟩
      simpa only [edist_comm, ENNReal.ofReal_coe_nnreal] using (lt_of_not_ge h)
  have hright : V ⁻¹' A ⊆
      (U ⁻¹' thickening (r : ℝ) A) ∪ {ω | (r : ℝ≥0∞) ≤ edist (U ω) (V ω)} := by
    intro ω hω
    by_cases h : (r : ℝ≥0∞) ≤ edist (U ω) (V ω)
    · exact Or.inr h
    · apply Or.inl
      apply (mem_thickening_iff_exists_edist_lt _ _).mpr
      refine ⟨V ω, hω, ?_⟩
      simpa only [ENNReal.ofReal_coe_nnreal] using (lt_of_not_ge h)
  constructor
  · change P.map U A ≤ P.map V (thickening (r : ℝ) A) + (r : ℝ≥0∞)
    rw [Measure.map_apply hU hA, Measure.map_apply hV isOpen_thickening.measurableSet]
    exact (measure_mono hleft).trans ((measure_union_le _ _).trans (add_le_add le_rfl hbad))
  · change P.map V A ≤ P.map U (thickening (r : ℝ) A) + (r : ℝ≥0∞)
    rw [Measure.map_apply hV hA, Measure.map_apply hU isOpen_thickening.measurableSet]
    exact (measure_mono hright).trans ((measure_union_le _ _).trans (add_le_add le_rfl hbad))

end Generic

section StoppedPaths

variable {E : Type*} [MetricSpace E]

/-- The continuous path `t ↦ f (t ∧ τ)` stopped at time `τ`. -/
def stopPath (f : C(ℝ≥0, E)) (τ : ℝ≥0) : C(ℝ≥0, E) :=
  f.comp ⟨fun t => min t τ, continuous_id.min continuous_const⟩

@[simp] lemma stopPath_apply (f : C(ℝ≥0, E)) (τ t : ℝ≥0) : stopPath f τ t = f (min t τ) := rfl

/-- **Stopped paths coupled after a time shift are `dUnif`-close.**  If `f ((t + Tf) ∧ τf) =
g ((t + Tg) ∧ τg)` for all `t`, the shifts are at most `ρ`, both paths oscillate by at most `ε` over
windows of length at most `ρ` before their stopping times and `dist (f 0) (g 0) ≤ η`, then
`dUnif (stopPath f τf) (stopPath g τg) ≤ T0 * (2 ε + η) + exp (-T0)` for every horizon `T0`. -/
theorem dUnif_stopPath_le_of_shift_coupled (f g : C(ℝ≥0, E)) (τf τg Tf Tg ρ : ℝ≥0) {ε η : ℝ}
    (hTf : Tf ≤ ρ) (hTg : Tg ≤ ρ)
    (hf : ∀ s t, s ≤ τf → t ≤ τf → dist s t ≤ ρ → dist (f s) (f t) ≤ ε)
    (hg : ∀ s t, s ≤ τg → t ≤ τg → dist s t ≤ ρ → dist (g s) (g t) ≤ ε)
    (h0 : dist (f 0) (g 0) ≤ η)
    (hcoup : ∀ t, f (min (t + Tf) τf) = g (min (t + Tg) τg)) (T0 : ℝ≥0) :
    dUnif (stopPath f τf) (stopPath g τg) ≤ T0 * (2 * ε + η) + Real.exp (-(T0 : ℝ)) :=
  dUnif_le_of_forall_dist_le T0 fun t _ =>
    dist_stopped_le_of_shift_coupled f g τf τg Tf Tg ρ hTf hTg hf hg h0 hcoup t

attribute [local instance] dUnifMetricSpace

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace C(ℝ≥0, E)]
  [OpensMeasurableSpace C(ℝ≥0, E)]

/-- **Lévy–Prokhorov bound for stopped paths coupled after a time shift.**  Let `F, G` be random
continuous paths stopped at the random times `τF, τG` (the stopped paths being measurable for the
Borel structure of the local uniform topology on `C(ℝ≥0, E)`).  Suppose that outside an event
`Good` of complement probability at most `r`, the paths agree after random time shifts `TF, TG` of at
most `ρ`, oscillate by at most `ε` over windows of length at most `ρ` before the stopping times, and
start within `η` of each other.  If `T0 * (2 ε + η) + exp (-T0) < r`, then the laws of the two
stopped paths are at Lévy–Prokhorov edistance at most `r` for the metric `dUnif`. -/
theorem levyProkhorovEDist_stopPath_le (P : Measure Ω) (F G : Ω → C(ℝ≥0, E))
    (τF τG TF TG : Ω → ℝ≥0)
    (hU : Measurable fun ω => stopPath (F ω) (τF ω))
    (hV : Measurable fun ω => stopPath (G ω) (τG ω))
    (ρ : ℝ≥0) {ε η : ℝ} (T0 r : ℝ≥0) (hr : T0 * (2 * ε + η) + Real.exp (-(T0 : ℝ)) < r)
    (Good : Set Ω)
    (hTF : ∀ ω ∈ Good, TF ω ≤ ρ) (hTG : ∀ ω ∈ Good, TG ω ≤ ρ)
    (hF : ∀ ω ∈ Good, ∀ s t, s ≤ τF ω → t ≤ τF ω → dist s t ≤ ρ → dist (F ω s) (F ω t) ≤ ε)
    (hG : ∀ ω ∈ Good, ∀ s t, s ≤ τG ω → t ≤ τG ω → dist s t ≤ ρ → dist (G ω s) (G ω t) ≤ ε)
    (h0 : ∀ ω ∈ Good, dist (F ω 0) (G ω 0) ≤ η)
    (hcoup : ∀ ω ∈ Good, ∀ t, F ω (min (t + TF ω) (τF ω)) = G ω (min (t + TG ω) (τG ω)))
    (hbad : P Goodᶜ ≤ r) :
    levyProkhorovEDist (P.map fun ω => stopPath (F ω) (τF ω))
      (P.map fun ω => stopPath (G ω) (τG ω)) ≤ r := by
  refine levyProkhorovEDist_map_le_of_bad P hU hV r (le_trans (measure_mono ?_) hbad)
  intro ω hω
  by_contra hmem
  have hGood : ω ∈ Good := not_not.1 hmem
  have hd : dist (stopPath (F ω) (τF ω)) (stopPath (G ω) (τG ω)) < r :=
    lt_of_le_of_lt (dUnif_stopPath_le_of_shift_coupled (F ω) (G ω) (τF ω) (τG ω) (TF ω) (TG ω) ρ
      (hTF ω hGood) (hTG ω hGood) (hF ω hGood) (hG ω hGood) (h0 ω hGood) (hcoup ω hGood) T0) hr
  have hlt : edist (stopPath (F ω) (τF ω)) (stopPath (G ω) (τG ω)) < (r : ℝ≥0∞) := by
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt dist_nonneg hd)).2 hd
  exact absurd hω (not_le.2 hlt)

end StoppedPaths

end LatticeProb
