/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate4Meas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4Pair
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4L420F
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-!
# Inputs of `T4_2PairOne` (DEC-89, packet C): measurability and the far normalization

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.7 (l. 1890–1912),
which uses the events `E_r(z)`, `𝔈_r(z)` and `{P ∩ B_{λ₂r}(z) ≠ ∅}` as events of `σ(h)` (GM
Thm 4.2 l. 1557: "events `E_r(z) ∈ σ(h)`"); decision D79 (far normalization `h − ⟨h, ψ₀⟩`, under
which `E`, `𝔈` and the witness of T4.2 are unchanged).

* `gm_measurableSet_of_aeEventIn`, `gm_fieldSigma_le_of_measurable`;
* `gm_measurableSet_E_of_cond2`, `gm_measurableSet_Ef_of_cond2`, `gm_measurableSet_hit`: the
  events of Thm 4.2 (2) and the hit events are measurable on a complete space;
* `gm_t42Wit_addConst`: the witness is invariant under additive constants.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter TopologicalSpace
open LQGMetric.Blueprint

namespace LQGMetric.GM

section Gen
variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem gm_measurableSet_of_aeEventIn {m0 m : MeasurableSpace Ω} {P : Measure[m0] Ω}
    [P.IsComplete] (hm : m ≤ m0) {E : Set Ω} (hE : @AEEventIn Ω m0 P m E) :
    MeasurableSet[m0] E := by
  obtain ⟨F, hF, hEF⟩ := hE
  exact (NullMeasurableSet.congr (hm _ hF).nullMeasurableSet hEF.symm).measurable_of_complete

theorem gm_fieldSigma_le_of_measurable {h : Ω → DistC} (hh : Measurable h) (U : Opens ℂ) :
    fieldSigma h U ≤ mΩ :=
  ((measurable_restrictTo U).comp hh).comap_le

/-- hit events of a measurable random path are measurable -/
theorem gm_measurableSet_hit {η : Ω → C(unitInterval, ℂ)} (hη : Measurable η) {B : Set ℂ}
    (hB : IsOpen B) : MeasurableSet {ω | (range (η ω) ∩ B).Nonempty} := by
  have e : {ω | (range (η ω) ∩ B).Nonempty} =
      ⋃ k : ℕ, {ω | η ω (denseSeq unitInterval k) ∈ B} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, hu⟩
      obtain ⟨k, hk⟩ := (denseRange_denseSeq unitInterval).exists_mem_open
        (hB.preimage (η ω).continuous) ⟨u, hu⟩
      exact ⟨k, hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨_, ⟨_, rfl⟩, hk⟩
  rw [e]
  exact MeasurableSet.iUnion fun k =>
    ((continuous_eval_const _).measurable.comp hη) hB.measurableSet

end Gen

variable {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- the event `E_r(z)` of Thm 4.2 (2) is measurable on a complete space -/
theorem gm_measurableSet_E_of_cond2 [P.IsComplete] (hh : IsWholePlaneGFF h P) {Es : Set DistC}
    {z : ℂ} {ρ a b : ℝ}
    (hE : AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) ρ z))
      (annulus z a b)) (h ⁻¹' Es)) : MeasurableSet (h ⁻¹' Es) := by
  have hAW : annulus z a b ≤ toOpens (Metric.ball z (|ρ| + |b| + 1)) Metric.isOpen_ball := by
    intro w hw
    have h2 : ‖w - z‖ < b := hw.2
    show dist w z < _
    rw [dist_eq_norm]
    have := le_abs_self b; have := abs_nonneg ρ; linarith
  have hsph : Metric.sphere z |ρ| ⊆ toOpens (Metric.ball z (|ρ| + |b| + 1)) Metric.isOpen_ball := by
    intro w hw
    show dist w z < _
    rw [Metric.mem_sphere.1 hw]
    have := abs_nonneg b; linarith
  exact gm_measurableSet_of_aeEventIn (P := P)
    ((gm_fieldSigma_circleAvg_le h hAW hsph).trans (gm_fieldSigma_le_of_measurable hh.measurable _))
    hE

/-- the event `𝔈_r(z)` of Thm 4.2 (2) is measurable on a complete space -/
theorem gm_measurableSet_Ef_of_cond2 [P.IsComplete] (hD : IsWeakLQGMetric γ D c')
    (hh : IsWholePlaneGFF h P) {𝕫 𝕨 : ℂ} {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨) {Es : Set DistC}
    {z : ℂ} {ρ : ℝ}
    (hEf : AEEventIn P (fieldSigma h (ballO z ρ) ⊔ MeasurableSpace.comap
      (fun ω => stopLastExit (η ω) (Metric.ball z ρ)) inferInstance) (h ⁻¹' Es)) :
    MeasurableSet (h ⁻¹' Es) := by
  have hηm := gm_measurable_geod_of_complete hD hh hη
  have hst : Measurable fun f : C(unitInterval, ℂ) => stopLastExit f (Metric.ball z ρ) :=
    measurable_pi_iff.2 fun u => gm_measurable_stopLastExit_apply Metric.isOpen_ball u
  exact gm_measurableSet_of_aeEventIn (P := P) (sup_le (gm_fieldSigma_le_of_measurable hh.measurable _)
    (hst.comp hηm).comap_le) hEf

omit [MeasurableSpace Ω] in
/-- **the witness of T4.2 is invariant under additive constants** (D79; GM l. 2801) -/
theorem gm_t42Wit_addConst {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)}
    (hsel : ∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g)
    {Ef : ℝ → ℂ → ℂ → ℂ → Set DistC}
    (hEf : ∀ (r : ℝ) (z a b : ℂ) (g : DistC) (c : ℝ), addConst g c ∈ Ef r z a b ↔ g ∈ Ef r z a b)
    (lam : Fin 5 → ℝ) (rr : ℝ → ℝ → ℕ → ℝ) (μ 𝕣 ε : ℝ) (𝕫 𝕨 : ℂ) (cst : Ω → ℝ) (ω : Ω) :
    t42Wit sel (fun ω => addConst (h ω) (cst ω)) Ef lam rr μ 𝕣 ε 𝕫 𝕨 ω ↔
      t42Wit sel h Ef lam rr μ 𝕣 ε 𝕫 𝕨 ω := by
  unfold t42Wit
  simp only [hsel, hEf]

end LQGMetric.GM
