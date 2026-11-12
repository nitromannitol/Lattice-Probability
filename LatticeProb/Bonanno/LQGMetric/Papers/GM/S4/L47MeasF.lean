/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L47MeasF at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47MeasA
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD6

/-!
# GM (4.8): `𝓕_k ⊆ 𝓕` on a complete probability space (D70, `decisions/DEC-47.md`)

GM, arXiv:1905.00383, `uniqueness-final.tex`, (4.8) (l. 1640–1650):
`𝓕_k = σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}}, P|_{[0,s_k]})` (`gmSigF`). Conditional expectations given
`𝓕_k` need `𝓕_k ≤ mΩ`; this holds on a complete space:

* `gm_setSigma_filledBall_le`: the hit events `{𝓑^•_{t} ∩ U ≠ ∅}` (`U` open) are read off the
  dense sequence (`gm_filledBall_inter_open_iff`) and `{x ∈ 𝓑^•_t}` is universally measurable in
  `(D, t)` (`gm_uMeasurableSet_notMem_filledBall`);
* `gm_hullSigma_filledBall_le`: the dyadic-hull pieces of `σ(A, h|_{int A^{(n)}})`;
* `gm_sigF_le`: `hF` of `gm_L4_7_of_null_G` (with `gm_measurable_geod_of_complete` for `P|_{[0,s_k]}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent TopologicalSpace

section
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- `σ(𝓑^•_{τ})` is a sub-σ-algebra on a complete space, `τ` measurable -/
theorem gm_setSigma_filledBall_le [P.IsComplete] {M : Ω → ContMetric} (hM : Measurable M)
    {τ : Ω → ℝ} (hτ : Measurable τ) (𝕫 : ℂ) :
    setSigma (fun ω => filledBall (M ω) 𝕫 (τ ω)) ≤ ‹MeasurableSpace Ω› := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨U, hU, rfl⟩
  have e : {ω | (filledBall (M ω) 𝕫 (τ ω) ∩ U).Nonempty} =
      ⋃ i : ℕ, {ω | denseSeq ℂ i ∈ U ∧ denseSeq ℂ i ∈ filledBall (M ω) 𝕫 (τ ω)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    exact gm_filledBall_inter_open_iff (M ω) 𝕫 (τ ω) hU
  rw [e]
  refine MeasurableSet.iUnion fun i => ?_
  by_cases hi : denseSeq ℂ i ∈ U
  · have hc : MeasurableSet {ω | denseSeq ℂ i ∉ filledBall (M ω) 𝕫 (τ ω)} :=
      gm_measurableSet_of_ae_eq_um (P := P) (hM.prodMk hτ)
        (gm_uMeasurableSet_notMem_filledBall 𝕫 (denseSeq ℂ i)) EventuallyEq.rfl
    convert hc.compl using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, hi, true_and, not_not]
  · convert (MeasurableSet.empty : MeasurableSet (∅ : Set Ω)) using 1
    ext ω
    simp only [mem_ofPred_eq, hi, false_and, mem_empty_iff_false]

/-- `σ(𝓑^•_{τ}, h|_{int (𝓑^•_τ)^{(n)}}) ≤ mΩ` on a complete space -/
theorem gm_hullSigma_filledBall_le [P.IsComplete] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {M : Ω → ContMetric} (hM : Measurable M) {τ : Ω → ℝ} (hτ : Measurable τ) (𝕫 : ℂ) (n : ℕ) :
    hullSigma h (fun ω => filledBall (M ω) 𝕫 (τ ω)) n ≤ ‹MeasurableSpace Ω› := by
  have hS := gm_setSigma_filledBall_le (P := P) hM hτ 𝕫
  refine sup_le hS (MeasurableSpace.generateFrom_le ?_)
  rintro _ ⟨S, F, hF, rfl⟩
  exact (hS _ (measurableSet_hull_eq (fun ω => gm_filledBall_isClosed (M ω) 𝕫 (τ ω)) n S)).inter
    (MarkovGermVer.fieldSigma_le hh _ _ hF)

end

/-- `d ↦ d(𝕫, 𝕨)` is measurable on `ContMetric` -/
theorem gm_measurable_contMetric_apply (p : ℂ × ℂ) : Measurable fun d : ContMetric => d.1 p :=
  (continuous_eval_const p).measurable.comp measurable_subtype_coe

/-- **GM (4.8): `𝓕_k ≤ mΩ`** on a complete space (`hF` of `gm_L4_7_of_null_G`) -/
theorem gm_sigF_le {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [P.IsComplete] {h : Ω → DistC}
    (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2) (hD : IsWeakLQGMetric γ D c')
    (hh : IsWholePlaneGFF h P) {𝕫 𝕨 : ℂ} {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (η ω) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    (ℓ 𝕣 ε β : ℝ) (k : ℕ) :
    gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k) ≤ ‹MeasurableSpace Ω› := by
  have hM : Measurable fun ω => D (h ω) := hD.measurable.comp hh.measurable
  refine sup_le ((iInf_le _ 0).trans (gm_hullSigma_filledBall_le (P := P) hh hM
    (gm_measurable_s4T h38 hγ hγ2 hD hh 𝕫 ℓ 𝕣 ε β k) 𝕫 0)) ?_
  refine Measurable.comap_le ?_
  have hηm := gm_measurable_geod_of_complete hD hh hη
  have hsk := gm_measurable_s4S h38 hγ hγ2 hD hh 𝕫 ℓ 𝕣 ε β k
  have hL : Measurable fun ω => (D (h ω)).1 (𝕫, 𝕨) := (gm_measurable_contMetric_apply _).comp hM
  refine measurable_pi_iff.mpr fun u => ?_
  have hs : Measurable fun ω => projIcc (0 : ℝ) 1 zero_le_one (s4S D h 𝕫 ℓ 𝕣 ε β k ω * u /
      (D (h ω)).1 (𝕫, 𝕨)) :=
    continuous_projIcc.measurable.comp ((hsk.mul_const _).div hL)
  exact continuous_eval.measurable.comp (hηm.prodMk hs)

end LQGMetric.GM
