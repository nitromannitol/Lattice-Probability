/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.IG.GFF.AbsContCM at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.Lem41
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Complex.Harmonic.Analytic

/-!
# Cameron–Martin shift of a zero-boundary GFF; smooth cut-offs (task IGR-2a, part 1)

Tools for IG1 Prop. 3.4 (Miller–Sheffield, *Imaginary geometry I*, arXiv:1201.1496,
 l. 1233–1265; proof l. 1260–1264):

* `map_add_absCont` : for a zero-boundary GFF `Z` on an open `V` (`LQGMetric.IsZeroBoundaryGFF`,
  `ZBAdmissible V`) and `F ∈ C_c^∞(V)` with `T = ∫ F ·`, `law(Z + T) ≪ law(Z)`
  (IG1 l. 1261: "if we weight the law … by `𝒵⁻¹ exp((h₁, g)_∇)` … the law of `h₁^Ũ` under the
  weighted law is equal to the law of `h₁^Ũ + g`"). Proof: copied from LQGMetric
  `MQ.mqLem4_1Gen` (Papers/MQ/Lem41.lean, steps 2 and "absolute continuity") with `B = U`;
  the Cameron–Martin identity is LQGMetric `MQ.map_tiltMeasure_cmSigma` (QZ's abstract
  `CameronMartin.map_tiltMeasure_path`).
* `contDiff_mul_of_tsupport` : `χ · g` is smooth on `ℂ` when `g` is smooth on an open `V` and
  `tsupport χ ⊆ V` (own elementary lemma).
* `exists_cutoff_of_isCompact` : a smooth compactly supported `χ` with `tsupport χ ⊆ V` and
  `χ = 1` on a compact `K ⊆ V` (the `φ ∈ C_0^∞(Ũ)`, `φ|_U ≡ 1` of IG1 l. 1261; mathlib
  `exists_contDiff_zero_iff_one_iff_of_isClosed` on a thickening of `K`).
* `contDiffOn_of_harmonicOnNhd` : harmonic functions are `C^∞` (mathlib
  `HarmonicAt.analyticAt`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort.IG.GFFAbsCont

open LQGMetric LQGMetric.MQ QuantumZipper QuantumZipper.CameronMartin MarkovZB MarkovHarm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Cameron–Martin, absolute-continuity half** for a zero-boundary GFF on `V`: shifting by
`T = ∫ F ·` with `F ∈ C_c^∞(V)` gives a law absolutely continuous w.r.t. the unshifted one. -/
theorem map_add_absCont {V : Opens ℂ} (hadm : ZBAdmissible V) {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → DistOn V} (hZ : IsZeroBoundaryGFF V Z P) {F : ℂ → ℝ}
    (hF : F ∈ zeroSpace (V : Set ℂ)) {T : DistOn V} (hT : ∀ φ : TestOn V, T φ = ∫ x, F x * φ x) :
    P.map (fun ω => Z ω + T) ≪ P.map Z := by
  rcases (V : Set ℂ).eq_empty_or_nonempty with hV | hne
  · have hF0 : ∀ x, F x = 0 := fun x =>
      image_eq_zero_of_notMem_tsupport fun h => by simpa [hV] using hF.2.2 h
    have hT0 : T = 0 := DFunLike.ext _ _ fun φ => by
      rw [hT]; simp [hF0]
    simp only [hT0, add_zero]
    exact Measure.AbsolutelyContinuous.rfl
  set X : TestOn V → Ω → ℝ := fun φ ω => Z ω φ
  have hX : IsZBGFFProcess V X P := hZ.process
  set f : zsSub (V : Set ℂ) := ⟨F, hF⟩
  set Q := tiltMeasure X P (cmSigma f)
  have hev : Measurable (fun (T : DistOn V) (φ : TestOn V) => T φ) :=
    measurable_iff_comap_le.2 le_rfl
  have hR' : Measurable fun ω => Z ω + T :=
    measurable_distOn_iff.2 fun φ => ((measurable_distOn_apply φ).comp hZ.measurable).add_const (T φ)
  have hμ : P.map (fun ω => Z ω + T) = Q.map Z := by
    refine measure_distOn_ext ?_
    rw [Measure.map_map hev hR', Measure.map_map hev hZ.measurable]
    have e1 : ((fun (T : DistOn V) (φ : TestOn V) => T φ) ∘ Z) = fun ω j => X j ω := rfl
    rw [e1, map_tiltMeasure_cmSigma hadm hne hX f]
    congr 1
    funext ω φ
    simp only [Function.comp_apply, add_apply, hT, X]
    rfl
  rw [hμ]
  have h1 : Q ≪ P := withDensity_absolutelyContinuous _ _
  exact h1.map hZ.measurable

/-- `χ · g` is `C^n` on `ℂ` when `χ` is, `g` is `C^n` on an open `V`, and `tsupport χ ⊆ V`. -/
theorem contDiff_mul_of_tsupport {n : WithTop ℕ∞} {V : Set ℂ} (hV : IsOpen V) {χ g : ℂ → ℝ}
    (hχ : ContDiff ℝ n χ) (hg : ContDiffOn ℝ n g V) (hsupp : tsupport χ ⊆ V) :
    ContDiff ℝ n fun x => χ x * g x := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ V
  · exact hχ.contDiffAt.mul (hg.contDiffAt (hV.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h => hx (hsupp h)
    have hev : (fun x => χ x * g x) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- harmonic functions are smooth -/
theorem contDiffOn_of_harmonicOnNhd {V : Set ℂ} {g : ℂ → ℝ}
    (hg : InnerProductSpace.HarmonicOnNhd g V) {n : WithTop ℕ∞} : ContDiffOn ℝ n g V :=
  fun x hx => ((HarmonicAt.analyticAt (hg x hx)).contDiffAt (n := n)).contDiffWithinAt

/-- a smooth cut-off: `χ ∈ C_c^∞(V)`, `0 ≤ χ ≤ 1`, `χ = 1` on the compact `K ⊆ V` -/
theorem exists_cutoff_of_isCompact {K V : Set ℂ} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) :
    ∃ χ : ℂ → ℝ, χ ∈ zeroSpace V ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hV hKV
  have hd : Disjoint (thickening (δ / 2) K)ᶜ (cthickening 0 K) := by
    rw [disjoint_compl_left_iff_subset]
    exact (cthickening_subset_thickening' (half_pos hδ) (half_pos hδ) K)
  obtain ⟨χ, hχ, -, h0, h1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed
    (n := (⊤ : ℕ∞)) isOpen_thickening.isClosed_compl isClosed_cthickening hd
  have hts : tsupport χ ⊆ cthickening (δ / 2) K := by
    refine closure_minimal (fun x hx => ?_) isClosed_cthickening
    by_contra hc
    exact hx ((h0 x).1 fun hx' => hc (thickening_subset_cthickening _ _ (by simpa using hx')))
  refine ⟨χ, ⟨hχ, ?_, hts.trans ((cthickening_mono (by linarith) K).trans hsub)⟩, fun x hx => ?_⟩
  · exact (hK.cthickening (r := δ / 2)).of_isClosed_subset (isClosed_tsupport _) hts
  · exact (h1 x).1 (by rw [cthickening_zero]; exact subset_closure hx)

end MatedCRTHarmonic.MoTPort.IG.GFFAbsCont
