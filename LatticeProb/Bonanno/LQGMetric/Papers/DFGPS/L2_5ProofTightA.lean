/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_5ProofTightA at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofLocTight
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8ProofF
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_9ProofPos
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.5 A, first conjunct: tightness of `𝔞_ε⁻¹ D_h^ε` (T:979–981)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:979–981 obtain tightness of the
restrictions of `𝔞_ε⁻¹ D_h^ε` to `S_r(0)` from Lemma 2.8 on `S_{Rr}(0)` and the agreement
event (2.13), then let `r → ∞`. For tightness alone we use the simpler domination
`D_h^ε(u,v) ≤ D_h^ε(u,v;S)` (fewer paths) on a closed square `S`: by the tightness criterion
(2.8) (`isTightMeasureSet_of_le_mul`, constant `1`) the laws of the restrictions to `S × S` are
tight; restricting further to the balls `B̄(0,n) ⊂ ℂ × ℂ` and the local criterion
`isTightMeasureSet_of_restrN` conclude. (Own simplification of the paper's route; the agreement
event is still needed for the length property, conjunct 2. Proposed DEVIATIONS entry
DF-L25-TIGHT.)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

/-- the image of a tight family under a continuous map is tight -/
theorem isTightMeasureSet_image_map {E F : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] [T2Space F]
    {g : E → F} (hg : Continuous g) {S : Set (Measure E)} (hS : IsTightMeasureSet S) :
    IsTightMeasureSet ((fun μ : Measure E => μ.map g) '' S) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hS ⊢
  intro e he
  obtain ⟨C, hC, hCm⟩ := hS e he
  refine ⟨g '' C, hC.image hg, ?_⟩
  rintro _ ⟨μ, hμ, rfl⟩
  rw [Measure.map_apply hg.measurable (hC.image hg).isClosed.isOpen_compl.measurableSet]
  exact (measure_mono (show g ⁻¹' (g '' C)ᶜ ⊆ Cᶜ from fun d hd hdC => hd ⟨d, hdC, rfl⟩)).trans
    (hCm μ hμ)

theorem lfppC_apply_of_continuous {ξ ε : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g))
    (p : ℂ × ℂ) : lfppC ξ ε g p = (aEpsDF ξ ε)⁻¹ * (lfppDistE ξ ε g p.1 p.2).toReal := by
  have e : (fun p : ℂ × ℂ => (aEpsDF ξ ε)⁻¹ * lfppDist ξ ε g p) =
      fun p => (aEpsDF ξ ε)⁻¹ * lfppDReal ξ (heatMollify ε g) p := by
    funext p; simp only [lfppDist, lfppDReal, lfppDistE_eq_lfppDOn]
  have hcont : Continuous fun p : ℂ × ℂ => (aEpsDF ξ ε)⁻¹ * lfppDist ξ ε g p := by
    rw [e]; exact continuous_const.mul (continuous_lfppDReal hc)
  exact toCMap_apply_of_continuous hcont p

theorem aemeasurable_lfppC {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsGFFPlusBddCont h P) {ξ ε : ℝ} (hε : ε ≠ 0) :
    AEMeasurable (fun ω => lfppC ξ ε (h ω)) P := by
  have hev : ∀ p : ℂ × ℂ, AEMeasurable (fun ω => lfppC ξ ε (h ω) p) P := fun p =>
    (((IsGFFPlusBddCont.aemeasurable_lfppDistE (ξ := ξ) hh hε p.1 p.2).ennreal_toReal).const_mul _).congr (by
      filter_upwards [hh.ae_tendstoLocallyUniformly_heatMollify ε hε] with ω hω
      exact (lfppC_apply_of_continuous hω.2 p).symm)
  have key : @Measurable (NullMeasurableSpace Ω P) C(ℂ × ℂ, ℝ) _ _
      (fun ω => lfppC ξ ε (h ω)) := by
    refine (ContinuousMap.measurable_iff_eval (Z := NullMeasurableSpace Ω P)).2 fun p => ?_
    have h1 : NullMeasurable (fun ω => lfppC ξ ε (h ω) p) P := (hev p).nullMeasurable
    exact fun s hs => h1 hs
  have h2 : NullMeasurable (fun ω => lfppC ξ ε (h ω)) P := fun s hs => key hs
  exact h2.aemeasurable

/-- the closed square `[-(n+1), n+1]²` contains both coordinates of `B̄(0, n)` -/
theorem ballN_coord_mem (n : ℕ) {p : ℂ × ℂ} (hp : p ∈ ballN n) :
    p.1 ∈ closedSq ⟨-((n : ℝ) + 1), -((n : ℝ) + 1)⟩ (2 * ((n : ℝ) + 1)) ∧
      p.2 ∈ closedSq ⟨-((n : ℝ) + 1), -((n : ℝ) + 1)⟩ (2 * ((n : ℝ) + 1)) := by
  rw [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] at hp
  have k : ∀ z : ℂ, ‖z‖ ≤ n →
      z ∈ closedSq ⟨-((n : ℝ) + 1), -((n : ℝ) + 1)⟩ (2 * ((n : ℝ) + 1)) := fun z hz => by
    have h1 := Complex.abs_re_le_norm z
    have h2 := Complex.abs_im_le_norm z
    rw [abs_le] at h1 h2
    exact ⟨by linarith [h1.1], by linarith [h1.2], by linarith [h2.1], by linarith [h2.2]⟩
  exact ⟨k _ hp.1, k _ hp.2⟩

/-- **DFGPS Lemma 2.5 A, first conjunct** (T:979–981): tightness of the laws of
`𝔞_ε⁻¹ D_h^ε`, `ε ∈ (0,1)`, in `C(ℂ × ℂ, ℝ)` (local uniform topology). -/
theorem lem2_5_tight (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsGFFPlusBddCont h P) :
    IsTightMeasureSet {μ | ∃ ε ∈ Ioo (0 : ℝ) 1, μ = P.map fun ω => lfppC (xiGamma γ) ε (h ω)} := by
  refine isTightMeasureSet_of_restrN fun n => ?_
  set ξ := xiGamma γ
  set a : ℂ := ⟨-((n : ℝ) + 1), -((n : ℝ) + 1)⟩
  set s : ℝ := 2 * ((n : ℝ) + 1)
  have hs : 0 < s := by positivity
  set S := closedSq a s
  haveI : CompactSpace S := isCompact_iff_compactSpace.1 (isCompact_closedSq a hs.le)
  haveI : ConnectedSpace S := isConnected_iff_connectedSpace.1
    ((convex_closedSq a s).isConnected ⟨a, by simp [closedSq]; exact hs.le⟩)
  obtain ⟨-, hT, -⟩ := h28 γ hγ hγ2 a s hs P h hh
  -- restriction `C(ℂ × ℂ, ℝ) → C(S × S, ℝ)`
  let iS : C(S × S, ℂ × ℂ) := ⟨fun q => (q.1.1, q.2.1), by fun_prop⟩
  let rS := ContinuousMap.compRightContinuousMap ℝ iS
  -- restriction `C(S × S, ℝ) → C(B̄(0,n), ℝ)`
  let iB : C(ballN n, S × S) := ⟨fun p => (⟨p.1.1, (ballN_coord_mem n p.2).1⟩,
    ⟨p.1.2, (ballN_coord_mem n p.2).2⟩), by fun_prop⟩
  let rB := ContinuousMap.compRightContinuousMap ℝ iB
  have hcS : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, Continuous (heatMollify ε (h ω)) := fun ε hε =>
    (hh.ae_tendstoLocallyUniformly_heatMollify ε hε.1.ne').mono fun ω hω => hω.2
  have hTS : IsTightMeasureSet {μ | ∃ ε ∈ Ioo (0 : ℝ) 1,
      μ = P.map fun ω => rS (lfppC ξ ε (h ω))} := by
    refine isTightMeasureSet_of_le_mul (Ioo (0 : ℝ) 1) (fun ε ω => lfppSqC ξ ε (h ω) S)
      (fun ε ω => rS (lfppC ξ ε (h ω))) (fun _ => 1) measurable_const hT
      (fun ε hε => aemeasurable_lfppSqC hh.1 (hcS ε hε) hs)
      (fun ε hε => rS.continuous.measurable.comp_aemeasurable (aemeasurable_lfppC hh hε.1.ne'))
      ?_ ?_ ?_
    · intro ε hε
      filter_upwards [hcS ε hε] with ω hω x
      rw [lfppSqC_apply_of_continuous hω hs, lfppDOn_self (convex_closedSq a s) x.2,
        ENNReal.toReal_zero, mul_zero]
    · intro ε hε
      filter_upwards [hcS ε hε] with ω hω
      refine ⟨fun x => ?_, fun x y z => ?_⟩
      · show lfppC ξ ε (h ω) (x.1, x.1) = 0
        rw [lfppC_apply_of_continuous hω, lfppDistE_self, ENNReal.toReal_zero, mul_zero]
      · show lfppC ξ ε (h ω) (x.1, z.1) ≤ lfppC ξ ε (h ω) (x.1, y.1) + lfppC ξ ε (h ω) (y.1, z.1)
        simp only [lfppC_apply_of_continuous hω]
        rw [← mul_add, ← ENNReal.toReal_add (by rw [lfppDistE_eq_lfppDOn]; exact lfppD_ne_top hω _ _)
          (by rw [lfppDistE_eq_lfppDOn]; exact lfppD_ne_top hω _ _)]
        refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (ENNReal.add_ne_top.2
          ⟨by rw [lfppDistE_eq_lfppDOn]; exact lfppD_ne_top hω _ _,
            by rw [lfppDistE_eq_lfppDOn]; exact lfppD_ne_top hω _ _⟩) ?_)
          (inv_nonneg.2 (aEpsDF_nonneg_sq ξ ε))
        simp only [lfppDistE_eq_lfppDOn]
        exact lfppDOn_triangle _ _ _
    · intro ε hε
      filter_upwards [hcS ε hε] with ω hω p
      rw [one_mul, lfppSqC_apply_of_continuous hω hs]
      show lfppC ξ ε (h ω) (p.1.1, p.2.1) ≤ _
      rw [lfppC_apply_of_continuous hω]
      obtain ⟨B, -, hB⟩ := exists_lfppDOn_le_mul_norm (ξ := ξ) hω (convex_closedSq a s)
        (closedSq_subset_closedBall a hs.le)
      exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB _ p.1.2 _ p.2.2))
        (lfppDistE_le_lfppDOn ξ ε (h ω) S _ _)) (inv_nonneg.2 (aEpsDF_nonneg_sq ξ ε))
  refine (isTightMeasureSet_image_map rB.continuous hTS).subset ?_
  rintro _ ⟨_, ⟨ε, hε, rfl⟩, rfl⟩
  refine ⟨P.map fun ω => rS (lfppC ξ ε (h ω)), ⟨ε, hε, rfl⟩, ?_⟩
  dsimp only
  rw [AEMeasurable.map_map_of_aemeasurable rB.continuous.aemeasurable
      (show AEMeasurable (fun ω => rS (lfppC ξ ε (h ω))) P from
        rS.continuous.measurable.comp_aemeasurable (aemeasurable_lfppC hh hε.1.ne')),
    AEMeasurable.map_map_of_aemeasurable (continuous_restrN n).aemeasurable
      (aemeasurable_lfppC hh hε.1.ne')]
  congr 1

end LQGMetric.DFGPS
