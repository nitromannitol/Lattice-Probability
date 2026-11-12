/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.Adapter at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Blueprint
import LatticeProb.Bonanno.LQGDimension.LFPP.LowerAssemblyAux1
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Adapter: DG Theorem 1.5 gives LQGDimension's LFPP exponent (node DIM.L-LD-exponent)

Decision D12 = `decisions/DEC-A.md` D-A1, step 4: `λ = 1 − 2/d_γ − γ²/(2d_γ)` is an LFPP exponent at
`ξ = γ/d_γ` in the sense of `LQGDimension.IsLFPPExponent` (paths `[0,1] → U = (−2,2)²` from `0`
to `1`). Lower bound from DG (1.5a) (`D(0,1) ≤ D_LD(0,1)`, more paths), upper bound from DG (1.5b)
with `U' = B_1(1/2)` and `K = {0,1}` (paths in `closure U' ⊂ U`, so `D_LD(0,1) ≤ D(0,1;U')`).
"`D = δ^{λ+o(1)}` w.p. → 1" then gives `log D / log δ → λ` in probability. DEC-A's own sandwich
argument (no published proof of this bookkeeping step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DG

lemma lfppLength_nonneg (ξ : ℝ) (φ : ℂ → ℝ) (p : ℝ → ℂ) :
    0 ≤ LQGDimension.lfppLength ξ φ p :=
  intervalIntegral.integral_nonneg zero_le_one fun _ _ =>
    mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

lemma bddBelow_dg (ξ : ℝ) (φ : ℂ → ℝ) (S : Set ℂ) (z w : ℂ) :
    BddBelow (range fun p : {p : ℝ → ℂ // IsDGPath S z w p} =>
      LQGDimension.lfppLength ξ φ p.1) :=
  ⟨0, by rintro _ ⟨q, rfl⟩; exact lfppLength_nonneg ξ φ q.1⟩

lemma bddBelow_ld (ξ : ℝ) (φ : ℂ → ℝ) :
    BddBelow (range fun p : {p : ℝ → ℂ // LQGDimension.IsAdmissiblePath p} =>
      LQGDimension.lfppLength ξ φ p.1) :=
  ⟨0, by rintro _ ⟨q, rfl⟩; exact lfppLength_nonneg ξ φ q.1⟩

/-- Every admissible path of LQGDimension is a whole-plane DG path. -/
lemma isDGPath_univ_of_admissible {p : ℝ → ℂ} (hp : LQGDimension.IsAdmissiblePath p) :
    IsDGPath univ 0 1 p :=
  ⟨hp.source, hp.target, mapsTo_univ _ _, hp.continuousOn, hp.piecewise_contDiff⟩

/-- The auxiliary domain `U' = B_1(1/2)`. -/
def auxU : Set ℂ := Metric.ball (1 / 2 : ℂ) 1

lemma closure_auxU : closure auxU = Metric.closedBall (1 / 2 : ℂ) 1 :=
  closure_ball _ one_ne_zero

lemma closure_auxU_subset : closure auxU ⊆ LQGDimension.U := by
  rw [closure_auxU]
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h1 := Complex.abs_re_le_norm (z - 1 / 2)
  have h2 := Complex.abs_im_le_norm (z - 1 / 2)
  simp only [Complex.sub_re, Complex.sub_im] at h1 h2
  norm_num at h1 h2
  refine ⟨?_, ?_⟩
  · have := abs_sub_abs_le_abs_sub z.re (1 / 2)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    linarith
  · linarith

lemma isDGPath_segment : IsDGPath (closure auxU) 0 1 (fun t : ℝ => (t : ℂ)) := by
  refine ⟨by simp, by simp, ?_, Complex.continuous_ofReal.continuousOn,
    LQGDimension.LowerAsm.admissible_ofReal.piecewise_contDiff⟩
  intro t ht
  rw [closure_auxU, Metric.mem_closedBall, dist_eq_norm]
  have : ((t : ℂ) - 1 / 2) = ((t - 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [ht.1, ht.2]

/-- `D(0,1) ≤ D_LD(0,1)`: LQGDimension's paths are whole-plane paths. -/
lemma dgLFPP_univ_le (ξ : ℝ) (φ : ℂ → ℝ) :
    dgLFPP ξ φ univ 0 1 ≤ LQGDimension.lfppDistance ξ φ := by
  have : Nonempty {p : ℝ → ℂ // LQGDimension.IsAdmissiblePath p} :=
    ⟨⟨_, LQGDimension.LowerAsm.admissible_ofReal⟩⟩
  exact le_ciInf fun p => ciInf_le (bddBelow_dg ξ φ univ 0 1)
    (⟨p.1, isDGPath_univ_of_admissible p.2⟩ : {p : ℝ → ℂ // IsDGPath univ 0 1 p})

/-- `D_LD(0,1) ≤ D(0,1;U')`: paths in `closure U'` are admissible. -/
lemma lfppDistance_le_dgLFPP_auxU (ξ : ℝ) (φ : ℂ → ℝ) :
    LQGDimension.lfppDistance ξ φ ≤ dgLFPP ξ φ (closure auxU) 0 1 := by
  have : Nonempty {p : ℝ → ℂ // IsDGPath (closure auxU) 0 1 p} := ⟨⟨_, isDGPath_segment⟩⟩
  refine le_ciInf fun p => ciInf_le (bddBelow_ld ξ φ)
    (⟨p.1, ⟨p.2.source, p.2.target, p.2.mapsTo.mono_right closure_auxU_subset,
      p.2.continuousOn, p.2.piecewise_contDiff⟩⟩ :
      {p : ℝ → ℂ // LQGDimension.IsAdmissiblePath p})

lemma ofReal_le_dgDiam (ξ : ℝ) (φ : ℂ → ℝ) :
    ENNReal.ofReal (dgLFPP ξ φ (closure auxU) 0 1) ≤ dgDiam ξ φ auxU {0, 1} :=
  le_iSup₂_of_le (0 : ℂ) (by simp) (le_iSup₂_of_le (1 : ℂ) (by simp) le_rfl)

/-- If `δ^{λ+η} ≤ X ≤ δ^{λ−η}` with `δ ∈ (0,1)` then `|log X / log δ − λ| ≤ η`. -/
lemma abs_log_div_sub_le {δ X lam η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h1 : δ ^ (lam + η) ≤ X) (h2 : X ≤ δ ^ (lam - η)) :
    |Real.log X / Real.log δ - lam| ≤ η := by
  have hX : 0 < X := lt_of_lt_of_le (Real.rpow_pos_of_pos hδ0 _) h1
  have hL : Real.log δ < 0 := Real.log_neg hδ0 hδ1
  have l1 := Real.log_le_log (Real.rpow_pos_of_pos hδ0 _) h1
  have l2 := Real.log_le_log hX h2
  rw [Real.log_rpow hδ0] at l1 l2
  have a1 : Real.log X / Real.log δ ≤ lam + η := by
    rw [div_le_iff_of_neg hL]; linarith
  have a2 : lam - η ≤ Real.log X / Real.log δ := by
    rw [le_div_iff_of_neg hL]; linarith
  rw [abs_sub_le_iff]; constructor <;> linarith

/-- **DIM.L-LD-exponent** (DEC-A D-A1 step 4). Under DG Theorem 1.5, for `γ ∈ (0,2)` the DG
exponent `λ = 1 − 2/d_γ − γ²/(2d_γ)` is an LFPP exponent at `ξ = γ/d_γ` in LQGDimension's
sense, for every circle-average process of the normalized whole-plane GFF. -/
theorem isLFPPExponent_of_dgThm1_5 (hDG : DGThm1_5) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hc : ℝ → ℂ → Ω → ℝ}
    (hG : LQGDimension.IsGFFCircleAverage hc P) :
    LQGDimension.IsLFPPExponent hc P (xiGamma γ) (dgLambda γ) := by
  obtain ⟨hA, hB⟩ := hDG γ hγ0 hγ2 P hc hG
  rw [LQGDimension.IsLFPPExponent, tendstoInMeasure_iff_dist]
  intro ε hε
  set ξ := xiGamma γ
  set lam := dgLambda γ
  set η := ε / 2 with hη
  have hη0 : 0 < η := by positivity
  have tA := hA 0 1 zero_ne_one η hη0
  have hK : IsCompact ({0, 1} : Set ℂ) := (Set.toFinite _).isCompact
  have hKU : ({0, 1} : Set ℂ) ⊆ auxU := by
    intro z hz
    rcases hz with rfl | rfl <;> simp [auxU, Metric.mem_ball, dist_eq_norm] <;> norm_num
  have tB := hB auxU {0, 1} Metric.isOpen_ball
    ((convex_ball _ _).isConnected (Metric.nonempty_ball.2 one_pos)) Metric.isBounded_ball hK hKU
    ⟨0, by simp, 1, by simp, zero_ne_one⟩ η hη0
  have tS := tA.add tB
  rw [add_zero] at tS
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tS
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  by_contra hn
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hn
  obtain ⟨⟨a1, -⟩, -, a4⟩ := hn
  have hX1 : δ ^ (lam + η) ≤ LQGDimension.lfppDistance ξ (fun z => hc δ z ω) :=
    a1.trans (dgLFPP_univ_le ξ _)
  have hX2 : LQGDimension.lfppDistance ξ (fun z => hc δ z ω) ≤ δ ^ (lam - η) := by
    have e := (ENNReal.ofReal_le_ofReal (lfppDistance_le_dgLFPP_auxU ξ (fun z => hc δ z ω))).trans
      ((ofReal_le_dgDiam ξ _).trans a4)
    exact (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hδ.1.le _)).1 e
  have key := abs_log_div_sub_le hδ.1 hδ.2 hX1 hX2
  simp only [mem_ofPred_eq, Real.dist_eq] at hω
  linarith
