/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_5ProofLocTight at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.Sequences

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Local tightness criterion in `C(ℂ × ℂ, ℝ)`

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`), proof of Lemma 2.5 (T:979–981):
"the laws of `𝔞_ε⁻¹ D_h^ε|_{S_r(0)}` are tight … Since `r` can be made arbitrarily large, we get
that the metrics `𝔞_ε⁻¹ D_h^ε` are tight w.r.t. the local uniform topology on `ℂ × ℂ`." The
step used: a family of laws on `C(ℂ × ℂ, ℝ)` (compact-open topology) is tight as soon as its
restrictions to the balls `B̄(0, n)` are tight (standard; Billingsley, *Convergence of
Probability Measures*, 2nd ed., §7 and Example 1.3 for `C[0,∞)`). Proof: the set
`{f | f|_{B̄(0,n)} ∈ Cₙ ∀ n}` is sequentially compact (Tychonoff on `Π_n C(B̄(0,n), ℝ)`, gluing
the limits), and a union bound.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

/-- the ball `B̄(0, n) ⊂ ℂ × ℂ` -/
abbrev ballN (n : ℕ) : Set (ℂ × ℂ) := closedBall (0 : ℂ × ℂ) n

/-- restriction to `B̄(0, n)` -/
def restrN (n : ℕ) : C(ℂ × ℂ, ℝ) → C(ballN n, ℝ) := fun f => f.restrict (ballN n)

theorem continuous_restrN (n : ℕ) : Continuous (restrN n) :=
  (ContinuousMap.compRightContinuousMap ℝ ⟨Subtype.val, continuous_subtype_val⟩).continuous

theorem mem_ballN_ceil (x : ℂ × ℂ) : x ∈ ballN ⌈‖x‖⌉₊ := by
  rw [mem_closedBall, dist_zero_right]; exact Nat.le_ceil _

/-- **compactness** of `{f | f|_{B̄(0,n)} ∈ Cₙ ∀ n}` for compact `Cₙ` -/
theorem isCompact_setOf_restrN_mem (C : (n : ℕ) → Set C(ballN n, ℝ))
    (hC : ∀ n, IsCompact (C n)) : IsCompact {f : C(ℂ × ℂ, ℝ) | ∀ n, restrN n f ∈ C n} := by
  haveI := polishSpace_continuousMap (ℂ × ℂ) ℝ
  refine IsSeqCompact.isCompact fun f hf => ?_
  set F : ℕ → (n : ℕ) → C(ballN n, ℝ) := fun k n => restrN n (f k)
  have hpi : IsCompact (Set.pi univ C) := isCompact_univ_pi hC
  obtain ⟨g, hg, φ, hφ, hFg⟩ := hpi.tendsto_subseq (x := F) fun k n _ => hf k n
  have hgn : ∀ n, Tendsto (fun k => restrN n (f (φ k))) atTop (𝓝 (g n)) := fun n =>
    (continuous_apply n).continuousAt.tendsto.comp hFg
  -- pointwise limits
  have hpt : ∀ n (x : ballN n), Tendsto (fun k => f (φ k) x) atTop (𝓝 (g n x)) := fun n x =>
    ((continuous_eval_const x).tendsto _).comp (hgn n)
  set G : ℂ × ℂ → ℝ := fun x => g ⌈‖x‖⌉₊ ⟨x, mem_ballN_ceil x⟩
  have hGg : ∀ n (x : ballN n), G x = g n x := fun n x =>
    tendsto_nhds_unique (hpt _ ⟨x.1, mem_ballN_ceil x.1⟩) (hpt n x)
  have hGc : Continuous G := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    set n := ⌈‖x‖⌉₊ + 1
    have hmem : ballN n ∈ 𝓝 x := by
      refine closedBall_mem_nhds_of_mem ?_
      rw [mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (Nat.le_ceil _) (by simp [n])
    have hon : ContinuousOn G (ballN n) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (ballN n).domRestrict G = g n := funext fun y => hGg n y
      rw [this]; exact (g n).continuous
    exact hon.continuousAt hmem
  set a : C(ℂ × ℂ, ℝ) := ⟨G, hGc⟩
  have hra : ∀ n, restrN n a = g n := fun n => by ext y; exact hGg n y
  refine ⟨a, fun n => (hra n).symm ▸ hg n trivial, φ, hφ, ?_⟩
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set n := ⌈R⌉₊
  have hKn : K ⊆ ballN n := hR.trans (closedBall_subset_closedBall (Nat.le_ceil R))
  have hu := (ContinuousMap.tendsto_iff_tendstoUniformly.1 (hgn n))
  have : TendstoUniformlyOn (fun k x => f (φ k) x) G atTop (ballN n) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have e : G ∘ ((↑) : ballN n → ℂ × ℂ) = ⇑(g n) := funext fun y => hGg n y
    rw [e]
    exact hu
  exact this.mono hKn

/-- **local tightness criterion**: laws on `C(ℂ × ℂ, ℝ)` whose restrictions to every ball
`B̄(0, n)` are tight are tight -/
theorem isTightMeasureSet_of_restrN {S : Set (Measure C(ℂ × ℂ, ℝ))}
    (h : ∀ n : ℕ, IsTightMeasureSet ((fun μ : Measure C(ℂ × ℂ, ℝ) => μ.map (restrN n)) '' S)) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  have h' := fun n => (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 (h n)) (δ n)
    (hδ0 n)
  choose C hC hCm using h'
  refine ⟨_, isCompact_setOf_restrN_mem C hC, fun μ hμ => ?_⟩
  have hsub : {f : C(ℂ × ℂ, ℝ) | ∀ n, restrN n f ∈ C n}ᶜ ⊆ ⋃ n, restrN n ⁻¹' (C n)ᶜ := by
    intro f hf
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall] at hf
    obtain ⟨n, hn⟩ := hf
    exact mem_iUnion.2 ⟨n, hn⟩
  calc μ {f : C(ℂ × ℂ, ℝ) | ∀ n, restrN n f ∈ C n}ᶜ ≤ μ (⋃ n, restrN n ⁻¹' (C n)ᶜ) :=
        measure_mono hsub
    _ ≤ ∑' n, μ (restrN n ⁻¹' (C n)ᶜ) := measure_iUnion_le _
    _ = ∑' n, μ.map (restrN n) (C n)ᶜ := by
        congr 1; funext n
        rw [Measure.map_apply (continuous_restrN n).measurable
          (hC n).isClosed.isOpen_compl.measurableSet]
    _ ≤ ∑' n, δ n := ENNReal.tsum_le_tsum fun n => hCm n _ ⟨μ, hμ, rfl⟩
    _ ≤ ε := hδ.le

end LQGMetric.DFGPS
