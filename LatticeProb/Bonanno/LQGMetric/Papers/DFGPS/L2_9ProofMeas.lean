/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_9ProofMeas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_9ProofTight
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.UniformSpace.CompactConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.9: measurability of `ω ↦ 𝔞_ε⁻¹ D_h^ε(·,·;W̄)`

The laws in DFGPS Lemma 2.9 (T:903–906) are laws of random elements of `C(W̄ × W̄, ℝ)`. For the
non-convex `W̄` the chain argument of `aemeasurable_lfppSqC` (squares) does not apply directly;
instead: the map `ψ ↦ c·D_ψ(·,·;W̄)` from `C(ℂ, ℝ)` (compact-open topology) to `C(W̄ × W̄, ℝ)`
is continuous, by the bi-Lipschitz bound `lfppDOn_toReal_le_of_abs_sub_le` (DFGPS T:897–898)
and uniform convergence on the compact `W̄`; the field `ω ↦ h*_ε` is an a.e.-measurable
`C(ℂ, ℝ)`-valued map (`measurable_iff_eval`, as `DG.aemeasurable_toContMap`). Own elementary
argument (measurability is implicit in the paper; DEVIATIONS).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

/-- `ψ ↦ c · D_ψ(·,·;K)` as a map `C(ℂ, ℝ) → C(K × K, ℝ)` -/
def unionMetricMap (ξ c : ℝ) (K : Set ℂ) (ψ : C(ℂ, ℝ)) : C(K × K, ℝ) :=
  toCMap fun p : K × K => c * (lfppDOn ξ ψ K p.1 p.2).toReal

theorem continuous_unionMetricMap {ξ c : ℝ} (hc : 0 ≤ c) (𝒮 : Finset (Set ℂ))
    (h𝒮 : ∀ S ∈ 𝒮, ∃ a s, 0 < s ∧ S = closedSq a s) (hK : IsPreconnected (⋃ S ∈ 𝒮, S)) :
    Continuous (unionMetricMap ξ c (⋃ S ∈ 𝒮, S)) := by
  set K := ⋃ S ∈ 𝒮, S
  have hKc : IsCompact K := isCompact_biUnion_closedSq 𝒮 h𝒮
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hval : ∀ (ψ : C(ℂ, ℝ)) (p : K × K),
      unionMetricMap ξ c K ψ p = c * (lfppDOn ξ ψ K p.1 p.2).toReal := fun ψ p =>
    toCMap_apply_of_continuous (continuous_lfppDOn_union_toReal ψ.continuous 𝒮 h𝒮 hK c) p
  refine continuous_iff_continuousAt.2 fun ψ0 => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro e he
  set M := ‖unionMetricMap ξ c K ψ0‖
  have hcont : Tendsto (fun η : ℝ => (Real.exp (|ξ| * η) - 1) * Real.exp (|ξ| * η) * M)
      (𝓝[>] 0) (𝓝 0) := by
    have : Continuous fun η : ℝ => (Real.exp (|ξ| * η) - 1) * Real.exp (|ξ| * η) * M := by
      fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨η, hηe, hη⟩ := ((hcont.eventually (gt_mem_nhds he)).and self_mem_nhdsWithin).exists
  have hη0 : (0 : ℝ) < η := hη
  have hU : ∀ᶠ ψ in 𝓝 ψ0, ∀ x ∈ K, dist (ψ0 x) (ψ x) < η :=
    Metric.tendstoUniformlyOn_iff.1
      (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
        (tendsto_id (x := 𝓝 ψ0)) K hKc) η hη0
  filter_upwards [hU] with ψ hψ
  rw [ContinuousMap.dist_lt_iff he]
  intro p
  rw [hval, hval, Real.dist_eq]
  have hd1 : ∀ x ∈ K, |ψ x - ψ0 x| ≤ η := fun x hx => by
    have := hψ x hx; rw [Real.dist_eq, abs_sub_comm] at this; exact this.le
  have hd2 : ∀ x ∈ K, |ψ0 x - ψ x| ≤ η := fun x hx => by
    have := hψ x hx; rw [Real.dist_eq] at this; exact this.le
  have f0 := lfppDOn_union_ne_top (ξ := ξ) ψ0.continuous 𝒮 h𝒮 hK p.1 p.1.2 p.2 p.2.2
  have f1 := lfppDOn_union_ne_top (ξ := ξ) ψ.continuous 𝒮 h𝒮 hK p.1 p.1.2 p.2 p.2.2
  have b1 := lfppDOn_toReal_le_of_abs_sub_le (ξ := ξ) hd1 f0
  have b2 := lfppDOn_toReal_le_of_abs_sub_le (ξ := ξ) hd2 f1
  have hM : c * (lfppDOn ξ ψ0 K p.1 p.2).toReal ≤ M := by
    rw [← hval]; exact (le_abs_self _).trans (by
      have := (unionMetricMap ξ c K ψ0).norm_coe_le_norm p
      rwa [Real.norm_eq_abs] at this)
  set E := Real.exp (|ξ| * η)
  have hE : 1 ≤ E := Real.one_le_exp (by positivity)
  set a := c * (lfppDOn ξ ψ0 K p.1 p.2).toReal
  set b := c * (lfppDOn ξ ψ K p.1 p.2).toReal
  have ha : 0 ≤ a := mul_nonneg hc ENNReal.toReal_nonneg
  have hb : 0 ≤ b := mul_nonneg hc ENNReal.toReal_nonneg
  have hba : b ≤ E * a := by
    simp only [a, b]; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left b1 hc
  have hab : a ≤ E * b := by
    simp only [a, b]; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left b2 hc
  have hM0 : 0 ≤ M := norm_nonneg _
  have hE1 : 0 ≤ E - 1 := sub_nonneg.2 hE
  have m1 : (E - 1) * a ≤ (E - 1) * M := mul_le_mul_of_nonneg_left hM hE1
  have m2 : (E - 1) * M ≤ (E - 1) * E * M := by
    have := mul_le_mul_of_nonneg_left hE (mul_nonneg hE1 hM0)
    linarith
  have m3 : (E - 1) * b ≤ (E - 1) * (E * a) := mul_le_mul_of_nonneg_left hba hE1
  have m4 : (E - 1) * E * a ≤ (E - 1) * E * M :=
    mul_le_mul_of_nonneg_left hM (mul_nonneg hE1 (by linarith))
  have k1 : b - a ≤ (E - 1) * E * M := by nlinarith
  have k2 : a - b ≤ (E - 1) * E * M := by nlinarith
  exact lt_of_le_of_lt (abs_sub_le_iff.2 ⟨k1, k2⟩) hηe

/-- **a.e.-measurability** of `ω ↦ 𝔞_ε⁻¹ D_h^ε(·,·;K)` for a connected finite union `K` of
closed squares -/
theorem aemeasurable_lfppSqC_union {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hm : Measurable h) {ξ ε : ℝ}
    (hc : ∀ᵐ ω ∂P, Continuous (heatMollify ε (h ω))) (𝒮 : Finset (Set ℂ))
    (h𝒮 : ∀ S ∈ 𝒮, ∃ a s, 0 < s ∧ S = closedSq a s) (hK : IsPreconnected (⋃ S ∈ 𝒮, S)) :
    AEMeasurable (fun ω => lfppSqC ξ ε (h ω) (⋃ S ∈ 𝒮, S)) P := by
  classical
  set Y : ℂ → Ω → ℝ := fun z ω =>
    if Continuous (heatMollify ε (h ω)) then heatMollify ε (h ω) z else 0
  have hYc : ∀ ω, Continuous fun z => Y z ω := fun ω => by
    by_cases hω : Continuous (heatMollify ε (h ω))
    · simpa only [Y, if_pos hω] using hω
    · simp only [Y, if_neg hω]; exact continuous_const
  set G : Ω → C(ℂ, ℝ) := fun ω => ⟨fun z => Y z ω, hYc ω⟩
  have hYm : ∀ z, AEMeasurable (Y z) P := fun z =>
    ((measurable_heatMollify_left ε z).comp hm).aemeasurable.congr (by
      filter_upwards [hc] with ω hω
      simp only [Function.comp, Y, if_pos hω])
  have hG : AEMeasurable G P := by
    have key : @Measurable (NullMeasurableSpace Ω P) C(ℂ, ℝ) _ _ G := by
      refine (ContinuousMap.measurable_iff_eval (Z := NullMeasurableSpace Ω P)).2 fun z => ?_
      have h1 : NullMeasurable (Y z) P := (hYm z).nullMeasurable
      exact fun s hs => h1 hs
    have h2 : NullMeasurable G P := fun s hs => key hs
    exact h2.aemeasurable
  have hΦ := (continuous_unionMetricMap (ξ := ξ) (c := (aEpsDF ξ ε)⁻¹)
    (inv_nonneg.2 (aEpsDF_nonneg_sq ξ ε)) 𝒮 h𝒮 hK).measurable
  refine (hΦ.comp_aemeasurable hG).congr ?_
  filter_upwards [hc] with ω hω
  have e : (⇑(G ω) : ℂ → ℝ) = heatMollify ε (h ω) := funext fun z => if_pos hω
  show unionMetricMap ξ _ _ (G ω) = lfppSqC ξ ε (h ω) _
  unfold unionMetricMap lfppSqC
  rw [e]

end LQGMetric.DFGPS
