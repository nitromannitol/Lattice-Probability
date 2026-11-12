/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L29Approx at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# CONF Lemma 2.9, approximation step: finite-dimensional approximations of a random
continuous function

Gwynne–Miller, *Confluence of geodesics in Liouville quantum gravity for γ ∈ (0,2)*
(arXiv:1905.00381), proof of Lemma 2.9 (`lem-fkg-cont`), `confluence-final.tex` lines 685–703:
take a compact exhaustion `K_n` of `X`, choose `δ_n` so that the `δ_n`-modulus of continuity of
`f` on `K_n` is at most `2^{-n}` with probability at least `1 - 2^{-n}` (eq. (2.11),
`eqn-fkg-modulus`), a finite `δ_n`-net `x_j^n ∈ K_n` of `K_n`, a partition of unity `φ_j^n` on
`K_n` subordinate to the balls `B_{δ_n}(x_j^n)`, and `f^n := Σ_j f(x_j^n) φ_j^n`. By
Borel–Cantelli, a.s. `|f − f^n| ≤ 2^{-n}` on `K_n` for all large `n`, so `f^n → f` locally
uniformly.

Main result: `LQGMetric.CONF.exists_fin_approx_ae_tendsto`.

Modelling: `X` is a metric space, locally compact and σ-compact (CONF only says "locally
compact", but uses a compact exhaustion: implicit hypothesis, blueprint CONF.L2.9). `C(X, ℝ)`
carries the compact-open topology (= local uniform topology) and any Borel σ-algebra;
`f : Ω → C(X, ℝ)` is measurable. The bad event uses strict inequalities
(`dist x y < δ`, `ε < |g x − g y|`) so that it is open in `C(X, ℝ)`, hence measurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace LQGMetric

namespace CONF

variable {X : Type*} [MetricSpace X]

/-- The set of continuous functions whose `δ`-oscillation on `K` exceeds `ε` (CONF:686, the
complement of the event in (2.11)). -/
def l29BadSet (K : Set X) (δ ε : ℝ) : Set C(X, ℝ) :=
  {g | ∃ x ∈ K, ∃ y ∈ K, dist x y < δ ∧ ε < |g x - g y|}

lemma isOpen_l29BadSet (K : Set X) (δ ε : ℝ) : IsOpen (l29BadSet K δ ε) := by
  have : l29BadSet K δ ε =
      ⋃ x ∈ K, ⋃ y ∈ K, ⋃ (_ : dist x y < δ), {g : C(X, ℝ) | ε < |g x - g y|} := by
    ext g; simp only [l29BadSet, mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [this]
  refine isOpen_biUnion fun x _ => isOpen_biUnion fun y _ => isOpen_iUnion fun _ => ?_
  exact isOpen_lt continuous_const
    (((continuous_eval_const x).sub (continuous_eval_const y)).abs)

lemma l29BadSet_antitone (K : Set X) (ε : ℝ) :
    Antitone fun k : ℕ => l29BadSet K (1 / ((k : ℝ) + 1)) ε := by
  intro k l hkl g ⟨x, hx, y, hy, hd, he⟩
  refine ⟨x, hx, y, hy, lt_of_lt_of_le hd ?_, he⟩
  gcongr

lemma iInter_l29BadSet {K : Set X} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ⋂ k : ℕ, l29BadSet K (1 / ((k : ℝ) + 1)) ε = ∅ := by
  ext g
  simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
  have hu := hK.uniformContinuousOn_of_continuous g.continuous.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, h⟩ := hu ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  refine ⟨k, fun ⟨x, hx, y, hy, hd, he⟩ => ?_⟩
  have := h x hx y hy (hd.trans hk)
  rw [Real.dist_eq] at this
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [MeasurableSpace C(X, ℝ)] [BorelSpace C(X, ℝ)]

/-- Choice of `δ_n` (CONF:685–687, eq. (2.11)): the probability that the `δ`-oscillation of `f`
on the compact `K` exceeds `ε` is at most `η` for some `δ > 0`. -/
lemma exists_delta_modulus [IsFiniteMeasure P] {f : Ω → C(X, ℝ)} (hfm : Measurable f)
    {K : Set X} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) {η : ENNReal} (hη : 0 < η) :
    ∃ δ > 0, P (f ⁻¹' l29BadSet K δ ε) < η := by
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (s := fun k : ℕ => f ⁻¹' l29BadSet K (1 / ((k : ℝ) + 1)) ε)
    (fun k => (hfm (isOpen_l29BadSet K _ ε).measurableSet).nullMeasurableSet)
    (fun k l hkl => preimage_mono (l29BadSet_antitone K ε hkl))
    ⟨0, measure_ne_top _ _⟩
  rw [← preimage_iInter, iInter_l29BadSet hK hε, preimage_empty, measure_empty] at hlim
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hlim).2 η hη).exists
  exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

omit [MeasurableSpace C(X, ℝ)] [BorelSpace C(X, ℝ)] in
/-- Deterministic error bound (CONF:695–699): if `g` has `δ`-oscillation at most `ε` on `K`,
the points `t ⊆ K` and the `φ_j` are nonnegative, supported in `B_δ(x_j)` and sum to `1` on `K`,
then `|g x − Σ_j g(x_j) φ_j(x)| ≤ ε` on `K`. -/
lemma abs_sub_sum_le {K : Set X} {δ ε : ℝ} {g : C(X, ℝ)} (hg : g ∉ l29BadSet K δ ε)
    {t : Finset X} (htK : ∀ j ∈ t, j ∈ K) (ρ : PartitionOfUnity t X K)
    (hρ : ρ.IsSubordinate fun j => ball (j : X) δ) {x : X} (hx : x ∈ K) :
    |g x - ∑ j : t, g j * ρ j x| ≤ ε := by
  have h1 : ∑ j : t, ρ j x = 1 := by
    rw [← finsum_eq_sum_of_fintype]; exact ρ.sum_eq_one hx
  have : g x - ∑ j : t, g j * ρ j x = ∑ j : t, (g x - g j) * ρ j x := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, mul_one]
  rw [this]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j : t, |(g x - g j) * ρ j x| ≤ ∑ j : t, ε * ρ j x := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (ρ.nonneg j x)]
        by_cases h0 : ρ j x = 0
        · simp [h0]
        refine mul_le_mul_of_nonneg_right ?_ (ρ.nonneg j x)
        have hxj : x ∈ ball (j : X) δ := hρ j (subset_tsupport _ h0)
        by_contra hlt
        exact hg ⟨x, hx, j, htK j j.2, by simpa [mem_ball] using hxj, lt_of_not_ge hlt⟩
    _ = ε := by rw [← Finset.mul_sum, h1, mul_one]

/-- One step of the construction (CONF:685–693): for a compact `K`, `ε > 0` and `η > 0` there
are finitely many points `t ⊆ K` and nonnegative continuous `φ_j` such that, outside an event of
probability `< η`, `|f − Σ_j f(x_j) φ_j| ≤ ε` on `K`. -/
lemma exists_fin_approx_step [IsFiniteMeasure P] {f : Ω → C(X, ℝ)} (hfm : Measurable f)
    {K : Set X} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) {η : ENNReal} (hη : 0 < η) :
    ∃ (t : Finset X) (φ : t → C(X, ℝ)), (∀ j, 0 ≤ φ j) ∧
      P {ω | ∃ x ∈ K, ε < |f ω x - ∑ j : t, f ω j * φ j x|} < η := by
  obtain ⟨δ, hδ, hP⟩ := exists_delta_modulus (P := P) hfm hK hε hη
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => ball x δ)
    (fun x _ => ball_mem_nhds x hδ)
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate (ι := t) hK.isClosed
    (fun j => ball (j : X) δ) (fun _ => isOpen_ball)
    (fun x hx => by
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 (hcov hx)
      exact mem_iUnion.2 ⟨⟨j, hj⟩, hxj⟩)
  refine ⟨t, fun j => ρ j, fun j x => ρ.nonneg j x, lt_of_le_of_lt (measure_mono ?_) hP⟩
  intro ω ⟨x, hx, hlt⟩
  by_contra hω
  exact absurd (abs_sub_sum_le hω (fun j hj => htK j hj) ρ hρ hx) (not_le.2 hlt)

variable [LocallyCompactSpace X] [SigmaCompactSpace X]

/-- **CONF Lemma 2.9, approximation** (CONF:685–703): there are finite sets `t n ⊆ X` and
nonnegative continuous functions `φ n j` such that a.s.
`f^n := Σ_j f(x_j^n) • φ_j^n → f` in `C(X, ℝ)` (local uniform topology). -/
theorem exists_fin_approx_ae_tendsto [IsFiniteMeasure P] {f : Ω → C(X, ℝ)} (hfm : Measurable f) :
    ∃ (t : ℕ → Finset X) (φ : ∀ n, t n → C(X, ℝ)), (∀ n j, 0 ≤ φ n j) ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => ∑ j : t n, f ω j • φ n j) atTop (𝓝 (f ω)) := by
  let K := CompactExhaustion.choice X
  have hstep : ∀ n : ℕ, ∃ (t : Finset X) (φ : t → C(X, ℝ)), (∀ j, 0 ≤ φ j) ∧
      P {ω | ∃ x ∈ K n, (1 / 2 : ℝ) ^ n < |f ω x - ∑ j : t, f ω j * φ j x|} <
        (2⁻¹ : ENNReal) ^ n := fun n =>
    exists_fin_approx_step hfm (K.isCompact n) (by positivity)
      (ENNReal.pow_pos (by norm_num) n)
  choose t φ hφ hP using hstep
  refine ⟨t, φ, hφ, ?_⟩
  have hsum : ∑' n, P {ω | ∃ x ∈ K n, (1 / 2 : ℝ) ^ n < |f ω x - ∑ j : t n, f ω j * φ n j x|}
      ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => (hP n).le)
    rw [ENNReal.tsum_geometric_two]; exact ENNReal.ofNat_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro L hL
  obtain ⟨m, hm⟩ := K.exists_superset_of_isCompact hL
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  filter_upwards [hω, eventually_ge_atTop m, eventually_ge_atTop N] with n hn hnm hnN x hx
  have hxK : x ∈ K n := K.subset hnm (hm hx)
  have hle : |f ω x - ∑ j : t n, f ω j * φ n j x| ≤ (1 / 2 : ℝ) ^ n := by
    by_contra hlt
    exact hn ⟨x, hxK, lt_of_not_ge hlt⟩
  have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hnN
  rw [Real.dist_eq]
  simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  linarith

end CONF

end LQGMetric
