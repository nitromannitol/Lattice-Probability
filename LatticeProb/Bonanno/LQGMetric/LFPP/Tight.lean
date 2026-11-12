/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.Tight at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# DFGPS.S10: tightness of random metrics with a uniform modulus of continuity

DFGPS (`literature/src/1905.00380/lqg-metric-estimates-final.tex` l. 909–913, proof of
Lemma 2.9): "For a connected set `X ⊂ ℂ`, a collection `𝒟` of random metrics on `X` is tight
w.r.t. the local uniform topology if and only if for each `ζ > 0`, there exists `δ > 0` such that
for each `d ∈ 𝒟`, it holds with probability at least `1 - ζ` that `d(z,w) ≤ ζ` for all
`z, w ∈ X` with `|z - w| ≤ δ`. Indeed, this is an easy consequence of the Arzéla–Ascoli theorem,
the Prokhorov theorem, and the triangle inequality."

We prove the direction used by DFGPS (the modulus condition implies tightness) for a compact
connected metric space `X` (DFGPS apply it to closures of dyadic domains, l. 914), for laws on
`C(X × X, ℝ)` a.e. supported on functions vanishing on the diagonal and satisfying the triangle
inequality. Following DFGPS: Arzelà–Ascoli (mathlib `ArzelaAscoli.isCompact_of_equicontinuous`)
for the set of such functions with a fixed sequence of moduli; equicontinuity from the triangle
inequality; pointwise boundedness from connectedness (the set where the family is bounded is
clopen); then a union bound (as in `Prob/TightHolder.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped NNReal ENNReal

namespace LQGMetric
namespace LFPP

variable {X : Type*} [MetricSpace X]

/-- the functions vanishing on the diagonal, satisfying the triangle inequality, with moduli
`(δ n, ζ n)` -/
def modSet (δ ζ : ℕ → ℝ) : Set (X × X → ℝ) :=
  {g | (∀ x, g (x, x) = 0) ∧ (∀ x y z, g (x, z) ≤ g (x, y) + g (y, z)) ∧
    ∀ n z w, dist z w ≤ δ n → g (z, w) ≤ ζ n}

theorem modSet_lipschitz {δ ζ : ℕ → ℝ} {g : X × X → ℝ} (hg : g ∈ modSet δ ζ) (n : ℕ)
    {p q : X × X} (hpq : dist p q ≤ δ n) : |g q - g p| ≤ 2 * ζ n := by
  obtain ⟨-, htri, hmod⟩ := hg
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  rw [Prod.dist_eq, max_le_iff] at hpq
  obtain ⟨h1, h2⟩ := hpq
  simp only at h1 h2
  have a1 := hmod n q1 p1 (by rw [dist_comm]; exact h1)
  have a2 := hmod n p2 q2 h2
  have a3 := hmod n p1 q1 h1
  have a4 := hmod n q2 p2 (by rw [dist_comm]; exact h2)
  have t1 := htri q1 p1 q2
  have t2 := htri p1 p2 q2
  have t3 := htri p1 q1 p2
  have t4 := htri q1 q2 p2
  rw [abs_le]; constructor <;> linarith

theorem modSet_continuous {δ ζ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hζ : Tendsto ζ atTop (𝓝 0))
    {g : X × X → ℝ} (hg : g ∈ modSet δ ζ) : Continuous g := by
  refine Metric.continuous_iff.2 fun p η hη => ?_
  obtain ⟨n, hn⟩ := ((hζ.const_mul 2).eventually (gt_mem_nhds (by simpa using hη))).exists
  refine ⟨δ n, hδ n, fun q hq => ?_⟩
  rw [Real.dist_eq]
  exact (modSet_lipschitz hg n (by rw [dist_comm]; exact hq.le)).trans_lt (by simpa using hn)

/-- pointwise boundedness from connectedness -/
theorem modSet_bounded [ConnectedSpace X] {δ ζ : ℕ → ℝ} (hδ : 0 < δ 0) (p : X × X) :
    ∃ M, ∀ g ∈ modSet (X := X) δ ζ, |g p| ≤ M := by
  by_cases hX : Nonempty X
  swap
  · exact absurd ⟨p.1⟩ hX
  obtain ⟨x0⟩ := hX
  set B : Set (X × X) := {p | ∃ M, ∀ g ∈ modSet (X := X) δ ζ, |g p| ≤ M}
  have hnear : ∀ p q : X × X, dist p q < δ 0 → (p ∈ B ↔ q ∈ B) := by
    intro p q hpq
    constructor
    · rintro ⟨M, hM⟩
      refine ⟨M + 2 * ζ 0, fun g hg => ?_⟩
      have := modSet_lipschitz hg 0 hpq.le
      have := abs_sub_abs_le_abs_sub (g q) (g p)
      linarith [hM g hg]
    · rintro ⟨M, hM⟩
      refine ⟨M + 2 * ζ 0, fun g hg => ?_⟩
      have := modSet_lipschitz hg 0 (by rw [dist_comm]; exact hpq.le)
      have := abs_sub_abs_le_abs_sub (g p) (g q)
      linarith [hM g hg]
  have hopen : IsOpen B := Metric.isOpen_iff.2 fun p hp =>
    ⟨δ 0, hδ, fun q hq => (hnear p q (by rw [dist_comm]; exact hq)).1 hp⟩
  have hclosed : IsClosed B := by
    rw [← isOpen_compl_iff]
    refine Metric.isOpen_iff.2 fun p hp => ⟨δ 0, hδ, fun q hq hqB => hp ?_⟩
    exact (hnear p q (by rw [dist_comm]; exact hq)).2 hqB
  have hne : B.Nonempty := ⟨(x0, x0), 0, fun g hg => by rw [hg.1 x0, abs_zero]⟩
  have huniv := (isClopen_iff.1 ⟨hclosed, hopen⟩).resolve_left hne.ne_empty
  have : p ∈ B := huniv ▸ mem_univ p
  exact this

theorem isClosed_modSet (δ ζ : ℕ → ℝ) : IsClosed (modSet (X := X) δ ζ) := by
  have e : modSet (X := X) δ ζ = (⋂ x, {g : X × X → ℝ | g (x, x) = 0}) ∩
      ((⋂ x, ⋂ y, ⋂ z, {g : X × X → ℝ | g (x, z) ≤ g (x, y) + g (y, z)}) ∩
        ⋂ n, ⋂ z, ⋂ w, {g : X × X → ℝ | dist z w ≤ δ n → g (z, w) ≤ ζ n}) := by
    ext g; simp only [modSet, mem_inter_iff, mem_iInter, mem_ofPred_eq]
  rw [e]
  refine (isClosed_iInter fun x => isClosed_eq (f := fun g : X × X → ℝ => g (x, x))
      (continuous_apply _) continuous_const).inter
    ((isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
      isClosed_le (f := fun g : X × X → ℝ => g (x, z)) (g := fun g => g (x, y) + g (y, z))
        (continuous_apply _) ((continuous_apply _).add (continuous_apply _))).inter
    (isClosed_iInter fun n => isClosed_iInter fun z => isClosed_iInter fun w => ?_))
  by_cases h : dist z w ≤ δ n
  · simp only [h, true_imp_iff]
    exact isClosed_le (f := fun g : X × X → ℝ => g (z, w)) (continuous_apply _) continuous_const
  · simp only [h, false_imp_iff, setOf_true]
    exact isClosed_univ

/-- **Arzelà–Ascoli for metrics with given moduli.** -/
theorem isCompact_setOf_modSet [CompactSpace X] [ConnectedSpace X] {δ ζ : ℕ → ℝ}
    (hδ : ∀ n, 0 < δ n) (hζ : Tendsto ζ atTop (𝓝 0)) :
    IsCompact {d : C(X × X, ℝ) | ⇑d ∈ modSet δ ζ} := by
  set S := {d : C(X × X, ℝ) | ⇑d ∈ modSet δ ζ}
  have himg : ContinuousMap.toFun '' S = modSet δ ζ := by
    ext g; constructor
    · rintro ⟨d, hd, rfl⟩; exact hd
    · intro hg; exact ⟨⟨g, modSet_continuous hδ hζ hg⟩, hg, rfl⟩
  choose b hb using fun p : X × X => modSet_bounded (X := X) (δ := δ) (ζ := ζ) (hδ 0) p
  have hsub : modSet δ ζ ⊆ Set.pi univ fun p => Icc (-b p) (b p) :=
    fun g hg p _ => abs_le.1 (hb p g hg)
  have hcpt : IsCompact (modSet (X := X) δ ζ) :=
    (isCompact_univ_pi fun p => isCompact_Icc).of_isClosed_subset (isClosed_modSet δ ζ) hsub
  refine ArzelaAscoli.isCompact_of_equicontinuous S (himg ▸ hcpt) ?_
  intro p
  rw [Metric.equicontinuousAt_iff_right]
  intro η hη
  obtain ⟨n, hn⟩ := ((hζ.const_mul 2).eventually (gt_mem_nhds (by simpa using hη))).exists
  filter_upwards [Metric.ball_mem_nhds p (hδ n)] with q hq
  intro d
  rw [Real.dist_eq]
  exact (modSet_lipschitz d.2 n (p := q) (q := p) (le_of_lt hq)).trans_lt (by simpa using hn)

/-- **DFGPS.S10 (tightness criterion, the direction DFGPS use)**: on a compact connected metric
space `X`, laws on `C(X × X, ℝ)` that are a.e. supported on functions vanishing on the diagonal
and satisfying the triangle inequality are tight if for every `ζ > 0` there is `δ > 0` with
`μ(d(z,w) ≤ ζ for all |z - w| ≤ δ fails) ≤ ζ` uniformly in `μ`. -/
theorem isTightMeasureSet_of_modulus [CompactSpace X] [ConnectedSpace X]
    (S : Set (Measure C(X × X, ℝ)))
    (hmet : ∀ μ ∈ S, μ {d | ¬ ((∀ x, d (x, x) = 0) ∧ ∀ x y z, d (x, z) ≤ d (x, y) + d (y, z))} = 0)
    (hmod : ∀ ζ : ℝ, 0 < ζ → ∃ δ > 0, ∀ μ ∈ S,
      μ {d | ¬ ∀ z w : X, dist z w ≤ δ → d (z, w) ≤ ζ} ≤ ENNReal.ofReal ζ) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨e, he, heε⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e ≤ ε := by
    rcases eq_top_or_lt_top ε with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' h.ne, by rw [ENNReal.ofReal_toReal h.ne]⟩
  set ζ : ℕ → ℝ := fun n => e / 4 * (1 / 2) ^ n
  have hζ0 : ∀ n, 0 < ζ n := fun n => by positivity
  have hζt : Tendsto ζ atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (e / 4)
    rw [mul_zero] at this
    exact this
  have hζs : Summable ζ := (summable_geometric_two).mul_left (e / 4)
  have hζsum : ∑' n, ENNReal.ofReal (ζ n) = ENNReal.ofReal (e / 2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (hζ0 n).le) hζs, tsum_mul_left,
      tsum_geometric_two]
    ring_nf
  choose δ hδ hδμ using fun n => hmod (ζ n) (hζ0 n)
  refine ⟨_, isCompact_setOf_modSet hδ hζt, fun μ hμ => ?_⟩
  have hsub : {d : C(X × X, ℝ) | ⇑d ∈ modSet δ ζ}ᶜ ⊆
      {d : C(X × X, ℝ) | ¬ ((∀ x, d (x, x) = 0) ∧ ∀ x y z, d (x, z) ≤ d (x, y) + d (y, z))} ∪
        ⋃ n, {d : C(X × X, ℝ) | ¬ ∀ z w : X, dist z w ≤ δ n → d (z, w) ≤ ζ n} := by
    intro d hd
    by_cases hm : (∀ x, d (x, x) = 0) ∧ ∀ x y z, d (x, z) ≤ d (x, y) + d (y, z)
    · right
      simp only [mem_iUnion, mem_ofPred_eq]
      by_contra hc
      push Not at hc
      exact hd ⟨hm.1, hm.2, fun n z w h => hc n z w h⟩
    · left; exact hm
  calc μ _ ≤ μ ({d : C(X × X, ℝ) | ¬ ((∀ x, d (x, x) = 0) ∧
        ∀ x y z, d (x, z) ≤ d (x, y) + d (y, z))} ∪
        ⋃ n, {d : C(X × X, ℝ) | ¬ ∀ z w : X, dist z w ≤ δ n → d (z, w) ≤ ζ n}) :=
        measure_mono hsub
    _ ≤ 0 + ∑' n, ENNReal.ofReal (ζ n) :=
        (measure_union_le _ _).trans (add_le_add (hmet μ hμ).le
          ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun n => hδμ n μ hμ)))
    _ ≤ ε := by
        rw [zero_add, hζsum]
        exact (ENNReal.ofReal_le_ofReal (by linarith)).trans heε

end LFPP
end LQGMetric
