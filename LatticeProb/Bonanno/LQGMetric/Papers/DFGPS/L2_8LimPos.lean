/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8LimPos at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8Lim
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8, third conjunct: positivity of subsequential limits under domination

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:880–889) transfers "subsequential
limits induce the Euclidean topology" along bi-Lipschitz comparisons with random,
`ε`-independent constants: from DDDF's `φ_δ`-metrics (DDDF Theorem 1, bi-Hölder limits) to the
zero-boundary field `h̊` (DDDF Proposition 29 coupling, DDDF §6.1), from `h̊` to `h` (T:887,
`eqn-localized-property`) and from `h` to `h + f` (T:897–898). For metrics on a compact space,
"induces the Euclidean topology" for a continuous limit is positivity off the diagonal; this
module proves the common law-level step:

* `ae_posOffDiag_of_dominated`: if `νₙ → μ`, the laws `αₙ` are relatively compact with all
  subsequential limits a.s. positive off the diagonal, and `νₙ` is dominated by `αₙ` in the sense
  `νₙ(∃ x,y: |x−y| ≥ δ, d(x,y) < η) ≤ αₙ(∃ x,y: |x−y| ≥ δ, d(x,y) < Mη) + ζ` (for all large `n`;
  `M = M(δ,ζ)` — this is what `A ≤ K·B` with a tight family of random constants `K` gives), then
  `μ` is a.s. positive off the diagonal.

Proof: portmanteau for open and closed sets along a subsequence on which `αₙ` converges
(Prokhorov compactness; the Lévy–Prokhorov metric makes the space of laws metrizable), and a
compactness argument on `{|x − y| ≥ δ}`. The paper leaves this step implicit ("combining …",
T:888); own standard argument (proposed DEVIATIONS entry DF-L28-POS).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS

variable {X : Type*} [MetricSpace X]

/-- `d` is positive off the diagonal -/
def IsPosOffDiag (d : C(X × X, ℝ)) : Prop := ∀ x y, x ≠ y → 0 < d (x, y)

/-- `d < η` at some pair at distance `≥ δ` (an open set) -/
def smallSet (δ η : ℝ) : Set C(X × X, ℝ) := {d | ∃ x y : X, δ ≤ dist x y ∧ d (x, y) < η}

/-- `d ≤ η` at some pair at distance `≥ δ` (a closed set for compact `X`) -/
def smallSetC (δ η : ℝ) : Set C(X × X, ℝ) := {d | ∃ x y : X, δ ≤ dist x y ∧ d (x, y) ≤ η}

theorem isOpen_smallSet (δ η : ℝ) : IsOpen (smallSet (X := X) δ η) := by
  have e : smallSet (X := X) δ η =
      ⋃ x, ⋃ y, ⋃ (_ : δ ≤ dist x y), {d : C(X × X, ℝ) | d (x, y) < η} := by
    ext d; simp [smallSet]
  rw [e]
  exact isOpen_iUnion fun x => isOpen_iUnion fun y => isOpen_iUnion fun _ =>
    isOpen_lt (continuous_eval_const _) continuous_const

theorem smallSet_subset_smallSetC (δ η : ℝ) : smallSet (X := X) δ η ⊆ smallSetC δ η :=
  fun _ ⟨x, y, h1, h2⟩ => ⟨x, y, h1, h2.le⟩

theorem isClosed_smallSetC [CompactSpace X] (δ η : ℝ) : IsClosed (smallSetC (X := X) δ η) := by
  refine isClosed_of_closure_subset fun d hd => ?_
  obtain ⟨dn, hdn, hlim⟩ := mem_closure_iff_seq_limit.1 hd
  choose x y hxy hle using hdn
  obtain ⟨p, -, ψ, hψ, hp⟩ :=
    isCompact_univ.tendsto_subseq (fun n => mem_univ ((x n, y n) : X × X))
  refine ⟨p.1, p.2, ?_, ?_⟩
  · exact ge_of_tendsto ((continuous_dist.tendsto p).comp hp)
      (Eventually.of_forall fun n => hxy (ψ n))
  · have := (continuous_eval.tendsto (d, p)).comp
      ((hlim.comp hψ.tendsto_atTop).prodMk_nhds hp)
    exact le_of_tendsto this (Eventually.of_forall fun n => hle (ψ n))

/-- a positive continuous `d` is bounded below on `{|x − y| ≥ δ}` -/
theorem exists_not_mem_smallSetC [CompactSpace X] {d : C(X × X, ℝ)} (hd : IsPosOffDiag d)
    {δ : ℝ} (hδ : 0 < δ) : ∃ m > 0, ∀ η < m, d ∉ smallSetC δ η := by
  set K : Set (X × X) := {p | δ ≤ dist p.1 p.2}
  have hK : IsCompact K :=
    (isClosed_le continuous_const continuous_dist).isCompact
  rcases K.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun η _ ⟨x, y, hxy, _⟩ => ?_⟩
    have : (x, y) ∈ K := hxy
    rw [he] at this; exact this
  · obtain ⟨p0, hp0, hmin⟩ := hK.exists_isMinOn hne d.continuous.continuousOn
    have hne0 : p0.1 ≠ p0.2 := fun h => by
      have : δ ≤ dist p0.1 p0.2 := hp0
      rw [h, dist_self] at this; linarith
    refine ⟨d p0, hd _ _ hne0, fun η hη ⟨x, y, hxy, hle⟩ => ?_⟩
    have := hmin (show (x, y) ∈ K from hxy)
    simp only [mem_setOf_eq] at this
    linarith

/-- **Positivity of limits under domination** (law level; see the module docstring). -/
theorem ae_posOffDiag_of_dominated [CompactSpace X]
    {ν α : ℕ → ProbabilityMeasure C(X × X, ℝ)} {μ : ProbabilityMeasure C(X × X, ℝ)}
    (hν : Tendsto ν atTop (𝓝 μ)) (hαc : IsCompact (closure (range α)))
    (hαlim : ∀ (ψ : ℕ → ℕ) (lam : ProbabilityMeasure C(X × X, ℝ)), StrictMono ψ →
      Tendsto (α ∘ ψ) atTop (𝓝 lam) → ∀ᵐ d ∂(lam : Measure C(X × X, ℝ)), IsPosOffDiag d)
    (hdom : ∀ δ > 0, ∀ ζ > 0, ∃ M > 0, ∀ η > 0, ∀ᶠ n in atTop,
      (ν n : Measure C(X × X, ℝ)) (smallSet δ η) ≤
        (α n : Measure C(X × X, ℝ)) (smallSet δ (M * η)) + ENNReal.ofReal ζ) :
    ∀ᵐ d ∂(μ : Measure C(X × X, ℝ)), IsPosOffDiag d := by
  obtain ⟨lam, -, ψ, hψ, hlimα⟩ :=
    hαc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  have hpos := hαlim ψ lam hψ hlimα
  have hνψ : Tendsto (ν ∘ ψ) atTop (𝓝 μ) := hν.comp hψ.tendsto_atTop
  -- step 1: `μ(small δ η) ≤ lam(smallC δ (M η)) + ζ`
  have key : ∀ δ > 0, ∀ ζ > 0, ∃ M > 0, ∀ η > 0,
      (μ : Measure C(X × X, ℝ)) (smallSet δ η) ≤
        (lam : Measure C(X × X, ℝ)) (smallSetC δ (M * η)) + ENNReal.ofReal ζ := by
    intro δ hδ ζ hζ
    obtain ⟨M, hM, hd⟩ := hdom δ hδ ζ hζ
    refine ⟨M, hM, fun η hη => ?_⟩
    have h1 := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hνψ (isOpen_smallSet δ η)
    have h2 := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlimα
      (isClosed_smallSetC δ (M * η))
    refine ENNReal.le_of_forall_pos_le_add fun ε' hε' _ => ?_
    have hlt : (lam : Measure C(X × X, ℝ)) (smallSetC δ (M * η)) <
        (lam : Measure C(X × X, ℝ)) (smallSetC δ (M * η)) + ε' :=
      ENNReal.lt_add_right (measure_ne_top _ _) (by simpa using hε'.ne')
    have hev := eventually_lt_of_limsup_lt (h2.trans_lt hlt)
    have hev2 := hψ.tendsto_atTop.eventually (hd η hη)
    refine h1.trans (liminf_le_of_frequently_le' (Eventually.frequently ?_))
    filter_upwards [hev, hev2] with k hk1 hk2
    calc (ν (ψ k) : Measure C(X × X, ℝ)) (smallSet δ η)
        ≤ (α (ψ k) : Measure C(X × X, ℝ)) (smallSet δ (M * η)) + ENNReal.ofReal ζ := hk2
      _ ≤ (α (ψ k) : Measure C(X × X, ℝ)) (smallSetC δ (M * η)) + ENNReal.ofReal ζ := by
          gcongr; exact smallSet_subset_smallSetC _ _
      _ ≤ (lam : Measure C(X × X, ℝ)) (smallSetC δ (M * η)) + ε' + ENNReal.ofReal ζ := by
          gcongr; exact hk1.le
      _ = (lam : Measure C(X × X, ℝ)) (smallSetC δ (M * η)) + ENNReal.ofReal ζ + ε' := by
          ring
  -- step 2: the bad event at scale `δ` is `μ`-null
  set N : ℝ → Set C(X × X, ℝ) := fun δ => {d | ∃ x y : X, δ ≤ dist x y ∧ d (x, y) ≤ 0}
  have hN : ∀ δ > 0, (μ : Measure C(X × X, ℝ)) (N δ) = 0 := by
    intro δ hδ
    have hC : Tendsto (fun j : ℕ => (lam : Measure C(X × X, ℝ))
        (smallSetC δ (1 / ((j : ℝ) + 1)))) atTop
        (𝓝 ((lam : Measure C(X × X, ℝ)) (⋂ j : ℕ, smallSetC δ (1 / ((j : ℝ) + 1))))) := by
      refine tendsto_measure_iInter_atTop
        (fun j => (isClosed_smallSetC δ _).measurableSet.nullMeasurableSet) ?_
        ⟨0, measure_ne_top _ _⟩
      intro i j hij d ⟨x, y, hxy, hle⟩
      refine ⟨x, y, hxy, hle.trans ?_⟩
      gcongr
    have h0 : (lam : Measure C(X × X, ℝ)) (⋂ j : ℕ, smallSetC δ (1 / ((j : ℝ) + 1))) = 0 := by
      refine measure_mono_null (t := {d | ¬ IsPosOffDiag d}) (fun d hd hp => ?_) (ae_iff.1 hpos)
      obtain ⟨m, hm, hmd⟩ := exists_not_mem_smallSetC hp hδ
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hm
      exact hmd _ hj (mem_iInter.1 hd j)
    rw [h0] at hC
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ζ' hζ' _ => ?_) zero_le
    obtain ⟨j, hj⟩ := (hC.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < (ζ' : ℝ≥0∞) / 2 by
      simpa using hζ'.ne'))).exists
    obtain ⟨M, hM, hkey⟩ := key δ hδ (ζ' / 2) (by positivity)
    have hη : 0 < 1 / (M * ((j : ℝ) + 1)) := by positivity
    have hMη : M * (1 / (M * ((j : ℝ) + 1))) = 1 / ((j : ℝ) + 1) := by field_simp
    have hsub : N δ ⊆ smallSet δ (1 / (M * ((j : ℝ) + 1))) :=
      fun d ⟨x, y, hxy, hle⟩ => ⟨x, y, hxy, hle.trans_lt hη⟩
    calc (μ : Measure C(X × X, ℝ)) (N δ)
        ≤ (μ : Measure C(X × X, ℝ)) (smallSet δ (1 / (M * ((j : ℝ) + 1)))) := measure_mono hsub
      _ ≤ (lam : Measure C(X × X, ℝ)) (smallSetC δ (1 / ((j : ℝ) + 1))) +
            ENNReal.ofReal (ζ' / 2) := by
          have := hkey _ hη; rwa [hMη] at this
      _ ≤ (ζ' : ℝ≥0∞) / 2 + (ζ' : ℝ≥0∞) / 2 := by
          gcongr
          rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_coe_nnreal]
          simp
      _ = 0 + ζ' := by rw [ENNReal.add_halves, zero_add]
  -- step 3: union over `δ = 1/(k+1)`
  refine ae_iff.2 (measure_mono_null (fun d hd => ?_)
    (measure_iUnion_null fun k : ℕ => hN (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat))
  simp only [IsPosOffDiag, not_forall, not_lt, mem_setOf_eq] at hd
  obtain ⟨x, y, hxy, hle⟩ := hd
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (dist_pos.2 hxy)
  exact mem_iUnion.2 ⟨k, x, y, hk.le, hle⟩

end LQGMetric.DFGPS
