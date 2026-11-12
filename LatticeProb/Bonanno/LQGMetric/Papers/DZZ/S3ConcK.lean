/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcK at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcH
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6Exp
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CM4

/-!
# DEC-124 packet I4: the path regularity of the coarse field, `DZZCoarseReg` (P2-DZZI4)

`DZZCoarseReg P γ W` (S3ConcH): for every `δ ∈ (0,1)` and `ε > 0` there is a set `ℛ` of coarse
paths with `P(𝒳_δ ∉ ℛ) ≤ ε` and a finite `1`-net on `ℛ`, for DZZ's coarse field
`𝒳_δ = coarseField W (dzzCmc γ) δ` (S3D124; DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 1557).
DZZ use this regularity implicitly (the passage from the continuum `𝒳_δ` to finitely many
Gaussian coordinates in the proof of Prop 3.17, l. 1584–1594).

Proof (the route of `decisions/DEC-124.md` §2 / §5 I4; no rate and no Gaussian tail needed):
* the `η`-part of the index (dyadic boxes of side `≥ δ^κ`) is finite (`kc_finite_boxes`);
* the coarse scales are finitely many (`kc_finite_coarseScale`);
* for each scale `ε > 0`, `v ↦ h̃_ε(v)` has a continuous version (`exists_continuous_tildeHInf`,
  S2L6Exp, from the Kolmogorov–Čentsov tool `exists_continuous_modification_of_kernel_half` and
  DZZ's increment bound, `lem-variance-continuity`, l. 453–520), uniformly continuous on the
  compact `𝕍`; hence the measurable events `kcBad W ε m` (two rational points of `𝕍` at distance
  `≤ 2·2^{-m}` whose `h̃_ε`-values differ by more than `1/2`) decrease to a null set
  (`kc_tendsto_bad`, `tendsto_measure_iInter_atTop`);
* `ℛ = {x : |x(v, ε) − x(π_M v, ε)| ≤ 1/2 for all coarse points}`, with `π_M` the floor map to
  the `2^{-M}`-grid; the net enumerates all boxes and the grid points at all coarse scales.
This is an elementary argument (DEC-124 §2), not a step written out in DZZ.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma kc_isCompact_dzzV : IsCompact dzzV := by
  have : dzzV = dzzVIn 0 := by ext z; simp [dzzV, dzzVIn]
  rw [this]; exact cm_isCompact_dzzVIn 0

/-! ### Finiteness of the index set modulo the grid -/

lemma kc_lt_of_le_pow {κ δ : ℝ} {N n : ℕ} (hN : (2 : ℝ)⁻¹ ^ N < δ ^ κ)
    (h : δ ^ κ ≤ (2 : ℝ)⁻¹ ^ n) : n < N := by
  by_contra h'
  push_neg at h'
  have : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) h'
  linarith

lemma kc_finite_coarseScale {κ δ : ℝ} (hδ : 0 < δ) : {ε | IsCoarseScale κ δ ε}.Finite := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (Real.rpow_pos_of_pos hδ κ)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ((Set.finite_singleton (δ ^ κ)).union
    ((Set.finite_lt_nat N).image fun n : ℕ => (2 : ℝ)⁻¹ ^ n)).subset ?_
  rintro ε (rfl | ⟨n, rfl, hn⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨n, kc_lt_of_le_pow hN hn, rfl⟩

lemma kc_pos_of_coarseScale {κ δ ε : ℝ} (hδ : 0 < δ) (h : IsCoarseScale κ δ ε) : 0 < ε := by
  rcases h with rfl | ⟨n, rfl, -⟩
  · exact Real.rpow_pos_of_pos hδ κ
  · positivity

lemma kc_finite_boxes {κ δ : ℝ} (hδ : 0 < δ) : Finite {b : DyBox // δ ^ κ ≤ b.side} := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (Real.rpow_pos_of_pos hδ κ)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hn : ∀ b : {b : DyBox // δ ^ κ ≤ b.side}, b.1.n < N := fun b =>
    kc_lt_of_le_pow hN b.2
  have hp : ∀ b : {b : DyBox // δ ^ κ ≤ b.side}, 2 ^ b.1.n ≤ 2 ^ N := fun b =>
    Nat.pow_le_pow_right two_pos (hn b).le
  refine Finite.of_injective (β := Fin N × Fin (2 ^ N) × Fin (2 ^ N))
    (fun b => (⟨b.1.n, hn b⟩, ⟨b.1.j, lt_of_lt_of_le b.1.hj (hp b)⟩,
      ⟨b.1.k, lt_of_lt_of_le b.1.hk (hp b)⟩)) ?_
  rintro ⟨⟨n, j, k, hj, hk⟩, _⟩ ⟨⟨n', j', k', hj', hk'⟩, _⟩ h
  simp only [Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-! ### The grid map -/

/-- The floor map to the `2^{-m}`-grid. -/
def kcGrid (m : ℕ) (v : ℂ) : ℂ :=
  ⟨(⌊v.re * 2 ^ m⌋ : ℝ) / 2 ^ m, (⌊v.im * 2 ^ m⌋ : ℝ) / 2 ^ m⟩

lemma kc_floor_div {y c : ℝ} (hc : 0 < c) : |y - (⌊y * c⌋ : ℝ) / c| ≤ c⁻¹ := by
  have h1 := Int.floor_le (y * c)
  have h2 := Int.lt_floor_add_one (y * c)
  have e : y - (⌊y * c⌋ : ℝ) / c = (y * c - ⌊y * c⌋) / c := by field_simp
  rw [e, abs_div, abs_of_pos hc, abs_of_nonneg (by linarith), div_le_iff₀ hc,
    inv_mul_cancel₀ hc.ne']
  linarith

lemma kc_floor_bounds {y c : ℝ} (hc : 0 < c) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    0 ≤ ⌊y * c⌋ ∧ (⌊y * c⌋ : ℝ) ≤ c := by
  refine ⟨Int.floor_nonneg.2 (mul_nonneg h0 hc.le), ?_⟩
  exact (Int.floor_le _).trans (mul_le_of_le_one_left hc.le h1)

lemma kc_floor_mem {y c : ℝ} (hc : 0 < c) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    0 ≤ (⌊y * c⌋ : ℝ) / c ∧ (⌊y * c⌋ : ℝ) / c ≤ 1 := by
  obtain ⟨a, b⟩ := kc_floor_bounds hc h0 h1
  have a' : (0 : ℝ) ≤ ⌊y * c⌋ := by exact_mod_cast a
  exact ⟨div_nonneg a' hc.le, (div_le_one hc).2 b⟩

lemma kcGrid_mem (m : ℕ) {v : ℂ} (hv : v ∈ dzzV) : kcGrid m v ∈ dzzV := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  have hc : (0 : ℝ) < 2 ^ m := by positivity
  exact ⟨(kc_floor_mem hc h1 h2).1, (kc_floor_mem hc h1 h2).2, (kc_floor_mem hc h3 h4).1,
    (kc_floor_mem hc h3 h4).2⟩

lemma kcGrid_rat (m : ℕ) (v : ℂ) : IsRatPt (kcGrid m v) :=
  ⟨(⌊v.re * 2 ^ m⌋ : ℚ) / 2 ^ m, (⌊v.im * 2 ^ m⌋ : ℚ) / 2 ^ m, by
    apply Complex.ext <;> simp [kcGrid]⟩

lemma kcGrid_dist (m : ℕ) (v : ℂ) : dist v (kcGrid m v) ≤ 2 * (2 : ℝ)⁻¹ ^ m := by
  rw [Complex.dist_eq]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hc : (0 : ℝ) < 2 ^ m := by positivity
  have e1 := kc_floor_div (y := v.re) hc
  have e2 := kc_floor_div (y := v.im) hc
  have r1 : (v - kcGrid m v).re = v.re - (⌊v.re * 2 ^ m⌋ : ℝ) / 2 ^ m := rfl
  have r2 : (v - kcGrid m v).im = v.im - (⌊v.im * 2 ^ m⌋ : ℝ) / 2 ^ m := rfl
  rw [r1, r2, inv_pow]
  linarith

lemma kcGrid_finite (m : ℕ) : (kcGrid m '' dzzV).Finite := by
  refine (((Set.finite_Icc (0 : ℤ) (2 ^ m)).prod (Set.finite_Icc (0 : ℤ) (2 ^ m))).image
    (fun p : ℤ × ℤ => (⟨(p.1 : ℝ) / 2 ^ m, (p.2 : ℝ) / 2 ^ m⟩ : ℂ))).subset ?_
  rintro _ ⟨v, ⟨h1, h2, h3, h4⟩, rfl⟩
  have hc : (0 : ℝ) < 2 ^ m := by positivity
  obtain ⟨a1, b1⟩ := kc_floor_bounds hc h1 h2
  obtain ⟨a2, b2⟩ := kc_floor_bounds hc h3 h4
  refine ⟨(⌊v.re * 2 ^ m⌋, ⌊v.im * 2 ^ m⌋), ⟨⟨a1, ?_⟩, ⟨a2, ?_⟩⟩, rfl⟩
  · exact_mod_cast b1
  · exact_mod_cast b2

/-! ### The bad events of one scale -/

lemma kc_measurable_tildeHInf (hW : IsWhiteNoise P W) (ε : ℝ) (v : ℂ) :
    Measurable (tildeHInf W ε v) :=
  (hW.measurable _).const_mul _

/-- Two rational points of `𝕍` at distance `≤ 2·2^{-m}` with `h̃_ε`-increment `> 1/2`. -/
def kcBad (W : WNSpace → Ω → ℝ) (ε : ℝ) (m : ℕ) : Set Ω :=
  ⋃ (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ), {ω | (⟨a, b⟩ : ℂ) ∈ dzzV ∧ (⟨c, d⟩ : ℂ) ∈ dzzV ∧
    dist (⟨a, b⟩ : ℂ) ⟨c, d⟩ ≤ 2 * (2 : ℝ)⁻¹ ^ m ∧
    1 / 2 < |tildeHInf W ε ⟨a, b⟩ ω - tildeHInf W ε ⟨c, d⟩ ω|}

lemma kc_tendsto_bad (hW : IsWhiteNoise P W) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m => P (kcBad W ε m)) atTop (𝓝 0) := by
  have := hW.isProbabilityMeasure
  have hmeas : ∀ m, MeasurableSet (kcBad W ε m) := fun m => by
    unfold kcBad
    refine MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
      MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun d => ?_
    simp only [setOf_and]
    refine (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      ((MeasurableSet.const _).inter ?_))
    exact measurableSet_lt measurable_const
      (continuous_abs.measurable.comp
        ((kc_measurable_tildeHInf hW ε _).sub (kc_measurable_tildeHInf hW ε _)))
  have hanti : Antitone (kcBad W ε) := fun m m' hmm' => by
    unfold kcBad
    refine iUnion_mono fun a => iUnion_mono fun b => iUnion_mono fun c => iUnion_mono fun d => ?_
    rintro ω ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmm') (by norm_num)), h4⟩
  have h := tendsto_measure_iInter_atTop (μ := P) (fun m => (hmeas m).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  obtain ⟨Y, hYc, -, hY⟩ := exists_continuous_tildeHInf hW hε
  have hnull : P (⋂ m, kcBad W ε m) = 0 := by
    refine measure_mono_null (t := ⋃ (a : ℚ) (b : ℚ),
      {ω | Y ⟨a, b⟩ ω ≠ tildeHInf W ε ⟨a, b⟩ ω}) ?_ ?_
    · intro ω hω
      by_contra hN
      simp only [mem_iUnion, mem_setOf_eq, not_exists, not_not] at hN
      obtain ⟨η, hη, hU⟩ := Metric.uniformContinuousOn_iff.1
        (kc_isCompact_dzzV.uniformContinuousOn_of_continuous (hYc ω).continuousOn) (1 / 2)
        (by norm_num)
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (half_pos hη) (by norm_num : (2 : ℝ)⁻¹ < 1)
      have hω' := mem_iInter.1 hω m
      simp only [kcBad, mem_iUnion, mem_setOf_eq] at hω'
      obtain ⟨a, b, c, d, h1, h2, h3, h4⟩ := hω'
      have := hU _ h1 _ h2 (by linarith)
      rw [Real.dist_eq, hN a b, hN c d] at this
      linarith
    · exact measure_iUnion_null fun a => measure_iUnion_null fun b => ae_iff.1 (hY _)
  rw [hnull] at h
  exact h

lemma kc_ev_bad (hW : IsWhiteNoise P W) {ε : ℝ} (hε : 0 < ε) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ m in atTop, P.real (kcBad W ε m) ≤ η := by
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (kc_tendsto_bad hW hε) (ENNReal.ofReal η)
    (by simpa using hη)] with m hm
  exact ENNReal.toReal_le_of_le_ofReal hη.le hm

/-! ### The main result -/

/-- The grid projection of a coarse point (same scale). -/
def kcProj {κ δ : ℝ} (m : ℕ) (q : CoarsePt κ δ) : CoarsePt κ δ :=
  ⟨(kcGrid m q.1.1, q.1.2), kcGrid_mem m q.2.1, kcGrid_rat m q.1.1, q.2.2.2⟩

/-- **`DZZCoarseReg`** (DEC-124 packet I4): the coarse field `𝒳_δ` has, outside an event of
probability `≤ ε`, a finite `1`-net. -/
theorem dzzCoarseReg (hW : IsWhiteNoise P W) (γ : ℝ) : DZZCoarseReg P γ W := by
  intro δ hδ η hη
  have := hW.isProbabilityMeasure
  have hS := kc_finite_coarseScale (κ := dzzCmc γ) hδ.1
  have hev : ∀ᶠ m in atTop, ∀ ε ∈ hS.toFinset,
      P.real (kcBad W ε m) ≤ η / (hS.toFinset.card + 1) := by
    rw [Filter.eventually_all_finset]
    intro ε hε
    exact kc_ev_bad hW (kc_pos_of_coarseScale hδ.1 ((Set.Finite.mem_toFinset hS).1 hε))
      (by positivity)
  obtain ⟨M, hM⟩ := hev.exists
  refine ⟨{x | ∀ q : CoarsePt (dzzCmc γ) δ,
    |x (Sum.inr q) - x (Sum.inr (kcProj M q))| ≤ 1 / 2}, ?_, ?_⟩
  · have hsub : {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ {x : CoarseIdx (dzzCmc γ) δ → ℝ |
        ∀ q : CoarsePt (dzzCmc γ) δ, |x (Sum.inr q) - x (Sum.inr (kcProj M q))| ≤ 1 / 2}} ⊆
        ⋃ ε ∈ hS.toFinset, kcBad W ε M := by
      intro ω hω
      simp only [mem_setOf_eq, not_forall, not_le] at hω
      obtain ⟨q, hq⟩ := hω
      obtain ⟨a, b, hab⟩ := q.2.2.1
      obtain ⟨c, d, hcd⟩ := kcGrid_rat M q.1.1
      simp only [mem_iUnion]
      refine ⟨q.1.2, (Set.Finite.mem_toFinset hS).2 q.2.2.2, ?_⟩
      simp only [kcBad, mem_iUnion, mem_setOf_eq]
      refine ⟨a, b, c, d, ?_, ?_, ?_, ?_⟩
      · rw [← hab]; exact q.2.1
      · rw [← hcd]; exact kcGrid_mem M q.2.1
      · rw [← hab, ← hcd]; exact kcGrid_dist M q.1.1
      · rw [← hab, ← hcd]; exact hq
    calc P.real _ ≤ P.real (⋃ ε ∈ hS.toFinset, kcBad W ε M) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ ε ∈ hS.toFinset, P.real (kcBad W ε M) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _ε ∈ hS.toFinset, η / (hS.toFinset.card + 1) := Finset.sum_le_sum hM
      _ ≤ η := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
  · have hQ : {q : CoarsePt (dzzCmc γ) δ | q.1.1 ∈ kcGrid M '' dzzV}.Finite :=
      (((kcGrid_finite M).prod hS).preimage Subtype.val_injective.injOn).subset
        fun q hq => ⟨hq, q.2.2.2⟩
    have := kc_finite_boxes (κ := dzzCmc γ) hδ.1
    have hF : (Set.range (Sum.inl : {b : DyBox // δ ^ dzzCmc γ ≤ b.side} →
        CoarseIdx (dzzCmc γ) δ) ∪ Sum.inr '' {q | q.1.1 ∈ kcGrid M '' dzzV}).Finite :=
      (Set.finite_range _).union (hQ.image _)
    have := hF.to_subtype
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ↥(Set.range (Sum.inl : {b : DyBox //
      δ ^ dzzCmc γ ≤ b.side} → CoarseIdx (dzzCmc γ) δ) ∪
        Sum.inr '' {q : CoarsePt (dzzCmc γ) δ | q.1.1 ∈ kcGrid M '' dzzV})
    refine ⟨n, fun i => (e.symm i).1, fun x hx x' hx' s => ?_⟩
    rcases s with b | q
    · refine ⟨e ⟨Sum.inl b, Set.mem_union_left _ ⟨b, rfl⟩⟩, ?_⟩
      simp only [Equiv.symm_apply_apply]
      linarith
    · refine ⟨e ⟨Sum.inr (kcProj M q),
        Set.mem_union_right _ ⟨kcProj M q, ⟨q.1.1, q.2.1, rfl⟩, rfl⟩⟩, ?_⟩
      simp only [Equiv.symm_apply_apply]
      have h1 := abs_le.1 (hx q)
      have h2 := abs_le.1 (hx' q)
      have h3 := le_abs_self (x (Sum.inr (kcProj M q)) - x' (Sum.inr (kcProj M q)))
      have h4 := neg_abs_le (x (Sum.inr (kcProj M q)) - x' (Sum.inr (kcProj M q)))
      exact abs_le.2 ⟨by linarith, by linarith⟩

end DZZ
end LQGMetric
