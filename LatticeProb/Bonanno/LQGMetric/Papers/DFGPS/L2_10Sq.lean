/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_10Sq at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_10Prok
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8ProofMeas
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.10, first step on the unit square (T:953–957)

The open sets `sqG C R ⊂ C(S_1(0) × S_1(0), ℝ)`: "`d < a` on `S_{1/(R+2)}(0)²` and `d > C a` on
`S_{1/(R+2)}(0) × ∂S_1(0)` for some `a`". Every continuous metric on `S_1(0)` lies in some
`sqG C R` (continuity at `(0,0)` and compactness), so `exists_eventually_measure_ge` with
`Lem2_8` (applied to `S_1(0)`, as DFGPS T:953 do) gives `lem2_10_unit`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry

theorem mem_sqC_iff {s : ℝ} {x : ℂ} :
    x ∈ sqC s 0 ↔ -(s / 2) ≤ x.re ∧ x.re ≤ s / 2 ∧ -(s / 2) ≤ x.im ∧ x.im ≤ s / 2 := by
  simp only [sqC, closedSq, mem_ofPred_eq, zero_sub, Complex.neg_re, Complex.neg_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem sqC_mono {s s' : ℝ} (hss : s ≤ s') : sqC s 0 ⊆ sqC s' 0 := by
  intro x hx
  rw [mem_sqC_iff] at hx ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem norm_le_of_mem_sqC {s : ℝ} {x : ℂ} (hx : x ∈ sqC s 0) : ‖x‖ ≤ s := by
  rw [mem_sqC_iff] at hx
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have := Complex.norm_le_abs_re_add_abs_im x
  have a1 : |x.re| ≤ s / 2 := abs_le.2 ⟨h1, h2⟩
  have a2 : |x.im| ≤ s / 2 := abs_le.2 ⟨h3, h4⟩
  linarith

theorem isCompact_sqC {s : ℝ} (hs : 0 ≤ s) : IsCompact (sqC s 0) := isCompact_closedSq _ hs

/-- points of `S_{1/2}(0)` are not on `∂S_1(0)` -/
theorem not_mem_frontier_of_mem_sqC_half {x : ℂ} (hx : x ∈ sqC (1 / 2) 0) :
    x ∉ frontier (sqC 1 0) := by
  rw [frontier, Set.mem_sdiff, not_and, not_not]
  intro _
  have hO : IsOpen {z : ℂ | -(1 / 2) < z.re ∧ z.re < 1 / 2 ∧ -(1 / 2) < z.im ∧ z.im < 1 / 2} := by
    refine (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)))
  refine interior_maximal (fun z hz => ?_) hO ?_
  · rw [mem_sqC_iff]; obtain ⟨h1, h2, h3, h4⟩ := hz
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rw [mem_sqC_iff] at hx; obtain ⟨h1, h2, h3, h4⟩ := hx
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- `S_1(0)` -/
abbrev sq1 : Set ℂ := sqC 1 0

theorem compactSpace_sq1 : CompactSpace sq1 := isCompact_iff_compactSpace.1 (isCompact_sqC zero_le_one)

/-- the inner side length `1/(R+2)` -/
def innSide (R : ℕ) : ℝ := 1 / ((R : ℝ) + 2)

theorem innSide_pos (R : ℕ) : 0 < innSide R := by unfold innSide; positivity

theorem innSide_le_half (R : ℕ) : innSide R ≤ 1 / 2 := by
  unfold innSide
  exact one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)])

theorem innSide_anti : Antitone innSide := fun m n hmn => by
  unfold innSide
  exact one_div_le_one_div_of_le (by positivity) (by linarith [(Nat.cast_le (α := ℝ)).2 hmn])

/-- pairs of points of `S_{1/(R+2)}(0)` -/
def innerPairs (R : ℕ) : Set (sq1 × sq1) := {x | x.1.1 ∈ sqC (innSide R) 0 ∧ x.2.1 ∈ sqC (innSide R) 0}

/-- pairs `(u, v) ∈ S_{1/(R+2)}(0) × ∂S_1(0)` -/
def crossPairs (R : ℕ) : Set (sq1 × sq1) :=
  {x | x.1.1 ∈ sqC (innSide R) 0 ∧ x.2.1 ∈ frontier (sqC 1 0)}

theorem isClosed_innerPairs (R : ℕ) : IsClosed (innerPairs R) :=
  ((isCompact_sqC (innSide_pos R).le).isClosed.preimage
      (continuous_subtype_val.comp continuous_fst)).inter
    ((isCompact_sqC (innSide_pos R).le).isClosed.preimage
      (continuous_subtype_val.comp continuous_snd))

theorem isClosed_crossPairs (R : ℕ) : IsClosed (crossPairs R) :=
  ((isCompact_sqC (innSide_pos R).le).isClosed.preimage
      (continuous_subtype_val.comp continuous_fst)).inter
    (isClosed_frontier.preimage (continuous_subtype_val.comp continuous_snd))

/-- the open event `sqG C R` -/
def sqG (C : ℝ) (R : ℕ) : Set C(sq1 × sq1, ℝ) :=
  {d | ∃ a : ℝ, MapsTo d (innerPairs R) (Iio a) ∧ MapsTo d (crossPairs R) (Ioi (C * a))}

theorem isOpen_sqG (C : ℝ) (R : ℕ) : IsOpen (sqG C R) := by
  have := compactSpace_sq1
  have : sqG C R = ⋃ a : ℝ, ({d : C(sq1 × sq1, ℝ) | MapsTo d (innerPairs R) (Iio a)} ∩
      {d : C(sq1 × sq1, ℝ) | MapsTo d (crossPairs R) (Ioi (C * a))}) := by
    ext d; simp [sqG]
  rw [this]
  exact isOpen_iUnion fun a =>
    (ContinuousMap.isOpen_setOfPred_mapsTo (isClosed_innerPairs R).isCompact isOpen_Iio).inter
      (ContinuousMap.isOpen_setOfPred_mapsTo (isClosed_crossPairs R).isCompact isOpen_Ioi)

theorem sqG_mono (C : ℝ) : Monotone (sqG C) := by
  intro m n hmn d ⟨a, h1, h2⟩
  refine ⟨a, fun x hx => h1 ⟨sqC_mono (innSide_anti hmn) hx.1, sqC_mono (innSide_anti hmn) hx.2⟩,
    fun x hx => h2 ⟨sqC_mono (innSide_anti hmn) hx.1, hx.2⟩⟩

/-- every continuous metric on `S_1(0)` lies in some `sqG C R` -/
theorem mem_iUnion_sqG {C : ℝ} (hC : 0 < C) (d : C(sq1 × sq1, ℝ)) (hd : IsMetricFun ⇑d) :
    d ∈ ⋃ R, sqG C R := by
  have := compactSpace_sq1
  -- a positive lower bound `m` of `d` on `S_{1/2}(0) × ∂S_1(0)`
  set A0 : Set (sq1 × sq1) := {x | x.1.1 ∈ sqC (1 / 2) 0 ∧ x.2.1 ∈ frontier (sqC 1 0)}
  have hA0 : IsCompact A0 :=
    (((isCompact_sqC (by norm_num)).isClosed.preimage
      (continuous_subtype_val.comp continuous_fst)).inter
      (isClosed_frontier.preimage (continuous_subtype_val.comp continuous_snd))).isCompact
  have hpos : ∀ x ∈ A0, 0 < d x := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hne : u ≠ v := fun e => not_mem_frontier_of_mem_sqC_half hu (e ▸ hv)
    have h0 : 0 ≤ d (u, v) := by
      have := hd.triangle u v u; rw [hd.self_eq_zero, hd.symm v u] at this; linarith
    exact lt_of_le_of_ne h0 fun e => hne (hd.eq_of_eq_zero u v e.symm)
  obtain ⟨m, hm, hmA⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ A0, m ≤ d x := by
    rcases A0.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun x hx => by rw [he] at hx; exact absurd hx (notMem_empty x)⟩
    · obtain ⟨x0, hx0, hmin⟩ := hA0.exists_isMinOn hne d.continuous.continuousOn
      exact ⟨d x0, hpos x0 hx0, fun x hx => hmin hx⟩
  set a := m / (2 * C)
  have ha : 0 < a := by positivity
  have hCa : C * a < m := by
    have : C * a = m / 2 := by simp only [a]; field_simp
    linarith
  -- continuity of `d` at `(0, 0)`
  have h00 : (0 : ℂ) ∈ sq1 := by rw [mem_sqC_iff]; norm_num
  set o : sq1 × sq1 := (⟨0, h00⟩, ⟨0, h00⟩)
  obtain ⟨δ, hδ, hδd⟩ := Metric.continuousAt_iff.1 d.continuous.continuousAt a ha
  obtain ⟨R, hR⟩ := exists_nat_one_div_lt hδ
  refine mem_iUnion.2 ⟨R, a, fun x hx => ?_, fun x hx => ?_⟩
  · have hdist : dist x o < δ := by
      rw [Prod.dist_eq, max_lt_iff, Subtype.dist_eq, Subtype.dist_eq, dist_zero_right,
        dist_zero_right]
      have hs : innSide R < δ := by
        unfold innSide
        exact lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by linarith)) hR
      exact ⟨(norm_le_of_mem_sqC hx.1).trans_lt hs, (norm_le_of_mem_sqC hx.2).trans_lt hs⟩
    have := hδd hdist
    rw [Real.dist_eq, show d o = 0 from hd.self_eq_zero _, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  · exact hCa.trans_le (hmA x ⟨sqC_mono (innSide_le_half R) hx.1, hx.2⟩)

/-- **DFGPS T:953–957** (first display of the proof of Lemma 2.10, on `S_1(0)` and for the
internal metric): for `p < 1` there is `R` with `P[𝔞_ε⁻¹ D_h^ε(·,·;S_1(0)) ∈ sqG C R] ≥ p` for all
small `ε`. From `Lem2_8` (tightness and limits are metrics) and `exists_eventually_measure_ge`. -/
theorem lem2_10_unit (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsGFFPlusBddCont h P) {C : ℝ} (hC : 0 < C) {p : ℝ} (hp : p < 1) :
    ∃ R : ℕ, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal p ≤ P {ω | lfppSqC (xiGamma γ) ε (h ω) sq1 ∈ sqG C R} := by
  obtain ⟨-, hT, hlim⟩ := h28 γ hγ hγ2 (0 - ((1 / 2 : ℝ) : ℂ) * (1 + Complex.I)) 1 one_pos P h hh
  have hae : ∀ ε ∈ Ioo (0 : ℝ) 1,
      AEMeasurable (fun ω => lfppSqC (xiGamma γ) ε (h ω) sq1) P := fun ε hε =>
    aemeasurable_lfppSqC hh.1
      ((hh.ae_tendstoLocallyUniformly_heatMollify ε hε.1.ne').mono fun ω hω => hω.2) one_pos
  have hlim' : ∀ (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(sq1 × sq1, ℝ))
      (μ : ProbabilityMeasure C(sq1 × sq1, ℝ)),
      (∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧ (ν n : Measure C(sq1 × sq1, ℝ)) =
        P.map fun ω => lfppSqC (xiGamma γ) (εn n) (h ω) sq1) →
      Tendsto εn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) →
      (μ : Measure C(sq1 × sq1, ℝ)) (⋃ R, sqG C R) = 1 := by
    intro εn ν μ hν h0 hc
    have hl : ∀ᵐ d ∂(μ : Measure C(sq1 × sq1, ℝ)), IsSqLengthMetric d := hlim εn ν μ hν h0 hc
    rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion fun R => (isOpen_sqG C R).measurableSet)]
    exact measure_mono_null (fun d hd (hl' : IsSqLengthMetric d) => hd (mem_iUnion_sqG hC d hl'.1))
      (ae_iff.1 hl)
  obtain ⟨R, hR⟩ := @exists_eventually_measure_ge C(sq1 × sq1, ℝ) _
    (by have := compactSpace_sq1; exact polishSpace_continuousMap _ _) _ ⟨rfl⟩
    (fun ε => P.map fun ω => lfppSqC (xiGamma γ) ε (h ω) sq1)
    (fun ε hε => (Measure.isProbabilityMeasure_map_iff (hae ε hε)).2 inferInstance) hT _
    (isOpen_sqG C) (sqG_mono C) hlim' _ hp
  refine ⟨R, ?_⟩
  filter_upwards [hR, Ioo_mem_nhdsGT one_pos] with ε hε hε1
  rwa [Measure.map_apply_of_aemeasurable (hae ε hε1) (isOpen_sqG C R).measurableSet] at hε

end LQGMetric.DFGPS
