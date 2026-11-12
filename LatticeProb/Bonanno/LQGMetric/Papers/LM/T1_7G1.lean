/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7G1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7D1

/-!
# LM Lemma 5.2 and (5.2) for a fixed path (packet P-GRID of DEC-107, first part)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), l. 933–953: the randomly shifted grid `ε𝒢_θ` (`θ` uniform on
`[0,1]²`), Lemma 5.2 (`lem-random-grid`, l. 937–946) and (5.2) (`eqn-geodesic-grid`, l. 950–953).

LM's proof of Lemma 5.2 (l. 944–946): "for each fixed `t`, `P[P(t) ∈ ε𝒢_θ | P] = 0` since `P` is
independent from `θ`. Hence a.s. the Lebesgue measure of `P⁻¹(ε𝒢_θ)` is zero." We formalize it
for a fixed (deterministic, measurable) curve `P` and an arbitrary s-finite measure `μ` on the time
line (e.g. Lebesgue measure on `[0, len(P)]` for `P` parametrized by length, or the length
measure of `P`): `t17_grid_null` — for Lebesgue-a.e. `θ`, `μ{t : P t ∈ ε𝒢_θ} = 0` (Tonelli,
`Measure.measure_prod_null`). The random-path version is then Tonelli over `(h, D)` as in
DEC-107 §1.3.

(5.2) in measure form (`t17_sum_pieces`): if the time set of the grid is `μ`-null and the open grid
squares `S` (`t17Square`, pairwise disjoint, `t17Square_disjoint`, covering `ℂ ∖ ε𝒢_θ`,
`t17_mem_square`) are finitely many on the range of `P`, then
`μ(T) = ∑_S μ(T ∩ P⁻¹ S)`, i.e. `len(P; D) = ∑_S len(P ∩ S; D)` when lengths of pieces are measured
by the length measure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.LM

/-- the grid `ε𝒢_θ`: the lines `Re x ∈ ε(ℤ + θ₁)` and `Im x ∈ ε(ℤ + θ₂)` -/
def t17Grid (ε : ℝ) (θ : ℝ × ℝ) : Set ℂ :=
  {x | ∃ k : ℤ, x.re = ε * (k + θ.1)} ∪ {x | ∃ k : ℤ, x.im = ε * (k + θ.2)}

/-- for fixed `x`, the set of shifts `θ` with `x ∈ ε𝒢_θ` is Lebesgue-null -/
theorem t17_volume_grid_shift (ε : ℝ) (hε : 0 < ε) (x : ℂ) :
    (volume : Measure (ℝ × ℝ)) {θ | x ∈ t17Grid ε θ} = 0 := by
  have hsub : {θ : ℝ × ℝ | x ∈ t17Grid ε θ} ⊆
      (⋃ k : ℤ, ({x.re / ε - k} : Set ℝ) ×ˢ (univ : Set ℝ)) ∪
        ⋃ k : ℤ, (univ : Set ℝ) ×ˢ ({x.im / ε - k} : Set ℝ) := by
    rintro θ (⟨k, hk⟩ | ⟨k, hk⟩)
    · refine Or.inl (mem_iUnion.2 ⟨k, ?_, mem_univ _⟩)
      simp only [mem_singleton_iff]
      field_simp
      linarith
    · refine Or.inr (mem_iUnion.2 ⟨k, mem_univ _, ?_⟩)
      simp only [mem_singleton_iff]
      field_simp
      linarith
  refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun k => ?_)
    (measure_iUnion_null fun k => ?_))
  · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

lemma t17_measurableSet_grid (ε : ℝ) {P : ℝ → ℂ} (hP : Measurable P) :
    MeasurableSet {p : ℝ × (ℝ × ℝ) | P p.1 ∈ t17Grid ε p.2} := by
  have h1 : {p : ℝ × (ℝ × ℝ) | P p.1 ∈ t17Grid ε p.2} =
      (⋃ k : ℤ, {p : ℝ × (ℝ × ℝ) | (P p.1).re = ε * (k + p.2.1)}) ∪
        ⋃ k : ℤ, {p : ℝ × (ℝ × ℝ) | (P p.1).im = ε * (k + p.2.2)} := by
    ext p; simp [t17Grid]
  rw [h1]
  exact (MeasurableSet.iUnion fun k => measurableSet_eq_fun
      (Complex.measurable_re.comp (hP.comp measurable_fst))
      (measurable_const.mul (measurable_const.add (measurable_fst.comp measurable_snd)))).union
    (MeasurableSet.iUnion fun k => measurableSet_eq_fun
      (Complex.measurable_im.comp (hP.comp measurable_fst))
      (measurable_const.mul (measurable_const.add (measurable_snd.comp measurable_snd))))

/-- **LM Lemma 5.2** (`lem-random-grid`, l. 937–946), fixed curve: for a measurable curve `P` and
an s-finite measure `μ` on times, for Lebesgue-a.e. shift `θ`, the times at which `P` is on the
grid `ε𝒢_θ` form a `μ`-null set. -/
theorem t17_grid_null {ε : ℝ} (hε : 0 < ε) {P : ℝ → ℂ} (hP : Measurable P) (μ : Measure ℝ)
    [SFinite μ] : ∀ᵐ θ ∂(volume : Measure (ℝ × ℝ)), μ {t | P t ∈ t17Grid ε θ} = 0 := by
  have hE := t17_measurableSet_grid ε hP
  have h1 : (μ.prod (volume : Measure (ℝ × ℝ))) {p | P p.1 ∈ t17Grid ε p.2} = 0 :=
    (Measure.measure_prod_null hE).2 (Eventually.of_forall fun t =>
      t17_volume_grid_shift ε hε (P t))
  have hE' : MeasurableSet (Prod.swap ⁻¹' {p : ℝ × (ℝ × ℝ) | P p.1 ∈ t17Grid ε p.2}) :=
    measurable_swap hE
  have h2 : ((volume : Measure (ℝ × ℝ)).prod μ)
      (Prod.swap ⁻¹' {p : ℝ × (ℝ × ℝ) | P p.1 ∈ t17Grid ε p.2}) = 0 := by
    rw [← Measure.map_apply measurable_swap hE, Measure.prod_swap, h1]
  have h3 := (Measure.measure_prod_null hE').1 h2
  filter_upwards [h3] with θ hθ
  exact hθ

/-! ## The grid squares and (5.2) -/

/-- the open grid square of index `k` -/
def t17Square (ε : ℝ) (θ : ℝ × ℝ) (k : ℤ × ℤ) : Set ℂ :=
  {x | ε * (k.1 + θ.1) < x.re ∧ x.re < ε * (k.1 + 1 + θ.1) ∧
    ε * (k.2 + θ.2) < x.im ∧ x.im < ε * (k.2 + 1 + θ.2)}

lemma t17_isOpen_square (ε : ℝ) (θ : ℝ × ℝ) (k : ℤ × ℤ) : IsOpen (t17Square ε θ k) := by
  unfold t17Square
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)))

lemma t17_square_index {ε c a : ℝ} (hε : 0 < ε) {k : ℤ} (h1 : ε * (k + c) < a)
    (h2 : a < ε * (k + 1 + c)) : k = ⌊a / ε - c⌋ := by
  rw [eq_comm, Int.floor_eq_iff]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hε]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hε]; nlinarith

/-- distinct grid squares are disjoint -/
theorem t17Square_disjoint {ε : ℝ} (hε : 0 < ε) (θ : ℝ × ℝ) {k l : ℤ × ℤ} (hkl : k ≠ l) :
    Disjoint (t17Square ε θ k) (t17Square ε θ l) := by
  refine Set.disjoint_left.2 fun x hk hl => hkl ?_
  obtain ⟨a1, a2, a3, a4⟩ := hk
  obtain ⟨b1, b2, b3, b4⟩ := hl
  exact Prod.ext ((t17_square_index hε a1 a2).trans (t17_square_index hε b1 b2).symm)
    ((t17_square_index hε a3 a4).trans (t17_square_index hε b3 b4).symm)

/-- the index of the square containing `x` -/
def t17Idx (ε : ℝ) (θ : ℝ × ℝ) (x : ℂ) : ℤ × ℤ := (⌊x.re / ε - θ.1⌋, ⌊x.im / ε - θ.2⌋)

/-- every point off the grid lies in the square `t17Idx` -/
theorem t17_mem_square {ε : ℝ} (hε : 0 < ε) (θ : ℝ × ℝ) {x : ℂ} (hx : x ∉ t17Grid ε θ) :
    x ∈ t17Square ε θ (t17Idx ε θ x) := by
  simp only [t17Grid, mem_union, Set.mem_ofPred_eq, not_or, not_exists] at hx
  have key : ∀ (a c : ℝ), (∀ k : ℤ, ¬ a = ε * (k + c)) →
      ε * (⌊a / ε - c⌋ + c) < a ∧ a < ε * (⌊a / ε - c⌋ + 1 + c) := by
    intro a c hne
    have h1 := Int.floor_le (a / ε - c)
    have h2 := Int.lt_floor_add_one (a / ε - c)
    have e : a = ε * (a / ε - c + c) := by field_simp; ring
    constructor
    · refine lt_of_le_of_ne ?_ (fun h => hne _ h.symm)
      calc ε * (⌊a / ε - c⌋ + c) ≤ ε * (a / ε - c + c) :=
            mul_le_mul_of_nonneg_left (by linarith) hε.le
        _ = a := e.symm
    · calc a = ε * (a / ε - c + c) := e
        _ < ε * (⌊a / ε - c⌋ + 1 + c) := mul_lt_mul_of_pos_left (by linarith) hε
  obtain ⟨r1, r2⟩ := key x.re θ.1 hx.1
  obtain ⟨i1, i2⟩ := key x.im θ.2 hx.2
  exact ⟨r1, r2, i1, i2⟩

lemma t17_floor_mem {ε R a c : ℝ} (hε : 0 < ε) (hc : c ∈ Icc (0 : ℝ) 1) (ha : |a| ≤ R) :
    ⌊a / ε - c⌋ ∈ Finset.Icc (-(⌈R / ε⌉ + 1)) (⌈R / ε⌉ + 1) := by
  have hR : |a| / ε ≤ R / ε := div_le_div_of_nonneg_right ha hε.le
  have h1 : a / ε ≤ R / ε := (div_le_div_of_nonneg_right (le_abs_self a) hε.le).trans hR
  have h2 : -(R / ε) ≤ a / ε := by
    rw [neg_le, ← neg_div]; exact (div_le_div_of_nonneg_right (neg_le_abs a) hε.le).trans hR
  have f1 := Int.floor_le (a / ε - c)
  have f2 := Int.lt_floor_add_one (a / ε - c)
  have c1 := Int.le_ceil (R / ε)
  rw [Finset.mem_Icc]
  constructor
  · have : (-(⌈R / ε⌉ + 1) : ℝ) < ⌊a / ε - c⌋ + 1 := by linarith [hc.2]
    exact_mod_cast Int.lt_add_one_iff.1 (by exact_mod_cast this)
  · have : (⌊a / ε - c⌋ : ℝ) ≤ ⌈R / ε⌉ + 1 := by linarith [hc.1]
    exact_mod_cast this

/-- **finitely many squares meet `cl B_R`**: for `θ ∈ [0,1]²` and `‖x‖ ≤ R`, the index of the
square containing `x` lies in `[-N, N]²`, `N = ⌈R/ε⌉ + 1` -/
theorem t17_idx_mem {ε R : ℝ} (hε : 0 < ε) {θ : ℝ × ℝ} (hθ1 : θ.1 ∈ Icc (0 : ℝ) 1)
    (hθ2 : θ.2 ∈ Icc (0 : ℝ) 1) {x : ℂ} (hx : ‖x‖ ≤ R) :
    t17Idx ε θ x ∈ Finset.Icc (-(⌈R / ε⌉ + 1)) (⌈R / ε⌉ + 1) ×ˢ
      Finset.Icc (-(⌈R / ε⌉ + 1)) (⌈R / ε⌉ + 1) :=
  Finset.mem_product.2 ⟨t17_floor_mem hε hθ1 ((Complex.abs_re_le_norm x).trans hx),
    t17_floor_mem hε hθ2 ((Complex.abs_im_le_norm x).trans hx)⟩

/-- **LM (5.2)** (`eqn-geodesic-grid`, l. 950–953), measure form: if the grid time set is
`μ`-null, then `μ(T) = ∑_S μ(T ∩ P⁻¹ S)` over a finite set of pairwise disjoint pieces covering the
off-grid part of `P(T)`. -/
theorem t17_sum_pieces {μ : Measure ℝ} {T : Set ℝ} (hT : MeasurableSet T) {P : ℝ → ℂ}
    (hP : Measurable P) {G : Set ℂ} {ι : Type*} (s : Finset ι) (S : ι → Set ℂ)
    (hS : ∀ i, MeasurableSet (S i)) (hdisj : (s : Set ι).PairwiseDisjoint S)
    (hcover : ∀ t ∈ T, P t ∉ G → ∃ i ∈ s, P t ∈ S i) (hnull : μ (T ∩ P ⁻¹' G) = 0) :
    μ T = ∑ i ∈ s, μ (T ∩ P ⁻¹' S i) := by
  have hU : ∑ i ∈ s, μ (T ∩ P ⁻¹' S i) = μ (⋃ i ∈ s, T ∩ P ⁻¹' S i) :=
    (measure_biUnion_finset (fun i hi j hj hij => by
      exact Disjoint.mono inter_subset_right inter_subset_right
        ((hdisj hi hj hij).preimage P)) fun i _ => hT.inter (hP (hS i))).symm
  rw [hU]
  refine le_antisymm ?_ (measure_mono (iUnion₂_subset fun i _ => inter_subset_left))
  calc μ T ≤ μ ((T ∩ P ⁻¹' G) ∪ ⋃ i ∈ s, T ∩ P ⁻¹' S i) := measure_mono fun t ht => by
        by_cases hG : P t ∈ G
        · exact Or.inl ⟨ht, hG⟩
        · obtain ⟨i, hi, hti⟩ := hcover t ht hG
          exact Or.inr (mem_iUnion₂.2 ⟨i, hi, ht, hti⟩)
    _ ≤ μ (T ∩ P ⁻¹' G) + μ (⋃ i ∈ s, T ∩ P ⁻¹' S i) := measure_union_le _ _
    _ = μ (⋃ i ∈ s, T ∩ P ⁻¹' S i) := by rw [hnull, zero_add]

end LQGMetric.LM
