/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54G0 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D123

/-!
# D123: the leg concentration `DZZProp317Leg` from walled P3.17 at the five leg walls (P-54LEG)

Decision DEC-123 §2 (packet P-54LEG); DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) proof of
Lemma 5.4, l. 2571–2578, where (eq-concentration-1) is applied to `min_{x ∈ L} D(u, x)` for the
segments `L ⊆ ∂𝕍_{u,λ}` (walled form, DZZ Remark 5.2). The wall `legWall u λ (L δ)` moves with
`δ`, but takes only five values (`legWalls u`, S5D123), so the walled P3.17 at each of the five
fixed walls (`DZZProp317In`, pairs inside `K^ξ`) gives the leg statement: for a wall `K` apply
it to `A δ = {u}` and `B δ = L δ` when `legWall u λ (L δ) = K`, `B δ = {m_K}` otherwise (a fixed
point of `∂𝕍_{u,λ}` deep inside `K`), and take the minimum of the five constants.

* `legSq_subset_tildeBox`: `legSq u l j ⊆ 𝕍̃_{u, u + l e_j}` (DEC-123 §4, P-54LEG);
* **`dzzProp317Leg_of_In`**: the statement of DEC-123 §2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- Points at sup-distance `≤ l/2 − ξ` from the centre of `𝕍_{c,l}` lie in `(𝕍_{c,l})^ξ`. -/
lemma mem_kXi_sqBox {c z : ℂ} {l ξ : ℝ} (hre : |z.re - c.re| ≤ l / 2 - ξ)
    (him : |z.im - c.im| ≤ l / 2 - ξ) : z ∈ kXi (sqBox c l) ξ := by
  have hne : (sqBox c l)ᶜ.Nonempty := by
    refine ⟨c + ((|l| + 1 : ℝ) : ℂ), fun h => ?_⟩
    have h1 := h.1
    rw [show (c + ((|l| + 1 : ℝ) : ℂ)).re - c.re = |l| + 1 by simp,
      abs_of_pos (by positivity)] at h1
    linarith [le_abs_self l, abs_nonneg l]
  refine (le_infDist hne).2 fun y hy => ?_
  rw [mem_compl_iff] at hy
  rw [dist_eq_norm]
  by_contra hlt
  push Not at hlt
  apply hy
  have h1 := Complex.abs_re_le_norm (z - y)
  have h2 := Complex.abs_im_le_norm (z - y)
  rw [Complex.sub_re] at h1
  rw [Complex.sub_im] at h2
  rw [abs_le] at hre him h1 h2
  exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

lemma sqSide_subset_frontier (u : ℂ) {l : ℝ} (hl : 0 < l) (j : Fin 4) :
    sqSide u l j ⊆ frontier (sqBox u l) := by
  rw [frontier_sqBox hl]
  intro z hz
  fin_cases j <;> simp only [sqSide, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at hz <;> simp only [mem_union] <;> tauto

lemma frontier_legBox_subset_sqBox (u : ℂ) : frontier (sqBox u (1 / 20)) ⊆ sqBox u (1 / 20) :=
  (isClosed_sqBox u _).frontier_subset

lemma mem_dzzVXi_of_mem_legBox {u z : ℂ} {ξ : ℝ} (hu : u ∈ dzzVbar) (hz : z ∈ sqBox u (1 / 20))
    (hξ : 0 ≤ ξ) (hξ' : ξ ≤ 1 / 40) : z ∈ dzzVXi ξ := by
  obtain ⟨h1, h2⟩ := near_of_mem_dzzVbar hu
  obtain ⟨h3, h4⟩ := hz
  rw [abs_le] at h1 h2 h3 h4
  refine mem_dzzVXi_of_near (a := 1 / 20) ?_ ?_ (by linarith) hξ <;>
    rw [abs_le] <;> constructor <;> linarith

/-- A segment of `∂𝕍_{u,λ}` lies in `(legWall u λ L)^ξ` for `ξ ≤ 1/40` (`λ = 1/20`). -/
lemma subset_kXi_legWall {u : ℂ} {ξ : ℝ} (hξ' : ξ ≤ 1 / 40) {L : Set ℂ}
    (hL : L ⊆ frontier (sqBox u (1 / 20))) : L ⊆ kXi (legWall u (1 / 20) L) ξ := by
  rcases legWall_eq_or u (1 / 20) L with h | ⟨j, hj, h⟩ <;> rw [h] <;> intro z hz
  · obtain ⟨h1, h2⟩ := frontier_legBox_subset_sqBox u (hL hz)
    exact mem_kXi_sqBox (by linarith) (by linarith)
  · have hz' := hj hz
    fin_cases j <;> simp only [sqSide, legSq, legDir, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] at hz' ⊢ <;> rw [Complex.mem_reProdIm] at hz' <;>
      simp only [mem_Icc, mem_singleton_iff] at hz' <;>
      refine mem_kXi_sqBox ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
        Complex.I_im, Complex.one_re, Complex.one_im] <;>
      rw [abs_le] <;> constructor <;> nlinarith [hz'.1, hz'.2]

lemma mem_kXi_of_mem_legWalls {u : ℂ} {ξ : ℝ} (hξ' : ξ ≤ 1 / 40) {K : Set ℂ}
    (hK : K ∈ legWalls u) : u ∈ kXi K ξ := by
  rcases hK with rfl | ⟨j, rfl⟩
  · exact mem_kXi_sqBox (by simp; linarith) (by simp; linarith)
  · fin_cases j <;> simp only [legSq, legDir, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] <;>
      refine mem_kXi_sqBox ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
        Complex.I_im, Complex.one_re, Complex.one_im] <;>
      rw [abs_le] <;> constructor <;> nlinarith

/-- Every leg wall contains a point of `∂𝕍_{u,λ}` deep inside it. -/
lemma exists_frontier_mem_kXi {u : ℂ} {ξ : ℝ} (hξ' : ξ ≤ 1 / 40) {K : Set ℂ}
    (hK : K ∈ legWalls u) : ∃ m ∈ frontier (sqBox u (1 / 20)), m ∈ kXi K ξ := by
  rcases hK with rfl | ⟨j, rfl⟩
  · refine ⟨⟨u.re, u.im - 1 / 40⟩, sqSide_subset_frontier u (by norm_num) 0 ?_, ?_⟩
    · show (⟨u.re, u.im - 1 / 40⟩ : ℂ) ∈
        Icc (u.re - 1 / 20 / 2) (u.re + 1 / 20 / 2) ×ℂ {u.im - 1 / 20 / 2}
      rw [Complex.mem_reProdIm]
      simp only [mem_Icc, mem_singleton_iff]
      norm_num
    · exact mem_kXi_sqBox (by simp; linarith) (by norm_num [abs_of_pos]; linarith)
  · refine ⟨u + ((1 / 20 / 2 : ℝ) : ℂ) * legDir j, sqSide_subset_frontier u (by norm_num) j ?_,
      mem_kXi_sqBox (by simp; linarith) (by simp; linarith)⟩
    fin_cases j <;> simp only [sqSide, legDir, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] <;> rw [Complex.mem_reProdIm] <;>
      simp only [mem_Icc, mem_singleton_iff, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im] <;>
      refine ⟨?_, ?_⟩ <;> (try constructor) <;> ring_nf <;> linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The second set of the pair used at the wall `K`: `L δ` when `legWall u λ (L δ) = K`, and the
fixed point `{m}` otherwise. -/
def legPairB (u m : ℂ) (K : Set ℂ) (L : ℝ → Set ℂ) (δ : ℝ) : Set ℂ :=
  if legWall u (1 / 20) (L δ) = K then L δ else {m}

/-- One wall: the leg concentration bound at the `δ` with `legWall u λ (L δ) = K`. -/
lemma legConc_bound_of_wall {P : Measure Ω} {μ : Ω → Measure ℂ} {ξ : ℝ} (hξ : 0 < ξ)
    (hξ' : ξ ≤ 1 / 40) {u : ℂ} (hu : u ∈ dzzVbar) {K : Set ℂ} (hK : K ∈ legWalls u)
    (h : DZZProp317In P (fun ω => dzzWall K (μ ω)) K ξ) :
    ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ → Set ℂ,
      (∀ δ ∈ Ioo (0 : ℝ) 1, L δ ⊆ frontier (sqBox u (1 / 20)) ∧ IsXiAdmissibleSet ξ δ (L δ)) →
      ∀ ι ∈ Ioo (0 : ℝ) 1, ∀ c' : ℝ, c' ≤ c → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
        legWall u (1 / 20) (L δ) = K →
        P (legConc P μ u δ ι (L δ))ᶜ ≤ ENNReal.ofReal (δ ^ (c' * ι ^ 2)) := by
  obtain ⟨m, hmF, hmK⟩ := exists_frontier_mem_kXi hξ' hK
  obtain ⟨c, hc, hconc⟩ := h
  refine ⟨c, hc, fun L hL ι hι c' hc' => ?_⟩
  have hdist : ∀ z ∈ frontier (sqBox u (1 / 20)), ξ ≤ dist u z := fun z hz =>
    le_trans (by linarith) (dist_ge_of_mem_frontier_sqBox (by norm_num) hz)
  have hBF : ∀ δ ∈ Ioo (0 : ℝ) 1, legPairB u m K L δ ⊆ frontier (sqBox u (1 / 20)) := by
    intro δ hδ
    unfold legPairB
    split_ifs
    · exact (hL δ hδ).1
    · exact singleton_subset_iff.2 hmF
  have hadm : IsXiAdmissible ξ (fun _ => {u}) (legPairB u m K L) :=
    { subset_left := fun _ _ => singleton_subset_iff.2
        (mem_dzzVXi_of_mem_legBox hu ⟨by simp; positivity, by simp; positivity⟩ hξ.le hξ')
      subset_right := fun δ hδ z hz => mem_dzzVXi_of_mem_legBox hu
        (frontier_legBox_subset_sqBox u (hBF δ hδ hz)) hξ.le hξ'
      adm_left := fun _ _ => Or.inl ⟨u, rfl⟩
      adm_right := fun δ hδ => by
        unfold legPairB
        split_ifs
        · exact (hL δ hδ).2
        · exact Or.inl ⟨m, rfl⟩
      dist_ge := fun δ hδ a ha b hb => by
        rw [mem_singleton_iff.1 ha]; exact hdist b (hBF δ hδ hb) }
  have hin : ∀ δ ∈ Ioo (0 : ℝ) 1, (fun _ => ({u} : Set ℂ)) δ ⊆ kXi K ξ ∧
      legPairB u m K L δ ⊆ kXi K ξ := by
    intro δ hδ
    refine ⟨singleton_subset_iff.2 (mem_kXi_of_mem_legWalls hξ' hK), ?_⟩
    unfold legPairB
    split_ifs with hK'
    · rw [← hK']; exact subset_kXi_legWall hξ' (hL δ hδ).1
    · exact singleton_subset_iff.2 hmK
  obtain ⟨δ₀, hδ₀, hδ₁⟩ := (hconc _ _ hadm hin).1 ι hι
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun δ hδ hKδ => ?_⟩
  have h1 := hδ₁ δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩
  have hB : legPairB u m K L δ = L δ := if_pos hKδ
  simp only [hB] at h1
  simp only [legConc, hKδ]
  refine h1.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδ.1
    (hδ.2.trans_le (min_le_right _ _)).le ?_))
  exact mul_le_mul_of_nonneg_right hc' (sq_nonneg ι)

/-- **`DZZProp317Leg` from walled P3.17 at the five leg walls** (DEC-123 §2, packet P-54LEG). -/
theorem dzzProp317Leg_of_In {P : Measure Ω} {μ : Ω → Measure ℂ} {ξ : ℝ} (hξ : 0 < ξ)
    (hξ' : ξ ≤ 1 / 40) {u : ℂ} (hu : u ∈ dzzVbar)
    (h : ∀ K ∈ legWalls u, DZZProp317In P (fun ω => dzzWall K (μ ω)) K ξ) :
    DZZProp317Leg P μ ξ u := by
  have h0 : sqBox u (1 / 10) ∈ legWalls u := mem_insert _ _
  have hj : ∀ j : Fin 4, legSq u (1 / 20) j ∈ legWalls u := fun j => mem_insert_of_mem _ ⟨j, rfl⟩
  obtain ⟨c₀, hc₀, H₀⟩ := legConc_bound_of_wall hξ hξ' hu h0 (h _ h0)
  choose cj hcj Hj using fun j => legConc_bound_of_wall hξ hξ' hu (hj j) (h _ (hj j))
  set c : ℝ := min c₀ (Finset.univ.inf' Finset.univ_nonempty cj) with hcdef
  have hc : 0 < c := lt_min hc₀ ((Finset.lt_inf'_iff _).2 fun j _ => hcj j)
  have hcj' : ∀ j, c ≤ cj j := fun j =>
    (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ j))
  refine ⟨c, hc, fun L hL ι hι => ?_⟩
  obtain ⟨d₀, hd₀, D₀⟩ := H₀ L hL ι hι c (min_le_left _ _)
  choose dj hdj Dj using fun j => Hj j L hL ι hι c (hcj' j)
  refine ⟨min d₀ (Finset.univ.inf' Finset.univ_nonempty dj),
    lt_min hd₀ ((Finset.lt_inf'_iff _).2 fun j _ => hdj j), fun δ hδ => ?_⟩
  have hδ0 : δ < d₀ := hδ.2.trans_le (min_le_left _ _)
  have hδj : ∀ j, δ < dj j := fun j =>
    hδ.2.trans_le ((min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ j)))
  rcases legWall_mem_legWalls u (L δ) with hK | ⟨j, hK⟩
  · exact D₀ δ ⟨hδ.1, hδ0⟩ hK
  · exact Dj j δ ⟨hδ.1, hδj j⟩ hK.symm

end DZZ
end LQGMetric
