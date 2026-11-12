/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53UF2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53M4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53L2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53P1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12S5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13G1

/-!
# DZZ Lemma 5.3 part 1, node 4 with the near-point cut-off (P2-DZZ53UF)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2516–2522, with the cut-off
DV-D131-3 of decision D131 at the point level: the points `x ∈ ∂𝖡` with `|w − x| < ε s_𝖡/1600`
are declared far (their `μH¹`-measure is `≤ 8 · ε s_𝖡/1600 = 0.005 ε s_𝖡`, half of the Markov
threshold `0.01 ε s_𝖡`). Needed because the scaling coupling (S5L53X4) holds only for
`2^{-m} ≤ ‖a‖ = |x − w|/|v − u|` (DZZ tacitly take `|x − w| ≍ s_𝖡`, l. 2474, 2533).

* `l53uf_near_le`: `μH¹(∂𝖡 ∩ B(w, r)) ≤ 8 r` (copy of `l53_near_le`, S5L53Y3, for `𝖡̄ = 𝕍_{c_𝖡,s_𝖡}`).
* **`l53WBadQ_le_cut`**: Markov with the cut-off: `P(bad_w) ≤ (800/ε) p` if the far probability
  is `≤ p` for `|w − x| ≥ ε s_𝖡/1600` (copy of `l53WBadQ_le`, S5L53M4).
* `l53uf_uv_bound`, `l53uf_UVBadBox_le`: `l53_uv_bound` (S5L53M4) and `l53UVBadBox_le` (S5L53M5)
  with the far hypothesis replaced by the bound on the bad events (same proofs).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- copy of `l53_near_le` (S5L53Y3): `μH¹(∂𝕍_{c,t} ∩ B(z, r)) ≤ 8 r` -/
lemma l53uf_near_sq (c : ℂ) {t : ℝ} (ht : 0 < t) (z : ℂ) (r : ℝ) :
    μH[1] (frontier (sqBox c t) ∩ {z' | dist z z' < r}) ≤ 8 * ENNReal.ofReal r := by
  have hsub : frontier (sqBox c t) ∩ {z' | dist z z' < r} ⊆
      ({z' : ℂ | z'.im = c.im - t / 2 ∧ z.re - r ≤ z'.re ∧ z'.re ≤ z.re + r} ∪
        {z' : ℂ | z'.re = c.re - t / 2 ∧ z.im - r ≤ z'.im ∧ z'.im ≤ z.im + r}) ∪
      ({z' : ℂ | z'.im = c.im + t / 2 ∧ z.re - r ≤ z'.re ∧ z'.re ≤ z.re + r} ∪
        {z' : ℂ | z'.re = c.re + t / 2 ∧ z.im - r ≤ z'.im ∧ z'.im ≤ z.im + r}) := by
    rintro z' ⟨hz', hd⟩
    rw [frontier_sqBox ht] at hz'
    have h1 : |z'.re - z.re| ≤ dist z z' := by
      rw [dist_comm, dist_eq_norm, ← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have h2 : |z'.im - z.im| ≤ dist z z' := by
      rw [dist_comm, dist_eq_norm, ← Complex.sub_im]; exact Complex.abs_im_le_norm _
    simp only [mem_setOf_eq] at hd
    rw [abs_le] at h1 h2
    simp only [mem_union, Complex.mem_reProdIm, mem_singleton_iff] at hz'
    rcases hz' with ((⟨-, h⟩ | ⟨h, -⟩) | ⟨-, h⟩) | ⟨h, -⟩
    · exact Or.inl (Or.inl ⟨h, by linarith, by linarith⟩)
    · exact Or.inl (Or.inr ⟨h, by linarith, by linarith⟩)
    · exact Or.inr (Or.inl ⟨h, by linarith, by linarith⟩)
    · exact Or.inr (Or.inr ⟨h, by linarith, by linarith⟩)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (measure_union_le _ _) (measure_union_le _ _)).trans (le_of_eq ?_)
  rw [l53M_hline_eq, l53M_vline_eq, l53M_hline_eq, l53M_vline_eq]
  rcases le_total r 0 with hr | hr
  · rw [ENNReal.ofReal_of_nonpos hr, ENNReal.ofReal_of_nonpos (by linarith)]; simp [hr]
  · rw [show z.re + r - (z.re - r) = 2 * r by ring, show z.im + r - (z.im - r) = 2 * r by ring,
      ENNReal.ofReal_mul (by norm_num)]
    simp only [ENNReal.ofReal_ofNat]
    ring

/-- `μH¹(∂𝖡 ∩ B(w, r)) ≤ 8 r` -/
lemma l53uf_near_le (b : DyBox) (w : ℂ) (r : ℝ) :
    μH[1] (frontier b.closedBox ∩ {x | dist w x < r}) ≤ 8 * ENNReal.ofReal r := by
  rw [closedBox_eq_sqBox]
  exact l53uf_near_sq _ (by unfold DyBox.side; positivity) w r

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Markov for node 4 with the cut-off** (copy of `l53WBadQ_le`, S5L53M4, with DV-D131-3). -/
theorem l53WBadQ_le_cut (P : Measure Ω) [SFinite P] {M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞}
    (hM : ∀ (c : ℚ × ℚ) (q : ℚ), Measurable fun ω => M ω c q) (δ T : ℝ)
    (w : ℂ) (b : DyBox) {ε : ℝ} (hε : 0 < ε) {p : ℝ≥0∞}
    (hp : ∀ x ∈ frontier b.closedBox, ε * b.side / 1600 ≤ dist w x →
      P {ω | l53FarQ M δ T ω w x} ≤ p) :
    P (l53WBadQ M δ T w (frontier b.closedBox) (ENNReal.ofReal (0.01 * ε * b.side))) ≤
      ENNReal.ofReal (800 / ε) * p := by
  set Bd := frontier b.closedBox
  set r : ℝ := ε * b.side / 1600 with hr
  set m : Measure ℂ := (μH[1] : Measure ℂ).restrict Bd with hm
  have hfin : IsFiniteMeasure m :=
    ⟨by rw [hm, Measure.restrict_apply_univ]; exact (l53_frontier_ne_top b).lt_top⟩
  have hs : 0 < b.side := by unfold DyBox.side; positivity
  have hBm : MeasurableSet Bd := isClosed_frontier.measurableSet
  set S : Set (Ω × ℂ) := {q | q.2 ∈ Bd ∧ l53FarQ M δ T q.1 w q.2 ∧ r ≤ dist w q.2} with hS
  have hSm : MeasurableSet S := by
    refine (measurable_snd hBm).inter (MeasurableSet.inter ?_ ?_)
    · exact (Measurable.prodMk (Measurable.prodMk measurable_fst measurable_const) measurable_snd)
        (measurableSet_l53FarQ hM δ T)
    · exact measurableSet_le measurable_const (measurable_const.dist measurable_snd)
  have hp' : ∀ x, P {ω | (ω, x) ∈ S} ≤ p := by
    intro x
    by_cases hx : x ∈ Bd
    · by_cases hd : r ≤ dist w x
      · exact (measure_mono fun ω hω => hω.2.1).trans (hp x hx hd)
      · have : {ω | (ω, x) ∈ S} = ∅ := by ext ω; simp [hS, hd]
        rw [this, measure_empty]; exact zero_le
    · have : {ω | (ω, x) ∈ S} = ∅ := by ext ω; simp [hS, hx]
      rw [this, measure_empty]; exact zero_le
  set a' : ℝ≥0∞ := ENNReal.ofReal (0.005 * ε * b.side) with ha'
  have hM' := l53_point_markov P m hSm hp' a'
  have hsplit : ENNReal.ofReal (0.01 * ε * b.side) = a' + 8 * ENNReal.ofReal r := by
    rw [ha', show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by simp, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; rw [hr]; ring
  have hset : l53WBadQ M δ T w Bd (ENNReal.ofReal (0.01 * ε * b.side)) ⊆
      {ω | a' ≤ m {x | (ω, x) ∈ S}} := by
    intro ω hω
    simp only [l53WBadQ, mem_ofPred_eq] at hω ⊢
    rw [Measure.restrict_apply' hBm] at hω
    rw [hm, Measure.restrict_apply' hBm]
    have hsub : {x | l53FarQ M δ T ω w x} ∩ Bd ⊆
        {x | (ω, x) ∈ S} ∩ Bd ∪ Bd ∩ {x | dist w x < r} := by
      rintro x ⟨hf, hxB⟩
      by_cases hd : r ≤ dist w x
      · exact Or.inl ⟨⟨hxB, hf, hd⟩, hxB⟩
      · exact Or.inr ⟨hxB, not_le.1 hd⟩
    have h1 := hω.trans ((measure_mono hsub).trans ((measure_union_le _ _).trans
      (add_le_add le_rfl (l53uf_near_le b w r))))
    rw [hsplit] at h1
    exact (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)).1 h1
  have ha0 : a' ≠ 0 := by
    rw [ha', ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  rw [hm, Measure.restrict_apply_univ] at hM'
  have hM'' := ((mul_le_mul_right (measure_mono hset) a').trans hM').trans
    (mul_le_mul_right (l53_frontier_le b) p)
  rw [mul_comm] at hM''
  have := (ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl ENNReal.ofReal_ne_top)).2 hM''
  have e : (4 : ℝ≥0∞) * ENNReal.ofReal b.side / a' = ENNReal.ofReal (800 / ε) := by
    rw [ha', show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
    ring
  refine this.trans (le_of_eq ?_)
  rw [mul_div_assoc, e, mul_comm]

/-- **Node 4 for any chain family, from the bad-event bound `B`** (copy of `l53_uv_bound`,
S5L53M4, with `hfar` replaced by the bound on the bad events). -/
theorem l53uf_uv_bound (P : Measure Ω) [SFinite P] {μ0 : Ω → Measure ℂ}
    (M : DyBox → Ω → ℚ × ℚ → ℚ → ℝ≥0∞) {u v : ℂ} {δ T ε : ℝ} (hε : 0 < ε) {N : ℕ}
    {q : ℝ≥0∞} {E G : Set Ω} {Adm : Ω → List DyBox → Prop}
    (hM : ∀ (b : DyBox) (c : ℚ × ℚ) (r : ℚ), Measurable fun ω => M b ω c r)
    {B : ℝ≥0∞} (hbad : ∀ n ≤ N, ∀ w : ℂ, (w = u ∨ w = v) → 12 * (boxAt n w).side ≤ ‖v - u‖ →
      P (l53WBadQ (M (boxAt n w)) δ T w (frontier (boxAt n w).closedBox)
        (ENNReal.ofReal (0.01 * ε * (boxAt n w).side))) ≤ B)
    (hG : P Gᶜ ≤ q)
    (hhead : ∀ ω ∈ E ∩ G, ∀ c, Adm ω c →
      L53WData μ0 M u v ε N ω (c.getD 0 DyBox.root) (l53Iface c 1) u)
    (hlast : ∀ ω ∈ E ∩ G, ∀ c, Adm ω c →
      L53WData μ0 M u v ε N ω (c.getD (c.length - 1) DyBox.root) (l53Iface c (c.length - 1)) v) :
    P (E ∩ {ω | ∃ c, Adm ω c ∧ ¬ (l53UClause (dzzWall (tildeBox u v) (μ0 ω)) u δ T c ∧
        l53VClause (dzzWall (tildeBox u v) (μ0 ω)) v δ T c)}) ≤
      q + 2 * ((N + 1 : ℕ) : ℝ≥0∞) * B := by
  set Bad : ℂ → ℕ → Set Ω := fun w n => {_ω | 12 * (boxAt n w).side ≤ ‖v - u‖} ∩
    l53WBadQ (M (boxAt n w)) δ T w
    (frontier (boxAt n w).closedBox) (ENNReal.ofReal (0.01 * ε * (boxAt n w).side)) with hBad
  have hsub : E ∩ {ω | ∃ c, Adm ω c ∧ ¬ (l53UClause (dzzWall (tildeBox u v) (μ0 ω)) u δ T c ∧
        l53VClause (dzzWall (tildeBox u v) (μ0 ω)) v δ T c)} ⊆
      Gᶜ ∪ ⋃ n ∈ Finset.range (N + 1), (Bad u n ∪ Bad v n) := by
    rintro ω ⟨hE, c, hc, hnot⟩
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not, mem_iUnion, Finset.mem_range,
      not_exists] at hcon
    obtain ⟨hωG, hbad⟩ := hcon
    apply hnot
    have key : ∀ w : ℂ, (w = u ∨ w = v) → ∀ b Λ, L53WData μ0 M u v ε N ω b Λ w →
        ∃ A ⊆ Λ, MeasurableSet A ∧
          0.99 * (μH[1] : Measure ℂ).real Λ ≤ (μH[1] : Measure ℂ).real A ∧
          ∀ x ∈ A, lgdLeExp (dzzWall (tildeBox u v) (μ0 ω)) δ T w x := by
      rintro w hw b Λ ⟨hbn, hbeq, hwb, hs, hΛm, hΛ, hΛfin, hΛε, hdom⟩
      have hnb : ω ∉ Bad w b.n := by
        rcases hw with rfl | rfl
        · exact (hbad b.n (by omega)).1
        · exact (hbad b.n (by omega)).2
      simp only [hBad, hbeq] at hnb
      exact l53_wclause_of_not_badQ hw hε (hM b) hΛm hΛ hΛfin hΛε hwb hs hdom
        fun h => hnb ⟨hs, h⟩
    refine ⟨key u (Or.inl rfl) _ _ (hhead ω ⟨hE, hωG⟩ c hc), ?_⟩
    obtain ⟨A, h1, -, h3, h4⟩ := key v (Or.inr rfl) _ _ (hlast ω ⟨hE, hωG⟩ c hc)
    exact ⟨A, h1, h3, h4⟩
  have hBad_le : ∀ n ∈ Finset.range (N + 1), P (Bad u n ∪ Bad v n) ≤ B + B := by
    intro n hn
    have hn' : n ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
    · by_cases h12 : 12 * (boxAt n u).side ≤ ‖v - u‖
      · exact (measure_mono inter_subset_right).trans (hbad n hn' u (Or.inl rfl) h12)
      · have : Bad u n = ∅ := by ext ω; simp [hBad, h12]
        rw [this, measure_empty]; exact zero_le
    · by_cases h12 : 12 * (boxAt n v).side ≤ ‖v - u‖
      · exact (measure_mono inter_subset_right).trans (hbad n hn' v (Or.inr rfl) h12)
      · have : Bad v n = ∅ := by ext ω; simp [hBad, h12]
        rw [this, measure_empty]; exact zero_le
  calc P (E ∩ {ω | ∃ c, Adm ω c ∧ ¬ (l53UClause (dzzWall (tildeBox u v) (μ0 ω)) u δ T c ∧
        l53VClause (dzzWall (tildeBox u v) (μ0 ω)) v δ T c)})
      ≤ P Gᶜ + P (⋃ n ∈ Finset.range (N + 1), (Bad u n ∪ Bad v n)) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ q + ∑ n ∈ Finset.range (N + 1), (B + B) :=
        add_le_add hG ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hBad_le))
    _ = q + 2 * ((N + 1 : ℕ) : ℝ≥0∞) * B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end DZZ
end LQGMetric
