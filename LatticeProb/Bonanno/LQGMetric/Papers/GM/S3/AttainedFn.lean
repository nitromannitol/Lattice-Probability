/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.AttainedFn at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedSwap
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusL38Trans
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventLength
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLength

/-!
# GM footnote at l. 1222 (`footnote-G-prob`): `P[Ḡ_1(C'', β)] ≥ β` (task P2-M2F3)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
footnote at l. 1222. GM's argument: by the definition of `C_*` there are `p, β, R` with
`P[∃ 𝕫, 𝕨 ∈ B_R(0), |𝕫 − 𝕨| ≥ β, D̃ ≥ C'D] ≥ p`; replace `𝕫, 𝕨` by a pair of points along a
`D`-geodesic so that they are close; cover by `N` unit balls; the probability of the event in
`B_1(z)` does not depend on `z` (Weyl scaling, translation invariance of the law of `h` modulo
additive constant, Axiom IV′); union bound: `P[Ḡ_1] ≥ p/N`.

We follow this argument with two bookkeeping choices (DEVIATIONS entry proposed in the report):
* the "pair of points along a geodesic" is taken along a near-minimal path (Axiom I, length
  space) instead of a geodesic, and the pair is any consecutive pair of a fine partition with
  ratio `> C''` (`fn_exists_short_pair`; Euclidean size `< 1/2`), not a pair at distance exactly
  `β r` (this also fixes the last-piece caveat of `handoff/P2-M2F.md`);
* `R`, `β` and the `N` centres are found at once by continuity from below over `m ∈ ℕ`, using
  rational points `q_i + q_k` (`q` a dense sequence) so that the events are Borel (`fnEv`,
  `fnF`).
Uniformity in the GFF: `P[h ∈ fnEv z m]` does not depend on `z` nor on the GFF
(`prob_fnEv_eq`, via `prob_eq_of_ae_addConst_iff` and Axiom IV′).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-! ## Deterministic part -/

/-- If `C D(u,w) < D̃(u,w)` and `D` is a length metric, some pair `x, y` with `|x − y| < δ` has
`C D(x,y) < D̃(x,y)` (GM footnote l. 1222, "replacing `𝕫, 𝕨` by a pair of points along a
`D`-geodesic"; partition of a near-minimal path, own bookkeeping). -/
theorem fn_exists_short_pair {D D' : ContMetric} (hL : D.IsLength) {C : ℝ} (hC : 0 ≤ C)
    {u w : ℂ} (huw : C * D.1 (u, w) < D'.1 (u, w)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x y : ℂ, ‖x - y‖ < δ ∧ C * D.1 (x, y) < D'.1 (x, y) := by
  by_contra hcon
  push_neg at hcon
  set gap := D'.1 (u, w) - C * D.1 (u, w) with hgap
  have hgap0 : 0 < gap := by linarith
  set ε := gap / (C + 1) with hε
  have hε0 : 0 < ε := div_pos hgap0 (by linarith)
  obtain ⟨γ, hγ⟩ := hL (D.pt u) (D.pt w) ε hε0
  have hf : Continuous fun t : unitInterval => weylToC D (γ t) :=
    (continuous_weylToC D).comp γ.continuous
  obtain ⟨η, hη, H⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous hf) δ hδ
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / η)
  have hn0 : (0 : ℝ) < n := lt_trans (by positivity) hn
  have hn1 : 1 / (n : ℝ) < η := by
    rw [div_lt_iff₀ hn0]; rw [div_lt_iff₀ hη] at hn; linarith
  set t : ℕ → ℝ := fun i => min ((i : ℝ) / n) 1 with ht
  have htm : Monotone t := fun i j hij =>
    min_le_min_right _ (div_le_div_of_nonneg_right (by exact_mod_cast hij) hn0.le)
  have htI : ∀ i, t i ∈ Icc (0 : ℝ) 1 := fun i =>
    ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
  have hti : ∀ i, i ≤ n → t i = (i : ℝ) / n := fun i hi =>
    min_eq_left ((div_le_one hn0).2 (by exact_mod_cast hi))
  set x : ℕ → ℂ := fun i => weylToC D (γ.extend (t i)) with hx
  -- the partition sum of `D` is at most the length
  have hsum := (eVariationOn.sum_le (f := γ.extend) (s := Icc (0 : ℝ) 1) (n := n) htm htI).trans
    hγ
  have hsumR : ∑ i ∈ Finset.range n, D.1 (x (i + 1), x i) ≤ D.1 (u, w) + ε := by
    have h0 : ∀ i, 0 ≤ D.1 (x (i + 1), x i) := fun i =>
      (dist_nonneg : 0 ≤ dist (D.pt (x (i + 1))) (D.pt (x i)))
    have hd0 : 0 ≤ D.1 (u, w) := (dist_nonneg : 0 ≤ dist (D.pt u) (D.pt w))
    rw [← ENNReal.ofReal_le_ofReal_iff (add_nonneg hd0 hε0.le), ENNReal.ofReal_add hd0 hε0.le,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => h0 i)]
    simp only [edist_dist] at hsum
    exact hsum
  -- endpoints
  have hx0 : x 0 = u := by
    simp only [hx, ht, Nat.cast_zero, zero_div, min_eq_left zero_le_one]
    exact γ.extend_zero
  have hxn : x n = w := by
    simp only [hx, ht, div_self hn0.ne', min_self]
    exact γ.extend_one
  -- the triangle inequality for `D̃`
  have htri := dist_le_range_sum_dist (fun i => D'.pt (x i)) n
  have htri' : D'.1 (u, w) ≤ ∑ i ∈ Finset.range n, D'.1 (x i, x (i + 1)) := by
    have := htri; rw [← hx0, ← hxn]; exact this
  -- each step is short
  have hstep : ∀ i ∈ Finset.range n, D'.1 (x i, x (i + 1)) ≤ C * D.1 (x (i + 1), x i) := by
    intro i hi
    have hi' : i < n := Finset.mem_range.1 hi
    rw [D.2.symm]
    refine hcon _ _ ?_
    have h1 := Path.extend_apply γ (htI i)
    have h2 := Path.extend_apply γ (htI (i + 1))
    have hd : dist (⟨t i, htI i⟩ : unitInterval) ⟨t (i + 1), htI (i + 1)⟩ < η := by
      rw [Subtype.dist_eq, Real.dist_eq]
      show |t i - t (i + 1)| < η
      rw [hti i hi'.le, hti (i + 1) hi', Nat.cast_add,
        Nat.cast_one, abs_sub_comm, ← sub_div, add_sub_cancel_left, abs_of_pos (by positivity)]
      exact hn1
    have := H hd
    rw [Complex.dist_eq] at this
    simp only [hx, h1, h2]
    exact this
  have hle : D'.1 (u, w) ≤ C * (D.1 (u, w) + ε) := by
    refine htri'.trans ((Finset.sum_le_sum hstep).trans ?_)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsumR hC
  have : gap ≤ C * ε := by rw [hgap]; nlinarith
  have hCε : C * ε < gap := by
    rw [hε, mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  linarith

/-- the dense sequence of `ℂ` used for rational points -/
abbrev fnq : ℕ → ℂ := TopologicalSpace.denseSeq ℂ

/-- the Borel event: some `q_i + z, q_j + z ∈ B_1(z)` with `|q_i − q_j| > 1/(m+1)` and
`C D(·,·) < D̃(·,·)` -/
def fnEv (D D' : DistC → ContMetric) (C : ℝ) (z : ℂ) (m : ℕ) : Set DistC :=
  ⋃ i : ℕ, ⋃ j : ℕ, ⋃ (_ : ‖fnq i‖ < 1 ∧ ‖fnq j‖ < 1 ∧ 1 / ((m : ℝ) + 1) < ‖fnq i - fnq j‖),
    {g | C * (D g).1 (fnq i + z, fnq j + z) < (D' g).1 (fnq i + z, fnq j + z)}

/-- the union over the centres `q_0, …, q_m` -/
def fnF (D D' : DistC → ContMetric) (C : ℝ) (m : ℕ) : Set DistC :=
  ⋃ k ∈ Finset.range (m + 1), fnEv D D' C (fnq k) m

lemma measurableSet_fnEv {D D' : DistC → ContMetric} (hD : Measurable D) (hD' : Measurable D')
    (C : ℝ) (z : ℂ) (m : ℕ) : MeasurableSet (fnEv D D' C z m) :=
  MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ =>
    measurableSet_lt (measurable_const.mul ((LocalEvent.measurable_apply _).comp hD))
      ((LocalEvent.measurable_apply _).comp hD')

lemma fnEv_mono (D D' : DistC → ContMetric) (C : ℝ) (z : ℂ) {m m' : ℕ} (hm : m ≤ m') :
    fnEv D D' C z m ⊆ fnEv D D' C z m' := by
  intro g hg
  simp only [fnEv, mem_iUnion, mem_ofPred_eq] at hg ⊢
  obtain ⟨i, j, ⟨h1, h2, h3⟩, h4⟩ := hg
  refine ⟨i, j, ⟨h1, h2, lt_of_le_of_lt ?_ h3⟩, h4⟩
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)

lemma fnF_mono (D D' : DistC → ContMetric) (C : ℝ) : Monotone (fnF D D' C) := by
  intro m m' hm g hg
  simp only [fnF, mem_iUnion] at hg ⊢
  obtain ⟨k, hk, hg⟩ := hg
  exact ⟨k, Finset.mem_range.2 (by have := Finset.mem_range.1 hk; omega),
    fnEv_mono D D' C _ hm hg⟩

lemma fnEv_zero_subset (D D' : DistC → ContMetric) (C : ℝ) (m : ℕ) :
    fnEv D D' C 0 m ⊆ GUp D D' 1 C (1 / ((m : ℝ) + 1)) := by
  intro g hg
  simp only [fnEv, mem_iUnion, mem_ofPred_eq, add_zero] at hg
  obtain ⟨i, j, ⟨h1, h2, h3⟩, h4⟩ := hg
  exact ⟨fnq i, mem_ball_zero_iff.2 h1, fnq j, mem_ball_zero_iff.2 h2, by rw [mul_one]; exact h3.le,
    h4.le⟩

/-- covering: a short pair with ratio `> C` gives `g ∈ fnF m` for some `m` -/
lemma exists_mem_fnF {D D' : DistC → ContMetric} {C : ℝ} {g : DistC} {x y : ℂ}
    (hxy : ‖x - y‖ < 1 / 2) (hlt : C * (D g).1 (x, y) < (D' g).1 (x, y)) :
    ∃ m, g ∈ fnF D D' C m := by
  have hne : x ≠ y := by
    rintro rfl; rw [(D g).2.self_eq_zero, (D' g).2.self_eq_zero, mul_zero] at hlt
    exact lt_irrefl _ hlt
  have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := (TopologicalSpace.denseRange_denseSeq ℂ).exists_dist_lt x
    (by norm_num : (0 : ℝ) < 1 / 4)
  set c := fnq k with hc
  rw [Complex.dist_eq] at hk
  set S : Set (ℂ × ℂ) := {p | C * (D g).1 (p.1 + c, p.2 + c) < (D' g).1 (p.1 + c, p.2 + c)} ∩
    ({p | ‖x - y‖ / 2 < ‖p.1 - p.2‖} ∩ ({p | ‖p.1‖ < 1} ∩ {p | ‖p.2‖ < 1})) with hS
  have hcp : Continuous fun p : ℂ × ℂ => (p.1 + c, p.2 + c) := by fun_prop
  have hSo : IsOpen S := by
    refine (isOpen_lt (continuous_const.mul ((D g).1.continuous.comp hcp))
      ((D' g).1.continuous.comp hcp)).inter ((isOpen_lt continuous_const (by fun_prop)).inter
      ((isOpen_lt (by fun_prop) continuous_const).inter (isOpen_lt (by fun_prop)
        continuous_const)))
  have hmem : (x - c, y - c) ∈ S := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show C * (D g).1 (x - c + c, y - c + c) < (D' g).1 (x - c + c, y - c + c)
      rw [sub_add_cancel, sub_add_cancel]; exact hlt
    · show ‖x - y‖ / 2 < ‖x - c - (y - c)‖
      rw [sub_sub_sub_cancel_right]; linarith
    · show ‖x - c‖ < 1; linarith
    · show ‖y - c‖ < 1
      have := norm_sub_le_norm_sub_add_norm_sub y x c
      rw [norm_sub_rev y x] at this; linarith
  obtain ⟨⟨i, j⟩, hij⟩ := ((TopologicalSpace.denseRange_denseSeq ℂ).prodMap
    (TopologicalSpace.denseRange_denseSeq ℂ)).exists_mem_open hSo ⟨_, hmem⟩
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt (half_pos hr)
  refine ⟨max k M, ?_⟩
  simp only [fnF, mem_iUnion]
  refine ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le (le_max_left _ _)), ?_⟩
  simp only [fnEv, mem_iUnion, mem_ofPred_eq]
  obtain ⟨h1, h2, h3, h4⟩ := hij
  refine ⟨i, j, ⟨h3, h4, lt_of_le_of_lt ?_ (hM.trans h2)⟩, h1⟩
  exact one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.add_le_add_right (le_max_right k M) 1)

/-! ## Law of `fnEv` -/

lemma mem_fnEv_iff_of_scale {D D' : DistC → ContMetric} {C : ℝ} {z : ℂ} {m : ℕ}
    {g₁ g₂ : DistC} {e : ℝ} (he : 0 < e) (h1 : ∀ u v, (D g₂).1 (u, v) = e * (D g₁).1 (u, v))
    (h2 : ∀ u v, (D' g₂).1 (u, v) = e * (D' g₁).1 (u, v)) :
    g₂ ∈ fnEv D D' C z m ↔ g₁ ∈ fnEv D D' C z m := by
  simp only [fnEv, mem_iUnion, mem_ofPred_eq, h1, h2, mul_left_comm C e]
  refine exists_congr fun i => exists_congr fun j => exists_congr fun _ =>
    ⟨fun H => lt_of_mul_lt_mul_left H he.le, fun H => mul_lt_mul_of_pos_left H he⟩

lemma mem_fnEv_iff_of_translate {D D' : DistC → ContMetric} {C : ℝ} {z : ℂ} {m : ℕ}
    {g g' : DistC} (h1 : ∀ u v, (D g').1 (u, v) = (D g).1 (u + z, v + z))
    (h2 : ∀ u v, (D' g').1 (u, v) = (D' g).1 (u + z, v + z)) :
    g' ∈ fnEv D D' C 0 m ↔ g ∈ fnEv D D' C z m := by
  simp only [fnEv, mem_iUnion, mem_ofPred_eq, h1, h2, add_zero]

section Prob
variable {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ}

lemma ae_fnEv_addConst {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c)
    (hh : IsWholePlaneGFF h P) (C : ℝ) (z : ℂ) (m : ℕ) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, addConst (h ω) a ∈ fnEv D D' C z m ↔ h ω ∈ fnEv D D' C z m := by
  filter_upwards [hD.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh),
    hD'.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh)] with ω hw hw' a
  exact mem_fnEv_iff_of_scale (Real.exp_pos _) (hw a) (hw' a)

/-- `P[h ∈ fnEv z m]` depends neither on `z` nor on the whole-plane GFF (GM footnote l. 1222:
Weyl scaling, translation invariance of the law of `h` modulo additive constant, Axiom IV′) -/
theorem prob_fnEv_eq (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {h : Ω → DistC} {h' : Ω' → DistC}
    (hh : IsWholePlaneGFF h P) (hh' : IsWholePlaneGFF h' P') (C : ℝ) (z : ℂ) (m : ℕ) :
    P (h ⁻¹' fnEv D D' C z m) = P' (h' ⁻¹' fnEv D D' C 0 m) := by
  have hz := hh.affineComp one_pos z
  have e1 : P (h ⁻¹' fnEv D D' C z m) =
      P ((fun ω => affineComp 1 z (h ω)) ⁻¹' fnEv D D' C 0 m) := by
    refine measure_congr ?_
    filter_upwards [hD.translation P h (Tight.isGFFPlusCont_of_wp hh) z,
      hD'.translation P h (Tight.isGFFPlusCont_of_wp hh) z] with ω ht ht'
    exact propext (mem_fnEv_iff_of_translate ht ht').symm
  rw [e1]
  exact prob_eq_of_ae_addConst_iff hz hh' (measurableSet_fnEv hD.measurable hD'.measurable C 0 m)
    (ae_fnEv_addConst hD hD' hz C 0 m) (ae_fnEv_addConst hD hD' hh' C 0 m)

end Prob

/-- **GM footnote at l. 1222** (`footnote-G-prob`): for `C'' ∈ (0, C_*)` there is `β ∈ (0,1)`
with `P[Ḡ_1(C'', β)] ≥ β` for every whole-plane GFF. -/
theorem gm_S3_2fn : S3_2fn := by
  intro γ D D' c cs Cs hS hR C'' hC''
  obtain ⟨-, -, hD, hD'⟩ := hS
  obtain ⟨Ω₀, _, P₀, h₀, hP₀, hh₀⟩ := GFFExist.exists_wholePlaneGFF
  have := hP₀
  haveI : Nonempty {p : ℂ × ℂ // p.1 ≠ p.2} := ⟨⟨(0, 1), zero_ne_one⟩⟩
  -- a.s. some `fnF m` occurs (definition of `C_*`, Axiom I)
  have hae : ∀ᵐ ω ∂P₀, ω ∈ ⋃ m, h₀ ⁻¹' fnF D D' C'' m := by
    filter_upwards [hR P₀ h₀ hh₀, hD.length P₀ h₀ (Tight.isGFFPlusCont_of_wp hh₀)] with ω hω hl
    obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup
      (show C'' < upperRatio D D' (h₀ ω) by rw [hω.2]; exact hC''.2)
    have hDp := dist_pos_of_ne (D (h₀ ω)) p.2
    rw [lt_div_iff₀ hDp] at hp
    obtain ⟨x, y, hxy, hlt⟩ := fn_exists_short_pair hl hC''.1.le hp (by norm_num : (0 : ℝ) < 1 / 2)
    exact mem_iUnion.2 (exists_mem_fnF hxy hlt)
  have hU : P₀ (⋃ m, h₀ ⁻¹' fnF D D' C'' m) = 1 := by
    rw [← measure_univ (μ := P₀)]
    exact measure_congr (ae_eq_univ.2 (ae_iff.1 hae))
  have htend := tendsto_measure_iUnion_atTop (μ := P₀)
    (fun m m' hm => preimage_mono (fnF_mono D D' C'' hm) : Monotone fun m =>
      h₀ ⁻¹' fnF D D' C'' m)
  rw [hU] at htend
  obtain ⟨m, hm⟩ := (htend.eventually (lt_mem_nhds (ENNReal.ofReal_lt_one.2
    (by norm_num : (1 / 2 : ℝ) < 1)))).exists
  -- union bound
  have hub : P₀ (h₀ ⁻¹' fnF D D' C'' m) ≤
      ((m + 1 : ℕ) : ℝ≥0∞) * P₀ (h₀ ⁻¹' fnEv D D' C'' 0 m) := by
    simp only [fnF, preimage_iUnion₂]
    refine (measure_biUnion_finset_le _ _).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl fun k _ => prob_fnEv_eq hD hD' hh₀ hh₀ C'' (fnq k) m,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  set β : ℝ := 1 / (2 * ((m : ℝ) + 1)) with hβ
  have hβ0 : 0 < β := by positivity
  have hβ1 : β < 1 := by
    rw [hβ, div_lt_one (by positivity)]; have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith
  have hβm : β ≤ 1 / ((m : ℝ) + 1) := by
    rw [hβ]; exact one_div_le_one_div_of_le (by positivity) (by
      have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith)
  have hp : ENNReal.ofReal β ≤ P₀ (h₀ ⁻¹' fnEv D D' C'' 0 m) := by
    by_contra hcon
    push_neg at hcon
    have h1 : ((m + 1 : ℕ) : ℝ≥0∞) * P₀ (h₀ ⁻¹' fnEv D D' C'' 0 m) ≤
        ENNReal.ofReal (1 / 2) := by
      calc _ ≤ ((m + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal β := by gcongr
        _ = ENNReal.ofReal (((m + 1 : ℕ) : ℝ) * β) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
        _ = ENNReal.ofReal (1 / 2) := by
          congr 1; rw [hβ]; push_cast; field_simp
    exact absurd (hm.trans_le (hub.trans h1)) (lt_irrefl _)
  refine ⟨β, ⟨hβ0, hβ1⟩, fun P _ h hh => ?_⟩
  rw [← prob_fnEv_eq hD hD' hh hh₀ C'' 0 m] at hp
  exact hp.trans (measure_mono (preimage_mono ((fnEv_zero_subset D D' C'' m).trans
    (GUp_anti_beta D D' zero_le_one C'' hβm))))

end LQGMetric.GM
