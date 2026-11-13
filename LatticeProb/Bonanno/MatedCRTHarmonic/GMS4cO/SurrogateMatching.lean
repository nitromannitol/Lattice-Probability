/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.SurrogateMatching at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Surrogate

/-!
# The surrogate curve matches the actual curve inside `U`

Deterministic core of the root form of [18] Lemma 4.3.

Let `U = B_R(0)` and let `c` be a continuous curve with an excursion family `(e q, x q)` into `U` over the rational
labels in `U` (`GMS4cP.IsExcursionFamily`), stored as `σ q = clampSeg c (e q) (x q)` with lengths `M q = x q − e q`,
distinct excursions having distinct stored segments. If the root `c 0 = 0` is visited only at time `0`, the times of
`c` and of the surrogate curve spent in `U` correspond by time translations, with matched roots
(`L43O.surrogate_matching`). Consequently the masked observables of `c` at time `0` are those of the surrogate at
its root time (`L43O.maskedLocUStarAt_surrogate`, `L43O.maskedLocDAAt_surrogate`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.L43O

open GMS4b GMS4cP

attribute [local instance] Classical.propDecidable

section matching

variable {R : ℝ} {c : C(ℝ, ℂ)} {e x : ℚ × ℚ → ℝ} {σ : ℚ × ℚ → C(ℝ, ℂ)} {M : ℚ × ℚ → ℝ}

/-- The hypotheses on the stored data of an actual curve. -/
structure GoodStore (R : ℝ) (c : C(ℝ, ℂ)) (e x : ℚ × ℚ → ℝ) (σ : ℚ × ℚ → C(ℝ, ℂ))
    (M : ℚ × ℚ → ℝ) : Prop where
  pos : 0 < R
  fam : IsExcursionFamily c (ball (0 : ℂ) R) {q | GMS4c.ratPt q ∈ ball (0 : ℂ) R} e x
  seg : ∀ q, GMS4c.ratPt q ∈ ball (0 : ℂ) R → ⇑(σ q) = clampSeg c (e q) (x q)
  len : ∀ q, GMS4c.ratPt q ∈ ball (0 : ℂ) R → M q = x q - e q
  sep : ∀ q q', GMS4c.ratPt q ∈ ball (0 : ℂ) R → GMS4c.ratPt q' ∈ ball (0 : ℂ) R →
    σ q = σ q' → e q = e q'

theorem clampSeg_eq_clampT (c : ℝ → ℂ) (a b u : ℝ) :
    clampSeg c a b u = c (a + clampT (b - a) u) := rfl

theorem exists_qOf_eq (q : ℚ × ℚ) : ∃ n, qOf n = q :=
  (Denumerable.eqv (ℚ × ℚ)).symm.surjective q

namespace GoodStore

variable (hG : GoodStore R c e x σ M)
include hG

theorem inU_mem {n : ℕ} (hn : InU R n) : qOf n ∈ {q | GMS4c.ratPt q ∈ ball (0 : ℂ) R} := hn

theorem len_pos {n : ℕ} (hn : InU R n) : 0 < M (qOf n) := by
  rw [hG.len _ hn]
  linarith [hG.fam.lt _ (hG.inU_mem hn)]

theorem piece_rep_apply {n : ℕ} (hn : IsRep R σ M n) (t : ℝ) :
    piece R σ M n t = c (e (qOf n) + clampT (x (qOf n) - e (qOf n)) t) := by
  have hM := hG.len _ hn.1
  have hle : 0 ≤ x (qOf n) - e (qOf n) := by linarith [hG.fam.lt _ (hG.inU_mem hn.1)]
  simp only [piece, if_pos hn]
  change σ (qOf n) (clampT (M (qOf n)) t) = _
  rw [hG.seg _ hn.1, clampSeg_eq_clampT, hM, clampT_clampT hle]

theorem piece_dead_apply {n : ℕ} (hn : ¬ IsRep R σ M n) (t : ℝ) :
    piece R σ M n t = (R : ℂ) := by
  simp only [piece, if_neg hn]
  rfl

theorem pieceLen_rep {n : ℕ} (hn : IsRep R σ M n) :
    pieceLen R σ M n = x (qOf n) - e (qOf n) := by
  simp only [pieceLen, if_pos hn]
  exact hG.len _ hn.1

/-- Endpoints of excursions lie on the circle `|w| = R`. -/
theorem norm_entry {q : ℚ × ℚ} (hq : GMS4c.ratPt q ∈ ball (0 : ℂ) R) : ‖c (e q)‖ = R := by
  have hlt := hG.fam.lt q hq
  apply le_antisymm
  · have hcl : c (e q) ∈ closure (ball (0 : ℂ) R) := by
      have ht : Tendsto (fun t => c t) (𝓝[>] (e q)) (𝓝 (c (e q))) :=
        (c.continuous.tendsto _).mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto ht ?_
      filter_upwards [Ioo_mem_nhdsGT hlt] with t ht'
      exact hG.fam.mem q hq t ht'
    rw [closure_ball _ hG.pos.ne', mem_closedBall, dist_zero_right] at hcl
    exact hcl
  · have := hG.fam.entry_not_mem q hq
    rw [mem_ball, dist_zero_right, not_lt] at this
    exact this

theorem norm_exit {q : ℚ × ℚ} (hq : GMS4c.ratPt q ∈ ball (0 : ℂ) R) : ‖c (x q)‖ = R := by
  have hlt := hG.fam.lt q hq
  apply le_antisymm
  · have hcl : c (x q) ∈ closure (ball (0 : ℂ) R) := by
      have ht : Tendsto (fun t => c t) (𝓝[<] (x q)) (𝓝 (c (x q))) :=
        (c.continuous.tendsto _).mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto ht ?_
      filter_upwards [Ioo_mem_nhdsLT hlt] with t ht'
      exact hG.fam.mem q hq t ht'
    rw [closure_ball _ hG.pos.ne', mem_closedBall, dist_zero_right] at hcl
    exact hcl
  · have := hG.fam.exit_not_mem q hq
    rw [mem_ball, dist_zero_right, not_lt] at this
    exact this

theorem norm_piece_zero (n : ℕ) : ‖piece R σ M n 0‖ = R := by
  by_cases hn : IsRep R σ M n
  · rw [hG.piece_rep_apply hn, clampT_of_nonpos (by linarith [hG.fam.lt _ (hG.inU_mem hn.1)])
      le_rfl, add_zero]
    exact hG.norm_entry hn.1
  · rw [hG.piece_dead_apply hn, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hG.pos]

theorem norm_piece_end (n : ℕ) : ‖piece R σ M n (pieceLen R σ M n)‖ = R := by
  by_cases hn : IsRep R σ M n
  · have hle : 0 ≤ x (qOf n) - e (qOf n) := by linarith [hG.fam.lt _ (hG.inU_mem hn.1)]
    rw [hG.piece_rep_apply hn, hG.pieceLen_rep hn, clampT_of_ge hle le_rfl,
      show e (qOf n) + (x (qOf n) - e (qOf n)) = x (qOf n) by ring]
    exact hG.norm_exit hn.1
  · rw [hG.piece_dead_apply hn, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hG.pos]

/-! ### The surrogate on its pieces -/

theorem cumT_odd (n : ℕ) : cumT (seqLen R σ M) (2 * n + 1) =
    cumT (seqLen R σ M) (2 * n) + pieceLen R σ M n := by
  rw [cumT_succ, seqLen_even]

theorem surrogate_on_piece {n : ℕ} {t : ℝ}
    (ht : t ∈ Icc (cumT (seqLen R σ M) (2 * n)) (cumT (seqLen R σ M) (2 * n + 1))) :
    surrogate R σ M t = piece R σ M n (t - cumT (seqLen R σ M) (2 * n)) := by
  rw [surrogate_apply, concatPath_eq_of_mem (seqLen_pos R σ M) (seq_match R σ M) ht, seqPath_even]

theorem surrogate_on_conn {n : ℕ} {t : ℝ}
    (ht : t ∈ Icc (cumT (seqLen R σ M) (2 * n + 1)) (cumT (seqLen R σ M) (2 * n + 1 + 1))) :
    ‖surrogate R σ M t‖ = R := by
  rw [surrogate_apply, concatPath_eq_of_mem (seqLen_pos R σ M) (seq_match R σ M) ht, seqPath_odd]
  exact norm_connC hG.pos.le (hG.norm_piece_end n) (hG.norm_piece_zero (n + 1)) _

/-- On the open time range of a representative piece the surrogate is the curve shifted. -/
theorem surrogate_on_rep {n : ℕ} (hn : IsRep R σ M n) {t : ℝ}
    (ht : t ∈ Ioo (cumT (seqLen R σ M) (2 * n))
      (cumT (seqLen R σ M) (2 * n) + (x (qOf n) - e (qOf n)))) :
    surrogate R σ M t = c (e (qOf n) + (t - cumT (seqLen R σ M) (2 * n))) := by
  rw [hG.surrogate_on_piece ⟨ht.1.le, by rw [hG.cumT_odd, hG.pieceLen_rep hn]; exact ht.2.le⟩,
    hG.piece_rep_apply hn, clampT_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩]

/-- The surrogate is in `U` only on the open time ranges of representative pieces. -/
theorem surrogate_mem_U {t : ℝ} (ht : surrogate R σ M t ∈ ball (0 : ℂ) R) :
    ∃ n, IsRep R σ M n ∧ t ∈ Ioo (cumT (seqLen R σ M) (2 * n))
      (cumT (seqLen R σ M) (2 * n) + (x (qOf n) - e (qOf n))) := by
  have hnorm : ‖surrogate R σ M t‖ < R := by rwa [mem_ball, dist_zero_right] at ht
  rcases lt_or_ge t 0 with hneg | hnn
  · exfalso
    rw [surrogate_apply, concatPath_of_nonpos (seqLen_pos R σ M) hneg.le] at hnorm
    have := hG.norm_piece_zero 0
    rw [← seqPath_even R σ M 0] at this
    simp only [mul_zero] at this
    linarith
  obtain ⟨h1, h2⟩ := segIdx_spec (seqLen_pos R σ M) (seq_unbounded R σ M) hnn
  set k := segIdx (seqLen R σ M) t with hk
  rcases Nat.even_or_odd' k with ⟨n, hkn | hkn⟩
  · rw [hkn] at h1 h2
    by_cases hn : IsRep R σ M n
    · refine ⟨n, hn, ?_⟩
      have hpc := hG.surrogate_on_piece (n := n) ⟨h1, h2.le⟩
      rw [hG.cumT_odd, hG.pieceLen_rep hn] at h2
      rw [hpc, hG.piece_rep_apply hn] at hnorm
      rcases eq_or_lt_of_le h1 with heq | hlt
      · exfalso
        rw [← heq, sub_self, clampT_of_nonpos (by linarith [hG.fam.lt _ (hG.inU_mem hn.1)])
          le_rfl, add_zero, hG.norm_entry hn.1] at hnorm
        exact lt_irrefl _ hnorm
      · exact ⟨hlt, h2⟩
    · exfalso
      rw [hG.surrogate_on_piece (n := n) ⟨h1, h2.le⟩, hG.piece_dead_apply hn, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hG.pos] at hnorm
      exact lt_irrefl _ hnorm
  · exfalso
    rw [hkn] at h1 h2
    rw [hG.surrogate_on_conn (n := n) ⟨h1, h2.le⟩] at hnorm
    exact lt_irrefl _ hnorm

/-! ### Representatives of excursions -/

theorem exists_inU_mem {t : ℝ} (ht : c t ∈ ball (0 : ℂ) R) :
    ∃ n, InU R n ∧ t ∈ Ioo (e (qOf n)) (x (qOf n)) := by
  obtain ⟨q, hq, htq⟩ := hG.fam.cover t ht
  obtain ⟨n, hn⟩ := exists_qOf_eq q
  refine ⟨n, ?_, ?_⟩
  · change GMS4c.ratPt (qOf n) ∈ _
    rw [hn]
    exact hq
  · rw [hn]
    exact htq

/-- The index of the first label whose excursion contains `t`. -/
def idxOf (hG : GoodStore R c e x σ M) {t : ℝ} (ht : c t ∈ ball (0 : ℂ) R) : ℕ :=
  Nat.find (hG.exists_inU_mem ht)

theorem idxOf_spec {t : ℝ} (ht : c t ∈ ball (0 : ℂ) R) :
    InU R (hG.idxOf ht) ∧ t ∈ Ioo (e (qOf (hG.idxOf ht))) (x (qOf (hG.idxOf ht))) :=
  Nat.find_spec (hG.exists_inU_mem ht)

theorem seg_eq_of_entry_eq {q q' : ℚ × ℚ} (hq : GMS4c.ratPt q ∈ ball (0 : ℂ) R)
    (hq' : GMS4c.ratPt q' ∈ ball (0 : ℂ) R) (he : e q = e q') : σ q = σ q' := by
  have hx := hG.fam.exit_eq_of_entry_eq hq hq' he
  ext u
  rw [hG.seg q hq, hG.seg q' hq', he, hx]

theorem idxOf_rep {t : ℝ} (ht : c t ∈ ball (0 : ℂ) R) : IsRep R σ M (hG.idxOf ht) := by
  obtain ⟨hU, hmem⟩ := hG.idxOf_spec ht
  refine ⟨hU, hG.len_pos hU, fun m hm hUm _ hseg => ?_⟩
  have he := hG.sep _ _ hUm hU hseg
  have hx := hG.fam.exit_eq_of_entry_eq hUm hU he
  have hmem' : t ∈ Ioo (e (qOf m)) (x (qOf m)) := by rw [he, hx]; exact hmem
  exact Nat.find_min (hG.exists_inU_mem ht) hm ⟨hUm, hmem'⟩

/-- Two representatives whose excursions contain a common time coincide. -/
theorem rep_unique {n n' : ℕ} (hn : IsRep R σ M n) (hn' : IsRep R σ M n') {t : ℝ}
    (ht : t ∈ Ioo (e (qOf n)) (x (qOf n))) (ht' : t ∈ Ioo (e (qOf n')) (x (qOf n'))) :
    n = n' := by
  have he := (hG.fam.eq_of_mem hn.1 hn'.1 ht ht').1
  have hseg := hG.seg_eq_of_entry_eq hn.1 hn'.1 he
  rcases lt_trichotomy n n' with h | h | h
  · exact absurd hseg (hn'.2.2 n h hn.1 hn.2.1)
  · exact h
  · exact absurd hseg.symm (hn.2.2 n' h hn'.1 hn'.2.1)

theorem idxOf_eq {n : ℕ} (hn : IsRep R σ M n) {t : ℝ} (ht : c t ∈ ball (0 : ℂ) R)
    (htn : t ∈ Ioo (e (qOf n)) (x (qOf n))) : hG.idxOf ht = n :=
  hG.rep_unique (hG.idxOf_rep ht) hn (hG.idxOf_spec ht).2 htn

/-- Piece ranges of distinct representatives are disjoint. -/
theorem range_unique {n n' : ℕ} (hn : IsRep R σ M n) (hn' : IsRep R σ M n') {t : ℝ}
    (ht : t ∈ Ioo (cumT (seqLen R σ M) (2 * n))
      (cumT (seqLen R σ M) (2 * n) + (x (qOf n) - e (qOf n))))
    (ht' : t ∈ Ioo (cumT (seqLen R σ M) (2 * n'))
      (cumT (seqLen R σ M) (2 * n') + (x (qOf n') - e (qOf n')))) : n = n' := by
  have hmono := cumT_strictMono (seqLen_pos R σ M)
  rcases lt_trichotomy n n' with h | h | h
  · exfalso
    have h1 : cumT (seqLen R σ M) (2 * n + 1) < cumT (seqLen R σ M) (2 * n') :=
      hmono (by omega)
    rw [hG.cumT_odd, hG.pieceLen_rep hn] at h1
    linarith [ht.2, ht'.1]
  · exact h
  · exfalso
    have h1 : cumT (seqLen R σ M) (2 * n' + 1) < cumT (seqLen R σ M) (2 * n) :=
      hmono (by omega)
    rw [hG.cumT_odd, hG.pieceLen_rep hn'] at h1
    linarith [ht'.2, ht.1]

/-- The index of the representative piece containing a surrogate time spent in `U`. -/
def idxOf' (hG : GoodStore R c e x σ M) {t : ℝ} (ht : surrogate R σ M t ∈ ball (0 : ℂ) R) : ℕ :=
  Nat.find (hG.surrogate_mem_U ht)

theorem idxOf'_spec {t : ℝ} (ht : surrogate R σ M t ∈ ball (0 : ℂ) R) :
    IsRep R σ M (hG.idxOf' ht) ∧ t ∈ Ioo (cumT (seqLen R σ M) (2 * hG.idxOf' ht))
      (cumT (seqLen R σ M) (2 * hG.idxOf' ht) + (x (qOf (hG.idxOf' ht)) - e (qOf (hG.idxOf' ht)))) :=
  Nat.find_spec (hG.surrogate_mem_U ht)

/-! ### The two matchings -/

/-- The matching from `c` to the surrogate. -/
def τc (hG : GoodStore R c e x σ M) (t : ℝ) : ℝ :=
  if ht : c t ∈ ball (0 : ℂ) R then
    cumT (seqLen R σ M) (2 * hG.idxOf ht) + (t - e (qOf (hG.idxOf ht)))
  else 0

/-- The matching from the surrogate to `c`. -/
def τs (hG : GoodStore R c e x σ M) (t : ℝ) : ℝ :=
  if ht : surrogate R σ M t ∈ ball (0 : ℂ) R then
    e (qOf (hG.idxOf' ht)) + (t - cumT (seqLen R σ M) (2 * hG.idxOf' ht))
  else 0

theorem τc_eq {n : ℕ} (hn : IsRep R σ M n) {t : ℝ} (ht : c t ∈ ball (0 : ℂ) R)
    (htn : t ∈ Ioo (e (qOf n)) (x (qOf n))) :
    hG.τc t = cumT (seqLen R σ M) (2 * n) + (t - e (qOf n)) := by
  simp only [τc, dif_pos ht, hG.idxOf_eq hn ht htn]

theorem τs_eq {n : ℕ} (hn : IsRep R σ M n) {t : ℝ}
    (ht : surrogate R σ M t ∈ ball (0 : ℂ) R)
    (htn : t ∈ Ioo (cumT (seqLen R σ M) (2 * n))
      (cumT (seqLen R σ M) (2 * n) + (x (qOf n) - e (qOf n)))) :
    hG.τs t = e (qOf n) + (t - cumT (seqLen R σ M) (2 * n)) := by
  have := hG.range_unique (hG.idxOf'_spec ht).1 hn (hG.idxOf'_spec ht).2 htn
  simp only [τs, dif_pos ht, this]

theorem matching_c : IsUMatching c (surrogate R σ M) (ball (0 : ℂ) R) hG.τc := by
  refine ⟨fun t ht => ?_, fun a b hab => ?_, fun t t' ht ht' heq => ?_⟩
  · have hn := hG.idxOf_rep ht
    have htn := (hG.idxOf_spec ht).2
    rw [hG.τc_eq hn ht htn, hG.surrogate_on_rep hn
      ⟨by linarith [htn.1], by linarith [htn.2]⟩]
    congr 1
    ring
  · by_cases hab' : a ≤ b
    · have haU := hab a ⟨le_rfl, hab'⟩
      set n := hG.idxOf haU
      have hn := hG.idxOf_rep haU
      have hsub := hG.fam.subset_Ioo hn.1 hab ⟨le_rfl, hab'⟩ (hG.idxOf_spec haU).2
      refine ⟨cumT (seqLen R σ M) (2 * n) - e (qOf n), fun u hu => ?_⟩
      rw [hG.τc_eq hn (hab u hu) (hsub hu)]
      ring
    · refine ⟨0, fun u hu => absurd (hu.1.trans hu.2) hab'⟩
  · have hn := hG.idxOf_rep ht
    have hn' := hG.idxOf_rep ht'
    have hmem := (hG.idxOf_spec ht).2
    have hmem' := (hG.idxOf_spec ht').2
    rw [hG.τc_eq hn ht hmem, hG.τc_eq hn' ht' hmem'] at heq
    have hr1 : hG.τc t ∈ Ioo (cumT (seqLen R σ M) (2 * hG.idxOf ht))
        (cumT (seqLen R σ M) (2 * hG.idxOf ht) + (x (qOf (hG.idxOf ht)) - e (qOf (hG.idxOf ht)))) := by
      rw [hG.τc_eq hn ht hmem]
      exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    have hr2 : hG.τc t ∈ Ioo (cumT (seqLen R σ M) (2 * hG.idxOf ht'))
        (cumT (seqLen R σ M) (2 * hG.idxOf ht') +
          (x (qOf (hG.idxOf ht')) - e (qOf (hG.idxOf ht')))) := by
      rw [hG.τc_eq hn ht hmem, heq]
      exact ⟨by linarith [hmem'.1], by linarith [hmem'.2]⟩
    have hnn := hG.range_unique hn hn' hr1 hr2
    rw [hnn] at heq
    linarith

theorem matching_s : IsUMatching (surrogate R σ M) c (ball (0 : ℂ) R) hG.τs := by
  refine ⟨fun t ht => ?_, fun a b hab => ?_, fun t t' ht ht' heq => ?_⟩
  · obtain ⟨hn, htn⟩ := hG.idxOf'_spec ht
    rw [hG.τs_eq hn ht htn, hG.surrogate_on_rep hn htn]
  · by_cases hab' : a ≤ b
    · have haU := hab a ⟨le_rfl, hab'⟩
      set n := hG.idxOf' haU
      obtain ⟨hn, hrange⟩ := hG.idxOf'_spec haU
      have hsub : ∀ u ∈ Icc a b, u ∈ Ioo (cumT (seqLen R σ M) (2 * n))
          (cumT (seqLen R σ M) (2 * n) + (x (qOf n) - e (qOf n))) := by
        intro u hu
        refine ⟨by linarith [hrange.1, hu.1], ?_⟩
        by_contra hge
        push Not at hge
        set B := cumT (seqLen R σ M) (2 * n) + (x (qOf n) - e (qOf n))
        have hB : B ∈ Icc a b := ⟨by linarith [hrange.2], hge.trans hu.2⟩
        have hBU := hab B hB
        have hval : surrogate R σ M B = c (x (qOf n)) := by
          have hBI : B ∈ Icc (cumT (seqLen R σ M) (2 * n)) (cumT (seqLen R σ M) (2 * n + 1)) := by
            rw [hG.cumT_odd, hG.pieceLen_rep hn]
            exact ⟨by linarith [hG.fam.lt _ (hG.inU_mem hn.1)], le_rfl⟩
          rw [hG.surrogate_on_piece hBI, hG.piece_rep_apply hn,
            show B - cumT (seqLen R σ M) (2 * n) = x (qOf n) - e (qOf n) by ring,
            clampT_of_ge (by linarith [hG.fam.lt _ (hG.inU_mem hn.1)]) le_rfl]
          congr 1
          ring
        rw [hval] at hBU
        exact hG.fam.exit_not_mem _ (hG.inU_mem hn.1) hBU
      refine ⟨e (qOf n) - cumT (seqLen R σ M) (2 * n), fun u hu => ?_⟩
      rw [hG.τs_eq hn (hab u hu) (hsub u hu)]
      ring
    · refine ⟨0, fun u hu => absurd (hu.1.trans hu.2) hab'⟩
  · obtain ⟨hn, htn⟩ := hG.idxOf'_spec ht
    obtain ⟨hn', htn'⟩ := hG.idxOf'_spec ht'
    rw [hG.τs_eq hn ht htn, hG.τs_eq hn' ht' htn'] at heq
    have hm1 : hG.τs t ∈ Ioo (e (qOf (hG.idxOf' ht))) (x (qOf (hG.idxOf' ht))) := by
      rw [hG.τs_eq hn ht htn]
      exact ⟨by linarith [htn.1], by linarith [htn.2]⟩
    have hm2 : hG.τs t ∈ Ioo (e (qOf (hG.idxOf' ht'))) (x (qOf (hG.idxOf' ht'))) := by
      rw [hG.τs_eq hn ht htn, heq]
      exact ⟨by linarith [htn'.1], by linarith [htn'.2]⟩
    have hnn := hG.rep_unique hn hn' hm1 hm2
    rw [hnn] at heq
    linarith

/-! ### The roots -/

variable (hroot : c 0 = 0) (huniq : ∀ t, c t = 0 → t = 0)
include hroot huniq

omit huniq in
theorem root_mem_U : c 0 ∈ ball (0 : ℂ) R := by
  rw [hroot, mem_ball, dist_self]
  exact hG.pos

theorem isRootRep_iff (n : ℕ) :
    IsRootRep R σ M n ↔ IsRep R σ M n ∧ (0 : ℝ) ∈ Ioo (e (qOf n)) (x (qOf n)) := by
  constructor
  · rintro ⟨hn, hzero⟩
    refine ⟨hn, ?_⟩
    have hlt := hG.fam.lt _ (hG.inU_mem hn.1)
    rw [hG.len _ hn.1, show (⇑(σ (qOf n)) : ℝ → ℂ) = clampSeg c (e (qOf n)) (x (qOf n)) from
      hG.seg _ hn.1, clampSeg_image_Icc_zero_of_ge hlt.le le_rfl] at hzero
    obtain ⟨u, hu, hcu⟩ := hzero
    have hu0 := huniq u hcu
    rw [hu0] at hu
    refine ⟨lt_of_le_of_ne hu.1 fun h => ?_, lt_of_le_of_ne hu.2 fun h => ?_⟩
    · have := hG.fam.entry_not_mem _ (hG.inU_mem hn.1)
      rw [h] at this
      exact this (hG.root_mem_U hroot)
    · have := hG.fam.exit_not_mem _ (hG.inU_mem hn.1)
      rw [← h] at this
      exact this (hG.root_mem_U hroot)
  · rintro ⟨hn, hzero⟩
    refine ⟨hn, ?_⟩
    have hlt := hG.fam.lt _ (hG.inU_mem hn.1)
    rw [hG.len _ hn.1, show (⇑(σ (qOf n)) : ℝ → ℂ) = clampSeg c (e (qOf n)) (x (qOf n)) from
      hG.seg _ hn.1, clampSeg_image_Icc_zero_of_ge hlt.le le_rfl]
    exact ⟨0, ⟨hzero.1.le, hzero.2.le⟩, hroot⟩

theorem rootIdx_eq : rootIdx R σ M = hG.idxOf (hG.root_mem_U hroot) := by
  have h0 := hG.root_mem_U hroot
  have hrep := hG.idxOf_rep h0
  have hmem := (hG.idxOf_spec h0).2
  have hex : ∃ n, IsRootRep R σ M n :=
    ⟨hG.idxOf h0, (hG.isRootRep_iff hroot huniq _).2 ⟨hrep, hmem⟩⟩
  unfold rootIdx
  rw [dif_pos hex]
  have hspec := (hG.isRootRep_iff hroot huniq _).1 (Nat.find_spec hex)
  exact hG.rep_unique hspec.1 hrep hspec.2 hmem

theorem hitTime_root : hitTime (σ (qOf (rootIdx R σ M))) 0 = -e (qOf (rootIdx R σ M)) := by
  have h0 := hG.root_mem_U hroot
  have hn : IsRep R σ M (rootIdx R σ M) := by
    rw [hG.rootIdx_eq hroot huniq]; exact hG.idxOf_rep h0
  have hmem : (0 : ℝ) ∈ Ioo (e (qOf (rootIdx R σ M))) (x (qOf (rootIdx R σ M))) := by
    rw [hG.rootIdx_eq hroot huniq]; exact (hG.idxOf_spec h0).2
  have hset : {u : ℝ | σ (qOf (rootIdx R σ M)) u = 0} = {-e (qOf (rootIdx R σ M))} := by
    ext u
    simp only [mem_ofPred_eq, mem_singleton_iff]
    rw [show (σ (qOf (rootIdx R σ M)) u) =
        clampSeg c (e (qOf (rootIdx R σ M))) (x (qOf (rootIdx R σ M))) u by rw [hG.seg _ hn.1],
      clampSeg_eq_clampT]
    constructor
    · intro h
      have h1 := huniq _ h
      have hcl : clampT (x (qOf (rootIdx R σ M)) - e (qOf (rootIdx R σ M))) u =
          -e (qOf (rootIdx R σ M)) := by linarith
      by_cases hu : u ∈ Icc 0 (x (qOf (rootIdx R σ M)) - e (qOf (rootIdx R σ M)))
      · rw [clampT_of_mem hu] at hcl
        exact hcl
      · exfalso
        rcases not_and_or.1 hu with hu | hu
        · rw [clampT_of_nonpos (by linarith [hmem.1, hmem.2]) (le_of_lt (not_le.1 hu))] at hcl
          linarith [hmem.1]
        · rw [clampT_of_ge (by linarith [hmem.1, hmem.2]) (le_of_lt (not_le.1 hu))] at hcl
          linarith [hmem.2]
    · intro h
      rw [h, clampT_of_mem ⟨by linarith [hmem.1], by linarith [hmem.2]⟩,
        show e (qOf (rootIdx R σ M)) + -e (qOf (rootIdx R σ M)) = 0 by ring]
      exact hroot
  unfold hitTime
  rw [hset, csInf_singleton]

theorem τc_root : hG.τc 0 = rootTime R σ M := by
  have h0 := hG.root_mem_U hroot
  unfold rootTime
  rw [hG.hitTime_root hroot huniq, hG.rootIdx_eq hroot huniq]
  simp only [τc, dif_pos h0]
  ring

theorem τs_root : hG.τs (rootTime R σ M) = 0 := by
  have h0 := hG.root_mem_U hroot
  have hn : IsRep R σ M (rootIdx R σ M) := by
    rw [hG.rootIdx_eq hroot huniq]; exact hG.idxOf_rep h0
  have hmem : (0 : ℝ) ∈ Ioo (e (qOf (rootIdx R σ M))) (x (qOf (rootIdx R σ M))) := by
    rw [hG.rootIdx_eq hroot huniq]; exact (hG.idxOf_spec h0).2
  have hrt : rootTime R σ M =
      cumT (seqLen R σ M) (2 * rootIdx R σ M) + -e (qOf (rootIdx R σ M)) := by
    unfold rootTime
    rw [hG.hitTime_root hroot huniq]
  have hrange : rootTime R σ M ∈ Ioo (cumT (seqLen R σ M) (2 * rootIdx R σ M))
      (cumT (seqLen R σ M) (2 * rootIdx R σ M) +
        (x (qOf (rootIdx R σ M)) - e (qOf (rootIdx R σ M)))) := by
    rw [hrt]
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  have hS : surrogate R σ M (rootTime R σ M) ∈ ball (0 : ℂ) R := by
    rw [hG.surrogate_on_rep hn hrange, hrt, show e (qOf (rootIdx R σ M)) +
      (cumT (seqLen R σ M) (2 * rootIdx R σ M) + -e (qOf (rootIdx R σ M)) -
        cumT (seqLen R σ M) (2 * rootIdx R σ M)) = 0 by ring]
    exact hG.root_mem_U hroot
  rw [hG.τs_eq hn hS hrange, hrt]
  ring

end GoodStore

/-- **Locality at the root.** The masked observables of `c` at time `0` are those of the surrogate at its root
time. -/
theorem maskedLocUStarAt_surrogate (hG : GoodStore R c e x σ M) (hroot : c 0 = 0)
    (huniq : ∀ t, c t = 0 → t = 0) {θ s : ℝ} (hs : 0 ≤ s)
    (hθ : closedBall (0 : ℂ) θ ⊆ ball (0 : ℂ) R) :
    maskedLocUStarAt θ s c 0 = maskedLocUStarAt θ s (surrogate R σ M) (rootTime R σ M) :=
  maskedLocUStarAt_eq_of_matching c.continuous (surrogate R σ M).continuous hs hθ
    hG.matching_c hG.matching_s (hG.τc_root hroot huniq) (hG.τs_root hroot huniq)

theorem maskedLocDAAt_surrogate (hG : GoodStore R c e x σ M) (hroot : c 0 = 0)
    (huniq : ∀ t, c t = 0 → t = 0) {θ s : ℝ} (hs : 0 ≤ s)
    (hθ : closedBall (0 : ℂ) θ ⊆ ball (0 : ℂ) R) :
    maskedLocDAAt θ s c 0 = maskedLocDAAt θ s (surrogate R σ M) (rootTime R σ M) :=
  maskedLocDAAt_eq_of_matching c.continuous (surrogate R σ M).continuous hs hθ
    hG.matching_c hG.matching_s (hG.τc_root hroot huniq) (hG.τs_root hroot huniq)

end matching

end MatedCRTHarmonic.L43O
