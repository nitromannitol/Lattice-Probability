/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.Concat at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Concatenation of a sequence of paths

A tool for the measurable form of [18] Lemma 4.3: the excursions of a curve into an open set are glued, in a fixed
order of their rational labels and joined by connectors outside the set, into one continuous surrogate curve. This
file is the generic part: a sequence of paths `f n`, each constant outside `[0, len n]`, with positive lengths,
matching endpoints `f n (len n) = f (n+1) 0`, and unbounded cumulative length, is concatenated into
`concatPath f len : ℝ → ℂ`.

* `L43O.cumT len n = ∑_{m<n} len m`, `L43O.segIdx len t` (the segment containing `t ≥ 0`);
* `L43O.concatPath_eq_of_mem`: on `[cumT n, cumT (n+1)]` the concatenation is `f n (· − cumT n)`;
* `L43O.continuous_concatPath`;
* `L43O.measurable_concatPath_apply`: measurability in parameters.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace MatedCRTHarmonic.L43O

attribute [local instance] Classical.propDecidable

/-- Clamp `t` to `[0, ℓ]`. -/
def clampT (ℓ t : ℝ) : ℝ := max 0 (min t ℓ)

theorem continuous_clampT (ℓ : ℝ) : Continuous (clampT ℓ) := by
  unfold clampT
  fun_prop

theorem clampT_of_mem {ℓ t : ℝ} (ht : t ∈ Icc 0 ℓ) : clampT ℓ t = t := by
  unfold clampT
  rw [min_eq_left ht.2, max_eq_right ht.1]

theorem clampT_mem {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (t : ℝ) : clampT ℓ t ∈ Icc 0 ℓ :=
  ⟨le_max_left _ _, max_le hℓ (min_le_right _ _)⟩

theorem clampT_clampT {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (t : ℝ) : clampT ℓ (clampT ℓ t) = clampT ℓ t :=
  clampT_of_mem (clampT_mem hℓ t)

theorem clampT_of_nonpos {ℓ t : ℝ} (hℓ : 0 ≤ ℓ) (ht : t ≤ 0) : clampT ℓ t = 0 := by
  unfold clampT
  exact max_eq_left ((min_le_left _ _).trans ht)

theorem clampT_of_ge {ℓ t : ℝ} (hℓ : 0 ≤ ℓ) (ht : ℓ ≤ t) : clampT ℓ t = ℓ := by
  unfold clampT
  rw [min_eq_right ht, max_eq_right hℓ]

theorem measurable_clampT_joint : Measurable fun p : ℝ × ℝ => clampT p.1 p.2 := by
  unfold clampT
  exact measurable_const.max (measurable_snd.min measurable_fst)

/-! ## Cumulative times -/

/-- `cumT len n = ∑_{m < n} len m`. -/
def cumT (len : ℕ → ℝ) (n : ℕ) : ℝ := ∑ m ∈ Finset.range n, len m

theorem cumT_zero (len : ℕ → ℝ) : cumT len 0 = 0 := by simp [cumT]

theorem cumT_succ (len : ℕ → ℝ) (n : ℕ) : cumT len (n + 1) = cumT len n + len n := by
  simp [cumT, Finset.sum_range_succ]

theorem cumT_strictMono {len : ℕ → ℝ} (hpos : ∀ n, 0 < len n) : StrictMono (cumT len) :=
  strictMono_nat_of_lt_succ fun n => by rw [cumT_succ]; linarith [hpos n]

theorem cumT_nonneg {len : ℕ → ℝ} (hpos : ∀ n, 0 < len n) (n : ℕ) : 0 ≤ cumT len n := by
  rw [← cumT_zero len]
  exact (cumT_strictMono hpos).monotone (Nat.zero_le n)

theorem measurable_cumT {Ξ : Type*} [MeasurableSpace Ξ] {Len : Ξ → ℕ → ℝ}
    (hLen : ∀ n, Measurable fun ξ => Len ξ n) (n : ℕ) : Measurable fun ξ => cumT (Len ξ) n := by
  unfold cumT
  exact Finset.measurable_sum _ fun m _ => hLen m

/-- The index of the segment containing `t` (`0` if there is none). -/
def segIdx (len : ℕ → ℝ) (t : ℝ) : ℕ :=
  if h : ∃ n, t < cumT len (n + 1) then Nat.find h else 0

theorem segIdx_eq {len : ℕ → ℝ} (hpos : ∀ n, 0 < len n) {n : ℕ} {t : ℝ}
    (h1 : cumT len n ≤ t) (h2 : t < cumT len (n + 1)) : segIdx len t = n := by
  have hex : ∃ n, t < cumT len (n + 1) := ⟨n, h2⟩
  unfold segIdx
  rw [dif_pos hex]
  refine le_antisymm (Nat.find_min' hex h2) ?_
  by_contra hlt
  push_neg at hlt
  have hm := Nat.find_spec hex
  have : cumT len (Nat.find hex + 1) ≤ cumT len n :=
    (cumT_strictMono hpos).monotone (Nat.succ_le_of_lt hlt)
  linarith

theorem segIdx_spec {len : ℕ → ℝ} (hpos : ∀ n, 0 < len n)
    (hunb : ∀ K : ℝ, ∃ N, K ≤ cumT len N) {t : ℝ} (ht : 0 ≤ t) :
    cumT len (segIdx len t) ≤ t ∧ t < cumT len (segIdx len t + 1) := by
  obtain ⟨N, hN⟩ := hunb (t + 1)
  have hex : ∃ n, t < cumT len (n + 1) :=
    ⟨N, lt_of_lt_of_le (by linarith) (hN.trans ((cumT_strictMono hpos).monotone (Nat.le_succ N)))⟩
  unfold segIdx
  rw [dif_pos hex]
  refine ⟨?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos'
  · rw [h0, cumT_zero]
    exact ht
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos'.ne'
    have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
    push_neg at hmin
    rw [hk]
    exact hmin

/-! ## The concatenation -/

/-- The concatenation of the paths `f n` of lengths `len n`, constant `f 0 0` before time `0`. -/
def concatPath (f : ℕ → ℝ → ℂ) (len : ℕ → ℝ) (t : ℝ) : ℂ :=
  if t < 0 then f 0 0 else f (segIdx len t) (t - cumT len (segIdx len t))

section props

variable {f : ℕ → ℝ → ℂ} {len : ℕ → ℝ}

theorem concatPath_eq_of_mem (hpos : ∀ n, 0 < len n)
    (hmatch : ∀ n, f n (len n) = f (n + 1) 0) {n : ℕ} {t : ℝ}
    (ht : t ∈ Icc (cumT len n) (cumT len (n + 1))) :
    concatPath f len t = f n (t - cumT len n) := by
  have ht0 : 0 ≤ t := (cumT_nonneg hpos n).trans ht.1
  unfold concatPath
  rw [if_neg (not_lt.2 ht0)]
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · have hidx : segIdx len t = n + 1 := by
      refine segIdx_eq hpos (le_of_eq heq.symm) ?_
      rw [heq, cumT_succ len (n + 1)]
      linarith [hpos (n + 1)]
    rw [hidx, heq, sub_self, ← hmatch n, cumT_succ]
    congr 1
    ring
  · rw [segIdx_eq hpos ht.1 hlt]

theorem concatPath_of_nonpos {t : ℝ} (hpos : ∀ n, 0 < len n) (ht : t ≤ 0) :
    concatPath f len t = f 0 0 := by
  unfold concatPath
  rcases eq_or_lt_of_le ht with h0 | hlt
  · rw [if_neg (not_lt.2 (le_of_eq h0.symm)), h0,
      segIdx_eq hpos (le_of_eq (cumT_zero len)) (by rw [cumT_succ, cumT_zero]; linarith [hpos 0]),
      cumT_zero, sub_zero]
  · rw [if_pos hlt]

theorem continuous_concatPath (hpos : ∀ n, 0 < len n)
    (hunb : ∀ K : ℝ, ∃ N, K ≤ cumT len N) (hcont : ∀ n, Continuous (f n))
    (hmatch : ∀ n, f n (len n) = f (n + 1) 0) : Continuous (concatPath f len) := by
  let S : Option ℕ → Set ℝ := fun o => Option.elim o (Iic 0)
    (fun n => Icc (cumT len n) (cumT len (n + 1)))
  have hlf : LocallyFinite S := by
    refine locallyFinite_option.2 fun x => ?_
    obtain ⟨N, hN⟩ := hunb (x + 1)
    refine ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    refine (Set.finite_lt_nat N).subset fun n hn => ?_
    obtain ⟨y, hyS, hyI⟩ := hn
    by_contra hge
    have hge' : N ≤ n := not_lt.1 hge
    have h1 : cumT len N ≤ cumT len n := (cumT_strictMono hpos).monotone hge'
    have h2 := hyS.1
    have h3 := hyI.2
    linarith
  refine hlf.continuous ?_ (fun o => ?_) (fun o => ?_)
  · refine eq_univ_of_forall fun t => mem_iUnion.2 ?_
    rcases le_or_gt t 0 with ht | ht
    · exact ⟨none, ht⟩
    · obtain ⟨h1, h2⟩ := segIdx_spec hpos hunb ht.le
      exact ⟨some (segIdx len t), h1, h2.le⟩
  · cases o with
    | none => exact isClosed_Iic
    | some n => exact isClosed_Icc
  · cases o with
    | none =>
      refine (continuousOn_const (c := f 0 0)).congr fun t ht => ?_
      exact concatPath_of_nonpos hpos ht
    | some n =>
      have hg : Continuous fun t : ℝ => f n (t - cumT len n) :=
        (hcont n).comp (continuous_id.sub continuous_const)
      refine hg.continuousOn.congr fun t ht => ?_
      exact concatPath_eq_of_mem hpos hmatch ht

end props

/-! ## Measurability in parameters -/

/-- Selecting one of countably many measurable maps by a measurable index. -/
theorem measurable_natSelect {Ξ β : Type*} [MeasurableSpace Ξ] [MeasurableSpace β]
    {idx : Ξ → ℕ} (hidx : Measurable idx) {g : ℕ → Ξ → β} (hg : ∀ n, Measurable (g n)) :
    Measurable fun ξ => g (idx ξ) ξ := by
  intro s hs
  have heq : (fun ξ => g (idx ξ) ξ) ⁻¹' s = ⋃ n, (idx ⁻¹' {n} ∩ g n ⁻¹' s) := by
    ext ξ
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun h => ⟨idx ξ, rfl, h⟩, fun ⟨n, hn, h⟩ => hn ▸ h⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n => (hidx (measurableSet_singleton n)).inter (hg n hs)

theorem measurable_segIdx {Ξ : Type*} [MeasurableSpace Ξ] {Len : Ξ → ℕ → ℝ}
    (hLen : ∀ n, Measurable fun ξ => Len ξ n) (t : ℝ) :
    Measurable fun ξ => segIdx (Len ξ) t := by
  refine measurable_to_countable' fun n => ?_
  have hlt : ∀ m, MeasurableSet {ξ | t < cumT (Len ξ) (m + 1)} := fun m =>
    measurableSet_lt measurable_const (measurable_cumT hLen (m + 1))
  have hE : MeasurableSet {ξ | ∃ m, t < cumT (Len ξ) (m + 1)} := by
    rw [Set.ofPred_exists]
    exact MeasurableSet.iUnion hlt
  have heq : (fun ξ => segIdx (Len ξ) t) ⁻¹' {n} =
      ({ξ | ∃ m, t < cumT (Len ξ) (m + 1)} ∩
        ({ξ | t < cumT (Len ξ) (n + 1)} ∩ ⋂ m ∈ Finset.range n, {ξ | t < cumT (Len ξ) (m + 1)}ᶜ)) ∪
      ({ξ | ∃ m, t < cumT (Len ξ) (m + 1)}ᶜ ∩ (if n = 0 then univ else ∅)) := by
    ext ξ
    simp only [mem_preimage, mem_singleton_iff, segIdx, mem_union, mem_inter_iff, mem_ofPred_eq,
      mem_iInter, Finset.mem_range, mem_compl_iff]
    by_cases hex : ∃ m, t < cumT (Len ξ) (m + 1)
    · simp only [hex, ↓reduceDIte, true_and, not_true_eq_false, false_and, or_false]
      rw [Nat.find_eq_iff]
    · simp only [hex, ↓reduceDIte, false_and, not_false_eq_true, true_and, false_or]
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn, Ne.symm hn]
  rw [heq]
  refine (hE.inter ((hlt n).inter (Finset.measurableSet_biInter _ fun m _ => (hlt m).compl))).union
    (hE.compl.inter ?_)
  split_ifs
  · exact MeasurableSet.univ
  · exact MeasurableSet.empty

/-- **Measurability in parameters.** If the paths are measurable `C(ℝ, ℂ)`-valued functions of a parameter and
The lengths are measurable, each value of the concatenation is measurable. -/
theorem measurable_concatPath_apply {Ξ : Type*} [MeasurableSpace Ξ] {F : Ξ → ℕ → C(ℝ, ℂ)}
    {Len : Ξ → ℕ → ℝ} (hF : ∀ n, Measurable fun ξ => F ξ n)
    (hLen : ∀ n, Measurable fun ξ => Len ξ n) (t : ℝ) :
    Measurable fun ξ => concatPath (fun n => ⇑(F ξ n)) (Len ξ) t := by
  unfold concatPath
  by_cases ht : t < 0
  · simp only [ht, ↓reduceIte]
    exact (continuous_eval_const (0 : ℝ)).measurable.comp (hF 0)
  · simp only [ht, ↓reduceIte]
    refine measurable_natSelect (measurable_segIdx hLen t) (g := fun n ξ =>
      (F ξ n) (t - cumT (Len ξ) n)) fun n => ?_
    exact continuous_eval.measurable.comp
      ((hF n).prodMk (measurable_const.sub (measurable_cumT hLen n)))

end MatedCRTHarmonic.L43O
