import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Straddling level pairs of a continuous function

Let `f : ℝ → ℝ` be continuous, `v` a time and `l < f v` a level such that `f ≤ l` somewhere on both sides of `v`.
The last time `lastBelow f v l ≤ v` and the first time `firstBelow f v l ≥ v` at which `f ≤ l` bound the excursion
interval of `f` above `l` that straddles `v`: `f = l` at both ends and `f > l` strictly inside
(`straddle_pair`). Conversely, every pair `a < v < b` with `f a = f b` and `f > f a` on `(a, b)` (a pair of times
identified in the contour tree of `f`, straddling `v`) is the straddling pair at level `f a`
(`lastBelow_eq_and_firstBelow_eq`).

The main result, `exists_level_eq_of_straddle_pairs`, compares two continuous functions `X` and `Y`. Suppose that every
straddling pair of `X` at `v` is a contour pair of `Y` (equal values of `Y` at both ends, strictly larger values
inside). If `X` takes values below `X v` in every left neighbourhood of `v`, distinct local minima of `X` have distinct
values, and `Y` is unbounded below, then every straddling pair of `Y` at `v` is a straddling pair of `X` at `v`: the
chain of straddling pairs has no gap. The proof uses the right continuity of `l ↦ lastBelow X v l`, and its left
continuity or that of `l ↦ firstBelow X v l` (one of the two endpoints is left continuous at each level, since a
jump of an endpoint produces a local minimum of `X` at that level).
-/

set_option autoImplicit false

open Set Filter Topology

namespace LatticeProb

/-- The last time at or before `v` at which `f` is at most `l`. -/
noncomputable def lastBelow (f : ℝ → ℝ) (v l : ℝ) : ℝ := sSup {u | u ≤ v ∧ f u ≤ l}

/-- The first time at or after `v` at which `f` is at most `l`. -/
noncomputable def firstBelow (f : ℝ → ℝ) (v l : ℝ) : ℝ := sInf {u | v ≤ u ∧ f u ≤ l}

section OneFunction

variable {f : ℝ → ℝ} {v l u : ℝ}

theorem lastBelow_mem (hf : Continuous f) (ha : ∃ a ≤ v, f a ≤ l) :
    lastBelow f v l ≤ v ∧ f (lastBelow f v l) ≤ l := by
  have hcl : IsClosed {u | u ≤ v ∧ f u ≤ l} :=
    (isClosed_le continuous_id continuous_const).inter (isClosed_le hf continuous_const)
  obtain ⟨a, hav, hfa⟩ := ha
  exact hcl.csSup_mem ⟨a, hav, hfa⟩ ⟨v, fun _ hw => hw.1⟩

theorem firstBelow_mem (hf : Continuous f) (hb : ∃ b, v ≤ b ∧ f b ≤ l) :
    v ≤ firstBelow f v l ∧ f (firstBelow f v l) ≤ l := by
  have hcl : IsClosed {u | v ≤ u ∧ f u ≤ l} :=
    (isClosed_le continuous_const continuous_id).inter (isClosed_le hf continuous_const)
  obtain ⟨b, hvb, hfb⟩ := hb
  exact hcl.csInf_mem ⟨b, hvb, hfb⟩ ⟨v, fun _ hw => hw.1⟩

theorem le_lastBelow (hu : u ≤ v) (hfu : f u ≤ l) : u ≤ lastBelow f v l :=
  le_csSup ⟨v, fun _ hw => hw.1⟩ ⟨hu, hfu⟩

theorem firstBelow_le (hu : v ≤ u) (hfu : f u ≤ l) : firstBelow f v l ≤ u :=
  csInf_le ⟨v, fun _ hw => hw.1⟩ ⟨hu, hfu⟩

theorem lt_apply_of_lastBelow_lt (hu : lastBelow f v l < u) (huv : u ≤ v) : l < f u := by
  by_contra h
  exact absurd (le_lastBelow huv (not_lt.mp h)) (not_le.mpr hu)

theorem lt_apply_of_lt_firstBelow (hvu : v ≤ u) (hu : u < firstBelow f v l) : l < f u := by
  by_contra h
  exact absurd (firstBelow_le hvu (not_lt.mp h)) (not_le.mpr hu)

theorem apply_lastBelow (hf : Continuous f) (hl : l < f v) (ha : ∃ a ≤ v, f a ≤ l) :
    f (lastBelow f v l) = l := by
  obtain ⟨hsv, hfs⟩ := lastBelow_mem hf ha
  refine le_antisymm hfs ?_
  by_contra h
  push Not at h
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hsv hf.continuousOn ⟨h.le, hl.le⟩
  have hsc : lastBelow f v l < c := lt_of_le_of_ne hc.1 (by rintro rfl; exact h.ne hfc)
  exact (lt_apply_of_lastBelow_lt hsc hc.2).ne' hfc

theorem apply_firstBelow (hf : Continuous f) (hl : l < f v) (hb : ∃ b, v ≤ b ∧ f b ≤ l) :
    f (firstBelow f v l) = l := by
  obtain ⟨hvt, hft⟩ := firstBelow_mem hf hb
  refine le_antisymm hft ?_
  by_contra h
  push Not at h
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hvt hf.continuousOn ⟨h.le, hl.le⟩
  have hct : c < firstBelow f v l := lt_of_le_of_ne hc.2 (by rintro rfl; exact h.ne hfc)
  exact (lt_apply_of_lt_firstBelow hc.1 hct).ne' hfc

theorem lastBelow_lt (hf : Continuous f) (hl : l < f v) (ha : ∃ a ≤ v, f a ≤ l) :
    lastBelow f v l < v := by
  refine lt_of_le_of_ne (lastBelow_mem hf ha).1 fun h => ?_
  have h2 := apply_lastBelow hf hl ha
  rw [h] at h2
  exact hl.ne' h2

theorem lt_firstBelow (hf : Continuous f) (hl : l < f v) (hb : ∃ b, v ≤ b ∧ f b ≤ l) :
    v < firstBelow f v l := by
  refine lt_of_le_of_ne (firstBelow_mem hf hb).1 fun h => ?_
  have h2 := apply_firstBelow hf hl hb
  rw [← h] at h2
  exact hl.ne' h2

/-- **The straddling pair is an excursion interval above the level.** -/
theorem straddle_pair (hf : Continuous f) (hl : l < f v) (ha : ∃ a ≤ v, f a ≤ l)
    (hb : ∃ b, v ≤ b ∧ f b ≤ l) :
    lastBelow f v l < firstBelow f v l ∧ f (lastBelow f v l) = f (firstBelow f v l) ∧
      ∀ u ∈ Ioo (lastBelow f v l) (firstBelow f v l), f (lastBelow f v l) < f u := by
  have hs := apply_lastBelow hf hl ha
  have ht := apply_firstBelow hf hl hb
  refine ⟨(lastBelow_lt hf hl ha).trans (lt_firstBelow hf hl hb), hs.trans ht.symm, fun u hu => ?_⟩
  rw [hs]
  rcases le_total u v with huv | hvu
  · exact lt_apply_of_lastBelow_lt hu.1 huv
  · exact lt_apply_of_lt_firstBelow hvu hu.2

/-- **Contour pairs straddling `v` are straddling pairs.** If `a < v < b`, `f a = f b` and `f > f a` on `(a, b)`,
then `(a, b)` is the straddling pair of `f` at `v` at level `f a`. -/
theorem lastBelow_eq_and_firstBelow_eq {a b : ℝ} (hav : a < v) (hvb : v < b) (hab : f a = f b)
    (hin : ∀ u ∈ Ioo a b, f a < f u) : lastBelow f v (f a) = a ∧ firstBelow f v (f a) = b := by
  constructor
  · refine IsGreatest.csSup_eq ⟨⟨hav.le, le_rfl⟩, fun w hw => ?_⟩
    by_contra h
    push Not at h
    exact absurd hw.2 (not_le.mpr (hin w ⟨h, hw.1.trans_lt hvb⟩))
  · refine IsLeast.csInf_eq ⟨⟨hvb.le, hab.symm.le⟩, fun w hw => ?_⟩
    by_contra h
    push Not at h
    exact absurd hw.2 (not_le.mpr (hin w ⟨hav.trans_le hw.1, h⟩))

theorem lastBelow_mono {l' : ℝ} (hll' : l ≤ l') (ha : ∃ a ≤ v, f a ≤ l) :
    lastBelow f v l ≤ lastBelow f v l' := by
  obtain ⟨a, hav, hfa⟩ := ha
  exact csSup_le_csSup ⟨v, fun _ hw => hw.1⟩ ⟨a, hav, hfa⟩ fun w hw => ⟨hw.1, hw.2.trans hll'⟩

theorem firstBelow_anti {l' : ℝ} (hll' : l ≤ l') (hb : ∃ b, v ≤ b ∧ f b ≤ l) :
    firstBelow f v l' ≤ firstBelow f v l := by
  obtain ⟨b, hvb, hfb⟩ := hb
  exact csInf_le_csInf ⟨v, fun _ hw => hw.1⟩ ⟨b, hvb, hfb⟩ fun w hw => ⟨hw.1, hw.2.trans hll'⟩

/-- **Right continuity of the left endpoint.** -/
theorem exists_lastBelow_lt_add (hf : Continuous f) (ha : ∃ a ≤ v, f a ≤ l) {ε : ℝ}
    (hε : 0 < ε) : ∃ l₁, l < l₁ ∧ ∀ l', l ≤ l' → l' < l₁ → lastBelow f v l' < lastBelow f v l + ε := by
  obtain ⟨a, hav, hfa⟩ := ha
  by_cases hK : v < lastBelow f v l + ε
  · refine ⟨l + 1, by linarith, fun l' hll' _ => ?_⟩
    exact lt_of_le_of_lt (lastBelow_mem hf ⟨a, hav, hfa.trans hll'⟩).1 hK
  push Not at hK
  obtain ⟨p, hp, hpmin⟩ := (isCompact_Icc (a := lastBelow f v l + ε) (b := v)).exists_isMinOn
    (nonempty_Icc.mpr hK) hf.continuousOn
  have hlp : l < f p := lt_apply_of_lastBelow_lt (by linarith [hp.1]) hp.2
  refine ⟨f p, hlp, fun l' hll' hl'p => ?_⟩
  by_contra h
  push Not at h
  obtain ⟨hs'v, hfs'⟩ := lastBelow_mem hf ⟨a, hav, hfa.trans hll'⟩
  have := isMinOn_iff.mp hpmin _ ⟨h, hs'v⟩
  linarith

/-- If the left endpoint jumps at level `l` (from the left), then it is a local minimum of `f`. -/
theorem isLocalMin_lastBelow (hf : Continuous f) (hl : l < f v) (ha : ∃ a ≤ v, f a ≤ l) {ε : ℝ}
    (hε : 0 < ε) (hjump : ∀ l' < l, lastBelow f v l' ≤ lastBelow f v l - ε) :
    IsLocalMin f (lastBelow f v l) := by
  have hs := apply_lastBelow hf hl ha
  have hsv := lastBelow_lt hf hl ha
  refine Filter.mem_of_superset (Ioo_mem_nhds (by linarith : lastBelow f v l - ε < lastBelow f v l) hsv)
    fun w hw => ?_
  show f (lastBelow f v l) ≤ f w
  rw [hs]
  by_contra h
  push Not at h
  have h1 := hjump (f w) h
  have h2 : w ≤ lastBelow f v (f w) := le_lastBelow hw.2.le le_rfl
  linarith [hw.1]

/-- If the right endpoint jumps at level `l` (from the left), then it is a local minimum of `f`. -/
theorem isLocalMin_firstBelow (hf : Continuous f) (hl : l < f v) (hb : ∃ b, v ≤ b ∧ f b ≤ l) {ε : ℝ}
    (hε : 0 < ε) (hjump : ∀ l' < l, firstBelow f v l + ε ≤ firstBelow f v l') :
    IsLocalMin f (firstBelow f v l) := by
  have ht := apply_firstBelow hf hl hb
  have hvt := lt_firstBelow hf hl hb
  refine Filter.mem_of_superset (Ioo_mem_nhds hvt (by linarith : firstBelow f v l < firstBelow f v l + ε))
    fun w hw => ?_
  show f (firstBelow f v l) ≤ f w
  rw [ht]
  by_contra h
  push Not at h
  have h1 := hjump (f w) h
  have h2 : firstBelow f v (f w) ≤ w := firstBelow_le hw.1.le le_rfl
  linarith [hw.2]

end OneFunction

/-- **No-gap lemma for chains of straddling pairs.** Let `X` and `Y` be continuous. Suppose that `X` is below every
level on both sides of `v`, takes values below `X v` in every left neighbourhood of `v`, and that distinct local
minima of `X` have distinct values. If every straddling pair of `X` at `v` is a contour pair of `Y`, then for every
level `m < Y v` that `Y` reaches, the straddling pair of `Y` at `v` at level `m` is a straddling pair of `X`. -/
theorem exists_level_eq_of_straddle_pairs {X Y : ℝ → ℝ} (hX : Continuous X) (hY : Continuous Y) {v : ℝ}
    (hXlow : ∀ l, (∃ a ≤ v, X a ≤ l) ∧ ∃ b, v ≤ b ∧ X b ≤ l)
    (hvL : ∀ u < v, ∃ w ∈ Ioo u v, X w < X v)
    (hmin : ∀ p q, p < q → IsLocalMin X p → IsLocalMin X q → X p ≠ X q)
    (hpair : ∀ l < X v, Y (lastBelow X v l) = Y (firstBelow X v l) ∧
      ∀ u ∈ Ioo (lastBelow X v l) (firstBelow X v l), Y (lastBelow X v l) < Y u)
    {m : ℝ} (hm : m < Y v) (hYm : ∃ u, Y u ≤ m) :
    ∃ l < X v, lastBelow X v l = lastBelow Y v m ∧ firstBelow X v l = firstBelow Y v m := by
  set A : Set ℝ := {l | l < X v ∧ Y (lastBelow X v l) ≤ m} with hAdef
  -- `Y` along a straddling pair of `X` is at least its endpoint value
  have hYge : ∀ l < X v, ∀ u ∈ Icc (lastBelow X v l) (firstBelow X v l), Y (lastBelow X v l) ≤ Y u := by
    intro l hl u hu
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [h]
    rcases eq_or_lt_of_le hu.2 with h' | h'
    · rw [h', (hpair l hl).1]
    · exact ((hpair l hl).2 u ⟨h, h'⟩).le
  -- `A` is nonempty
  have hAne : A.Nonempty := by
    obtain ⟨u, hu⟩ := hYm
    obtain ⟨p, -, hpmin⟩ := (isCompact_Icc (a := min u v) (b := max u v)).exists_isMinOn
      (nonempty_Icc.mpr min_le_max) hX.continuousOn
    have hpK : ∀ q ∈ Icc (min u v) (max u v), X p - 1 < X q := fun q hq => by
      have := isMinOn_iff.mp hpmin q hq
      linarith
    have hlv : X p - 1 < X v := hpK v ⟨min_le_right _ _, le_max_right _ _⟩
    have hSu : lastBelow X v (X p - 1) ≤ u := by
      by_contra h
      push Not at h
      obtain ⟨hsv, hfs⟩ := lastBelow_mem hX (hXlow (X p - 1)).1
      have := hpK _ ⟨(min_le_left _ _).trans h.le, hsv.trans (le_max_right _ _)⟩
      linarith
    have huT : u ≤ firstBelow X v (X p - 1) := by
      by_contra h
      push Not at h
      obtain ⟨hvt, hft⟩ := firstBelow_mem hX (hXlow (X p - 1)).2
      have := hpK _ ⟨(min_le_right _ _).trans hvt, h.le.trans (le_max_left _ _)⟩
      linarith
    exact ⟨X p - 1, hlv, (hYge _ hlv u ⟨hSu, huT⟩).trans hu⟩
  -- `A` stays below a level strictly smaller than `X v`
  obtain ⟨δ, hδ, hδY⟩ := Metric.continuousAt_iff.mp (hY.continuousAt : ContinuousAt Y v) (Y v - m)
    (by linarith)
  obtain ⟨w, hw, hXw⟩ := hvL (v - δ) (by linarith)
  have hAub : ∀ l ∈ A, l < X w := by
    intro l hl
    by_contra h
    push Not at h
    have hws : w ≤ lastBelow X v l := le_lastBelow hw.2.le h
    have hsv : lastBelow X v l ≤ v := (lastBelow_mem hX (hXlow l).1).1
    have hd : dist (lastBelow X v l) v < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hw.1]
    have h2 := hδY hd
    rw [Real.dist_eq, abs_lt] at h2
    have h3 : Y (lastBelow X v l) ≤ m := hl.2
    linarith [h2.1]
  have hAbdd : BddAbove A := ⟨X w, fun l hl => (hAub l hl).le⟩
  set l₀ := sSup A with hl₀
  have hl₀w : l₀ ≤ X w := csSup_le hAne fun l hl => (hAub l hl).le
  have hl₀v : l₀ < X v := hl₀w.trans_lt hXw
  have ha₀ := (hXlow l₀).1
  have hb₀ := (hXlow l₀).2
  have hsv := lastBelow_lt hX hl₀v ha₀
  have hvt := lt_firstBelow hX hl₀v hb₀
  have hS₀ := apply_lastBelow hX hl₀v ha₀
  have hT₀ := apply_firstBelow hX hl₀v hb₀
  -- `Y (S l₀) ≥ m`, by right continuity of the left endpoint
  have hge : m ≤ Y (lastBelow X v l₀) := by
    by_contra h
    push Not at h
    obtain ⟨δ', hδ', hδ'Y⟩ := Metric.continuousAt_iff.mp
      (hY.continuousAt : ContinuousAt Y (lastBelow X v l₀)) (m - Y (lastBelow X v l₀)) (by linarith)
    obtain ⟨l₁, hl₀l₁, hl₁⟩ := exists_lastBelow_lt_add hX ha₀ hδ'
    have hl₀l : l₀ < min ((l₀ + l₁) / 2) ((l₀ + X v) / 2) := lt_min (by linarith) (by linarith)
    have hll₁ : min ((l₀ + l₁) / 2) ((l₀ + X v) / 2) < l₁ := (min_le_left _ _).trans_lt (by linarith)
    have hlv : min ((l₀ + l₁) / 2) ((l₀ + X v) / 2) < X v := (min_le_right _ _).trans_lt (by linarith)
    have hmono := lastBelow_mono hl₀l.le ha₀
    have hlt := hl₁ _ hl₀l.le hll₁
    have hd : dist (lastBelow X v (min ((l₀ + l₁) / 2) ((l₀ + X v) / 2))) (lastBelow X v l₀) < δ' := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have h2 := hδ'Y hd
    rw [Real.dist_eq, abs_lt] at h2
    have hlA : min ((l₀ + l₁) / 2) ((l₀ + X v) / 2) ∈ A := ⟨hlv, by linarith [h2.2]⟩
    have h3 : min ((l₀ + l₁) / 2) ((l₀ + X v) / 2) ≤ l₀ := le_csSup hAbdd hlA
    linarith
  -- `Y (S l₀) ≤ m`, by left continuity of one of the two endpoints
  have hle : Y (lastBelow X v l₀) ≤ m := by
    by_contra h
    push Not at h
    have key : ∀ g : ℝ → ℝ, (∀ l < X v, Y (g l) = Y (lastBelow X v l)) →
        (∀ ε > 0, ∃ l' < l₀, ∀ l, l' < l → l ≤ l₀ → dist (g l) (g l₀) < ε) → False := by
      intro g hg hcont
      obtain ⟨δ', hδ', hδ'Y⟩ := Metric.continuousAt_iff.mp (hY.continuousAt : ContinuousAt Y (g l₀))
        (Y (g l₀) - m) (by rw [hg l₀ hl₀v]; linarith)
      obtain ⟨l', hl'l₀, hl'⟩ := hcont δ' hδ'
      obtain ⟨l, hlA, hl'l⟩ := exists_lt_of_lt_csSup hAne hl'l₀
      have hll₀ : l ≤ l₀ := le_csSup hAbdd hlA
      have h2 := hδ'Y (hl' l hl'l hll₀)
      rw [Real.dist_eq, abs_lt] at h2
      have h1 := hg l hlA.1
      have h4 := hg l₀ hl₀v
      have h5 : Y (lastBelow X v l) ≤ m := hlA.2
      linarith [h2.1]
    by_cases hSc : ∀ ε > 0, ∃ l' < l₀, lastBelow X v l₀ - ε < lastBelow X v l'
    · refine key (lastBelow X v) (fun l _ => rfl) fun ε hε => ?_
      obtain ⟨l', hl'l₀, hl'⟩ := hSc ε hε
      refine ⟨l', hl'l₀, fun l hl'l hll₀ => ?_⟩
      have h1 := lastBelow_mono hl'l.le (hXlow l').1
      have h2 := lastBelow_mono hll₀ (hXlow l).1
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    · push Not at hSc
      obtain ⟨ε, hε, hjump⟩ := hSc
      have hSmin := isLocalMin_lastBelow hX hl₀v ha₀ hε hjump
      by_cases hTc : ∀ ε > 0, ∃ l' < l₀, firstBelow X v l' < firstBelow X v l₀ + ε
      · refine key (firstBelow X v) (fun l hl => (hpair l hl).1.symm) fun ε hε => ?_
        obtain ⟨l', hl'l₀, hl'⟩ := hTc ε hε
        refine ⟨l', hl'l₀, fun l hl'l hll₀ => ?_⟩
        have h1 := firstBelow_anti hl'l.le (hXlow l').2
        have h2 := firstBelow_anti hll₀ (hXlow l).2
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      · push Not at hTc
        obtain ⟨ε', hε', hjump'⟩ := hTc
        have hTmin := isLocalMin_firstBelow hX hl₀v hb₀ hε' hjump'
        exact hmin _ _ (hsv.trans hvt) hSmin hTmin (hS₀.trans hT₀.symm)
  have heq : Y (lastBelow X v l₀) = m := le_antisymm hle hge
  obtain ⟨hp1, hp2⟩ := hpair l₀ hl₀v
  have hu := lastBelow_eq_and_firstBelow_eq (f := Y) hsv hvt hp1 hp2
  rw [heq] at hu
  exact ⟨l₀, hl₀v, hu.1.symm, hu.2.symm⟩

end LatticeProb
