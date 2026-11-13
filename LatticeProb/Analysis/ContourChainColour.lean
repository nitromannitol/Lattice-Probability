import LatticeProb.Analysis.StraddlingLevelPairs

/-!
# One colour along a chain of straddling pairs

A *contour pair* of `Y : ℝ → ℝ` is a pair of times `s < t` with `Y s = Y t` and `Y > Y s` on `(s, t)`; a *weak
contour pair* only asks `Y ≥ Y s` on `[s, t]`.

Let `X`, `Y₁`, `Y₂ : ℝ → ℝ` be continuous. Suppose that
* no pair of times is a weak contour pair of `Y₁` and of `Y₂` at once (the planar path `(Y₁, Y₂)` has no corner
  return: no `s < t` with `(Y₁, Y₂) t = (Y₁, Y₂) s` and `(Y₁, Y₂) u - (Y₁, Y₂) s ∈ [0, ∞)²` for `u ∈ [s, t]`);
* distinct local minima of `X` have distinct values, and `X` is unbounded below on both sides of every time;
* for every anchor `w` of a dense set `Q` there is a dense set of levels `D w` such that, at every level `l ∈ D w`
  below `X w`, the straddling pair of `X` at `w` at level `l` (the excursion interval of `X` above `l` containing `w`)
  is a contour pair of `Y₁` or of `Y₂` (its *colour*).

Then the colour does not switch along the chain of straddling pairs at an anchor `v ∈ Q`: either all the pairs at the
levels of `D v` below `X v` are contour pairs of `Y₁`, or all are contour pairs of `Y₂` (`contour_chain_one_colour`).

The proof looks at the supremum `m` of the levels of one colour below a level of the other colour. The pair at `m`,
a limit of pairs from above, and the limit of the pairs from below are weak contour pairs of the two colours; they are
nested, and `X = m` at their four ends. If the two pairs coincide, the path has a corner return. If both ends differ,
they are two local minima of `X` with the same value. If exactly one end differs, the gap between the two pairs is an
excursion interval of `X` above `m`; the chain at an anchor inside the gap gives it a colour
(`excursion_weak_colour`), and either colour gives a corner return, because two weak contour pairs of one colour
sharing an end give the third pair formed by their ends (`IsWeakContourPair.trans`, `.of_left`, `.of_right`).
-/

set_option autoImplicit false

open Set Filter Topology

namespace LatticeProb

/-- A *contour pair* of `Y`: times `s < t` with `Y s = Y t` and `Y > Y s` strictly between them (two times identified
in the contour tree of `Y`). -/
def IsContourPair (Y : ℝ → ℝ) (s t : ℝ) : Prop :=
  s < t ∧ Y s = Y t ∧ ∀ u ∈ Ioo s t, Y s < Y u

/-- A *weak contour pair* of `Y`: times `s < t` with `Y s = Y t` and `Y ≥ Y s` on `[s, t]`. -/
def IsWeakContourPair (Y : ℝ → ℝ) (s t : ℝ) : Prop :=
  s < t ∧ Y s = Y t ∧ ∀ u ∈ Icc s t, Y s ≤ Y u

theorem IsContourPair.weak {Y : ℝ → ℝ} {s t : ℝ} (h : IsContourPair Y s t) : IsWeakContourPair Y s t := by
  refine ⟨h.1, h.2.1, fun u hu => ?_⟩
  rcases eq_or_lt_of_le hu.1 with rfl | hsu
  · exact le_rfl
  rcases eq_or_lt_of_le hu.2 with rfl | hut
  · exact h.2.1.le
  exact (h.2.2 u ⟨hsu, hut⟩).le

namespace IsWeakContourPair

variable {Y : ℝ → ℝ} {a b d : ℝ}

/-- Adjacent weak contour pairs `(a, b)` and `(b, d)` give the weak contour pair `(a, d)`. -/
theorem trans (h₁ : IsWeakContourPair Y a b) (h₂ : IsWeakContourPair Y b d) :
    IsWeakContourPair Y a d := by
  refine ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, fun u hu => ?_⟩
  rcases le_total u b with hub | hbu
  · exact h₁.2.2 u ⟨hu.1, hub⟩
  · rw [h₁.2.1]
    exact h₂.2.2 u ⟨hbu, hu.2⟩

/-- Weak contour pairs `(a, d)` and `(a, b)` with `b < d` give the weak contour pair `(b, d)`. -/
theorem of_left (h : IsWeakContourPair Y a d) (h₁ : IsWeakContourPair Y a b) (hbd : b < d) :
    IsWeakContourPair Y b d := by
  refine ⟨hbd, h₁.2.1.symm.trans h.2.1, fun u hu => ?_⟩
  rw [← h₁.2.1]
  exact h.2.2 u ⟨h₁.1.le.trans hu.1, hu.2⟩

/-- Weak contour pairs `(a, d)` and `(b, d)` with `a < b` give the weak contour pair `(a, b)`. -/
theorem of_right (h : IsWeakContourPair Y a d) (h₂ : IsWeakContourPair Y b d) (hab : a < b) :
    IsWeakContourPair Y a b :=
  ⟨hab, h.2.1.trans h₂.2.1.symm, fun u hu => h.2.2 u ⟨hu.1, hu.2.trans h₂.1.le⟩⟩

end IsWeakContourPair

/-- **Weak contour pairs are closed.** If weak contour pairs `(s i, t i)` of a continuous `Y` occur frequently along a
filter on which `s → a` and `t → b`, with `a < b`, then `(a, b)` is a weak contour pair of `Y`. -/
theorem isWeakContourPair_of_frequently {ι : Type*} {F : Filter ι} {Y : ℝ → ℝ} (hY : Continuous Y)
    {s t : ι → ℝ} {a b : ℝ} (hab : a < b) (hs : Tendsto s F (𝓝 a)) (ht : Tendsto t F (𝓝 b))
    (h : ∃ᶠ i in F, IsWeakContourPair Y (s i) (t i)) : IsWeakContourPair Y a b := by
  have : NeBot (F ⊓ 𝓟 {i | IsWeakContourPair Y (s i) (t i)}) := frequently_iff_neBot.1 h
  have hG : ∀ᶠ i in F ⊓ 𝓟 {i | IsWeakContourPair Y (s i) (t i)}, IsWeakContourPair Y (s i) (t i) :=
    mem_inf_of_right (mem_principal_self _)
  have hsG := hs.mono_left (inf_le_left (b := 𝓟 {i | IsWeakContourPair Y (s i) (t i)}))
  have htG := ht.mono_left (inf_le_left (b := 𝓟 {i | IsWeakContourPair Y (s i) (t i)}))
  have hYs := (hY.tendsto a).comp hsG
  have hYt := (hY.tendsto b).comp htG
  have hYab : Y a = Y b := tendsto_nhds_unique_of_eventuallyEq hYs hYt (hG.mono fun i hi => hi.2.1)
  refine ⟨hab, hYab, fun u hu => ?_⟩
  rcases eq_or_lt_of_le hu.1 with rfl | hau
  · exact le_rfl
  rcases eq_or_lt_of_le hu.2 with rfl | hub
  · exact hYab.le
  have h1 := hsG.eventually (gt_mem_nhds hau)
  have h2 := htG.eventually (lt_mem_nhds hub)
  exact le_of_tendsto hYs ((hG.and (h1.and h2)).mono fun i hi => hi.1.2.2 u ⟨hi.2.1.le, hi.2.2.le⟩)

/-- **Right continuity of the left endpoint**, as a limit. -/
theorem tendsto_lastBelow_nhdsGT {f : ℝ → ℝ} (hf : Continuous f) {v l : ℝ} (ha : ∃ a ≤ v, f a ≤ l) :
    Tendsto (lastBelow f v) (𝓝[>] l) (𝓝 (lastBelow f v l)) := by
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with l' hl'
    exact hc.trans_le (lastBelow_mono (mem_Ioi.1 hl').le ha)
  · obtain ⟨l₁, hl₁, h⟩ := exists_lastBelow_lt_add hf ha (sub_pos.2 hc)
    filter_upwards [Ioo_mem_nhdsGT hl₁] with l' hl'
    have := h l' hl'.1.le hl'.2
    linarith

/-- **Right continuity of the right endpoint**, as a limit. -/
theorem tendsto_firstBelow_nhdsGT {f : ℝ → ℝ} (hf : Continuous f) {v l : ℝ}
    (hb : ∃ b, v ≤ b ∧ f b ≤ l) : Tendsto (firstBelow f v) (𝓝[>] l) (𝓝 (firstBelow f v l)) := by
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨l₁, hl₁, h⟩ := exists_firstBelow_sub_lt hf hb (sub_pos.2 hc)
    filter_upwards [Ioo_mem_nhdsGT hl₁] with l' hl'
    have := h l' hl'.1.le hl'.2
    linarith
  · filter_upwards [self_mem_nhdsWithin] with l' hl'
    exact (firstBelow_anti (mem_Ioi.1 hl').le hb).trans_lt hc

/-- The points of a dense subset of `ℝ` to the right of `m` accumulate at `m`. -/
theorem neBot_nhdsWithin_inter_Ioi {D : Set ℝ} (hD : Dense D) (m : ℝ) : NeBot (𝓝[D ∩ Ioi m] m) := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨l, hlD, hl1, hl2⟩ := hD.exists_between (lt_add_of_pos_right m hε)
  refine ⟨l, ⟨hlD, hl1⟩, ?_⟩
  rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 hl1)]
  linarith

/-- **Excursion intervals are coloured.** Under the colouring hypothesis at the anchors of a dense set `Q`, every
excursion interval `(a, b)` of `X` (`X a = X b`, `X > X a` on `(a, b)`) is a weak contour pair of `Y₁` or of `Y₂`: it
is the limit of the straddling pairs at an anchor inside it, at dense levels decreasing to `X a`. -/
theorem excursion_weak_colour {X Y₁ Y₂ : ℝ → ℝ} (hX : Continuous X) (hY₁ : Continuous Y₁)
    (hY₂ : Continuous Y₂) (hXlow : ∀ w l, (∃ a ≤ w, X a ≤ l) ∧ ∃ b, w ≤ b ∧ X b ≤ l) {Q : Set ℝ}
    (hQ : Dense Q) {D : ℝ → Set ℝ} (hD : ∀ w ∈ Q, Dense (D w))
    (hcol : ∀ w ∈ Q, ∀ l ∈ D w, l < X w → IsContourPair Y₁ (lastBelow X w l) (firstBelow X w l) ∨
      IsContourPair Y₂ (lastBelow X w l) (firstBelow X w l))
    {a b : ℝ} (hab : a < b) (hXab : X a = X b) (hin : ∀ u ∈ Ioo a b, X a < X u) :
    IsWeakContourPair Y₁ a b ∨ IsWeakContourPair Y₂ a b := by
  obtain ⟨w, hwQ, haw, hwb⟩ := hQ.exists_between hab
  obtain ⟨hSw, hTw⟩ := lastBelow_eq_and_firstBelow_eq haw hwb hXab hin
  have hmw : X a < X w := hin w ⟨haw, hwb⟩
  have := neBot_nhdsWithin_inter_Ioi (hD w hwQ) (X a)
  have hle : 𝓝[D w ∩ Ioi (X a)] (X a) ≤ 𝓝[>] (X a) := nhdsWithin_mono _ inter_subset_right
  have hS := (tendsto_lastBelow_nhdsGT hX (hXlow w (X a)).1).mono_left hle
  have hT := (tendsto_firstBelow_nhdsGT hX (hXlow w (X a)).2).mono_left hle
  rw [hSw] at hS
  rw [hTw] at hT
  have hev : ∀ᶠ l in 𝓝[D w ∩ Ioi (X a)] (X a), l ∈ D w ∧ l < X w :=
    (eventually_mem_nhdsWithin.mono fun l hl => hl.1).and
      ((gt_mem_nhds hmw).filter_mono nhdsWithin_le_nhds)
  rcases frequently_or_distrib.1 (hev.mono fun l hl => hcol w hwQ l hl.1 hl.2).frequently with h1 | h2
  · exact Or.inl (isWeakContourPair_of_frequently hY₁ hab hS hT (h1.mono fun l hl => hl.weak))
  · exact Or.inr (isWeakContourPair_of_frequently hY₂ hab hS hT (h2.mono fun l hl => hl.weak))

/-- **No switch from `Y₂` up to `Y₁`.** Under the hypotheses of `contour_chain_one_colour`, there are no levels
`l₁ < l₂ < X v` of `D v` such that the straddling pair at `l₁` is not a contour pair of `Y₁` and the one at `l₂` is. -/
theorem no_switch_up {X Y₁ Y₂ : ℝ → ℝ} (hX : Continuous X) (hY₁ : Continuous Y₁) (hY₂ : Continuous Y₂)
    (hXlow : ∀ w l, (∃ a ≤ w, X a ≤ l) ∧ ∃ b, w ≤ b ∧ X b ≤ l)
    (hmin : ∀ p q, p < q → IsLocalMin X p → IsLocalMin X q → X p ≠ X q)
    (hNC : ∀ s t, IsWeakContourPair Y₁ s t → IsWeakContourPair Y₂ s t → False)
    {Q : Set ℝ} (hQ : Dense Q) {D : ℝ → Set ℝ} (hD : ∀ w ∈ Q, Dense (D w))
    (hcol : ∀ w ∈ Q, ∀ l ∈ D w, l < X w → IsContourPair Y₁ (lastBelow X w l) (firstBelow X w l) ∨
      IsContourPair Y₂ (lastBelow X w l) (firstBelow X w l))
    {v : ℝ} (hv : v ∈ Q) {l₁ l₂ : ℝ} (hl₁₂ : l₁ < l₂) (hl₂ : l₂ < X v) (hl₁D : l₁ ∈ D v)
    (h₁ : ¬ IsContourPair Y₁ (lastBelow X v l₁) (firstBelow X v l₁))
    (h₂ : IsContourPair Y₁ (lastBelow X v l₂) (firstBelow X v l₂)) : False := by
  have hlow := fun l => (hXlow v l).1
  have hhigh := fun l => (hXlow v l).2
  have hmono : Monotone (lastBelow X v) := fun l l' h => lastBelow_mono h (hlow l)
  have hanti : Antitone (firstBelow X v) := fun l l' h => firstBelow_anti h (hhigh l)
  have hpair : ∀ l < X v, lastBelow X v l < firstBelow X v l ∧ X (lastBelow X v l) = l ∧
      X (firstBelow X v l) = l ∧ ∀ u ∈ Icc (lastBelow X v l) (firstBelow X v l), l ≤ X u := by
    intro l hl
    obtain ⟨hst, -, hin⟩ := straddle_pair hX hl (hlow l) (hhigh l)
    have hs := apply_lastBelow hX hl (hlow l)
    have ht := apply_firstBelow hX hl (hhigh l)
    refine ⟨hst, hs, ht, fun u hu => ?_⟩
    rcases eq_or_lt_of_le hu.1 with h | h
    · subst h
      exact hs.ge
    rcases eq_or_lt_of_le hu.2 with h' | h'
    · subst h'
      exact ht.ge
    linarith [hin u ⟨h, h'⟩]
  -- the levels of the first colour between `l₁` and `l₂`, and their supremum `m`
  set Bad : Set ℝ := {l | l ∈ Icc l₁ l₂ ∧ l ∈ D v ∧ ¬ IsContourPair Y₁ (lastBelow X v l) (firstBelow X v l)}
    with hBad
  have hl₁B : l₁ ∈ Bad := ⟨⟨le_rfl, hl₁₂.le⟩, hl₁D, h₁⟩
  have hBne : Bad.Nonempty := ⟨l₁, hl₁B⟩
  have hBbdd : BddAbove Bad := ⟨l₂, fun l hl => hl.1.2⟩
  set m := sSup Bad with hm
  have hl₁m : l₁ ≤ m := le_csSup hBbdd hl₁B
  have hml₂ : m ≤ l₂ := csSup_le hBne fun l hl => hl.1.2
  have hmv : m < X v := hml₂.trans_lt hl₂
  have hBadY₂ : ∀ l ∈ Bad, IsContourPair Y₂ (lastBelow X v l) (firstBelow X v l) := fun l hl =>
    (hcol v hv l hl.2.1 (hl.1.2.trans_lt hl₂)).resolve_left hl.2.2
  obtain ⟨hSTm, hXSm, hXTm, -⟩ := hpair m hmv
  -- the pair at `m` is a weak contour pair of `Y₁` (limit from above)
  have hA : IsWeakContourPair Y₁ (lastBelow X v m) (firstBelow X v m) := by
    rcases eq_or_lt_of_le hml₂ with heq | hlt
    · rw [heq]
      exact h₂.weak
    have := neBot_nhdsWithin_inter_Ioi (hD v hv) m
    have hle : 𝓝[D v ∩ Ioi m] m ≤ 𝓝[>] m := nhdsWithin_mono _ inter_subset_right
    refine isWeakContourPair_of_frequently hY₁ hSTm ((tendsto_lastBelow_nhdsGT hX (hlow m)).mono_left hle)
      ((tendsto_firstBelow_nhdsGT hX (hhigh m)).mono_left hle) (Eventually.frequently ?_)
    filter_upwards [eventually_mem_nhdsWithin, (gt_mem_nhds hlt).filter_mono nhdsWithin_le_nhds]
      with l hl hll₂
    have hlm : m < l := hl.2
    refine IsContourPair.weak ?_
    by_contra hc
    exact (not_le.2 hlm) (le_csSup hBbdd ⟨⟨hl₁m.trans hlm.le, hll₂.le⟩, hl.1, hc⟩)
  by_cases hmB : m ∈ Bad
  · exact hNC _ _ hA (hBadY₂ m hmB).weak
  -- the levels of the first colour lie below `m` and accumulate at `m`
  have hBlt : Bad ⊆ Iio m := fun l hl =>
    lt_of_le_of_ne (le_csSup hBbdd hl) fun h => hmB (by rw [hm, ← h]; exact hl)
  have : NeBot (𝓝[Bad] m) := mem_closure_iff_nhdsWithin_neBot.1 (csSup_mem_closure hBne hBbdd)
  have hle : 𝓝[Bad] m ≤ 𝓝[<] m := nhdsWithin_mono _ hBlt
  set a := sSup (lastBelow X v '' Iio m) with ha
  set d := sInf (firstBelow X v '' Iio m) with hd
  have hSbdd : BddAbove (lastBelow X v '' Iio m) := by
    refine ⟨lastBelow X v m, ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    exact hmono (le_of_lt hl)
  have hTbdd : BddBelow (firstBelow X v '' Iio m) := by
    refine ⟨firstBelow X v m, ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    exact hanti (le_of_lt hl)
  have hSa : Tendsto (lastBelow X v) (𝓝[Bad] m) (𝓝 a) := (hmono.tendsto_nhdsLT m).mono_left hle
  have hTd : Tendsto (firstBelow X v) (𝓝[Bad] m) (𝓝 d) := (hanti.tendsto_nhdsLT m).mono_left hle
  have haS : a ≤ lastBelow X v m := csSup_le (nonempty_Iio.image _) (by
    rintro _ ⟨l, hl, rfl⟩
    exact hmono (le_of_lt hl))
  have hTd' : firstBelow X v m ≤ d := le_csInf (nonempty_Iio.image _) (by
    rintro _ ⟨l, hl, rfl⟩
    exact hanti (le_of_lt hl))
  have had : a < d := haS.trans_lt (hSTm.trans_le hTd')
  -- the limit pair from below is a weak contour pair of `Y₂`
  have hB : IsWeakContourPair Y₂ a d :=
    isWeakContourPair_of_frequently hY₂ had hSa hTd
      (Eventually.frequently (eventually_mem_nhdsWithin.mono fun l hl => (hBadY₂ l hl).weak))
  -- `X ≥ m` on `[a, d]`, with equality at the ends
  have hXge : ∀ u ∈ Icc a d, m ≤ X u := by
    intro u hu
    refine csSup_le hBne fun l hl => ?_
    have hlm : l < m := hBlt hl
    have h1 : lastBelow X v l ≤ a := le_csSup hSbdd ⟨l, hlm, rfl⟩
    have h2 : d ≤ firstBelow X v l := csInf_le hTbdd ⟨l, hlm, rfl⟩
    exact (hpair l (hlm.trans hmv)).2.2.2 u ⟨h1.trans hu.1, hu.2.trans h2⟩
  have hid : Tendsto (fun l : ℝ => l) (𝓝[Bad] m) (𝓝 m) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hXa : X a = m := tendsto_nhds_unique_of_eventuallyEq ((hX.tendsto a).comp hSa) hid
    (eventually_mem_nhdsWithin.mono fun l hl => (hpair l ((hBlt hl).trans hmv)).2.1)
  have hXd : X d = m := tendsto_nhds_unique_of_eventuallyEq ((hX.tendsto d).comp hTd) hid
    (eventually_mem_nhdsWithin.mono fun l hl => (hpair l ((hBlt hl).trans hmv)).2.2.1)
  have hlocmin : ∀ p ∈ Ioo a d, X p = m → IsLocalMin X p := fun p hp hXp =>
    Filter.mem_of_superset (Ioo_mem_nhds hp.1 hp.2) fun y hy => by
      show X p ≤ X y
      rw [hXp]
      exact hXge y ⟨hy.1.le, hy.2.le⟩
  rcases eq_or_lt_of_le haS with haS' | haS'
  · rcases eq_or_lt_of_le hTd' with hTd'' | hTd''
    · -- the two pairs coincide
      rw [haS', ← hTd''] at hB
      exact hNC _ _ hA hB
    · -- the right ends differ: the gap `(T m, d)` is an excursion interval above `m`
      rw [← haS'] at hA
      have hin : ∀ u ∈ Ioo (firstBelow X v m) d, X (firstBelow X v m) < X u := by
        intro u hu
        rw [hXTm]
        have hau : a < u := (haS'.symm ▸ hSTm).trans hu.1
        refine lt_of_le_of_ne (hXge u ⟨hau.le, hu.2.le⟩) fun hXu => ?_
        exact hmin _ u hu.1 (hlocmin _ ⟨hA.1, hTd''⟩ hXTm) (hlocmin u ⟨hau, hu.2⟩ hXu.symm)
          (hXTm.trans hXu)
      rcases excursion_weak_colour hX hY₁ hY₂ hXlow hQ hD hcol hTd'' (hXTm.trans hXd.symm) hin with g | g
      · exact hNC _ _ (hA.trans g) hB
      · exact hNC _ _ hA (hB.of_right g hA.1)
  · rcases eq_or_lt_of_le hTd' with hTd'' | hTd''
    · -- the left ends differ: the gap `(a, S m)` is an excursion interval above `m`
      rw [hTd''] at hA
      have hin : ∀ u ∈ Ioo a (lastBelow X v m), X a < X u := by
        intro u hu
        rw [hXa]
        have hud : u < d := hu.2.trans hA.1
        refine lt_of_le_of_ne (hXge u ⟨hu.1.le, hud.le⟩) fun hXu => ?_
        exact hmin u _ hu.2 (hlocmin u ⟨hu.1, hud⟩ hXu.symm) (hlocmin _ ⟨haS', hA.1⟩ hXSm)
          (hXu.symm.trans hXSm.symm)
      rcases excursion_weak_colour hX hY₁ hY₂ hXlow hQ hD hcol haS' (hXa.trans hXSm.symm) hin with g | g
      · exact hNC _ _ (g.trans hA) hB
      · exact hNC _ _ hA (hB.of_left g hA.1)
    · -- both ends differ: two local minima of `X` with the same value `m`
      exact hmin _ _ hSTm (hlocmin _ ⟨haS', hSTm.trans hTd''⟩ hXSm)
        (hlocmin _ ⟨haS'.trans hSTm, hTd''⟩ hXTm) (hXSm.trans hXTm.symm)

/-- **One colour along a chain (no-switch lemma).** Let `X`, `Y₁`, `Y₂` be continuous, `X` unbounded below on both
sides of every time, with distinct values at distinct local minima, and suppose that the path `(Y₁, Y₂)` has no
corner return (no pair of times is a weak contour pair of both `Y₁` and `Y₂`). If, for every anchor `w` of a dense set
`Q`, the straddling pairs of `X` at `w` at the levels of a dense set `D w` below `X w` are contour pairs of `Y₁` or of
`Y₂`, then at each anchor `v ∈ Q` they are all contour pairs of `Y₁` or all contour pairs of `Y₂`. -/
theorem contour_chain_one_colour {X Y₁ Y₂ : ℝ → ℝ} (hX : Continuous X) (hY₁ : Continuous Y₁)
    (hY₂ : Continuous Y₂) (hXlow : ∀ w l, (∃ a ≤ w, X a ≤ l) ∧ ∃ b, w ≤ b ∧ X b ≤ l)
    (hmin : ∀ p q, p < q → IsLocalMin X p → IsLocalMin X q → X p ≠ X q)
    (hNC : ∀ s t, IsWeakContourPair Y₁ s t → IsWeakContourPair Y₂ s t → False)
    {Q : Set ℝ} (hQ : Dense Q) {D : ℝ → Set ℝ} (hD : ∀ w ∈ Q, Dense (D w))
    (hcol : ∀ w ∈ Q, ∀ l ∈ D w, l < X w → IsContourPair Y₁ (lastBelow X w l) (firstBelow X w l) ∨
      IsContourPair Y₂ (lastBelow X w l) (firstBelow X w l))
    {v : ℝ} (hv : v ∈ Q) :
    (∀ l ∈ D v, l < X v → IsContourPair Y₁ (lastBelow X v l) (firstBelow X v l)) ∨
      ∀ l ∈ D v, l < X v → IsContourPair Y₂ (lastBelow X v l) (firstBelow X v l) := by
  by_contra h
  push Not at h
  obtain ⟨⟨l₁, hl₁D, hl₁, h₁⟩, ⟨l₂, hl₂D, hl₂, h₂⟩⟩ := h
  have hcol' : ∀ w ∈ Q, ∀ l ∈ D w, l < X w → IsContourPair Y₂ (lastBelow X w l) (firstBelow X w l) ∨
      IsContourPair Y₁ (lastBelow X w l) (firstBelow X w l) := fun w hw l hl hlw =>
    (hcol w hw l hl hlw).symm
  have hNC' : ∀ s t, IsWeakContourPair Y₂ s t → IsWeakContourPair Y₁ s t → False :=
    fun s t h₂ h₁ => hNC s t h₁ h₂
  rcases lt_trichotomy l₁ l₂ with h12 | rfl | h21
  · exact no_switch_up hX hY₁ hY₂ hXlow hmin hNC hQ hD hcol hv h12 hl₂ hl₁D h₁
      ((hcol v hv l₂ hl₂D hl₂).resolve_right h₂)
  · exact (hcol v hv l₁ hl₁D hl₁).elim h₁ h₂
  · exact no_switch_up hX hY₂ hY₁ hXlow hmin hNC' hQ hD hcol' hv h21 hl₁ hl₂D h₂
      ((hcol v hv l₁ hl₁D hl₁).resolve_left h₁)

end LatticeProb
