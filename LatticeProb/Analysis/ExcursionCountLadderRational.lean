import LatticeProb.Analysis.ExcursionCountRational

/-!
# Ladder-set conditions at rational times

For a continuous path `X : ℝ → ℝ` and an anchor `a`, the forward ladder set `K = forwardLadderSet X a` is the zero
set on `[a, ∞)` of the continuous function `D t = X t - inf_{[a, t]} X` (`continuousOn_sInf_image_Icc`,
`mem_forwardLadderSet_iff_sub_sInf_eq_zero`). Hence the two conditions on `K` in the rational witnesses for the
excursion count (`le_excursionCount_iff`) are countable conditions on `D` at rational times:

* `forall_notMem_forwardLadderSet_iff`: `[r, u]` (`a ≤ r < u`) contains no ladder time iff `D ≥ 1 / (n + 1)` at the
  rational points of `[r, u]` for some `n`;
* `exists_mem_forwardLadderSet_iff`: `[u, r]` (`a ≤ u < r`) contains a ladder time iff for every `n` some rational
  point of `[u, r]` has `D < 1 / (n + 1)`;

and the running minimum over `[a, b]`, `a < b`, is the infimum over the rational points (`sInf_image_Icc_eq_iInf_rat`).
-/

open Set Filter Topology

namespace LatticeProb.LadderSet

/-- A function continuous on `[r, u]`, `r < u`, which is at least `c` at the rational points of `[r, u]`, is at
least `c` on `[r, u]`. -/
theorem le_of_forall_rat_mem_Icc {f : ℝ → ℝ} {r u c : ℝ} (hf : ContinuousOn f (Icc r u)) (hru : r < u)
    (h : ∀ q : ℚ, (q : ℝ) ∈ Icc r u → c ≤ f q) : ∀ x ∈ Icc r u, c ≤ f x := by
  have hF : IsClosed (Icc r u ∩ f ⁻¹' Ici c) := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hsub : Ioo r u ⊆ Icc r u ∩ f ⁻¹' Ici c := by
    refine ((Rat.denseRange_cast (𝕜 := ℝ)).open_subset_closure_inter isOpen_Ioo).trans (closure_minimal ?_ hF)
    rintro y ⟨hy, q, rfl⟩
    exact ⟨Ioo_subset_Icc_self hy, h q (Ioo_subset_Icc_self hy)⟩
  intro x hx
  have hx' : x ∈ closure (Ioo r u) := by
    rw [closure_Ioo hru.ne]
    exact hx
  exact (closure_minimal hsub hF hx').2

/-- A function continuous and positive on `[r, u]` is at least some `1 / (n + 1)` on `[r, u]`. -/
theorem exists_one_div_le_of_pos {f : ℝ → ℝ} {r u : ℝ} (hf : ContinuousOn f (Icc r u))
    (hpos : ∀ x ∈ Icc r u, 0 < f x) : ∃ n : ℕ, ∀ x ∈ Icc r u, 1 / ((n : ℝ) + 1) ≤ f x := by
  rcases (Icc r u).eq_empty_or_nonempty with he | hne
  · exact ⟨0, by simp [he]⟩
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hf
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hpos x₀ hx₀)
  exact ⟨n, fun x hx => hn.le.trans (hmin hx)⟩

variable {X : ℝ → ℝ} {a : ℝ}

/-- **The running minimum of a continuous path is continuous**: `t ↦ inf_{[a, t]} X` is continuous on `[a, ∞)`. -/
theorem continuousOn_sInf_image_Icc (hX : Continuous X) (a : ℝ) :
    ContinuousOn (fun t => sInf (X '' Icc a t)) (Ici a) := by
  have hcont : Continuous fun p : ℝ × ℝ => X (a + p.2 * (p.1 - a)) := hX.comp (by fun_prop)
  have hc : Continuous fun t : ℝ => sInf ((fun t s : ℝ => X (a + s * (t - a))) t '' Icc 0 1) :=
    isCompact_Icc.continuous_sInf hcont
  refine hc.continuousOn.congr fun t ht => ?_
  have himg : (fun s : ℝ => X (a + s * (t - a))) '' Icc 0 1 = X '' Icc a t := by
    have : (fun s : ℝ => X (a + s * (t - a))) = X ∘ (fun s => a + s) ∘ (fun s => s * (t - a)) := rfl
    rw [this, image_comp, image_comp, image_mul_right_Icc zero_le_one (sub_nonneg.2 ht), image_const_add_Icc]
    simp
  show sInf (X '' Icc a t) = sInf ((fun s : ℝ => X (a + s * (t - a))) '' Icc 0 1)
  rw [himg]

/-- The running minimum over `[a, t]` is at most the value at `t`. -/
theorem sInf_image_Icc_le_apply (hX : Continuous X) {t : ℝ} (ht : a ≤ t) : sInf (X '' Icc a t) ≤ X t :=
  csInf_le (isCompact_Icc.image hX).bddBelow ⟨t, right_mem_Icc.2 ht, rfl⟩

/-- A time `t ≥ a` is a forward ladder time from `a` iff the value at `t` is the running minimum over `[a, t]`. -/
theorem mem_forwardLadderSet_iff_sub_sInf_eq_zero (hX : Continuous X) {t : ℝ} (ht : a ≤ t) :
    t ∈ forwardLadderSet X a ↔ X t - sInf (X '' Icc a t) = 0 := by
  constructor
  · intro h
    have h1 := le_csInf ((nonempty_Icc.2 ht).image X) (by rintro _ ⟨s, hs, rfl⟩; exact h.2 s hs)
    linarith [sInf_image_Icc_le_apply hX ht]
  · intro h
    refine ⟨ht, fun s hs => ?_⟩
    have h1 := csInf_le (isCompact_Icc.image hX).bddBelow (mem_image_of_mem X hs)
    linarith

/-- **No ladder time in `[r, u]`, at rational times.** For `a ≤ r < u`, the interval `[r, u]` contains no forward
ladder time from `a` iff `X q - inf_{[a, q]} X ≥ 1 / (n + 1)` at the rational points `q` of `[r, u]`, for some `n`. -/
theorem forall_notMem_forwardLadderSet_iff (hX : Continuous X) {r u : ℝ} (har : a ≤ r) (hru : r < u) :
    (∀ x ∈ Icc r u, x ∉ forwardLadderSet X a) ↔
      ∃ n : ℕ, ∀ q : ℚ, (q : ℝ) ∈ Icc r u → 1 / ((n : ℝ) + 1) ≤ X q - sInf (X '' Icc a q) := by
  have hD : ContinuousOn (fun t => X t - sInf (X '' Icc a t)) (Icc r u) :=
    (hX.continuousOn.sub (continuousOn_sInf_image_Icc hX a)).mono fun x hx => har.trans hx.1
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_one_div_le_of_pos hD fun x hx => by
      have h0 := sInf_image_Icc_le_apply hX (har.trans hx.1)
      have h1 : X x - sInf (X '' Icc a x) ≠ 0 := fun he =>
        h x hx ((mem_forwardLadderSet_iff_sub_sInf_eq_zero hX (har.trans hx.1)).2 he)
      exact lt_of_le_of_ne (by linarith) (Ne.symm h1)
    exact ⟨n, fun q hq => hn q hq⟩
  · rintro ⟨n, hn⟩ x hx hxK
    have h1 : 1 / ((n : ℝ) + 1) ≤ X x - sInf (X '' Icc a x) := le_of_forall_rat_mem_Icc hD hru hn x hx
    rw [(mem_forwardLadderSet_iff_sub_sInf_eq_zero hX (har.trans hx.1)).1 hxK] at h1
    have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- **A ladder time in `[u, r]`, at rational times.** For `a ≤ u < r`, the interval `[u, r]` contains a forward
ladder time from `a` iff for every `n` some rational point `q` of `[u, r]` has `X q - inf_{[a, q]} X < 1 / (n + 1)`. -/
theorem exists_mem_forwardLadderSet_iff (hX : Continuous X) {u r : ℝ} (hau : a ≤ u) (hur : u < r) :
    (∃ x ∈ forwardLadderSet X a, u ≤ x ∧ x ≤ r) ↔
      ∀ n : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Icc u r ∧ X q - sInf (X '' Icc a q) < 1 / ((n : ℝ) + 1) := by
  have h := forall_notMem_forwardLadderSet_iff hX hau hur
  constructor
  · rintro ⟨x, hxK, hx⟩ n
    by_contra hn
    push Not at hn
    exact h.2 ⟨n, hn⟩ x hx hxK
  · intro hn
    by_contra hne
    obtain ⟨m, hm⟩ := h.1 fun x hx hxK => hne ⟨x, hxK, hx⟩
    obtain ⟨q, hq, hlt⟩ := hn m
    exact absurd (hm q hq) (not_le.2 hlt)

/-- **The running minimum at rational times.** For a continuous path and `a < b`, the infimum of `X` over `[a, b]`
is the infimum of `X` over the rational points of `[a, b]`. -/
theorem sInf_image_Icc_eq_iInf_rat (hX : Continuous X) {b : ℝ} (hab : a < b) :
    sInf (X '' Icc a b) = ⨅ q : {q : ℚ // (q : ℝ) ∈ Icc a b}, X q := by
  have hbdd : BddBelow (X '' Icc a b) := (isCompact_Icc.image hX).bddBelow
  obtain ⟨q₀, hq₀⟩ := exists_rat_btwn hab
  have : Nonempty {q : ℚ // (q : ℝ) ∈ Icc a b} := ⟨⟨q₀, hq₀.1.le, hq₀.2.le⟩⟩
  have hbdd' : BddBelow (range fun q : {q : ℚ // (q : ℝ) ∈ Icc a b} => X q) :=
    hbdd.mono (by rintro _ ⟨q, rfl⟩; exact mem_image_of_mem X q.2)
  apply le_antisymm
  · exact le_ciInf fun q => csInf_le hbdd (mem_image_of_mem X q.2)
  · refine le_csInf ((nonempty_Icc.2 hab.le).image X) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact le_of_forall_rat_mem_Icc hX.continuousOn hab (fun q hq => ciInf_le hbdd' ⟨q, hq⟩) x hx

end LatticeProb.LadderSet
