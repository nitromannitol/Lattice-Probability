/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.Packing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Localized

/-!
# The area-packing core of [18] Lemma 4.7

Source: [18] Lemma 4.7, proof : on the event `F^ε`, every interval
`[a_j, b_j]` of an outer-degree family has `diam(η([a_j, b_j])) ≥ diam(η([τ_z − ε, τ_z + ε]))`, so `η([a_j, b_j])`
contains a Euclidean ball of radius `r₀` (GHM15 Prop 3.4); these balls lie in `B̄^ε_z` and are disjoint because
"different segments of the form `η([a, b])` as above intersect only along their boundaries"; comparing areas gives
`deg^ε_out(z) ≲ ε^{−ζ}` (`16 ε^{−ζ}` disjoint balls).

* `NullOverlaps c`: segments of `c` over time intervals with disjoint interiors have Lebesgue-null intersection. It holds
  for every increasing reparametrization of a curve parametrized by Lebesgue measure (`nullOverlaps_of_reparam`), i.e.
  for the space-filling SLE parametrized by LQG mass (`[18]`; bundle fields `spaceFilling`, `areaParam`).
* `IsDegOutFamily.diam_le`: every outer-degree segment has diameter at least `diam(η([τ − ε, τ + ε]))`.
* `card_mul_sq_le_of_balls`, `locDegOut_le_of_balls`: the packing bound `N r₀² ≤ (4 diam)²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

/-- Segments over time intervals with disjoint interiors overlap in a Lebesgue-null set. -/
def NullOverlaps (c : ℝ → ℂ) : Prop :=
  ∀ a b a' b' : ℝ, b ≤ a' → volume (c '' Icc a b ∩ c '' Icc a' b') = 0

private theorem image_Icc_union {f : ℝ → ℂ} {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b) :
    f '' Icc a m ∪ f '' Icc m b = f '' Icc a b := by
  rw [← image_union, Icc_union_Icc_eq_Icc ham hmb]

/-- **Null overlaps of a reparametrized Lebesgue-parametrized curve.** If `c = ηL ∘ φ` with `φ` monotone and
`area(ηL([s, t])) = t − s` for `s ≤ t`, then `c` has null overlaps. -/
theorem nullOverlaps_of_reparam {ηL : ℝ → ℂ} {φ : ℝ → ℝ} (hφ : Monotone φ)
    (hvol : ∀ s t : ℝ, s ≤ t → volume (ηL '' Icc s t) = ENNReal.ofReal (t - s)) :
    NullOverlaps (ηL ∘ φ) := by
  intro a b a' b' hba'
  -- reduce to the Lebesgue-parametrized curve on the time intervals `[φ a, φ b]`, `[φ a', φ b']`
  have himg : ∀ x y : ℝ, x ≤ y → (ηL ∘ φ) '' Icc x y ⊆ ηL '' Icc (φ x) (φ y) := by
    rintro x y - _ ⟨t, ht, rfl⟩
    exact ⟨φ t, ⟨hφ ht.1, hφ ht.2⟩, rfl⟩
  rcases lt_or_ge b a with hab | hab
  · simp [Icc_eq_empty_of_lt hab]
  rcases lt_or_ge b' a' with hab' | hab'
  · simp [Icc_eq_empty_of_lt hab']
  set s₁ := φ a
  set s₂ := φ b
  set s₃ := φ a'
  set s₄ := φ b'
  have h12 : s₁ ≤ s₂ := hφ hab
  have h23 : s₂ ≤ s₃ := hφ hba'
  have h34 : s₃ ≤ s₄ := hφ hab'
  let A : Set ℂ := ηL '' Icc s₁ s₃
  let B : Set ℂ := ηL '' Icc s₃ s₄
  have hA : volume A = ENNReal.ofReal (s₃ - s₁) := hvol _ _ (h12.trans h23)
  have hB : volume B = ENNReal.ofReal (s₄ - s₃) := hvol _ _ h34
  have hAB : volume (A ∪ B) = ENNReal.ofReal (s₄ - s₁) := by
    rw [show A ∪ B = ηL '' Icc s₁ s₄ from image_Icc_union (h12.trans h23) h34]
    exact hvol _ _ (h12.trans (h23.trans h34))
  -- `B` is measurable as soon as the volumes are finite? We avoid measurability by the outer-measure inequality
  -- `μ(A ∩ B) + μ(A ∪ B) ≤ μ A + μ B` for a measurable superset of `B`.
  obtain ⟨B', hBB', hB'm, hB'eq⟩ := exists_measurable_superset volume B
  have hunion : volume (A ∪ B) ≤ volume (A ∪ B') := measure_mono (union_subset_union_right A hBB')
  have hfin : volume A + volume B' ≠ ⊤ := by
    rw [hB'eq, hA, hB]; exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hsum : volume A + volume B' = volume (A ∪ B) := by
    rw [hB'eq, hA, hB, hAB, ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1; ring
  have hU : volume (A ∪ B') + volume (A ∩ B') = volume A + volume B' := measure_union_add_inter A hB'm
  have hfinU : volume (A ∪ B') ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_union_le A B')
  have h1 : volume (A ∪ B') + volume (A ∩ B') ≤ volume (A ∪ B') + 0 := by
    rw [hU, add_zero, hsum]; exact hunion
  have hzero : volume (A ∩ B') = 0 :=
    le_antisymm ((ENNReal.add_le_add_iff_left hfinU).mp h1) bot_le
  refine le_antisymm ?_ bot_le
  calc volume ((ηL ∘ φ) '' Icc a b ∩ (ηL ∘ φ) '' Icc a' b')
      ≤ volume (A ∩ B') := by
        refine measure_mono (inter_subset_inter ?_ ((himg a' b' hab').trans hBB'))
        exact (himg a b hab).trans (image_mono (Icc_subset_Icc le_rfl h23))
    _ = 0 := hzero

/-! ## Outer-degree segments are long -/

theorem diam_locWindow_nonneg (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) : 0 ≤ diam (locWindow ε c t₀) :=
  diam_nonneg

/-- In a nonempty outer-degree family the window has positive diameter (else `int B̄ = ∅`). -/
theorem IsDegOutFamily.diam_pos {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} {N : ℕ} {a b : Fin N → ℝ}
    (h : IsDegOutFamily ε c t₀ a b) (i : Fin N) : 0 < diam (locWindow ε c t₀) := by
  rcases (diam_locWindow_nonneg ε c t₀).lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    have hsub := (h.2.2 i).1
    rw [locBall, ← hzero, mul_zero, closedBall_zero, interior_singleton] at hsub
    obtain ⟨t, ht⟩ := nonempty_Ioo.mpr (h.1 i)
    exact hsub (mem_image_of_mem c ht)

/-- Every outer-degree segment lies in `B̄^ε`. -/
theorem IsDegOutFamily.image_Icc_subset {ε : ℝ} {c : ℝ → ℂ} (hc : Continuous c) {t₀ : ℝ} {N : ℕ}
    {a b : Fin N → ℝ} (h : IsDegOutFamily ε c t₀ a b) (i : Fin N) :
    c '' Icc (a i) (b i) ⊆ locBall ε c t₀ := by
  have hcl : Icc (a i) (b i) = closure (Ioo (a i) (b i)) := (closure_Ioo (h.1 i).ne).symm
  rw [hcl]
  refine (image_closure_subset_closure_image hc).trans ?_
  refine (closure_mono ((h.2.2 i).1.trans interior_subset)).trans ?_
  exact isClosed_closedBall.closure_subset

/-- **Outer-degree segments are long**: for continuous `c`, every segment of an outer-degree family
has diameter at least `3 diam(c([t₀ − ε, t₀ + ε])) ≥ diam(c([t₀ − ε, t₀ + ε]))`. -/
theorem IsDegOutFamily.diam_le {ε : ℝ} {c : ℝ → ℂ} (hc : Continuous c) {t₀ : ℝ} (hε : 0 ≤ ε) {N : ℕ}
    {a b : Fin N → ℝ} (h : IsDegOutFamily ε c t₀ a b) (i : Fin N) :
    3 * diam (locWindow ε c t₀) ≤ diam (c '' Icc (a i) (b i)) := by
  set D := diam (locWindow ε c t₀) with hD
  have hDpos : 0 < D := h.diam_pos i
  have hbW : Bornology.IsBounded (locWindow ε c t₀) := (isCompact_Icc.image hc).isBounded
  have ht₀ : c t₀ ∈ locWindow ε c t₀ := mem_image_of_mem c ⟨by linarith, by linarith⟩
  have hbS : Bornology.IsBounded (c '' Icc (a i) (b i)) := (isCompact_Icc.image hc).isBounded
  have ha : c (a i) ∈ c '' Icc (a i) (b i) := mem_image_of_mem c ⟨le_rfl, (h.1 i).le⟩
  have hb : c (b i) ∈ c '' Icc (a i) (b i) := mem_image_of_mem c ⟨(h.1 i).le, le_rfl⟩
  have hfront : frontier (locBall ε c t₀) = sphere (c t₀) (4 * D) := by
    rw [locBall, frontier_closedBall _ (by positivity)]
  have key : ∀ x y : ℂ, x ∈ sphere (c t₀) (4 * D) → y ∈ locWindow ε c t₀ → 3 * D ≤ dist x y := by
    intro x y hx hy
    have h1 : dist x (c t₀) = 4 * D := mem_sphere.mp hx
    have h2 : dist y (c t₀) ≤ D := dist_le_diam_of_mem hbW hy ht₀
    have h3 := dist_triangle x y (c t₀)
    linarith
  rcases (h.2.2 i).2 with ⟨hfa, hwb⟩ | ⟨hfb, hwa⟩
  · rw [hfront] at hfa
    exact (key _ _ hfa hwb).trans (dist_le_diam_of_mem hbS ha hb)
  · rw [hfront] at hfb
    exact (key _ _ hfb hwa).trans (dist_le_diam_of_mem hbS hb ha)

/-- Two segments of an outer-degree family have time intervals in order. -/
theorem IsDegOutFamily.ordered {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} {N : ℕ} {a b : Fin N → ℝ}
    (h : IsDegOutFamily ε c t₀ a b) {i j : Fin N} (hij : i ≠ j) : b i ≤ a j ∨ b j ≤ a i := by
  have hd := h.2.1 i j hij
  rw [Ioo_disjoint_Ioo] at hd
  have hi := h.1 i
  have hj := h.1 j
  rcases le_total (b i) (b j) with h1 | h1 <;> rcases le_total (a i) (a j) with h2 | h2
  · rw [min_eq_left h1, max_eq_right h2] at hd; exact Or.inl hd
  · rw [min_eq_left h1, max_eq_left h2] at hd; linarith
  · rw [min_eq_right h1, max_eq_right h2] at hd; linarith
  · rw [min_eq_right h1, max_eq_left h2] at hd; exact Or.inr hd

/-! ## The packing bound -/

/-- **Area packing**. If every segment `c([a, b])` inside `B̄^ε` with diameter at least
`diam(c([t₀ − ε, t₀ + ε]))` contains a ball of radius `r₀`, and `c` has null overlaps, then every outer-degree family
of size `N` satisfies `N r₀² ≤ (4 diam(c([t₀ − ε, t₀ + ε])))²`. -/
theorem card_mul_sq_le_of_balls {ε : ℝ} {c : ℝ → ℂ} (hc : Continuous c) {t₀ : ℝ} (hε : 0 ≤ ε)
    (hnull : NullOverlaps c) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hball : ∀ a b : ℝ, a < b → c '' Icc a b ⊆ locBall ε c t₀ →
      diam (locWindow ε c t₀) ≤ diam (c '' Icc a b) → ∃ w : ℂ, ball w r₀ ⊆ c '' Icc a b)
    {N : ℕ} {a b : Fin N → ℝ} (h : IsDegOutFamily ε c t₀ a b) :
    (N : ℝ) * r₀ ^ 2 ≤ (4 * diam (locWindow ε c t₀)) ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp only [Nat.cast_zero, zero_mul]; positivity
  set D := diam (locWindow ε c t₀) with hD
  have hDpos : 0 < D := h.diam_pos ⟨0, hN⟩
  -- the balls
  have hex : ∀ i, ∃ w : ℂ, ball w r₀ ⊆ c '' Icc (a i) (b i) := by
    intro i
    refine hball (a i) (b i) (h.1 i) (h.image_Icc_subset hc i) ?_
    have := h.diam_le hc hε i
    linarith
  choose w hw using hex
  have hdisj : Pairwise (Function.onFun Disjoint fun i => ball (w i) r₀) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
    have hopen : IsOpen (ball (w i) r₀ ∩ ball (w j) r₀) := isOpen_ball.inter isOpen_ball
    refine (hopen.measure_eq_zero_iff volume).mp (le_antisymm ?_ bot_le)
    calc volume (ball (w i) r₀ ∩ ball (w j) r₀)
        ≤ volume (c '' Icc (a i) (b i) ∩ c '' Icc (a j) (b j)) :=
          measure_mono (inter_subset_inter (hw i) (hw j))
      _ = 0 := by
          rcases h.ordered hij with hle | hle
          · exact hnull _ _ _ _ hle
          · rw [inter_comm]; exact hnull _ _ _ _ hle
  have hsub : (⋃ i, ball (w i) r₀) ⊆ locBall ε c t₀ :=
    iUnion_subset fun i => (hw i).trans (h.image_Icc_subset hc i)
  have hvol : volume (⋃ i, ball (w i) r₀) = ∑ i, volume (ball (w i) r₀) :=
    (measure_iUnion hdisj (fun _ => measurableSet_ball)).trans (tsum_fintype _)
  have hle : ∑ i : Fin N, volume (ball (w i) r₀) ≤ volume (locBall ε c t₀) := by
    rw [← hvol]; exact measure_mono hsub
  simp only [Complex.volume_ball, locBall, Complex.volume_closedBall, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  have hpi : (0 : ℝ≥0∞) < (NNReal.pi : ℝ≥0∞) := by
    rw [ENNReal.coe_pos]; exact NNReal.pi_pos
  rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hpi.ne' ENNReal.coe_ne_top] at hle
  rw [← ENNReal.ofReal_pow hr₀.le, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_pow (by positivity)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle

/-- **Outer-degree packing bound.** Under the hypotheses of `card_mul_sq_le_of_balls`,
`deg^ε_out ≤ (4 diam(c([t₀ − ε, t₀ + ε])) / r₀)²`. -/
theorem locDegOut_le_of_balls {ε : ℝ} {c : ℝ → ℂ} (hc : Continuous c) {t₀ : ℝ} (hε : 0 ≤ ε)
    (hnull : NullOverlaps c) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hball : ∀ a b : ℝ, a < b → c '' Icc a b ⊆ locBall ε c t₀ →
      diam (locWindow ε c t₀) ≤ diam (c '' Icc a b) → ∃ w : ℂ, ball w r₀ ⊆ c '' Icc a b) :
    ((locDegOut ε c t₀ : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((4 * diam (locWindow ε c t₀) / r₀) ^ 2) := by
  have key : ∀ (N : ℕ) (a b : Fin N → ℝ), IsDegOutFamily ε c t₀ a b →
      ((N : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((4 * diam (locWindow ε c t₀) / r₀) ^ 2) := by
    intro N a b hab
    have h := card_mul_sq_le_of_balls hc hε hnull hr₀ hball hab
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_pow, le_div_iff₀ (by positivity)]
    exact h
  have hmono : Monotone (fun n : ℕ∞ => (n : ℝ≥0∞)) := fun _ _ h => ENat.toENNReal_le.mpr h
  rw [locDegOut]
  simp only [ENat.toENNReal_iSup]
  exact iSup_le fun N => iSup_le fun a => iSup_le fun b => iSup_le fun hab => key N a b hab

end MatedCRTHarmonic.GMS4b
