/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.CurveSpace at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Localized

/-!
# Semicontinuity and measurability of `DA^ε` and `deg^ε_in` on the curve space

The law-transfer step in the proof of [18] Theorem 4.4 (: "the laws of
these three quantities do not depend on `ε`") needs the localized quantities of §4.2 to be measurable functions of the
curve. Here the curve space is `C(ℝ, ℂ)` with the compact-open topology and its Borel σ-algebra (the σ-algebra of the
 bundle's curves; the curve-space formulation).

* `eventually_forall_dist_lt`: compact-open neighbourhoods give uniform closeness on compact time sets.
* `continuous_diam_image`, `upperSemicontinuous_volume_image`: `c ↦ diam c(K)` is continuous and
  `c ↦ area c(K)` is upper semicontinuous for compact `K`.
* `lowerSemicontinuous_locDA`, `measurable_locDA`: `DA^ε` (4.4) is lower semicontinuous, hence Borel.
* `isClosed_exists_mem_of_isCompact`, `measurableSet_exists_of_isClosed`: projections of closed sets along compact,
  resp. `ℝ^N`, factors.
* `le_locDegIn_iff`, `measurable_locDegIn`: `{deg^ε_in ≥ k}` is an `F_σ` set, so `deg^ε_in` is Borel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

/-! ## Uniform closeness on compacts -/

/-- In the compact-open topology, nearby curves are uniformly close on a compact time set. -/
theorem eventually_forall_dist_lt (c : C(ℝ, ℂ)) {K : Set ℝ} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ c' in 𝓝 c, ∀ t ∈ K, dist (c' t) (c t) < δ := by
  set Nb : Set (C(ℝ, ℂ) × ℝ) := {p | dist (p.1 p.2) (c p.2) < δ} with hNb
  have hopen : IsOpen Nb :=
    isOpen_lt (continuous_eval.dist (c.continuous.comp continuous_snd)) continuous_const
  have hsub : ({c} : Set C(ℝ, ℂ)) ×ˢ K ⊆ Nb := by
    rintro ⟨c', t⟩ ⟨hc', -⟩
    rw [mem_singleton_iff] at hc'
    subst hc'
    simp [hNb, hδ]
  obtain ⟨u, v, hu, -, hcu, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK hopen hsub
  filter_upwards [hu.mem_nhds (hcu (mem_singleton c))] with c' hc' t ht
  exact (huv (show (c', t) ∈ u ×ˢ v from ⟨hc', hKv ht⟩) : (c', t) ∈ Nb)

/-- If `f` is uniformly `δ`-close to `g` on `K` and `g(K)` is bounded, `diam f(K) ≤ diam g(K) + 2δ`. -/
theorem diam_image_le_of_forall_dist_le {f g : ℝ → ℂ} {K : Set ℝ} (hg : Bornology.IsBounded (g '' K))
    {δ : ℝ} (hδ : 0 ≤ δ) (h : ∀ t ∈ K, dist (f t) (g t) ≤ δ) :
    diam (f '' K) ≤ diam (g '' K) + 2 * δ := by
  refine diam_le_of_forall_dist_le (by positivity) ?_
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  have h1 := dist_triangle4 (f s) (g s) (g t) (f t)
  have h2 := dist_le_diam_of_mem hg (mem_image_of_mem g hs) (mem_image_of_mem g ht)
  have h3 := h s hs
  have h4 := h t ht
  rw [dist_comm (g t)] at h1
  linarith

/-- `c ↦ diam c(K)` is continuous on `C(ℝ, ℂ)` for compact `K`. -/
theorem continuous_diam_image {K : Set ℝ} (hK : IsCompact K) :
    Continuous fun c : C(ℝ, ℂ) => diam (c '' K) := by
  refine continuous_iff_continuousAt.mpr fun c => ?_
  refine Metric.tendsto_nhds.mpr fun η hη => ?_
  filter_upwards [eventually_forall_dist_lt c hK (show 0 < η / 3 by positivity)] with c' hc'
  have hb : ∀ d : C(ℝ, ℂ), Bornology.IsBounded (d '' K) := fun d => (hK.image d.continuous).isBounded
  have h1 := diam_image_le_of_forall_dist_le (hb c) (show 0 ≤ η / 3 by positivity)
    (fun t ht => (hc' t ht).le)
  have h2 := diam_image_le_of_forall_dist_le (f := c) (g := c') (hb c') (show 0 ≤ η / 3 by positivity)
    (fun t ht => by rw [dist_comm]; exact (hc' t ht).le)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- `c ↦ area c(K)` is upper semicontinuous on `C(ℝ, ℂ)` for compact `K` (outer regularity of Lebesgue measure). -/
theorem upperSemicontinuous_volume_image {K : Set ℝ} (hK : IsCompact K) :
    UpperSemicontinuous fun c : C(ℝ, ℂ) => volume (c '' K) := by
  intro c y hy
  obtain ⟨U, hKU, hU, hUy⟩ := exists_isOpen_lt_of_lt (μ := (volume : Measure ℂ)) _ y hy
  obtain ⟨δ, hδ, hthick⟩ := (hK.image c.continuous).exists_thickening_subset_open hU hKU
  filter_upwards [eventually_forall_dist_lt c hK hδ] with c' hc'
  refine lt_of_le_of_lt (measure_mono ?_) hUy
  rintro _ ⟨t, ht, rfl⟩
  exact hthick (mem_thickening_iff.mpr ⟨c t, mem_image_of_mem c ht, hc' t ht⟩)

/-- `diam²/area` of a fixed time interval is lower semicontinuous in the curve. -/
theorem lowerSemicontinuous_segRatio (a b : ℝ) :
    LowerSemicontinuous fun c : C(ℝ, ℂ) => segRatio c a b := by
  intro c y hy
  set X : C(ℝ, ℂ) → ℝ≥0∞ := fun c => ENNReal.ofReal (diam (c '' Icc a b) ^ 2) with hX
  set v : C(ℝ, ℂ) → ℝ≥0∞ := fun c => volume (c '' Icc a b) with hv
  have hXc : Continuous X :=
    ENNReal.continuous_ofReal.comp ((continuous_diam_image isCompact_Icc).pow 2)
  have hvu : UpperSemicontinuous v := upperSemicontinuous_volume_image isCompact_Icc
  change y < X c / v c at hy
  change ∀ᶠ c' in 𝓝 c, y < X c' / v c'
  have hytop : y ≠ ⊤ := ne_top_of_lt hy
  have hvtop : v c ≠ ⊤ := by
    intro h; rw [h, ENNReal.div_top] at hy; exact not_lt_bot hy
  have hX0 : X c ≠ 0 := by
    intro h; rw [h, ENNReal.zero_div] at hy; exact not_lt_bot hy
  have hyv : y * v c < X c := (ENNReal.lt_div_iff_mul_lt (Or.inr hytop) (Or.inl hvtop)).mp hy
  obtain ⟨X'', hX''1, hX''2⟩ := exists_between hyv
  -- a value `w > v c` with `y * w < X''`
  have hcont : Tendsto (fun w : ℝ≥0∞ => y * w) (𝓝 (v c)) (𝓝 (y * v c)) :=
    ENNReal.Tendsto.const_mul tendsto_id (Or.inr hytop)
  have hev : ∀ᶠ w in 𝓝[>] (v c), y * w < X'' :=
    (hcont.eventually (gt_mem_nhds hX''1)).filter_mono nhdsWithin_le_nhds
  have : (𝓝[>] (v c)).NeBot := nhdsGT_neBot_of_exists_gt ⟨⊤, lt_top_iff_ne_top.mpr hvtop⟩
  obtain ⟨w, hw1, hw2⟩ := (hev.and self_mem_nhdsWithin).exists
  have hX''pos : X'' ≠ 0 := ne_bot_of_gt hX''1
  filter_upwards [hvu c w hw2, (hXc.tendsto c).eventually (lt_mem_nhds hX''2)] with c' hc'1 hc'2
  rw [ENNReal.lt_div_iff_mul_lt (Or.inr hytop) (Or.inl (ne_top_of_lt hc'1))]
  calc y * v c' ≤ y * w := by gcongr
    _ < X'' := hw1
    _ < X c' := hc'2

/-- **`DA^ε` is lower semicontinuous** on `C(ℝ, ℂ)`. -/
theorem lowerSemicontinuous_locDA (ε t₀ : ℝ) :
    LowerSemicontinuous fun c : C(ℝ, ℂ) => locDA ε c t₀ := by
  simp only [locDA]
  exact lowerSemicontinuous_iSup fun s => lowerSemicontinuous_iSup fun _ =>
    lowerSemicontinuous_segRatio (s - ε) s

/-- **`DA^ε` is Borel** on `C(ℝ, ℂ)`. -/
theorem measurable_locDA (ε t₀ : ℝ) : Measurable fun c : C(ℝ, ℂ) => locDA ε c t₀ :=
  (lowerSemicontinuous_locDA ε t₀).measurable

/-! ## Projections of closed sets -/

/-- The projection of a closed set along a compact factor is closed (tube lemma). -/
theorem isClosed_exists_mem_of_isCompact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set Y} (hK : IsCompact K) {F : Set (X × Y)} (hF : IsClosed F) :
    IsClosed {x | ∃ y ∈ K, (x, y) ∈ F} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  have hsub : ({x} : Set X) ×ˢ K ⊆ Fᶜ := by
    rintro ⟨x', y⟩ ⟨hx', hy⟩
    rw [mem_singleton_iff] at hx'
    subst hx'
    exact fun hF' => hx ⟨y, hy, hF'⟩
  obtain ⟨u, v, hu, -, hxu, hKv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hK hF.isOpen_compl hsub
  refine ⟨u, fun x' hx' ⟨y, hy, hF'⟩ => huv ⟨hx', hKv hy⟩ hF', hu, hxu (mem_singleton x)⟩

/-- The projection of a closed subset of `X × ℝ^N` to `X` is `F_σ`, hence measurable. -/
theorem measurableSet_exists_of_isClosed {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {N : ℕ} {F : Set (X × (Fin N → ℝ))} (hF : IsClosed F) :
    MeasurableSet {x | ∃ y, (x, y) ∈ F} := by
  have heq : {x | ∃ y, (x, y) ∈ F} = ⋃ m : ℕ, {x | ∃ y ∈ closedBall (0 : Fin N → ℝ) m, (x, y) ∈ F} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨m, hm⟩ := exists_nat_ge ‖y‖
      exact ⟨m, y, mem_closedBall_zero_iff.mpr hm, hy⟩
    · rintro ⟨m, y, -, hy⟩
      exact ⟨y, hy⟩
  rw [heq]
  exact MeasurableSet.iUnion fun m =>
    (isClosed_exists_mem_of_isCompact (isCompact_closedBall _ _) hF).measurableSet

/-! ## `deg^ε_in` -/

/-- Restricting an inner-degree family to its first `M` members. -/
theorem IsDegInFamily.castLE {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} {M N : ℕ} {a : Fin N → ℝ}
    (h : IsDegInFamily ε c t₀ a) (hMN : M ≤ N) : IsDegInFamily ε c t₀ (a ∘ Fin.castLE hMN) :=
  ⟨fun _ _ hij => h.1 _ _ fun he => hij (Fin.castLE_injective hMN he), fun _ => h.2 _⟩

/-- `deg^ε_in ≥ k` iff there is an inner-degree family of size `k`. -/
theorem le_locDegIn_iff {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} (k : ℕ) :
    (k : ℕ∞) ≤ locDegIn ε c t₀ ↔ ∃ a : Fin k → ℝ, IsDegInFamily ε c t₀ a := by
  constructor
  · intro hk
    by_contra hno
    push Not at hno
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      exact hno Fin.elim0 ⟨fun i => i.elim0, fun i => i.elim0⟩
    have hle : locDegIn ε c t₀ ≤ ((k - 1 : ℕ) : ℕ∞) := by
      refine locDegIn_le fun N a ha => ?_
      by_contra hlt
      push Not at hlt
      have hkN : k ≤ N := by
        have : (k - 1 : ℕ) < N := by exact_mod_cast hlt
        omega
      exact hno _ (ha.castLE hkN)
    have := hk.trans hle
    have : k ≤ k - 1 := by exact_mod_cast this
    omega
  · rintro ⟨a, ha⟩
    exact le_locDegIn ha

end MatedCRTHarmonic.GMS4b
