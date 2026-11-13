/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Probability.BMLocalMin.Det at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Data.Real.Archimedean

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Local minima of a path with distinct interval minima: deterministic part

Source: P. Mörters, Y. Peres, *Brownian Motion* (CUP 2010), Theorem 2.11 and its proof
(draft lines 2400–2450). The
probabilistic input of that proof is: a.s. the minima of the path over any two nonoverlapping
closed intervals from a countable family differ. This file contains the deterministic part of the
proof (parts (a), (c) and the countability in (b)), for a continuous `f : ℝ → ℝ` restricted to a
set `I ⊆ [0, ∞)` (in practice `I = [0, T]` or `I = [0, ∞)`).

* `ratMin f a b`: the infimum of `f` over the rational times in `[a, b]` (a countable infimum, so
  that it is measurable in the randomness); for continuous `f` and `a < b` it is `min_{[a,b]} f`
  (`ratMin_eq`).
* `Sep f D`: for `p < q < r < s` in `D` with `0 ≤ p`, `ratMin f p q ≠ ratMin f r s`.
* `Fine D I`: every `t ∈ I` lies in arbitrarily short intervals `[p, q] ⊆ I`, `p < q` in `D`.
* `localMin_props`: under `Sep` and `Fine`, every local minimum on `I` is strict, distinct local
  minima have distinct values and the set of local-minimum times is countable (MP 2.11 (a), (b)).
* `isMinOn_unique`: the minimum over `[a, b]` (`a, b ∈ D`) is attained at a unique time (MP 2.11 (c)).

Only strictly separated interval pairs (`q < r`) are used, which avoids MP's reduction of the
adjacent case `b₁ = a₂` (that reduction needs Theorem 2.8).
-/

open Set Filter Topology

namespace MatedCRTHarmonic.MoTPort
namespace BMLocalMin

/-- The rational times of `[a, b]`. -/
abbrev RI (a b : ℝ) := {u : ℚ // a ≤ u ∧ (u : ℝ) ≤ b}

/-- The infimum of `f` over the rational times in `[a, b]`. -/
noncomputable def ratMin (f : ℝ → ℝ) (a b : ℝ) : ℝ := ⨅ u : RI a b, f u

/-- For continuous `f` and `a < b`, `ratMin f a b` is the minimum of `f` over `[a, b]`. -/
lemma ratMin_eq {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b) {x : ℝ}
    (hx : x ∈ Icc a b) (hmin : ∀ y ∈ Icc a b, f x ≤ f y) : ratMin f a b = f x := by
  obtain ⟨u0, hu0⟩ := exists_rat_btwn hab
  haveI : Nonempty (RI a b) := ⟨⟨u0, hu0.1.le, hu0.2.le⟩⟩
  have hbdd : BddBelow (Set.range fun u : RI a b => f u) :=
    ⟨f x, by rintro _ ⟨u, rfl⟩; exact hmin _ u.2⟩
  refine le_antisymm ?_ (le_ciInf fun u => hmin _ u.2)
  by_contra hlt
  push Not at hlt
  have hev : ∀ᶠ y in 𝓝 x, f y < ratMin f a b := hf.continuousAt.eventually (gt_mem_nhds hlt)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have h1 : max a (x - δ) < min b (x + δ) := by
    obtain ⟨hxa, hxb⟩ := hx
    simp only [max_lt_iff, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  obtain ⟨u, hu1, hu2⟩ := exists_rat_btwn h1
  simp only [max_lt_iff, lt_min_iff] at hu1 hu2
  have hfu : f u < ratMin f a b :=
    hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  have : ratMin f a b ≤ f u := ciInf_le hbdd ⟨u, hu1.1.le, hu2.1.le⟩
  linarith

/-- Minima over strictly separated intervals with endpoints in `D` differ. -/
def Sep (f : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ p ∈ D, ∀ q ∈ D, ∀ r ∈ D, ∀ s ∈ D, 0 ≤ p → p < q → q < r → r < s →
    ratMin f p q ≠ ratMin f r s
lemma Sep.mono {f : ℝ → ℝ} {D D' : Set ℝ} (h : Sep f D) (hD : D' ⊆ D) : Sep f D' :=
  fun p hp q hq r hr s hs => h p (hD hp) q (hD hq) r (hD hr) s (hD hs)

/-- Every point of `I` lies in arbitrarily short nondegenerate intervals `[p, q] ⊆ I`, `p, q ∈ D`. -/
def Fine (D I : Set ℝ) : Prop :=
  ∀ t ∈ I, ∀ ε > 0, ∃ p ∈ D, ∃ q ∈ D, p < q ∧ p ≤ t ∧ t ≤ q ∧ t - ε < p ∧ q < t + ε ∧
    Icc p q ⊆ I

lemma isLocalMinOn_iff_eps {f : ℝ → ℝ} {I : Set ℝ} {t : ℝ} :
    IsLocalMinOn f I t ↔ ∃ ε > 0, ∀ u ∈ I, |u - t| < ε → f t ≤ f u := by
  unfold IsLocalMinOn IsMinFilter
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  simp only [Real.dist_eq]
  exact ⟨fun ⟨ε, hε, h⟩ => ⟨ε, hε, fun u hu hd => h hd hu⟩,
    fun ⟨ε, hε, h⟩ => ⟨ε, hε, fun {u} hd hu => h u hu hd⟩⟩

variable {f : ℝ → ℝ} {D I : Set ℝ}

/-- Core of MP Thm 2.11: two times `t₁ < t₂` of `I`, each minimizing `f` on an `ε`-neighbourhood
within `I`, have different values. -/
lemma core (hf : Continuous f) (hS : Sep f D) (hD : Fine D I) (hI : I ⊆ Ici 0)
    {t₁ t₂ : ℝ} (h₁ : t₁ ∈ I) (h₂ : t₂ ∈ I) (hlt : t₁ < t₂) {ε : ℝ} (hε : 0 < ε)
    (hm₁ : ∀ u ∈ I, |u - t₁| < ε → f t₁ ≤ f u) (hm₂ : ∀ u ∈ I, |u - t₂| < ε → f t₂ ≤ f u) :
    f t₁ ≠ f t₂ := by
  intro heq
  have hδ : 0 < min ε ((t₂ - t₁) / 2) := lt_min hε (by linarith)
  have hδ1 : min ε ((t₂ - t₁) / 2) ≤ ε := min_le_left _ _
  have hδ2 : min ε ((t₂ - t₁) / 2) ≤ (t₂ - t₁) / 2 := min_le_right _ _
  obtain ⟨p, hp, q, hq, hpq, hpt, htq, hp', hq', hsub⟩ := hD t₁ h₁ _ hδ
  obtain ⟨r, hr, s, hs, hrs, hrt, hts, hr', hs', hsub'⟩ := hD t₂ h₂ _ hδ
  have e1 : ratMin f p q = f t₁ := ratMin_eq hf hpq ⟨hpt, htq⟩ fun y hy =>
    hm₁ y (hsub hy) (by rw [abs_lt]; constructor <;> linarith [hy.1, hy.2])
  have e2 : ratMin f r s = f t₂ := ratMin_eq hf hrs ⟨hrt, hts⟩ fun y hy =>
    hm₂ y (hsub' hy) (by rw [abs_lt]; constructor <;> linarith [hy.1, hy.2])
  exact hS p hp q hq r hr s hs (hI (hsub ⟨le_rfl, hpq.le⟩)) hpq (by linarith) hrs
    (e1.trans (heq.trans e2.symm))

lemma core_ne (hf : Continuous f) (hS : Sep f D) (hD : Fine D I) (hI : I ⊆ Ici 0)
    {t₁ t₂ : ℝ} (h₁ : t₁ ∈ I) (h₂ : t₂ ∈ I) (hne : t₁ ≠ t₂) {ε : ℝ} (hε : 0 < ε)
    (hm₁ : ∀ u ∈ I, |u - t₁| < ε → f t₁ ≤ f u) (hm₂ : ∀ u ∈ I, |u - t₂| < ε → f t₂ ≤ f u) :
    f t₁ ≠ f t₂ := by
  rcases hne.lt_or_gt with h | h
  · exact core hf hS hD hI h₁ h₂ h hε hm₁ hm₂
  · exact (core hf hS hD hI h₂ h₁ h hε hm₂ hm₁).symm

/-- Distinct local minima on `I` have distinct values. -/
lemma localMin_ne (hf : Continuous f) (hS : Sep f D) (hD : Fine D I) (hI : I ⊆ Ici 0)
    {t₁ t₂ : ℝ} (h₁ : t₁ ∈ I) (h₂ : t₂ ∈ I) (hl₁ : IsLocalMinOn f I t₁)
    (hl₂ : IsLocalMinOn f I t₂) (hne : t₁ ≠ t₂) : f t₁ ≠ f t₂ := by
  obtain ⟨ε₁, hε₁, hm₁⟩ := isLocalMinOn_iff_eps.1 hl₁
  obtain ⟨ε₂, hε₂, hm₂⟩ := isLocalMinOn_iff_eps.1 hl₂
  exact core_ne hf hS hD hI h₁ h₂ hne (lt_min hε₁ hε₂)
    (fun u hu hd => hm₁ u hu (hd.trans_le (min_le_left _ _)))
    (fun u hu hd => hm₂ u hu (hd.trans_le (min_le_right _ _)))

/-- Every local minimum on `I` is strict. -/
lemma localMin_strict (hf : Continuous f) (hS : Sep f D) (hD : Fine D I) (hI : I ⊆ Ici 0)
    {t : ℝ} (ht : t ∈ I) (hl : IsLocalMinOn f I t) :
    ∃ ε > 0, ∀ u ∈ I, u ≠ t → |u - t| < ε → f t < f u := by
  obtain ⟨ε, hε, hm⟩ := isLocalMinOn_iff_eps.1 hl
  refine ⟨ε / 2, by linarith, fun u hu hne hd => ?_⟩
  have hle : f t ≤ f u := hm u hu (by linarith)
  refine lt_of_le_of_ne hle fun heq => ?_
  refine core_ne hf hS hD hI ht hu hne.symm (half_pos hε)
    (fun v hv hdv => hm v hv (by linarith)) (fun v hv hdv => ?_) heq
  rw [← heq]
  refine hm v hv ?_
  calc |v - t| = |(v - u) + (u - t)| := by ring_nf
    _ ≤ |v - u| + |u - t| := abs_add_le _ _
    _ < ε := by linarith

/-- The set of local-minimum times on `I` is countable. -/
lemma localMin_countable (hf : Continuous f) (hS : Sep f D) (hDc : D.Countable) (hD : Fine D I)
    (hI : I ⊆ Ici 0) : {t ∈ I | IsLocalMinOn f I t}.Countable := by
  let A : ℝ × ℝ → Set ℝ := fun pq => {t | t ∈ I ∧ IsLocalMinOn f I t ∧ pq.1 < pq.2 ∧
    t ∈ Icc pq.1 pq.2 ∧ ∀ y ∈ Icc pq.1 pq.2, f t ≤ f y}
  have hcov : {t ∈ I | IsLocalMinOn f I t} ⊆ ⋃ pq ∈ D ×ˢ D, A pq := by
    rintro t ⟨ht, hl⟩
    obtain ⟨ε, hε, hm⟩ := isLocalMinOn_iff_eps.1 hl
    obtain ⟨p, hp, q, hq, hpq, hpt, htq, hp', hq', hsub⟩ := hD t ht ε hε
    refine mem_iUnion₂.2 ⟨(p, q), ⟨hp, hq⟩, ht, hl, hpq, ⟨hpt, htq⟩, fun y hy => ?_⟩
    exact hm y (hsub hy) (by rw [abs_lt]; constructor <;> linarith [hy.1, hy.2])
  refine Countable.mono hcov ((hDc.prod hDc).biUnion fun pq _ => ?_)
  refine Subsingleton.countable fun t ht t' ht' => ?_
  by_contra hne
  refine localMin_ne hf hS hD hI ht.1 ht'.1 ht.2.1 ht'.2.1 hne ?_
  rw [← ratMin_eq hf ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2, ratMin_eq hf ht'.2.2.1 ht'.2.2.2.1 ht'.2.2.2.2]

/-- MP Thm 2.11 (a), (b) (countability), deterministic part. -/
theorem localMin_props (hf : Continuous f) (hS : Sep f D) (hDc : D.Countable) (hD : Fine D I)
    (hI : I ⊆ Ici 0) :
    (∀ t ∈ I, IsLocalMinOn f I t → ∃ ε > 0, ∀ u ∈ I, u ≠ t → |u - t| < ε → f t < f u) ∧
    (∀ t₁ ∈ I, ∀ t₂ ∈ I, IsLocalMinOn f I t₁ → IsLocalMinOn f I t₂ → t₁ ≠ t₂ → f t₁ ≠ f t₂) ∧
    {t ∈ I | IsLocalMinOn f I t}.Countable :=
  ⟨fun _ ht hl => localMin_strict hf hS hD hI ht hl,
    fun _ h₁ _ h₂ hl₁ hl₂ hne => localMin_ne hf hS hD hI h₁ h₂ hl₁ hl₂ hne,
    localMin_countable hf hS hDc hD hI⟩

/-- MP Thm 2.11 (c), deterministic part: the minimum over `[a, b]`, `a, b ∈ D`, is attained at a
unique time when `D` contains the rationals. -/
theorem isMinOn_unique (hf : Continuous f) (hS : Sep f D) (hQ : ∀ u : ℚ, (u : ℝ) ∈ D)
    {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) (ha0 : 0 ≤ a) {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc a b) (hmx : IsMinOn f (Icc a b) x) (hmy : IsMinOn f (Icc a b) y) : x = y := by
  rw [isMinOn_iff] at hmx hmy
  by_contra hne
  wlog hxy : x < y generalizing x y
  · exact this hy hx hmy hmx (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hxy) (Ne.symm hne))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < (2 * x + y) / 3 by linarith)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show (x + 2 * y) / 3 < y by linarith)
  have e1 : ratMin f a q = f x := ratMin_eq hf (by linarith [hx.1]) ⟨hx.1, hq1.le⟩
    fun z hz => hmx z ⟨hz.1, by linarith [hz.2, hy.2]⟩
  have e2 : ratMin f r b = f y := ratMin_eq hf (by linarith [hy.2]) ⟨hr2.le, hy.2⟩
    fun z hz => hmy z ⟨by linarith [hz.1, hx.1], hz.2⟩
  have hfxy : f x = f y := le_antisymm (hmx y hy) (hmy x hx)
  exact hS a ha q (hQ q) r (hQ r) b hb ha0 (by linarith [hx.1]) (by linarith)
    (by linarith [hy.2]) (e1.trans (hfxy.trans e2.symm))

/-! ### The interval families used for Brownian motion -/

lemma fine_left {D : Set ℝ} (hQ : ∀ u : ℚ, (u : ℝ) ∈ D) {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) :
    ∃ p ∈ D, 0 ≤ p ∧ p ≤ t ∧ t - ε < p ∧ (p < t ∨ t = 0) := by
  rcases ht.eq_or_lt with h | h
  · exact ⟨0, by simpa using hQ 0, le_rfl, h.le, by linarith, Or.inr h.symm⟩
  · obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show max 0 (t - ε) < t from max_lt h (by linarith))
    rw [max_lt_iff] at hp1
    exact ⟨p, hQ p, hp1.1.le, hp2.le, hp1.2, Or.inl hp2⟩

/-- The rationals are fine in `[0, ∞)`. -/
lemma fine_Ici {D : Set ℝ} (hQ : ∀ u : ℚ, (u : ℝ) ∈ D) : Fine D (Ici 0) := by
  intro t ht ε hε
  obtain ⟨p, hp, hp0, hpt, hp', -⟩ := fine_left hQ ht hε
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < t + ε by linarith)
  exact ⟨p, hp, q, hQ q, by linarith, hpt, hq1.le, hp', hq2,
    fun z hz => le_trans hp0 hz.1⟩

end BMLocalMin
end MatedCRTHarmonic.MoTPort
