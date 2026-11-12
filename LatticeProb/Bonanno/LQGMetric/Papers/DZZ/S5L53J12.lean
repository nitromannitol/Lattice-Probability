/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53J12 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J11

/-!
# DZZ Lemma 5.3, node 3: the bottom-side coverage inputs of `l53_cell_desirable_prob`

`l53_cover_side` (any side `d`, abstract): let `S u v` be the pieces of the side (in units `t`
from the corner) with `𝓛₁(S u v) = (v - u) t`, monotone, and covered by consecutive unit pieces,
and let the segment of the boundary box at every non-corner position `a` be `S a (a+1)`. For a
grid-aligned piece `Λ = S p q` (`0 ≤ p ≤ q ≤ K = 2N + 2`) and the non-corner positions
`a ∈ [max p (N-n+1), min q (N+n))` (`l53SidePrev`):
* every segment lies in `Λ` and the positions are non-corner (inputs `hPrev`/`hNext`, `hrange`
  of `l53_cell_desirable_prob`);
* `𝓛₁(Λ) ≤ 𝓛₁(⋃ segments) + (2(N-n)+3) t` and `𝓛₁(Λ \ ⋃ segments) ≤ (2(N-n)+3) t` (DZZ
  l. 1946–1952: only the corner columns and the partial pieces are lost).
**`l53_cover_bot`**: the bottom side (`S = l53BotSeg`, `l53CellSeg` the segments `𝖡̄ ∩ ∂𝖢̄`).
The other three sides need only the analogue of `l53_seg_bot_eq` (not done here).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DZZ

open LQGMetric DyBox

/-- The boundary segment `𝖡̄ ∩ ∂𝖢̄` of the boundary box at position `p` (side, position). -/
def l53CellSeg (C : DyBox) (k n N : ℕ) (p : PercDir × ℤ) : Set ℂ :=
  (l53Sub C k N (l53Col n N p.1 p.2 (l53EvenTb n N p.1))).closedBox ∩ frontier C.closedBox

open scoped Classical in
/-- The non-corner positions of side `d` whose unit pieces lie in `S p q`. -/
def l53SidePrev (d : PercDir) (n N : ℕ) (p q : ℤ) : Finset (PercDir × ℤ) :=
  (Finset.Ico (max p ((N : ℤ) - n + 1)) (min q (N + n))).image fun a => (d, a)

lemma mem_l53SidePrev {d : PercDir} {n N : ℕ} {p q : ℤ} {x : PercDir × ℤ} :
    x ∈ l53SidePrev d n N p q ↔ x.1 = d ∧ max p ((N : ℤ) - n + 1) ≤ x.2 ∧
      x.2 < min q (N + n) := by
  obtain ⟨d', a⟩ := x
  simp only [l53SidePrev, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro ⟨b, ⟨h1, h2⟩, rfl, rfl⟩
    exact ⟨rfl, h1, h2⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨a, ⟨h1, h2⟩, rfl, rfl⟩

/-- **Coverage of a grid-aligned side piece by its boundary segments** (DZZ l. 1946–1952,
abstract side). -/
theorem l53_cover_side (S : ℝ → ℝ → Set ℂ) {t : ℝ} (t0 : 0 < t)
    (hSm : ∀ u v, u ≤ v → (μH[1] : Measure ℂ).real (S u v) = (v - u) * t)
    (hSfin : ∀ u v, μH[1] (S u v) ≠ ⊤)
    (hScov : ∀ a₀ a₁ : ℤ, a₀ < a₁ → S a₀ a₁ ⊆ ⋃ a ∈ Finset.Ico a₀ a₁, S a (a + 1))
    (hSmono : ∀ u v u' v' : ℝ, u' ≤ u → v ≤ v' → S u v ⊆ S u' v')
    (seg : PercDir × ℤ → Set ℂ) (hsegm : ∀ x, MeasurableSet (seg x)) (d : PercDir) {n N : ℕ}
    (hnN : n ≤ N) (hseg : ∀ a : ℤ, (N : ℤ) - n < a → a < N + n → seg (d, a) = S a (a + 1))
    {p q : ℤ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 2 * N + 2) :
    (∀ x ∈ l53SidePrev d n N p q, seg x ⊆ S p q ∧ (N : ℤ) - n < x.2 ∧ x.2 < N + n) ∧
    (μH[1] : Measure ℂ).real (S p q) ≤
        (μH[1] : Measure ℂ).real (⋃ x ∈ l53SidePrev d n N p q, seg x) +
          (2 * ((N : ℝ) - n) + 3) * t ∧
      (μH[1] : Measure ℂ).real (S p q \ ⋃ x ∈ l53SidePrev d n N p q, seg x) ≤
        (2 * ((N : ℝ) - n) + 3) * t := by
  have hsub : ∀ x ∈ l53SidePrev d n N p q, seg x ⊆ S p q ∧ (N : ℤ) - n < x.2 ∧ x.2 < N + n := by
    rintro ⟨d', a⟩ hx
    obtain ⟨rfl, h1, h2⟩ := mem_l53SidePrev.1 hx
    simp only at h1 h2 ⊢
    have ha₁ : (N : ℤ) - n < a := by omega
    have ha₂ : a < N + n := by omega
    refine ⟨?_, ha₁, ha₂⟩
    rw [hseg a ha₁ ha₂]
    refine hSmono _ _ _ _ ?_ ?_
    · exact_mod_cast (le_max_left _ _).trans h1
    · have : a + 1 ≤ q := by omega
      exact_mod_cast this
  set a₀ : ℤ := max p ((N : ℤ) - n + 1) with ha₀
  set a₁ : ℤ := min q (N + n) with ha₁
  set U : Set ℂ := ⋃ x ∈ l53SidePrev d n N p q, seg x with hU
  have hUΛ : U ⊆ S p q := by
    intro z hz
    simp only [hU, mem_iUnion] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    exact (hsub x hx).1 hzx
  have hmid : (a₁ - a₀ : ℝ) * t ≤ (μH[1] : Measure ℂ).real U := by
    rcases le_or_gt a₁ a₀ with h | h
    · have h' : (a₁ : ℝ) ≤ a₀ := by exact_mod_cast h
      nlinarith [measureReal_nonneg (μ := (μH[1] : Measure ℂ)) (s := U)]
    · have hcov := hScov a₀ a₁ h
      have hsub' : S a₀ a₁ ⊆ U := by
        intro z hz
        have := hcov hz
        simp only [mem_iUnion, Finset.mem_Ico] at this
        obtain ⟨a, ⟨h1, h2⟩, hza⟩ := this
        have ha₁' : (N : ℤ) - n < a := by omega
        have ha₂' : a < N + n := by omega
        simp only [hU, mem_iUnion]
        refine ⟨(d, a), mem_l53SidePrev.2 ⟨rfl, h1, h2⟩, ?_⟩
        rw [hseg a ha₁' ha₂']
        exact_mod_cast hza
      have h' := measureReal_mono hsub' (ne_top_of_le_ne_top (hSfin p q) (measure_mono hUΛ))
      rw [hSm _ _ (by exact_mod_cast h.le)] at h'
      exact h'
  have hloss : ((q : ℝ) - p) * t ≤ (a₁ - a₀ : ℝ) * t + (2 * ((N : ℝ) - n) + 3) * t := by
    have e1 : a₀ - p ≤ (N : ℤ) - n + 1 := by omega
    have e2 : q - a₁ ≤ (N : ℤ) - n + 2 := by omega
    have e1R : (a₀ : ℝ) - p ≤ (N : ℝ) - n + 1 := by exact_mod_cast e1
    have e2R : (q : ℝ) - a₁ ≤ (N : ℝ) - n + 2 := by exact_mod_cast e2
    nlinarith
  have hΛ := hSm p q (by exact_mod_cast hpq)
  refine ⟨hsub, by rw [hΛ]; linarith, ?_⟩
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion _ fun x _ => hsegm x
  rw [measureReal_sdiff hUΛ hUm (hSfin p q), hΛ]
  linarith

lemma l53_cellSeg_bot (C : DyBox) {k n N : ℕ} (hK : 2 ^ k = 2 * N + 2) (hnN : n ≤ N) {a : ℤ}
    (ha₁ : (N : ℤ) - n < a) (ha₂ : a < N + n) :
    l53CellSeg C k n N (PercDir.B, a) = l53BotSeg C k a (a + 1) := by
  rw [l53CellSeg, (l53_even_site n N a).1]
  exact l53_seg_bot_eq C hK (by omega) (by omega)

lemma l53_botSeg_mono (C : DyBox) (k : ℕ) {u v u' v' : ℝ} (hu : u' ≤ u) (hv : v ≤ v') :
    l53BotSeg C k u v ⊆ l53BotSeg C k u' v' := by
  have t0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (C.n + k) := by positivity
  rintro z ⟨h1, h2, h3⟩
  exact ⟨h1, by nlinarith, by nlinarith⟩

lemma measurableSet_l53CellSeg (C : DyBox) (k n N : ℕ) (x : PercDir × ℤ) :
    MeasurableSet (l53CellSeg C k n N x) :=
  ((isClosed_closedBox _).inter isClosed_frontier).measurableSet

/-- **Coverage of a bottom piece by its boundary segments** (`l53_cover_side` for `d = B`). -/
theorem l53_cover_bot (C : DyBox) {k n N : ℕ} (hK : 2 ^ k = 2 * N + 2) (hnN : n ≤ N)
    {p q : ℤ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 2 * N + 2) :
    (∀ x ∈ l53SidePrev .B n N p q, l53CellSeg C k n N x ⊆ l53BotSeg C k p q ∧
      (N : ℤ) - n < x.2 ∧ x.2 < N + n) ∧
    (μH[1] : Measure ℂ).real (l53BotSeg C k p q) ≤
        (μH[1] : Measure ℂ).real (⋃ x ∈ l53SidePrev .B n N p q, l53CellSeg C k n N x) +
          (2 * ((N : ℝ) - n) + 3) * (2 : ℝ)⁻¹ ^ (C.n + k) ∧
      (μH[1] : Measure ℂ).real
          (l53BotSeg C k p q \ ⋃ x ∈ l53SidePrev .B n N p q, l53CellSeg C k n N x) ≤
        (2 * ((N : ℝ) - n) + 3) * (2 : ℝ)⁻¹ ^ (C.n + k) := by
  have t0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (C.n + k) := by positivity
  refine l53_cover_side (l53BotSeg C k) t0 (fun u v huv => ?_) (fun u v => ?_)
    (fun a₀ a₁ h => l53_botSeg_cover C k h) (fun u v u' v' hu hv => l53_botSeg_mono C k hu hv)
    (l53CellSeg C k n N) (measurableSet_l53CellSeg C k n N) .B hnN
    (fun a ha₁ ha₂ => l53_cellSeg_bot C hK hnN ha₁ ha₂) hp hpq hq
  · rw [Measure.real, l53_botSeg_measure, ENNReal.toReal_ofReal (by nlinarith)]
  · rw [l53_botSeg_measure]; exact ENNReal.ofReal_ne_top

end LQGMetric.DZZ
