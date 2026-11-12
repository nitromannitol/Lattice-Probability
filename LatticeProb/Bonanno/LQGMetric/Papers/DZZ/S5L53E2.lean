/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53E2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53E1
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# DZZ Lemma 5.3, part 1: the choice of the points `x_i` (P2-DZZ53E)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of (eq-union-bound-distance),
l. 2504–2530: on the event that `u`, `v` and the cells `𝖢₂, …, 𝖢_{d−1}` are *desirable*
(l. 2504–2522), DZZ set `Λ*_{d−1} = Λ_v`, `Λ*_i = Λ_{i+1,start}(Λ*_{i+1})` (recursively, downward),
`x₀ = u` and `x_i = argmin_{x' ∈ Λ*_i} D(x_{i−1}, x')`; `Λ_u ∩ Λ*_1 ≠ ∅` "comes from the lower
bounds on their Lebesgue measures".

* `inter_nonempty_of_measureReal`: two subsets of `Λ` of measures `≥ 0.99 m(Λ)` and `≥ 0.1 m(Λ)`
  meet (`0 < m(Λ) < ∞`, one of them measurable).
* **`l53_chain_select`**: the selection, abstractly (any measure `m`, any relation `R` for the
  pieces). Instead of the `argmin`, we take a point of `Λ*_i` at good distance from `x_{i−1}`
  (which is what DZZ use of the `argmin`); the chain is built backward from `v`, as DZZ build `Λ*`.
* `l53DesirableEvent`: `𝒟₁` and the desirability of `u`, `v`, `𝖢₂, …, 𝖢_{d−1}` (l. 2504–2522),
  with `𝓛₁ = μH[1]` and abstract interfaces `Λ_i` (DZZ: `Λ_i = ∂𝖢_i ∩ ∂𝖢_{i+1}`).
* **`dzzLem53Event_of_desirable`**: `DZZLem53Event` from `P(desirable event ᶜ) ≤ 2e^{−(k log 2)^{0.22}}`.

`𝓛₁` of an arbitrary set is the outer measure. Only `Λ_u` is required to be measurable (for the
additivity in `inter_nonempty_of_measureReal`); the desirability of `𝖢_i` is DZZ's, "for any
`Λ_{i,end}`".
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal MeasureTheory

namespace LQGMetric
namespace DZZ

/-- Two big subsets of `Λ` meet (DZZ l. 2529, "from the lower bounds on their Lebesgue measures"). -/
lemma inter_nonempty_of_measureReal {α : Type*} [MeasurableSpace α] {m : Measure α}
    {Λ A B : Set α} (hΛ : m Λ ≠ ⊤) (hΛ0 : 0 < m.real Λ) (hA : A ⊆ Λ) (hB : B ⊆ Λ)
    (hAm : MeasurableSet A) (hAΛ : 0.99 * m.real Λ ≤ m.real A) (hBΛ : 0.1 * m.real Λ ≤ m.real B) :
    (A ∩ B).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hne
  have hAf : m A ≠ ⊤ := ne_top_of_le_ne_top hΛ (measure_mono hA)
  have hBf : m B ≠ ⊤ := ne_top_of_le_ne_top hΛ (measure_mono hB)
  have hU := measureReal_union hne.symm hAm hBf hAf
  have hle : m.real (B ∪ A) ≤ m.real Λ := measureReal_mono (union_subset hB hA) hΛ
  linarith

/-- **The choice of `x₁, …, x_{d−1}`** (DZZ l. 2525–2530), for an abstract measure and relation. -/
theorem l53_chain_select {α : Type*} [MeasurableSpace α] (m : Measure α) (R : α → α → Prop)
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℕ → Set α) (u v : α)
    (hΛ : ∀ i, 1 ≤ i → i ≤ d - 1 → m (Λ i) ≠ ⊤ ∧ 0 < m.real (Λ i))
    (hu : ∃ A ⊆ Λ 1, MeasurableSet A ∧ 0.99 * m.real (Λ 1) ≤ m.real A ∧ ∀ x ∈ A, R u x)
    (hv : ∃ A ⊆ Λ (d - 1), 0.99 * m.real (Λ (d - 1)) ≤ m.real A ∧
      ∀ x ∈ A, R x v)
    (hC : ∀ i, 2 ≤ i → i ≤ d - 1 → ∀ E ⊆ Λ i, 0.1 * m.real (Λ i) ≤ m.real E →
      ∃ S ⊆ Λ (i - 1), 0.1 * m.real (Λ (i - 1)) ≤ m.real S ∧
        ∀ x ∈ S, ∃ x' ∈ E, R x x') :
    ∃ x : ℕ → α, x 0 = u ∧ x d = v ∧ ∀ i < d, R (x i) (x (i + 1)) := by
  -- backward claim: `Λ*_{d-1-n}` with chains of length `n+1` to `v`
  have claim : ∀ n, n + 2 ≤ d → ∃ E ⊆ Λ (d - 1 - n),
      0.1 * m.real (Λ (d - 1 - n)) ≤ m.real E ∧ ∀ x ∈ E, ∃ y : ℕ → α, y 0 = x ∧ y (n + 1) = v ∧
        ∀ i < n + 1, R (y i) (y (i + 1)) := by
    intro n
    induction n with
    | zero =>
      intro _
      obtain ⟨A, hAΛ, hAμ, hAR⟩ := hv
      have h0 : 0 ≤ m.real (Λ (d - 1)) := measureReal_nonneg
      refine ⟨A, by simpa using hAΛ, by simp only [Nat.sub_zero]; linarith, fun x hx => ?_⟩
      refine ⟨fun i => if i = 0 then x else v, by simp, by simp, fun i hi => ?_⟩
      have : i = 0 := by omega
      subst this; simpa using hAR x hx
    | succ n ih =>
      intro hn
      obtain ⟨E, hEΛ, hEμ, hER⟩ := ih (by omega)
      have hi2 : 2 ≤ d - 1 - n := by omega
      obtain ⟨S, hSΛ, hSμ, hSR⟩ := hC (d - 1 - n) hi2 (by omega) E hEΛ hEμ
      have he : d - 1 - n - 1 = d - 1 - (n + 1) := by omega
      rw [he] at hSΛ hSμ
      refine ⟨S, hSΛ, hSμ, fun x hx => ?_⟩
      obtain ⟨x', hx'E, hxx'⟩ := hSR x hx
      obtain ⟨y, hy0, hyn, hyR⟩ := hER x' hx'E
      refine ⟨fun i => match i with | 0 => x | j + 1 => y j, rfl, hyn, fun i hi => ?_⟩
      rcases i with _ | j
      · simpa [hy0] using hxx'
      · exact hyR j (by omega)
  obtain ⟨E, hEΛ, hEμ, hER⟩ := claim (d - 2) (by omega)
  have h1 : d - 1 - (d - 2) = 1 := by omega
  rw [h1] at hEΛ hEμ
  obtain ⟨A, hAΛ, hAm, hAμ, hAR⟩ := hu
  obtain ⟨hΛ1, hΛ10⟩ := hΛ 1 le_rfl (by omega)
  obtain ⟨x₁, hx₁A, hx₁E⟩ := inter_nonempty_of_measureReal hΛ1 hΛ10 hAΛ hEΛ hAm hAμ hEμ
  obtain ⟨y, hy0, hyn, hyR⟩ := hER x₁ hx₁E
  have hd' : d - 2 + 1 + 1 = d := by omega
  refine ⟨fun i => if i = 0 then u else y (i - 1), by simp, ?_, fun i hi => ?_⟩
  · have e : d - 1 = d - 2 + 1 := by omega
    simp only [show d ≠ 0 by omega, ↓reduceIte, e]
    exact hyn
  · rcases i with _ | j
    · simpa [hy0] using hAR x₁ hx₁A
    · simpa using hyR j (by omega)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`𝒟₁` and the desirability of `u`, `v`, `𝖢₂, …, 𝖢_{d−1}`** (DZZ l. 2504–2522), with
interfaces `Λ₁, …, Λ_{d−1}` of positive finite length, the leg threshold `T` (`u`, `v` desirable)
and the middle threshold `T'` ((eq-start-end)). -/
def l53DesirableEvent (ν : Ω → Measure ℂ) (u v : ℂ) (δ T₁ T T' : ℝ) : Set Ω :=
  {ω | ∃ d : ℕ, 2 ≤ d ∧ (d : ℝ) ≤ Real.exp T₁ ∧ ∃ Λ : ℕ → Set ℂ,
    (∀ i, 1 ≤ i → i ≤ d - 1 → μH[1] (Λ i) ≠ ⊤ ∧ 0 < (μH[1] : Measure ℂ).real (Λ i)) ∧
    (∃ A ⊆ Λ 1, MeasurableSet A ∧ 0.99 * (μH[1] : Measure ℂ).real (Λ 1) ≤ (μH[1] : Measure ℂ).real A ∧
      ∀ x ∈ A, lgdLeExp (ν ω) δ T u x) ∧
    (∃ A ⊆ Λ (d - 1),
      0.99 * (μH[1] : Measure ℂ).real (Λ (d - 1)) ≤ (μH[1] : Measure ℂ).real A ∧
      ∀ x ∈ A, lgdLeExp (ν ω) δ T v x) ∧
    (∀ i, 2 ≤ i → i ≤ d - 1 → ∀ E ⊆ Λ i,
      0.1 * (μH[1] : Measure ℂ).real (Λ i) ≤ (μH[1] : Measure ℂ).real E →
      ∃ S ⊆ Λ (i - 1),
        0.1 * (μH[1] : Measure ℂ).real (Λ (i - 1)) ≤ (μH[1] : Measure ℂ).real S ∧
        ∀ x ∈ S, ∃ x' ∈ E, lgdLeExp (ν ω) δ T' x x')}

omit [MeasurableSpace Ω] in
/-- DZZ l. 2525–2530: the desirable event is contained in the chain event `𝒟`. -/
lemma l53DesirableEvent_subset {ν : Ω → Measure ℂ} {u v : ℂ} {δ T₁ T T' T₂ : ℝ}
    (hT : T ≤ T₂) (hT' : T' ≤ T₂) :
    l53DesirableEvent ν u v δ T₁ T T' ⊆ l53ChainEvent ν u v δ T₁ T₂ := by
  rintro ω ⟨d, hd, hdT, Λ, hΛ, hu, hv, hC⟩
  obtain ⟨x, hx0, hxd, hx⟩ := l53_chain_select (μH[1] : Measure ℂ) (lgdLeExp (ν ω) δ T₂) hd Λ u v
    hΛ (by obtain ⟨A, h1, h2, h3, h4⟩ := hu; exact ⟨A, h1, h2, h3, fun x hx => (h4 x hx).mono hT⟩)
    (by
      obtain ⟨A, h1, h3, h4⟩ := hv
      refine ⟨A, h1, h3, fun x hx => ?_⟩
      have := (h4 x hx).mono hT
      unfold lgdLeExp at this ⊢; rwa [lgdDZZ_comm])
    (fun i hi hi' E hE hEμ => by
      obtain ⟨S, h1, h3, h4⟩ := hC i hi hi' E hE hEμ
      exact ⟨S, h1, h3, fun x hx => by
        obtain ⟨x', hx', h⟩ := h4 x hx; exact ⟨x', hx', h.mono hT'⟩⟩)
  exact ⟨d, by omega, hdT, x, hx0, hxd, hx⟩

end DZZ
end LQGMetric
