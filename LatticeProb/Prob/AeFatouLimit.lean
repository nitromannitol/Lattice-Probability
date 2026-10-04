/-
# The a.e. Fatou limit for the tails of a convergent sequence

A general, reusable form of the limit step in the isonormal concentration bridge
(`~/fleet/audit/lib-isonormal-concentration.md`, Part 2).  It is stated for an abstract measure
space, a sequence `X : ℕ → α → ℝ` and a limit `Y : α → ℝ`, with no Gaussian
development.

For an **open** set `A ⊆ ℝ`:

* `ae_subset_iUnion_iInter_of_tendsto_ae`: if `X n → Y` almost everywhere, then a.e.
  `Y ω ∈ A` implies `ω ∈ ⋃ N, ⋂ n ≥ N, {X n ∈ A}`: on a path with `X · ω → Y ω`, the
  limit enters the open set `A` eventually;
* `measure_le_of_tendsto_ae_of_isOpen`: if moreover every tail `μ {X n ∈ A}` is at most `B`, then
  `μ {Y ∈ A} ≤ B`, by Fatou: the union increases, so continuity from below makes it
  into the supremum of the tail measures) — the exact step the concentration needs;
* `measure_le_of_tendsto_ae_of_lt`: the special case `A = Set.Ioi a`.

**Open vs closed.**  The Fatou direction `μ {Y ∈ A} ≤ liminf μ {X n ∈ A}` concerns
*open* `A` (a limit of points of `A` lands in `A` eventually).  For a *closed* `A` the inclusion
reverses (`{X n ∈ A}` eventually forces `Y ∈ A`), so no direct Fatou bound holds; the closed
needed by the concentration, `{∫F + t ≤ F}`, is handled by intersecting with the open
`{∫F + t - ε < F}` and letting `ε ↓ 0` (the exponent `exp(-(t-ε)²/(2L²))` tends to
`exp(-t²/(2L²))`).  That transition is recorded here rather than formalised.

No `sorry`, no `axiom`.
-/
import Mathlib

noncomputable section

namespace LatticeProb

open MeasureTheory Filter

open scoped Topology ENNReal

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α} {X : ℕ → α → ℝ} {Y : α → ℝ}

/-- **The a.e. event inclusion.**  If `X n → Y` almost everywhere and `A ⊆ ℝ` is open, then,
almost everywhere, `Y ω ∈ A` implies `ω ∈ ⋃ N, ⋂ n ≥ N, {X n ∈ A}`: on a path with
`X · ω → Y ω` the sequence enters the open set `A` eventually. -/
theorem ae_subset_iUnion_iInter_of_tendsto_ae {A : Set ℝ} (hA : IsOpen A)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    ∀ᵐ ω ∂μ, Y ω ∈ A → ω ∈ ⋃ N, ⋂ n ∈ Set.Ici N, {ω' | X n ω' ∈ A} := by
  filter_upwards [hae] with ω hω hYA
  have hev : ∀ᶠ n in atTop, X n ω ∈ A := hω.eventually (hA.mem_nhds hYA)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  exact Set.mem_iUnion.mpr ⟨N, Set.mem_iInter₂.mpr fun n hn => hN n hn⟩

/-- **The Fatou bound.**  If `X n → Y` almost everywhere, `A` is open, and every tail
`μ {ω | X n ω ∈ A}` is at most `B`, then `μ {ω | Y ω ∈ A} ≤ B`. -/
theorem measure_le_of_tendsto_ae_of_isOpen {A : Set ℝ} (hA : IsOpen A)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    {B : ℝ≥0∞} (hB : ∀ n, μ {ω | X n ω ∈ A} ≤ B) :
    μ {ω | Y ω ∈ A} ≤ B := by
  classical
  set T : Set α := ⋃ N, ⋂ n ∈ Set.Ici N, {ω | X n ω ∈ A} with hT
  have hmp : ∀ᵐ ω ∂μ, Y ω ∈ A → ω ∈ T :=
    ae_subset_iUnion_iInter_of_tendsto_ae hA hae
  have hnul : μ ({ω | Y ω ∈ A} \ T) = 0 := by
    rw [ae_iff] at hmp
    exact measure_mono_null (fun ω hω (h : Y ω ∈ A → ω ∈ T) => hω.2 (h hω.1)) hmp
  have hle : μ {ω | Y ω ∈ A} ≤ μ T := by
    calc μ {ω | Y ω ∈ A} ≤ μ (T ∪ ({ω | Y ω ∈ A} \ T)) :=
          measure_mono fun ω hω => by
            by_cases h : ω ∈ T
            · exact Or.inl h
            · exact Or.inr ⟨hω, h⟩
      _ ≤ μ T + μ ({ω | Y ω ∈ A} \ T) := measure_union_le _ _
      _ = μ T := by rw [hnul, add_zero]
  refine le_trans hle ?_
  have hmono : Monotone fun N => ⋂ n ∈ Set.Ici N, {ω | X n ω ∈ A} := by
    intro m n hmn ω hω
    exact Set.mem_iInter₂.mpr fun k hk =>
      (Set.mem_iInter₂.mp hω) k (le_trans hmn hk)
  rw [hT, hmono.measure_iUnion]
  refine iSup_le fun N => le_trans (measure_mono ?_) (hB N)
  exact Set.iInter₂_subset (s := fun n (_ : n ∈ Set.Ici N) => {ω | X n ω ∈ A}) N (le_refl N)

/-- **The strict-tail Fatou limit.**  If `X n → Y` almost everywhere and every strict tail
`μ {ω | a < X n ω}` is at most `B`, then `μ {ω | a < Y ω} ≤ B`. -/
theorem measure_le_of_tendsto_ae_of_lt
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    {a : ℝ} {B : ℝ≥0∞} (hB : ∀ n, μ {ω | a < X n ω} ≤ B) :
    μ {ω | a < Y ω} ≤ B :=
  measure_le_of_tendsto_ae_of_isOpen isOpen_Ioi hae hB

end LatticeProb
