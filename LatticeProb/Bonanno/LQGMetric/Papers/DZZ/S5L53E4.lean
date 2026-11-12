/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53E4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53E3

/-!
# DZZ Lemma 5.3, part 1: crossing a chain of open boxes (P2-DZZ53E)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`. The cells are desirable "similar to
(eq-par)" (l. 2512–2514). In the heat-kernel proof (l. 1960–2000) a sequence of neighbouring
pre-fast boxes `𝖡₁, …, 𝖡_ℓ` from a segment `L ∈ 𝕃'` to `𝕃` is crossed through the interfaces
`Λ_{i,j}` (common boundaries), each of length `≥ s_i/(2K)`. Here is the deterministic LGD analogue
for open boxes in the sense of `l53_open_of_not_bad` (DZZ l. 2429; for the LGD version DZZ only say
"similar"). This is our own elementary adaptation of the structure of l. 1960–2000.

* **`l53_open_chain`**: boxes `0, …, n` with boundaries `Bd j` and interfaces `I j ⊆ Bd j ∩ Bd (j+1)`
  of measure `≥ c ≥ b + a`, all open. For every `Λ ⊆ Bd n` with `ν Λ ≥ b` there are `z₀ ∈ Bd 0`, whose
  far set in `Bd 0` has measure `≤ a`, and a chain `z₀, …, z_n ∈ Λ` of `R`-related points.
* `lgdLeExp_chain`: such a chain of `lgdLeExp δ T` pieces of length `n + 1` gives
  `D_δ(x, z_n) ≤ (n + 1) e^T` (finite).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal MeasureTheory

namespace LQGMetric
namespace DZZ

/-- **Crossing a chain of open boxes** (analogue of DZZ l. 1960–2000 for the LGD). -/
theorem l53_open_chain {α : Type*} [MeasurableSpace α] (ν : Measure α) (R : α → α → Prop)
    (Bd I : ℕ → Set α) {a b c : ℝ≥0∞} (ha : a ≠ ⊤) (hc : b + a ≤ c)
    (hI : ∀ j, I j ⊆ Bd j ∩ Bd (j + 1)) (hIc : ∀ j, c ≤ ν (I j))
    (hopen : ∀ j, ∀ Λ ⊆ Bd j, b ≤ ν Λ → ∃ z ∈ Λ, ν {z' ∈ Bd j | ¬ R z z'} ≤ a) :
    ∀ n, ∀ Λ ⊆ Bd n, b ≤ ν Λ → ∃ z₀ ∈ Bd 0, ν {z' ∈ Bd 0 | ¬ R z₀ z'} ≤ a ∧
      ∃ y : ℕ → α, y 0 = z₀ ∧ y n ∈ Λ ∧ ∀ j < n, R (y (j + 1)) (y j) := by
  intro n
  induction n with
  | zero =>
    intro Λ hΛ hb
    obtain ⟨z, hz, hza⟩ := hopen 0 Λ hΛ hb
    exact ⟨z, hΛ hz, hza, fun _ => z, rfl, hz, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    intro Λ hΛ hb
    obtain ⟨z, hz, hza⟩ := hopen (n + 1) Λ hΛ hb
    set E : Set α := I n ∩ {z' | R z z'} with hE
    have hEB : E ⊆ Bd n := fun x hx => (hI n hx.1).1
    have hcov : I n ⊆ E ∪ {z' ∈ Bd (n + 1) | ¬ R z z'} := by
      intro x hx
      by_cases h : R z x
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨(hI n hx).2, h⟩
    have hEb : b ≤ ν E := by
      have h1 : b + a ≤ ν E + a :=
        calc b + a ≤ c := hc
          _ ≤ ν (I n) := hIc n
          _ ≤ ν (E ∪ {z' ∈ Bd (n + 1) | ¬ R z z'}) := measure_mono hcov
          _ ≤ ν E + ν {z' ∈ Bd (n + 1) | ¬ R z z'} := measure_union_le _ _
          _ ≤ ν E + a := by gcongr
      exact (ENNReal.add_le_add_iff_right ha).1 h1
    obtain ⟨z₀, hz₀, hz₀a, y, hy0, hyn, hyR⟩ := ih E hEB hEb
    refine ⟨z₀, hz₀, hz₀a, fun j => if j ≤ n then y j else z, by simp [hy0], by simpa using hz,
      fun j hj => ?_⟩
    rcases Nat.lt_or_ge j n with hjn | hjn
    · have h1 : j + 1 ≤ n := hjn
      have h2 : j ≤ n := hjn.le
      simp only [h1, h2, ite_true]
      exact hyR j hjn
    · have hj' : j = n := by omega
      subst hj'
      simp only [le_refl, ite_true, show ¬ j + 1 ≤ j by omega, ite_false]
      exact hyn.2

/-- A chain `x, z₀, …, z_n` of `lgdLeExp δ T` pieces (`R (z_{j+1}) z_j` and `R z₀ x`) gives
`D_δ(x, z_n) ≤ (n + 1) e^T`. -/
lemma lgdLeExp_chain (μ : Measure ℂ) {δ T : ℝ} {n : ℕ} {x : ℂ} (y : ℕ → ℂ)
    (h0 : lgdLeExp μ δ T (y 0) x) (hR : ∀ j < n, lgdLeExp μ δ T (y (j + 1)) (y j)) :
    lgdDZZ μ δ x (y n) ≠ ⊤ ∧ ((lgdDZZ μ δ x (y n)).toNat : ℝ) ≤ (n + 1) * Real.exp T := by
  set w : ℕ → ℂ := fun j => if j = 0 then x else y (j - 1) with hw
  have hstep : ∀ j < n + 1, lgdLeExp μ δ T (w j) (w (j + 1)) := by
    intro j hj
    rcases j with _ | j
    · simp only [hw, ite_true, Nat.zero_add, one_ne_zero, ite_false, Nat.sub_self]
      unfold lgdLeExp at h0 ⊢; rwa [lgdDZZ_comm]
    · have := hR j (by omega)
      simp only [hw, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
      unfold lgdLeExp at this ⊢; rwa [lgdDZZ_comm]
  have hchain := lgdDZZ_chain_le μ δ w (Nat.succ_pos n)
  have hw0 : w 0 = x := by simp [hw]
  have hwn : w (n + 1) = y n := by simp [hw]
  rw [hw0, hwn] at hchain
  have hfin : ∀ i ∈ Finset.range (n + 1), lgdDZZ μ δ (w i) (w (i + 1)) ≠ ⊤ :=
    fun i hi => (hstep i (Finset.mem_range.1 hi)).1
  have hsum_ne := ENat.sum_ne_top.2 hfin
  refine ⟨ne_top_of_le_ne_top hsum_ne hchain, ?_⟩
  have hN : (lgdDZZ μ δ x (y n)).toNat ≤
      ∑ i ∈ Finset.range (n + 1), (lgdDZZ μ δ (w i) (w (i + 1))).toNat := by
    rw [← ENat.toNat_sum hfin]; exact ENat.toNat_le_toNat hchain hsum_ne
  have h1 : ((lgdDZZ μ δ x (y n)).toNat : ℝ) ≤
      ∑ i ∈ Finset.range (n + 1), ((lgdDZZ μ δ (w i) (w (i + 1))).toNat : ℝ) := by
    exact_mod_cast hN
  refine h1.trans ?_
  have := Finset.sum_le_sum (s := Finset.range (n + 1))
    (fun i hi => (hstep i (Finset.mem_range.1 hi)).2)
  simpa using this

end DZZ
end LQGMetric
