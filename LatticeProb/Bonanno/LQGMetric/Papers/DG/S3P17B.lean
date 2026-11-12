/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P17B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L2
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputsDG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.17, Step 3: comparison of the approximate LFPP with the LGD along chains

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.17, Step 3
(DG:1567–1591): for a chain `S_0, …, S_k` of squares of `𝒮_{δ_ε}` from `K` to `∂U`, the sets
`Y_{S_j}` (unions of rectangle crossings, Step 2) are pairwise `D^ε`-close (eqn-lfpp-max-Y),
consecutive ones intersect, hence (eqn-lfpp-lower-sum)
`D^ε(S_0, S_k) ≤ Σ_j 12 N e^{ξ ĥ_{ε^β}(v_{S_j})}`; comparing with the lower bound
`D^ε(K', ∂U') ≥ ε^{-1/(d+ζ̃)}` gives a lower bound for `D̂^{ε^β}(K, ∂U)` (eqn-lfpp-lower-last).

* `p17_lgd_tri` — triangle inequality for `dgLGD` (witness concatenation; the argument of
  `LGDWit.trans`, Papers/DG/S3L11Det.lean by P2-DG105g, re-proved here since that file is not
  yet committed).
* `p17_chain_sum` — DG (eqn-lfpp-lower-sum) for an abstract chain of cells.
* `dg_prop317_step3` — DG (eqn-lfpp-lower-last) in the form
  `Lb · δ ≤ T · D̂^δ(z, w; 𝕊)` from the Step 2 data `Y`, the per-square bound `T e^{ξ φ(v_S)}` and
  a lower bound `Lb` for `D^ε(y, y')` for `y` near `K` and `y'` near `∂U`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint

variable {μ : Measure ℂ} {ε : ℝ} {U : Set ℂ}

/-- witnesses of `dgLGD ≤ N` -/
def P17Wit (μ : Measure ℂ) (ε : ℝ) (U : Set ℂ) (z w : ℂ) (N : ℕ) : Prop :=
  ∃ (x : Fin N → ℂ) (ρ : Fin N → ℝ) (P : Path z w),
    (∀ i, 0 < ρ i ∧ Metric.ball (x i) (ρ i) ⊆ closure U ∧
      μ (Metric.ball (x i) (ρ i)) ≤ ENNReal.ofReal ε) ∧
    ∀ t, ∃ i, P t ∈ Metric.ball (x i) (ρ i)

lemma p17_exists_wit {z w : ℂ} (h : dgLGD μ ε U z w ≠ ⊤) :
    ∃ N, P17Wit μ ε U z w N ∧ dgLGD μ ε U z w = N := by
  classical
  have hex : ∃ N, P17Wit μ ε U z w N := by
    by_contra hne
    push Not at hne
    apply h
    unfold dgLGD
    exact iInf₂_eq_top.2 fun N hN => absurd hN (hne N)
  refine ⟨Nat.find hex, Nat.find_spec hex, le_antisymm (iInf₂_le _ (Nat.find_spec hex)) ?_⟩
  unfold dgLGD
  exact le_iInf₂ fun N hN => by exact_mod_cast Nat.find_min' hex hN

lemma P17Wit.trans {z x w : ℂ} {N₁ N₂ : ℕ} (h₁ : P17Wit μ ε U z x N₁)
    (h₂ : P17Wit μ ε U x w N₂) : P17Wit μ ε U z w (N₁ + N₂) := by
  obtain ⟨x₁, ρ₁, P₁, hb₁, hc₁⟩ := h₁
  obtain ⟨x₂, ρ₂, P₂, hb₂, hc₂⟩ := h₂
  refine ⟨Fin.append x₁ x₂, Fin.append ρ₁ ρ₂, P₁.trans P₂, fun i => ?_, fun t => ?_⟩
  · induction i using Fin.addCases with
    | left i => simpa only [Fin.append_left] using hb₁ i
    | right i => simpa only [Fin.append_right] using hb₂ i
  · have ht : (P₁.trans P₂) t ∈ Set.range (P₁.trans P₂) := ⟨t, rfl⟩
    rw [Path.trans_range] at ht
    rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
    · obtain ⟨i, hi⟩ := hc₁ s
      exact ⟨Fin.castAdd N₂ i, by rw [Fin.append_left, Fin.append_left, ← hs]; exact hi⟩
    · obtain ⟨i, hi⟩ := hc₂ s
      exact ⟨Fin.natAdd N₁ i, by rw [Fin.append_right, Fin.append_right, ← hs]; exact hi⟩

/-- **triangle inequality** for the Liouville graph distance -/
lemma p17_lgd_tri (z x w : ℂ) :
    (dgLGD μ ε U z w : ℝ≥0∞) ≤ dgLGD μ ε U z x + dgLGD μ ε U x w := by
  by_cases h₁ : dgLGD μ ε U z x = ⊤
  · rw [h₁]; simp
  by_cases h₂ : dgLGD μ ε U x w = ⊤
  · rw [h₂]; simp
  obtain ⟨N₁, w₁, e₁⟩ := p17_exists_wit h₁
  obtain ⟨N₂, w₂, e₂⟩ := p17_exists_wit h₂
  rw [e₁, e₂]
  have : dgLGD μ ε U z w ≤ (N₁ + N₂ : ℕ) := iInf₂_le _ (w₁.trans w₂)
  calc (dgLGD μ ε U z w : ℝ≥0∞) ≤ ((N₁ + N₂ : ℕ) : ℕ∞) := by exact_mod_cast this
    _ = _ := by push_cast; rfl

/-- **DG (eqn-lfpp-lower-sum)** for an abstract chain of cells `k₀, …` with sets `Y k` of
`D^ε`-diameter `≤ N k`, consecutive ones intersecting -/
theorem p17_chain_sum {ι : Type} {R : ι → ι → Prop} {Y : ι → Set ℂ} {N : ι → ℝ≥0∞}
    (hadj : ∀ k k', R k k' → (Y k ∩ Y k').Nonempty) :
    ∀ (L : List ι) (k₀ : ι), (k₀ :: L).IsChain R →
      (∀ k ∈ k₀ :: L, ∀ y ∈ Y k, ∀ y' ∈ Y k, (dgLGD μ ε U y y' : ℝ≥0∞) ≤ N k) →
      ∀ y ∈ Y k₀, ∀ y' ∈ Y ((k₀ :: L).getLast (List.cons_ne_nil _ _)),
        (dgLGD μ ε U y y' : ℝ≥0∞) ≤ ((k₀ :: L).map N).sum := by
  intro L
  induction L with
  | nil =>
    intro k₀ _ hY y hy y' hy'
    simpa using hY k₀ (by simp) y hy y' hy'
  | cons k₁ L ih =>
    intro k₀ hc hY y hy y' hy'
    rw [List.isChain_cons_cons] at hc
    obtain ⟨x, hx₀, hx₁⟩ := hadj _ _ hc.1
    have h1 := hY k₀ (by simp) y hy x hx₀
    have h2 := ih k₁ hc.2 (fun k hk => hY k (List.mem_cons_of_mem _ hk)) x hx₁ y'
      (by simpa using hy')
    calc (dgLGD μ ε U y y' : ℝ≥0∞) ≤ dgLGD μ ε U y x + dgLGD μ ε U x y' := p17_lgd_tri y x y'
      _ ≤ N k₀ + ((k₁ :: L).map N).sum := add_le_add h1 h2
      _ = ((k₀ :: k₁ :: L).map N).sum := by simp

lemma p17_list_sum_ofReal {ι : Type} (f : ι → ℝ) (hf : ∀ k, 0 ≤ f k) (L : List ι) :
    (L.map fun k => ENNReal.ofReal (f k)).sum = ENNReal.ofReal (L.map f).sum := by
  induction L with
  | nil => simp
  | cons k L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [ENNReal.ofReal_add (hf k) (List.sum_nonneg fun x hx => by
      obtain ⟨k', -, rfl⟩ := List.mem_map.1 hx; exact hf k')]

/-- **DG (eqn-lfpp-lower-last)**, deterministic: with the Step 2 data (`hY`: `Y_S` has
`D^ε`-diameter `≤ T e^{ξ φ(v_S)}`, `hadj`: adjacent `Y_S` intersect, `hnear`: `Y_S` comes within
`ρ` of every point of `S`) and a lower bound `Lb` for `D^ε(y, y')` when `y` is `ρ`-close to `z`
and `y'` is `ρ`-close to `w` (`hLb`), `Lb δ ≤ T D̂^δ(z, w; 𝕊)`. -/
theorem dg_prop317_step3 {Q : Set ℂ} {δ ξ T Lb ρ : ℝ} (hδ : 0 < δ) (hT : 0 < T)
    {φ : ℂ → ℝ} {Y : ℤ × ℤ → Set ℂ}
    (hY : ∀ k ∈ dgIdx (dgM δ), ∀ y ∈ Y k, ∀ y' ∈ Y k, (dgLGD μ ε Q y y' : ℝ≥0∞) ≤
      ENNReal.ofReal (T * Real.exp (ξ * φ (dgCenter (dgM δ) k))))
    (hadj : ∀ k k', dgAdj k k' → (Y k ∩ Y k').Nonempty)
    (hnear : ∀ k ∈ dgIdx (dgM δ), ∀ x ∈ gridSquare ((2 : ℝ)⁻¹ ^ dgM δ) k, ∃ y ∈ Y k, ‖y - x‖ ≤ ρ)
    {z w : ℂ} (hLb : ∀ y y' : ℂ, ‖y - z‖ ≤ ρ → ‖y' - w‖ ≤ ρ →
      ENNReal.ofReal Lb ≤ dgLGD μ ε Q y y')
    (hne : Nonempty {L : List (ℤ × ℤ) // IsDGSqChain (dgM δ) z w L}) :
    Lb * δ ≤ T * dgApproxLFPP ξ δ φ z w := by
  have key : ∀ L : {L : List (ℤ × ℤ) // IsDGSqChain (dgM δ) z w L},
      Lb * δ / T ≤ (L.1.map fun k => δ * Real.exp (ξ * φ (dgCenter (dgM δ) k))).sum := by
    rintro ⟨L, hnd, hidx, hch, ⟨k₀, hk₀, hz⟩, ⟨kl, hkl, hw⟩⟩
    obtain ⟨k₀', L', rfl⟩ : ∃ a l, L = a :: l := by
      cases L with
      | nil => simp at hk₀
      | cons a l => exact ⟨a, l, rfl⟩
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hk₀
    subst hk₀
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), Option.mem_def,
      Option.some.injEq] at hkl
    obtain ⟨y, hy, hyz⟩ := hnear _ (hidx _ (by simp)) z hz
    obtain ⟨y', hy', hyw⟩ := hnear _ (hidx _ (List.getLast_mem _)) w (hkl ▸ hw)
    have hs := p17_chain_sum (μ := μ) (ε := ε) (U := Q) (R := dgAdj) (Y := Y)
      (N := fun k => ENNReal.ofReal (T * Real.exp (ξ * φ (dgCenter (dgM δ) k)))) hadj L' k₀'
      hch (fun k hk => hY k (hidx k hk)) y hy y' hy'
    rw [p17_list_sum_ofReal _ (fun k => by positivity)] at hs
    have hb := (hLb y y' hyz hyw).trans hs
    rw [ENNReal.ofReal_le_ofReal_iff (List.sum_nonneg fun x hx => by
      obtain ⟨k', -, rfl⟩ := List.mem_map.1 hx; positivity)] at hb
    rw [List.sum_map_mul_left] at hb ⊢
    rw [div_le_iff₀ hT]
    calc Lb * δ ≤ T * (List.map (fun k => Real.exp (ξ * φ (dgCenter (dgM δ) k)))
          (k₀' :: L')).sum * δ := mul_le_mul_of_nonneg_right hb hδ.le
      _ = _ := by ring
  have := le_ciInf key
  rw [div_le_iff₀ hT] at this
  unfold dgApproxLFPP
  linarith

end LQGMetric.DG
