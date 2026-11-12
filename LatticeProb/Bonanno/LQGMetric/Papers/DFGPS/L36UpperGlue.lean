/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36UpperGlue at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperPath

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Gluing graph paths (upper half of DFGPS Lemma 3.6)

Concatenation and reversal of graph paths of `𝕊 ∩ δℤ²` (DFGPS (eq:graph), T:1606), the chain of
box paths, straight walks between grid points of `𝕊`, and the corner vertices `δ(1,1)` (leftmost)
and `δ(⌈1/δ⌉ − 1, 1)` (rightmost). Elementary (D52).
-/

noncomputable section

open Set

namespace LQGMetric.DFGPS.L36

open Blueprint

variable {δ : ℝ} {U : Set ℂ}

lemma isGraphPath_append {L₁ L₂ : List ℂ} {v : ℂ} (h₁ : IsGraphPath δ U L₁)
    (h₂ : IsGraphPath δ U L₂) (hl : L₁.getLast? = some v) (hh : L₂.head? = some v) :
    IsGraphPath δ U (L₁ ++ L₂.tail) ∧ (L₁ ++ L₂.tail).head? = L₁.head? ∧
      (L₁ ++ L₂.tail).getLast? = L₂.getLast? := by
  obtain ⟨t, rfl⟩ : ∃ t, L₂ = v :: t := by
    cases L₂ with
    | nil => simp at hh
    | cons a t => simp only [List.head?_cons, Option.some.injEq] at hh; exact ⟨t, by rw [hh]⟩
  have hc2 := h₂.2.2
  refine ⟨⟨by simp [h₁.1], fun x hx => ?_, ?_⟩, ?_, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact h₁.2.1 x hx
    · exact h₂.2.1 x (List.mem_cons_of_mem _ hx)
  · rw [List.isChain_append]
    refine ⟨h₁.2.2, hc2.tail, fun x hx y hy => ?_⟩
    rw [hl, Option.mem_def, Option.some.injEq] at hx
    subst hx
    cases t with
    | nil => simp at hy
    | cons b t =>
      simp only [List.tail_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact (List.isChain_cons_cons.1 hc2).1
  · rw [List.head?_append]
    cases L₁ with
    | nil => exact absurd rfl h₁.1
    | cons a l => simp
  · cases t with
    | nil => simp [hl]
    | cons b t => rw [List.tail_cons, List.getLast?_append]; simp [List.getLast?_cons]

lemma sum_append_tail_le (f : ℂ → ℝ) (hf : ∀ x, 0 ≤ f x) (L₁ L₂ : List ℂ) :
    ((L₁ ++ L₂.tail).map f).sum ≤ (L₁.map f).sum + (L₂.map f).sum := by
  rw [List.map_append, List.sum_append]
  cases L₂ with
  | nil => simp
  | cons a t => simp only [List.tail_cons, List.map_cons, List.sum_cons]; linarith [hf a]

lemma isGraphPath_reverse {L : List ℂ} (h : IsGraphPath δ U L) : IsGraphPath δ U L.reverse := by
  refine ⟨by simpa using h.1, fun x hx => h.2.1 x (List.mem_reverse.1 hx), ?_⟩
  rw [List.isChain_reverse]
  exact h.2.2.imp fun x y hxy => by rwa [norm_sub_rev]

/-- **Chain of box paths** from `v N` to `v 0`. -/
theorem exists_chain_paths (v : ℕ → ℂ) (f : ℂ → ℝ) (hf : ∀ x, 0 ≤ f x) (S : ℕ → ℝ) :
    ∀ N : ℕ, (∀ k < N + 1, ∃ L, IsGraphPath δ U L ∧ L.head? = some (v (k+1)) ∧
      L.getLast? = some (v k) ∧ (L.map f).sum ≤ S k) →
    ∃ L, IsGraphPath δ U L ∧ L.head? = some (v (N+1)) ∧ L.getLast? = some (v 0) ∧
      (L.map f).sum ≤ ∑ k ∈ Finset.range (N + 1), S k
  | 0, hP => by
    obtain ⟨L, h1, h2, h3, h4⟩ := hP 0 (by omega)
    exact ⟨L, h1, h2, h3, by simpa using h4⟩
  | N + 1, hP => by
    obtain ⟨L₀, h1, h2, h3, h4⟩ := exists_chain_paths v f hf S N fun k hk => hP k (by omega)
    obtain ⟨L, g1, g2, g3, g4⟩ := hP (N + 1) (by omega)
    obtain ⟨a1, a2, a3⟩ := isGraphPath_append g1 h1 g3 h2
    refine ⟨_, a1, by rw [a2, g2], by rw [a3, h3], ?_⟩
    rw [Finset.sum_range_succ]
    linarith [sum_append_tail_le f hf L L₀]

lemma graphLFPP_le_sum {ξ : ℝ} {φ : ℂ → ℝ} {A B : Set ℂ} {L : List ℂ}
    (hL : IsGraphPath δ U L) (hA : ∃ x ∈ L.head?, x ∈ A) (hB : ∃ y ∈ L.getLast?, y ∈ B) :
    graphLFPP ξ δ φ A B U ≤ (L.map fun x => Real.exp (ξ * φ x)).sum := by
  unfold graphLFPP
  refine ciInf_le ⟨0, ?_⟩ (⟨L, hL, hA, hB⟩ : {L : List ℂ // IsGraphPath δ U L ∧
    (∃ x ∈ L.head?, x ∈ A) ∧ ∃ y ∈ L.getLast?, y ∈ B})
  rintro _ ⟨L', rfl⟩
  exact List.sum_nonneg fun y hy => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy
    exact (Real.exp_pos _).le

/-- a straight walk between two grid points of `𝕊` is a graph path of `𝕊 ∩ δℤ²` -/
lemma isGraphPath_gridWalk (hδ : 0 < δ) {k k' : ℤ × ℤ} (hk : gpt δ k ∈ rS 1)
    (hk' : gpt δ k' ∈ rS 1) : IsGraphPath δ (rS 1) (gridWalk δ k k') := by
  refine ⟨gridWalk_ne_nil δ k k', fun x hx => ?_, gridWalk_chain hδ k k'⟩
  obtain ⟨c, rfl, h1, h2, h3, h4⟩ := mem_gridWalk hx
  refine ⟨?_, ⟨c.1, c.2, rfl⟩⟩
  obtain ⟨a1, a2, a3, a4⟩ := mem_rS_one.1 hk
  obtain ⟨b1, b2, b3, b4⟩ := mem_rS_one.1 hk'
  simp only [gpt] at a1 a2 a3 a4 b1 b2 b3 b4 ⊢
  have e1 : min (k.1 : ℝ) k'.1 ≤ c.1 := by exact_mod_cast h1
  have e2 : (c.1 : ℝ) ≤ max (k.1 : ℝ) k'.1 := by exact_mod_cast h2
  have e3 : min (k.2 : ℝ) k'.2 ≤ c.2 := by exact_mod_cast h3
  have e4 : (c.2 : ℝ) ≤ max (k.2 : ℝ) k'.2 := by exact_mod_cast h4
  refine mem_rS_one.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp only
  · rcases min_choice (k.1 : ℝ) k'.1 with h | h <;> rw [h] at e1 <;> nlinarith
  · rcases max_choice (k.1 : ℝ) k'.1 with h | h <;> rw [h] at e2 <;> nlinarith
  · rcases min_choice (k.2 : ℝ) k'.2 with h | h <;> rw [h] at e3 <;> nlinarith
  · rcases max_choice (k.2 : ℝ) k'.2 with h | h <;> rw [h] at e4 <;> nlinarith

/-- `δ(1,1)` is a leftmost vertex of `𝕊 ∩ δℤ²` -/
lemma gpt_one_one_mem_leftVerts (hδ : 0 < δ) (hδ1 : δ < 1) : gpt δ (1, 1) ∈ leftVerts δ 1 := by
  refine ⟨⟨mem_rS_one.2 ⟨by simp [gpt, hδ], by simp [gpt, hδ1], by simp [gpt, hδ],
    by simp [gpt, hδ1]⟩, ⟨1, 1, by simp [gpt]⟩⟩, fun y ⟨hyS, a, b, hy⟩ => ?_⟩
  rw [hy] at hyS ⊢
  have h0 := (mem_rS_one.1 hyS).1
  simp only at h0 ⊢
  have ha : (0:ℝ) < a := pos_of_mul_pos_left h0 hδ.le
  have ha1 : (1:ℝ) ≤ a := by exact_mod_cast (show (1:ℤ) ≤ a by exact_mod_cast ha)
  simp [gpt]; nlinarith

/-- the right corner index `⌈1/δ⌉ − 1` -/
def mR (δ : ℝ) : ℤ := ⌈1 / δ⌉ - 1

lemma mR_mul_bounds (hδ : 0 < δ) : 1 - δ ≤ (mR δ : ℝ) * δ ∧ (mR δ : ℝ) * δ < 1 := by
  have hc1 : 1 / δ ≤ (⌈1 / δ⌉ : ℝ) := Int.le_ceil _
  have hc2 : (⌈1 / δ⌉ : ℝ) < 1 / δ + 1 := Int.ceil_lt_add_one _
  have e : (mR δ : ℝ) = (⌈1 / δ⌉ : ℝ) - 1 := by simp [mR]
  rw [e]
  have h1 : 1 ≤ (⌈1 / δ⌉ : ℝ) * δ := (div_le_iff₀ hδ).1 hc1
  have h2 : ((⌈1 / δ⌉ : ℝ) - 1) * δ < 1 := (lt_div_iff₀ hδ).1 (by linarith)
  constructor <;> nlinarith

/-- `δ(⌈1/δ⌉ − 1, 1)` is a rightmost vertex of `𝕊 ∩ δℤ²` -/
lemma gpt_mR_mem_rightVerts (hδ : 0 < δ) (hδ4 : δ ≤ 1/4) : gpt δ (mR δ, 1) ∈ rightVerts δ 1 := by
  obtain ⟨h1, h2⟩ := mR_mul_bounds hδ
  refine ⟨⟨mem_rS_one.2 ⟨by simp [gpt]; linarith, by simp [gpt]; linarith, by simp [gpt, hδ],
    by simp [gpt]; linarith⟩, ⟨mR δ, 1, by simp [gpt]⟩⟩, fun y ⟨hyS, a, b, hy⟩ => ?_⟩
  rw [hy] at hyS ⊢
  have h3 := (mem_rS_one.1 hyS).2.1
  simp only at h3 ⊢
  have hc2 : (⌈1 / δ⌉ : ℝ) ≥ 1 / δ := Int.le_ceil _
  have ha : (a:ℝ) < ⌈1 / δ⌉ := by
    have : (a:ℝ) < 1 / δ := by rw [lt_div_iff₀ hδ]; linarith
    linarith
  have ha' : a ≤ mR δ := by
    have : a < ⌈1 / δ⌉ := by exact_mod_cast ha
    unfold mR; omega
  have : (a : ℝ) ≤ mR δ := by exact_mod_cast ha'
  simp [gpt]; nlinarith

end LQGMetric.DFGPS.L36
