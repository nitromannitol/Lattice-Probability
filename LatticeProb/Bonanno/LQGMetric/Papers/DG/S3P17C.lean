/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P17C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17B
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Chains of dyadic squares between two points of `𝕊` (DG (3.32))

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, (3.32) (DG:1425–1430): the
minimum defining `D̂^δ(z, w; 𝕊)` is over sequences of distinct squares `S_0, …, S_k ∈ 𝒮_{2^{-m_δ}}`
with `z ∈ S_0`, `w ∈ S_k`, consecutive ones sharing a side. DG use implicitly that such a
sequence exists for all `z, w ∈ 𝕊`; this file proves it (own elementary argument: the grid graph
is connected, a shortest walk is a path, `SimpleGraph.Walk.bypass`).
-/

noncomputable section

open Set

namespace LQGMetric.DG

open Blueprint

/-- the grid graph on the dyadic squares of `𝕊` -/
def p17Grid (m : ℕ) : SimpleGraph {k : ℤ × ℤ // k ∈ dgIdx m} where
  Adj a b := dgAdj a.1 b.1
  symm := ⟨fun a b h => by
    unfold dgAdj at *
    rw [abs_sub_comm, abs_sub_comm b.1.2]; exact h⟩
  loopless := ⟨fun a h => by unfold dgAdj at h; simp at h⟩

lemma p17_reach_snd {m : ℕ} (i : ℤ) (hi : 0 ≤ i ∧ i < 2 ^ m) :
    ∀ n : ℕ, ∀ j : ℤ, 0 ≤ j → j + n < 2 ^ m →
      ∀ (h₁ : (i, j) ∈ dgIdx m) (h₂ : (i, j + n) ∈ dgIdx m),
        (p17Grid m).Reachable ⟨(i, j), h₁⟩ ⟨(i, j + n), h₂⟩ := by
  intro n
  induction n with
  | zero => intro j _ _ h₁ h₂; simp only [CharP.cast_eq_zero, add_zero]; rfl
  | succ n ih =>
    intro j hj hjn h₁ h₂
    have h₃ : (i, j + n) ∈ dgIdx m := ⟨hi.1, hi.2, by omega, by push_cast at hjn; omega⟩
    refine (ih j hj (by push_cast at hjn; omega) h₁ h₃).trans (SimpleGraph.Adj.reachable ?_)
    show |i - i| + |(j + n) - (j + ((n + 1 : ℕ) : ℤ))| = 1
    push_cast; simp

lemma p17_reach_fst {m : ℕ} (j : ℤ) (hj : 0 ≤ j ∧ j < 2 ^ m) :
    ∀ n : ℕ, ∀ i : ℤ, 0 ≤ i → i + n < 2 ^ m →
      ∀ (h₁ : (i, j) ∈ dgIdx m) (h₂ : (i + n, j) ∈ dgIdx m),
        (p17Grid m).Reachable ⟨(i, j), h₁⟩ ⟨(i + n, j), h₂⟩ := by
  intro n
  induction n with
  | zero => intro i _ _ h₁ h₂; simp only [CharP.cast_eq_zero, add_zero]; rfl
  | succ n ih =>
    intro i hi hin h₁ h₂
    have h₃ : (i + n, j) ∈ dgIdx m := ⟨by omega, by push_cast at hin; omega, hj.1, hj.2⟩
    refine (ih i hi (by push_cast at hin; omega) h₁ h₃).trans (SimpleGraph.Adj.reachable ?_)
    show |(i + n) - (i + ((n + 1 : ℕ) : ℤ))| + |j - j| = 1
    push_cast; simp

lemma p17_reach_snd' {m : ℕ} (a b : {k : ℤ × ℤ // k ∈ dgIdx m}) (h : a.1.1 = b.1.1) :
    (p17Grid m).Reachable a b := by
  obtain ⟨⟨i, j⟩, ha⟩ := a
  obtain ⟨⟨i', j'⟩, hb⟩ := b
  simp only at h
  subst h
  rcases le_total j j' with hjj | hjj
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, j' = j + n := ⟨(j' - j).toNat, by omega⟩
    subst hn
    exact p17_reach_snd i ⟨ha.1, ha.2.1⟩ n j ha.2.2.1 hb.2.2.2 ha hb
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = j' + n := ⟨(j - j').toNat, by omega⟩
    subst hn
    exact (p17_reach_snd i ⟨ha.1, ha.2.1⟩ n j' hb.2.2.1 ha.2.2.2 hb ha).symm

lemma p17_reach_fst' {m : ℕ} (a b : {k : ℤ × ℤ // k ∈ dgIdx m}) (h : a.1.2 = b.1.2) :
    (p17Grid m).Reachable a b := by
  obtain ⟨⟨i, j⟩, ha⟩ := a
  obtain ⟨⟨i', j'⟩, hb⟩ := b
  simp only at h
  subst h
  rcases le_total i i' with hii | hii
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, i' = i + n := ⟨(i' - i).toNat, by omega⟩
    subst hn
    exact p17_reach_fst j ⟨ha.2.2.1, ha.2.2.2⟩ n i ha.1 hb.2.1 ha hb
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, i = i' + n := ⟨(i - i').toNat, by omega⟩
    subst hn
    exact (p17_reach_fst j ⟨ha.2.2.1, ha.2.2.2⟩ n i' hb.1 ha.2.1 hb ha).symm

lemma p17_reach {m : ℕ} (a b : {k : ℤ × ℤ // k ∈ dgIdx m}) : (p17Grid m).Reachable a b := by
  have hc : (b.1.1, a.1.2) ∈ dgIdx m := ⟨b.2.1, b.2.2.1, a.2.2.2.1, a.2.2.2.2⟩
  exact (p17_reach_fst' a ⟨_, hc⟩ rfl).trans (p17_reach_snd' ⟨_, hc⟩ b rfl)

/-- every point of `𝕊` lies in a dyadic square of `𝒮_{2^{-m}}` -/
lemma p17_exists_sq (m : ℕ) {z : ℂ} (hz : z ∈ closedUnitSquare) :
    ∃ k ∈ dgIdx m, z ∈ gridSquare ((2 : ℝ)⁻¹ ^ m) k := by
  have hs : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  have e : (2 : ℝ)⁻¹ ^ m * (2 : ℝ) ^ m = 1 := by rw [← mul_pow]; norm_num
  have hpos : (0 : ℤ) < 2 ^ m := by positivity
  have coord : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∃ a : ℤ, 0 ≤ a ∧ a < 2 ^ m ∧
      (a : ℝ) * (2 : ℝ)⁻¹ ^ m ≤ x ∧ x ≤ (a + 1) * (2 : ℝ)⁻¹ ^ m := by
    intro x hx0 hx1
    set y := x * (2 : ℝ) ^ m
    have hy0 : 0 ≤ y := by positivity
    have hxy : x = y * (2 : ℝ)⁻¹ ^ m := by
      simp only [y]; rw [mul_assoc, mul_comm ((2 : ℝ) ^ m), e, mul_one]
    have hy1 : y ≤ (2 : ℝ) ^ m := by simp only [y]; nlinarith [pow_pos (two_pos (α := ℝ)) m]
    refine ⟨min ⌊y⌋ (2 ^ m - 1), le_min (Int.floor_nonneg.2 hy0) (by omega), by omega, ?_, ?_⟩
    · rw [hxy]
      refine mul_le_mul_of_nonneg_right ?_ hs.le
      exact (Int.cast_le.2 (min_le_left _ _)).trans (Int.floor_le y)
    · rw [hxy]
      refine mul_le_mul_of_nonneg_right ?_ hs.le
      rcases le_total ⌊y⌋ (2 ^ m - 1) with h | h
      · rw [min_eq_left h]; exact (Int.lt_floor_add_one y).le
      · rw [min_eq_right h]; push_cast; linarith
  obtain ⟨a, ha0, ha1, ha2, ha3⟩ := coord z.re hz.1 hz.2.1
  obtain ⟨b, hb0, hb1, hb2, hb3⟩ := coord z.im hz.2.2.1 hz.2.2.2
  exact ⟨(a, b), ⟨ha0, ha1, hb0, hb1⟩, ha2, ha3, hb2, hb3⟩

/-- **chains of squares exist** between any two points of `𝕊` -/
theorem p17_exists_chain (m : ℕ) {z w : ℂ} (hz : z ∈ closedUnitSquare)
    (hw : w ∈ closedUnitSquare) : Nonempty {L : List (ℤ × ℤ) // IsDGSqChain m z w L} := by
  classical
  obtain ⟨a, ha, hza⟩ := p17_exists_sq m hz
  obtain ⟨b, hb, hwb⟩ := p17_exists_sq m hw
  obtain ⟨p⟩ := p17_reach (m := m) ⟨a, ha⟩ ⟨b, hb⟩
  set q := p.bypass
  have hq : q.IsPath := p.bypass_isPath
  refine ⟨⟨q.support.map Subtype.val, (List.nodup_map_iff Subtype.val_injective).2 hq.support_nodup,
    fun k hk => ?_, ?_, ⟨a, ?_, hza⟩, ⟨b, ?_, hwb⟩⟩⟩
  · obtain ⟨k', -, rfl⟩ := List.mem_map.1 hk; exact k'.2
  · exact List.isChain_map_of_isChain (R := (p17Grid m).Adj) Subtype.val (fun x y h => h)
      q.isChain_adj_support
  · rw [← SimpleGraph.Walk.cons_tail_support]; exact Option.mem_def.2 rfl
  · rw [List.getLast?_map, List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil _),
      SimpleGraph.Walk.getLast_support]; simp

/-- **DG (eqn-lfpp-lower-last)** for `z, w ∈ 𝕊` (the chain exists, `p17_exists_chain`) -/
theorem dg_prop317_step3' {μ : MeasureTheory.Measure ℂ} {ε : ℝ} {Q : Set ℂ} {δ ξ T Lb ρ : ℝ}
    (hδ : 0 < δ) (hT : 0 < T) {φ : ℂ → ℝ} {Y : ℤ × ℤ → Set ℂ}
    (hY : ∀ k ∈ dgIdx (dgM δ), ∀ y ∈ Y k, ∀ y' ∈ Y k, (dgLGD μ ε Q y y' : ENNReal) ≤
      ENNReal.ofReal (T * Real.exp (ξ * φ (dgCenter (dgM δ) k))))
    (hadj : ∀ k k', dgAdj k k' → (Y k ∩ Y k').Nonempty)
    (hnear : ∀ k ∈ dgIdx (dgM δ), ∀ x ∈ gridSquare ((2 : ℝ)⁻¹ ^ dgM δ) k, ∃ y ∈ Y k, ‖y - x‖ ≤ ρ)
    {z w : ℂ} (hz : z ∈ closedUnitSquare) (hw : w ∈ closedUnitSquare)
    (hLb : ∀ y y' : ℂ, ‖y - z‖ ≤ ρ → ‖y' - w‖ ≤ ρ → ENNReal.ofReal Lb ≤ dgLGD μ ε Q y y') :
    Lb * δ ≤ T * dgApproxLFPP ξ δ φ z w :=
  dg_prop317_step3 hδ hT hY hadj hnear hLb (p17_exists_chain _ hz hw)

end LQGMetric.DG
