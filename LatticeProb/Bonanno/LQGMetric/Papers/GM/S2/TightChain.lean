/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightChain at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
Decision D-A3 (`decisions/DEC-A.md` (c), S2.4c): "connectedness of `K′` and a `b/2`-net of `N(b)`
points give a chain of at most `N(b)` such steps between any two points". Here:
`exists_chain_compact`: for `U ⊆ ℂ` open and connected and `K ⊆ U` compact there is a compact
`L` with `K ⊆ L ⊆ U` such that for every `b > 0` some `N` joins any two points of `K` by a chain
of `N` steps of Euclidean length `≤ b` inside `L` (`L` = a closed `δ`-thickening of `K` plus
finitely many paths in `U`, which exist since connected open sets of `ℂ` are path connected).
Own elementary argument (D-A3; DEVIATIONS DA5).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology

namespace LQGMetric
namespace GM
namespace Tight

/-- `u` and `v` are joined inside `L` by a chain of `N` steps of length `≤ b` (the chain is an
eventually constant sequence) -/
def ChainJoined (L : Set ℂ) (b : ℝ) (N : ℕ) (u v : ℂ) : Prop :=
  ∃ x : ℕ → ℂ, x 0 = u ∧ (∀ i, x i ∈ L) ∧ (∀ i, ‖x i - x (i + 1)‖ ≤ b) ∧ ∀ i, N ≤ i → x i = v

variable {L : Set ℂ} {b : ℝ} {N N₁ N₂ : ℕ} {u v w : ℂ}

lemma ChainJoined.mono (h : ChainJoined L b N u v) {N' : ℕ} (hN : N ≤ N') :
    ChainJoined L b N' u v :=
  let ⟨x, h0, hL, hs, he⟩ := h
  ⟨x, h0, hL, hs, fun i hi => he i (hN.trans hi)⟩

lemma ChainJoined.symm (hb : 0 ≤ b) (h : ChainJoined L b N u v) : ChainJoined L b N v u := by
  obtain ⟨x, h0, hL, hs, he⟩ := h
  refine ⟨fun i => x (N - i), by simpa using he N le_rfl, fun i => hL _, fun i => ?_,
    fun i hi => ?_⟩
  · by_cases hi : i < N
    · have e : N - i = (N - (i + 1)) + 1 := by omega
      simp only
      rw [e, norm_sub_rev]
      exact hs _
    · have h1 : N - i = 0 := by omega
      have h2 : N - (i + 1) = 0 := by omega
      simp only [h1, h2, sub_self, norm_zero]
      exact hb
  · simp only
    rw [show N - i = 0 by omega, h0]

lemma ChainJoined.trans (h₁ : ChainJoined L b N₁ u w) (h₂ : ChainJoined L b N₂ w v) :
    ChainJoined L b (N₁ + N₂) u v := by
  obtain ⟨x, h0, hL, hs, he⟩ := h₁
  obtain ⟨y, h0', hL', hs', he'⟩ := h₂
  refine ⟨fun i => if i ≤ N₁ then x i else y (i - N₁), by simp [h0], fun i => ?_, fun i => ?_,
    fun i hi => ?_⟩
  · dsimp only
    split_ifs
    exacts [hL i, hL' _]
  · dsimp only
    by_cases h1 : i + 1 ≤ N₁
    · rw [ite_eq_left (by omega), ite_eq_left h1]; exact hs i
    · by_cases h2 : i = N₁
      · subst h2
        rw [ite_eq_left le_rfl, ite_eq_right h1, he i le_rfl, Nat.add_sub_cancel_left, ← h0']
        exact hs' 0
      · rw [ite_eq_right (by omega), ite_eq_right h1, show i + 1 - N₁ = (i - N₁) + 1 by omega]
        exact hs' _
  · dsimp only
    split_ifs with h
    · have hi' : i = N₁ := by omega
      rw [hi', he N₁ le_rfl, ← h0']
      exact he' 0 (by omega)
    · exact he' _ (by omega)

/-- A curve `f : [0,1] → L` with modulus `|s - t| ≤ 1/m ⇒ ‖f s - f t‖ ≤ b` gives an `m`-step
chain. -/
lemma chainJoined_of_fun {m : ℕ} (hm : 0 < m) {f : ℝ → ℂ} (hf0 : f 0 = u) (hf1 : f 1 = v)
    (hfL : ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ L)
    (hmod : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |s - t| ≤ 1 / m → ‖f s - f t‖ ≤ b) :
    ChainJoined L b m u v := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hI : ∀ i : ℕ, min ((i : ℝ) / m) 1 ∈ Icc (0 : ℝ) 1 := fun i =>
    ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
  refine ⟨fun i => f (min ((i : ℝ) / m) 1), by simp [hf0], fun i => hfL _ (hI i),
    fun i => hmod _ (hI i) _ (hI (i + 1)) ?_, fun i hi => ?_⟩
  · refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero]
    refine max_le (le_of_eq ?_) (by positivity)
    rw [abs_sub_comm, show ((i + 1 : ℕ) : ℝ) / m - (i : ℝ) / m = 1 / m by push_cast; ring]
    exact abs_of_pos (by positivity)
  · simp only
    rw [min_eq_right ((le_div_iff₀ hm').2 (by simpa using (show (m : ℝ) ≤ i by exact_mod_cast hi))),
      hf1]

/-- Paths give chains. -/
lemma exists_chainJoined_of_path (hb : 0 < b) (γ : Path u v) (hγ : ∀ t, γ t ∈ L) :
    ∃ m : ℕ, ChainJoined L b m u v := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    (γ.continuous_extend.continuousOn (s := Icc (0 : ℝ) 1))
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc b hb
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n + 1, chainJoined_of_fun n.succ_pos γ.extend_zero γ.extend_one
    (fun t _ => hγ _) fun s hs t ht hst => ?_⟩
  rw [← dist_eq_norm]
  refine (hδ' s hs t ht ?_).le
  rw [Real.dist_eq]
  push_cast at hst
  exact lt_of_le_of_lt hst hn

/-- Segments in a ball give chains. -/
lemma chainJoined_segment {δ : ℝ} (hb : 0 < b) {x : ℂ} (hux : ‖u - x‖ ≤ δ)
    (hL : closedBall x δ ⊆ L) : ChainJoined L b (⌈δ / b⌉₊ + 1) u x := by
  have hm : (0 : ℝ) < (⌈δ / b⌉₊ + 1 : ℕ) := by positivity
  refine chainJoined_of_fun (Nat.succ_pos _) (f := fun t => u + (t : ℂ) * (x - u))
    (by simp) (by simp) (fun t ht => hL ?_) fun s _ t _ hst => ?_
  · rw [mem_closedBall, dist_eq_norm,
      show u + (t : ℂ) * (x - u) - x = ((1 - t : ℝ) : ℂ) * (u - x) by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
    nlinarith [ht.1, norm_nonneg (u - x)]
  · rw [show u + (s : ℂ) * (x - u) - (u + (t : ℂ) * (x - u)) = ((s - t : ℝ) : ℂ) * (x - u) by
        push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev]
    have h1 : |s - t| * ‖u - x‖ ≤ 1 / (⌈δ / b⌉₊ + 1 : ℕ) * δ :=
      mul_le_mul hst hux (norm_nonneg _) (by positivity)
    refine h1.trans ?_
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hm]
    have := Nat.le_ceil (δ / b)
    rw [div_le_iff₀ hb] at this
    push_cast
    nlinarith

/-- **Chains in a domain** (D-A3, S2.4c). -/
theorem exists_chain_compact {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U) {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : Set ℂ, IsCompact L ∧ K ⊆ L ∧ L ⊆ U ∧
      ∀ b : ℝ, 0 < b → ∃ N : ℕ, ∀ u ∈ K, ∀ v ∈ K, ChainJoined L b N u v := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨∅, isCompact_empty, subset_rfl, empty_subset _, fun _ _ => ⟨0, by simp⟩⟩
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨T, hTK, hTfin, hcover⟩ := finite_cover_balls_of_compact hK hδ
  have hpc := hU.isConnected_iff_isPathConnected.1 hUc
  classical
  let g : ℂ → Set ℂ := fun x => if hx : x ∈ K then
    range (hpc.joinedIn x₀ (hKU hx₀) x (hKU hx)).somePath else ∅
  let L : Set ℂ := cthickening δ K ∪ ⋃ x ∈ T, g x
  have hgK : ∀ x (hx : x ∈ K), g x = range (hpc.joinedIn x₀ (hKU hx₀) x (hKU hx)).somePath :=
    fun x hx => by simp only [g, hx, dite_true]
  refine ⟨L, (hK.cthickening).union (hTfin.isCompact_biUnion fun x hx => ?_),
    (self_subset_cthickening K).trans subset_union_left,
    union_subset hδU (iUnion₂_subset fun x hx => ?_), fun b hb => ?_⟩
  · rw [hgK x (hTK hx)]; exact isCompact_range (Path.continuous _)
  · rw [hgK x (hTK hx)]
    exact range_subset_iff.2 fun t => JoinedIn.somePath_mem _ t
  have hpath : ∀ x ∈ T, ∃ m, ChainJoined L b m x₀ x := fun x hx =>
    exists_chainJoined_of_path hb _ fun t => Or.inr (mem_biUnion hx (by
      rw [hgK x (hTK hx)]; exact mem_range_self t))
  choose! m hm using hpath
  let M : ℕ := ∑ x ∈ hTfin.toFinset, m x
  have hM : ∀ x ∈ T, ChainJoined L b M x₀ x := fun x hx =>
    (hm x hx).mono (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hTfin.mem_toFinset.2 hx))
  have hto : ∀ u ∈ K, ChainJoined L b ((⌈δ / b⌉₊ + 1) + M) u x₀ := fun u hu => by
    obtain ⟨x, hxT, hux⟩ := mem_iUnion₂.1 (hcover hu)
    refine (chainJoined_segment hb ?_ ?_).trans ((hM x hxT).symm hb.le)
    · rw [← dist_eq_norm]; exact (mem_ball.1 hux).le
    · exact (closedBall_subset_cthickening (hTK hxT) δ).trans subset_union_left
  exact ⟨_, fun u hu v hv => (hto u hu).trans ((hto v hv).symm hb.le)⟩

end Tight
end GM
end LQGMetric
