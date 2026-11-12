/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_1StepCross at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Defs
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Finset.Max

/-!
# DFGPS Proposition 4.1, Step 2: the deterministic crossing bound

DFGPS (Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380), proof of Proposition 4.1, Step 2
(T:2486–2492): "Each path from `u` to `v` in `B_{ε𝕣}(𝕣L)` must enter `B_{2ε𝕣}(z_k^ε)` for each
`k ∈ [k₁'+2, k₂'−2]`, and hence must cross the annulus `𝔸_{2ε𝕣,3ε𝕣}(z_k^ε)` for each such `k`.
Combining this with (4.2) shows that `D_h(u,v; B_{ε𝕣}(𝕣L)) ≥ ε^ζ 𝔠_{ε𝕣} ∑_k e^{ξh_{ε𝕣}(z_k)}`."

`crossing_sum_le` is the deterministic content of this sentence: if every Euclidean path from `u`
to `v` in `V` comes within `2ρ` of each of the centres `z_i` (`i ∈ S`), whose closed `4ρ`-balls
are pairwise disjoint and do not contain `u`, then `D(u, v; V)` is at least the sum of the
internal crossing distances `D(B̄_{2ρ}(z_i), ∂B_{4ρ}(z_i); B_{16ρ/3}(z_i))`. (The annuli are
`2ρ → 4ρ` instead of DFGPS's `2ε𝕣 → 3ε𝕣`, because the annulus estimate available is DFGPS
Prop 3.1 for `B̄_{3/4}(0) → ∂B_{3/2}(0)` in `B_2(0)`, used at scale `(8/3)ε𝕣`; see DEV-P41-6.)
The argument: for each `i`, the piece of the path between its last exit from `B_{4ρ}(z_i)`
before it first meets `B̄_{2ρ}(z_i)` lies in `B̄_{4ρ}(z_i)`; these time intervals are disjoint,
and the length of a curve is superadditive over disjoint subintervals (`sum_curveLength_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace LQGMetric.DFGPS.P41

open MetricGeometry

/-- Superadditivity of length over finitely many pairwise disjoint subintervals of `[a, b]`. -/
theorem sum_curveLength_le {X : Type*} [PseudoEMetricSpace X] (P : ℝ → X) {ι : Type*}
    (S : Finset ι) (s t : ι → ℝ) (hst : ∀ i ∈ S, s i ≤ t i)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i < s j ∨ t j < s i) :
    ∀ a b : ℝ, (∀ i ∈ S, a ≤ s i ∧ t i ≤ b) →
      ∑ i ∈ S, curveLength P (s i) (t i) ≤ curveLength P a b := by
  classical
  induction S using Finset.induction_on_max_value t with
  | empty => intro a b _; simp
  | insert i S hi hmax ih =>
    intro a b hab
    have hS : ∀ j ∈ S, t j < s i := by
      intro j hj
      have hne : i ≠ j := fun h => hi (h ▸ hj)
      rcases hdisj i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) hne with h | h
      · have := hst j (Finset.mem_insert_of_mem hj)
        have := hmax j hj
        linarith
      · exact h
    have ih' := ih (fun j hj => hst j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk hjk => hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
        hjk) a (s i) (fun j hj => ⟨(hab j (Finset.mem_insert_of_mem hj)).1, (hS j hj).le⟩)
    have hai := hab i (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hi]
    calc curveLength P (s i) (t i) + ∑ j ∈ S, curveLength P (s j) (t j)
        ≤ curveLength P (s i) b + curveLength P a (s i) :=
          add_le_add (curveLength_mono P le_rfl hai.2) ih'
      _ = curveLength P a b := by
          rw [add_comm, curveLength_add P hai.1 ((hst i (Finset.mem_insert_self _ _)).trans hai.2)]

/-- the Euclidean trace of a `D`-path from `u` to `v` inside `V` -/
lemma path_shadow (D : ContMetric) {V : Set ℂ} {u v : ℂ} (γ : Path (D.pt u) (D.pt v))
    (hγV : ∀ t, γ t ∈ D.pt '' V) :
    Continuous (fun τ => D.unpt (γ.extend τ)) ∧ D.unpt (γ.extend 0) = u ∧
      D.unpt (γ.extend 1) = v ∧ (fun τ => D.unpt (γ.extend τ)) '' Icc 0 1 ⊆ V := by
  refine ⟨D.continuous_unpt.comp γ.continuous_extend, by simp, by simp, ?_⟩
  rintro _ ⟨τ, hτ, rfl⟩
  obtain ⟨w, hw, hw'⟩ := hγV ⟨τ, hτ⟩
  have : D.unpt (γ.extend τ) = w := by
    simp only [γ.extend_extends' ⟨τ, hτ⟩]
    exact hw'.symm
  show D.unpt (γ.extend τ) ∈ V
  rw [this]; exact hw

/-- **DFGPS Prop 4.1, Step 2** (T:2486–2492), deterministic part, for one path: the `D`-length of
a path from `u` to `v` which comes within `2ρ` of each of the centres `z_i` (`i ∈ S`), whose
closed `4ρ`-balls are disjoint and do not contain `u`, is at least the sum of the crossing
distances. -/
theorem crossing_sum_le_path (D : ContMetric) {u v : ℂ} {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdisj : (S : Set ι).PairwiseDisjoint fun i => closedBall (z i) (4 * ρ))
    (hu : ∀ i ∈ S, 4 * ρ < ‖u - z i‖) (γ : Path (D.pt u) (D.pt v))
    (hmeet : ∀ i ∈ S, ∃ t ∈ Icc (0 : ℝ) 1, ‖D.unpt (γ.extend t) - z i‖ ≤ 2 * ρ) :
    ∑ i ∈ S, setDistIn D (closedBall (z i) (2 * ρ)) (sphere (z i) (4 * ρ))
      (ball (z i) (16 / 3 * ρ)) ≤ pathLength γ := by
  classical
  set Pe : ℝ → ℂ := fun τ => D.unpt (γ.extend τ) with hPe
  have hPc : Continuous Pe := D.continuous_unpt.comp γ.continuous_extend
  have hP0 : Pe 0 = u := by simp [hPe]
  choose! t ht using hmeet
  -- last exit from `B_{4ρ}(z_i)` before `t_i`
  have hexit : ∀ i ∈ S, ∃ s ∈ Icc (0 : ℝ) (t i), ‖Pe s - z i‖ = 4 * ρ ∧
      ∀ τ ∈ Icc s (t i), ‖Pe τ - z i‖ ≤ 4 * ρ := by
    intro i hi
    set f : ℝ → ℝ := fun τ => ‖Pe τ - z i‖ with hf
    have hfc : Continuous f := (hPc.sub continuous_const).norm
    have hti := ht i hi
    set S₀ : Set ℝ := Icc 0 (t i) ∩ f ⁻¹' Ici (4 * ρ) with hS₀
    have hS₀c : IsCompact S₀ := isCompact_Icc.inter_right (isClosed_Ici.preimage hfc)
    have h0 : (0 : ℝ) ∈ S₀ := ⟨⟨le_rfl, hti.1.1⟩, by
      show 4 * ρ ≤ f 0
      simp only [hf, hP0]; exact (hu i hi).le⟩
    obtain ⟨s, hs, hsmax⟩ := hS₀c.exists_isGreatest ⟨0, h0⟩
    have hfs : f s = 4 * ρ := by
      obtain ⟨τ, hτ, hfτ⟩ := intermediate_value_Icc' hs.1.2 hfc.continuousOn
        ⟨by show f (t i) ≤ 4 * ρ; simp only [hf]; linarith [hti.2], hs.2⟩
      have : τ ≤ s := hsmax ⟨⟨hs.1.1.trans hτ.1, hτ.2⟩, hfτ.ge⟩
      rw [← le_antisymm this hτ.1]; exact hfτ
    refine ⟨s, hs.1, hfs, fun τ hτ => ?_⟩
    by_contra hlt
    push Not at hlt
    have : τ ≤ s := hsmax ⟨⟨hs.1.1.trans hτ.1, hτ.2⟩, hlt.le⟩
    rw [le_antisymm this hτ.1] at hlt
    exact absurd hfs (ne_of_gt hlt)
  choose! s hs using hexit
  have hst : ∀ i ∈ S, s i ≤ t i := fun i hi => (hs i hi).1.2
  -- the pieces are disjoint
  have hdisj' : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i < s j ∨ t j < s i := by
    intro i hi j hj hij
    by_contra hc
    push Not at hc
    set τ := max (s i) (s j)
    have hτi : τ ∈ Icc (s i) (t i) := ⟨le_max_left _ _, max_le (hst i hi) hc.1⟩
    have hτj : τ ∈ Icc (s j) (t j) := ⟨le_max_right _ _, max_le hc.2 (hst j hj)⟩
    have h1 : Pe τ ∈ closedBall (z i) (4 * ρ) := by
      rw [mem_closedBall, dist_eq_norm]; exact (hs i hi).2.2 τ hτi
    have h2 : Pe τ ∈ closedBall (z j) (4 * ρ) := by
      rw [mem_closedBall, dist_eq_norm]; exact (hs j hj).2.2 τ hτj
    exact Set.disjoint_left.1 (hdisj hi hj hij) h1 h2
  -- each piece bounds the crossing distance
  have hpiece : ∀ i ∈ S, setDistIn D (closedBall (z i) (2 * ρ)) (sphere (z i) (4 * ρ))
      (ball (z i) (16 / 3 * ρ)) ≤ curveLength γ.extend (s i) (t i) := by
    intro i hi
    have hmaps : MapsTo γ.extend (Icc (s i) (t i)) (D.pt '' ball (z i) (16 / 3 * ρ)) := by
      intro τ hτ
      refine ⟨Pe τ, ?_, rfl⟩
      rw [mem_ball, dist_eq_norm]
      have := (hs i hi).2.2 τ hτ
      linarith
    have h1 := internalEDist_le_curveLength (hst i hi) γ.continuous_extend.continuousOn hmaps
    refine le_trans ?_ h1
    refine le_trans (iInf₂_le (Pe (t i)) ?_) (le_trans (iInf₂_le (Pe (s i)) ?_) ?_)
    · rw [mem_closedBall, dist_eq_norm]; exact (ht i hi).2
    · rw [mem_sphere, dist_eq_norm]; exact (hs i hi).2.1
    · unfold ContMetric.internal
      rw [internalEDist_comm]
      exact le_rfl
  calc ∑ i ∈ S, setDistIn D (closedBall (z i) (2 * ρ)) (sphere (z i) (4 * ρ))
        (ball (z i) (16 / 3 * ρ))
      ≤ ∑ i ∈ S, curveLength γ.extend (s i) (t i) := Finset.sum_le_sum hpiece
    _ ≤ curveLength γ.extend 0 1 :=
        sum_curveLength_le γ.extend S s t hst hdisj' 0 1 fun i hi =>
          ⟨(hs i hi).1.1, (ht i hi).1.2⟩
    _ = pathLength γ := rfl

end LQGMetric.DFGPS.P41
