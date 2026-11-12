/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.ChiCover at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension
import Mathlib.Topology.Path
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Covering the segment `[1/4, 3/4] × {1/2}` by `M + 1` rational balls (for `χ ≤ 2`)

Deterministic half of DEC-A node DIM.S-chi-le-2 (`decisions/DEC-A.md`, "DIM.S-chi-le-2, proof":
"Cover the segment `[u,v]` by `N ≤ |u−v|/r + 2` open balls with rational centres … so
`D_{γ,δ}(u,v) ≤ N`", following DZZ's covering in the proof of DZZ Lemma 2.12, DZZ:740–746).
With `M = n + 8`, the balls `B(q_i, 1/M)`, `q_i = (1/4 + i/(2M), 1/2)`, `i = 0, …, M`, cover the
horizontal segment from `u = (1/4,1/2)` to `v = (3/4,1/2)`, have closures inside the open unit
square, and give `lgdDZZ μ δ u v ≤ M + 1` as soon as each has `μ`-mass `≤ δ²`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DG

/-- `u = (1/4, 1/2)` -/
def chiU : ℂ := ⟨1 / 4, 1 / 2⟩
/-- `v = (3/4, 1/2)` -/
def chiV : ℂ := ⟨3 / 4, 1 / 2⟩

lemma chiU_mem : chiU ∈ openSquare := by
  simp only [chiU, openSquare, mem_ofPred_eq]; norm_num

lemma chiV_mem : chiV ∈ openSquare := by
  simp only [chiV, openSquare, mem_ofPred_eq]; norm_num

lemma chiU_ne_chiV : chiU ≠ chiV := by
  intro h; have := congrArg Complex.re h; simp [chiU, chiV] at this; norm_num at this

/-- the straight path from `u` to `v` -/
def chiPath : Path chiU chiV where
  toFun t := ⟨1 / 4 + (t : ℝ) / 2, 1 / 2⟩
  continuous_toFun := by
    have : Continuous fun t : unitInterval => ((1 / 4 + (t : ℝ) / 2 : ℝ) : ℂ) +
        ((1 / 2 : ℝ) : ℂ) * Complex.I := by fun_prop
    refine this.congr fun t => ?_
    apply Complex.ext <;> simp
  source' := by apply Complex.ext <;> simp [chiU]
  target' := by apply Complex.ext <;> simp [chiV]; norm_num

/-- the rational centres `q_i = (1/4 + i/(2M), 1/2)`, `M = n + 8` -/
def chiCentre (n : ℕ) (i : Fin (n + 9)) : ℚ × ℚ :=
  (1 / 4 + (i : ℚ) / (2 * ((n : ℚ) + 8)), 1 / 2)

lemma ratPt_chiCentre (n : ℕ) (i : Fin (n + 9)) :
    ratPt (chiCentre n i) = ⟨1 / 4 + (i : ℝ) / (2 * ((n : ℝ) + 8)), 1 / 2⟩ := by
  apply Complex.ext <;> simp [ratPt, chiCentre]

lemma closedBall_chiCentre_subset (n : ℕ) (i : Fin (n + 9)) :
    Metric.closedBall (ratPt (chiCentre n i)) (1 / ((n : ℝ) + 8)) ⊆ openSquare := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm, ratPt_chiCentre] at hz
  have hM : (8 : ℝ) ≤ (n : ℝ) + 8 := by have := n.cast_nonneg (α := ℝ); linarith
  have hr : 1 / ((n : ℝ) + 8) ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hM
  have hi : (i : ℝ) ≤ (n : ℝ) + 8 := by
    have := i.isLt; have : (i : ℕ) ≤ n + 8 := by omega
    exact_mod_cast this
  have hq : (i : ℝ) / (2 * ((n : ℝ) + 8)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hq0 : 0 ≤ (i : ℝ) / (2 * ((n : ℝ) + 8)) := by positivity
  have h1 := Complex.abs_re_le_norm (z - ⟨1 / 4 + (i : ℝ) / (2 * ((n : ℝ) + 8)), 1 / 2⟩)
  have h2 := Complex.abs_im_le_norm (z - ⟨1 / 4 + (i : ℝ) / (2 * ((n : ℝ) + 8)), 1 / 2⟩)
  simp only [Complex.sub_re, Complex.sub_im] at h1 h2
  rw [abs_le] at h1 h2
  simp only [openSquare, mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Covering bound**: if each ball `B(q_i, 1/M)` has `μ`-mass `≤ δ²`, then
`D_δ(u,v) ≤ M + 1 = n + 9`. -/
lemma lgdDZZ_le_of_balls (μ : MeasureTheory.Measure ℂ) (δ : ℝ) (n : ℕ)
    (h : ∀ i : Fin (n + 9), μ (Metric.ball (ratPt (chiCentre n i)) (1 / ((n : ℝ) + 8))) ≤
      ENNReal.ofReal (δ ^ 2)) :
    lgdDZZ μ δ chiU chiV ≤ ((n + 9 : ℕ) : ℕ∞) := by
  unfold lgdDZZ
  refine iInf₂_le (n + 9) ⟨chiCentre n, fun _ => 1 / ((n : ℝ) + 8), chiPath,
    fun i => ⟨by positivity, h i⟩, fun t => ?_⟩
  set M : ℝ := (n : ℝ) + 8 with hM
  have hM0 : 0 < M := by positivity
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  set k := ⌊(t : ℝ) * M⌋₊ with hk
  have hkM : k ≤ n + 8 := by
    have : (t : ℝ) * M ≤ ((n + 8 : ℕ) : ℝ) := by push_cast; nlinarith
    exact (Nat.floor_le_floor this).trans (by rw [Nat.floor_natCast])
  refine ⟨⟨k, by omega⟩, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, ratPt_chiCentre]
  have hfl := Nat.floor_le (show 0 ≤ (t : ℝ) * M by positivity)
  have hfl2 := Nat.lt_floor_add_one ((t : ℝ) * M)
  rw [← hk] at hfl hfl2
  have e : chiPath t - ⟨1 / 4 + ((k : ℕ) : ℝ) / (2 * M), 1 / 2⟩ =
      (((t : ℝ) / 2 - (k : ℝ) / (2 * M) : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; simp [chiPath]
    · rw [Complex.ofReal_im]; simp [chiPath]
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  have hd : (t : ℝ) / 2 - (k : ℝ) / (2 * M) = ((t : ℝ) * M - k) / (2 * M) := by
    field_simp
  rw [hd, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * M), div_lt_iff₀ (by positivity),
    abs_lt]
  constructor
  · have : 0 ≤ (t : ℝ) * M - k := by linarith
    have : 0 < 1 / M * (2 * M) := by positivity
    linarith
  · have : 1 / M * (2 * M) = 2 := by field_simp
    linarith

end DG
end LQGMetric
