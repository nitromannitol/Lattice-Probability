/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightLoop at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.Internal

/-!
# GM S2.4d, curve part: concatenating finitely many paths on `[0, k]` (task P2-TIGHT)

For points `w 0, w 1, …` of a pseudo-emetric space and paths `γ j : w j ⟶ w (j + 1)`,
`concatCurve w γ k : ℝ → X` runs through `γ 0, …, γ (k − 1)` on `[0, 1], …, [k − 1, k]`
(constant outside `[0, k]`). It is continuous, agrees with `t ↦ γ j (t − j)` on `[j, j + 1]`, and
its length on `[0, k]` is `∑_{j<k} len(γ j)`. Used to build the disconnecting loop of GM S2.4d
(D-A3, `decisions/DEC-A.md` (c)). Own elementary construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace GM
namespace Tight

open MetricGeometry

variable {X : Type*} [PseudoEMetricSpace X] (w : ℕ → X) (γ : ∀ k, Path (w k) (w (k + 1)))

/-- the concatenation of `γ 0, …, γ (k - 1)`, parametrized by `[0, k]` -/
def concatCurve : ℕ → ℝ → X
  | 0 => fun _ => w 0
  | k + 1 => fun t => if t ≤ k then concatCurve k t else (γ k).extend (t - k)

lemma concatCurve_succ (k : ℕ) (t : ℝ) :
    concatCurve w γ (k + 1) t = if t ≤ k then concatCurve w γ k t else (γ k).extend (t - k) :=
  rfl

lemma concatCurve_of_ge : ∀ (k : ℕ) (t : ℝ), (k : ℝ) ≤ t → concatCurve w γ k t = w k
  | 0, _, _ => rfl
  | k + 1, t, ht => by
    push_cast at ht
    rw [concatCurve_succ, ite_eq_right (by linarith)]
    exact (γ k).extend_of_one_le (by linarith)

lemma continuous_concatCurve : ∀ k, Continuous (concatCurve w γ k)
  | 0 => continuous_const
  | k + 1 => by
    have : concatCurve w γ (k + 1) =
        fun t => if t ≤ (k : ℝ) then concatCurve w γ k t else (γ k).extend (t - k) := by
      funext t; exact concatCurve_succ w γ k t
    rw [this]
    refine Continuous.if_le (continuous_concatCurve k)
      ((γ k).continuous_extend.comp (continuous_id.sub continuous_const)) continuous_id
      continuous_const fun t ht => ?_
    rw [ht, concatCurve_of_ge w γ k k le_rfl, sub_self, Path.extend_zero]

lemma concatCurve_eqOn : ∀ (k j : ℕ), j < k →
    EqOn (concatCurve w γ k) (fun t => (γ j).extend (t - j)) (Icc (j : ℝ) (j + 1))
  | 0, j, h => absurd h (Nat.not_lt_zero _)
  | k + 1, j, h => by
    intro t ht
    rw [concatCurve_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with hj | rfl
    · have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
      rw [ite_eq_left (ht.2.trans hjk)]
      exact concatCurve_eqOn k j hj ht
    · split_ifs with h1
      · have : t = j := le_antisymm h1 ht.1
        rw [this, concatCurve_of_ge w γ j j le_rfl]
        show w j = (γ j).extend ((j : ℝ) - j)
        rw [sub_self, Path.extend_zero]
      · rfl

/-- length of a shifted path -/
lemma curveLength_shift_extend {x y : X} (p : Path x y) (j : ℝ) :
    curveLength (fun t => p.extend (t - j)) j (j + 1) = pathLength p := by
  have := curveLength_comp_of_continuousOn_monotoneOn p.extend (φ := fun t => t - j)
    (c := j) (d := j + 1) (by linarith) (continuous_id.sub continuous_const).continuousOn
    (fun a _ b _ hab => by simp only; linarith)
  simp only [sub_self, add_sub_cancel_left] at this
  exact this

/-- the length of the concatenation is the sum of the lengths -/
theorem curveLength_concatCurve (k : ℕ) :
    curveLength (concatCurve w γ k) 0 k = ∑ j ∈ Finset.range k, pathLength (γ j) := by
  have := sum_curveLength_eq (concatCurve w γ k) (u := fun i : ℕ => (i : ℝ))
    (fun a b hab => by simp only; exact_mod_cast hab) k
  simp only [Nat.cast_zero, Nat.cast_succ] at this
  rw [← this]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [curveLength_congr (concatCurve_eqOn w γ k j (Finset.mem_range.1 hj)),
    curveLength_shift_extend]

/-- points of `[0, k]` lie on one of the paths -/
lemma concatCurve_mem (k : ℕ) (hk : 0 < k) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) k) :
    ∃ j < k, t ∈ Icc (j : ℝ) (j + 1) ∧ concatCurve w γ k t = (γ j).extend (t - j) := by
  by_cases htk : t < k
  · refine ⟨⌊t⌋₊, ?_, ⟨Nat.floor_le ht.1, (Nat.lt_floor_add_one t).le⟩, ?_⟩
    · exact (Nat.floor_lt ht.1).2 htk
    · exact concatCurve_eqOn w γ k _ ((Nat.floor_lt ht.1).2 htk)
        ⟨Nat.floor_le ht.1, (Nat.lt_floor_add_one t).le⟩
  · have htk' : t = k := le_antisymm ht.2 (not_lt.1 htk)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
    refine ⟨j, by omega, ⟨by rw [htk']; push_cast; linarith, by rw [htk']; push_cast; linarith⟩,
      concatCurve_eqOn w γ _ j (by omega) ⟨by rw [htk']; push_cast; linarith,
        by rw [htk']; push_cast; linarith⟩⟩

/-- points of a path are within its length of its start -/
lemma edist_extend_le_pathLength {x y : X} (p : Path x y) (s : ℝ) :
    edist x (p.extend s) ≤ pathLength p := by
  rcases le_total s 0 with hs | hs
  · rw [p.extend_of_le_zero hs, edist_self]; exact zero_le
  rcases le_total s 1 with hs1 | hs1
  · calc edist x (p.extend s) = edist (p.extend 0) (p.extend s) := by rw [Path.extend_zero]
      _ ≤ curveLength p.extend 0 s := edist_le_curveLength _ hs
      _ ≤ curveLength p.extend 0 1 := curveLength_mono _ le_rfl hs1
  · rw [p.extend_of_one_le hs1]; exact edist_le_pathLength p

end Tight
end GM
end LQGMetric
