/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.LengthSpace at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.CurveLength
import Mathlib.Topology.Path

/-!
# Length of paths, length spaces, internal metrics (GM §1.2)

* `pathLength γ` for `γ : Path x y` is `curveLength γ.extend 0 1`.
  `exists_path_of_curve` turns a curve `P : [a, b] → X` (GM's notion) into a path with the same
  length and the same image, so GM's curves on arbitrary intervals and paths on `[0, 1]` give
  the same notions.
* `IsLengthSpace X` (GM §1.2): for all `x, y` and `ε > 0` there is a path from `x` to `y` of
  length at most `d(x, y) + ε`. `isLengthSpace_iff_curves` is the literal GM form with curves
  on arbitrary intervals.
* `internalEDist Y x y` (GM §1.2, `d(x, y; Y)`): the infimum of the lengths of paths in `Y`
  from `x` to `y`, in `[0, ∞]`. Basic properties: it dominates the metric, is symmetric, satisfies
  the triangle inequality, vanishes on the diagonal of `Y`, is antitone in `Y`, and equals the
  metric on the whole space of a length space.

Sources: Petrunin, *Pure metric geometry* (arXiv:2007.09846), §1 "Length" and "Length spaces"
(`metric.tex`, definition of length metric, page:length metric, line 510); Alexander–Kapovitch–
Petrunin, *Alexandrov geometry: foundations* (arXiv:1903.08539), §2 "Length spaces"
(`metr.tex`, Definition `def:length`, `def:length-space`); Burago–Burago–Ivanov, *A course in
metric geometry*, §2.3 (induced intrinsic metric, Prop. 2.3.4 for additivity/reversal).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Topology unitInterval
open scoped ENNReal

namespace LQGMetric.MetricGeometry

variable {X : Type*} [PseudoEMetricSpace X]

/-- The length of a path `γ : Path x y`, i.e. of `γ.extend` on `[0, 1]`. -/
noncomputable def pathLength {x y : X} (γ : Path x y) : ℝ≥0∞ :=
  curveLength γ.extend 0 1

theorem edist_le_pathLength {x y : X} (γ : Path x y) : edist x y ≤ pathLength γ := by
  have := edist_le_curveLength γ.extend zero_le_one
  rwa [Path.extend_zero, Path.extend_one] at this

theorem pathLength_refl (x : X) : pathLength (Path.refl x) = 0 :=
  eVariationOn.constant_on (by
    rintro _ ⟨s, -, rfl⟩ _ ⟨t, -, rfl⟩
    simp [Path.extend, Set.IccExtend])

theorem pathLength_symm {x y : X} (γ : Path x y) : pathLength γ.symm = pathLength γ := by
  unfold pathLength
  rw [Path.extend_symm]
  simpa using curveLength_reverse γ.extend (zero_le_one' ℝ)

theorem pathLength_trans {x y z : X} (γ : Path x y) (γ' : Path y z) :
    pathLength (γ.trans γ') = pathLength γ + pathLength γ' := by
  unfold pathLength
  rw [← curveLength_add _ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  have h1 : curveLength (γ.trans γ').extend 0 (1 / 2) = curveLength γ.extend 0 1 := by
    rw [curveLength_congr (Q := γ.extend ∘ fun t => 2 * t)
      (fun t ht => Path.extend_trans_of_le_half _ _ ht.2)]
    rw [curveLength_comp_of_continuousOn_monotoneOn _ (by norm_num) (by fun_prop)
      (fun s _ t _ hst => by linarith)]
    norm_num
  have h2 : curveLength (γ.trans γ').extend (1 / 2) 1 = curveLength γ'.extend 0 1 := by
    rw [curveLength_congr (Q := γ'.extend ∘ fun t => 2 * t - 1)
      (fun t ht => Path.extend_trans_of_half_le _ _ ht.1)]
    rw [curveLength_comp_of_continuousOn_monotoneOn _ (by norm_num) (by fun_prop)
      (fun s _ t _ hst => by linarith)]
    norm_num
  rw [h1, h2]

/-- A curve `P : [a, b] → X` (GM's notion of curve) gives a path from `P a` to `P b` with the
same length and image (affine reparametrization `t ↦ a + t (b - a)`). -/
theorem exists_path_of_curve {P : ℝ → X} {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b)) :
    ∃ γ : Path (P a) (P b), pathLength γ = curveLength P a b ∧ Set.range γ ⊆ P '' Icc a b := by
  set φ : ℝ → ℝ := fun t => a + t * (b - a)
  have hφmono : Monotone φ := fun s t hst => by
    simp only [φ]; nlinarith [sub_nonneg.2 hab]
  have hφmaps : ∀ t : I, φ t ∈ Icc a b := fun t =>
    ⟨by simp only [φ]; nlinarith [t.2.1, sub_nonneg.2 hab],
      by simp only [φ]; nlinarith [t.2.2, sub_nonneg.2 hab]⟩
  let γ : Path (P a) (P b) :=
    { toFun := fun t => P (φ t)
      continuous_toFun := hP.comp_continuous (by fun_prop) hφmaps
      source' := by simp [φ]
      target' := by simp [φ] }
  refine ⟨γ, ?_, ?_⟩
  · unfold pathLength
    rw [curveLength_congr (Q := P ∘ φ) (fun t ht => by simp [γ, Path.extend_apply _ ht])]
    rw [curveLength_comp_of_continuousOn_monotoneOn _ zero_le_one (by fun_prop)
      (hφmono.monotoneOn _)]
    simp [φ]
  · rintro _ ⟨t, rfl⟩
    exact ⟨φ t, hφmaps t, rfl⟩

/-- **Length space** (GM §1.2): for all `x, y` and `ε > 0` there is a path from `x` to `y` of
length at most `d(x, y) + ε`. -/
def IsLengthSpace (X : Type*) [PseudoEMetricSpace X] : Prop :=
  ∀ x y : X, ∀ ε : ℝ, 0 < ε → ∃ γ : Path x y, pathLength γ ≤ edist x y + ENNReal.ofReal ε

/-- GM's literal definition (curves `P : [a, b] → X`) is equivalent to `IsLengthSpace`. -/
theorem isLengthSpace_iff_curves :
    IsLengthSpace X ↔ ∀ x y : X, ∀ ε : ℝ, 0 < ε → ∃ (P : ℝ → X) (a b : ℝ), a ≤ b ∧
      ContinuousOn P (Icc a b) ∧ P a = x ∧ P b = y ∧
      curveLength P a b ≤ edist x y + ENNReal.ofReal ε := by
  constructor
  · intro h x y ε hε
    obtain ⟨γ, hγ⟩ := h x y ε hε
    exact ⟨γ.extend, 0, 1, zero_le_one, γ.continuous_extend.continuousOn, Path.extend_zero γ,
      Path.extend_one γ, hγ⟩
  · intro h x y ε hε
    obtain ⟨P, a, b, hab, hP, rfl, rfl, hlen⟩ := h x y ε hε
    obtain ⟨γ, hγ, -⟩ := exists_path_of_curve hab hP
    exact ⟨γ, hγ ▸ hlen⟩

/-- The **internal metric** `d(x, y; Y)` (GM §1.2): the infimum of the lengths of paths from `x`
to `y` contained in `Y` (`∞` if there is none). -/
noncomputable def internalEDist (Y : Set X) (x y : X) : ℝ≥0∞ :=
  ⨅ γ : {γ : Path x y // ∀ t, γ t ∈ Y}, pathLength γ.1

theorem internalEDist_le_pathLength {Y : Set X} {x y : X} (γ : Path x y) (hγ : ∀ t, γ t ∈ Y) :
    internalEDist Y x y ≤ pathLength γ :=
  iInf_le_of_le ⟨γ, hγ⟩ le_rfl

theorem edist_le_internalEDist (Y : Set X) (x y : X) : edist x y ≤ internalEDist Y x y :=
  le_iInf fun γ => edist_le_pathLength γ.1

theorem internalEDist_self {Y : Set X} {x : X} (hx : x ∈ Y) : internalEDist Y x x = 0 :=
  le_antisymm ((internalEDist_le_pathLength (Path.refl x) fun _ => hx).trans_eq
    (pathLength_refl x)) bot_le

theorem internalEDist_comm (Y : Set X) (x y : X) : internalEDist Y x y = internalEDist Y y x := by
  have key : ∀ x y : X, internalEDist Y y x ≤ internalEDist Y x y := fun x y =>
    le_iInf fun γ => (internalEDist_le_pathLength γ.1.symm fun t => γ.2 _).trans_eq
      (pathLength_symm γ.1)
  exact le_antisymm (key y x) (key x y)

theorem internalEDist_triangle (Y : Set X) (x y z : X) :
    internalEDist Y x z ≤ internalEDist Y x y + internalEDist Y y z :=
  ENNReal.le_iInf_add_iInf fun γ γ' =>
    (internalEDist_le_pathLength (γ.1.trans γ'.1) fun t => by
      rw [Path.trans_apply]; split_ifs
      · exact γ.2 _
      · exact γ'.2 _).trans_eq (pathLength_trans γ.1 γ'.1)

/-- The internal metric is antitone in the subset. -/
theorem internalEDist_anti {Y Z : Set X} (hYZ : Y ⊆ Z) (x y : X) :
    internalEDist Z x y ≤ internalEDist Y x y :=
  le_iInf fun γ => internalEDist_le_pathLength γ.1 fun t => hYZ (γ.2 t)

/-- In a length space the internal metric of the whole space is the metric. -/
theorem internalEDist_univ_of_isLengthSpace (hX : IsLengthSpace X) (x y : X) :
    internalEDist univ x y = edist x y := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
    (edist_le_internalEDist _ x y)
  obtain ⟨γ, hγ⟩ := hX x y ε (by exact_mod_cast hε)
  refine (internalEDist_le_pathLength (Y := univ) γ fun _ => Set.mem_univ _).trans (hγ.trans_eq ?_)
  rw [ENNReal.ofReal_coe_nnreal]

end LQGMetric.MetricGeometry
