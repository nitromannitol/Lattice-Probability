/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412fSel
import Mathlib.Data.Rat.Denumerable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The Effros σ-algebra and a measurable dense sequence of a random closed set (DEC-120 §4, J3)

CONF (arXiv:1905.00381, `confluence-final.tex`) C:1514, C:1740–1744 chooses the arc families
`𝓘₀` of `∂𝓑^•_τ` "in a manner depending only on `(𝓑^•_τ, h|)`". DEC-120 §4 (DV-D120-1) replaces
CONF's harmonic-measure arcs by a canonical subdivision obtained by measurable point selection.
This file provides the measurable-selection layer, as a function of the set `Γ` itself:

* `effrosSigma`: the hit (Effros) σ-algebra on `Set ℂ` (DEC-120 §4, exact text);
* `t39jBall j = closedBall (t39jBc j) (t39jBr j)`: an enumeration of the closed balls with
  rational centres and radii `1/(n+1)`; `t39j_ball_basis`;
* `t39j_hit_closure_compact`: `{Γ | (closure Γ ∩ K).Nonempty}` is Effros-measurable for compact `K`;
* `t39jValid j Γ := (closure Γ ∩ t39jBall j).Nonempty`, `t39jPt j Γ ∈ closure Γ ∩ t39jBall j`
  (when valid), Effros-measurable (`GM.p412f_meas_select`, the lexicographic minimum, applied on
  `Ω := Set ℂ`), and its density `t39j_pt_dense`.

Own elementary arguments (standard; the Kuratowski–Ryll-Nardzewski theorem is not in mathlib).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace LQGMetric.CONF

/-- the hit (Effros) σ-algebra on `Set ℂ` -/
def effrosSigma : MeasurableSpace (Set ℂ) :=
  MeasurableSpace.generateFrom {E | ∃ U : Set ℂ, IsOpen U ∧ E = {Γ | (Γ ∩ U).Nonempty}}

theorem t39j_hit_open {U : Set ℂ} (hU : IsOpen U) :
    MeasurableSet[effrosSigma] {Γ : Set ℂ | (Γ ∩ U).Nonempty} :=
  MeasurableSpace.measurableSet_generateFrom ⟨U, hU, rfl⟩

/-- the parameters of the `j`-th rational closed ball -/
def t39jPar (j : ℕ) : ℚ × ℚ × ℕ := (Denumerable.eqv (ℚ × ℚ × ℕ)).symm j

/-- centre of the `j`-th rational closed ball -/
def t39jBc (j : ℕ) : ℂ := ⟨((t39jPar j).1 : ℝ), ((t39jPar j).2.1 : ℝ)⟩

/-- radius of the `j`-th rational closed ball -/
def t39jBr (j : ℕ) : ℝ := 1 / ((t39jPar j).2.2 + 1)

/-- the `j`-th rational closed ball -/
def t39jBall (j : ℕ) : Set ℂ := closedBall (t39jBc j) (t39jBr j)

theorem t39jBr_pos (j : ℕ) : 0 < t39jBr j := by unfold t39jBr; positivity

theorem t39jBall_isCompact (j : ℕ) : IsCompact (t39jBall j) := isCompact_closedBall _ _

/-- every point has arbitrarily small rational closed balls around it -/
theorem t39j_ball_basis (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ j, x ∈ t39jBall j ∧ t39jBall j ⊆ ball x ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
  have hr : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x.re - 1 / ((n : ℝ) + 1) / 2 < x.re by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x.im - 1 / ((n : ℝ) + 1) / 2 < x.im by linarith)
  obtain ⟨j₀, hp⟩ := (Denumerable.eqv (ℚ × ℚ × ℕ)).symm.surjective (a, b, n)
  replace hp : t39jPar j₀ = (a, b, n) := hp
  have hc : dist (⟨(a : ℝ), (b : ℝ)⟩ : ℂ) x ≤ 1 / ((n : ℝ) + 1) / 2 + 1 / ((n : ℝ) + 1) / 2 := by
    rw [Complex.dist_eq]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  refine ⟨j₀, ?_, ?_⟩
  all_goals unfold t39jBall t39jBc t39jBr; rw [hp]
  · rw [mem_closedBall, dist_comm]; push_cast; linarith
  · intro y hy
    rw [mem_closedBall] at hy
    rw [mem_ball]
    push_cast at hy
    linarith [dist_triangle y (⟨(a : ℝ), (b : ℝ)⟩ : ℂ) x]

/-- **hit events of a compact set by the closure** are Effros-measurable -/
theorem t39j_hit_closure_compact {K : Set ℂ} (hK : IsCompact K) :
    MeasurableSet[effrosSigma] {Γ : Set ℂ | (closure Γ ∩ K).Nonempty} := by
  have heq : {Γ : Set ℂ | (closure Γ ∩ K).Nonempty} =
      ⋂ n : ℕ, {Γ | (Γ ∩ thickening (1 / ((n : ℝ) + 1)) K).Nonempty} := by
    ext Γ
    simp only [mem_setOf_eq, mem_iInter]
    constructor
    · rintro ⟨x, hxc, hxK⟩ n
      obtain ⟨y, hyB, hyΓ⟩ := mem_closure_iff.1 hxc _ isOpen_ball
        (mem_ball_self (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity))
      exact ⟨y, hyΓ, mem_thickening_iff.2 ⟨x, hxK, by rw [mem_ball] at hyB; exact hyB⟩⟩
    · intro H
      choose y hyΓ hyK using H
      choose z hzK hzy using fun n => mem_thickening_iff.1 (hyK n)
      obtain ⟨w, hwK, φ, hφ, hlim⟩ := hK.tendsto_subseq hzK
      refine ⟨w, mem_closure_of_tendsto (f := y ∘ φ) (b := atTop) ?_ (Eventually.of_forall fun n => hyΓ _),
        hwK⟩
      have h1 : Tendsto (fun n => dist ((y ∘ φ) n) ((z ∘ φ) n)) atTop (𝓝 0) := by
        refine squeeze_zero (fun _ => dist_nonneg) (fun n => (hzy (φ n)).le) ?_
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
        simpa only [Function.comp_def, one_div] using this
      exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
        (fun n => dist_triangle _ _ _) (by simpa using h1.add (tendsto_iff_dist_tendsto_zero.1
          hlim)))
  rw [heq]
  exact MeasurableSet.iInter fun n => t39j_hit_open isOpen_thickening

/-- hits of `closure Γ ∩ K ∩ U` (`K` compact, `U` open) are Effros-measurable -/
theorem t39j_hit_closure_compact_open {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) :
    MeasurableSet[effrosSigma] {Γ : Set ℂ | (closure Γ ∩ K ∩ U).Nonempty} := by
  have heq : {Γ : Set ℂ | (closure Γ ∩ K ∩ U).Nonempty} =
      ⋃ j : ℕ, ⋃ (_ : t39jBall j ⊆ U), {Γ | (closure Γ ∩ (K ∩ t39jBall j)).Nonempty} := by
    ext Γ
    simp only [mem_setOf_eq, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨x, ⟨hxc, hxK⟩, hxU⟩
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hxU
      obtain ⟨j, hxj, hj⟩ := t39j_ball_basis x hε
      exact ⟨j, hj.trans hεU, x, hxc, hxK, hxj⟩
    · rintro ⟨j, hj, x, hxc, hxK, hxj⟩
      exact ⟨x, ⟨hxc, hxK⟩, hj hxj⟩
  rw [heq]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
    t39j_hit_closure_compact (hK.inter_right (t39jBall_isCompact j).isClosed)

/-- the `j`-th ball meets `closure Γ` -/
def t39jValid (j : ℕ) (Γ : Set ℂ) : Prop := (closure Γ ∩ t39jBall j).Nonempty

theorem t39jValid_meas (j : ℕ) : MeasurableSet[effrosSigma] {Γ | t39jValid j Γ} :=
  t39j_hit_closure_compact (t39jBall_isCompact j)

/-- the random compact set selected from in step `j` -/
def t39jSelSet (j : ℕ) (Γ : Set ℂ) : Set ℂ :=
  open Classical in if t39jValid j Γ then closure Γ ∩ t39jBall j else {t39jBc j}

theorem t39j_selSet_exists (j : ℕ) :
    ∃ x : Set ℂ → ℂ, Measurable[effrosSigma] x ∧ ∀ Γ, x Γ ∈ t39jSelSet j Γ := by
  classical
  refine @GM.p412f_meas_select (Set ℂ) effrosSigma (t39jSelSet j) (fun Γ => ?_) (fun Γ => ?_)
    (fun U hU => ?_)
  · unfold t39jSelSet; split_ifs
    · exact (t39jBall_isCompact j).inter_left isClosed_closure
    · exact isCompact_singleton
  · unfold t39jSelSet; split_ifs with h
    · exact h
    · exact singleton_nonempty _
  · have heq : {Γ | (t39jSelSet j Γ ∩ U).Nonempty} =
        ({Γ | t39jValid j Γ} ∩ {Γ | (closure Γ ∩ t39jBall j ∩ U).Nonempty}) ∪
          ({Γ | t39jValid j Γ}ᶜ ∩ {_Γ | t39jBc j ∈ U}) := by
      ext Γ
      simp only [t39jSelSet, mem_setOf_eq, mem_union, mem_inter_iff, mem_compl_iff]
      split_ifs with h
      · simp [h]
      · simp [h, singleton_inter_nonempty]
    rw [heq]
    exact ((t39jValid_meas j).inter (t39j_hit_closure_compact_open (t39jBall_isCompact j) hU)).union
      ((t39jValid_meas j).compl.inter (MeasurableSet.const _))

/-- the `j`-th selected point: a point of `closure Γ ∩ t39jBall j` when this set is nonempty -/
def t39jPt (j : ℕ) : Set ℂ → ℂ := Classical.choose (t39j_selSet_exists j)

theorem t39jPt_meas (j : ℕ) : Measurable[effrosSigma] (t39jPt j) :=
  (Classical.choose_spec (t39j_selSet_exists j)).1

theorem t39jPt_mem {j : ℕ} {Γ : Set ℂ} (h : t39jValid j Γ) :
    t39jPt j Γ ∈ closure Γ ∩ t39jBall j := by
  have := (Classical.choose_spec (t39j_selSet_exists j)).2 Γ
  unfold t39jSelSet at this; rw [if_pos h] at this; exact this

/-- **density**: near every point of `closure Γ` there is a valid selected point, inside any
prescribed ball -/
theorem t39j_pt_dense {Γ : Set ℂ} {x : ℂ} (hx : x ∈ closure Γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ j, t39jValid j Γ ∧ t39jPt j Γ ∈ ball x ε ∧ t39jBall j ⊆ ball x ε := by
  obtain ⟨j, hxj, hj⟩ := t39j_ball_basis x hε
  have hv : t39jValid j Γ := ⟨x, hx, hxj⟩
  exact ⟨j, hv, hj (t39jPt_mem hv).2, hj⟩

end LQGMetric.CONF
