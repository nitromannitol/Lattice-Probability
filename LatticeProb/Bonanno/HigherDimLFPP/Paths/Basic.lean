/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Paths.Basic at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.Kappa
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsLFPPKernel
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsBandVersion
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsLFPPExponent
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
# Piecewise `C¹` paths in `ℝ^d` and their LFPP lengths

Packet P-X1, target T1 (the path layer; audit HA5, §4.3 row X1 and Details D1; ruling H8).

* `IsPcwC1Path γ x y`: a path `[0,1] → ℝ^d` from `x` to `y`, continuous on `[0,1]` and `C¹` on
  the closed pieces of a partition of `[0,1]`.  These are the clauses of the frozen
  `IsAdmissiblePath` without its endpoint and domain constraints (`isAdmissiblePath_iff`).
* The breakpoint form `PcwC1 γ F` (`C¹` on every closed subinterval avoiding a finite set `F`),
  used to build new paths.
* Analysis: differentiability off a finite set, integrability of `γ'` and of the LFPP integrand
  `lfppIntegrand ζ φ γ t = e^{ζ φ(γ t)} |γ'(t)|` for continuous `φ`, `lfppLength ≥ 0`, and
  chord ≤ arclength on every subinterval (`IsPcwC1Path.norm_sub_le_integral`).
* Path operations with their LFPP lengths: affine reparametrization, segments `segPath`,
  sub-paths `subPath` (`lfppLength_subPath`: the length is the integral over the sub-interval),
  reversal `revPath`, concatenation `concatPath` (`lfppLength_concatPath`: additivity).

2D sources: `LQGMetric/LFPP/PathPiece.lean`, `PathOps.lean`, `PathConcat.lean` (paths in `ℂ`,
`ℝ≥0∞`-valued lengths) and `HigherDimLFPP/Upper/TreeInequality.lean` (path analysis for the frozen
admissible paths).  Here lengths are the frozen real-valued `lfppLength`, so additivity needs the
integrability of the LFPP integrand, which holds for continuous fields.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLFPP

variable {d : ℕ}

/-! ## Piecewise `C¹` paths -/

/-- A piecewise `C¹` path `[0,1] → ℝ^d` from `x` to `y`: continuous on `[0,1]` and `C¹` on each
closed piece of a partition `0 = t₀ < ⋯ < t_k = 1` (the frozen `IsAdmissiblePath` without its
endpoint and domain clauses). -/
structure IsPcwC1Path (γ : ℝ → Rd d) (x y : Rd d) : Prop where
  source : γ 0 = x
  target : γ 1 = y
  continuousOn : ContinuousOn γ (Icc 0 1)
  piecewise_contDiff : ∃ (k : ℕ) (t : Fin (k + 1) → ℝ), StrictMono t ∧ t 0 = 0 ∧
    t (Fin.last k) = 1 ∧ ∀ i : Fin k, ContDiffOn ℝ 1 γ (Icc (t i.castSucc) (t i.succ))

/-- The frozen admissible paths are exactly the piecewise `C¹` paths from `0` to `e₁` that stay in
the cube `U = (-2,2)^d`. -/
theorem isAdmissiblePath_iff {γ : ℝ → Rd d} :
    IsAdmissiblePath d γ ↔ IsPcwC1Path γ 0 (e₁ d) ∧ MapsTo γ (Icc 0 1) (cube d) :=
  ⟨fun h => ⟨⟨h.source, h.target, h.continuousOn, h.piecewise_contDiff⟩, h.mapsTo⟩,
    fun h => ⟨h.1.source, h.1.target, h.2, h.1.continuousOn, h.1.piecewise_contDiff⟩⟩

/-- Breakpoint form of "piecewise `C¹` on `[0,1]`": `γ` is `C¹` on every closed subinterval of
`[0,1]` whose interior misses the finite set `F`. -/
def PcwC1 (γ : ℝ → Rd d) (F : Finset ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → (∀ x ∈ F, x ∉ Ioo a b) → ContDiffOn ℝ 1 γ (Icc a b)

theorem pcwC1_of_partition {γ : ℝ → Rd d} {k : ℕ} {t : Fin (k + 1) → ℝ} (ht0 : t 0 = 0)
    (htk : t (Fin.last k) = 1)
    (hC : ∀ i : Fin k, ContDiffOn ℝ 1 γ (Icc (t i.castSucc) (t i.succ))) :
    PcwC1 γ (Finset.univ.image t) := by
  classical
  intro a b ha hab hb hF
  set S := Finset.univ.filter fun j => t j ≤ a
  have hne : S.Nonempty := ⟨0, by simp [S, ht0, ha]⟩
  have hj : t (S.max' hne) ≤ a := (Finset.mem_filter.1 (S.max'_mem hne)).2
  have hjl : S.max' hne ≠ Fin.last k := by
    intro h; rw [h, htk] at hj; linarith
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hjl
  have hsucc : a < t i.succ := by
    by_contra hcon
    rw [not_lt] at hcon
    have : i.succ ≤ S.max' hne := S.le_max' _ (by simp [S, hcon])
    rw [← hi] at this
    exact absurd this (not_le.2 Fin.castSucc_lt_succ)
  have hb' : b ≤ t i.succ := by
    by_contra hcon
    rw [not_le] at hcon
    exact hF _ (Finset.mem_image_of_mem t (Finset.mem_univ _)) ⟨hsucc, hcon⟩
  exact (hC i).mono (Icc_subset_Icc (by rw [hi]; exact hj) hb')

theorem partition_of_pcwC1 {γ : ℝ → Rd d} {F : Finset ℝ} (hγ : PcwC1 γ F) :
    ∃ (k : ℕ) (t : Fin (k + 1) → ℝ), StrictMono t ∧ t 0 = 0 ∧
      t (Fin.last k) = 1 ∧ ∀ i : Fin k, ContDiffOn ℝ 1 γ (Icc (t i.castSucc) (t i.succ)) := by
  classical
  set G : Finset ℝ := insert 0 (insert 1 (F.filter fun x => x ∈ Ioo (0 : ℝ) 1))
  have h0 : (0 : ℝ) ∈ G := by simp [G]
  have h1 : (1 : ℝ) ∈ G := by simp [G]
  have hsub : ∀ x ∈ G, x ∈ Icc (0 : ℝ) 1 := by
    intro x hx
    simp only [G, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨_, h⟩
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact Ioo_subset_Icc_self h
  have hcard : 2 ≤ G.card := by
    have hs : ({0, 1} : Finset ℝ) ⊆ G := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have := Finset.card_le_card hs
    rwa [Finset.card_pair zero_ne_one] at this
  obtain ⟨k, hk⟩ : ∃ k, G.card = k + 1 := ⟨G.card - 1, by omega⟩
  set t := G.orderEmbOfFin hk
  have htm : ∀ i, t i ∈ G := fun i => G.orderEmbOfFin_mem hk i
  refine ⟨k, t, t.strictMono, ?_, ?_, ?_⟩
  · have := Finset.orderEmbOfFin_zero hk (Nat.succ_pos k)
    rw [show (0 : Fin (k + 1)) = ⟨0, Nat.succ_pos k⟩ from rfl, this]
    exact le_antisymm (G.min'_le 0 h0) (hsub _ (G.min'_mem _)).1
  · have := Finset.orderEmbOfFin_last hk (Nat.succ_pos k)
    rw [show (Fin.last k) = ⟨k + 1 - 1, Nat.sub_lt (Nat.succ_pos k) (Nat.succ_pos 0)⟩ from
      Fin.ext (by simp), this]
    exact le_antisymm (hsub _ (G.max'_mem _)).2 (G.le_max' 1 h1)
  · intro i
    have ha := hsub _ (htm i.castSucc)
    have hb := hsub _ (htm i.succ)
    refine hγ _ _ ha.1 (t.strictMono Fin.castSucc_lt_succ) hb.2 fun x hxF hx => ?_
    have hxG : x ∈ G := by
      simp only [G, Finset.mem_insert, Finset.mem_filter]
      exact Or.inr (Or.inr ⟨hxF, ha.1.trans_lt hx.1, hx.2.trans_le hb.2⟩)
    have hr : x ∈ Set.range t := by rw [Finset.range_orderEmbOfFin]; exact hxG
    obtain ⟨j, rfl⟩ := hr
    have hj1 : i.castSucc < j := t.lt_iff_lt.1 hx.1
    have hj2 : j < i.succ := t.lt_iff_lt.1 hx.2
    exact absurd hj2 (not_lt.2 (Fin.castSucc_lt_iff_succ_le.1 hj1))

section Basic

variable {γ : ℝ → Rd d} {x y : Rd d}

theorem IsPcwC1Path.exists_pcwC1 (hγ : IsPcwC1Path γ x y) : ∃ F, PcwC1 γ F := by
  classical
  obtain ⟨k, t, _, ht0, htk, hC⟩ := hγ.piecewise_contDiff
  exact ⟨_, pcwC1_of_partition ht0 htk hC⟩

theorem IsPcwC1Path.of_pcwC1 {F : Finset ℝ} (h0 : γ 0 = x) (h1 : γ 1 = y)
    (hc : ContinuousOn γ (Icc 0 1)) (hγ : PcwC1 γ F) : IsPcwC1Path γ x y :=
  ⟨h0, h1, hc, partition_of_pcwC1 hγ⟩

theorem IsPcwC1Path.mem_of_mapsTo {V : Set (Rd d)} (hγ : IsPcwC1Path γ x y)
    (hV : MapsTo γ (Icc 0 1) V) : x ∈ V ∧ y ∈ V := by
  refine ⟨?_, ?_⟩
  · rw [← hγ.source]; exact hV ⟨le_rfl, zero_le_one⟩
  · rw [← hγ.target]; exact hV ⟨zero_le_one, le_rfl⟩

end Basic

/-! ## Analysis of piecewise `C¹` paths -/

section Analysis

variable {γ : ℝ → Rd d} {x y : Rd d}

theorem exists_mem_piece {k : ℕ} {t : Fin (k + 1) → ℝ} (ht0 : t 0 = 0)
    (htk : t (Fin.last k) = 1) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hst : s ∉ range t) :
    ∃ i : Fin k, t i.castSucc < s ∧ s < t i.succ := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (k + 1)), S = Finset.univ.filter fun j => t j < s :=
    ⟨_, rfl⟩
  have hmem : ∀ j, j ∈ S ↔ t j < s := fun j => by simp [hS]
  have hne : S.Nonempty := ⟨0, (hmem 0).2 (by rw [ht0]; exact hs.1)⟩
  have hm : t (S.max' hne) < s := (hmem _).1 (S.max'_mem hne)
  have hml : S.max' hne ≠ Fin.last k := by
    intro h
    rw [h, htk] at hm
    linarith [hs.2]
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hml
  refine ⟨i, by rw [hi]; exact hm, ?_⟩
  rcases lt_or_ge s (t i.succ) with h | h
  · exact h
  · exfalso
    rcases h.lt_or_eq with h | h
    · have : i.succ ≤ S.max' hne := S.le_max' _ ((hmem _).2 h)
      rw [← hi] at this
      exact absurd this (not_le.2 Fin.castSucc_lt_succ)
    · exact hst ⟨_, h⟩

theorem norm_deriv_le_of_contDiffOn {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 1 γ (Icc a b)) :
    ∃ C, 0 ≤ C ∧ ∀ s ∈ Ioo a b, ‖deriv γ s‖ ≤ C := by
  obtain ⟨C, hC'⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (hC.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl)
  refine ⟨max C 0, le_max_right _ _, fun s hs => ?_⟩
  rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)]
  exact (hC' s (Ioo_subset_Icc_self hs)).trans (le_max_left _ _)

/-- Off a finite set of times, a piecewise `C¹` path is differentiable on `(0,1)`, and its
derivative there is bounded. -/
theorem IsPcwC1Path.exists_finset_hasDerivAt (hγ : IsPcwC1Path γ x y) :
    ∃ (F : Finset ℝ) (C : ℝ), 0 ≤ C ∧ ∀ s ∈ Ioo (0 : ℝ) 1, s ∉ F →
      HasDerivAt γ (deriv γ s) s ∧ ‖deriv γ s‖ ≤ C := by
  classical
  obtain ⟨k, t, ht, ht0, htk, hC⟩ := hγ.piecewise_contDiff
  have hB : ∀ i : Fin k, ∃ C, 0 ≤ C ∧
      ∀ s ∈ Ioo (t i.castSucc) (t i.succ), ‖deriv γ s‖ ≤ C :=
    fun i => norm_deriv_le_of_contDiffOn (ht Fin.castSucc_lt_succ) (hC i)
  choose C hC0 hCb using hB
  refine ⟨Finset.univ.image t, ∑ i, C i, Finset.sum_nonneg fun i _ => hC0 i, fun s hs hsF => ?_⟩
  have hst : s ∉ range t := by
    rintro ⟨j, rfl⟩
    exact hsF (Finset.mem_image_of_mem t (Finset.mem_univ j))
  obtain ⟨i, h1, h2⟩ := exists_mem_piece ht0 htk hs hst
  refine ⟨((hC i).contDiffAt (Icc_mem_nhds h1 h2)).differentiableAt_one.hasDerivAt, ?_⟩
  exact (hCb i s ⟨h1, h2⟩).trans (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i))

/-- `γ'` is integrable on `[0,1]` for a piecewise `C¹` path. -/
theorem IsPcwC1Path.intervalIntegrable_deriv (hγ : IsPcwC1Path γ x y) :
    IntervalIntegrable (deriv γ) volume 0 1 := by
  obtain ⟨F, C, _, hFC⟩ := hγ.exists_finset_hasDerivAt
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne
    (measurable_deriv γ).aestronglyMeasurable ?_
  have hfin : (insert (1 : ℝ) (F : Set ℝ)).Countable := (F.finite_toSet.insert 1).countable
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hfin.ae_notMem volume] with s hs hsI
  rw [mem_insert_iff, not_or] at hs
  exact (hFC s ⟨hsI.1, lt_of_le_of_ne hsI.2 hs.1⟩ hs.2).2

/-- The LFPP integrand `e^{ζ φ(γ t)} |γ'(t)|`, so that `lfppLength ζ φ γ = ∫₀¹ lfppIntegrand`. -/
def lfppIntegrand (ζ : ℝ) (φ : Rd d → ℝ) (γ : ℝ → Rd d) (t : ℝ) : ℝ :=
  Real.exp (ζ * φ (γ t)) * ‖deriv γ t‖

theorem lfppLength_eq_integral (ζ : ℝ) (φ : Rd d → ℝ) (γ : ℝ → Rd d) :
    lfppLength ζ φ γ = ∫ t in (0 : ℝ)..1, lfppIntegrand ζ φ γ t := rfl

theorem lfppIntegrand_nonneg (ζ : ℝ) (φ : Rd d → ℝ) (γ : ℝ → Rd d) (t : ℝ) :
    0 ≤ lfppIntegrand ζ φ γ t :=
  mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

/-- The LFPP length is nonnegative (for every path and every field). -/
theorem lfppLength_nonneg (ζ : ℝ) (φ : Rd d → ℝ) (γ : ℝ → Rd d) : 0 ≤ lfppLength ζ φ γ :=
  intervalIntegral.integral_nonneg zero_le_one fun t _ => lfppIntegrand_nonneg ζ φ γ t

theorem integral_lfppIntegrand_nonneg (ζ : ℝ) (φ : Rd d → ℝ) (γ : ℝ → Rd d) {a b : ℝ}
    (hab : a ≤ b) : 0 ≤ ∫ t in a..b, lfppIntegrand ζ φ γ t :=
  intervalIntegral.integral_nonneg hab fun t _ => lfppIntegrand_nonneg ζ φ γ t

/-- For a continuous field the LFPP integrand of a piecewise `C¹` path is integrable on `[0,1]`. -/
theorem IsPcwC1Path.intervalIntegrable_lfppIntegrand (hγ : IsPcwC1Path γ x y)
    {φ : Rd d → ℝ} (hφ : Continuous φ) (ζ : ℝ) :
    IntervalIntegrable (lfppIntegrand ζ φ γ) volume 0 1 := by
  have hc : ContinuousOn (fun t => Real.exp (ζ * φ (γ t))) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact Real.continuous_exp.comp_continuousOn
      ((continuous_const.mul hφ).comp_continuousOn hγ.continuousOn)
  exact hγ.intervalIntegrable_deriv.norm.continuousOn_mul hc

theorem intervalIntegrable_of_sub {F : Type*} [NormedAddCommGroup F] {f : ℝ → F}
    (hf : IntervalIntegrable f volume 0 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable f volume a b :=
  hf.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc ha hb)

/-- **Chord ≤ arclength** on every subinterval of `[0,1]`. -/
theorem IsPcwC1Path.norm_sub_le_integral (hγ : IsPcwC1Path γ x y) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) : ‖γ b - γ a‖ ≤ ∫ t in a..b, ‖deriv γ t‖ := by
  obtain ⟨F, C, _, hFC⟩ := hγ.exists_finset_hasDerivAt
  have hI := intervalIntegrable_of_sub hγ.intervalIntegrable_deriv ha hab hb
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le γ (deriv γ) hab
    F.countable_toSet (hγ.continuousOn.mono (Icc_subset_Icc ha hb))
    (fun s hs => (hFC s ⟨lt_of_le_of_lt ha hs.1.1, lt_of_lt_of_le hs.1.2 hb⟩ hs.2).1) hI
  rw [← hFTC]
  exact intervalIntegral.norm_integral_le_integral_norm hab

end Analysis

/-! ## Affine reparametrizations -/

section Affine

theorem contDiffOn_comp_affine {γ : ℝ → Rd d} {a' b' c s : ℝ} {S : Set ℝ}
    (hγ : ContDiffOn ℝ 1 γ (Icc a' b')) (hS : MapsTo (fun u => c * u + s) S (Icc a' b')) :
    ContDiffOn ℝ 1 (fun u => γ (c * u + s)) S :=
  hγ.comp ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffOn hS

theorem deriv_comp_affine (γ : ℝ → Rd d) (c s u : ℝ) :
    deriv (fun u => γ (c * u + s)) u = c • deriv γ (c * u + s) := by
  have := deriv_comp_mul_left (f := fun v => γ (v + s)) (c := c) (x := u)
  simp only [deriv_comp_add_const] at this
  exact this

end Affine

/-! ## Segments -/

section Segment

variable {x y : Rd d}

/-- The straight segment `u ↦ x + u (y - x)`. -/
def segPath (x y : Rd d) (u : ℝ) : Rd d := x + u • (y - x)

@[simp] theorem segPath_zero (x y : Rd d) : segPath x y 0 = x := by simp [segPath]

@[simp] theorem segPath_one (x y : Rd d) : segPath x y 1 = y := by simp [segPath]

theorem hasDerivAt_segPath (x y : Rd d) (u : ℝ) : HasDerivAt (segPath x y) (y - x) u := by
  exact (((hasDerivAt_id u).smul_const (y - x)).const_add x).congr_deriv (one_smul _ _)

theorem deriv_segPath (x y : Rd d) (u : ℝ) : deriv (segPath x y) u = y - x :=
  (hasDerivAt_segPath x y u).deriv

theorem contDiff_segPath (x y : Rd d) : ContDiff ℝ 1 (segPath x y) := by
  unfold segPath; fun_prop

theorem continuous_segPath (x y : Rd d) : Continuous (segPath x y) :=
  (contDiff_segPath x y).continuous

theorem isPcwC1Path_segPath (x y : Rd d) : IsPcwC1Path (segPath x y) x y :=
  IsPcwC1Path.of_pcwC1 (F := ∅) (segPath_zero x y) (segPath_one x y)
    (continuous_segPath x y).continuousOn fun _ _ _ _ _ _ => (contDiff_segPath x y).contDiffOn

theorem segPath_mem_of_convex {V : Set (Rd d)} (hV : Convex ℝ V) (hx : x ∈ V) (hy : y ∈ V)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : segPath x y u ∈ V :=
  hV.add_smul_sub_mem hx hy hu

theorem mapsTo_segPath {V : Set (Rd d)} (hV : Convex ℝ V) (hx : x ∈ V) (hy : y ∈ V) :
    MapsTo (segPath x y) (Icc 0 1) V := fun _ hu => segPath_mem_of_convex hV hx hy hu

theorem norm_segPath_sub (x y : Rd d) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ‖segPath x y u - x‖ ≤ ‖y - x‖ := by
  rw [segPath, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hu.2

theorem lfppLength_segPath (ζ : ℝ) (φ : Rd d → ℝ) (x y : Rd d) :
    lfppLength ζ φ (segPath x y) =
      (∫ u in (0 : ℝ)..1, Real.exp (ζ * φ (segPath x y u))) * ‖y - x‖ := by
  rw [lfppLength_eq_integral, ← intervalIntegral.integral_mul_const]
  simp only [lfppIntegrand, deriv_segPath]

theorem lfppLength_segPath_self (ζ : ℝ) (φ : Rd d → ℝ) (x : Rd d) :
    lfppLength ζ φ (segPath x x) = 0 := by
  rw [lfppLength_segPath, sub_self, norm_zero, mul_zero]

/-- **Segment bound**: `lfppLength (segment) ≤ B |y - x|` if `e^{ζ φ} ≤ B` along the segment. -/
theorem lfppLength_segPath_le {ζ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ) (x y : Rd d) {B : ℝ}
    (hB : ∀ u ∈ Icc (0 : ℝ) 1, Real.exp (ζ * φ (segPath x y u)) ≤ B) :
    lfppLength ζ φ (segPath x y) ≤ B * ‖y - x‖ := by
  rw [lfppLength_segPath]
  have hc : Continuous fun u => Real.exp (ζ * φ (segPath x y u)) :=
    Real.continuous_exp.comp (continuous_const.mul (hφ.comp (continuous_segPath x y)))
  have hle : ∫ u in (0 : ℝ)..1, Real.exp (ζ * φ (segPath x y u)) ≤ ∫ _ in (0 : ℝ)..1, B :=
    intervalIntegral.integral_mono_on zero_le_one (hc.intervalIntegrable 0 1)
      intervalIntegrable_const hB
  rw [intervalIntegral.integral_const, sub_zero, one_smul] at hle
  exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

end Segment

/-! ## Sub-paths -/

section SubPath

variable {γ : ℝ → Rd d} {x y : Rd d}

/-- The restriction of `γ` to `[s, t]`, reparametrized by `[0,1]`. -/
def subPath (γ : ℝ → Rd d) (s t : ℝ) (u : ℝ) : Rd d := γ ((t - s) * u + s)

@[simp] theorem subPath_zero (γ : ℝ → Rd d) (s t : ℝ) : subPath γ s t 0 = γ s := by
  simp [subPath]

@[simp] theorem subPath_one (γ : ℝ → Rd d) (s t : ℝ) : subPath γ s t 1 = γ t := by
  simp [subPath]

end SubPath

/-! ## Reversal -/

section Reverse

variable {γ : ℝ → Rd d} {x y : Rd d}
/-- The time reversal `u ↦ γ (1 - u)`. -/
def revPath (γ : ℝ → Rd d) (u : ℝ) : Rd d := γ (1 - u)

theorem revPath_eq_affine (γ : ℝ → Rd d) : revPath γ = fun u => γ ((-1) * u + 1) := by
  funext u; simp only [revPath]; congr 1; ring

theorem IsPcwC1Path.revPath (hγ : IsPcwC1Path γ x y) :
    IsPcwC1Path (HigherDimLFPP.revPath γ) y x := by
  classical
  obtain ⟨F, hF⟩ := hγ.exists_pcwC1
  rw [revPath_eq_affine]
  have hmaps : ∀ a b : ℝ, MapsTo (fun u : ℝ => (-1) * u + 1) (Icc a b) (Icc (1 - b) (1 - a)) :=
    fun a b u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩
  refine IsPcwC1Path.of_pcwC1 (F := F.image fun x => 1 - x)
    (by simp [hγ.target]) (by simp [hγ.source]) ?_ ?_
  · refine hγ.continuousOn.comp (by fun_prop) fun u hu => ?_
    have := hmaps 0 1 hu
    simpa using this
  · intro a b ha hab hb hFa
    exact contDiffOn_comp_affine (hF _ _ (by linarith) (by linarith) (by linarith)
      fun x hx hxI => hFa _ (Finset.mem_image_of_mem _ hx)
        ⟨by linarith [hxI.2], by linarith [hxI.1]⟩) (hmaps a b)

theorem mapsTo_revPath {V : Set (Rd d)} (hV : MapsTo γ (Icc 0 1) V) :
    MapsTo (revPath γ) (Icc 0 1) V := fun u hu =>
  hV ⟨by linarith [hu.2], by linarith [hu.1]⟩


end Reverse

/-! ## Concatenation -/

section Concat

variable {γ₁ γ₂ : ℝ → Rd d} {x y z : Rd d}

/-- Concatenation: `γ₁ (2u)` on `[0, 1/2]`, `γ₂ (2u - 1)` on `[1/2, 1]`. -/
def concatPath (γ₁ γ₂ : ℝ → Rd d) (u : ℝ) : Rd d :=
  if u ≤ 1 / 2 then γ₁ (2 * u) else γ₂ (2 * u - 1)

theorem concatPath_eqOn_left (γ₁ γ₂ : ℝ → Rd d) :
    EqOn (concatPath γ₁ γ₂) (fun u => γ₁ (2 * u)) (Iic (1 / 2)) := fun _ hu => by
  simp only [concatPath, mem_Iic.1 hu, ite_true]

theorem concatPath_eqOn_right (h : γ₁ 1 = γ₂ 0) :
    EqOn (concatPath γ₁ γ₂) (fun u => γ₂ (2 * u - 1)) (Ici (1 / 2)) := by
  intro u hu
  simp only [concatPath]
  split_ifs with h1
  · have : u = 1 / 2 := le_antisymm h1 hu
    subst this
    norm_num [h]
  · rfl

theorem IsPcwC1Path.concat (h₁ : IsPcwC1Path γ₁ x y) (h₂ : IsPcwC1Path γ₂ y z) :
    IsPcwC1Path (concatPath γ₁ γ₂) x z := by
  classical
  have h12 : γ₁ 1 = γ₂ 0 := h₁.target.trans h₂.source.symm
  obtain ⟨F, hF⟩ := h₁.exists_pcwC1
  obtain ⟨G, hG⟩ := h₂.exists_pcwC1
  have hL := concatPath_eqOn_left γ₁ γ₂
  have hR := concatPath_eqOn_right h12
  have hm1 : ∀ a b : ℝ, MapsTo (fun u : ℝ => 2 * u + 0) (Icc a b) (Icc (2 * a) (2 * b)) :=
    fun a b u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hm2 : ∀ a b : ℝ, MapsTo (fun u : ℝ => 2 * u + -1) (Icc a b)
      (Icc (2 * a - 1) (2 * b - 1)) :=
    fun a b u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  refine IsPcwC1Path.of_pcwC1
    (F := insert (1 / 2) (F.image (fun x => x / 2) ∪ G.image (fun x => (x + 1) / 2)))
    (by rw [hL (by norm_num : (0 : ℝ) ∈ Iic (1 / 2))]; simpa using h₁.source)
    (by rw [hR (by norm_num : (1 : ℝ) ∈ Ici (1 / 2))]; norm_num [h₂.target]) ?_ ?_
  · have c1 : ContinuousOn (concatPath γ₁ γ₂) (Icc 0 (1 / 2)) := by
      refine (h₁.continuousOn.comp (by fun_prop) fun u hu => ?_).congr fun u hu => hL hu.2
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have c2 : ContinuousOn (concatPath γ₁ γ₂) (Icc (1 / 2) 1) := by
      refine (h₂.continuousOn.comp (by fun_prop) fun u hu => ?_).congr fun u hu => hR hu.1
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have := c1.union_of_isClosed c2 isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at this
  · intro a b ha hab hb hFa
    by_cases hb2 : b ≤ 1 / 2
    · have hC := contDiffOn_comp_affine (c := 2) (s := 0) (hF (2 * a) (2 * b) (by linarith)
        (by linarith) (by linarith) fun x hx hxI => hFa (x / 2) (Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)))
          ⟨by linarith [hxI.1], by linarith [hxI.2]⟩) (by simpa using hm1 a b)
      refine hC.congr fun u hu => ?_
      rw [hL (hu.2.trans hb2)]
      simp
    · have ha2 : 1 / 2 ≤ a := by
        by_contra h
        exact hFa _ (Finset.mem_insert_self _ _) ⟨by linarith, by linarith⟩
      have hC := contDiffOn_comp_affine (c := 2) (s := -1) (hG (2 * a - 1) (2 * b - 1)
        (by linarith) (by linarith) (by linarith) fun x hx hxI => hFa ((x + 1) / 2)
          (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)))
          ⟨by linarith [hxI.1], by linarith [hxI.2]⟩) (hm2 a b)
      refine hC.congr fun u hu => ?_
      rw [hR (ha2.trans hu.1)]
      simp only [sub_eq_add_neg]

theorem mapsTo_concatPath {V : Set (Rd d)} (h₁ : MapsTo γ₁ (Icc 0 1) V)
    (h₂ : MapsTo γ₂ (Icc 0 1) V) : MapsTo (concatPath γ₁ γ₂) (Icc 0 1) V := by
  intro u hu
  simp only [concatPath]
  split_ifs with h
  · exact h₁ ⟨by linarith [hu.1], by linarith⟩
  · exact h₂ ⟨by linarith, by linarith [hu.2]⟩

/-- **Additivity of the LFPP length under concatenation** (continuous field). -/
theorem lfppLength_concatPath {ζ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ)
    (h₁ : IsPcwC1Path γ₁ x y) (h₂ : IsPcwC1Path γ₂ y z) :
    lfppLength ζ φ (concatPath γ₁ γ₂) = lfppLength ζ φ γ₁ + lfppLength ζ φ γ₂ := by
  have h12 : γ₁ 1 = γ₂ 0 := h₁.target.trans h₂.source.symm
  have hI := (h₁.concat h₂).intervalIntegrable_lfppIntegrand hφ ζ
  have hnull : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ ({1 / 2} : Set ℝ) :=
    (countable_singleton _).ae_notMem volume
  have hleft : ∫ u in (0 : ℝ)..1 / 2, lfppIntegrand ζ φ (concatPath γ₁ γ₂) u =
      lfppLength ζ φ γ₁ := by
    have heq : ∫ u in (0 : ℝ)..1 / 2, lfppIntegrand ζ φ (concatPath γ₁ γ₂) u =
        ∫ u in (0 : ℝ)..1 / 2, 2 * lfppIntegrand ζ φ γ₁ (2 * u) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hnull] with u hu hmem
      rw [uIoc_of_le (by norm_num)] at hmem
      have hlt : u < 1 / 2 := lt_of_le_of_ne hmem.2 hu
      have hev : concatPath γ₁ γ₂ =ᶠ[𝓝 u] fun v => γ₁ (2 * v) :=
        Filter.eventuallyEq_of_mem (Iio_mem_nhds hlt)
          fun v hv => concatPath_eqOn_left γ₁ γ₂ (mem_Iic.2 (le_of_lt hv))
      unfold lfppIntegrand
      rw [hev.deriv_eq, hev.eq_of_nhds, deriv_comp_mul_left, norm_smul, Real.norm_two]
      ring
    rw [heq, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun u => lfppIntegrand ζ φ γ₁ u) two_ne_zero,
      lfppLength_eq_integral, smul_eq_mul, ← mul_assoc]
    norm_num
  have hright : ∫ u in (1 / 2 : ℝ)..1, lfppIntegrand ζ φ (concatPath γ₁ γ₂) u =
      lfppLength ζ φ γ₂ := by
    have heq : ∫ u in (1 / 2 : ℝ)..1, lfppIntegrand ζ φ (concatPath γ₁ γ₂) u =
        ∫ u in (1 / 2 : ℝ)..1, 2 * lfppIntegrand ζ φ γ₂ (2 * u - 1) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hnull] with u hu hmem
      rw [uIoc_of_le (by norm_num)] at hmem
      have hlt : 1 / 2 < u := hmem.1
      have hev : concatPath γ₁ γ₂ =ᶠ[𝓝 u] fun v => γ₂ (2 * v - 1) :=
        Filter.eventuallyEq_of_mem (Ioi_mem_nhds hlt)
          fun v hv => concatPath_eqOn_right h12 (mem_Ici.2 (le_of_lt hv))
      unfold lfppIntegrand
      have hd : deriv (fun v => γ₂ (2 * v - 1)) u = (2 : ℝ) • deriv γ₂ (2 * u - 1) := by
        have := deriv_comp_affine γ₂ 2 (-1) u
        simp only [← sub_eq_add_neg] at this
        exact this
      rw [hev.deriv_eq, hev.eq_of_nhds, hd, norm_smul, Real.norm_two]
      ring
    rw [heq, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_sub (fun u => lfppIntegrand ζ φ γ₂ u) two_ne_zero,
      lfppLength_eq_integral, smul_eq_mul, ← mul_assoc]
    norm_num
  rw [lfppLength_eq_integral, ← intervalIntegral.integral_add_adjacent_intervals
    (b := 1 / 2) (intervalIntegrable_of_sub hI le_rfl (by norm_num) (by norm_num))
    (intervalIntegrable_of_sub hI (by norm_num) (by norm_num) le_rfl), hleft, hright]

end Concat

end HigherDimLFPP
