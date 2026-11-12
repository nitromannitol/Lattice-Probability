/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36UpperPath at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperWalk
import LatticeProb.Bonanno.LQGDimension.LFPP.TreeInequalityAux
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# From a continuum LFPP path to a graph path (upper half of DFGPS Lemma 3.6)

DFGPS (T:1645–1650) pass from continuum LFPP to the discretized LFPP `D̃^δ` "by the same argument
as in the proof of [DG, Proposition 3.16]". For the upper bound we need the direction
"continuum path ⇒ graph path". We use an own elementary argument (decision D52, DEVIATIONS
DV-DFC2-2): cut the path into pieces of Euclidean length in `[δ, 2δ]` (arclength), round the
cut points to `δℤ²`, join consecutive rounded points by straight 8-neighbour walks of `≤ 3` steps
(`L36UpperWalk`), and compare each vertex weight with the LFPP integral over its piece using the
oscillation `osc φ (8δ)` (LQGDimension `Draft.osc`, the quantity of `Osc37.osc_tendsto`).
Result: `Σ e^{ξ φ} ≤ 4 δ⁻¹ e^{ξ osc φ (8δ)} ∫_P e^{ξ φ} |dz|`.

The integrability / chord-≤-arclength facts copy LQGDimension's `TreeIneqJ42` proofs (stated
there for `IsAdmissiblePath`) to `DG.IsDGPath`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace LQGMetric.DFGPS.L36

open LQGDimension.Blueprint.Draft (osc)

variable {S : Set ℂ} {z w : ℂ} {p : ℝ → ℂ}

/-- `p'` is integrable on `[0,1]` for a DG path (copy of `TreeIneqJ42.deriv_intervalIntegrable`) -/
theorem dgPath_deriv_intervalIntegrable (hp : DG.IsDGPath S z w p) :
    IntervalIntegrable (deriv p) volume 0 1 := by
  obtain ⟨k, t, ht, ht0, htk, hC⟩ := hp.piecewise_contDiff
  have hB : ∀ i : Fin k, ∃ C, 0 ≤ C ∧
      ∀ x ∈ Ioo (t i.castSucc) (t i.succ), ‖deriv p x‖ ≤ C :=
    fun i => LQGDimension.TreeIneqJ42.deriv_bound_piece (ht Fin.castSucc_lt_succ) (hC i)
  choose C hC0 hCb using hB
  have hbound : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ range t → ‖deriv p x‖ ≤ ∑ i, C i := by
    intro x hx hxt
    obtain ⟨i, h1, h2⟩ := LQGDimension.TreeIneqJ42.exists_piece ht0 htk hx hxt
    exact (hCb i x ⟨h1, h2⟩).trans
      (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := ∑ i, C i) measure_Ioc_lt_top.ne
    (measurable_deriv p).aestronglyMeasurable ?_
  have hfin : (insert (1 : ℝ) (range t)).Countable := ((finite_range t).insert 1).countable
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hfin.ae_notMem volume] with x hx hxI
  rw [mem_insert_iff, not_or] at hx
  exact hbound x ⟨hxI.1, lt_of_le_of_ne hxI.2 hx.1⟩ hx.2

lemma intervalIntegrable_sub01 {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : IntervalIntegrable f volume 0 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable f volume a b :=
  hf.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc ha hb)

/-- chord ≤ arclength (copy of `TreeIneqJ42.chord_le_arclength`) -/
theorem dgPath_chord_le (hp : DG.IsDGPath S z w p) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) : ‖p b - p a‖ ≤ ∫ t in a..b, ‖deriv p t‖ := by
  obtain ⟨k, t, _, ht0, htk, hC⟩ := hp.piecewise_contDiff
  have hI := intervalIntegrable_sub01 (dgPath_deriv_intervalIntegrable hp) ha hab hb
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le p (deriv p) hab
    (countable_range t) (hp.continuousOn.mono (Icc_subset_Icc ha hb))
    (fun x hx => LQGDimension.TreeIneqJ42.hasDerivAt_of_piece ht0 htk hC
      ⟨lt_of_le_of_lt ha hx.1.1, lt_of_lt_of_le hx.1.2 hb⟩ hx.2) hI
  rw [← hFTC]
  exact intervalIntegral.norm_integral_le_integral_norm hab

/-- rounding to the grid `δℤ²` -/
def rnd (δ : ℝ) (x : ℂ) : ℤ × ℤ := (round (x.re / δ), round (x.im / δ))

lemma abs_round_mul_sub {δ : ℝ} (hδ : 0 < δ) (a : ℝ) : |(round (a / δ) : ℝ) * δ - a| ≤ δ / 2 := by
  have h := abs_sub_round (a / δ)
  have e : (round (a / δ) : ℝ) * δ - a = -((a / δ - round (a / δ)) * δ) := by
    field_simp; ring
  rw [e, abs_neg, abs_mul, abs_of_pos hδ]
  nlinarith

lemma abs_round_sub_round_le {δ : ℝ} (hδ : 0 < δ) {a b : ℝ} (h : |a - b| ≤ 2 * δ) :
    |round (a / δ) - round (b / δ)| ≤ 3 := by
  have ha := abs_round_mul_sub hδ a
  have hb := abs_round_mul_sub hδ b
  have hr : |((round (a / δ) - round (b / δ) : ℤ) : ℝ)| * δ < 4 * δ := by
    have e : |((round (a / δ) - round (b / δ) : ℤ) : ℝ)| * δ =
        |((round (a / δ) : ℝ) * δ - a) - ((round (b / δ) : ℝ) * δ - b) + (a - b)| := by
      rw [← abs_of_pos hδ, ← abs_mul, abs_of_pos hδ]; push_cast; ring_nf
    rw [e]
    calc _ ≤ |((round (a / δ) : ℝ) * δ - a) - ((round (b / δ) : ℝ) * δ - b)| + |a - b| :=
          abs_add_le _ _
      _ ≤ |(round (a / δ) : ℝ) * δ - a| + |(round (b / δ) : ℝ) * δ - b| + |a - b| := by
          gcongr; exact abs_sub _ _
      _ < 4 * δ := by linarith
  have : |((round (a / δ) - round (b / δ) : ℤ) : ℝ)| < 4 := lt_of_mul_lt_mul_right hr hδ.le
  have : |round (a / δ) - round (b / δ)| < 4 := by exact_mod_cast this
  omega

lemma norm_le_three_of_mem_rS {x : ℂ} (hx : x ∈ rS 1) : ‖x‖ ≤ 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_rS_one.1 hx
  have := Complex.norm_le_abs_re_add_abs_im x
  rw [abs_of_pos h1, abs_of_pos h3] at this
  linarith

/-- a grid point within sup-distance `3δ` (coordinatewise, in grid units) of `rnd δ y` is within
`5δ` of `y` -/
lemma norm_gpt_sub_le {δ : ℝ} (hδ : 0 < δ) (y : ℂ) (c : ℤ × ℤ) (h1 : |c.1 - (rnd δ y).1| ≤ 3)
    (h2 : |c.2 - (rnd δ y).2| ≤ 3) : ‖gpt δ c - y‖ ≤ 5 * δ := by
  have hr1 := abs_round_mul_sub hδ y.re
  have hr2 := abs_round_mul_sub hδ y.im
  have e1 : |(gpt δ c - y).re| ≤ 7 / 2 * δ := by
    have : (gpt δ c - y).re = ((c.1 - (rnd δ y).1 : ℤ) : ℝ) * δ +
        ((round (y.re / δ) : ℝ) * δ - y.re) := by simp [gpt, rnd]; ring
    rw [this]
    have h1' : |((c.1 - (rnd δ y).1 : ℤ) : ℝ)| ≤ 3 := by exact_mod_cast h1
    calc _ ≤ |((c.1 - (rnd δ y).1 : ℤ) : ℝ) * δ| + |(round (y.re / δ) : ℝ) * δ - y.re| :=
          abs_add_le _ _
      _ ≤ 3 * δ + δ / 2 := by
          rw [abs_mul, abs_of_pos hδ]; gcongr
      _ = 7 / 2 * δ := by ring
  have e2 : |(gpt δ c - y).im| ≤ 7 / 2 * δ := by
    have : (gpt δ c - y).im = ((c.2 - (rnd δ y).2 : ℤ) : ℝ) * δ +
        ((round (y.im / δ) : ℝ) * δ - y.im) := by simp [gpt, rnd]; ring
    rw [this]
    have h2' : |((c.2 - (rnd δ y).2 : ℤ) : ℝ)| ≤ 3 := by exact_mod_cast h2
    calc _ ≤ |((c.2 - (rnd δ y).2 : ℤ) : ℝ) * δ| + |(round (y.im / δ) : ℝ) * δ - y.im| :=
          abs_add_le _ _
      _ ≤ 3 * δ + δ / 2 := by
          rw [abs_mul, abs_of_pos hδ]; gcongr
      _ = 7 / 2 * δ := by ring
  have hs : Real.sqrt 2 < 10 / 7 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  calc ‖gpt δ c - y‖ ≤ Real.sqrt 2 * max |(gpt δ c - y).re| |(gpt δ c - y).im| :=
        Complex.norm_le_sqrt_two_mul_max _
    _ ≤ Real.sqrt 2 * (7 / 2 * δ) := by gcongr; exact max_le e1 e2
    _ ≤ 10 / 7 * (7 / 2 * δ) := by gcongr
    _ = 5 * δ := by ring

/-- **Continuum path ⇒ graph path.** If a DG path `p` from `z` to `w` (`|w − z| ≥ δ`) has its
`8δ`-neighbourhood in `𝕊`, there is a graph path of `𝕊 ∩ δℤ²` from `δ·rnd(z)` to `δ·rnd(w)` with
`Σ e^{ξ φ} ≤ 4 δ⁻¹ e^{ξ osc φ (8δ)} ∫_p e^{ξ φ} |dz|`. -/
theorem exists_graphPath_of_dgPath {δ ξ : ℝ} (hδ : 0 < δ) (hξ : 0 ≤ ξ) {φ : ℂ → ℝ}
    (hφ : Continuous φ) (hp : DG.IsDGPath S z w p) (hzw : δ ≤ ‖w - z‖)
    (hS : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y : ℂ, ‖y - p t‖ ≤ 8 * δ → y ∈ rS 1) :
    ∃ L : List ℂ, IsGraphPath δ (rS 1) L ∧ L.head? = some (gpt δ (rnd δ z)) ∧
      L.getLast? = some (gpt δ (rnd δ w)) ∧
      (L.map fun x => Real.exp (ξ * φ x)).sum ≤
        4 * δ⁻¹ * Real.exp (ξ * osc φ (8 * δ)) * LQGDimension.lfppLength ξ φ p := by
  have hD := dgPath_deriv_intervalIntegrable hp
  have hN : IntervalIntegrable (fun u => ‖deriv p u‖) volume 0 1 := hD.norm
  set s : ℝ → ℝ := fun t => ∫ u in (0:ℝ)..t, ‖deriv p u‖ with hsdef
  have hs0 : s 0 = 0 := by simp [hsdef]
  have hscont : ContinuousOn s (Icc 0 1) := by
    have := intervalIntegral.continuousOn_primitive_interval' hN (left_mem_uIcc)
    rwa [uIcc_of_le zero_le_one] at this
  have hsdiff : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → s b - s a = ∫ u in a..b, ‖deriv p u‖ :=
    fun a b ha hab hb => intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_sub01 hN le_rfl (ha.trans hab) hb)
      (intervalIntegrable_sub01 hN le_rfl ha (hab.trans hb))
  have hsmono : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → s a ≤ s b := fun a b ha hab hb => by
    have := hsdiff a b ha hab hb
    have h2 : 0 ≤ ∫ u in a..b, ‖deriv p u‖ :=
      intervalIntegral.integral_nonneg hab fun _ _ => norm_nonneg _
    linarith
  have hchord : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → ‖p b - p a‖ ≤ s b - s a := fun a b ha hab hb => by
    rw [hsdiff a b ha hab hb]; exact dgPath_chord_le hp ha hab hb
  set ℓ := s 1 with hℓ
  have hℓδ : δ ≤ ℓ := by
    have := hchord 0 1 le_rfl zero_le_one le_rfl
    rw [hp.source, hp.target, hs0] at this
    linarith
  set n : ℕ := ⌊ℓ / δ⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hδ]; linarith)
  have hnle : (n : ℝ) * δ ≤ ℓ := by
    have := Nat.floor_le (div_nonneg (by linarith) hδ.le : 0 ≤ ℓ / δ)
    rw [← hn, le_div_iff₀ hδ] at this; exact this
  have hnlt : ℓ < ((n : ℝ) + 1) * δ := by
    have := Nat.lt_floor_add_one (ℓ / δ)
    rw [← hn, div_lt_iff₀ hδ] at this; exact this
  -- cut times
  have hex : ∀ i : ℕ, ∃ t ∈ Icc (0:ℝ) 1, (i < n → s t = i * δ) ∧ (i = 0 → t = 0) ∧
      (n ≤ i → t = 1) := by
    intro i
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; exact ⟨0, ⟨le_rfl, zero_le_one⟩, fun _ => by simp [hs0], fun _ => rfl,
        fun h => absurd h (by omega)⟩
    by_cases hin : i < n
    · have hmem : (i : ℝ) * δ ∈ Icc (s 0) (s 1) := by
        rw [hs0]
        refine ⟨by positivity, ?_⟩
        have : (i : ℝ) ≤ n := by exact_mod_cast hin.le
        nlinarith
      obtain ⟨t, ht, hst⟩ := intermediate_value_Icc zero_le_one hscont hmem
      exact ⟨t, ht, fun _ => hst, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · exact ⟨1, ⟨zero_le_one, le_rfl⟩, fun h => absurd h hin, fun h => absurd h (by omega),
        fun _ => rfl⟩
  choose T hT hTs hT0 hT1 using hex
  have hTn : T n = 1 := hT1 n le_rfl
  have hsT : ∀ i ≤ n, s (T i) = if i < n then i * δ else ℓ := fun i hi => by
    split_ifs with h
    · exact hTs i h
    · rw [hT1 i (by omega)]
  have hsT_lt : ∀ i < n, s (T i) < s (T (i+1)) := fun i hi => by
    rw [hsT i hi.le, hsT (i+1) hi, if_pos hi]
    split_ifs with h
    · push_cast; linarith
    · have : (n:ℝ) = i + 1 := by exact_mod_cast (show n = i + 1 by omega)
      rw [this] at hnle; linarith
  have hTmono : ∀ i < n, T i ≤ T (i+1) := fun i hi => by
    by_contra hc
    push_neg at hc
    have := hsmono (T (i+1)) (T i) (hT (i+1)).1 hc.le (hT i).2
    linarith [hsT_lt i hi]
  have hpiece : ∀ i < n, δ ≤ s (T (i+1)) - s (T i) ∧ s (T (i+1)) - s (T i) ≤ 2 * δ :=
    fun i hi => by
    rw [hsT i hi.le, hsT (i+1) hi, if_pos hi]
    split_ifs with h
    · push_cast; constructor <;> linarith
    · have : (n:ℝ) = i + 1 := by exact_mod_cast (show n = i + 1 by omega)
      rw [this] at hnle hnlt; constructor <;> linarith
  -- displacement inside a piece
  have hdisp : ∀ i < n, ∀ t ∈ Icc (T i) (T (i+1)), ‖p t - p (T i)‖ ≤ 2 * δ :=
    fun i hi t ht => by
    have h1 := hchord (T i) t (hT i).1 ht.1 (ht.2.trans (hT (i+1)).2)
    have h2 := hsmono t (T (i+1)) ((hT i).1.trans ht.1) ht.2 (hT (i+1)).2
    linarith [(hpiece i hi).2]
  set U : ℕ → ℤ × ℤ := fun i => rnd δ (p (T i)) with hU
  have hstep : ∀ i < n, |(U (i+1)).1 - (U i).1| ≤ 3 ∧ |(U (i+1)).2 - (U i).2| ≤ 3 :=
    fun i hi => by
    have hd := hdisp i hi (T (i+1)) ⟨hTmono i hi, le_rfl⟩
    refine ⟨abs_round_sub_round_le hδ ?_, abs_round_sub_round_le hδ ?_⟩
    · exact (Complex.abs_re_le_norm _).trans (by simpa using hd)
    · exact (Complex.abs_im_le_norm _).trans (by simpa using hd)
  have hwlen : ∀ i < n, wlen (U i) (U (i+1)) ≤ 3 := fun i hi => by
    obtain ⟨h1, h2⟩ := hstep i hi
    unfold wlen
    rw [Int.abs_eq_natAbs] at h1 h2
    exact max_le (by omega) (by omega)
  -- every walk vertex is within `7δ` of every point of its piece
  have hnear : ∀ i < n, ∀ x ∈ gridWalk δ (U i) (U (i+1)), ∀ t ∈ Icc (T i) (T (i+1)),
      ‖x - p t‖ ≤ 8 * δ := fun i hi x hx t ht => by
    obtain ⟨c, rfl, h1, h2, h3, h4⟩ := mem_gridWalk hx
    obtain ⟨a1, a2⟩ := hstep i hi
    have hc1 : |c.1 - (rnd δ (p (T i))).1| ≤ 3 := by
      rw [abs_le] at a1 ⊢; simp only [min_def, max_def, hU] at h1 h2 a1 ⊢
      split_ifs at h1 h2 <;> constructor <;> omega
    have hc2 : |c.2 - (rnd δ (p (T i))).2| ≤ 3 := by
      rw [abs_le] at a2 ⊢; simp only [min_def, max_def, hU] at h3 h4 a2 ⊢
      split_ifs at h3 h4 <;> constructor <;> omega
    have := norm_gpt_sub_le hδ (p (T i)) c hc1 hc2
    have hd := hdisp i hi t ht
    calc ‖gpt δ c - p t‖ = ‖(gpt δ c - p (T i)) - (p t - p (T i))‖ := by ring_nf
      _ ≤ ‖gpt δ c - p (T i)‖ + ‖p t - p (T i)‖ := norm_sub_le _ _
      _ ≤ 8 * δ := by linarith
  have hTi01 : ∀ i < n, ∀ t ∈ Icc (T i) (T (i+1)), t ∈ Icc (0:ℝ) 1 := fun i hi t ht =>
    ⟨(hT i).1.trans ht.1, ht.2.trans (hT (i+1)).2⟩
  -- the bound on each walk
  set f : ℂ → ℝ := fun x => Real.exp (ξ * φ x) with hf
  set g : ℝ → ℝ := fun t => Real.exp (ξ * φ (p t)) * ‖deriv p t‖ with hg
  have hgI : IntervalIntegrable g volume 0 1 := by
    have hc : ContinuousOn (fun t => Real.exp (ξ * φ (p t))) (uIcc (0 : ℝ) 1) := by
      rw [uIcc_of_le zero_le_one]
      exact Real.continuous_exp.comp_continuousOn
        ((continuous_const.mul hφ).comp_continuousOn hp.continuousOn)
    have := hN.continuousOn_mul hc
    simpa [hg, mul_comm] using this
  set B : ℕ → ℝ := fun i => δ⁻¹ * Real.exp (ξ * osc φ (8 * δ)) * ∫ t in T i..T (i+1), g t
    with hB
  have hfB : ∀ i < n, ∀ x ∈ gridWalk δ (U i) (U (i+1)), f x ≤ B i := fun i hi x hx => by
    have hab := hTmono i hi
    have hxS : x ∈ rS 1 := hS (T i) (hT i) x (hnear i hi x hx (T i) ⟨le_rfl, hab⟩)
    have hpt : ∀ t ∈ Icc (T i) (T (i+1)), f x * ‖deriv p t‖ ≤
        Real.exp (ξ * osc φ (8 * δ)) * g t := fun t ht => by
      have hpS : p t ∈ rS 1 := hS t (hTi01 i hi t ht) (p t) (by simp; positivity)
      have ho := LQGDimension.TreeIneqJ42.abs_sub_le_osc hφ (norm_le_three_of_mem_rS hxS)
        (norm_le_three_of_mem_rS hpS) (hnear i hi x hx t ht)
      have h1 : f x ≤ Real.exp (ξ * osc φ (8 * δ)) * Real.exp (ξ * φ (p t)) := by
        rw [hf, ← Real.exp_add]
        apply Real.exp_le_exp.2
        have := (abs_le.1 ho).2
        nlinarith
      simp only [hg, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have hI1 : IntervalIntegrable (fun t => f x * ‖deriv p t‖) volume (T i) (T (i+1)) :=
      (intervalIntegrable_sub01 hN (hT i).1 hab (hT (i+1)).2).const_mul _
    have hI2 : IntervalIntegrable (fun t => Real.exp (ξ * osc φ (8 * δ)) * g t) volume
        (T i) (T (i+1)) := (intervalIntegrable_sub01 hgI (hT i).1 hab (hT (i+1)).2).const_mul _
    have hint := intervalIntegral.integral_mono_on hab hI1 hI2 hpt
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      ← hsdiff (T i) (T (i+1)) (hT i).1 hab (hT (i+1)).2] at hint
    have hδs := (hpiece i hi).1
    have hfx : 0 ≤ f x := (Real.exp_pos _).le
    have : δ * f x ≤ Real.exp (ξ * osc φ (8 * δ)) * ∫ t in T i..T (i+1), g t := by nlinarith
    rw [hB]
    simp only
    rw [mul_assoc, le_inv_mul_iff₀ hδ]
    linarith
  obtain ⟨L, hL0, hLh, hLl, hLc, hLm, hLs⟩ :=
    exists_chain_walks hδ U f (fun x => (Real.exp_pos _).le) B n hwlen hfB
  have hU0 : U 0 = rnd δ z := by simp only [hU]; rw [hT0 0 rfl, hp.source]
  have hUn : U n = rnd δ w := by simp only [hU]; rw [hTn, hp.target]
  have hmem0 : gpt δ (U 0) ∈ gridWalk δ (U 0) (U (0+1)) := by
    rw [gridWalk_eq_cons]; exact List.mem_cons_self
  have hwalkS : ∀ i < n, ∀ x ∈ gridWalk δ (U i) (U (i+1)), x ∈ rS 1 ∧ x ∈ Blueprint.gridPts δ :=
    fun i hi x hx => by
    refine ⟨hS (T i) (hT i) x (hnear i hi x hx (T i) ⟨le_rfl, hTmono i hi⟩), ?_⟩
    obtain ⟨c, rfl, -⟩ := mem_gridWalk hx
    exact ⟨c.1, c.2, rfl⟩
  refine ⟨L, ⟨hL0, fun x hx => ?_, hLc⟩, by rw [hLh, hU0], by rw [hLl, hUn], ?_⟩
  · rcases hLm x hx with h | ⟨i, hi, h⟩
    · subst h; exact hwalkS 0 (by omega) _ hmem0
    · exact hwalkS i hi x h
  · have hB0 : f (gpt δ (U 0)) ≤ B 0 := hfB 0 (by omega) _ hmem0
    have hBnn : ∀ i < n, 0 ≤ B i := fun i hi =>
      (Real.exp_pos _).le.trans (hfB i hi _ (by rw [gridWalk_eq_cons]; exact List.mem_cons_self))
    have hsumB : ∑ i ∈ Finset.range n, B i =
        δ⁻¹ * Real.exp (ξ * osc φ (8 * δ)) * LQGDimension.lfppLength ξ φ p := by
      simp only [hB]
      rw [← Finset.mul_sum, intervalIntegral.sum_integral_adjacent_intervals
        (fun k hk => intervalIntegrable_sub01 hgI (hT k).1 (hTmono k hk) (hT (k+1)).2),
        hT0 0 rfl, hTn]
      rfl
    have hB0le : B 0 ≤ ∑ i ∈ Finset.range n, B i :=
      Finset.single_le_sum (fun i hi => hBnn i (Finset.mem_range.1 hi))
        (Finset.mem_range.2 (by omega))
    calc (L.map f).sum ≤ f (gpt δ (U 0)) + 3 * ∑ i ∈ Finset.range n, B i := hLs
      _ ≤ 4 * ∑ i ∈ Finset.range n, B i := by linarith
      _ = _ := by rw [hsumB]; ring

end LQGMetric.DFGPS.L36
