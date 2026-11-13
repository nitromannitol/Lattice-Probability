/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS3.Annulus at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.LogAnnulus

/-!
# Annuli, boundary layers and crossings

Geometric helpers for GMS [18] Lemmas 3.4 and 3.8 ([18])
and the corrected boundary term of Lemma 3.1.

* `annulusSet z r₁ r₂ = {u : r₁ < |u − z| < r₂}` (open; its frontier lies on the two circles,
  `frontier_annulusSet_subset`); `volume_annulusSet_le`.
* `radialBump z a w`: the boundary layer of the circle `∂B_a(z)` in the boundary correction,
  `min{1, max{0, 2 − dist(u, ∂B_a(z))/w}}`
  (`dist(u, ∂B_a(z)) = ||u − z| − a|`): it takes values in `[0, 1]`, equals `1` within `w` of the circle,
  vanishes farther than `2w` from it, is `w⁻¹`-Lipschitz (`lipschitzWith_radialBump`, the hypothesis
  Proposition 2.10 needs with `w = ε^{β'}`), and `∫ radialBump ≤ 8π w (a + 2w)`
  (`lintegral_radialBump_le`).
* `volume_radialShell_le`: `area({u : ||u − z| − a| < r}) ≤ 4π r (a + r)` (the hypothesis
  `area(B_r(∂D)) ≤ C r` of Proposition 2.10 for annuli).
* `exists_mem_eq_of_isPreconnected`: a preconnected set on which a continuous function takes values
  `≤ t` and `≥ t` takes the value `t` (cells and chains of cells cross circles and square loops).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace MatedCRTHarmonic.GMS3

/-- The open annulus `{u : r₁ < |u − z| < r₂}`. -/
def annulusSet (z : ℂ) (r₁ r₂ : ℝ) : Set ℂ := {u | r₁ < ‖u - z‖ ∧ ‖u - z‖ < r₂}

theorem continuous_norm_sub_const (z : ℂ) : Continuous fun u : ℂ => ‖u - z‖ :=
  (continuous_id.sub continuous_const).norm

theorem isOpen_annulusSet (z : ℂ) (r₁ r₂ : ℝ) : IsOpen (annulusSet z r₁ r₂) :=
  (isOpen_lt continuous_const (continuous_norm_sub_const z)).inter
    (isOpen_lt (continuous_norm_sub_const z) continuous_const)

theorem annulusSet_subset_ball (z : ℂ) (r₁ r₂ : ℝ) : annulusSet z r₁ r₂ ⊆ ball z r₂ :=
  fun u hu => by rw [mem_ball, dist_eq_norm]; exact hu.2

theorem isBounded_annulusSet (z : ℂ) (r₁ r₂ : ℝ) : Bornology.IsBounded (annulusSet z r₁ r₂) :=
  isBounded_ball.subset (annulusSet_subset_ball z r₁ r₂)

theorem volume_annulusSet_le (z : ℂ) (r₁ r₂ : ℝ) :
    volume (annulusSet z r₁ r₂) ≤ ENNReal.ofReal (π * r₂ ^ 2) := by
  refine (measure_mono (annulusSet_subset_ball z r₁ r₂)).trans ?_
  rw [Complex.volume_ball]
  by_cases hr : 0 ≤ r₂
  · rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      NNReal.coe_real_pi, mul_comm]
  · rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp hr))]
    simp

/-- The frontier of the open annulus lies on its two circles. -/
theorem frontier_annulusSet_subset (z : ℂ) (r₁ r₂ : ℝ) :
    frontier (annulusSet z r₁ r₂) ⊆ {u | ‖u - z‖ = r₁ ∨ ‖u - z‖ = r₂} := by
  intro u hu
  rw [frontier, (isOpen_annulusSet z r₁ r₂).interior_eq] at hu
  have hcl : closure (annulusSet z r₁ r₂) ⊆ {u | r₁ ≤ ‖u - z‖ ∧ ‖u - z‖ ≤ r₂} :=
    closure_minimal (fun v hv => ⟨hv.1.le, hv.2.le⟩)
      ((isClosed_le continuous_const (continuous_norm_sub_const z)).inter
        (isClosed_le (continuous_norm_sub_const z) continuous_const))
  obtain ⟨h1, h2⟩ := hcl hu.1
  by_contra hne
  simp only [Set.mem_ofPred_eq, not_or] at hne
  exact hu.2 ⟨lt_of_le_of_ne h1 (Ne.symm hne.1), lt_of_le_of_ne h2 hne.2⟩

/-- **Crossing lemma.** If a continuous function takes a value `≤ t` and a value `≥ t` on a
preconnected set, it takes the value `t` there. -/
theorem exists_mem_eq_of_isPreconnected {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {φ : X → ℝ} (hφ : Continuous φ) {a b : X} (ha : a ∈ S) (hb : b ∈ S)
    {t : ℝ} (hat : φ a ≤ t) (htb : t ≤ φ b) : ∃ c ∈ S, φ c = t := by
  obtain ⟨c, hc, hct⟩ := hS.intermediate_value ha hb hφ.continuousOn ⟨hat, htb⟩
  exact ⟨c, hc, hct⟩

/-! ### Boundary layers of circles -/

/-- The boundary layer of the circle `∂B_a(z)` at width `w`:
`min{1, max{0, 2 − ||u − z| − a| / w}}`. -/
def radialBump (z : ℂ) (a w : ℝ) (u : ℂ) : ℝ := max 0 (min 1 (2 - |‖u - z‖ - a| / w))

theorem radialBump_nonneg (z : ℂ) (a w : ℝ) (u : ℂ) : 0 ≤ radialBump z a w u := le_max_left _ _

theorem radialBump_le_one (z : ℂ) (a w : ℝ) (u : ℂ) : radialBump z a w u ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem radialBump_eq_one {z : ℂ} {a w : ℝ} (hw : 0 < w) {u : ℂ} (hu : |‖u - z‖ - a| ≤ w) :
    radialBump z a w u = 1 := by
  unfold radialBump
  have : 1 ≤ 2 - |‖u - z‖ - a| / w := by
    rw [le_sub_comm, div_le_iff₀ hw]; linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

theorem radialBump_eq_zero {z : ℂ} {a w : ℝ} (hw : 0 < w) {u : ℂ} (hu : 2 * w ≤ |‖u - z‖ - a|) :
    radialBump z a w u = 0 := by
  unfold radialBump
  have : 2 - |‖u - z‖ - a| / w ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hw]; linarith
  rw [max_eq_left ((min_le_right _ _).trans this)]

/-- The boundary layer is `w⁻¹`-Lipschitz. -/
theorem lipschitzWith_radialBump (z : ℂ) (a : ℝ) {w : ℝ} (hw : 0 < w) :
    LipschitzWith (Real.toNNReal w⁻¹) (radialBump z a w) := by
  have h1 : LipschitzWith 1 fun u : ℂ => |‖u - z‖ - a| := by
    have hn : LipschitzWith 1 fun u : ℂ => ‖u - z‖ :=
      LipschitzWith.of_dist_le_mul fun u v => by
        rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
        have := abs_norm_sub_norm_le (u - z) (v - z)
        rwa [sub_sub_sub_cancel_right] at this
    exact LipschitzWith.of_dist_le_mul fun u v => by
      rw [NNReal.coe_one, one_mul, Real.dist_eq]
      calc |abs (‖u - z‖ - a) - abs (‖v - z‖ - a)| ≤ |(‖u - z‖ - a) - (‖v - z‖ - a)| :=
            abs_abs_sub_abs_le_abs_sub _ _
        _ = |‖u - z‖ - ‖v - z‖| := by ring_nf
        _ ≤ dist u v := by
            have := hn.dist_le_mul u v
            rwa [NNReal.coe_one, one_mul, Real.dist_eq] at this
  have h2 : LipschitzWith (Real.toNNReal w⁻¹) fun u : ℂ => 2 - |‖u - z‖ - a| / w := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    rw [Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.mpr hw.le)]
    have := h1.dist_le_mul u v
    rw [NNReal.coe_one, one_mul, Real.dist_eq] at this
    calc |(2 - |‖u - z‖ - a| / w) - (2 - |‖v - z‖ - a| / w)|
        = w⁻¹ * |abs (‖u - z‖ - a) - abs (‖v - z‖ - a)| := by
          rw [show (2 - |‖u - z‖ - a| / w) - (2 - |‖v - z‖ - a| / w) =
              -(w⁻¹ * (|‖u - z‖ - a| - |‖v - z‖ - a|)) by ring, abs_neg, abs_mul,
            abs_of_pos (inv_pos.mpr hw)]
      _ ≤ w⁻¹ * dist u v := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hw.le)
  exact (h2.const_min 1).const_max 0

theorem continuous_radialBump (z : ℂ) (a : ℝ) {w : ℝ} (hw : 0 < w) :
    Continuous (radialBump z a w) :=
  (lipschitzWith_radialBump z a hw).continuous

/-- The radial shell `{u : ||u − z| − a| < r}` has area at most `4π r (a + r)` (`a ≥ 0`). -/
theorem lintegral_radial_shell_le {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t * (Ioo (a - r) (a + r)).indicator 1 t ≤
      ENNReal.ofReal (2 * r * (a + r)) := by
  calc ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t * (Ioo (a - r) (a + r)).indicator 1 t
      ≤ ∫⁻ t, (Ioo (a - r) (a + r)).indicator (fun _ => ENNReal.ofReal (a + r)) t := by
        refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun t => ?_)
        by_cases ht : t ∈ Ioo (a - r) (a + r)
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, Pi.one_apply, mul_one]
          exact ENNReal.ofReal_le_ofReal ht.2.le
        · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]
    _ = ENNReal.ofReal (a + r) * volume (Ioo (a - r) (a + r)) :=
        lintegral_indicator_const measurableSet_Ioo _
    _ = ENNReal.ofReal (2 * r * (a + r)) := by
        rw [Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

theorem volume_radialShell_le (z : ℂ) {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) :
    volume {u : ℂ | |‖u - z‖ - a| < r} ≤ ENNReal.ofReal (4 * π * r * (a + r)) := by
  have hmeas : Measurable fun t : ℝ => (Ioo (a - r) (a + r)).indicator (1 : ℝ → ℝ≥0∞) t :=
    measurable_const.indicator measurableSet_Ioo
  have hset : {u : ℂ | |‖u - z‖ - a| < r} = (fun u => u - z) ⁻¹' {u | ‖u‖ ∈ Ioo (a - r) (a + r)} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioo, abs_lt]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hm2 : MeasurableSet {u : ℂ | ‖u‖ ∈ Ioo (a - r) (a + r)} :=
    measurableSet_Ioo.preimage continuous_norm.measurable
  rw [hset, ← lintegral_indicator_one ((measurable_sub_const z) hm2)]
  have : ∫⁻ u, ((fun u => u - z) ⁻¹' {u : ℂ | ‖u‖ ∈ Ioo (a - r) (a + r)}).indicator 1 u =
      ∫⁻ u : ℂ, (Ioo (a - r) (a + r)).indicator (1 : ℝ → ℝ≥0∞) ‖u‖ := by
    rw [← lintegral_sub_right_eq_self (fun u : ℂ => (Ioo (a - r) (a + r)).indicator
      (1 : ℝ → ℝ≥0∞) ‖u‖) z]
    rfl
  rw [this, lintegral_radial _ hmeas]
  calc ENNReal.ofReal (2 * π) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t * (Ioo (a - r) (a + r)).indicator 1 t
      ≤ ENNReal.ofReal (2 * π) * ENNReal.ofReal (2 * r * (a + r)) := by
        gcongr
        exact lintegral_radial_shell_le ha hr
    _ = ENNReal.ofReal (4 * π * r * (a + r)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- `∫ radialBump z a w ≤ 8π w (a + 2w)`. -/
theorem lintegral_radialBump_le (z : ℂ) {a w : ℝ} (ha : 0 ≤ a) (hw : 0 < w) :
    ∫⁻ u, ENNReal.ofReal (radialBump z a w u) ≤ ENNReal.ofReal (8 * π * w * (a + 2 * w)) := by
  calc ∫⁻ u, ENNReal.ofReal (radialBump z a w u)
      ≤ ∫⁻ u, {u : ℂ | |‖u - z‖ - a| < 2 * w}.indicator 1 u := by
        refine lintegral_mono fun u => ?_
        by_cases hu : u ∈ {u : ℂ | |‖u - z‖ - a| < 2 * w}
        · rw [Set.indicator_of_mem hu, Pi.one_apply, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (radialBump_le_one z a w u)
        · rw [Set.indicator_of_notMem hu, radialBump_eq_zero hw (not_lt.mp hu),
            ENNReal.ofReal_zero]
    _ = volume {u : ℂ | |‖u - z‖ - a| < 2 * w} := by
        refine lintegral_indicator_one ?_
        exact measurableSet_lt ((continuous_norm_sub_const z).sub continuous_const).abs.measurable
          measurable_const
    _ ≤ ENNReal.ofReal (4 * π * (2 * w) * (a + 2 * w)) := volume_radialShell_le z ha (by positivity)
    _ = ENNReal.ofReal (8 * π * w * (a + 2 * w)) := by ring_nf

/-- A set of diameter `≤ δ` meeting the circle `∂B_a(z)` lies in its `δ`-shell. -/
theorem abs_norm_sub_le_of_diam {S : Set ℂ} (hS : Bornology.IsBounded S) {δ : ℝ}
    (hdiam : diam S ≤ δ) {z c : ℂ} {a : ℝ} (hc : c ∈ S) (hca : ‖c - z‖ = a) {u : ℂ} (hu : u ∈ S) :
    |‖u - z‖ - a| ≤ δ := by
  rw [← hca]
  calc |‖u - z‖ - ‖c - z‖| ≤ ‖(u - z) - (c - z)‖ := abs_norm_sub_norm_le _ _
    _ = dist u c := by rw [sub_sub_sub_cancel_right, dist_eq_norm]
    _ ≤ diam S := dist_le_diam_of_mem hS hu hc
    _ ≤ δ := hdiam

end MatedCRTHarmonic.GMS3
