/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.CurvePauses at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.CurveSpace
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Order.Hom.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Constant pauses do not change the actual Fréchet curve class. A continuous
nondecreasing time map is approximated by explicit strictly increasing
homeomorphisms; it is never assumed to be an allowed homeomorphism itself. -/

open Set
open scoped unitInterval ENNReal

namespace BouRabeeGwynne
namespace CurvePauses

variable (φ : C(unitInterval, unitInterval))

/-- Add a small strictly increasing part to the original nondecreasing clock. -/
noncomputable def blend (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (t : unitInterval) : unitInterval :=
  ⟨(1 - ε) * (φ t : ℝ) + ε * (t : ℝ),
    ⟨add_nonneg (mul_nonneg (sub_nonneg.mpr hε1) (φ t).property.1)
      (mul_nonneg hε t.property.1), by
      have h₁ := mul_le_mul_of_nonneg_left (φ t).property.2 (sub_nonneg.mpr hε1)
      have h₂ := mul_le_mul_of_nonneg_left t.property.2 hε
      nlinarith⟩⟩

lemma continuous_blend (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Continuous (blend φ ε hε hε1) := by
  unfold blend
  fun_prop

lemma blend_strictMono (hmono : Monotone φ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    StrictMono (blend φ ε hε.le hε1) := by
  intro s t hst
  change (1 - ε) * (φ s : ℝ) + ε * (s : ℝ) <
    (1 - ε) * (φ t : ℝ) + ε * (t : ℝ)
  exact add_lt_add_of_le_of_lt
    (mul_le_mul_of_nonneg_left (hmono hst.le) (sub_nonneg.mpr hε1))
    (mul_lt_mul_of_pos_left hst hε)

lemma blend_zero (hzero : φ 0 = 0) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    blend φ ε hε hε1 0 = 0 := by
  apply Subtype.ext
  simp [blend, hzero]

lemma blend_one (hone : φ 1 = 1) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    blend φ ε hε hε1 1 = 1 := by
  apply Subtype.ext
  simp [blend, hone]

lemma blend_surjective (hzero : φ 0 = 0) (hone : φ 1 = 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Function.Surjective (blend φ ε hε hε1) := by
  intro y
  apply intermediate_value_univ (0 : unitInterval) (1 : unitInterval)
    (continuous_blend φ ε hε hε1)
  rw [blend_zero φ hzero, blend_one φ hone]
  exact ⟨bot_le, le_top⟩

/-- An actual increasing order isomorphism, hence an allowed time homeomorphism. -/
noncomputable def blendTimeChange (hmono : Monotone φ) (hzero : φ 0 = 0) (hone : φ 1 = 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : unitInterval ≃o unitInterval :=
  StrictMono.orderIsoOfSurjective (blend φ ε hε.le hε1)
    (blend_strictMono φ hmono ε hε hε1) (blend_surjective φ hzero hone ε hε.le hε1)

lemma blend_dist_le (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (t : unitInterval) :
    dist (blend φ ε hε hε1 t) (φ t) ≤ ε := by
  change |(1 - ε) * (φ t : ℝ) + ε * (t : ℝ) - (φ t : ℝ)| ≤ ε
  have heq : (1 - ε) * (φ t : ℝ) + ε * (t : ℝ) - (φ t : ℝ) =
      ε * ((t : ℝ) - (φ t : ℝ)) := by ring
  rw [heq, abs_mul, abs_of_nonneg hε]
  have hd : |(t : ℝ) - (φ t : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [t.property.1, t.property.2,
      (φ t).property.1, (φ t).property.2]
  exact (mul_le_mul_of_nonneg_left hd hε).trans_eq (mul_one ε)

end CurvePauses

/-- Continuous nondecreasing surjective clocks, including terminal pauses,
preserve the actual infimum-over-homeomorphisms Fréchet quotient. -/
theorem curveSpace_project_comp_monotone {d : ℕ}
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d)))
    (φ : C(unitInterval, unitInterval)) (hmono : Monotone φ)
    (hzero : φ 0 = 0) (hone : φ 1 = 1) :
    CurveSpace.project (f.comp φ) = CurveSpace.project f := by
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨δ, hδ, huc⟩ := f.uniform_continuity η hη
  let ε : ℝ := min (δ / 2) (1 / 2)
  have hε : 0 < ε := lt_min (half_pos hδ) (by norm_num)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  let e := CurvePauses.blendTimeChange φ hmono hzero hone ε hε hε1
  have hcost : NormalizedCurve.timeChangeCost
      (NormalizedCurve.ofPath (f.comp φ)) (NormalizedCurve.ofPath f) e ≤ ENNReal.ofReal η := by
    apply iSup_le
    intro t
    change edist (f (φ t)) (f (e t)) ≤ ENNReal.ofReal η
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    apply (huc ?_).le
    have ht := CurvePauses.blend_dist_le φ ε hε.le hε1 t
    change dist (φ t) (CurvePauses.blend φ ε hε.le hε1 t) < δ
    rw [dist_comm]
    exact ht.trans_lt hεδ
  have hdist : edist (CurveSpace.project (f.comp φ)) (CurveSpace.project f) ≤
      ENNReal.ofReal η := (iInf_le _ e).trans hcost
  rw [edist_dist] at hdist
  have hr := (ENNReal.ofReal_le_ofReal_iff hη.le).mp hdist
  simpa only [zero_add] using hr

/-- A clock which finishes the original path at normalized time `a` and then
holds its endpoint. -/
noncomputable def terminalPauseClock (a : ℝ) : C(unitInterval, unitInterval) :=
  ⟨fun t => projIcc 0 1 zero_le_one ((t : ℝ) / a), by fun_prop⟩

lemma terminalPauseClock_monotone {a : ℝ} (ha : 0 < a) :
    Monotone (terminalPauseClock a) := by
  intro s t hst
  exact monotone_projIcc zero_le_one (div_le_div_of_nonneg_right hst ha.le)

@[simp] lemma terminalPauseClock_zero (a : ℝ) : terminalPauseClock a 0 = 0 := by
  simp [terminalPauseClock, projIcc_left]

lemma terminalPauseClock_one {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    terminalPauseClock a 1 = 1 := by
  apply projIcc_eq_one.mpr
  exact (one_le_div ha).mpr ha1

lemma terminalPauseClock_of_le {a : ℝ} (ha : 0 < a) (t : unitInterval)
    (ht : a ≤ (t : ℝ)) : terminalPauseClock a t = 1 := by
  apply projIcc_eq_one.mpr
  exact (one_le_div ha).mpr ht

/-- Adding a constant terminal segment leaves the genuine curve class unchanged. -/
theorem curveSpace_project_terminalPause {d : ℕ}
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    CurveSpace.project (f.comp (terminalPauseClock a)) = CurveSpace.project f :=
  curveSpace_project_comp_monotone f _ (terminalPauseClock_monotone ha)
    (terminalPauseClock_zero a) (terminalPauseClock_one ha ha1)

end BouRabeeGwynne
