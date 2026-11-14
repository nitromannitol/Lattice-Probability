import LatticeProb.Topology.ZeroPrefixRayDistance
import LatticeProb.Topology.PositivePrefixRayDistance

/-! # Distances of finite prefixes and constant-tail rays -/

set_option autoImplicit false
open Set
open scoped ENNReal NNReal

namespace LatticeProb.StoppedRayIntervalDistance

open LatticeProb.IntervalReparamEDist

variable {T₁ T₂ : ℝ≥0}

/-- The point `min t T₁` of `[0, T₁]`. -/
def clipIcc (T₁ : ℝ≥0) (t : ℝ≥0) : Icc (0 : ℝ≥0) T₁ :=
  ⟨min t T₁, zero_le, min_le_right _ _⟩

/-- An increasing homeomorphism `φ : [0, T₁] → [0, T₂]` continued after `T₁` by the shift `t ↦ T₂ + (t - T₁)`. -/
noncomputable def extendIccFun (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) (t : ℝ≥0) : ℝ≥0 :=
  (φ (clipIcc T₁ t) : ℝ≥0) + (t - T₁)

/-- An order isomorphism of `[0, T₁]` onto `[0, T₂]` sends `T₁` to `T₂`. -/
theorem orderIso_Icc_right (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) :
    (φ ⟨T₁, zero_le, le_rfl⟩ : ℝ≥0) = T₂ := by
  obtain ⟨x, hx⟩ := φ.surjective ⟨T₂, zero_le, le_rfl⟩
  refine le_antisymm (φ ⟨T₁, zero_le, le_rfl⟩).2.2 ?_
  have hle : φ x ≤ φ ⟨T₁, zero_le, le_rfl⟩ := φ.monotone (show x ≤ ⟨T₁, zero_le, le_rfl⟩ from x.2.2)
  rw [hx] at hle
  exact hle

theorem orderIso_clipIcc_of_le (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) {t : ℝ≥0} (ht : T₁ ≤ t) :
    (φ (clipIcc T₁ t) : ℝ≥0) = T₂ := by
  have hc : clipIcc T₁ t = ⟨T₁, zero_le, le_rfl⟩ := Subtype.ext (min_eq_right ht)
  rw [hc, orderIso_Icc_right]

theorem extendIccFun_strictMono (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) : StrictMono (extendIccFun φ) := by
  have hg : Monotone fun t : ℝ≥0 => (φ (clipIcc T₁ t) : ℝ≥0) := fun t t' htt' =>
    φ.monotone (show clipIcc T₁ t ≤ clipIcc T₁ t' from min_le_min htt' le_rfl)
  intro t t' htt'
  rcases le_or_gt t' T₁ with h' | h'
  · have ht : t ≤ T₁ := htt'.le.trans h'
    have hlt : clipIcc T₁ t < clipIcc T₁ t' := by
      show min t T₁ < min t' T₁
      rw [min_eq_left ht, min_eq_left h']
      exact htt'
    have h1 : (φ (clipIcc T₁ t) : ℝ≥0) < φ (clipIcc T₁ t') := φ.strictMono hlt
    simp only [extendIccFun, tsub_eq_zero_of_le ht, tsub_eq_zero_of_le h', add_zero]
    exact h1
  · have h1 : t - T₁ < t' - T₁ := by
      rcases le_total T₁ t with ht | ht
      · exact tsub_lt_tsub_right_of_le ht htt'
      · rw [tsub_eq_zero_of_le ht]
        exact tsub_pos_of_lt h'
    exact add_lt_add_of_le_of_lt (hg htt'.le) h1

theorem extendIccFun_surjective (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) :
    Function.Surjective (extendIccFun φ) := by
  intro y
  rcases le_or_gt y T₂ with hy | hy
  · obtain ⟨x, hx⟩ := φ.surjective ⟨y, zero_le, hy⟩
    refine ⟨x.1, ?_⟩
    have hc : clipIcc T₁ x.1 = x := Subtype.ext (min_eq_left x.2.2)
    rw [extendIccFun, hc, tsub_eq_zero_of_le x.2.2, add_zero, hx]
  · refine ⟨T₁ + (y - T₂), ?_⟩
    simp only [extendIccFun, orderIso_clipIcc_of_le φ (le_self_add : T₁ ≤ T₁ + (y - T₂)), add_tsub_cancel_left]
    exact add_tsub_cancel_of_le hy.le

/-- The extension `extendIccFun φ` as an order isomorphism of `[0, ∞)`. -/
noncomputable def extendIccOrderIso (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) : ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective (extendIccFun φ) (extendIccFun_strictMono φ) (extendIccFun_surjective φ)

theorem extendIccOrderIso_apply (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) (t : ℝ≥0) :
    extendIccOrderIso φ t = extendIccFun φ t := rfl

/-- After the extension, clipping at `T₂` is the image of the clip at `T₁`. -/
theorem min_extendIccFun (φ : Icc (0 : ℝ≥0) T₁ ≃o Icc (0 : ℝ≥0) T₂) (t : ℝ≥0) :
    min (extendIccFun φ t) T₂ = (φ (clipIcc T₁ t) : ℝ≥0) := by
  rcases le_total t T₁ with ht | ht
  · simp only [extendIccFun, tsub_eq_zero_of_le ht, add_zero]
    exact min_eq_left (φ (clipIcc T₁ t)).2.2
  · rw [orderIso_clipIcc_of_le φ ht]
    exact min_eq_right (by simp only [extendIccFun, orderIso_clipIcc_of_le φ ht]; exact le_self_add)


variable {E : Type*} [PseudoEMetricSpace E]

/-- A finite interval in the extended-duration convention is the corresponding closed interval. -/
def timeIntervalOrderIso (T : ℝ≥0) : TimeInterval (T : ℝ≥0∞) ≃o Icc (0 : ℝ≥0) T where
  toFun t := ⟨t.1, zero_le, ENNReal.coe_le_coe.mp t.2⟩
  invFun t := ⟨t.1, ENNReal.coe_le_coe.mpr t.2.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

/-- The ray distance of constant-tail extensions is bounded by the distance of their finite
intervals, including the case in which the interval time-change type is empty. -/
theorem reparamEDist_stopped_le_intervalEDist (f g : ℝ≥0 → E) (T U : ℝ≥0) :
    ReparamEDist.reparamEDist (fun t => f (min t T)) (fun t => g (min t U)) ≤
      intervalEDist f g (T : ℝ≥0∞) (U : ℝ≥0∞) := by
  refine le_iInf fun φ => ?_
  let ψ : Icc (0 : ℝ≥0) T ≃o Icc (0 : ℝ≥0) U :=
    (timeIntervalOrderIso T).symm.trans (φ.trans (timeIntervalOrderIso U))
  refine iInf_le_of_le (extendIccOrderIso ψ) (iSup_le fun t => ?_)
  have ht : min (extendIccOrderIso ψ t) U = (ψ (clipIcc T t) : ℝ≥0) :=
    min_extendIccFun ψ t
  dsimp only
  rw [ht]
  have h := le_iSup (fun s : TimeInterval (T : ℝ≥0∞) =>
    edist (f s.1) (g (φ s).1)) ((timeIntervalOrderIso T).symm (clipIcc T t))
  simpa [ψ, timeIntervalOrderIso, clipIcc] using h


/-- Continuous finite prefixes and their constant-tail rays have the same distance. -/
theorem reparamEDist_stopped_eq_normalizedPrefixCurve {d : ℕ}
    (f g : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (T U : ℝ≥0) :
    ReparamEDist.reparamEDist (fun t => f (min t T)) (fun t => g (min t U)) =
      edist (normalizedPrefixCurve f T) (normalizedPrefixCurve g U) := by
  refine le_antisymm ?_ (normalizedPrefixCurve_edist_le_reparamEDist_stopped_all f g T U)
  by_cases hT : T = 0
  · subst T
    exact reparamEDist_stopped_zero_left_le f g U
  by_cases hU : U = 0
  · subst U
    exact reparamEDist_stopped_zero_right_le f g T
  · have hTpos : 0 < T := pos_iff_ne_zero.mpr hT
    have hUpos : 0 < U := pos_iff_ne_zero.mpr hU
    rw [← intervalEDist_eq_edist_normalizedPrefixCurve f g T U hTpos hUpos]
    exact reparamEDist_stopped_le_intervalEDist f g T U

end LatticeProb.StoppedRayIntervalDistance
