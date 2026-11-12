/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasE4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE3

/-!
# Leftmost geodesics through a point, as a Borel condition on Polish witnesses
(task P2-E3d, decision D65 (ii))

GM = Gwynne–Miller, arXiv:1905.00383v3; leftmost geodesics as in `Blueprint.IsSideGeod`
(CONF Lemma 2.4 reading). Own descriptive-set-theory argument (GM do not discuss measurability).

`gmE_hit_iff`: for `d ∈ lenSet`, "some leftmost `d`-geodesic `P` from `𝕫` to `y ∈ ∂𝓑^•_t`
passes through `x`" iff there is a witness
`(η, (φ, ψ), t₀, (tₙ, ηₙ)ₙ, v) ∈ C([0,1],ℂ) × (C(𝕋,ℂ) × C(𝕋,ℝ)) × ℝ × (ℕ → ℝ × C([0,1],ℂ)) × [0,1]`
satisfying the Borel condition `gmHitF` (`P = η(·/t)`, `Pₙ = ηₙ(·/t)`, the Jordan
parametrization `φ(· mod 2π)` with angle lift `t + ψ(t mod 2π)`, `x = η(v)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

local notation "𝕋" => AddCircle (2 * Real.pi)

/-- a dense sequence of `[0,1]` -/
def gmDI : ℕ → unitInterval := TopologicalSpace.denseSeq unitInterval

/-- `η ∈ C([0,1], ℂ)` is a constant-speed `d`-geodesic from `𝕫` to `y` of length `t`,
countable form -/
def gmGeoF (d : ContMetric) (t : ℝ) (𝕫 y : ℂ) (η : C(unitInterval, ℂ)) : Prop :=
  0 ≤ t ∧ η 0 = 𝕫 ∧ η 1 = y ∧
    ∀ a b : ℕ, d.1 (η (gmDI a), η (gmDI b)) = t * |((gmDI b : unitInterval) : ℝ) - gmDI a|

lemma gmE_geo_to {d : ContMetric} {P : ℝ → ℂ} {t : ℝ} {𝕫 y : ℂ} (hP : IsGeodesicL d P t 𝕫 y) :
    ∃ η : C(unitInterval, ℂ), gmGeoF d t 𝕫 y η ∧ ∀ v : unitInterval, η v = P (t * v) := by
  have hc := gm_geodL_continuousOn hP
  have hm : ∀ v : unitInterval, t * (v : ℝ) ∈ Icc 0 t := fun v =>
    ⟨mul_nonneg hP.1 v.2.1, mul_le_of_le_one_right hP.1 v.2.2⟩
  refine ⟨⟨fun v => P (t * v), hc.comp_continuous (by fun_prop) hm⟩, ⟨hP.1, ?_, ?_, ?_⟩,
    fun v => rfl⟩
  · simp [hP.2.1]
  · simp [hP.2.2.1]
  · intro a b
    simp only [ContinuousMap.coe_mk]
    rw [hP.2.2.2 _ (hm _) _ (hm _), ← mul_sub, abs_mul, abs_of_nonneg hP.1]

lemma gmE_geo_all {d : ContMetric} {t : ℝ} {𝕫 y : ℂ} {η : C(unitInterval, ℂ)}
    (h : gmGeoF d t 𝕫 y η) (a b : unitInterval) :
    d.1 (η a, η b) = t * |(b : ℝ) - a| := by
  refine (TopologicalSpace.denseRange_denseSeq unitInterval).induction_on₂
    (p := fun a b : unitInterval => d.1 (η a, η b) = t * |(b : ℝ) - a|) ?_ h.2.2.2 a b
  exact isClosed_eq (continuous_contMetric_apply.comp (continuous_const.prodMk
    ((η.continuous.comp continuous_fst).prodMk (η.continuous.comp continuous_snd))))
    (continuous_const.mul ((continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst)).abs)

lemma gmE_pj_div {t : ℝ} (ht : 0 < t) (v : unitInterval) : pj (t * v / t) = v := by
  rw [mul_div_cancel_left₀ _ ht.ne']
  exact Set.projIcc_val zero_le_one v

lemma gmE_geo_of {d : ContMetric} {t : ℝ} {𝕫 y : ℂ} {η : C(unitInterval, ℂ)} (ht : 0 < t)
    (h : gmGeoF d t 𝕫 y η) : IsGeodesicL d (fun u => η (pj (u / t))) t 𝕫 y := by
  refine ⟨ht.le, ?_, ?_, fun a ha b hb => ?_⟩
  · simp only [zero_div, pjPath_zero, h.2.1]
  · simp only [div_self ht.ne', pjPath_one, h.2.2.1]
  · rw [gmE_geo_all h, pj_coe_of_mem ⟨div_nonneg ha.1 ht.le, (div_le_one ht).2 ha.2⟩,
      pj_coe_of_mem ⟨div_nonneg hb.1 ht.le, (div_le_one ht).2 hb.2⟩, ← sub_div, abs_div, abs_of_pos ht, mul_div_cancel₀ _ ht.ne']

lemma gmE_pos_of_mem_frontier {d : ContMetric} {𝕫 y : ℂ} {t : ℝ}
    (hy : y ∈ frontier (filledBall d 𝕫 t)) : 0 < t := by
  by_contra ht
  have hb : ballM d 𝕫 t = ∅ := eq_empty_iff_forall_notMem.2 fun w hw => by
    have h0 : 0 ≤ d.1 (𝕫, w) := @dist_nonneg d.Space _ 𝕫 w
    exact ht (h0.trans_lt hw)
  have hK : filledBall d 𝕫 t = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
    simp only [filledBall, hb, closure_empty, compl_empty, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ, mem_union, notMem_empty, mem_ofPred_eq,
      not_false_eq_true, true_and, false_or] at hx
    exact NormedSpace.unbounded_univ ℝ ℂ hx
  rw [hK, frontier_empty] at hy
  exact hy

/-- the witness space -/
abbrev GMHitW : Type :=
  C(unitInterval, ℂ) × (C(𝕋, ℂ) × C(𝕋, ℝ)) × ℝ × (ℕ → ℝ × C(unitInterval, ℂ)) × unitInterval

/-- the Borel condition on `(d, t, y, x)` and a witness -/
def gmHitF (d : ContMetric) (𝕫 : ℂ) (t : ℝ) (y x : ℂ) (w : GMHitW) : Prop :=
  gmFrF d 𝕫 t y ∧ gmGeoF d t 𝕫 y w.1 ∧ gmJordF d 𝕫 t w.2.1.1 w.2.1.2 ∧
    w.2.1.1 (w.2.2.1 : 𝕋) = y ∧
    Tendsto (fun n => dist (w.2.2.2.1 n).1 w.2.2.1) atTop (𝓝 0) ∧
    (∀ n, w.2.2.1 < (w.2.2.2.1 n).1) ∧
    (∀ n, gmGeoF d t 𝕫 (w.2.1.1 ((w.2.2.2.1 n).1 : 𝕋)) (w.2.2.2.1 n).2) ∧
    Tendsto (fun n => dist (w.2.2.2.1 n).2 w.1) atTop (𝓝 0) ∧ w.1 w.2.2.2.2 = x

/-- **leftmost geodesics through a point, with Polish witnesses** -/
theorem gmE_hit_iff {d : ContMetric} (hd : d ∈ lenSet) (𝕫 : ℂ) (t : ℝ) (y x : ℂ) :
    (∃ P, IsLeftmostGeod d 𝕫 t y P ∧ ∃ u ∈ Icc 0 t, P u = x) ↔ ∃ w, gmHitF d 𝕫 t y x w := by
  constructor
  · rintro ⟨P, ⟨hy, hP, φ, hJ, t₀, hφ₀, tn, Pn, htn, hlt, hPn, hconv⟩, u, hu, rfl⟩
    have ht := gmE_pos_of_mem_frontier hy
    obtain ⟨η, hη, hηP⟩ := gmE_geo_to hP
    choose ηn hηn hηnP using fun n => gmE_geo_to (hPn n)
    obtain ⟨φ', ψ, hφ', hJC⟩ := (gmE_isPosJordanParam_iff _ _ _).1 hJ
    have hv : u / t ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hu.1 ht.le, (div_le_one ht).2 hu.2⟩
    refine ⟨(η, (φ', ψ), t₀, fun n => (tn n, ηn n), ⟨u / t, hv⟩),
      (gmE_mem_frontier_iff hd _ _ _).1 hy, hη, (gmE_jordanC_iff hd _ _ _ _).1 hJC,
      by rw [hφ', hφ₀], (tendsto_iff_dist_tendsto_zero).1 htn, fun n => by simpa using hlt n,
      fun n => by rw [hφ']; exact hηn n, ?_, ?_⟩
    · refine (tendsto_iff_dist_tendsto_zero).1 (Metric.tendsto_atTop.2 fun ε hε => ?_)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (ENNReal.tendsto_nhds_zero.1 hconv _
        (ENNReal.ofReal_pos.2 (half_pos hε)))
      refine ⟨N, fun n hn => ?_⟩
      refine lt_of_le_of_lt ((ContinuousMap.dist_le (half_pos hε).le).2 fun v => ?_)
        (half_lt_self hε)
      rw [hηnP, hηP, ← edist_le_ofReal (half_pos hε).le]
      refine le_trans ?_ (hN n hn)
      exact le_iSup₂ (f := fun s (_ : s ∈ Icc 0 t) => edist (Pn n s) (P s)) (t * v)
        ⟨mul_nonneg ht.le v.2.1, mul_le_of_le_one_right ht.le v.2.2⟩
    · simp only [hηP]
      congr 1
      field_simp
  · rintro ⟨⟨η, ⟨φ', ψ⟩, t₀, sq, v⟩, hy, hη, hJ, hφ₀, htn, hlt, hPn, hconv, rfl⟩
    have hy' := (gmE_mem_frontier_iff hd _ _ _).2 hy
    have ht := gmE_pos_of_mem_frontier hy'
    refine ⟨fun u => η (pj (u / t)), ⟨hy', gmE_geo_of ht hη, fun s => φ' (s : 𝕋),
      (gmE_isPosJordanParam_iff _ _ _).2 ⟨φ', ψ, fun _ => rfl, (gmE_jordanC_iff hd _ _ _ _).2 hJ⟩,
      t₀, hφ₀, fun n => (sq n).1, fun n u => (sq n).2 (pj (u / t)),
      (tendsto_iff_dist_tendsto_zero).2 htn, fun n => by simpa using hlt n,
      fun n => gmE_geo_of ht (hPn n), ?_⟩, t * v, ⟨mul_nonneg ht.le v.2.1,
      mul_le_of_le_one_right ht.le v.2.2⟩, by simp only [gmE_pj_div ht]⟩
    have hc := (tendsto_iff_edist_tendsto_0).1 ((tendsto_iff_dist_tendsto_zero).2 hconv)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => bot_le)
      fun n => iSup₂_le fun s _ => ?_
    rw [edist_dist, edist_dist]
    exact ENNReal.ofReal_le_ofReal (ContinuousMap.dist_apply_le_dist _)

end LQGMetric.GM
