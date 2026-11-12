/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.PolygonRiemann at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped Interval

namespace LQGDimension.PolygonRiemannAux

variable (V : ℕ → ℂ) (m : ℕ)

/-- The affine parametrization of edge `i` (from `V i` to `V (i+1)`), defined on all of `ℝ`. -/
def edgeAff (i : ℕ) (t : ℝ) : ℂ := V i + (t * (m : ℝ) - (i : ℝ)) • (V (i + 1) - V i)

/-- The piecewise-linear path through `V 0, …, V m`. -/
def polyPath (t : ℝ) : ℂ := edgeAff V m ⌊t * (m : ℝ)⌋₊ t

/-- Segment parametrization by `s ∈ [0,1]`. -/
def segAff (i : ℕ) (s : ℝ) : ℂ := V i + (s : ℝ) • (V (i + 1) - V i)


/-- Key value-matching lemma. -/
theorem polyPath_eq_edgeAff (hm : 0 < m) (i : ℕ) (_hi : i < m) (t : ℝ)
    (ht : t ∈ Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m)) :
    polyPath V m t = edgeAff V m i t := by
  have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  obtain ⟨ht1, ht2⟩ := ht
  have h1 : (i:ℝ) ≤ t * m := (div_le_iff₀ hm').mp ht1
  have h2 : t * m ≤ (i:ℝ) + 1 := (le_div_iff₀ hm').mp ht2
  rcases lt_or_eq_of_le h2 with hlt | heq
  · have hfloor : ⌊t*(m:ℝ)⌋₊ = i := by
      rw [Nat.floor_eq_iff (by linarith : (0:ℝ) ≤ t*(m:ℝ))]
      exact ⟨h1, hlt⟩
    unfold polyPath
    rw [hfloor]
  · unfold polyPath
    have hfloor : ⌊t*(m:ℝ)⌋₊ = i+1 := by
      rw [Nat.floor_eq_iff (by linarith : (0:ℝ) ≤ t*(m:ℝ))]
      constructor
      · push_cast; linarith [heq]
      · push_cast; linarith [heq]
    rw [hfloor]
    unfold edgeAff
    have e0 : t*(m:ℝ) - (((i+1:ℕ):ℝ)) = 0 := by push_cast; linarith [heq]
    rw [e0, zero_smul, add_zero]
    have e1 : t*(m:ℝ) - (i:ℝ) = 1 := by linarith [heq]
    rw [e1, one_smul]
    ring

/-- `edgeAff` is smooth (affine) everywhere. -/
theorem hasDerivAt_edgeAff (i : ℕ) (t : ℝ) :
    HasDerivAt (edgeAff V m i) ((m:ℝ) • (V (i+1) - V i)) t := by
  have h1 : HasDerivAt (fun x : ℝ => x * (m:ℝ)) (m:ℝ) t := hasDerivAt_mul_const (m:ℝ)
  have h2 : HasDerivAt (fun x : ℝ => x * (m:ℝ) - (i:ℝ)) (m:ℝ) t := h1.sub_const (i:ℝ)
  have h3 : HasDerivAt (fun x : ℝ => (x * (m:ℝ) - (i:ℝ)) • (V (i+1) - V i))
      ((m:ℝ) • (V (i+1) - V i)) t := h2.smul_const (V (i+1) - V i)
  exact h3.const_add (V i)

/-- Continuity of `edgeAff`. -/
theorem continuous_edgeAff (i : ℕ) : Continuous (edgeAff V m i) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeAff V m i t).continuousAt

/-- On interior points of an edge, `polyPath` has the expected derivative. -/
theorem hasDerivAt_polyPath (hm : 0 < m) (i : ℕ) (hi : i < m) (t : ℝ)
    (ht : t ∈ Ioo ((i : ℝ) / m) (((i : ℝ) + 1) / m)) :
    HasDerivAt (polyPath V m) ((m:ℝ) • (V (i+1) - V i)) t := by
  have hnhd : Icc ((i:ℝ)/m) (((i:ℝ)+1)/m) ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have heq : (polyPath V m) =ᶠ[𝓝 t] (edgeAff V m i) :=
    Filter.eventuallyEq_of_mem hnhd (fun t' ht' => polyPath_eq_edgeAff V m hm i hi t' ht')
  exact (hasDerivAt_edgeAff V m i t).congr_of_eventuallyEq heq

/-- The edge index of `t`, clamped so that it always lies in `range m`. -/
def idx (m : ℕ) (t : ℝ) : ℕ := min ⌊t * (m:ℝ)⌋₊ (m-1)

theorem idx_lt (hm : 0 < m) (t : ℝ) : idx m t < m :=
  lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hm Nat.one_pos)

theorem mem_Icc_idx (hm : 0 < m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ∈ Icc ((idx m t:ℝ)/m) (((idx m t:ℝ)+1)/m) := by
  have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  unfold idx
  by_cases hle : ⌊t*(m:ℝ)⌋₊ ≤ m - 1
  · rw [min_eq_left hle]
    have hfl1 : (⌊t*(m:ℝ)⌋₊ : ℝ) ≤ t*(m:ℝ) := Nat.floor_le (by positivity)
    have hfl2 : t*(m:ℝ) < (⌊t*(m:ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    constructor
    · rw [div_le_iff₀ hm']; linarith
    · rw [le_div_iff₀ hm']; linarith
  · push Not at hle
    rw [min_eq_right hle.le]
    have hge : m ≤ ⌊t*(m:ℝ)⌋₊ := by omega
    have hge' : (m:ℝ) ≤ t*(m:ℝ) :=
      le_trans (by exact_mod_cast hge) (Nat.floor_le (by positivity))
    have ht1' : t = 1 := by nlinarith
    subst ht1'
    have hnat : (m-1)+1 = m := Nat.sub_add_cancel hm
    have hcast : ((m-1:ℕ):ℝ) + 1 = (m:ℝ) := by exact_mod_cast hnat
    constructor
    · rw [div_le_one hm']; linarith
    · rw [le_div_iff₀ hm', one_mul, hcast]

theorem iUnion_Icc_eq (hm : 0 < m) :
    (⋃ i : Fin m, Icc ((i:ℝ)/m) (((i:ℝ)+1)/m)) = Icc (0:ℝ) 1 := by
  have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  apply Set.Subset.antisymm
  · rintro t ht
    simp only [mem_iUnion] at ht
    obtain ⟨i, hti⟩ := ht
    have hi_nat : i.1 + 1 ≤ m := i.2
    have hi : (i:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hi_nat
    constructor
    · have : (0:ℝ) ≤ (i:ℝ)/m := by positivity
      linarith [hti.1]
    · have h2 : ((i:ℝ)+1)/m ≤ 1 := by rw [div_le_one hm']; linarith
      linarith [hti.2]
  · intro t ht
    exact Set.mem_iUnion.mpr ⟨⟨idx m t, idx_lt m hm t⟩, mem_Icc_idx m hm t ht.1 ht.2⟩

theorem continuousOn_polyPath (hm : 0 < m) : ContinuousOn (polyPath V m) (Icc (0:ℝ) 1) := by
  rw [← iUnion_Icc_eq m hm]
  refine (locallyFinite_of_finite (fun i : Fin m =>
      Icc ((i:ℝ)/m) (((i:ℝ)+1)/m))).continuousOn_iUnion
    (fun i => isClosed_Icc) (fun i => ?_)
  apply (continuous_edgeAff V m i).continuousOn.congr
  intro t ht
  exact polyPath_eq_edgeAff V m hm i i.2 t ht

theorem hab_lt (hm : 0 < m) (i : ℕ) : ((i:ℝ)/m) < (((i:ℝ)+1)/m) := by
  have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have e3 : (((i:ℝ)+1)/m) - ((i:ℝ)/m) = 1/(m:ℝ) := by field_simp; ring
  have hpos : (0:ℝ) < 1/(m:ℝ) := by positivity
  linarith [e3]

/-- Oscillation set of a continuous `φ` at scale `r` is bounded above. -/
theorem bddAbove_osc {φ : ℂ → ℝ} (hφ : Continuous φ) (r : ℝ) :
    BddAbove {x : ℝ | ∃ z w : ℂ, ‖z‖ ≤ 3 ∧ ‖w‖ ≤ 3 ∧ ‖z - w‖ ≤ r ∧ x = |φ z - φ w|} := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0:ℂ) 3).exists_bound_of_continuousOn hφ.continuousOn
  refine ⟨2*C, ?_⟩
  rintro x ⟨z, w, hz, hw, -, rfl⟩
  have h1 : ‖φ z‖ ≤ C := hC z (by simpa using hz)
  have h2 : ‖φ w‖ ≤ C := hC w (by simpa using hw)
  rw [Real.norm_eq_abs] at h1 h2
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  exact abs_le.mpr ⟨by linarith [h1'.1,h1'.2,h2'.1,h2'.2], by linarith [h1'.1,h1'.2,h2'.1,h2'.2]⟩

theorem le_osc {φ : ℂ → ℝ} (hφ : Continuous φ) {r : ℝ} {z w : ℂ}
    (hz : ‖z‖ ≤ 3) (hw : ‖w‖ ≤ 3) (hzw : ‖z - w‖ ≤ r) :
    |φ z - φ w| ≤ LQGDimension.Blueprint.Draft.osc φ r := by
  unfold LQGDimension.Blueprint.Draft.osc
  exact le_csSup (bddAbove_osc hφ r) ⟨z, w, hz, hw, hzw, rfl⟩

/-- The two edge formulas for the cost integrand agree except possibly at the right
endpoint of the edge's parameter interval. -/
theorem edge_congr_ae (φ : ℂ → ℝ) (ξ : ℝ) (hm : 0 < m) (i : ℕ) (hi : i < m) :
    ∀ᵐ t ∂ (volume : Measure ℝ),
      t ∈ Ι ((i:ℝ)/m) (((i:ℝ)+1)/m) →
        Real.exp (ξ * φ (polyPath V m t)) * ‖deriv (polyPath V m) t‖
          = Real.exp (ξ * φ (edgeAff V m i t)) * ‖(m:ℝ) • (V (i+1) - V i)‖ := by
  have hab : ((i:ℝ)/m) < (((i:ℝ)+1)/m) := hab_lt m hm i
  rw [uIoc_of_le hab.le, ae_iff]
  apply measure_mono_null (t := {(((i:ℝ)+1)/m)})
  · intro t ht
    simp only [Set.mem_ofPred_eq, not_imp, Set.mem_singleton_iff] at ht ⊢
    obtain ⟨htmem, hne⟩ := ht
    by_contra htne
    apply hne
    have htOoo : t ∈ Ioo ((i:ℝ)/m) (((i:ℝ)+1)/m) := ⟨htmem.1, lt_of_le_of_ne htmem.2 htne⟩
    have h1 : polyPath V m t = edgeAff V m i t :=
      polyPath_eq_edgeAff V m hm i hi t ⟨htOoo.1.le, htOoo.2.le⟩
    have h2 : HasDerivAt (polyPath V m) ((m:ℝ) • (V (i+1) - V i)) t :=
      hasDerivAt_polyPath V m hm i hi t htOoo
    rw [h1, h2.deriv]
  · exact measure_singleton _

/-- The cost integrand is interval integrable over each edge's parameter interval. -/
theorem intervalIntegrable_edge (φ : ℂ → ℝ) (hφ : Continuous φ) (ξ : ℝ) (hm : 0 < m) (i : ℕ)
    (hi : i < m) :
    IntervalIntegrable
      (fun t => Real.exp (ξ * φ (polyPath V m t)) * ‖deriv (polyPath V m) t‖) volume
      ((i:ℝ)/m) (((i:ℝ)+1)/m) := by
  have hgcont : Continuous
      (fun t => Real.exp (ξ * φ (edgeAff V m i t)) * ‖(m:ℝ) • (V (i+1) - V i)‖) :=
    (Real.continuous_exp.comp (continuous_const.mul (hφ.comp (continuous_edgeAff V m i)))).mul
      continuous_const
  have hae := edge_congr_ae V m φ ξ hm i hi
  exact (intervalIntegrable_congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae)).mpr
    (hgcont.intervalIntegrable _ _)

/-- The value of the edge integral, as a multiple of `‖V(i+1)-Vi‖`. -/
theorem lintegral_edge (φ : ℂ → ℝ) (ξ : ℝ) (hm : 0 < m) (i : ℕ) (hi : i < m) :
    (∫ t in ((i:ℝ)/m)..(((i:ℝ)+1)/m),
        Real.exp (ξ * φ (polyPath V m t)) * ‖deriv (polyPath V m) t‖)
      = ‖V (i+1) - V i‖ * ∫ s in (0:ℝ)..1, Real.exp (ξ * φ (segAff V i s)) := by
  have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  set a := (i:ℝ)/m with ha_def
  set b := ((i:ℝ)+1)/m with hb_def
  have hval : (∫ t in a..b, Real.exp (ξ * φ (polyPath V m t)) * ‖deriv (polyPath V m) t‖)
      = ∫ t in a..b, Real.exp (ξ * φ (edgeAff V m i t)) * ‖(m:ℝ) • (V (i+1) - V i)‖ :=
    intervalIntegral.integral_congr_ae (edge_congr_ae V m φ ξ hm i hi)
  have hgval : (∫ t in a..b, Real.exp (ξ * φ (edgeAff V m i t)) * ‖(m:ℝ) • (V (i+1) - V i)‖)
      = (∫ t in a..b, Real.exp (ξ * φ (edgeAff V m i t))) * ‖(m:ℝ) • (V (i+1) - V i)‖ :=
    intervalIntegral.integral_mul_const _ _
  have hkey : ∀ s : ℝ, edgeAff V m i (a + s/m) = segAff V i s := by
    intro s
    have hc : (a + s/m)*(m:ℝ) - (i:ℝ) = s := by rw [ha_def]; field_simp; ring
    unfold edgeAff segAff
    rw [hc]
  have hb_eq : a + 1/(m:ℝ) = b := by rw [ha_def, hb_def]; field_simp
  have hsub0 : (m:ℝ)⁻¹ • (∫ s in (0:ℝ)..1, Real.exp (ξ * φ (segAff V i s)))
      = ∫ t in a..b, Real.exp (ξ * φ (edgeAff V m i t)) := by
    have := intervalIntegral.inv_smul_integral_comp_add_div
      (fun s => Real.exp (ξ * φ (edgeAff V m i s)))
      (m:ℝ) a (a := (0:ℝ)) (b := (1:ℝ))
    simp only [hkey] at this
    rw [this]
    congr 2 <;> simp
  have hsub : (∫ t in a..b, Real.exp (ξ * φ (edgeAff V m i t)))
      = (1/(m:ℝ)) * ∫ s in (0:ℝ)..1, Real.exp (ξ * φ (segAff V i s)) := by
    rw [← hsub0, smul_eq_mul, one_div]
  rw [hval, hgval, hsub]
  have hnorm : ‖(m:ℝ) • (V (i+1) - V i)‖ = (m:ℝ) * ‖V (i+1) - V i‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hm'.le]
  rw [hnorm]
  field_simp

/-- `lfppLength` decomposes as a sum over edges. -/
theorem lfppLength_eq_sum (φ : ℂ → ℝ) (hφ : Continuous φ) (ξ : ℝ) (hm : 0 < m) :
    LQGDimension.lfppLength ξ φ (polyPath V m) =
      ∑ i ∈ Finset.range m,
        ‖V (i+1) - V i‖ * ∫ s in (0:ℝ)..1, Real.exp (ξ * φ (segAff V i s)) := by
  have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  show (∫ t in (0:ℝ)..1, Real.exp (ξ * φ (polyPath V m t)) * ‖deriv (polyPath V m) t‖) = _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i:ℕ => (i:ℝ)/m)
    (f := fun t => Real.exp (ξ * φ (polyPath V m t)) * ‖deriv (polyPath V m) t‖)
    (μ := volume) (n := m)
    (fun k hk => by simpa using intervalIntegrable_edge V m φ hφ ξ hm k hk)
  push_cast at hsum
  have h0 : (0:ℝ)/m = 0 := by norm_num
  have h1 : (m:ℝ)/m = 1 := by rw [div_self]; exact_mod_cast hm'.ne'
  rw [h0, h1] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_edge V m φ ξ hm i (Finset.mem_range.mp hi)

end LQGDimension.PolygonRiemannAux

namespace LQGDimension.PolygonRiemannAux

end LQGDimension.PolygonRiemannAux

namespace LQGDimension

end LQGDimension
