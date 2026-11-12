/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.PolygonRiemann at commit fdb5cad; only the module paths of local imports are changed. -/
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

theorem polyPath_mem_of_convex {S : Set ℂ} (hS : Convex ℝ S) (hm : 0 < m) (i : ℕ) (hi : i < m)
    (hVi : V i ∈ S) (hVi1 : V (i+1) ∈ S) (t : ℝ) (ht : t ∈ Icc ((i:ℝ)/m) (((i:ℝ)+1)/m)) :
    polyPath V m t ∈ S := by
  have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  obtain ⟨ht1, ht2⟩ := ht
  have h1 : (i:ℝ) ≤ t * m := (div_le_iff₀ hm').mp ht1
  have h2 : t * m ≤ (i:ℝ) + 1 := (le_div_iff₀ hm').mp ht2
  rw [polyPath_eq_edgeAff V m hm i hi t ⟨ht1, ht2⟩]
  set s := t*(m:ℝ) - (i:ℝ) with hs_def
  have hs0 : 0 ≤ s := by rw [hs_def]; linarith
  have hs1 : s ≤ 1 := by rw [hs_def]; linarith
  have hcombo : edgeAff V m i t = (1 - s) • V i + s • V (i+1) := by
    unfold edgeAff
    rw [← hs_def]
    module
  rw [hcombo]
  exact hS hVi hVi1 (by linarith) hs0 (by ring)

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

/-- Convexity of `U`. -/
theorem convex_U : Convex ℝ LQGDimension.U := by
  have hU : LQGDimension.U =
      ({c:ℂ | -2 < c.re} ∩ {c:ℂ | c.re < 2} ∩ {c:ℂ | -2 < c.im}) ∩ {c:ℂ | c.im < 2} := by
    ext z
    simp only [LQGDimension.U, Set.mem_ofPred_eq, Set.mem_inter_iff, abs_lt]
    tauto
  rw [hU]
  exact (((convex_halfSpace_re_gt (-2)).inter (convex_halfSpace_re_lt 2)).inter
    (convex_halfSpace_im_gt (-2))).inter (convex_halfSpace_im_lt 2)

/-- `U` is contained in the closed ball of radius `3`. -/
theorem norm_le_three_of_mem_U {z : ℂ} (hz : z ∈ LQGDimension.U) : ‖z‖ ≤ 3 := by
  obtain ⟨hre, him⟩ := hz
  rw [abs_lt] at hre him
  have h9 : ‖z‖ * ‖z‖ ≤ 9 := by
    rw [Complex.norm_mul_self_eq_normSq, Complex.normSq_apply]
    nlinarith [hre.1, hre.2, him.1, him.2]
  nlinarith [norm_nonneg z, h9, sq_nonneg (‖z‖ - 3)]

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

/-- The Riemann-sum bound for a single edge. -/
theorem riemann_bound_edge (φ : ℂ → ℝ) (hφ : Continuous φ) (ξ : ℝ) (hξ : 0 < ξ) (r : ℝ)
    (N : ℕ) (hN : 1 ≤ N) (i : ℕ)
    (hVi : V i ∈ LQGDimension.U) (hVi1 : V (i+1) ∈ LQGDimension.U)
    (hlen : ‖V (i+1) - V i‖ ≤ N * r) :
    (∫ s in (0:ℝ)..1, Real.exp (ξ * φ (segAff V i s)))
      ≤ Real.exp (ξ * LQGDimension.Blueprint.Draft.osc φ r) *
        ((1:ℝ)/N) * ∑ q ∈ Finset.range N, Real.exp (ξ * φ (segAff V i ((q:ℝ)/N))) := by
  have hN' : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hcombo : ∀ s:ℝ, segAff V i s = (1-s) • (V i) + s • (V (i+1)) := by
    intro s; unfold segAff; module
  have hball : ∀ s : ℝ, s ∈ Icc (0:ℝ) 1 → ‖segAff V i s‖ ≤ 3 := by
    intro s hs
    rw [hcombo s]
    have h1s : |1-s| = 1-s := abs_of_nonneg (by linarith [hs.2])
    have h2s : |s| = s := abs_of_nonneg hs.1
    calc ‖(1-s) • (V i) + s • (V (i+1))‖
        ≤ ‖(1-s) • (V i)‖ + ‖s • (V (i+1))‖ := norm_add_le _ _
      _ = |1-s| * ‖V i‖ + |s| * ‖V (i+1)‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (1-s)*3 + s*3 := by
          rw [h1s, h2s]
          gcongr <;> first
            | linarith [hs.1, hs.2]
            | exact norm_le_three_of_mem_U hVi
            | exact norm_le_three_of_mem_U hVi1
      _ = 3 := by ring
  have hcont : Continuous (fun s : ℝ => Real.exp (ξ * φ (segAff V i s))) := by
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    apply hφ.comp
    unfold segAff
    fun_prop
  have hdist : ∀ q : ℕ, q < N → ∀ s ∈ Icc ((q:ℝ)/N) (((q:ℝ)+1)/N),
      ‖segAff V i s - segAff V i ((q:ℝ)/N)‖ ≤ r := by
    intro q hq s hs
    have heq : segAff V i s - segAff V i ((q:ℝ)/N) = (s - (q:ℝ)/N) • (V (i+1) - V i) := by
      unfold segAff; module
    rw [heq, norm_smul, Real.norm_eq_abs]
    have hdiff : ((q:ℝ)+1)/N - (q:ℝ)/N = 1/(N:ℝ) := by field_simp; ring
    have hsb : |s - (q:ℝ)/N| ≤ 1/(N:ℝ) := by
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2, hdiff]
    calc |s-(q:ℝ)/N| * ‖V (i+1)-V i‖ ≤ (1/(N:ℝ)) * ((N:ℝ)*r) :=
          mul_le_mul hsb hlen (norm_nonneg _) (by positivity)
      _ = r := by field_simp
  have hstep : ∀ q : ℕ, q < N →
      (∫ s in ((q:ℝ)/N)..(((q:ℝ)+1)/N), Real.exp (ξ * φ (segAff V i s)))
        ≤ (1/(N:ℝ)) * (Real.exp (ξ * LQGDimension.Blueprint.Draft.osc φ r) *
            Real.exp (ξ * φ (segAff V i ((q:ℝ)/N)))) := by
    intro q hq
    have hqN : ((q:ℝ)/N) ≤ (((q:ℝ)+1)/N) := (hab_lt N hN q).le
    have hbound : ∀ s ∈ Icc ((q:ℝ)/N) (((q:ℝ)+1)/N),
        Real.exp (ξ * φ (segAff V i s)) ≤
          Real.exp (ξ * LQGDimension.Blueprint.Draft.osc φ r) *
            Real.exp (ξ * φ (segAff V i ((q:ℝ)/N))) := by
      intro s hs
      have hsI : s ∈ Icc (0:ℝ) 1 := by
        constructor
        · have h0 : (0:ℝ) ≤ (q:ℝ)/N := by positivity
          linarith [hs.1]
        · have h1 : (((q:ℝ)+1)/N) ≤ 1 := by
            rw [div_le_one hN']
            have hcast : q+1 ≤ N := hq
            exact_mod_cast hcast
          linarith [hs.2]
      have hqI : ((q:ℝ)/N) ∈ Icc (0:ℝ) 1 := by
        constructor
        · positivity
        · rw [div_le_one hN']; exact_mod_cast hq.le
      have hzs : ‖segAff V i s‖ ≤ 3 := hball s hsI
      have hzq : ‖segAff V i ((q:ℝ)/N)‖ ≤ 3 := hball _ hqI
      have hzw : ‖segAff V i s - segAff V i ((q:ℝ)/N)‖ ≤ r := hdist q hq s hs
      have hphi := le_osc hφ hzs hzq hzw
      have hphi' : φ (segAff V i s) ≤
          φ (segAff V i ((q:ℝ)/N)) + LQGDimension.Blueprint.Draft.osc φ r := by
        have := (abs_le.mp hphi).2; linarith
      calc Real.exp (ξ * φ (segAff V i s))
          ≤ Real.exp (ξ * (φ (segAff V i ((q:ℝ)/N)) +
              LQGDimension.Blueprint.Draft.osc φ r)) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hphi' hξ.le)
        _ = Real.exp (ξ * LQGDimension.Blueprint.Draft.osc φ r) *
              Real.exp (ξ * φ (segAff V i ((q:ℝ)/N))) := by
            rw [mul_add, Real.exp_add]; ring
    calc (∫ s in ((q:ℝ)/N)..(((q:ℝ)+1)/N), Real.exp (ξ * φ (segAff V i s)))
        ≤ ∫ _s in ((q:ℝ)/N)..(((q:ℝ)+1)/N),
            Real.exp (ξ * LQGDimension.Blueprint.Draft.osc φ r) *
              Real.exp (ξ * φ (segAff V i ((q:ℝ)/N))) :=
          intervalIntegral.integral_mono_on hqN (hcont.intervalIntegrable _ _)
            intervalIntegrable_const hbound
      _ = (1/(N:ℝ)) * (Real.exp (ξ * LQGDimension.Blueprint.Draft.osc φ r) *
            Real.exp (ξ * φ (segAff V i ((q:ℝ)/N)))) := by
          rw [intervalIntegral.integral_const]
          have hdiff : ((q:ℝ)+1)/N - (q:ℝ)/N = 1/(N:ℝ) := by field_simp; ring
          rw [hdiff, smul_eq_mul]
  have hsplit : (∫ s in (0:ℝ)..1, Real.exp (ξ * φ (segAff V i s)))
      = ∑ q ∈ Finset.range N,
          ∫ s in ((q:ℝ)/N)..(((q:ℝ)+1)/N), Real.exp (ξ * φ (segAff V i s)) := by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun q:ℕ => (q:ℝ)/N) (f := fun s => Real.exp (ξ * φ (segAff V i s)))
      (μ := volume) (n := N) (fun k _ => hcont.intervalIntegrable _ _)
    push_cast at hsum
    have h0 : (0:ℝ)/N = 0 := by norm_num
    have h1 : (N:ℝ)/N = 1 := by rw [div_self]; exact_mod_cast hN'.ne'
    rw [h0, h1] at hsum
    exact hsum.symm
  rw [hsplit]
  calc ∑ q ∈ Finset.range N, ∫ s in ((q:ℝ)/N)..(((q:ℝ)+1)/N), Real.exp (ξ * φ (segAff V i s))
      ≤ ∑ q ∈ Finset.range N, (1/(N:ℝ)) * (Real.exp (ξ * LQGDimension.Blueprint.Draft.osc φ r) *
          Real.exp (ξ * φ (segAff V i ((q:ℝ)/N)))) :=
        Finset.sum_le_sum (fun q hq => hstep q (Finset.mem_range.mp hq))
    _ = Real.exp (ξ * LQGDimension.Blueprint.Draft.osc φ r) * (1/(N:ℝ)) *
          ∑ q ∈ Finset.range N, Real.exp (ξ * φ (segAff V i ((q:ℝ)/N))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring

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

/-- `polyPath` is an admissible path when its vertices lie in `U` with the right endpoints. -/
theorem isAdmissiblePath_polyPath (hm : 0 < m) (hV0 : V 0 = 0) (hVm : V m = 1)
    (hVU : ∀ i ≤ m, V i ∈ LQGDimension.U) :
    LQGDimension.IsAdmissiblePath (polyPath V m) := by
  have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h00 : (0:ℝ) ∈ Icc ((0:ℝ)/m) (((0:ℝ)+1)/m) := ⟨by norm_num, by positivity⟩
    have h0eq : polyPath V m 0 = edgeAff V m 0 0 := by
      have := polyPath_eq_edgeAff V m hm 0 hm 0 (by simpa using h00)
      simpa using this
    rw [h0eq]
    unfold edgeAff
    simp [hV0]
  · have hcast : ((m-1:ℕ):ℝ) + 1 = (m:ℝ) := by
      have hnat : (m-1)+1 = m := Nat.sub_add_cancel hm
      exact_mod_cast hnat
    have hlast : (1:ℝ) ∈ Icc (((m-1:ℕ):ℝ)/m) ((((m-1:ℕ):ℝ)+1)/m) := by
      rw [hcast]
      refine ⟨?_, by rw [div_self hm'.ne']⟩
      rw [div_le_one hm']
      have := Nat.sub_le m 1
      exact_mod_cast this
    have hm1lt : m - 1 < m := Nat.sub_lt hm Nat.one_pos
    have h11 : polyPath V m 1 = edgeAff V m (m-1) 1 :=
      polyPath_eq_edgeAff V m hm (m-1) hm1lt 1 hlast
    rw [h11]
    unfold edgeAff
    have hstep : (1:ℝ)*(m:ℝ) - ((m-1:ℕ):ℝ) = 1 := by rw [← hcast]; ring
    rw [hstep, one_smul]
    have hnat2 : m - 1 + 1 = m := Nat.sub_add_cancel hm
    rw [hnat2, hVm]
    ring
  · intro t ht
    have hidx : idx m t < m := idx_lt m hm t
    have hmem : t ∈ Icc ((idx m t:ℝ)/m) (((idx m t:ℝ)+1)/m) := mem_Icc_idx m hm t ht.1 ht.2
    exact polyPath_mem_of_convex V m convex_U hm (idx m t) hidx
      (hVU (idx m t) hidx.le) (hVU (idx m t + 1) hidx) t hmem
  · exact continuousOn_polyPath V m hm
  · refine ⟨m, fun j => (j:ℝ)/m, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : (a:ℝ) < (b:ℝ) := by exact_mod_cast hab
      have hdiff : (b:ℝ)/m - (a:ℝ)/m = ((b:ℝ)-(a:ℝ))/m := by ring
      have hpos : (0:ℝ) < ((b:ℝ)-(a:ℝ))/m := div_pos (by linarith) hm'
      linarith [hdiff, hpos]
    · simp
    · show ((Fin.last m : Fin (m+1)):ℝ)/m = 1
      rw [Fin.val_last]
      exact div_self hm'.ne'
    · intro i
      have hcd : ContDiff ℝ 1 (edgeAff V m i) := by unfold edgeAff; fun_prop
      have heq1 : (fun j : Fin (m+1) => (j:ℝ)/m) i.castSucc = (i:ℝ)/m := by
        simp
      have heq2 : (fun j : Fin (m+1) => (j:ℝ)/m) i.succ = ((i:ℝ)+1)/m := by
        simp
      rw [heq1, heq2]
      apply (hcd.contDiffOn (s := Icc ((i:ℝ)/m) (((i:ℝ)+1)/m))).congr
      intro t ht
      exact polyPath_eq_edgeAff V m hm i i.2 t ht

end LQGDimension.PolygonRiemannAux

namespace LQGDimension.PolygonRiemannAux

/-- Conversion between a `Finset.range` sum and the sum of a `List.range`-indexed list. -/
theorem finset_sum_range_eq_list_sum {β : Type*} [AddCommMonoid β] (n : ℕ) (g : ℕ → β) :
    ∑ i ∈ Finset.range n, g i = ((List.range n).map g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]
    simp

/-- `edges z` is, as a list, the range-indexed list of consecutive vertex pairs. -/
theorem edges_eq_range_map (z : List ℂ) :
    LQGDimension.Blueprint.Draft.edges z =
      (List.range (z.length - 1)).map
        (fun i => (z.getD i (0:ℂ), z.getD (i+1) (0:ℂ))) := by
  apply List.ext_getElem?
  intro n
  by_cases hn : n < z.length - 1
  · have h1 : n < z.length := by omega
    have h1' : n + 1 < z.length := by omega
    have hz_n : z[n]? = some (z.getD n 0) :=
      List.getElem?_eq_some_iff.mpr ⟨h1, List.getElem_eq_getD (h := h1) 0⟩
    have hz_n1 : z[n+1]? = some (z.getD (n+1) 0) :=
      List.getElem?_eq_some_iff.mpr ⟨h1', List.getElem_eq_getD (h := h1') 0⟩
    have hzip : (LQGDimension.Blueprint.Draft.edges z)[n]? = some (z.getD n 0, z.getD (n+1) 0) := by
      show (z.zip z.tail)[n]? = _
      rw [List.getElem?_zip_eq_some]
      refine ⟨hz_n, ?_⟩
      rw [List.getElem?_tail]
      exact hz_n1
    have hrange : ((List.range (z.length - 1)).map
        (fun i => (z.getD i (0:ℂ), z.getD (i+1) (0:ℂ))))[n]? =
        some (z.getD n 0, z.getD (n+1) 0) := by
      rw [List.getElem?_map, List.getElem?_range hn]
      simp
    rw [hzip, hrange]
  · push Not at hn
    have hlen1 : (LQGDimension.Blueprint.Draft.edges z).length = z.length - 1 := by
      show (z.zip z.tail).length = z.length - 1
      rw [List.length_zip, List.length_tail]
      omega
    have hlen2 : ((List.range (z.length - 1)).map
        (fun i => (z.getD i (0:ℂ), z.getD (i+1) (0:ℂ)))).length = z.length - 1 := by
      simp
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- **Node `PR`.** -/
theorem polygonRiemannBound_proof : LQGDimension.Blueprint.Draft.PolygonRiemannBound := by
  intro ξ hξ z N r hN hz0 hz1 hzU hlenE φ hφ
  set V : ℕ → ℂ := fun i => z.getD i 0 with hV_def
  set m := z.length - 1 with hm_def
  have hne : z ≠ [] := by intro h; rw [h] at hz0; simp at hz0
  have hlen1 : 1 ≤ z.length := List.length_pos_iff.mpr hne
  have hm : 0 < m := by
    by_contra hc
    push Not at hc
    have hz1len : z.length = 1 := by omega
    have heq : z.head? = z.getLast? := by
      rw [List.head?_eq_getElem?, List.getLast?_eq_getElem?, hz1len]
    rw [hz0, hz1] at heq
    exact absurd (Option.some.inj heq) (by norm_num)
  have hz0' : z[0]? = some (0:ℂ) := by rw [← List.head?_eq_getElem?]; exact hz0
  have hV0 : V 0 = 0 := by
    show z.getD 0 0 = 0
    rw [List.getD_eq_getElem?_getD, hz0']
    rfl
  have hzm' : z[m]? = some (1:ℂ) := by
    have : z[m]? = z.getLast? := (List.getLast?_eq_getElem? (l := z)).symm
    rw [this, hz1]
  have hVm : V m = 1 := by
    show z.getD m 0 = 1
    rw [List.getD_eq_getElem?_getD, hzm']
    rfl
  have hVmem : ∀ i, i < z.length → V i ∈ z := by
    intro i hi
    show z.getD i 0 ∈ z
    rw [← List.getElem_eq_getD (h := hi) 0]
    exact List.getElem_mem hi
  have hVU : ∀ i ≤ m, V i ∈ LQGDimension.U := by
    intro i hi
    exact hzU (V i) (hVmem i (by omega))
  have hVedge : ∀ i, i < m → ‖V (i+1) - V i‖ ≤ N * r := by
    intro i hi
    have hmem : (V i, V (i+1)) ∈ LQGDimension.Blueprint.Draft.edges z := by
      rw [edges_eq_range_map z]
      exact List.mem_map_of_mem (List.mem_range.mpr hi)
    exact hlenE (V i, V (i+1)) hmem
  have hAdm : LQGDimension.IsAdmissiblePath (polyPath V m) :=
    isAdmissiblePath_polyPath V m hm hV0 hVm hVU
  have hBdd : BddBelow (Set.range (fun γ' : {γ // LQGDimension.IsAdmissiblePath γ} =>
      LQGDimension.lfppLength ξ φ γ'.1)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨γ', rfl⟩
    show (0:ℝ) ≤ ∫ t in (0:ℝ)..1, Real.exp (ξ * φ (γ'.1 t)) * ‖deriv γ'.1 t‖
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t _
    positivity
  have hle : LQGDimension.lfppDistance ξ φ ≤ LQGDimension.lfppLength ξ φ (polyPath V m) :=
    ciInf_le hBdd ⟨polyPath V m, hAdm⟩
  have hsum_eq := lfppLength_eq_sum V m φ hφ ξ hm
  have hsum_le : (∑ i ∈ Finset.range m,
        ‖V (i+1) - V i‖ * ∫ s in (0:ℝ)..1, Real.exp (ξ * φ (segAff V i s)))
      ≤ ∑ i ∈ Finset.range m, ‖V (i+1) - V i‖ *
          (Real.exp (ξ * LQGDimension.Blueprint.Draft.osc φ r) * (1/(N:ℝ)) *
            ∑ q ∈ Finset.range N, Real.exp (ξ * φ (segAff V i ((q:ℝ)/N)))) := by
    apply Finset.sum_le_sum
    intro i hi
    have hilt := Finset.mem_range.mp hi
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact riemann_bound_edge V φ hφ ξ hξ r N hN i
      (hVU i hilt.le) (hVU (i+1) hilt) (hVedge i hilt)
  have hcost_eq : LQGDimension.Blueprint.Draft.riemannCost ξ N z φ =
      ∑ i ∈ Finset.range m, ‖V (i+1) - V i‖ * ((1:ℝ)/N) *
        ∑ q ∈ Finset.range N, Real.exp (ξ * φ (segAff V i ((q:ℝ)/N))) := by
    unfold LQGDimension.Blueprint.Draft.riemannCost
    rw [edges_eq_range_map z, List.map_map]
    rw [← finset_sum_range_eq_list_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Function.comp_apply, hV_def]
    push_cast
    have harg : ∀ q : ℕ,
        z.getD i (0:ℂ) + (q:ℂ)/(N:ℂ) * (z.getD (i+1) (0:ℂ) - z.getD i (0:ℂ))
          = segAff (fun j => z.getD j (0:ℂ)) i ((q:ℝ)/N) := by
      intro q
      unfold segAff
      rw [Complex.real_smul]
      push_cast
      ring
    simp only [harg]
  calc LQGDimension.lfppDistance ξ φ
      ≤ LQGDimension.lfppLength ξ φ (polyPath V m) := hle
    _ = ∑ i ∈ Finset.range m,
        ‖V (i+1) - V i‖ * ∫ s in (0:ℝ)..1, Real.exp (ξ * φ (segAff V i s)) := hsum_eq
    _ ≤ ∑ i ∈ Finset.range m, ‖V (i+1) - V i‖ *
          (Real.exp (ξ * LQGDimension.Blueprint.Draft.osc φ r) * (1/(N:ℝ)) *
            ∑ q ∈ Finset.range N, Real.exp (ξ * φ (segAff V i ((q:ℝ)/N)))) := hsum_le
    _ = Real.exp (ξ * LQGDimension.Blueprint.Draft.osc φ r) *
          ∑ i ∈ Finset.range m, ‖V (i+1) - V i‖ * ((1:ℝ)/N) *
            ∑ q ∈ Finset.range N, Real.exp (ξ * φ (segAff V i ((q:ℝ)/N))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = Real.exp (ξ * LQGDimension.Blueprint.Draft.osc φ r) *
          LQGDimension.Blueprint.Draft.riemannCost ξ N z φ := by rw [hcost_eq]

end LQGDimension.PolygonRiemannAux

namespace LQGDimension

/-- **Node `PR`.** A polygon from `0` to `1` in `U` is an admissible path, and its LFPP
length is at most `e^{ξ ω}` times its Riemann cost, `ω` the oscillation at the Riemann
spacing. -/
theorem polygonRiemannBound : Blueprint.Draft.PolygonRiemannBound :=
  PolygonRiemannAux.polygonRiemannBound_proof

end LQGDimension
