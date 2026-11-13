/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Planar.ArcUnion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Jordan.Complex

/-!
# A Jordan curve made from two arcs

This is the arc-union lemma needed with the Jordan and Schoenflies ports. The proof glues the two
arc parametrizations along the upper and lower semicircles, then transports the resulting circle
embedding through `Jordan.Arcs.complexLIE` to the complex unit circle.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRTHarmonic.Planar.ArcUnion

open Set Topology Function

abbrev Plane := Jordan.Arcs.Plane

/-- The unit circle in the real plane used by the Jordan port. -/
abbrev Circle1 := Metric.sphere (0 : Plane) 1

/-- First coordinate on the unit circle. -/
noncomputable def cx (z : Circle1) : ℝ := (z : EuclideanSpace ℝ (Fin 2)) 0

/-- Second coordinate on the unit circle. -/
noncomputable def cy (z : Circle1) : ℝ := (z : EuclideanSpace ℝ (Fin 2)) 1

lemma continuous_cx : Continuous cx :=
  (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.comp
    continuous_subtype_val

lemma continuous_cy : Continuous cy :=
  (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.comp
    continuous_subtype_val

lemma cx_sq_add_cy_sq (z : Circle1) : cx z ^ 2 + cy z ^ 2 = 1 := by
  have h := z.2
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.sqrt_eq_one] at h
  simpa [cx, cy, Real.norm_eq_abs, sq_abs] using h

lemma circle_ext {z w : Circle1} (h0 : cx z = cx w) (h1 : cy z = cy w) : z = w := by
  apply Subtype.ext
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- The point `(x,y)` of the unit circle. -/
noncomputable def pt (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) : Circle1 :=
  ⟨!₂[x, y], by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs, h]⟩

@[simp] lemma cx_pt (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) : cx (pt x y h) = x := by
  simp [cx, pt]

@[simp] lemma cy_pt (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) : cy (pt x y h) = y := by
  simp [cy, pt]

lemma neg_one_le_cx (z : Circle1) : -1 ≤ cx z := by
  nlinarith [cx_sq_add_cy_sq z, sq_nonneg (cy z)]

lemma cx_le_one (z : Circle1) : cx z ≤ 1 := by
  nlinarith [cx_sq_add_cy_sq z, sq_nonneg (cy z)]

/-- The parameter `(1 - x) / 2` of a point on the unit circle. -/
noncomputable def par (z : Circle1) : unitInterval :=
  ⟨(1 - cx z) / 2, by constructor <;> linarith [neg_one_le_cx z, cx_le_one z]⟩

lemma continuous_par : Continuous par :=
  ((continuous_const.sub continuous_cx).div_const 2).subtype_mk _

lemma par_eq_zero_iff (z : Circle1) : par z = 0 ↔ cx z = 1 := by
  rw [← Subtype.coe_inj]
  simp only [par, Set.Icc.coe_zero]
  constructor <;> intro h <;> linarith

lemma par_eq_one_iff (z : Circle1) : par z = 1 ↔ cx z = -1 := by
  rw [← Subtype.coe_inj]
  simp only [par, Set.Icc.coe_one]
  constructor <;> intro h <;> linarith

lemma cy_eq_zero_of_cx {z : Circle1} (h : cx z = 1 ∨ cx z = -1) : cy z = 0 := by
  have hz := cx_sq_add_cy_sq z
  rcases h with h | h <;> rw [h] at hz <;> nlinarith [sq_nonneg (cy z)]

lemma cx_eq_of_cy_eq_zero {z : Circle1} (h : cy z = 0) : cx z = 1 ∨ cx z = -1 := by
  have hz := cx_sq_add_cy_sq z
  rw [h] at hz
  have h₂ : (cx z - 1) * (cx z + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h₂ with h₁ | h₁
  · left
    linarith
  · right
    linarith

/-- The union of two simple arcs with the same endpoints and no other common points is a Jordan
curve. The hypotheses give continuous injective parametrizations of the arcs, and the intersection
condition is expressed directly on their ranges. -/
theorem jordanCurve_union_of_arcs {a b : unitInterval → ℂ}
    (ha : Continuous a) (ha_inj : Injective a) (hb : Continuous b) (hb_inj : Injective b)
    (h₀ : a 0 = b 0) (h₁ : a 1 = b 1)
    (hAB : range a ∩ range b = {a 0, a 1}) :
    LQGMetric.JordanMap.IsJordanCurve (range a ∪ range b) := by
  have hbd : ∀ z : Circle1, cy z = 0 → a (par z) = b (par z) := by
    intro z hz
    rcases cx_eq_of_cy_eq_zero hz with h | h
    · rw [(par_eq_zero_iff z).mpr h, h₀]
    · rw [(par_eq_one_iff z).mpr h, h₁]
  obtain ⟨f, hf, hinj, hrange⟩ :
      ∃ f : Circle1 → ℂ, Continuous f ∧ Injective f ∧ range f = range a ∪ range b := by
    refine ⟨fun z => if 0 ≤ cy z then a (par z) else b (par z), ?_, ?_, ?_⟩
    · exact continuous_if_le continuous_const continuous_cy (ha.comp continuous_par).continuousOn
        (hb.comp continuous_par).continuousOn fun z hz => hbd z hz.symm
    · have hpar : ∀ z w : Circle1, par z = par w → cx z = cx w := by
        intro z w h
        have h' := congrArg Subtype.val h
        simp only [par] at h'
        linarith
      have hmixed : ∀ z w : Circle1, a (par z) = b (par w) → cy z = 0 ∧ cy w = 0 := by
        intro z w h
        have hmem : a (par z) ∈ range a ∩ range b :=
          ⟨mem_range_self _, h ▸ mem_range_self _⟩
        rw [hAB] at hmem
        rcases hmem with hp | hq
        · have hz : par z = 0 := ha_inj hp
          have hw : par w = 0 := hb_inj (h.symm.trans (hp.trans h₀))
          exact ⟨cy_eq_zero_of_cx (Or.inl ((par_eq_zero_iff z).mp hz)),
            cy_eq_zero_of_cx (Or.inl ((par_eq_zero_iff w).mp hw))⟩
        · have hz : par z = 1 := ha_inj hq
          have hw : par w = 1 := hb_inj (h.symm.trans (hq.trans h₁))
          exact ⟨cy_eq_zero_of_cx (Or.inr ((par_eq_one_iff z).mp hz)),
            cy_eq_zero_of_cx (Or.inr ((par_eq_one_iff w).mp hw))⟩
      have hsq : ∀ z w : Circle1, cx z = cx w → cy z ^ 2 = cy w ^ 2 := by
        intro z w h
        have hz := cx_sq_add_cy_sq z
        have hw := cx_sq_add_cy_sq w
        rw [h] at hz
        linarith
      intro z w h
      simp only at h
      by_cases hz : 0 ≤ cy z <;> by_cases hw : 0 ≤ cy w <;>
        simp only [hz, hw, ite_true, ite_false] at h
      · have hx := hpar z w (ha_inj h)
        exact circle_ext hx ((sq_eq_sq₀ hz hw).mp (hsq z w hx))
      · exact absurd (hmixed z w h).2 (ne_of_lt (not_le.mp hw))
      · exact absurd (hmixed w z h.symm).2 (ne_of_lt (not_le.mp hz))
      · have hx := hpar z w (hb_inj h)
        have hy := (sq_eq_sq₀ (neg_nonneg.mpr (not_le.mp hz).le)
          (neg_nonneg.mpr (not_le.mp hw).le)).mp
            (by rw [neg_sq, neg_sq]; exact hsq z w hx)
        exact circle_ext hx (by linarith)
    · apply Subset.antisymm
      · rintro _ ⟨z, rfl⟩
        simp only
        split_ifs
        · exact Or.inl (mem_range_self _)
        · exact Or.inr (mem_range_self _)
      · have hpt : ∀ t : unitInterval, ∀ s : ℝ,
            s ^ 2 = 1 - (1 - 2 * (t : ℝ)) ^ 2 →
            ∃ z : Circle1, par z = t ∧ cy z = s := by
          intro t s hs
          refine ⟨pt (1 - 2 * (t : ℝ)) s (by linarith), ?_, cy_pt _ _ _⟩
          apply Subtype.ext
          simp only [par, cx_pt]
          ring
        have hnn : ∀ t : unitInterval, 0 ≤ 1 - (1 - 2 * (t : ℝ)) ^ 2 := fun t => by
          nlinarith [t.2.1, t.2.2]
        rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
        · obtain ⟨z, hz, hy⟩ := hpt t (Real.sqrt (1 - (1 - 2 * (t : ℝ)) ^ 2))
            (Real.sq_sqrt (hnn t))
          refine ⟨z, ?_⟩
          simp only [hy, Real.sqrt_nonneg, ite_true, hz]
        · obtain ⟨z, hz, hy⟩ := hpt t (-Real.sqrt (1 - (1 - 2 * (t : ℝ)) ^ 2))
            (by rw [neg_sq]; exact Real.sq_sqrt (hnn t))
          refine ⟨z, ?_⟩
          simp only
          split_ifs with h
          · have hzero : cy z = 0 := by
              have hnonneg := Real.sqrt_nonneg (1 - (1 - 2 * (t : ℝ)) ^ 2)
              linarith
            rw [hbd z hzero, hz]
          · rw [hz]
  let L := Jordan.Arcs.complexLIE
  let e : Metric.sphere (0 : ℂ) 1 ≃ₜ Circle1 :=
    L.toHomeomorph.subtype (fun z => by
      simp only [mem_sphere_zero_iff_norm]
      change ‖z‖ = 1 ↔ ‖L z‖ = 1
      rw [L.norm_map])
  let φ : Metric.sphere (0 : ℂ) 1 → ℂ := f ∘ e
  let F : ℂ → ℂ := Function.extend Subtype.val φ (fun _ => 0)
  have hF : ∀ z : Metric.sphere (0 : ℂ) 1, F z = φ z := fun z =>
    Subtype.val_injective.extend_apply φ (fun _ => 0) z
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    exact (hf.comp e.continuous).congr (fun z => (hF z).symm)
  · intro z hz w hw hzw
    have heq : φ ⟨z, hz⟩ = φ ⟨w, hw⟩ :=
      (hF ⟨z, hz⟩).symm.trans (hzw.trans (hF ⟨w, hw⟩))
    exact congrArg Subtype.val (e.injective (hinj heq))
  · rw [← hrange]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨e ⟨w, hw⟩, (hF ⟨w, hw⟩).symm⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨v, rfl⟩ := e.surjective w
      exact ⟨v, v.2, hF v⟩

end MatedCRTHarmonic.Planar.ArcUnion

end
