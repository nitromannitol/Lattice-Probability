import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.UnitInterval
import LatticeProb.Topology.PlaneTopology

/-!
# Two arcs with common endpoints form a simple closed curve

* `exists_circle_injective_of_injOn_Ico`: a map `γ : ℝ → X`, continuous on `[0, 1]`, with `γ 0 = γ 1` and
  injective on `[0, 1)`, factors through a continuous injective map of the circle with image `γ '' [0, 1]`.
* `exists_circle_injective_of_arcs`: if two arcs `f, g : [0, 1] → X` run from `a` to `b` and meet only at `a` and
  `b`, then `range f ∪ range g` is the image of a continuous injective map of the circle.
* `isSimpleLoop_union_of_arcs`: the plane case, in terms of `IsSimpleLoop`.
-/

namespace LatticeProb.Topology

open Set

variable {X : Type*} [TopologicalSpace X]

/-- A map of `[0, 1]`, continuous on `[0, 1]`, which identifies the two endpoints and is injective on `[0, 1)`,
factors through a continuous injective map of the circle. -/
theorem exists_circle_injective_of_injOn_Ico {γ : ℝ → X} (hc : ContinuousOn γ (Icc 0 1))
    (h01 : γ 0 = γ 1) (hinj : InjOn γ (Ico 0 1)) :
    ∃ φ : Circle → X, Continuous φ ∧ Function.Injective φ ∧ range φ = γ '' Icc 0 1 := by
  have hψc : Continuous (AddCircle.liftIco 1 0 γ) := AddCircle.liftIco_zero_continuous h01 hc
  have hψ : ∀ x ∈ Ico (0 : ℝ) 1, AddCircle.liftIco 1 0 γ (x : AddCircle (1 : ℝ)) = γ x :=
    fun x hx => AddCircle.liftIco_zero_coe_apply hx
  have hrep : ∀ z : AddCircle (1 : ℝ), ∃ x ∈ Ico (0 : ℝ) 1, (x : AddCircle (1 : ℝ)) = z := by
    intro z
    refine ⟨(AddCircle.equivIco 1 0 z : ℝ), by simpa using (AddCircle.equivIco 1 0 z).2, ?_⟩
    exact (AddCircle.equivIco 1 0).symm_apply_apply z
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  refine ⟨AddCircle.liftIco 1 0 γ ∘ e.symm, hψc.comp e.symm.continuous, ?_, ?_⟩
  · have hinjψ : Function.Injective (AddCircle.liftIco 1 0 γ) := by
      intro z w hzw
      obtain ⟨x, hx, rfl⟩ := hrep z
      obtain ⟨y, hy, rfl⟩ := hrep w
      rw [hψ x hx, hψ y hy] at hzw
      rw [hinj hx hy hzw]
    exact hinjψ.comp e.symm.injective
  · rw [e.symm.surjective.range_comp]
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hrep z
      exact ⟨x, Ico_subset_Icc_self hx, (hψ x hx).symm⟩
    · rintro ⟨t, ht, rfl⟩
      rcases eq_or_lt_of_le ht.2 with h1 | h1
      · refine ⟨((0 : ℝ) : AddCircle (1 : ℝ)), ?_⟩
        rw [hψ 0 ⟨le_rfl, zero_lt_one⟩, h01, h1]
      · exact ⟨(t : AddCircle (1 : ℝ)), hψ t ⟨ht.1, h1⟩⟩

/-- **Two arcs with common endpoints and no other common point form a simple closed curve.** If
`f, g : [0, 1] → X` are continuous and injective, `f 0 = g 0 = a`, `f 1 = g 1 = b`, and the two arcs meet only at
`a` and `b`, then `range f ∪ range g` is the image of a continuous injective map of the circle. -/
theorem exists_circle_injective_of_arcs {a b : X} {f g : unitInterval → X} (hf : Continuous f)
    (hg : Continuous g) (hfi : Function.Injective f) (hgi : Function.Injective g) (hf0 : f 0 = a)
    (hf1 : f 1 = b) (hg0 : g 0 = a) (hg1 : g 1 = b) (hfg : range f ∩ range g ⊆ {a, b}) :
    ∃ φ : Circle → X, Continuous φ ∧ Function.Injective φ ∧ range φ = range f ∪ range g := by
  set F : ℝ → X := IccExtend zero_le_one f with hFdef
  set G : ℝ → X := IccExtend zero_le_one g with hGdef
  have hF : ∀ x (hx : x ∈ Icc (0 : ℝ) 1), F x = f ⟨x, hx⟩ := fun x hx => IccExtend_of_mem _ _ hx
  have hG : ∀ x (hx : x ∈ Icc (0 : ℝ) 1), G x = g ⟨x, hx⟩ := fun x hx => IccExtend_of_mem _ _ hx
  have hFc : Continuous F := hf.Icc_extend'
  have hGc : Continuous G := hg.Icc_extend'
  set γ : ℝ → X := fun t => if t ≤ 1 / 2 then F (2 * t) else G (2 - 2 * t) with hγdef
  have hγc : Continuous γ := by
    refine Continuous.if_le (hFc.comp (continuous_const.mul continuous_id))
      (hGc.comp (continuous_const.sub (continuous_const.mul continuous_id))) continuous_id
      continuous_const fun t ht => ?_
    rw [ht]
    norm_num
    rw [hF 1 ⟨zero_le_one, le_rfl⟩, hG 1 ⟨zero_le_one, le_rfl⟩]
    exact (show f 1 = g 1 by rw [hf1, hg1])
  have hγl : ∀ t, t ≤ 1 / 2 → γ t = F (2 * t) := by
    intro t ht
    simp only [hγdef]
    split_ifs
    rfl
  have hγr : ∀ t, ¬ t ≤ 1 / 2 → γ t = G (2 - 2 * t) := by
    intro t ht
    simp only [hγdef]
    split_ifs
    rfl
  -- a point of `g` strictly inside the arc is not on `f`
  have hmix : ∀ (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) (v : unitInterval),
      f v ≠ g ⟨u, Ioo_subset_Icc_self hu⟩ := by
    intro u hu v hv
    have hmem : g ⟨u, Ioo_subset_Icc_self hu⟩ ∈ ({a, b} : Set X) := hfg ⟨⟨v, hv⟩, ⟨_, rfl⟩⟩
    rcases hmem with h | h
    · have := hgi (h.trans hg0.symm)
      exact hu.1.ne' (congrArg Subtype.val this)
    · have := hgi (h.trans hg1.symm)
      exact hu.2.ne (congrArg Subtype.val this)
  have h01 : γ 0 = γ 1 := by
    rw [hγl 0 (by norm_num), hγr 1 (by norm_num)]
    norm_num
    rw [hF 0 ⟨le_rfl, zero_le_one⟩, hG 0 ⟨le_rfl, zero_le_one⟩]
    exact (show f 0 = g 0 by rw [hf0, hg0])
  have hinj : InjOn γ (Ico 0 1) := by
    intro s hs t ht hst
    by_cases hs2 : s ≤ 1 / 2 <;> by_cases ht2 : t ≤ 1 / 2
    · rw [hγl s hs2, hγl t ht2, hF (2 * s) ⟨by linarith [hs.1], by linarith⟩,
        hF (2 * t) ⟨by linarith [ht.1], by linarith⟩] at hst
      have := congrArg Subtype.val (hfi hst)
      simp only at this
      linarith
    · rw [hγl s hs2, hγr t ht2, hF (2 * s) ⟨by linarith [hs.1], by linarith⟩,
        hG (2 - 2 * t) ⟨by linarith [ht.2], by linarith⟩] at hst
      exact absurd hst (hmix (2 - 2 * t) ⟨by linarith [ht.2], by linarith⟩ _)
    · rw [hγr s hs2, hγl t ht2, hF (2 * t) ⟨by linarith [ht.1], by linarith⟩,
        hG (2 - 2 * s) ⟨by linarith [hs.2], by linarith⟩] at hst
      exact absurd hst.symm (hmix (2 - 2 * s) ⟨by linarith [hs.2], by linarith⟩ _)
    · rw [hγr s hs2, hγr t ht2, hG (2 - 2 * s) ⟨by linarith [hs.2], by linarith⟩,
        hG (2 - 2 * t) ⟨by linarith [ht.2], by linarith⟩] at hst
      have := congrArg Subtype.val (hgi hst)
      simp only at this
      linarith
  obtain ⟨φ, hφc, hφi, hφr⟩ := exists_circle_injective_of_injOn_Ico hγc.continuousOn h01 hinj
  refine ⟨φ, hφc, hφi, hφr.trans ?_⟩
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases ht2 : t ≤ 1 / 2
    · rw [hγl t ht2, hF (2 * t) ⟨by linarith [ht.1], by linarith⟩]
      exact Or.inl ⟨_, rfl⟩
    · rw [hγr t ht2, hG (2 - 2 * t) ⟨by linarith [ht.2], by linarith⟩]
      exact Or.inr ⟨_, rfl⟩
  · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · refine ⟨u / 2, ⟨by linarith [u.2.1], by linarith [u.2.2]⟩, ?_⟩
      rw [hγl (u / 2) (by linarith [u.2.2]), hF (2 * (u / 2)) ⟨by linarith [u.2.1], by linarith [u.2.2]⟩]
      congr 1
      ext
      simp only
      ring
    · rcases eq_or_lt_of_le u.2.2 with hu | hu
      · have hu1 : u = 1 := Subtype.ext hu
        refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
        rw [hγl (1 / 2) le_rfl, show (2 : ℝ) * (1 / 2) = 1 by norm_num, hF 1 ⟨zero_le_one, le_rfl⟩, hu1]
        exact (show f 1 = g 1 by rw [hf1, hg1])
      · refine ⟨1 - u / 2, ⟨by linarith [u.2.2], by linarith [u.2.1]⟩, ?_⟩
        rw [hγr (1 - u / 2) (by push Not; linarith),
          hG (2 - 2 * (1 - u / 2)) ⟨by linarith [u.2.1], by linarith [u.2.2]⟩]
        congr 1
        ext
        simp only
        ring

/-- **Two arcs in the plane with common endpoints and no other common point form a simple loop.** -/
theorem isSimpleLoop_union_of_arcs {a b : ℂ} {f g : unitInterval → ℂ} (hf : Continuous f)
    (hg : Continuous g) (hfi : Function.Injective f) (hgi : Function.Injective g) (hf0 : f 0 = a)
    (hf1 : f 1 = b) (hg0 : g 0 = a) (hg1 : g 1 = b) (hfg : range f ∩ range g ⊆ {a, b}) :
    IsSimpleLoop (range f ∪ range g) :=
  exists_circle_injective_of_arcs hf hg hfi hgi hf0 hf1 hg0 hg1 hfg

end LatticeProb.Topology
