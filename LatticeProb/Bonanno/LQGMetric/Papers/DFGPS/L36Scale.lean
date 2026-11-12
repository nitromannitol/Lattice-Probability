/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36Scale at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36Lower
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Dilate
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
"By the scale and translation invariance of the law of `h`, modulo additive constant, we have
`h(𝕣·) − h_𝕣(0) =ᵈ h`. Moreover … `D̃^δ_{h(𝕣·)−h_𝕣(0)}(·,·;𝕊) = e^{−ξ h_𝕣(0)} D̃^{δ𝕣}_h(·,·;𝕣𝕊)`."
(DFGPS arXiv:1905.00380, T:1640–1644.) We use it pathwise: `h' = h(𝕣·) − h_𝕣(0)` is again a
normalized whole-plane GFF on the same space (`IsWholePlaneGFF.affineComp`, `.addConst`,
`CircleAvg.ae_circleAvg_affineComp`, `ae_circleAvg_addConst`, `GM.affineComp_comp`), its circle
averages are `h'_δ(u) = h_{δ𝕣}(𝕣u) − h_𝕣(0)` a.s. on the countable grid, and the graph LFPP
scales as displayed (`graphLFPP_scale`, `graphLFPP_add_const`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS.L36

open Blueprint

/-! ## Deterministic scaling of the graph LFPP -/

section scale

variable {𝕣 : ℝ} (h𝕣 : 0 < 𝕣)
include h𝕣

lemma mul_inv_cancel_r (x : ℂ) : (𝕣 : ℂ) * ((𝕣 : ℂ)⁻¹ * x) = x := by
  have : (𝕣 : ℂ) ≠ 0 := by exact_mod_cast h𝕣.ne'
  field_simp

lemma mem_rS_iff (x : ℂ) : x ∈ rS 𝕣 ↔ (𝕣 : ℂ)⁻¹ * x ∈ rS 1 := by
  have h0 : (𝕣 : ℂ) ≠ 0 := by exact_mod_cast h𝕣.ne'
  simp only [rS, scaleSet, mem_image, Complex.ofReal_one, one_mul, add_zero, exists_eq_right]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [← mul_assoc, inv_mul_cancel₀ h0, one_mul]
  · intro hx
    exact ⟨_, hx, mul_inv_cancel_r h𝕣 x⟩

lemma re_inv_mul (x : ℂ) : ((𝕣 : ℂ)⁻¹ * x).re = x.re / 𝕣 := by
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]; ring

lemma im_inv_mul (x : ℂ) : ((𝕣 : ℂ)⁻¹ * x).im = x.im / 𝕣 := by
  rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]; ring

lemma mem_gridPts_iff {δ : ℝ} (x : ℂ) :
    x ∈ gridPts (δ * 𝕣) ↔ (𝕣 : ℂ)⁻¹ * x ∈ gridPts δ := by
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨a, b, Complex.ext ?_ ?_⟩
    · rw [re_inv_mul h𝕣]; simp; field_simp
    · rw [im_inv_mul h𝕣]; simp; field_simp
  · rintro ⟨a, b, hab⟩
    refine ⟨a, b, Complex.ext ?_ ?_⟩
    · have := congrArg Complex.re hab
      rw [re_inv_mul h𝕣] at this
      simp only at this ⊢
      field_simp at this; linarith
    · have := congrArg Complex.im hab
      rw [im_inv_mul h𝕣] at this
      simp only at this ⊢
      field_simp at this; linarith

lemma norm_sub_inv_mul (x y : ℂ) :
    ‖x - y‖ = 𝕣 * ‖(𝕣 : ℂ)⁻¹ * x - (𝕣 : ℂ)⁻¹ * y‖ := by
  rw [← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg h𝕣.le, ← mul_assoc,
    mul_inv_cancel₀ h𝕣.ne', one_mul]

lemma mem_cell_iff {δ : ℝ} (x : ℂ) : x ∈ rS 𝕣 ∩ gridPts (δ * 𝕣) ↔
    (𝕣 : ℂ)⁻¹ * x ∈ rS 1 ∩ gridPts δ := by
  rw [mem_inter_iff, mem_inter_iff, mem_rS_iff h𝕣, mem_gridPts_iff h𝕣]

lemma mem_leftVerts_iff {δ : ℝ} (x : ℂ) :
    x ∈ leftVerts (δ * 𝕣) 𝕣 ↔ (𝕣 : ℂ)⁻¹ * x ∈ leftVerts δ 1 := by
  simp only [leftVerts, mem_setOf_eq, mem_cell_iff h𝕣]
  refine and_congr_right fun _ => ⟨fun H y hy => ?_, fun H y hy => ?_⟩
  · have := H ((𝕣 : ℂ) * y) (by rwa [← mul_assoc,
      inv_mul_cancel₀ (by exact_mod_cast h𝕣.ne'), one_mul])
    rw [re_inv_mul h𝕣, div_le_iff₀ h𝕣]
    rw [Complex.re_ofReal_mul] at this; linarith
  · have := H _ hy
    rw [re_inv_mul h𝕣, re_inv_mul h𝕣] at this
    exact (div_le_div_iff_of_pos_right h𝕣).1 this

lemma mem_rightVerts_iff {δ : ℝ} (x : ℂ) :
    x ∈ rightVerts (δ * 𝕣) 𝕣 ↔ (𝕣 : ℂ)⁻¹ * x ∈ rightVerts δ 1 := by
  simp only [rightVerts, mem_setOf_eq, mem_cell_iff h𝕣]
  refine and_congr_right fun _ => ⟨fun H y hy => ?_, fun H y hy => ?_⟩
  · have := H ((𝕣 : ℂ) * y) (by rwa [← mul_assoc,
      inv_mul_cancel₀ (by exact_mod_cast h𝕣.ne'), one_mul])
    rw [re_inv_mul h𝕣, le_div_iff₀ h𝕣]
    rw [Complex.re_ofReal_mul] at this; linarith
  · have := H _ hy
    rw [re_inv_mul h𝕣, re_inv_mul h𝕣] at this
    exact (div_le_div_iff_of_pos_right h𝕣).1 this

/-- the admissible lists for `(δ𝕣, 𝕣𝕊)` are the images under `u ↦ 𝕣u` of those for `(δ, 𝕊)` -/
lemma admissible_iff {δ : ℝ} (L : List ℂ) :
    (IsGraphPath (δ * 𝕣) (rS 𝕣) L ∧ (∃ x ∈ L.head?, x ∈ leftVerts (δ * 𝕣) 𝕣) ∧
      ∃ y ∈ L.getLast?, y ∈ rightVerts (δ * 𝕣) 𝕣) ↔
    (IsGraphPath δ (rS 1) (L.map ((𝕣 : ℂ)⁻¹ * ·)) ∧
      (∃ x ∈ (L.map ((𝕣 : ℂ)⁻¹ * ·)).head?, x ∈ leftVerts δ 1) ∧
      ∃ y ∈ (L.map ((𝕣 : ℂ)⁻¹ * ·)).getLast?, y ∈ rightVerts δ 1) := by
  have hR : ∀ x y : ℂ, (‖x - y‖ = δ * 𝕣 ∨ ‖x - y‖ = Real.sqrt 2 * (δ * 𝕣)) ↔
      (‖(𝕣 : ℂ)⁻¹ * x - (𝕣 : ℂ)⁻¹ * y‖ = δ ∨
        ‖(𝕣 : ℂ)⁻¹ * x - (𝕣 : ℂ)⁻¹ * y‖ = Real.sqrt 2 * δ) := fun x y => by
    rw [norm_sub_inv_mul h𝕣 x y]
    constructor <;> rintro (h | h)
    · left; nlinarith [mul_left_cancel₀ h𝕣.ne' (show 𝕣 * _ = 𝕣 * δ by rw [h]; ring)]
    · right; exact mul_left_cancel₀ h𝕣.ne' (by rw [h]; ring)
    · left; rw [h]; ring
    · right; rw [h]; ring
  unfold IsGraphPath
  rw [List.isChain_map, List.head?_map, List.getLast?_map]
  simp only [ne_eq, List.map_eq_nil_iff, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Option.mem_def, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨hne, hmem, hch⟩, ⟨x, hx, hxl⟩, ⟨y, hy, hyr⟩⟩
    refine ⟨⟨hne, fun a ha => (mem_cell_iff h𝕣 a).1 (hmem a ha), hch.imp fun {a b} h => (hR a b).1 h⟩,
      ⟨_, ⟨x, hx, rfl⟩, (mem_leftVerts_iff h𝕣 x).1 hxl⟩, ⟨_, ⟨y, hy, rfl⟩, (mem_rightVerts_iff h𝕣 y).1 hyr⟩⟩
  · rintro ⟨⟨hne, hmem, hch⟩, ⟨_, ⟨x, hx, rfl⟩, hxl⟩, ⟨_, ⟨y, hy, rfl⟩, hyr⟩⟩
    exact ⟨⟨hne, fun a ha => (mem_cell_iff h𝕣 a).2 (hmem a ha), hch.imp fun {a b} h => (hR a b).2 h⟩,
      ⟨x, hx, (mem_leftVerts_iff h𝕣 x).2 hxl⟩, ⟨y, hy, (mem_rightVerts_iff h𝕣 y).2 hyr⟩⟩

/-- `D̃^{δ𝕣}_φ(∂_L, ∂_R; 𝕣𝕊) = D̃^δ_{φ(𝕣·)}(∂_L, ∂_R; 𝕊)` -/
theorem graphLFPP_scale (ξ δ : ℝ) (ψ : ℂ → ℝ) :
    graphLFPP ξ (δ * 𝕣) ψ (leftVerts (δ * 𝕣) 𝕣) (rightVerts (δ * 𝕣) 𝕣) (rS 𝕣) =
      graphLFPP ξ δ (fun u => ψ ((𝕣 : ℂ) * u)) (leftVerts δ 1) (rightVerts δ 1) (rS 1) := by
  have hinv : ∀ L : List ℂ, (L.map ((𝕣 : ℂ)⁻¹ * ·)).map ((𝕣 : ℂ) * ·) = L := fun L => by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id L]
    exact List.map_congr_left fun x _ => mul_inv_cancel_r h𝕣 x
  have hinv' : ∀ L : List ℂ, (L.map ((𝕣 : ℂ) * ·)).map ((𝕣 : ℂ)⁻¹ * ·) = L := fun L => by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id L]
    refine List.map_congr_left fun x _ => ?_
    have : (𝕣 : ℂ) ≠ 0 := by exact_mod_cast h𝕣.ne'
    simp only [Function.comp_apply, id]
    field_simp
  let e : {L : List ℂ // IsGraphPath (δ * 𝕣) (rS 𝕣) L ∧
      (∃ x ∈ L.head?, x ∈ leftVerts (δ * 𝕣) 𝕣) ∧ ∃ y ∈ L.getLast?, y ∈ rightVerts (δ * 𝕣) 𝕣} ≃
      {L : List ℂ // IsGraphPath δ (rS 1) L ∧ (∃ x ∈ L.head?, x ∈ leftVerts δ 1) ∧
        ∃ y ∈ L.getLast?, y ∈ rightVerts δ 1} :=
    { toFun := fun L => ⟨L.1.map ((𝕣 : ℂ)⁻¹ * ·), (admissible_iff h𝕣 L.1).1 L.2⟩
      invFun := fun L => ⟨L.1.map ((𝕣 : ℂ) * ·), (admissible_iff h𝕣 _).2 (by rw [hinv']; exact L.2)⟩
      left_inv := fun L => Subtype.ext (hinv L.1)
      right_inv := fun L => Subtype.ext (hinv' L.1) }
  unfold graphLFPP
  refine (e.iInf_congr fun L => ?_)
  show ((L.1.map ((𝕣 : ℂ)⁻¹ * ·)).map fun u => Real.exp (ξ * ψ ((𝕣 : ℂ) * u))).sum =
    (L.1.map fun x => Real.exp (ξ * ψ x)).sum
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun x _ => by simp only [Function.comp_apply, mul_inv_cancel_r h𝕣 x]

end scale

/-- `D̃^ε_{φ + c} = e^{ξ c} D̃^ε_φ` -/
theorem graphLFPP_add_const (ξ ε c : ℝ) (φ : ℂ → ℝ) (A B U : Set ℂ) :
    graphLFPP ξ ε (fun u => φ u + c) A B U = Real.exp (ξ * c) * graphLFPP ξ ε φ A B U := by
  unfold graphLFPP
  rw [Real.mul_iInf_of_nonneg (Real.exp_pos _).le]
  refine iInf_congr fun L => ?_
  rw [← List.sum_map_mul_left]
  congr 1
  exact List.map_congr_left fun x _ => by
    simp only [Function.comp_apply, mul_add, Real.exp_add]; ring

end LQGMetric.DFGPS.L36
