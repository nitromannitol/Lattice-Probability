/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4GreenBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4Green
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4CoarseCovariance
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFBoxDegree

 



















set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory Matrix

namespace SupercriticalLQGUniqueness.B2.QPos.P4

open P3

open Classical in
theorem box_edge_apply (n : ℕ) (a b : DGFFSite n) :
    (boxConductances n).edge a b = if latticeAdjacent a.1 b.1 then dgffConductance else 0 := by
  classical
  unfold boxConductances
  simp only

open Classical in
 
theorem box_precision_apply (n : ℕ) (a b : DGFFSite n) :
    (boxConductances n).precision a b =
      (2 / Real.pi) * ((if a = b then 1 else 0) -
        (if latticeAdjacent a.1 b.1 then (1 / 4 : ℝ) else 0)) := by
  classical
  rw [WiredConductances.precision_eq_totalRate_sub_edge, box_totalRate_eq, box_edge_apply]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold dgffConductance
  split_ifs <;> field_simp <;> ring

 
def innerSet (n : ℕ) (S : Finset (DGFFSite n)) : Finset (ℤ × ℤ) :=
  S.map (Function.Embedding.subtype _)

theorem mem_innerSet {n : ℕ} {S : Finset (DGFFSite n)} {c : ℤ × ℤ} :
    c ∈ innerSet n S ↔ ∃ h : c ∈ interiorSites n, (⟨c, h⟩ : DGFFSite n) ∈ S := by
  unfold innerSet
  simp only [mem_map, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d.2, hd⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨c, h⟩, hc, rfl⟩

theorem mem_innerSet_of_mem {n : ℕ} {S : Finset (DGFFSite n)} {c : DGFFSite n}
    (hc : c ∈ S) : c.1 ∈ innerSet n S :=
  mem_innerSet.mpr ⟨c.2, hc⟩

 
theorem sum_inner_eq (n : ℕ) (S : Finset (DGFFSite n)) (f : ℤ × ℤ → ℝ) :
    ∑ c : {z : DGFFSite n // z ∈ S}, f c.1.1 = ∑ c ∈ innerSet n S, f c := by
  classical
  unfold innerSet
  rw [Finset.sum_map]
  exact (Finset.sum_subtype S (fun _ => Iff.rfl) (fun z : DGFFSite n => f z.1)).symm

 
theorem sum_site_eq (n : ℕ) (f : ℤ × ℤ → ℝ) :
    ∑ c : DGFFSite n, f c.1 = ∑ c ∈ interiorSites n, f c :=
  (Finset.sum_subtype (interiorSites n) (fun _ => Iff.rfl) f).symm

open Classical in
 

theorem green_lap_eq (V : Finset (ℤ × ℤ)) {a b : ℤ × ℤ} (ha : a ∈ V) (hb : b ∈ V) :
    green V a b - (1 / 4 : ℝ) * ∑ c ∈ V,
        (if latticeAdjacent a c then green V c b else 0) =
      if a = b then 1 else 0 := by
  classical
  have h1 := sum_adj_eq V a (fun c => green V c b) (fun c hc => green_of_not_mem_left hc b)
  have h2 := green_eq ha b
  have h3 : ∑ c ∈ V, (if latticeAdjacent a c then green V c b else 0) =
      ∑ c ∈ V, (if latticeAdjacent a c then (1 : ℝ) else 0) * green V c b := by
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> ring
  have hpt : pt V b a = if a = b then 1 else 0 := by
    unfold pt
    by_cases hab : a = b
    · rw [if_pos ⟨hab, hb⟩, if_pos hab]
    · rw [if_neg (fun h => hab h.1), if_neg hab]
  unfold avg at h2
  convert (show green V a b - (1 / 4 : ℝ) *
      ∑ c ∈ V, (if latticeAdjacent a c then green V c b else 0) = pt V b a by
    rw [h1, h2]; ring) using 1
  rw [hpt]

open Classical in
 

theorem innerBlock_mul_green (n : ℕ) (S : Finset (DGFFSite n)) :
    (boxSplitPrecision n (boxInnerOuterEquiv n S)).toBlocks₁₁ *
        (Matrix.of fun i j : {z : DGFFSite n // z ∈ S} =>
          (Real.pi / 2) * green (innerSet n S) i.1.1 j.1.1) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  have hblk : ∀ c : {z : DGFFSite n // z ∈ S},
      (boxSplitPrecision n (boxInnerOuterEquiv n S)).toBlocks₁₁ i c =
        (boxConductances n).precision i.1 c.1 := by
    intro c
    rfl
  simp_rw [hblk, box_precision_apply]
  have hrw : ∀ c : {z : DGFFSite n // z ∈ S},
      (2 / Real.pi) * ((if i.1 = c.1 then (1 : ℝ) else 0) -
          (if latticeAdjacent i.1.1 c.1.1 then (1 / 4 : ℝ) else 0)) *
        ((Real.pi / 2) * green (innerSet n S) c.1.1 j.1.1) =
      (if i.1.1 = c.1.1 then green (innerSet n S) c.1.1 j.1.1 else 0) -
        (1 / 4 : ℝ) * (if latticeAdjacent i.1.1 c.1.1 then
          green (innerSet n S) c.1.1 j.1.1 else 0) := by
    intro c
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hiff : (i.1 = c.1) ↔ (i.1.1 = c.1.1) := Subtype.ext_iff
    by_cases h1 : i.1.1 = c.1.1
    · have h1' : i.1 = c.1 := hiff.mpr h1
      rw [if_pos h1', if_pos h1]
      split_ifs <;> field_simp <;> ring
    · have h1' : ¬ i.1 = c.1 := fun h => h1 (hiff.mp h)
      rw [if_neg h1', if_neg h1]
      split_ifs <;> field_simp <;> ring
  simp_rw [hrw]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_inner_eq n S (fun c => if i.1.1 = c then green (innerSet n S) c j.1.1 else 0),
    sum_inner_eq n S (fun c => if latticeAdjacent i.1.1 c then
      green (innerSet n S) c j.1.1 else 0)]
  rw [Finset.sum_ite_eq (innerSet n S) i.1.1, if_pos (mem_innerSet_of_mem i.2)]
  rw [green_lap_eq _ (mem_innerSet_of_mem i.2) (mem_innerSet_of_mem j.2)]
  rw [Matrix.one_apply]
  have hiff : (i = j) ↔ (i.1.1 = j.1.1) := by
    constructor
    · rintro rfl; rfl
    · intro h; exact Subtype.ext (Subtype.ext h)
  by_cases h : i = j
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

theorem innerBlock_inv_eq_green (n : ℕ) (S : Finset (DGFFSite n))
    (i j : {z : DGFFSite n // z ∈ S}) :
    (boxSplitPrecision n (boxInnerOuterEquiv n S)).toBlocks₁₁⁻¹ i j =
      (Real.pi / 2) * green (innerSet n S) i.1.1 j.1.1 := by
  rw [Matrix.inv_eq_right_inv (innerBlock_mul_green n S), Matrix.of_apply]

open Classical in
 

theorem precision_mul_green (n : ℕ) :
    (boxConductances n).precision *
        (Matrix.of fun a b : DGFFSite n => (Real.pi / 2) * green (interiorSites n) a.1 b.1) = 1 := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  simp_rw [box_precision_apply]
  have hrw : ∀ c : DGFFSite n,
      (2 / Real.pi) * ((if a = c then (1 : ℝ) else 0) -
          (if latticeAdjacent a.1 c.1 then (1 / 4 : ℝ) else 0)) *
        ((Real.pi / 2) * green (interiorSites n) c.1 b.1) =
      (if a.1 = c.1 then green (interiorSites n) c.1 b.1 else 0) -
        (1 / 4 : ℝ) * (if latticeAdjacent a.1 c.1 then
          green (interiorSites n) c.1 b.1 else 0) := by
    intro c
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hiff : (a = c) ↔ (a.1 = c.1) := Subtype.ext_iff
    by_cases h1 : a.1 = c.1
    · rw [if_pos (hiff.mpr h1), if_pos h1]
      split_ifs <;> field_simp <;> ring
    · rw [if_neg (fun h => h1 (hiff.mp h)), if_neg h1]
      split_ifs <;> field_simp <;> ring
  simp_rw [hrw]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_site_eq n (fun c => if a.1 = c then green (interiorSites n) c b.1 else 0),
    sum_site_eq n (fun c => if latticeAdjacent a.1 c then
      green (interiorSites n) c b.1 else 0)]
  rw [Finset.sum_ite_eq (interiorSites n) a.1, if_pos a.2]
  rw [green_lap_eq _ a.2 b.2, Matrix.one_apply]
  have hiff : (a = b) ↔ (a.1 = b.1) := Subtype.ext_iff
  by_cases h : a = b
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

theorem precision_inv_eq_green (n : ℕ) (a b : DGFFSite n) :
    (boxConductances n).precision⁻¹ a b =
      (Real.pi / 2) * green (interiorSites n) a.1 b.1 := by
  rw [Matrix.inv_eq_right_inv (precision_mul_green n), Matrix.of_apply]

 
theorem splitPrecision_inv_inl (n : ℕ) (S : Finset (DGFFSite n))
    (i j : {z : DGFFSite n // z ∈ S}) :
    (boxSplitPrecision n (boxInnerOuterEquiv n S))⁻¹ (Sum.inl i) (Sum.inl j) =
      (Real.pi / 2) * green (interiorSites n) i.1.1 j.1.1 := by
  unfold boxSplitPrecision
  rw [Matrix.inv_reindex]
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [precision_inv_eq_green]
  rfl

 

theorem mem_interiorSites_iff (n : ℕ) (c : ℤ × ℤ) :
    c ∈ interiorSites n ↔
      -interiorRadius n ≤ c.1 ∧ c.1 ≤ interiorRadius n ∧
      -interiorRadius n ≤ c.2 ∧ c.2 ≤ interiorRadius n := by
  simp [interiorSites, Finset.mem_product, Finset.mem_Icc, and_assoc]

 
theorem exists_box_superset (U : Finset (ℤ × ℤ)) : ∃ N : ℕ, U ⊆ interiorSites N := by
  classical
  set M : ℕ := U.sup fun c => max c.1.natAbs c.2.natAbs
  refine ⟨M + 1, fun c hc => ?_⟩
  have h : max c.1.natAbs c.2.natAbs ≤ M :=
    Finset.le_sup (f := fun c : ℤ × ℤ => max c.1.natAbs c.2.natAbs) hc
  have hM : (M : ℤ) + 1 ≤ interiorRadius (M + 1) := by
    unfold interiorRadius
    have : (M : ℤ) + 2 ≤ 2 ^ (M + 1) := by
      have h2 : M + 2 ≤ 2 ^ (M + 1) := by
        induction M with
        | zero => norm_num
        | succ k ih => rw [pow_succ]; omega
      exact_mod_cast h2
    omega
  have h1 : c.1.natAbs ≤ M := le_trans (le_max_left _ _) h
  have h2 : c.2.natAbs ≤ M := le_trans (le_max_right _ _) h
  have h1' : |c.1| ≤ M := by rw [Int.abs_eq_natAbs]; exact_mod_cast h1
  have h2' : |c.2| ≤ M := by rw [Int.abs_eq_natAbs]; exact_mod_cast h2
  rw [abs_le] at h1' h2'
  rw [mem_interiorSites_iff]
  omega

 
def siteFilter (N : ℕ) (U : Finset (ℤ × ℤ)) : Finset (DGFFSite N) :=
  Finset.univ.filter fun c => c.1 ∈ U

theorem innerSet_siteFilter {N : ℕ} {U : Finset (ℤ × ℤ)} (hU : U ⊆ interiorSites N) :
    innerSet N (siteFilter N U) = U := by
  ext c
  rw [mem_innerSet]
  unfold siteFilter
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨hU h, h⟩

 
theorem green_symm (U : Finset (ℤ × ℤ)) (a b : ℤ × ℤ) : green U a b = green U b a := by
  classical
  by_cases ha : a ∈ U
  swap
  · rw [green_of_not_mem_left ha, green_of_not_mem_right b ha]
  by_cases hb : b ∈ U
  swap
  · rw [green_of_not_mem_right a hb, green_of_not_mem_left hb]
  obtain ⟨N, hN⟩ := exists_box_superset U
  set S := siteFilter N U
  have hS : innerSet N S = U := innerSet_siteFilter hN
  set i : {z : DGFFSite N // z ∈ S} :=
    ⟨⟨a, hN ha⟩, by simp [S, siteFilter, ha]⟩
  set j : {z : DGFFSite N // z ∈ S} :=
    ⟨⟨b, hN hb⟩, by simp [S, siteFilter, hb]⟩
  have hsymm : ((boxSplitPrecision N (boxInnerOuterEquiv N S)).toBlocks₁₁)⁻¹.IsSymm := by
    apply Matrix.IsSymm.inv
    have hH : (boxConductances N).precision.IsHermitian :=
      (boxConductances N).precision_isHermitian
    unfold Matrix.IsSymm
    ext x y
    change (boxConductances N).precision y.1 x.1 = (boxConductances N).precision x.1 y.1
    have := congrFun (congrFun hH x.1) y.1
    simpa using this
  have h1 := innerBlock_inv_eq_green N S i j
  have h2 := innerBlock_inv_eq_green N S j i
  have h3 : ((boxSplitPrecision N (boxInnerOuterEquiv N S)).toBlocks₁₁)⁻¹ i j =
      ((boxSplitPrecision N (boxInnerOuterEquiv N S)).toBlocks₁₁)⁻¹ j i := by
    have := congrFun (congrFun hsymm j) i
    simpa [Matrix.transpose_apply] using this
  rw [h1, h2, hS] at h3
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  simpa [i, j] using (mul_left_cancel₀ hpi.ne' h3)

 

 


theorem harmonic_increment_variance_eq_green (n : ℕ) (S : Finset (DGFFSite n))
    (i j : {z : DGFFSite n // z ∈ S}) :
    Var[fun h : EuclideanSpace ℝ (DGFFSite n) =>
        boxHarmonicField n (boxInnerOuterEquiv n S) h i -
          boxHarmonicField n (boxInnerOuterEquiv n S) h j; boxDGFF n] =
      (Real.pi / 2) * (incr (interiorSites n) i.1.1 j.1.1 -
        incr (innerSet n S) i.1.1 j.1.1) := by
  rw [boxHarmonicField_increment_variance]
  rw [splitPrecision_inv_inl, splitPrecision_inv_inl, splitPrecision_inv_inl,
    innerBlock_inv_eq_green, innerBlock_inv_eq_green, innerBlock_inv_eq_green]
  unfold incr
  rw [green_symm (interiorSites n) j.1.1 i.1.1, green_symm (innerSet n S) j.1.1 i.1.1]
  ring

 
theorem incr_le_incr_box {N : ℕ} {V : Finset (ℤ × ℤ)} (hV : V ⊆ interiorSites N)
    {x y : ℤ × ℤ} (hx : x ∈ V) (hy : y ∈ V) :
    incr V x y ≤ incr (interiorSites N) x y := by
  classical
  set S := siteFilter N V
  have hS : innerSet N S = V := innerSet_siteFilter hV
  set i : {z : DGFFSite N // z ∈ S} := ⟨⟨x, hV hx⟩, by simp [S, siteFilter, hx]⟩
  set j : {z : DGFFSite N // z ∈ S} := ⟨⟨y, hV hy⟩, by simp [S, siteFilter, hy]⟩
  have h := harmonic_increment_variance_eq_green N S i j
  rw [hS] at h
  have hvar : 0 ≤ Var[fun h : EuclideanSpace ℝ (DGFFSite N) =>
      boxHarmonicField N (boxInnerOuterEquiv N S) h i -
        boxHarmonicField N (boxInnerOuterEquiv N S) h j; boxDGFF N] := variance_nonneg _ _
  rw [h] at hvar
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have h2 : 0 ≤ (Real.pi / 2) * (incr (interiorSites N) x y - incr V x y) := hvar
  have h3 := (mul_nonneg_iff_of_pos_left hpi).mp h2
  linarith

end SupercriticalLQGUniqueness.B2.QPos.P4
