/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3Energy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3Hitting

 












set_option autoImplicit false
noncomputable section

open Finset Matrix
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos.P3

open Classical

 
theorem precision_mulVec_eq (n : ℕ) (x : DGFFSite n → ℝ) (i : DGFFSite n) :
    ((boxConductances n).precision *ᵥ x) i =
      (boxConductances n).totalRate i *
        (x i - ∑ j, (boxConductances n).killedTransition i j * x j) := by
  rw [(boxConductances n).precision_mulVec]
  have hr := ((boxConductances n).totalRate_pos (box_hK n) i).ne'
  simp only [WiredConductances.killedTransition, WiredConductances.totalRate] at hr ⊢
  rw [mul_sub, mul_sum]
  have : ∀ j, ((boxConductances n).boundary i + ∑ k, (boxConductances n).edge i k) *
      ((boxConductances n).edge i j / ((boxConductances n).boundary i +
        ∑ k, (boxConductances n).edge i k) * x j) = (boxConductances n).edge i j * x j := by
    intro j; field_simp
  simp_rw [this, mul_sub, sum_sub_distrib, ← sum_mul]
  ring

 
theorem boundary_sum_eq_energy (n : ℕ) (T : Set (DGFFSite n)) (h : DGFFSite n → ℝ)
    (hT : ∀ y ∈ T, h y = 1)
    (hharm : ∀ y ∉ T, h y = ∑ y', (boxConductances n).killedTransition y y' * h y') :
    ∑ y, (boxConductances n).boundary y * h y = h ⬝ᵥ ((boxConductances n).precision *ᵥ h) := by
  have hterm : ∀ y, h y * ((boxConductances n).precision *ᵥ h) y =
      ((boxConductances n).precision *ᵥ h) y := by
    intro y
    by_cases hy : y ∈ T
    · rw [hT y hy, one_mul]
    · rw [precision_mulVec_eq, ← hharm y hy, sub_self, mul_zero, mul_zero]
  have h1 : h ⬝ᵥ ((boxConductances n).precision *ᵥ h) =
      (fun _ => (1 : ℝ)) ⬝ᵥ ((boxConductances n).precision *ᵥ h) := by
    simp only [dotProduct]; apply sum_congr rfl; intro y _; rw [hterm y, one_mul]
  have hsymm : vecMul (fun _ => (1 : ℝ)) (boxConductances n).precision =
      (boxConductances n).precision *ᵥ (fun _ => (1 : ℝ)) := by
    have hK : (boxConductances n).precisionᵀ = (boxConductances n).precision := by
      have := (boxConductances n).precision_isHermitian.eq
      rwa [conjTranspose_eq_transpose_of_trivial] at this
    conv_lhs => rw [← hK]
    exact vecMul_transpose _ _
  rw [h1, dotProduct_mulVec, hsymm]
  simp only [dotProduct]
  apply sum_congr rfl; intro i _
  rw [(boxConductances n).precision_mulVec_one]

theorem boundary_ge_of_right (n : ℕ) (z : DGFFSite n) (hz : z.1.1 = interiorRadius n) :
    dgffConductance ≤ (boxConductances n).boundary z := by
  change dgffConductance ≤ boxBoundaryConductance n z
  unfold boxBoundaryConductance
  rw [if_pos hz]
  have hc := dgffConductance_pos
  have : (0 : ℝ) ≤ (if z.1.1 = -interiorRadius n then 1 else 0) +
      (if z.1.2 = -interiorRadius n then 1 else 0) + (if z.1.2 = interiorRadius n then 1 else 0) := by
    positivity
  nlinarith

theorem edge_of_adjacent (n : ℕ) (z w : DGFFSite n) (h : latticeAdjacent z.1 w.1) :
    (boxConductances n).edge z w = dgffConductance := by
  change (if latticeAdjacent z.1 w.1 then dgffConductance else 0) = _
  rw [if_pos h]

 

 
def extZ {n : ℕ} (v : DGFFSite n → ℝ) (z : ℤ × ℤ) : ℝ :=
  if h : z ∈ interiorSites n then v ⟨z, h⟩ else 0

theorem mem_interior_iff (n : ℕ) (z : ℤ × ℤ) :
    z ∈ interiorSites n ↔ -interiorRadius n ≤ z.1 ∧ z.1 ≤ interiorRadius n ∧
      -interiorRadius n ≤ z.2 ∧ z.2 ≤ interiorRadius n := by
  simp [interiorSites, Finset.mem_product, Finset.mem_Icc, and_assoc]

 
def siteOf (n : ℕ) (z : ℤ × ℤ) : DGFFSite n :=
  if h : z ∈ interiorSites n then ⟨z, h⟩ else
    ⟨(0, 0), (mem_interior_iff n _).mpr (by
      have : (0 : ℤ) ≤ interiorRadius n := by
        unfold interiorRadius; have : (1 : ℤ) ≤ 2 ^ n := one_le_pow₀ (by norm_num); omega
      simp only; omega)⟩

theorem siteOf_val (n : ℕ) {z : ℤ × ℤ} (hz : z ∈ interiorSites n) : (siteOf n z).1 = z := by
  simp [siteOf, hz]

theorem v_siteOf {n : ℕ} (v : DGFFSite n → ℝ) {z : ℤ × ℤ} (hz : z ∈ interiorSites n) :
    v (siteOf n z) = extZ v z := by
  simp [siteOf, extZ, hz]

attribute [irreducible] siteOf extZ

 
theorem row_bound (a : ℕ → ℝ) (M : ℕ) (h0 : a 0 = 1) :
    1 / ((M : ℝ) + 1) ≤ ∑ t ∈ range M, (a t - a (t + 1)) ^ 2 + a M ^ 2 := by
  set g : ℕ → ℝ := fun t => if t < M then a t - a (t + 1) else a M with hg
  have hsum : ∑ t ∈ range (M + 1), g t = 1 := by
    rw [sum_range_succ]
    have : ∑ t ∈ range M, g t = ∑ t ∈ range M, (a t - a (t + 1)) := by
      apply sum_congr rfl; intro t ht; simp [hg, mem_range.mp ht]
    rw [this, sum_range_sub', hg]; simp [h0]
  have hsq : ∑ t ∈ range (M + 1), g t ^ 2 = ∑ t ∈ range M, (a t - a (t + 1)) ^ 2 + a M ^ 2 := by
    rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl; intro t ht; simp [hg, mem_range.mp ht]
    · simp [hg]
  have hcs := sq_sum_le_card_mul_sum_sq (s := range (M + 1)) (f := g)
  rw [hsum, card_range, hsq] at hcs
  rw [div_le_iff₀ (by positivity)]
  push_cast at hcs
  linarith

 

theorem energy_lower (n : ℕ) (hn : 17 ≤ n) (v : DGFFSite n → ℝ)
    (hv : ∀ x : DGFFSite n, InTarget n x.1 → v x = 1) :
    dgffConductance / 21 ≤ v ⬝ᵥ ((boxConductances n).precision *ᵥ v) := by
  rw [(boxConductances n).precision_energy]
  set ℓ : ℤ := 1024 * ((2 ^ (n - 16) : ℕ) : ℤ) with hℓ
  have hℓ1 : 1024 ≤ ℓ := by
    have : (1 : ℤ) ≤ ((2 ^ (n - 16) : ℕ) : ℤ) := by exact_mod_cast Nat.one_le_two_pow
    omega
  have hR : interiorRadius n = 64 * ℓ - 1 := by
    rw [interiorRadius_eq n (by omega), hℓ]; ring
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = 21 * ℓ - 1 := ⟨(21 * ℓ - 1).toNat, by omega⟩
  set c := dgffConductance with hc
  have hc0 : 0 < c := dgffConductance_pos
  let pt : ℤ → ℕ → ℤ × ℤ := fun r t => (43 * ℓ + t, r)
  have hpt : ∀ r ∈ Icc (-ℓ) ℓ, ∀ t ≤ M, pt r t ∈ interiorSites n := by
    intro r hr t ht
    rw [mem_Icc] at hr
    have : (t : ℤ) ≤ M := by exact_mod_cast ht
    rw [mem_interior_iff, hR]; simp only [pt]; omega
  have hlast : ∀ r, pt r M = (interiorRadius n, r) := by
    intro r; simp only [pt, hR]; ext <;> simp <;> omega
  
  have hA : ∑ r ∈ Icc (-ℓ) ℓ, c * extZ v (pt r M) ^ 2 ≤
      ∑ i, (boxConductances n).boundary i * v i ^ 2 := by
    have hinj : Set.InjOn (fun r => siteOf n (pt r M)) (Icc (-ℓ) ℓ) := by
      intro r hr r' hr' h
      have := congrArg Subtype.val h
      rw [siteOf_val n (hpt r hr M le_rfl), siteOf_val n (hpt r' hr' M le_rfl)] at this
      simpa [pt] using this
    calc ∑ r ∈ Icc (-ℓ) ℓ, c * extZ v (pt r M) ^ 2
        ≤ ∑ r ∈ Icc (-ℓ) ℓ, (boxConductances n).boundary (siteOf n (pt r M)) *
            v (siteOf n (pt r M)) ^ 2 := by
          apply sum_le_sum; intro r hr
          rw [v_siteOf v (hpt r hr M le_rfl)]
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          apply boundary_ge_of_right
          rw [siteOf_val n (hpt r hr M le_rfl), hlast]
      _ = ∑ i ∈ (Icc (-ℓ) ℓ).image (fun r => siteOf n (pt r M)),
            (boxConductances n).boundary i * v i ^ 2 :=
          (sum_image (f := fun i => (boxConductances n).boundary i * v i ^ 2) hinj).symm
      _ ≤ ∑ i, (boxConductances n).boundary i * v i ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ =>
            mul_nonneg ((boxConductances n).boundary_nonneg i) (sq_nonneg _))
  
  have hB : ∑ r ∈ Icc (-ℓ) ℓ, ∑ t ∈ range M, c * (extZ v (pt r t) - extZ v (pt r (t + 1))) ^ 2 ≤
      ∑ i, ∑ j, (boxConductances n).edge i j * (v i - v j) ^ 2 := by
    obtain ⟨S, hS⟩ : ∃ S : Finset (ℤ × ℕ), S = (Icc (-ℓ) ℓ) ×ˢ (range M) := ⟨_, rfl⟩
    let e : ℤ × ℕ → DGFFSite n × DGFFSite n :=
      fun q => (siteOf n (pt q.1 q.2), siteOf n (pt q.1 (q.2 + 1)))
    have hmem : ∀ q ∈ S, pt q.1 q.2 ∈ interiorSites n ∧ pt q.1 (q.2 + 1) ∈ interiorSites n := by
      intro q hq
      rw [hS, mem_product, mem_range] at hq
      exact ⟨hpt q.1 hq.1 q.2 hq.2.le, hpt q.1 hq.1 (q.2 + 1) hq.2⟩
    have hinj : Set.InjOn e (S : Set (ℤ × ℕ)) := by
      intro q hq q' hq' h
      have h1 := congrArg (fun p => p.1.1) h
      simp only [e] at h1
      rw [siteOf_val n (hmem q hq).1, siteOf_val n (hmem q' hq').1] at h1
      simp only [pt, Prod.mk.injEq] at h1
      ext
      · exact h1.2
      · omega
    have hF : ∀ q ∈ S, c * (extZ v (pt q.1 q.2) - extZ v (pt q.1 (q.2 + 1))) ^ 2 =
        (boxConductances n).edge (e q).1 (e q).2 * (v (e q).1 - v (e q).2) ^ 2 := by
      intro q hq
      obtain ⟨h1, h2⟩ := hmem q hq
      simp only [e]
      rw [v_siteOf v h1, v_siteOf v h2, edge_of_adjacent]
      rw [siteOf_val n h1, siteOf_val n h2]
      simp only [latticeAdjacent, pt]; left; refine ⟨?_, trivial⟩; push_cast; ring
    have e1 : ∑ r ∈ Icc (-ℓ) ℓ, ∑ t ∈ range M, c * (extZ v (pt r t) - extZ v (pt r (t + 1))) ^ 2 =
        ∑ q ∈ S, c * (extZ v (pt q.1 q.2) - extZ v (pt q.1 (q.2 + 1))) ^ 2 := by
      rw [hS, sum_product]
    have e2 : ∑ q ∈ S, (boxConductances n).edge (e q).1 (e q).2 * (v (e q).1 - v (e q).2) ^ 2 =
        ∑ p ∈ S.image e, (boxConductances n).edge p.1 p.2 * (v p.1 - v p.2) ^ 2 :=
      (sum_image (f := fun p => (boxConductances n).edge p.1 p.2 * (v p.1 - v p.2) ^ 2) hinj).symm
    have e3 : ∑ p ∈ S.image e, (boxConductances n).edge p.1 p.2 * (v p.1 - v p.2) ^ 2 ≤
        ∑ p : DGFFSite n × DGFFSite n, (boxConductances n).edge p.1 p.2 * (v p.1 - v p.2) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun p _ _ =>
        mul_nonneg ((boxConductances n).edge_nonneg _ _) (sq_nonneg _))
    have e4 : ∑ p : DGFFSite n × DGFFSite n, (boxConductances n).edge p.1 p.2 * (v p.1 - v p.2) ^ 2 =
        ∑ i, ∑ j, (boxConductances n).edge i j * (v i - v j) ^ 2 :=
      Fintype.sum_prod_type _
    rw [e1, sum_congr rfl hF, e2, ← e4]
    exact e3
  
  have hrow : ∀ r ∈ Icc (-ℓ) ℓ, 1 / ((M : ℝ) + 1) ≤
      ∑ t ∈ range M, (extZ v (pt r t) - extZ v (pt r (t + 1))) ^ 2 + extZ v (pt r M) ^ 2 := by
    intro r hr
    apply row_bound (fun t => extZ v (pt r t)) M
    have hm := hpt r hr 0 (Nat.zero_le _)
    rw [← v_siteOf v hm]
    apply hv
    rw [siteOf_val n hm]
    rw [mem_Icc] at hr
    show 41 * ℓ ≤ (pt r 0).1 ∧ (pt r 0).1 ≤ 43 * ℓ ∧ |(pt r 0).2| ≤ ℓ
    simp only [pt, CharP.cast_eq_zero, add_zero]
    refine ⟨by omega, le_rfl, ?_⟩
    rw [abs_le]; exact ⟨hr.1, hr.2⟩
  have hcard : ((Icc (-ℓ) ℓ).card : ℝ) = 2 * ℓ + 1 := by
    have h1 : ((Icc (-ℓ) ℓ).card : ℤ) = 2 * ℓ + 1 := by rw [Int.card_Icc]; omega
    exact_mod_cast h1
  have hMR : ((M : ℝ) + 1) = 21 * (ℓ : ℝ) := by
    have : ((M : ℤ) : ℝ) = 21 * (ℓ : ℝ) - 1 := by rw [hM]; push_cast; ring
    push_cast at this; linarith
  have hℓR : (1024 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  
  have hsumrow : (2 * (ℓ : ℝ) + 1) * (1 / ((M : ℝ) + 1)) ≤
      ∑ r ∈ Icc (-ℓ) ℓ, (∑ t ∈ range M, (extZ v (pt r t) - extZ v (pt r (t + 1))) ^ 2 +
        extZ v (pt r M) ^ 2) := by
    rw [← hcard, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hrow
  have hfinal : c / 21 ≤ c / 2 * ((2 * (ℓ : ℝ) + 1) * (1 / ((M : ℝ) + 1))) := by
    rw [hMR]
    have hpos : (0 : ℝ) < 21 * ℓ := by positivity
    rw [show (2 * (ℓ : ℝ) + 1) * (1 / (21 * ℓ)) = (2 * ℓ + 1) / (21 * ℓ) by ring]
    rw [show c / 2 * ((2 * (ℓ : ℝ) + 1) / (21 * ℓ)) = c * (2 * ℓ + 1) / (42 * ℓ) by
      field_simp; ring]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hsplit : ∑ r ∈ Icc (-ℓ) ℓ, (∑ t ∈ range M, (extZ v (pt r t) - extZ v (pt r (t + 1))) ^ 2 +
        extZ v (pt r M) ^ 2) * (c / 2) ≤
      ∑ r ∈ Icc (-ℓ) ℓ, c * extZ v (pt r M) ^ 2 +
        1 / 2 * ∑ r ∈ Icc (-ℓ) ℓ, ∑ t ∈ range M,
          c * (extZ v (pt r t) - extZ v (pt r (t + 1))) ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum; intro r _
    rw [mul_sum]
    have : 0 ≤ c * extZ v (pt r M) ^ 2 := mul_nonneg hc0.le (sq_nonneg _)
    have e1 : (∑ t ∈ range M, (extZ v (pt r t) - extZ v (pt r (t + 1))) ^ 2 +
        extZ v (pt r M) ^ 2) * (c / 2) =
        ∑ t ∈ range M, 1 / 2 * (c * (extZ v (pt r t) - extZ v (pt r (t + 1))) ^ 2) +
          c / 2 * extZ v (pt r M) ^ 2 := by
      rw [add_mul, sum_mul]; congr 1
      · apply sum_congr rfl; intro t _; ring
      · ring
    rw [e1]; linarith
  calc c / 21 ≤ c / 2 * ((2 * (ℓ : ℝ) + 1) * (1 / ((M : ℝ) + 1))) := hfinal
    _ ≤ c / 2 * ∑ r ∈ Icc (-ℓ) ℓ, (∑ t ∈ range M,
          (extZ v (pt r t) - extZ v (pt r (t + 1))) ^ 2 + extZ v (pt r M) ^ 2) :=
        mul_le_mul_of_nonneg_left hsumrow (by positivity)
    _ = ∑ r ∈ Icc (-ℓ) ℓ, (∑ t ∈ range M,
          (extZ v (pt r t) - extZ v (pt r (t + 1))) ^ 2 + extZ v (pt r M) ^ 2) * (c / 2) := by
        rw [mul_comm, sum_mul]
    _ ≤ _ := hsplit
    _ ≤ _ := by
        apply add_le_add hA
        exact mul_le_mul_of_nonneg_left hB (by norm_num)

end SupercriticalLQGUniqueness.B2.QPos.P3
