import LatticeProb.Analysis.Elliptic.HolderCompositionConvex

/-!
# Hölder composition on open sets

A coordinate composition estimate with explicit lower-order Hölder bounds.
-/

namespace LatticeProb.Elliptic

open scoped ENNReal BigOperators Topology

noncomputable section

variable {d : ℕ} {σ : ℝ} {S T : Set (Fin d → ℝ)} {u : (Fin d → ℝ) → ℝ}
  {φ : (Fin d → ℝ) → (Fin d → ℝ)}

/-- Hölder increments of a composed Hessian are controlled by the two component norms. -/
theorem abs_sub_secondPartial_comp_le_of_first_holder (hσ : 0 < σ)
    (hS : IsOpen S) (hT : IsOpen T)
    (hφ : ContDiffOn ℝ 2 φ S) (hu : ContDiffOn ℝ 2 u T) (hmap : Set.MapsTo φ S T)
    (hn : c2HolderNorm σ T u < ⊤) {M : ℝ} (hM : 0 ≤ M)
    (hφbound : ∀ k, (c2HolderNorm σ S (fun y => φ y k)).toReal ≤ M)
    (hφn : ∀ k, c2HolderNorm σ S (fun y => φ y k) < ⊤)
    (hφfirst : ∀ k a, holderSeminorm σ S (partialDeriv a (fun w => φ w k)) < ⊤)
    (hφfirstbound : ∀ k a, (holderSeminorm σ S (partialDeriv a (fun w => φ w k))).toReal ≤ M)
    {A : ℝ} (hA : 0 ≤ A)
    (hufirst : ∀ k, holderSeminorm σ T (partialDeriv k u) ≤
      ENNReal.ofReal A * c2HolderNorm σ T u)
    {K : NNReal} (hLip : LipschitzOnWith K φ S)
    {x y : Fin d → ℝ} (hx : x ∈ S) (hy : y ∈ S) (i j : Fin d) :
    |secondPartial j i (u ∘ φ) x - secondPartial j i (u ∘ φ) y| ≤
      ((d : ℝ) ^ 2 * (M ^ 2 *
          ((‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * K) ^ σ + 2)) +
        d * M * (A *
          (‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * K) ^ σ + 1)) *
      (c2HolderNorm σ T u).toReal * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := by
  let N := (c2HolderNorm σ T u).toReal
  let Q : ℝ := (‖(PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * K) ^ σ
  let R := LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hR : 0 ≤ R := Real.rpow_nonneg (LatticeProb.Euclidean.Lattice.radius_nonneg _) _
  have hp (k a : Fin d) (z : Fin d → ℝ) (hz : z ∈ S) :
      |partialDeriv a (fun w => φ w k) z| ≤ M :=
    (abs_partialDeriv_le_c2HolderNorm_toReal (hφn k) a hz).trans (hφbound k)
  have hs (k a b : Fin d) (z : Fin d → ℝ) (hz : z ∈ S) :
      |secondPartial a b (fun w => φ w k) z| ≤ M :=
    (abs_secondPartial_le_c2HolderNorm_toReal (hφn k) a b hz).trans (hφbound k)
  have hpi (k a : Fin d) : |partialDeriv a (fun w => φ w k) x -
      partialDeriv a (fun w => φ w k) y| ≤ M * R := by
    have hfinite : c0HolderNorm σ S (partialDeriv a (fun w => φ w k)) < ⊤ := by
      simp only [c0HolderNorm, ENNReal.add_lt_top]
      exact ⟨lt_of_le_of_lt (partialDeriv_supNorm_le_c2HolderNorm a) (hφn k), hφfirst k a⟩
    exact (abs_sub_le_holderSeminorm_toReal hfinite hx hy).trans
      (mul_le_mul_of_nonneg_right (hφfirstbound k a) hR)
  have hsi (k a b : Fin d) : |secondPartial a b (fun w => φ w k) x -
      secondPartial a b (fun w => φ w k) y| ≤ M * R := by
    exact (abs_sub_secondPartial_le_c2HolderNorm_toReal (hφn k) a b hx hy).trans
      (mul_le_mul_of_nonneg_right (hφbound k) hR)
  have houter1 (k : Fin d) : |partialDeriv k u (φ x) - partialDeriv k u (φ y)| ≤
      (A * N * Q) * R := by
    have hfinite : c0HolderNorm σ T (partialDeriv k u) < ⊤ := by
      simp only [c0HolderNorm, ENNReal.add_lt_top]
      exact ⟨lt_of_le_of_lt (partialDeriv_supNorm_le_c2HolderNorm k) hn,
        lt_of_le_of_lt (hufirst k) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hn)⟩
    have hbound : (holderSeminorm σ T (partialDeriv k u)).toReal ≤ A * N := by
      calc
        _ ≤ (ENNReal.ofReal A * c2HolderNorm σ T u).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hn.ne) (hufirst k)
        _ = A * N := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA]
    apply abs_sub_comp_le_of_holder_bound hσ.le (mul_nonneg hA hN) _ hmap hLip hx hy
    intro x hx y hy
    exact (abs_sub_le_holderSeminorm_toReal hfinite hx hy).trans
      (mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg
        (LatticeProb.Euclidean.Lattice.radius_nonneg _) _))
  have houter2 (k l : Fin d) : |secondPartial l k u (φ x) - secondPartial l k u (φ y)| ≤
      (N * Q) * R := by
    exact abs_sub_comp_le_of_holder_bound hσ.le hN
      (fun _ hx' _ hy' => abs_sub_secondPartial_le_c2HolderNorm_toReal hn l k hx' hy')
      hmap hLip hx hy
  have hprod3 (k l : Fin d) :
      |secondPartial l k u (φ x) * partialDeriv j (fun w => φ w l) x *
          partialDeriv i (fun w => φ w k) x -
        secondPartial l k u (φ y) * partialDeriv j (fun w => φ w l) y *
          partialDeriv i (fun w => φ w k) y| ≤
      (((N * Q) * M + N * M) * M + N * M * M) * R := by
    apply abs_mul_mul_sub_mul_mul_le_of_bounds hN hM (mul_nonneg hN hQ)
      hM hR
    · exact abs_secondPartial_le_c2HolderNorm_toReal hn l k (hmap hx)
    · exact hp l j x hx
    · exact hp l j y hy
    · exact hp k i y hy
    · exact houter2 k l
    · exact hpi l j
    · exact hpi k i
  have hprod2 (k : Fin d) :
      |partialDeriv k u (φ x) * secondPartial j i (fun w => φ w k) x -
        partialDeriv k u (φ y) * secondPartial j i (fun w => φ w k) y| ≤
      ((A * N * Q) * M + N * M) * R := by
    exact abs_mul_sub_mul_le_of_bounds (by positivity) hR hN
      (abs_partialDeriv_le_c2HolderNorm_toReal hn k (hmap hx)) (hs k j i y hy)
      (houter1 k) (hsi k j i)
  rw [secondPartial_comp hS hT hφ hu hmap hx i j,
    secondPartial_comp hS hT hφ hu hmap hy i j, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k, |((∑ l, secondPartial l k u (φ x) *
        partialDeriv j (fun w => φ w l) x) * partialDeriv i (fun w => φ w k) x +
        partialDeriv k u (φ x) * secondPartial j i (fun w => φ w k) x) -
        ((∑ l, secondPartial l k u (φ y) *
        partialDeriv j (fun w => φ w l) y) * partialDeriv i (fun w => φ w k) y +
        partialDeriv k u (φ y) * secondPartial j i (fun w => φ w k) y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, ((d : ℝ) *
        ((((N * Q) * M + N * M) * M + N * M * M) * R) +
          ((A * N * Q) * M + N * M) * R) := by
      apply Finset.sum_le_sum
      intro k _
      have hsum : |(∑ l, secondPartial l k u (φ x) *
          partialDeriv j (fun w => φ w l) x) * partialDeriv i (fun w => φ w k) x -
          (∑ l, secondPartial l k u (φ y) *
          partialDeriv j (fun w => φ w l) y) * partialDeriv i (fun w => φ w k) y| ≤
          (d : ℝ) * ((((N * Q) * M + N * M) * M + N * M * M) * R) := by
        simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact (Finset.abs_sum_le_sum_abs _ _).trans (by
          calc
            _ ≤ ∑ _l : Fin d, ((((N * Q) * M + N * M) * M + N * M * M) * R) :=
              Finset.sum_le_sum fun l _ => hprod3 k l
            _ = _ := by simp)
      have hsplit : ∀ a b c e : ℝ, |(a + b) - (c + e)| ≤ |a - c| + |b - e| := by
        intro a b c e
        have hid : (a + b) - (c + e) = (a - c) + (b - e) := by ring
        rw [hid]
        exact abs_add_le _ _
      exact (hsplit _ _ _ _).trans (add_le_add hsum (hprod2 k))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; dsimp [N, Q, R]; ring


/-- A smooth coordinate change with bounded Hölder norm acts boundedly on `C^{2,σ}`. -/
theorem c2HolderNorm_comp_of_first_holder {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (_hσ' : σ < 1)
    (S T : Set (Fin d → ℝ)) (hS : IsOpen S) (hT : IsOpen T)
    (φ : (Fin d → ℝ) → Fin d → ℝ)
    (hφ : ContDiffOn ℝ 2 φ S) (hmap : Set.MapsTo φ S T)
    (hφn : ∀ i, c2HolderNorm σ S (fun x => φ x i) < ⊤)
    (hφfirst : ∀ i j, holderSeminorm σ S (partialDeriv j (fun x => φ x i)) < ⊤)
    (K : NNReal) (hLip : LipschitzOnWith K φ S) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ 2 u T → c2HolderNorm σ T u < ⊤ →
      (∀ i, holderSeminorm σ T (partialDeriv i u) ≤
        ENNReal.ofReal A * c2HolderNorm σ T u) →
      ContDiffOn ℝ 2 (u ∘ φ) S ∧
      c2HolderNorm σ S (u ∘ φ) ≤ ENNReal.ofReal C * c2HolderNorm σ T u := by
  let M : ℝ := 1 + (∑ k : Fin d, (c2HolderNorm σ S (fun y => φ y k)).toReal) +
    ∑ k : Fin d, ∑ a : Fin d, (holderSeminorm σ S (partialDeriv a (fun y => φ y k))).toReal
  let Q : ℝ := (‖(PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * K) ^ σ
  let P₁ : ℝ := d * M
  let P₂ : ℝ := (d : ℝ) ^ 2 * M ^ 2 + d * M
  let P₃ : ℝ := (d : ℝ) ^ 2 * (M ^ 2 * (Q + 2)) +
    d * M * (A * Q + 1)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hP₁ : 0 ≤ P₁ := by dsimp [P₁]; positivity
  have hP₂ : 0 ≤ P₂ := by dsimp [P₂]; positivity
  have hP₃ : 0 ≤ P₃ := by dsimp [P₃]; positivity
  have hbound (k : Fin d) : (c2HolderNorm σ S (fun y => φ y k)).toReal ≤ M := by
    have h := Finset.single_le_sum (f := fun l : Fin d =>
      (c2HolderNorm σ S (fun y => φ y l)).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ k)
    dsimp [M]
    have hs : 0 ≤ ∑ k : Fin d, ∑ a : Fin d,
        (holderSeminorm σ S (partialDeriv a (fun y => φ y k))).toReal := by positivity
    linarith
  have hfirstbound (k a : Fin d) :
      (holderSeminorm σ S (partialDeriv a (fun y => φ y k))).toReal ≤ M := by
    have ha := Finset.single_le_sum (f := fun b : Fin d =>
      (holderSeminorm σ S (partialDeriv b (fun y => φ y k))).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ a)
    have hk := Finset.single_le_sum (f := fun l : Fin d => ∑ b : Fin d,
      (holderSeminorm σ S (partialDeriv b (fun y => φ y l))).toReal)
      (fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ k)
    have hs : 0 ≤ ∑ k : Fin d, (c2HolderNorm σ S (fun y => φ y k)).toReal := by positivity
    dsimp [M]
    linarith
  let C : ℝ := 1 + (∑ _ : Fin d, P₁) + (∑ _ : Fin d, ∑ _ : Fin d, P₂) +
    (∑ _ : Fin d, ∑ _ : Fin d, P₃)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun u hu hn hufirst => ⟨hu.comp hφ hmap, ?_⟩⟩
  let N := (c2HolderNorm σ T u).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hb := c2HolderNorm_le_of_bounds (σ := σ) (S := S) (u := u ∘ φ)
    (B₀ := N) (B₁ := P₁ * N) (B₂ := P₂ * N) (H := P₃ * N)
    (fun x hx => abs_le_c2HolderNorm_toReal hn (hmap hx))
    (fun i x hx => abs_partialDeriv_comp_le hS hT hφ hu hmap hn hbound hφn hx i)
    (fun i j x hx => by
      simpa only using abs_secondPartial_comp_le hS hT hφ hu hmap hn hM hbound hφn hx j i)
    (fun i j x hx y hy => by
      simpa only using abs_sub_secondPartial_comp_le_of_first_holder hσ hS hT
        hφ hu hmap hn hM hbound hφn hφfirst hfirstbound hA.le hufirst hLip hx hy j i)
  have hcoef : ENNReal.ofReal C = 1 + (∑ _ : Fin d, ENNReal.ofReal P₁) +
      (∑ _ : Fin d, ∑ _ : Fin d, ENNReal.ofReal P₂) +
      (∑ _ : Fin d, ∑ _ : Fin d, ENNReal.ofReal P₃) := by
    dsimp [C]
    have hsum₁ : 0 ≤ ∑ _ : Fin d, P₁ := Finset.sum_nonneg fun _ _ => hP₁
    have hsum₂ : 0 ≤ ∑ _ : Fin d, ∑ _ : Fin d, P₂ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hP₂
    have hsum₃ : 0 ≤ ∑ _ : Fin d, ∑ _ : Fin d, P₃ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hP₃
    rw [ENNReal.ofReal_add (add_nonneg (add_nonneg (by norm_num) hsum₁) hsum₂) hsum₃,
      ENNReal.ofReal_add (add_nonneg (by norm_num) hsum₁) hsum₂,
      ENNReal.ofReal_add (by norm_num) hsum₁]
    simp only [ENNReal.ofReal_one, ENNReal.ofReal_sum_of_nonneg (fun _ _ => hP₁),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => hP₂),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => hP₃),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => hP₂),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => hP₃)]
  calc
    _ ≤ ENNReal.ofReal N + (∑ _ : Fin d, ENNReal.ofReal (P₁ * N)) +
        (∑ _ : Fin d, ∑ _ : Fin d, ENNReal.ofReal (P₂ * N)) +
        (∑ _ : Fin d, ∑ _ : Fin d, ENNReal.ofReal (P₃ * N)) := hb
    _ = ENNReal.ofReal C * c2HolderNorm σ T u := by
      rw [hcoef]
      dsimp only [N]
      simp only [ENNReal.ofReal_mul hP₁, ENNReal.ofReal_mul hP₂, ENNReal.ofReal_mul hP₃,
        ENNReal.ofReal_toReal hn.ne, one_mul, add_mul, Finset.sum_mul]


end

end LatticeProb.Elliptic
