import LatticeProb.External.GilbargTrudinger

/-!
# Interior cutoff for coordinate `C^{2,σ}` norms

For a compact set `K` inside an open set `U`, multiplication by a smooth cutoff equal to one on
`K` and supported in a fixed closed thickening of `K` turns a function with finite coordinate
`C^{2,σ}` norm on `U` into a compactly supported `C²` function on the whole space. Its
whole-space `C^{2,σ}` norm is bounded by a constant multiple of the norm on `U`, and the constant
depends only on `σ`, `U` and `K`. This is the localization step of Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Section 6.1 and Lemma 6.37
(printed pp. 136–137).

The first and second coordinate derivatives of the product are expanded by the Leibniz rule.
For the Hölder quotient of a second derivative, a pair of nearby points with one point in the
support of the cutoff lies in a ball inside `U`, where the mean value inequality controls the
function and its first derivatives; a pair of distant points is bounded by twice the supremum.
-/

namespace LatticeProb.Elliptic.HolderExtension

open LatticeProb.Euclidean.Lattice
open scoped ENNReal ContDiff Manifold Topology

noncomputable section

namespace InteriorCutoff

variable {d : ℕ}

/-- The sup norm on coordinates is bounded by the Euclidean radius. -/
theorem norm_le_radius (v : Fin d → ℝ) : ‖v‖ ≤ radius v :=
  (pi_norm_le_iff_of_nonneg (radius_nonneg v)).2 fun k => by
    simpa [Real.norm_eq_abs] using abs_coord_le_radius v k

/-- The Euclidean radius of a difference is symmetric. -/
theorem radius_sub_comm (x y : Fin d → ℝ) : radius (x - y) = radius (y - x) := by
  simp only [radius, Pi.sub_apply]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- A smooth cutoff equal to one on a compact set, supported in its closed `δ`-thickening. -/
theorem exists_smooth_cutoff (K : Set (Fin d → ℝ)) (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ χ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ χ ∧ Set.EqOn χ 1 K ∧
      tsupport χ ⊆ Metric.cthickening δ K := by
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, Fin d → ℝ)
    (n := ⊤) (Metric.isOpen_thickening (δ := δ) (E := K)).isClosed_compl hK.isClosed
    (Set.disjoint_compl_left_iff_subset.2 (Metric.self_subset_thickening hδ K))
  refine ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, hf1, ?_⟩
  refine (closure_mono ?_).trans (Metric.closure_thickening_subset_cthickening δ K)
  intro x hx
  by_contra h
  exact hx (hf0 h)

/-- A second coordinate derivative is the iterated first coordinate derivative. -/
theorem secondPartial_eq_partialDeriv {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (i j : Fin d)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    secondPartial i j f x = partialDeriv i (partialDeriv j f) x := by
  have h : partialDeriv j f = fun y => fderiv ℝ f y (Pi.single j 1) := rfl
  simp only [secondPartial, partialDeriv, iteratedFDeriv_two_apply, h]
  rw [fderiv_clm_apply hf (differentiableAt_const _)]
  simp

/-- The Leibniz rule for a coordinate derivative. -/
theorem partialDeriv_mul {f g : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (i : Fin d)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialDeriv i (fun y => f y * g y) x =
      f x * partialDeriv i g x + partialDeriv i f x * g x := by
  simp only [partialDeriv, fderiv_fun_mul hf hg]
  simp [mul_comm]

/-- A coordinate derivative is additive at a point of differentiability. -/
theorem partialDeriv_add {f g : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (i : Fin d)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialDeriv i (fun y => f y + g y) x = partialDeriv i f x + partialDeriv i g x := by
  simp only [partialDeriv, fderiv_fun_add hf hg]
  simp

/-- A coordinate derivative vanishes outside the topological support. -/
theorem partialDeriv_eq_zero_of_notMem {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (i : Fin d)
    (hx : x ∉ tsupport f) : partialDeriv i f x = 0 := by
  have : fderiv ℝ f x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_fderiv_subset ℝ h)
  simp [partialDeriv, this]

/-- A coordinate derivative is supported in the topological support of the function. -/
theorem tsupport_partialDeriv_subset (i : Fin d) (f : (Fin d → ℝ) → ℝ) :
    tsupport (partialDeriv i f) ⊆ tsupport f :=
  (tsupport_comp_subset (g := fun L : (Fin d → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) (by simp)
    (fderiv ℝ f)).trans (tsupport_fderiv_subset ℝ)

/-- A coordinate derivative of a smooth function is smooth. -/
theorem contDiff_partialDeriv {f : (Fin d → ℝ) → ℝ} (i : Fin d) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (partialDeriv i f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- A coordinate derivative of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_partialDeriv {f : (Fin d → ℝ) → ℝ} (i : Fin d)
    (hf : HasCompactSupport f) : HasCompactSupport (partialDeriv i f) :=
  IsCompact.of_isClosed_subset hf (isClosed_tsupport _) (tsupport_partialDeriv_subset i f)

/-- The operator norm of a linear form is at most the sum of its values on the basis. -/
theorem norm_le_sum_abs_apply_single (L : (Fin d → ℝ) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ k, |L (Pi.single k 1)| := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun h => ?_
  have hh : h = ∑ k, h k • (Pi.single k (1 : ℝ) : Fin d → ℝ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  calc ‖L h‖ = |∑ k, h k * L (Pi.single k 1)| := by
        conv_lhs => rw [hh]
        simp [map_sum, Real.norm_eq_abs]
    _ ≤ ∑ k, |h k| * |L (Pi.single k 1)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp [abs_mul]
    _ ≤ ∑ k, ‖h‖ * |L (Pi.single k 1)| := by
        gcongr with k
        simpa [Real.norm_eq_abs] using norm_le_pi_norm h k
    _ = (∑ k, |L (Pi.single k 1)|) * ‖h‖ := by
        rw [← Finset.mul_sum, mul_comm]

/-- The mean value inequality on a convex set, with coordinate derivative bounds and the
Euclidean radius. -/
theorem abs_sub_le_of_partialDeriv {g : (Fin d → ℝ) → ℝ} {s : Set (Fin d → ℝ)}
    (hs : Convex ℝ s) (hg : ∀ z ∈ s, DifferentiableAt ℝ g z) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z ∈ s, ∀ k, |partialDeriv k g z| ≤ M) {x y : Fin d → ℝ} (hx : x ∈ s)
    (hy : y ∈ s) : |g x - g y| ≤ d * M * radius (x - y) := by
  have hbound : ∀ z ∈ s, ‖fderiv ℝ g z‖ ≤ d * M := fun z hz => by
    refine (norm_le_sum_abs_apply_single _).trans ?_
    have := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hb z hz k
    simpa [partialDeriv] using this
  have := hs.norm_image_sub_le_of_norm_fderiv_le hg hbound hy hx
  rw [Real.norm_eq_abs] at this
  exact this.trans (mul_le_mul_of_nonneg_left (norm_le_radius _) (by positivity))

/-- The increment of a product, bounded by the increments and sizes of its factors. -/
theorem abs_mul_sub_mul_le {a₁ a₂ b₁ b₂ A Ha Mb Hb : ℝ} (h₁ : |a₁| ≤ A) (h₂ : |a₁ - a₂| ≤ Ha)
    (h₃ : |b₂| ≤ Mb) (h₄ : |b₁ - b₂| ≤ Hb) : |a₁ * b₁ - a₂ * b₂| ≤ A * Hb + Mb * Ha := by
  have : a₁ * b₁ - a₂ * b₂ = a₁ * (b₁ - b₂) + b₂ * (a₁ - a₂) := by ring
  rw [this]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_mul h₁ h₄ (abs_nonneg _) ((abs_nonneg _).trans h₁)
  · exact mul_le_mul h₃ h₂ (abs_nonneg _) ((abs_nonneg _).trans h₃)

end InteriorCutoff

open InteriorCutoff

/-- Gilbarg–Trudinger, Lemma 6.37 (localization): a compactly contained interior piece of a
function with finite `C^{2,σ}` norm on an open set is cut off to a compactly supported `C²`
function on the whole space, equal to the function on the piece, with whole-space `C^{2,σ}` norm
bounded by a constant independent of the function times the norm on the open set. -/
theorem interior_cutoff {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (hσ' : σ < 1)
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) (K : Set (Fin d → ℝ)) (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ 2 u U → c2HolderNorm σ U u < ⊤ →
      ∃ v : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧
        tsupport v ⊆ U ∧ Set.EqOn v u K ∧
        c2HolderNorm σ Set.univ v ≤ ENNReal.ofReal C * c2HolderNorm σ U u := by
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ + δ = ε := ⟨ε / 2, by positivity, by ring⟩
  obtain ⟨χ, hχ, hχK, hχsupp⟩ := exists_smooth_cutoff K hK hδ
  have hball : ∀ x ∈ tsupport χ, Metric.ball x δ ⊆ U := by
    intro x hx
    calc Metric.ball x δ ⊆ Metric.closedBall x δ := Metric.ball_subset_closedBall
      _ ⊆ Metric.cthickening δ (Metric.cthickening δ K) :=
          Metric.closedBall_subset_cthickening (hχsupp hx) δ
      _ ⊆ Metric.cthickening (δ + δ) K := Metric.cthickening_cthickening_subset hδ.le hδ.le K
      _ ⊆ U := by rw [hδε]; exact hεU
  have hχU : tsupport χ ⊆ U := fun x hx => hball x hx (Metric.mem_ball_self hδ)
  have hχc : HasCompactSupport χ :=
    IsCompact.of_isClosed_subset hK.cthickening (isClosed_tsupport χ) hχsupp
  have hP : ∀ f : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∃ B, 0 ≤ B ∧ ∀ x y, |f x| ≤ B ∧ |f x - f y| ≤ B * radius (x - y) := by
    intro f hf hfc
    obtain ⟨B₁, hB₁⟩ := hf.continuous.bounded_above_of_compact_support hfc
    obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf (by simp)
    have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
    have hB0 : (0 : ℝ) ≤ max B₁ 0 := le_max_right _ _
    refine ⟨max B₁ 0 + L, add_nonneg hB0 hL0, fun x y => ⟨?_, ?_⟩⟩
    · have h := hB₁ x
      rw [Real.norm_eq_abs] at h
      linarith [le_max_left B₁ 0]
    · have h1 := hL.dist_le_mul x y
      rw [Real.dist_eq, dist_eq_norm] at h1
      have h2 := mul_le_mul_of_nonneg_left (norm_le_radius (x - y)) hL0
      have h3 := mul_nonneg hB0 (radius_nonneg (x - y))
      nlinarith
  have hχ1 : ∀ i, ContDiff ℝ ∞ (partialDeriv i χ) := fun i => contDiff_partialDeriv i hχ
  have hχ1c : ∀ i, HasCompactSupport (partialDeriv i χ) :=
    fun i => hasCompactSupport_partialDeriv i hχc
  obtain ⟨B₀, hB₀0, hB₀⟩ := hP χ hχ hχc
  choose B₁ hB₁0 hB₁ using fun i => hP _ (hχ1 i) (hχ1c i)
  choose B₂ hB₂0 hB₂ using fun i j =>
    hP _ (contDiff_partialDeriv i (hχ1 j)) (hasCompactSupport_partialDeriv i (hχ1c j))
  set B := B₀ + ∑ i, B₁ i + ∑ i, ∑ j, B₂ i j with hBdef
  have hS₁ : 0 ≤ ∑ i, B₁ i := Finset.sum_nonneg fun i _ => hB₁0 i
  have hS₂ : 0 ≤ ∑ i, ∑ j, B₂ i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hB₂0 i j
  have hB0 : 0 ≤ B := by linarith
  have hmono : ∀ (f : (Fin d → ℝ) → ℝ) (B' : ℝ), B' ≤ B →
      (∀ x y, |f x| ≤ B' ∧ |f x - f y| ≤ B' * radius (x - y)) →
      (∀ x, |f x| ≤ B) ∧ ∀ x y, |f x - f y| ≤ B * radius (x - y) :=
    fun f B' hle h => ⟨fun x => (h x x).1.trans hle,
      fun x y => (h x y).2.trans (mul_le_mul_of_nonneg_right hle (radius_nonneg _))⟩
  have hG0 := hmono χ B₀ (by linarith) hB₀
  have hG1 : ∀ i, (∀ x, |partialDeriv i χ x| ≤ B) ∧
      ∀ x y, |partialDeriv i χ x - partialDeriv i χ y| ≤ B * radius (x - y) := fun i =>
    hmono _ (B₁ i) (by
      have := Finset.single_le_sum (fun j _ => hB₁0 j) (Finset.mem_univ i)
      linarith) (hB₁ i)
  have hG2 : ∀ i j, (∀ x, |partialDeriv i (partialDeriv j χ) x| ≤ B) ∧
      ∀ x y, |partialDeriv i (partialDeriv j χ) x - partialDeriv i (partialDeriv j χ) y| ≤
        B * radius (x - y) := fun i j =>
    hmono _ (B₂ i j) (by
      have h1 := Finset.single_le_sum (fun k _ => hB₂0 i k) (Finset.mem_univ j)
      have h2 := Finset.single_le_sum (f := fun k => ∑ l, B₂ k l)
        (fun k _ => Finset.sum_nonneg fun l _ => hB₂0 k l) (Finset.mem_univ i)
      linarith) (hB₂ i j)
  have hZ0 : ∀ x, x ∉ tsupport χ → χ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hZ1 : ∀ i x, x ∉ tsupport χ → partialDeriv i χ x = 0 :=
    fun i x hx => partialDeriv_eq_zero_of_notMem i hx
  have hZ2 : ∀ i j x, x ∉ tsupport χ → partialDeriv i (partialDeriv j χ) x = 0 :=
    fun i j x hx =>
      partialDeriv_eq_zero_of_notMem i fun h => hx (tsupport_partialDeriv_subset j χ h)
  have hχdiff : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hχ1diff : ∀ j, Differentiable ℝ (partialDeriv j χ) :=
    fun j => (hχ1 j).differentiable (by simp)
  have hδ1 : 0 < δ ^ (1 - σ) := Real.rpow_pos_of_pos hδ _
  have hδσ : 0 < δ ^ σ := Real.rpow_pos_of_pos hδ _
  have hrle : ∀ x y : Fin d → ℝ, x ≠ y → radius (x - y) < δ →
      radius (x - y) ≤ δ ^ (1 - σ) * radius (x - y) ^ σ := by
    intro x y hxy hr
    have hpos : 0 < radius (x - y) := radius_pos (sub_ne_zero.mpr hxy)
    calc radius (x - y) = radius (x - y) ^ (1 - σ) * radius (x - y) ^ σ := by
          rw [← Real.rpow_add hpos]; simp
      _ ≤ δ ^ (1 - σ) * radius (x - y) ^ σ :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hpos.le hr.le (by linarith))
            (Real.rpow_nonneg hpos.le _)
  set κ : ℝ := 1 + d * δ ^ (1 - σ) with hκ
  have hκ1 : 1 ≤ κ := by
    have : 0 ≤ (d : ℝ) * δ ^ (1 - σ) := mul_nonneg (Nat.cast_nonneg d) hδ1.le
    linarith
  set Hn : ℝ := 4 * (B * κ + B * δ ^ (1 - σ)) with hHn
  have hHn0 : 0 ≤ Hn := by
    have := mul_nonneg hB0 hδ1.le
    have := mul_nonneg hB0 (zero_le_one.trans hκ1)
    linarith
  have hfar0 : 0 ≤ 8 * B * (δ ^ σ)⁻¹ := mul_nonneg (by linarith) (inv_nonneg.2 hδσ.le)
  set C₀ : ℝ := Hn + 8 * B * (δ ^ σ)⁻¹ + 4 * B + 1 with hC₀
  have hC₀pos : 0 < C₀ := by linarith
  have hCpos : (0 : ℝ) < ((1 + d + d * d + d * d : ℕ) : ℝ) := by positivity
  refine ⟨((1 + d + d * d + d * d : ℕ) : ℝ) * C₀, mul_pos hCpos hC₀pos, fun u hu hA => ?_⟩
  set M := (c2HolderNorm σ U u).toReal with hMdef
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hle0 : supNorm U u ≤ c2HolderNorm σ U u := by
    unfold c2HolderNorm
    exact le_add_right (le_add_right (le_add_right le_rfl))
  have hle1 : ∀ i, supNorm U (partialDeriv i u) ≤ c2HolderNorm σ U u := fun i => by
    unfold c2HolderNorm
    exact le_add_right (le_add_right (le_add_left
      (Finset.single_le_sum (f := fun i => supNorm U (partialDeriv i u)) (fun j _ => zero_le)
        (Finset.mem_univ i))))
  have hle2 : ∀ i j, supNorm U (secondPartial i j u) ≤ c2HolderNorm σ U u := fun i j => by
    unfold c2HolderNorm
    exact le_add_right (le_add_left ((Finset.single_le_sum
      (f := fun j => supNorm U (secondPartial i j u)) (fun k _ => zero_le)
      (Finset.mem_univ j)).trans (Finset.single_le_sum
        (f := fun i => ∑ j, supNorm U (secondPartial i j u)) (fun k _ => zero_le)
        (Finset.mem_univ i))))
  have hleh : ∀ i j, holderSeminorm σ U (secondPartial i j u) ≤ c2HolderNorm σ U u :=
    fun i j => by
    unfold c2HolderNorm
    exact le_add_left ((Finset.single_le_sum
      (f := fun j => holderSeminorm σ U (secondPartial i j u)) (fun k _ => zero_le)
      (Finset.mem_univ j)).trans (Finset.single_le_sum
        (f := fun i => ∑ j, holderSeminorm σ U (secondPartial i j u)) (fun k _ => zero_le)
        (Finset.mem_univ i)))
  have hu2at : ∀ x ∈ U, ContDiffAt ℝ 2 u x := fun x hx => hu.contDiffAt (hU.mem_nhds hx)
  have hud : ∀ x ∈ U, DifferentiableAt ℝ u x :=
    fun x hx => (hu2at x hx).differentiableAt (by norm_num)
  have hudd : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ u) x := fun x hx =>
    ((hu2at x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hupd : ∀ j, ∀ x ∈ U, DifferentiableAt ℝ (partialDeriv j u) x :=
    fun j x hx => (hudd x hx).clm_apply (differentiableAt_const _)
  have hu0 : ∀ x ∈ U, |u x| ≤ M := fun x hx =>
    (abs_le_supNorm_toReal (hle0.trans_lt hA) hx).trans (ENNReal.toReal_mono hA.ne hle0)
  have hu1 : ∀ i, ∀ x ∈ U, |partialDeriv i u x| ≤ M := fun i x hx =>
    (abs_le_supNorm_toReal ((hle1 i).trans_lt hA) hx).trans
      (ENNReal.toReal_mono hA.ne (hle1 i))
  have hu2 : ∀ i j, ∀ x ∈ U, |partialDeriv i (partialDeriv j u) x| ≤ M := fun i j x hx => by
    rw [← secondPartial_eq_partialDeriv i j (hudd x hx)]
    exact (abs_le_supNorm_toReal ((hle2 i j).trans_lt hA) hx).trans
      (ENNReal.toReal_mono hA.ne (hle2 i j))
  have hu2h : ∀ i j, ∀ x ∈ U, ∀ y ∈ U,
      |partialDeriv i (partialDeriv j u) x - partialDeriv i (partialDeriv j u) y| ≤
        M * radius (x - y) ^ σ := fun i j x hx y hy => by
    rw [← secondPartial_eq_partialDeriv i j (hudd x hx),
      ← secondPartial_eq_partialDeriv i j (hudd y hy)]
    have hc0 : c0HolderNorm σ U (secondPartial i j u) < ⊤ :=
      ENNReal.add_lt_top.2 ⟨(hle2 i j).trans_lt hA, (hleh i j).trans_lt hA⟩
    exact (abs_sub_le_holderSeminorm_toReal hc0 hx hy).trans
      (mul_le_mul_of_nonneg_right (ENNReal.toReal_mono hA.ne (hleh i j))
        (Real.rpow_nonneg (radius_nonneg _) _))
  set v : (Fin d → ℝ) → ℝ := fun x => χ x * u x with hvdef
  have hvsupp : tsupport v ⊆ tsupport χ := closure_mono (Function.support_mul_subset_left _ _)
  have hv : ContDiff ℝ 2 v := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hχ.of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt.mul (hu2at x hx)
    · have hxv : x ∉ tsupport v := fun h => hx (hχU (hvsupp h))
      exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 hxv)
  have hvdd : ∀ x, DifferentiableAt ℝ (fderiv ℝ v) x := fun x =>
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have hF1 : ∀ j x, partialDeriv j v x =
      χ x * partialDeriv j u x + partialDeriv j χ x * u x := by
    intro j x
    by_cases hx : x ∈ U
    · exact partialDeriv_mul j (hχdiff x) (hud x hx)
    · have hxχ : x ∉ tsupport χ := fun h => hx (hχU h)
      rw [partialDeriv_eq_zero_of_notMem j (fun h => hxχ (hvsupp h)), hZ0 x hxχ, hZ1 j x hxχ]
      ring
  have hF1' : ∀ j, partialDeriv j v =
      fun y => χ y * partialDeriv j u y + partialDeriv j χ y * u y := fun j => funext (hF1 j)
  have hF2 : ∀ i j x, secondPartial i j v x =
      χ x * partialDeriv i (partialDeriv j u) x + partialDeriv i χ x * partialDeriv j u x +
        (partialDeriv j χ x * partialDeriv i u x +
          partialDeriv i (partialDeriv j χ) x * u x) := by
    intro i j x
    rw [secondPartial_eq_partialDeriv i j (hvdd x)]
    by_cases hx : x ∈ U
    · have hd1 : DifferentiableAt ℝ (fun y => χ y * partialDeriv j u y) x :=
        (hχdiff x).mul (hupd j x hx)
      have hd2 : DifferentiableAt ℝ (fun y => partialDeriv j χ y * u y) x :=
        (hχ1diff j x).mul (hud x hx)
      rw [hF1' j, partialDeriv_add i hd1 hd2, partialDeriv_mul i (hχdiff x) (hupd j x hx),
        partialDeriv_mul i (hχ1diff j x) (hud x hx)]
    · have hxχ : x ∉ tsupport χ := fun h => hx (hχU h)
      have h0 : partialDeriv i (partialDeriv j v) x = 0 :=
        partialDeriv_eq_zero_of_notMem i fun h => hxχ (hvsupp (tsupport_partialDeriv_subset j v h))
      simp only [h0, hZ0 x hxχ, hZ1 i x hxχ, hZ1 j x hxχ, hZ2 i j x hxχ]
      ring
  have hzero : ∀ i j x, x ∉ tsupport χ → secondPartial i j v x = 0 := by
    intro i j x hx
    rw [secondPartial_eq_partialDeriv i j (hvdd x)]
    exact partialDeriv_eq_zero_of_notMem i fun h => hx (hvsupp (tsupport_partialDeriv_subset j v h))
  have hterm : ∀ a b : (Fin d → ℝ) → ℝ, (∀ x, |a x| ≤ B) → (∀ x, x ∉ tsupport χ → a x = 0) →
      (∀ x ∈ U, |b x| ≤ M) → ∀ x, |a x * b x| ≤ B * M := by
    intro a b ha ha0 hb x
    by_cases hx : x ∈ U
    · rw [abs_mul]
      exact mul_le_mul (ha x) (hb x hx) (abs_nonneg _) hB0
    · rw [ha0 x (fun h => hx (hχU h)), zero_mul, abs_zero]
      exact mul_nonneg hB0 hM
  have hv0 : ∀ x, |v x| ≤ B * M := hterm χ u hG0.1 hZ0 hu0
  have hv1 : ∀ i x, |partialDeriv i v x| ≤ 2 * B * M := by
    intro i x
    rw [hF1]
    have t1 := hterm χ _ hG0.1 hZ0 (hu1 i) x
    have t2 := hterm _ u (hG1 i).1 (hZ1 i) hu0 x
    have := abs_add_le (χ x * partialDeriv i u x) (partialDeriv i χ x * u x)
    linarith
  have hv2 : ∀ i j x, |secondPartial i j v x| ≤ 4 * B * M := by
    intro i j x
    rw [hF2]
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_add_le _ _) (abs_add_le _ _)).trans ?_
    have t1 := hterm χ _ hG0.1 hZ0 (hu2 i j) x
    have t2 := hterm _ _ (hG1 i).1 (hZ1 i) (hu1 j) x
    have t3 := hterm _ _ (hG1 j).1 (hZ1 j) (hu1 i) x
    have t4 := hterm _ u (hG2 i j).1 (hZ2 i j) hu0 x
    linarith
  have hnear : ∀ i j x y, x ∈ tsupport χ → x ≠ y → radius (x - y) < δ →
      |secondPartial i j v x - secondPartial i j v y| ≤ Hn * M * radius (x - y) ^ σ := by
    intro i j x y hx hxy hr
    have hxU : x ∈ U := hχU hx
    have hyb : y ∈ Metric.ball x δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact (norm_le_radius _).trans_lt (by rwa [radius_sub_comm])
    have hyU : y ∈ U := hball x hx hyb
    have hxb : x ∈ Metric.ball x δ := Metric.mem_ball_self hδ
    have hρ : 0 ≤ radius (x - y) ^ σ := Real.rpow_nonneg (radius_nonneg _) _
    have hrρ := hrle x y hxy hr
    have hKM : ∀ g : (Fin d → ℝ) → ℝ, |g x - g y| ≤ d * M * radius (x - y) →
        |g x - g y| ≤ κ * M * radius (x - y) ^ σ := by
      intro g hg
      have h1 : (d : ℝ) * M * radius (x - y) ≤ d * M * (δ ^ (1 - σ) * radius (x - y) ^ σ) :=
        mul_le_mul_of_nonneg_left hrρ (mul_nonneg (Nat.cast_nonneg d) hM)
      have h2 := mul_nonneg hM hρ
      have h3 : κ * M * radius (x - y) ^ σ =
          M * radius (x - y) ^ σ + d * M * (δ ^ (1 - σ) * radius (x - y) ^ σ) := by
        rw [hκ]; ring
      linarith
    have hub := hKM u (abs_sub_le_of_partialDeriv (convex_ball x δ)
      (fun z hz => hud z (hball x hx hz)) hM (fun z hz k => hu1 k z (hball x hx hz)) hxb hyb)
    have hpub : ∀ j, |partialDeriv j u x - partialDeriv j u y| ≤
        κ * M * radius (x - y) ^ σ := fun j =>
      hKM _ (abs_sub_le_of_partialDeriv (convex_ball x δ)
        (fun z hz => hupd j z (hball x hx hz)) hM
        (fun z hz k => hu2 k j z (hball x hx hz)) hxb hyb)
    have hsub : |partialDeriv i (partialDeriv j u) x - partialDeriv i (partialDeriv j u) y| ≤
        κ * M * radius (x - y) ^ σ := by
      have h1 := hu2h i j x hxU y hyU
      have h2 := mul_le_mul_of_nonneg_right hκ1 (mul_nonneg hM hρ)
      nlinarith
    have hχK : ∀ a : (Fin d → ℝ) → ℝ, (∀ x y, |a x - a y| ≤ B * radius (x - y)) →
        |a x - a y| ≤ B * (δ ^ (1 - σ) * radius (x - y) ^ σ) :=
      fun a ha => (ha x y).trans (mul_le_mul_of_nonneg_left hrρ hB0)
    rw [hF2 i j x, hF2 i j y]
    have e : ∀ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℝ, a₁ + a₂ + (a₃ + a₄) - (b₁ + b₂ + (b₃ + b₄)) =
        (a₁ - b₁) + (a₂ - b₂) + ((a₃ - b₃) + (a₄ - b₄)) := by intros; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_add_le _ _) (abs_add_le _ _)).trans ?_
    have t1 := abs_mul_sub_mul_le (hG0.1 x) (hχK χ hG0.2) (hu2 i j y hyU) hsub
    have t2 := abs_mul_sub_mul_le ((hG1 i).1 x) (hχK _ (hG1 i).2) (hu1 j y hyU) (hpub j)
    have t3 := abs_mul_sub_mul_le ((hG1 j).1 x) (hχK _ (hG1 j).2) (hu1 i y hyU) (hpub i)
    have t4 := abs_mul_sub_mul_le ((hG2 i j).1 x) (hχK _ (hG2 i j).2) (hu0 y hyU) hub
    have h : Hn * M * radius (x - y) ^ σ = 4 * (B * (κ * M * radius (x - y) ^ σ) +
        M * (B * (δ ^ (1 - σ) * radius (x - y) ^ σ))) := by
      rw [hHn]; ring
    linarith
  have hvh : ∀ i j x y, x ≠ y →
      |secondPartial i j v x - secondPartial i j v y| ≤ C₀ * M * radius (x - y) ^ σ := by
    intro i j x y hxy
    have hρ : 0 ≤ radius (x - y) ^ σ := Real.rpow_nonneg (radius_nonneg _) _
    have hMρ := mul_nonneg hM hρ
    have hHnC : Hn * M * radius (x - y) ^ σ ≤ C₀ * M * radius (x - y) ^ σ := by
      have := mul_le_mul_of_nonneg_right (show Hn ≤ C₀ by linarith) hMρ
      linarith
    by_cases hr : radius (x - y) < δ
    · by_cases hx : x ∈ tsupport χ
      · exact (hnear i j x y hx hxy hr).trans hHnC
      · by_cases hy : y ∈ tsupport χ
        · have h := hnear i j y x hy hxy.symm (by rwa [radius_sub_comm])
          rw [abs_sub_comm, radius_sub_comm y x] at h
          exact h.trans hHnC
        · rw [hzero i j x hx, hzero i j y hy, sub_self, abs_zero]
          exact mul_nonneg (mul_nonneg hC₀pos.le hM) hρ
    · push Not at hr
      have h1 := abs_le.1 (hv2 i j x)
      have h2 := abs_le.1 (hv2 i j y)
      have h3 : |secondPartial i j v x - secondPartial i j v y| ≤ 8 * B * M :=
        abs_le.2 ⟨by linarith, by linarith⟩
      have hδρ : δ ^ σ ≤ radius (x - y) ^ σ := Real.rpow_le_rpow hδ.le hr hσ.le
      have h4 : 1 ≤ (δ ^ σ)⁻¹ * radius (x - y) ^ σ := by
        rw [inv_mul_eq_div, le_div_iff₀ hδσ, one_mul]
        exact hδρ
      have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg (by linarith : (0 : ℝ) ≤ 8 * B) hM)
      have h6 := mul_le_mul_of_nonneg_right (show 8 * B * (δ ^ σ)⁻¹ ≤ C₀ by linarith) hMρ
      nlinarith
  have hsup : ∀ f : (Fin d → ℝ) → ℝ, (∀ x, |f x| ≤ C₀ * M) →
      supNorm Set.univ f ≤ ENNReal.ofReal (C₀ * M) :=
    fun f hf => iSup₂_le fun x _ => ENNReal.ofReal_le_ofReal (hf x)
  have hhol : ∀ f : (Fin d → ℝ) → ℝ,
      (∀ x y, x ≠ y → |f x - f y| ≤ C₀ * M * radius (x - y) ^ σ) →
      holderSeminorm σ Set.univ f ≤ ENNReal.ofReal (C₀ * M) :=
    fun f hf => iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy =>
      ENNReal.ofReal_le_ofReal <| by
        rw [div_le_iff₀ (Real.rpow_pos_of_pos (radius_pos (sub_ne_zero.mpr hxy)) _)]
        exact hf x y hxy
  have hBM : B * M ≤ C₀ * M := mul_le_mul_of_nonneg_right (by linarith) hM
  have h2BM : 2 * B * M ≤ C₀ * M := mul_le_mul_of_nonneg_right (by linarith) hM
  have h4BM : 4 * B * M ≤ C₀ * M := mul_le_mul_of_nonneg_right (by linarith) hM
  refine ⟨v, hv, IsCompact.of_isClosed_subset hχc (isClosed_tsupport v) hvsupp,
    hvsupp.trans hχU, fun x hx => ?_, ?_⟩
  · change χ x * u x = u x
    rw [hχK hx, Pi.one_apply, one_mul]
  have hAeq : c2HolderNorm σ U u = ENNReal.ofReal M := (ENNReal.ofReal_toReal hA.ne).symm
  calc c2HolderNorm σ Set.univ v ≤ ENNReal.ofReal (C₀ * M) +
        ∑ _i : Fin d, ENNReal.ofReal (C₀ * M) +
        ∑ _i : Fin d, ∑ _j : Fin d, ENNReal.ofReal (C₀ * M) +
        ∑ _i : Fin d, ∑ _j : Fin d, ENNReal.ofReal (C₀ * M) := by
        unfold c2HolderNorm
        gcongr with i _ i _ j _ i _ j _
        · exact hsup _ fun x => (hv0 x).trans hBM
        · exact hsup _ fun x => (hv1 i x).trans h2BM
        · exact hsup _ fun x => (hv2 i j x).trans h4BM
        · exact hhol _ (hvh i j)
    _ = ENNReal.ofReal (((1 + d + d * d + d * d : ℕ) : ℝ) * C₀) * c2HolderNorm σ U u := by
        rw [hAeq, ← ENNReal.ofReal_mul (mul_pos hCpos hC₀pos).le, mul_assoc,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end

end LatticeProb.Elliptic.HolderExtension
