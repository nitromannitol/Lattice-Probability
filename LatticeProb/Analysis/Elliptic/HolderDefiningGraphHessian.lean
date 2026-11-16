import LatticeProb.Analysis.Elliptic.HolderDefiningGraph

/-!
# Hölder increments for the Hessian of a local graph

The Hessian formula for a regular graph gives local Hölder increments.
-/

open scoped Topology

namespace LatticeProb.Elliptic.HolderExtension

private def HolderControl {α : Type*} (S : Set α) (D : α → α → ℝ)
    (f : α → ℝ) (B H : ℝ) : Prop :=
  0 ≤ B ∧ 0 ≤ H ∧ (∀ x ∈ S, |f x| ≤ B) ∧
    ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ H * D x y

private theorem HolderControl.mul {α : Type*} {S : Set α} {D : α → α → ℝ}
    {f g : α → ℝ} {A B H K : ℝ} (hf : HolderControl S D f A H)
    (hg : HolderControl S D g B K) :
    HolderControl S D (fun x => f x * g x) (A * B) (A * K + B * H) := by
  rcases hf with ⟨hA, hH, hfa, hfh⟩
  rcases hg with ⟨hB, hK, hgb, hgk⟩
  refine ⟨mul_nonneg hA hB, add_nonneg (mul_nonneg hA hK) (mul_nonneg hB hH), ?_, ?_⟩
  · intro x hx
    rw [abs_mul]
    exact mul_le_mul (hfa x hx) (hgb x hx) (abs_nonneg _) hA
  · intro x hx y hy
    calc
      |f x * g x - f y * g y| = |f x * (g x - g y) + g y * (f x - f y)| := by
        congr 1; ring
      _ ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
        simpa only [abs_mul] using abs_add_le (f x * (g x - g y)) (g y * (f x - f y))
      _ ≤ A * (K * D x y) + B * (H * D x y) := by
        exact add_le_add (mul_le_mul (hfa x hx) (hgk x hx y hy) (abs_nonneg _) hA)
          (mul_le_mul (hgb y hy) (hfh x hx y hy) (abs_nonneg _) hB)
      _ = (A * K + B * H) * D x y := by ring

private theorem HolderControl.sum {α ι : Type*} {S : Set α} {D : α → α → ℝ}
    {f : ι → α → ℝ} {B H : ι → ℝ} (s : Finset ι)
    (hf : ∀ i ∈ s, HolderControl S D (f i) (B i) (H i)) :
    HolderControl S D (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, B i) (∑ i ∈ s, H i) := by
  classical
  refine ⟨Finset.sum_nonneg (fun i hi => (hf i hi).1),
    Finset.sum_nonneg (fun i hi => (hf i hi).2.1), ?_, ?_⟩
  · intro x hx
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => (hf i hi).2.2.1 x hx)
  · intro x hx y hy
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i ∈ s, (f i x - f i y)| ≤ ∑ i ∈ s, |f i x - f i y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s, H i * D x y := Finset.sum_le_sum fun i hi => (hf i hi).2.2.2 x hx y hy
      _ = (∑ i ∈ s, H i) * D x y := by rw [Finset.sum_mul]

/-- The second derivatives of a regular local graph have Hölder increments. -/
theorem exists_holder_increment_secondPartial_graph {d : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ ≤ 1)
    (ρ g : (Fin d → ℝ) → ℝ) (hρ2 : ContDiff ℝ 2 ρ)
    (hρ : ∀ R : ℝ, c2HolderNorm σ {x | LatticeProb.Euclidean.Lattice.radius x < R} ρ < ⊤)
    (hg : ContDiff ℝ 2 g) (p : Fin d → ℝ) (i : Fin d) (hgp : g p = p i)
    (hzero : ∀ᶠ y in 𝓝 p, ρ (Function.update y i (g y)) = 0) (hi : partialDeriv i ρ p ≠ 0) :
    ∃ (H r : ℝ), 0 ≤ H ∧ 0 < r ∧ ∀ j k, ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
      |secondPartial j k g x - secondPartial j k g y| ≤ H * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := by
  classical
  let φ : (Fin d → ℝ) → (Fin d → ℝ) := fun x => Function.update x i (g x)
  let R := LatticeProb.Euclidean.Lattice.radius (φ p) + 1
  let T : Set (Fin d → ℝ) := {x | LatticeProb.Euclidean.Lattice.radius x < R}
  have hφ : Continuous φ := by
    have h := (contDiff_update_pair i).comp (contDiff_id.prodMk hg)
    exact (by simpa [φ, Function.comp_def] using h : ContDiff ℝ 2 φ).continuous
  have hT : IsOpen T := isOpen_lt (LatticeProb.Euclidean.Lattice.radius_continuous d) continuous_const
  have hpT : φ p ∈ T := by simp [T, R]
  have hmap : ∀ᶠ x in 𝓝 p, φ x ∈ T := hφ.continuousAt.tendsto.eventually (hT.mem_nhds hpT)
  obtain ⟨a, r₀, ha, hr₀, hreg⟩ :=
    exists_graph_partialDeriv_abs_lower_bound ρ g hρ2 hg.continuous.continuousAt i hgp hi
  obtain ⟨I, r₁, hI, hr₁, hincI⟩ :=
    exists_holder_increment_inv_graph_partialDeriv hσ hσ' ρ g hρ2 hg p i hgp hi
  obtain ⟨J, r₂, hJ, hr₂, hincJ⟩ :=
    exists_holder_increment_secondPartial_along_graph hσ ρ g hρ hg p i
  obtain ⟨B, K, r₃, hB, hK, hr₃, hgraph⟩ :=
    exists_uniform_bound_partialDeriv_graph_map hσ hσ' g hg p i
  have hz : ∀ᶠ x in 𝓝 p, ∀ᶠ y in 𝓝 x, ρ (φ y) = 0 :=
    eventually_eventually_nhds.mpr hzero
  have hnear : ∀ᶠ x in 𝓝 p, (∀ᶠ y in 𝓝 x, ρ (φ y) = 0) ∧ φ x ∈ T ∧
      x ∈ Metric.ball p r₀ ∧ x ∈ Metric.ball p r₁ ∧
      x ∈ Metric.ball p r₂ ∧ x ∈ Metric.ball p r₃ := by
    filter_upwards [hz, hmap, Metric.ball_mem_nhds p hr₀, Metric.ball_mem_nhds p hr₁,
      Metric.ball_mem_nhds p hr₂, Metric.ball_mem_nhds p hr₃] with x hx hm h0 h1 h2 h3
    exact ⟨hx, hm, h0, h1, h2, h3⟩
  obtain ⟨r, hr, hrnear⟩ := Metric.mem_nhds_iff.mp hnear
  let S := Metric.ball p r
  let D : (Fin d → ℝ) → (Fin d → ℝ) → ℝ :=
    fun x y => LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ
  let A := (c2HolderNorm σ T ρ).toReal
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hnρ : c2HolderNorm σ T ρ < ⊤ := hρ R
  have hInv : HolderControl S D (fun x => (partialDeriv i ρ (φ x))⁻¹) a⁻¹ I := by
    refine ⟨le_of_lt (inv_pos.mpr ha), hI, ?_, ?_⟩
    · intro x hx
      have hb := hreg x (hrnear hx).2.2.1
      rw [abs_inv]
      exact (inv_le_inv₀ (lt_of_lt_of_le ha hb) ha).2 hb
    · intro x hx y hy
      exact hincI x (hrnear hx).2.2.2.1 y (hrnear hy).2.2.2.1
  have hRho (m l : Fin d) : HolderControl S D (fun x => secondPartial m l ρ (φ x)) A J := by
    refine ⟨hA, hJ, ?_, ?_⟩
    · intro x hx
      exact abs_secondPartial_le_c2HolderNorm_toReal hnρ m l (hrnear hx).2.1
    · intro x hx y hy
      exact hincJ m l x (hrnear hx).2.2.2.2.1 y (hrnear hy).2.2.2.2.1
  have hGraph (j m : Fin d) : HolderControl S D
      (fun x => partialDeriv j (fun z => Function.update z i (g z) m) x) B K := by
    refine ⟨hB, hK, ?_, ?_⟩
    · intro x hx
      exact (hgraph j m).1 x (hrnear hx).2.2.2.2.2
    · intro x hx y hy
      exact (hgraph j m).2 x (hrnear hx).2.2.2.2.2 y (hrnear hy).2.2.2.2.2
  let P := (A * B) * B
  let Q := (A * K + B * J) * B + B * K * A
  have hTriple (j k l m : Fin d) : HolderControl S D
      (fun x => (secondPartial m l ρ (φ x) *
        partialDeriv j (fun z => Function.update z i (g z) m) x) *
        partialDeriv k (fun z => Function.update z i (g z) l) x) P Q := by
    dsimp [P, Q]
    convert (hRho m l).mul (hGraph j m) |>.mul (hGraph k l) using 1; ring
  let C := ∑ _l : Fin d, ∑ _m : Fin d, P
  let E := ∑ _l : Fin d, ∑ _m : Fin d, Q
  have hSum (j k : Fin d) : HolderControl S D
      (fun x => ∑ l, ∑ m, (secondPartial m l ρ (φ x) *
        partialDeriv j (fun z => Function.update z i (g z) m) x) *
        partialDeriv k (fun z => Function.update z i (g z) l) x) C E := by
    dsimp [C, E]
    apply HolderControl.sum Finset.univ
    intro l _
    apply HolderControl.sum Finset.univ
    intro m _
    exact hTriple j k l m
  refine ⟨C * I + a⁻¹ * E, r, ?_, hr, ?_⟩
  · exact add_nonneg (mul_nonneg (hSum i i).1 hI) (mul_nonneg (le_of_lt (inv_pos.mpr ha)) (hSum i i).2.1)
  · intro j k x hx y hy
    have hprod := (hSum j k).mul hInv
    have hxform := secondPartial_graph_formula ρ g hρ2 hg i (hrnear hx).1
      (abs_pos.mp (lt_of_lt_of_le ha (hreg x (hrnear hx).2.2.1))) j k
    have hyform := secondPartial_graph_formula ρ g hρ2 hg i (hrnear hy).1
      (abs_pos.mp (lt_of_lt_of_le ha (hreg y (hrnear hy).2.2.1))) j k
    have h := hprod.2.2.2 x hx y hy
    rw [hxform, hyform, neg_div, neg_div, neg_sub_neg, abs_sub_comm]
    simpa only [div_eq_mul_inv, Finset.sum_mul] using h

end LatticeProb.Elliptic.HolderExtension
