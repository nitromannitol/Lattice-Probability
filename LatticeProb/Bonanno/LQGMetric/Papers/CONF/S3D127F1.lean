/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127F1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127E4
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127C7
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127A6
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108R2

/-!
# D127 N5: `G_U = π ∫ p_U` in pairing form (`ZBHeatRepr`), by polarization

DEC-127 §3 N5 / §4 P-127F. For a bounded open `U` satisfying the Green-potential regularity
`GreenPotReg U` (S3D127E4), N2+N3 (`dualNormSq_eq_killedGreen`) identify the dual Dirichlet norm
of every bounded density `ρ ≥ 0` vanishing off `U` with the killed-Green form `B(ρ, ρ)`. The QZ
covariance `zeroGFFTestCov U` is the polarization (`dualCov`) of `dualNormSq` expanded
bilinearly over `testMeasPos`/`testMeasNeg`; since `B` is bilinear and symmetric
(`killedGreenForm_add_self`, S3D127E2), `zeroGFFTestCov U ρ σ = B(ρ, σ)`.

Source: Berestycki–Powell, *Gaussian free field and Liouville quantum gravity*, arXiv:2404.16642,
§1.5 (Lemmas 1.37–1.38: `Γ₀(ρ) = ∫∫ ρ ρ G`), with the polarization identity of the covariance
(the same pattern as `cov_zbProcU_of_heatRepr`, S3D108R2).

* `hN1_of_bounded`: N1 (`killedGreen_lap`) in the `∀ y ∈ U` form of `hN1`;
* `greenPotReg_confU`: `GreenPotReg (confU r δ z T)` from `greenPot_confU_props` (S3D127C7);
* `dualCov_withDensity_eq_killedGreenForm`: `dualCov (a dx) (b dx) = B(a, b)`;
* **`zbHeatRepr_of_reg`**: `ZBHeatRepr U` for every bounded open `U` with `GreenPotReg U`;
* **`zbHeatRepr_confU`**: `ZBHeatRepr (confU r δ z T)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Laplacian
open scoped Real ContDiff

namespace LQGMetric.CONF.ZBM

open KilledHeat Blueprint

variable {U : Set ℂ} {c : ℂ} {R : ℝ}

/-- N1 (`killedGreen_lap`) in the hypothesis form `hN1` of S3D127B1/E4 -/
theorem hN1_of_bounded (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y :=
  fun _ hg y _ => killedGreen_lap hU hUb hg y

/-- **N4 at `confU`**: the Green-potential regularity `GreenPotReg (confU r δ z T)` -/
theorem greenPotReg_confU {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    GreenPotReg (confU r δ z T) := by
  intro ρ hρ hcs _ _
  obtain ⟨M, hM⟩ := (hρ.continuous.norm.bddAbove_range_of_hasCompactSupport hcs.norm)
  obtain ⟨h1, -, h3⟩ := greenPot_confU_props hr hδ z T hρ.continuous.measurable (M := M)
    (fun y => by simpa [Real.norm_eq_abs] using hM ⟨y, rfl⟩)
  exact ⟨h1, h3⟩

/-- **polarization**: for bounded measurable `a, b ≥ 0` vanishing off `U`,
`dualCov U (zeroSpace U) (a dx) (b dx) = B(a, b)` -/
theorem dualCov_withDensity_eq_killedGreenForm (hU : IsOpen U) (hR : 0 ≤ R)
    (hUR : U ⊆ Metric.ball c R)
    (hN1 : ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y)
    (hreg : GreenPotReg U) {a b : ℂ → ℝ} (ha : Measurable a) (hb : Measurable b) {C : ℝ}
    (haC : ∀ z, |a z| ≤ C) (hbC : ∀ z, |b z| ≤ C) (ha0 : ∀ z, 0 ≤ a z) (hb0 : ∀ z, 0 ≤ b z)
    (haU : ∀ z, z ∉ U → a z = 0) (hbU : ∀ z, z ∉ U → b z = 0) :
    QuantumZipper.dualCov U (QuantumZipper.zeroSpace U)
        (volume.withDensity fun z => ENNReal.ofReal (a z))
        (volume.withDensity fun z => ENNReal.ofReal (b z)) =
      killedGreenForm U a b := by
  have hai := integrable_of_bdd_of_vanish hUR ha haC haU
  have hbi := integrable_of_bdd_of_vanish hUR hb hbC hbU
  have hsum : (volume.withDensity fun z => ENNReal.ofReal (a z)) +
      (volume.withDensity fun z => ENNReal.ofReal (b z)) =
      volume.withDensity fun z => ENNReal.ofReal (a z + b z) := by
    rw [← withDensity_add_left ha.ennreal_ofReal]
    congr 1
    funext z
    simp only [Pi.add_apply]
    rw [ENNReal.ofReal_add (ha0 z) (hb0 z)]
  have hsC : ∀ z, |a z + b z| ≤ C + C := fun z =>
    (abs_add_le _ _).trans (add_le_add (haC z) (hbC z))
  have hsm : Measurable fun z => a z + b z := ha.add hb
  have hab := dualNormSq_eq_killedGreen hU hR hUR hN1 hreg hsm hsC
    (fun z => add_nonneg (ha0 z) (hb0 z)) (fun z hz => by simp [haU z hz, hbU z hz])
  have haa := dualNormSq_eq_killedGreen hU hR hUR hN1 hreg ha haC ha0 haU
  have hbb := dualNormSq_eq_killedGreen hU hR hUR hN1 hreg hb hbC hb0 hbU
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (haC 0)
  have haC' : ∀ z, |a z| ≤ C + C := fun z => (haC z).trans (by linarith)
  have hbC' : ∀ z, |b z| ≤ C + C := fun z => (hbC z).trans (by linarith)
  have psab := killedGreenForm_psd hU hR hUR hsm hsC (hai.add hbi)
  have psa := killedGreenForm_psd hU hR hUR ha haC hai
  have psb := killedGreenForm_psd hU hR hUR hb hbC hbi
  have hexp := killedGreenForm_add_self hU hR hUR ha hb haC' hbC' hai hbi
  unfold QuantumZipper.dualCov
  rw [hsum, hab, haa, hbb, ENNReal.toReal_ofReal psab, ENNReal.toReal_ofReal psa,
    ENNReal.toReal_ofReal psb, hexp]
  ring

/-- `B(a - a', b) = B(a, b) - B(a', b)` -/
lemma killedGreenForm_sub_left (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {a a' b : ℂ → ℝ} (ha : Measurable a) (ha' : Measurable a') (hb : Measurable b) {C : ℝ}
    (hbC : ∀ z, |b z| ≤ C) (hai : Integrable a) (hai' : Integrable a') (hbi : Integrable b) :
    killedGreenForm U (fun z => a z - a' z) b = killedGreenForm U a b - killedGreenForm U a' b := by
  unfold killedGreenForm
  rw [← integral_sub (integrable_killedGreenForm hU hR hUR ha hb hbC hai hbi)
    (integrable_killedGreenForm hU hR hUR ha' hb hbC hai' hbi)]
  exact integral_congr_ae (Eventually.of_forall fun q => by ring)

/-- `B(a, b - b') = B(a, b) - B(a, b')` -/
lemma killedGreenForm_sub_right (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {a b b' : ℂ → ℝ} (ha : Measurable a) (hb : Measurable b) (hb' : Measurable b') {C : ℝ}
    (hbC : ∀ z, |b z| ≤ C) (hbC' : ∀ z, |b' z| ≤ C) (hai : Integrable a) (hbi : Integrable b)
    (hbi' : Integrable b') :
    killedGreenForm U a (fun z => b z - b' z) = killedGreenForm U a b - killedGreenForm U a b' := by
  unfold killedGreenForm
  rw [← integral_sub (integrable_killedGreenForm hU hR hUR ha hb hbC hai hbi)
    (integrable_killedGreenForm hU hR hUR ha hb' hbC' hai hbi')]
  exact integral_congr_ae (Eventually.of_forall fun q => by ring)

lemma max_sub_max_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- the zero-boundary test covariance of bounded measurable densities vanishing off `U` is the
killed-Green form (polarization over the positive and negative parts) -/
theorem zeroGFFTestCov_eq_killedGreenForm (hU : IsOpen U) (hR : 0 ≤ R)
    (hUR : U ⊆ Metric.ball c R)
    (hN1 : ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y)
    (hreg : GreenPotReg U) {ρ σ : ℂ → ℝ} (hρ : Measurable ρ) (hσ : Measurable σ) {C : ℝ}
    (hρC : ∀ z, |ρ z| ≤ C) (hσC : ∀ z, |σ z| ≤ C)
    (hρU : ∀ z, z ∉ U → ρ z = 0) (hσU : ∀ z, z ∉ U → σ z = 0) :
    QuantumZipper.zeroGFFTestCov U ρ σ = killedGreenForm U ρ σ := by
  set p : ℂ → ℝ := fun z => max (ρ z) 0 with hp
  set n : ℂ → ℝ := fun z => max (-ρ z) 0 with hn
  set p' : ℂ → ℝ := fun z => max (σ z) 0 with hp'
  set n' : ℂ → ℝ := fun z => max (-σ z) 0 with hn'
  have pm : Measurable p := hρ.max measurable_const
  have nm : Measurable n := hρ.neg.max measurable_const
  have pm' : Measurable p' := hσ.max measurable_const
  have nm' : Measurable n' := hσ.neg.max measurable_const
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hρC 0)
  have bnd : ∀ x : ℝ, |x| ≤ C → |max x 0| ≤ C := fun x hx => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans hx) hC0
  have pC : ∀ z, |p z| ≤ C := fun z => bnd _ (hρC z)
  have nC : ∀ z, |n z| ≤ C := fun z => bnd _ (by rw [abs_neg]; exact hρC z)
  have pC' : ∀ z, |p' z| ≤ C := fun z => bnd _ (hσC z)
  have nC' : ∀ z, |n' z| ≤ C := fun z => bnd _ (by rw [abs_neg]; exact hσC z)
  have p0 : ∀ z, 0 ≤ p z := fun z => le_max_right _ _
  have n0 : ∀ z, 0 ≤ n z := fun z => le_max_right _ _
  have p0' : ∀ z, 0 ≤ p' z := fun z => le_max_right _ _
  have n0' : ∀ z, 0 ≤ n' z := fun z => le_max_right _ _
  have pU : ∀ z, z ∉ U → p z = 0 := fun z hz => by simp [hp, hρU z hz]
  have nU : ∀ z, z ∉ U → n z = 0 := fun z hz => by simp [hn, hρU z hz]
  have pU' : ∀ z, z ∉ U → p' z = 0 := fun z hz => by simp [hp', hσU z hz]
  have nU' : ∀ z, z ∉ U → n' z = 0 := fun z hz => by simp [hn', hσU z hz]
  have pi := integrable_of_bdd_of_vanish hUR pm pC pU
  have ni := integrable_of_bdd_of_vanish hUR nm nC nU
  have pi' := integrable_of_bdd_of_vanish hUR pm' pC' pU'
  have ni' := integrable_of_bdd_of_vanish hUR nm' nC' nU'
  have ePos : ∀ f : ℂ → ℝ, QuantumZipper.testMeasPos f =
      volume.withDensity fun z => ENNReal.ofReal (max (f z) 0) := fun f => by
    simp only [QuantumZipper.testMeasPos, ofReal_max_zero]
  have eNeg : ∀ f : ℂ → ℝ, QuantumZipper.testMeasNeg f =
      volume.withDensity fun z => ENNReal.ofReal (max (-f z) 0) := fun f => by
    simp only [QuantumZipper.testMeasNeg, ofReal_max_zero]
  have hρe : ρ = fun z => p z - n z := funext fun z => (max_sub_max_neg (ρ z)).symm
  have hσe : σ = fun z => p' z - n' z := funext fun z => (max_sub_max_neg (σ z)).symm
  have D := fun {a b : ℂ → ℝ} (ha : Measurable a) (hb : Measurable b) (haC : ∀ z, |a z| ≤ C)
      (hbC : ∀ z, |b z| ≤ C) (ha0 : ∀ z, 0 ≤ a z) (hb0 : ∀ z, 0 ≤ b z)
      (haU : ∀ z, z ∉ U → a z = 0) (hbU : ∀ z, z ∉ U → b z = 0) =>
    dualCov_withDensity_eq_killedGreenForm hU hR hUR hN1 hreg ha hb haC hbC ha0 hb0 haU hbU
  unfold QuantumZipper.zeroGFFTestCov
  rw [ePos, ePos, eNeg, eNeg]
  rw [D pm pm' pC pC' p0 p0' pU pU', D pm nm' pC nC' p0 n0' pU nU',
    D nm pm' nC pC' n0 p0' nU pU', D nm nm' nC nC' n0 n0' nU nU']
  have hdC : ∀ z, |p' z - n' z| ≤ C + C := fun z =>
    (abs_sub _ _).trans (add_le_add (pC' z) (nC' z))
  have hdm : Measurable fun z => p' z - n' z := pm'.sub nm'
  rw [hρe, hσe, killedGreenForm_sub_left hU hR hUR pm nm hdm hdC pi ni (pi'.sub ni'),
    killedGreenForm_sub_right hU hR hUR pm pm' nm' pC' nC' pi pi' ni',
    killedGreenForm_sub_right hU hR hUR nm pm' nm' pC' nC' ni pi' ni']
  ring

/-- **D127 N5 (general form)**: `ZBHeatRepr U` for every bounded open `U` with `GreenPotReg U` -/
theorem zbHeatRepr_of_reg (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hreg : GreenPotReg U) :
    ZBHeatRepr U := by
  intro φ ψ
  obtain ⟨R, hR0, hUR⟩ := hUb.subset_ball_lt 0 0
  obtain ⟨C₁, h₁⟩ := testC_abs_le φ
  obtain ⟨C₂, h₂⟩ := testC_abs_le ψ
  obtain ⟨m1, b1, -⟩ := indicator_props hU φ (C := max C₁ C₂)
    (fun z => (h₁ z).trans (le_max_left _ _))
  obtain ⟨m2, b2, -⟩ := indicator_props hU ψ (C := max C₁ C₂)
    (fun z => (h₂ z).trans (le_max_right _ _))
  exact zeroGFFTestCov_eq_killedGreenForm hU hR0.le hUR (hN1_of_bounded hU hUb) hreg m1 m2 b1 b2
    (fun z hz => indicator_of_notMem hz _) (fun z hz => indicator_of_notMem hz _)

/-- **D127 N5 at `confU`**: `G_U = π ∫ p_U` in pairing form on CONF's domains -/
theorem zbHeatRepr_confU {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    ZBHeatRepr (confU r δ z T) :=
  zbHeatRepr_of_reg (isOpen_confU r δ z T)
    (Metric.isBounded_ball.subset (confU_subset_ball r δ z T))
    (greenPotReg_confU hr hδ z T)

end LQGMetric.CONF.ZBM
