/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127E4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127E3

/-!
# D127 N3: the killed-Green form is bounded by the dual Dirichlet norm (BP Lemma 1.37)

Packet P-127E of DEC-127 (§3, item N3). For a bounded open `U` and a measurable bounded
`ρ ≥ 0` vanishing off `U`:

**`killedGreen_le_dualNormSq`**: `ofReal B(ρ, ρ) ≤ dualNormSq U (zeroSpace U) (ρ dx)`,

with the `testMeasPos`/`testMeasNeg` forms. Together with N2 (`dualNormSq_le_killedGreen`,
S3D127B1) this is `dualNormSq = B` (BP Lemma 1.37, `Γ₀(ρ, ρ) = ∫|∇(G ρ)|² = ∫∫ G ρ ρ`).

Proof. Write `‖·‖_B = √B` (a seminorm, S3D127E2) and `s = √dualNormSq`. Given `η > 0`, take
`ρ' ∈ C_c^∞(U)`, `ρ' ≥ 0`, with `‖ρ − ρ'‖_B ≤ η` (`exists_smooth_approx`, S3D127E3), and the
truncation test function `f` of `ρ'` (`exists_trunc_test`, S3D127E1): `E(f) ≤ a := ∫ ρ' f` and
`a ≥ B(ρ', ρ') − η²`. By `sq_integral_le_energy_mul`, `|∫ (ρ − ρ') f| ≤ √E(f) η`, so
`s √E(f) ≥ |∫ ρ f| ≥ a − √E(f) η ≥ √E(f) (√a − η)`; hence `s ≥ √a − η ≥ ‖ρ'‖_B − 2η ≥ ‖ρ‖_B − 3η`.
(If `E(f) = 0` then `a = 0` by the same Cauchy–Schwarz bound.)

Source: Berestycki–Powell, *Gaussian free field and Liouville quantum gravity*, arXiv:2404.16642,
§1.5, Lemma 1.37 (`literature/pdf/2404.16642.txt` l. 1640–1658). BP prove `Γ₀(ρ) = ∫|∇Gρ|²` for
smooth `ρ`; the truncation (DV-D127-1) and the extension to bounded `ρ` by approximation (D127
addendum) are own elementary steps.

Hypotheses (from the running packets, in clean form): `hN1` (N1, P-127A, the form of
S3D127B1) and `hreg` (N4a/N4c, P-127C): for every `ρ' ∈ C_c^∞(U)`, `ρ' ≥ 0`, the Green potential
`u = ∫ G_U(·, y) ρ'(y) dy` is continuous on `U` and the closures of its superlevel sets
`{x ∈ U | ε ≤ u x}`, `ε > 0`, are compact subsets of `U` (the conclusion of
`closure_superlevel_subset`, S3D127C4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped Real ContDiff Laplacian

namespace LQGMetric.CONF.ZBM

open KilledHeat

variable {U : Set ℂ} {c : ℂ} {R : ℝ}

/-- the regularity of Green potentials of smooth densities assumed from N4a/N4c -/
def GreenPotReg (U : Set ℂ) : Prop :=
  ∀ ρ : ℂ → ℝ, ContDiff ℝ ∞ ρ → HasCompactSupport ρ → tsupport ρ ⊆ U → (∀ z, 0 ≤ ρ z) →
    ContinuousOn (fun x => ∫ y, killedGreen U x y * ρ y) U ∧
      ∀ ε > 0, IsCompact (closure {x | x ∈ U ∧ ε ≤ ∫ y, killedGreen U x y * ρ y}) ∧
        closure {x | x ∈ U ∧ ε ≤ ∫ y, killedGreen U x y * ρ y} ⊆ U

lemma dirichletEnergyOn_nonneg' (f : ℂ → ℝ) : 0 ≤ QuantumZipper.dirichletEnergyOn U f :=
  mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)

lemma integrable_mul_test {ρ : ℂ → ℝ} (hρ : Measurable ρ) {C : ℝ} (hC : ∀ z, |ρ z| ≤ C)
    {f : ℂ → ℝ} (hf : f ∈ QuantumZipper.zeroSpace U) : Integrable (fun y => ρ y * f y) :=
  (hf.1.continuous.integrable_of_hasCompactSupport hf.2.1).bdd_mul hρ.aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hC z)

/-- **D127 N3 (BP Lemma 1.37, lower bound)**: for `ρ ≥ 0` bounded measurable vanishing off the
bounded open set `U`, given N1 and the regularity `GreenPotReg U` (N4),
`∫∫ ρ ρ G_U ≤ dualNormSq U (zeroSpace U) (ρ dx)` -/
theorem killedGreen_le_dualNormSq (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hN1 : ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y)
    (hreg : GreenPotReg U)
    {ρ : ℂ → ℝ} (hρ : Measurable ρ) {C : ℝ} (hC : ∀ z, |ρ z| ≤ C) (hρ0 : ∀ z, 0 ≤ ρ z)
    (hρU : ∀ z, z ∉ U → ρ z = 0) :
    ENNReal.ofReal (killedGreenForm U ρ ρ) ≤
      QuantumZipper.dualNormSq U (QuantumZipper.zeroSpace U)
        (volume.withDensity fun z => ENNReal.ofReal (ρ z)) := by
  set D := QuantumZipper.dualNormSq U (QuantumZipper.zeroSpace U)
    (volume.withDensity fun z => ENNReal.ofReal (ρ z)) with hD
  rcases eq_or_ne D ⊤ with hDt | hDt
  · rw [hDt]; exact le_top
  have hρi := integrable_of_bdd_of_vanish hUR hρ hC hρU
  have hρC : ∀ z, ρ z ≤ C := fun z => (le_abs_self _).trans (hC z)
  -- the dual norm dominates every Rayleigh quotient
  have hRay : ∀ f ∈ QuantumZipper.zeroSpace U, 0 < QuantumZipper.dirichletEnergyOn U f →
      (∫ y, ρ y * f y) ^ 2 / QuantumZipper.dirichletEnergyOn U f ≤ D.toReal := by
    intro f hf hE
    have hint : ∫ x, f x ∂(volume.withDensity fun z => ENNReal.ofReal (ρ z)) =
        ∫ y, ρ y * f y := by
      rw [integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [ENNReal.toReal_ofReal (hρ0 y), smul_eq_mul]
    have h := le_iSup₂_of_le (f := fun f (_ : f ∈ {f ∈ QuantumZipper.zeroSpace U |
        0 < QuantumZipper.dirichletEnergyOn U f}) => ENNReal.ofReal
        ((∫ x, f x ∂(volume.withDensity fun z => ENNReal.ofReal (ρ z))) ^ 2 /
          QuantumZipper.dirichletEnergyOn U f)) f ⟨hf, hE⟩ le_rfl
    rw [hint] at h
    exact (ENNReal.ofReal_le_iff_le_toReal hDt).1 h
  set s := √D.toReal with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hB0 := killedGreenForm_psd hU hR hUR hρ hC hρi
  have hmain : √(killedGreenForm U ρ ρ) ≤ s := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set η := ε / 3 with hη_def
    have hη : 0 < η := by positivity
    obtain ⟨ρ', h1, h2, h3, h4, h5, h6⟩ := exists_smooth_approx hU hR hUR hρ hρ0 hρC hρU hη
    have hρ'U : ∀ z, z ∉ U → ρ' z = 0 := fun z hz =>
      image_eq_zero_of_notMem_tsupport fun h => hz (h3 h)
    have hρ'm : Measurable ρ' := h1.continuous.measurable
    have hρ'C : ∀ z, |ρ' z| ≤ C := fun z => by rw [abs_of_nonneg (h4 z)]; exact h5 z
    have hρ'i := integrable_of_bdd_of_vanish hUR hρ'm hρ'C hρ'U
    set d : ℂ → ℝ := fun z => ρ z - ρ' z with hd
    have hdm : Measurable d := hρ.sub hρ'm
    have hdC : ∀ z, |d z| ≤ 2 * C := fun z => by
      rw [abs_le]; constructor <;> linarith [hρ0 z, hρC z, h4 z, h5 z]
    have hdU : ∀ z, z ∉ U → d z = 0 := fun z hz => by simp [hd, hρU z hz, hρ'U z hz]
    have hdi := integrable_of_bdd_of_vanish hUR hdm hdC hdU
    have hC2 : ∀ z, |ρ' z| ≤ 2 * C := fun z => by
      have := hρ'C z; linarith [abs_nonneg (ρ' z)]
    -- `‖ρ‖_B ≤ ‖ρ'‖_B + η`
    have htri := sqrt_killedGreenForm_add_le hU hR hUR hρ'm hdm hC2 hdC hρ'i hdi
    have e : (fun z => ρ' z + d z) = ρ := funext fun z => by simp [hd]
    rw [e] at htri
    -- the truncation test function of `ρ'`
    have hI0 : 0 ≤ ∫ y, ρ' y := integral_nonneg h4
    set ε' := η ^ 2 / (2 * ((∫ y, ρ' y) + 1)) with hε'
    have hε'0 : 0 < ε' := by positivity
    obtain ⟨hcont, hsup⟩ := hreg ρ' h1 h2 h3 h4
    obtain ⟨f, hf, hEa, hlow⟩ := exists_trunc_test hU hR hUR hN1 h1 h2 h3 h4 hcont hsup hε'0
    set a := ∫ y, ρ' y * f y with ha
    set E := QuantumZipper.dirichletEnergyOn U f with hE
    have hE0 : 0 ≤ E := dirichletEnergyOn_nonneg' f
    have ha0 : 0 ≤ a := hE0.trans hEa
    have hεI : 2 * ε' * ∫ y, ρ' y ≤ η ^ 2 := by
      rw [hε']
      have hpos : 0 < (∫ y, ρ' y) + 1 := by linarith
      rw [show 2 * (η ^ 2 / (2 * ((∫ y, ρ' y) + 1))) * ∫ y, ρ' y =
        η ^ 2 * ((∫ y, ρ' y) / ((∫ y, ρ' y) + 1)) by field_simp]
      refine mul_le_of_le_one_right (sq_nonneg _) ?_
      rw [div_le_one hpos]; linarith
    have hB' : √(killedGreenForm U ρ' ρ') ≤ √a + η := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [Real.sq_sqrt ha0, Real.sqrt_nonneg a]
    have hdB : √(killedGreenForm U d d) ≤ η := h6
    have hdB0 := killedGreenForm_psd hU hR hUR hdm hdC hdi
    rcases hE0.lt_or_eq with hEpos | hEz
    · -- `s √E ≥ |∫ ρ f|`
      have hR1 := hRay f hf hEpos
      have hsqE := Real.sq_sqrt hE0
      have hsE : 0 < √E := Real.sqrt_pos.2 hEpos
      have hRf : |∫ y, ρ y * f y| ≤ s * √E := by
        rw [div_le_iff₀ hEpos] at hR1
        refine (Real.abs_le_sqrt hR1).trans (le_of_eq ?_)
        rw [Real.sqrt_mul ENNReal.toReal_nonneg]
      -- `|∫ d f| ≤ √E η`
      have hCS := sq_integral_le_energy_mul hU hR hUR hN1 hdm hdC hdi hdU hf
      have hdf : |∫ y, d y * f y| ≤ √E * η := by
        refine (Real.abs_le_sqrt hCS).trans ?_
        rw [Real.sqrt_mul hE0]
        exact mul_le_mul_of_nonneg_left hdB (Real.sqrt_nonneg _)
      have hsplit : ∫ y, ρ y * f y = a + ∫ y, d y * f y := by
        rw [ha, ← integral_add (integrable_mul_test hρ'm hρ'C hf) (integrable_mul_test hdm hdC hf)]
        exact integral_congr_ae (Eventually.of_forall fun y => by simp [hd]; ring)
      -- `√a √E ≤ a`
      have haE : √a * √E ≤ a := by
        have : √E ≤ √a := Real.sqrt_le_sqrt hEa
        nlinarith [Real.sq_sqrt ha0, Real.sqrt_nonneg a]
      have hkey : √E * √a ≤ √E * (s + η) := by
        have := le_abs_self (∫ y, ρ y * f y)
        nlinarith [neg_abs_le (∫ y, d y * f y)]
      have hsa : √a ≤ s + η := le_of_mul_le_mul_left hkey hsE
      linarith
    · -- `E = 0` forces `a = 0`
      have hCS := sq_integral_le_energy_mul hU hR hUR hN1 hρ'm hρ'C hρ'i hρ'U hf
      have hE00 : QuantumZipper.dirichletEnergyOn U f = 0 := hEz.symm
      rw [hE00, zero_mul] at hCS
      have ha00 : a = 0 := by nlinarith [sq_nonneg a]
      rw [ha00, Real.sqrt_zero] at hB'
      linarith
  have hBle : killedGreenForm U ρ ρ ≤ D.toReal := by
    have h1 := Real.sq_sqrt hB0
    have h2 := Real.sq_sqrt (ENNReal.toReal_nonneg (a := D))
    nlinarith [Real.sqrt_nonneg (killedGreenForm U ρ ρ)]
  exact ENNReal.ofReal_le_of_le_toReal hBle

/-- **N2 + N3: `dualNormSq = B`** for `ρ ≥ 0` bounded measurable vanishing off `U` -/
theorem dualNormSq_eq_killedGreen (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hN1 : ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y)
    (hreg : GreenPotReg U)
    {ρ : ℂ → ℝ} (hρ : Measurable ρ) {C : ℝ} (hC : ∀ z, |ρ z| ≤ C) (hρ0 : ∀ z, 0 ≤ ρ z)
    (hρU : ∀ z, z ∉ U → ρ z = 0) :
    QuantumZipper.dualNormSq U (QuantumZipper.zeroSpace U)
        (volume.withDensity fun z => ENNReal.ofReal (ρ z)) =
      ENNReal.ofReal (killedGreenForm U ρ ρ) :=
  le_antisymm (dualNormSq_le_killedGreen hU hR hUR hN1 hρ hC hρ0 hρU)
    (killedGreen_le_dualNormSq hU hR hUR hN1 hreg hρ hC hρ0 hρU)

end LQGMetric.CONF.ZBM
