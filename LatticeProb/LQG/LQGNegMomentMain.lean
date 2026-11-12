import Mathlib
import LatticeProb.LQG.LQGNegLognormal
import LatticeProb.LQG.LQGNegStart
import LatticeProb.LQG.LQGNegMomentLimit
import LatticeProb.Analysis.NegMomentLamForm
import LatticeProb.Analysis.NegMomentBootstrap

/-!
# Negative moments of the mass of the unit ball of the Liouville measure

For `0 < |γ| < 2` and every `q > 0` the negative moment `E μ(B(0,1))^{-q}` of the Liouville
measure of the unit ball is bounded uniformly over the models of the whole-plane Gaussian free
field.

The proof follows the multiscale argument of Garban, Holden, Sepúlveda and Sun (negative moments of
the Liouville measure).  Let `Z_n` be the mass of the square `[-1/8, 1/8]²` for the approximation of
the Liouville measure at scale `2^{-n}`, and
`l(λ) = sup E exp (-λ Z_n)`, the supremum over all models of the whole-plane field on a probability
space of the universe `u` and all `n ≥ 1`; `β(λ)` is the same supremum over `1 ≤ n ≤ 4`.

* `laplaceValues`, `laplaceSup`: the set of the values and their supremum.
* `exists_laplace_decay_all`: for each `a > 0`, `l(λ) ≤ A λ^{-a}`, from
  - the recursion `l(λ) ≤ max (β(λ)) (E ∏_s l(λ W_s))` obtained from the recursion for one model and
    the independence of the model of the law of the weights `W_0, W_1`,
  - the polynomial bounds for `β` of every order (small scales),
  - the uniform bound `l(λ₀) < 1` (single scale),
  - and the splitting and bootstrap lemmas for such recursions.
* `ballMassNegMoment_of_lt`: the negative moments of the unit-ball mass of every order.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal NNReal

universe u

namespace LatticeProb.Gauss

open LatticeProb LatticeProb.LQG LQGDyadicScaling

/-- The values `E exp (-x Z_n)` of the Laplace transform of the mass `Z_n` of the square
`[-1/8, 1/8]²` for the approximation at scale `2^{-n}`, over all models of the whole-plane Gaussian
free field on probability spaces of the universe `u` and all `n` with `S n`. -/
def laplaceValues (γ x : ℝ) (S : ℕ → Prop) : Set ℝ :=
  {y | ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc ∧ ∃ n : ℕ, S n ∧
        y = ∫ ω, Real.exp (-(x * (lqgApproxMass γ (hcirc ω) (lqgSquare.indicator 1) n).toReal)) ∂P}

/-- The supremum of `laplaceValues`. -/
def laplaceSup (γ x : ℝ) (S : ℕ → Prop) : ℝ := sSup (laplaceValues.{u} γ x S)

section Models

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

theorem IsWholePlaneGFF.integrable_exp_neg_mul_lqgSquareMass (hh : IsWholePlaneGFF P hC hcirc)
    (γ : ℝ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun ω => Real.exp (-(x *
      (lqgApproxMass γ (hcirc ω) (lqgSquare.indicator 1) n).toReal))) P := by
  have := hh.isProbabilityMeasure
  have hmeasT : Measurable (lqgSquare.indicator (1 : ℂ → ℝ≥0∞)) :=
    measurable_const.indicator measurableSet_lqgSquare
  obtain ⟨Z, hZm, -, hZae⟩ := hh.exists_measurable_ae_eq_toReal_lqgApproxMass γ n hmeasT
  refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · refine (Real.measurable_exp.comp (hZm.const_mul x).neg).aestronglyMeasurable.congr ?_
    filter_upwards [hZae] with ω hω
    show Real.exp (-(x * Z ω)) = _
    rw [hω]
  · rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hx ENNReal.toReal_nonneg))

theorem IsWholePlaneGFF.integral_exp_neg_mul_le_one (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∫ ω, Real.exp (-(x * (lqgApproxMass γ (hcirc ω) (lqgSquare.indicator 1) n).toReal)) ∂P ≤ 1 := by
  have := hh.isProbabilityMeasure
  calc _ ≤ ∫ _ : Ω, (1 : ℝ) ∂P := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
          (integrable_const 1) (Filter.Eventually.of_forall fun _ => ?_)
        exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hx ENNReal.toReal_nonneg))
    _ = 1 := by simp

theorem IsWholePlaneGFF.integral_exp_neg_mul_anti (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∫ ω, Real.exp (-(y * (lqgApproxMass γ (hcirc ω) (lqgSquare.indicator 1) n).toReal)) ∂P ≤
      ∫ ω, Real.exp (-(x * (lqgApproxMass γ (hcirc ω) (lqgSquare.indicator 1) n).toReal)) ∂P :=
  integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
    (hh.integrable_exp_neg_mul_lqgSquareMass γ n hx)
    (Filter.Eventually.of_forall fun _ => Real.exp_le_exp.2
      (neg_le_neg (mul_le_mul_of_nonneg_right hxy ENNReal.toReal_nonneg)))

end Models

theorem laplaceValues_bddAbove (γ : ℝ) {x : ℝ} (hx : 0 ≤ x) (S : ℕ → Prop) :
    BddAbove (laplaceValues.{u} γ x S) := by
  refine ⟨1, ?_⟩
  rintro y ⟨Ω, _, P, hC, hcirc, hh, n, -, rfl⟩
  exact hh.integral_exp_neg_mul_le_one γ n hx

theorem IsWholePlaneGFF.integral_le_laplaceSup {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {x : ℝ} (hx : 0 ≤ x) {S : ℕ → Prop} {n : ℕ} (hn : S n) :
    ∫ ω, Real.exp (-(x * (lqgApproxMass γ (hcirc ω) (lqgSquare.indicator 1) n).toReal)) ∂P ≤
      laplaceSup.{u} γ x S :=
  le_csSup (laplaceValues_bddAbove.{u} γ hx S) ⟨Ω, inferInstance, P, hC, hcirc, hh, n, hn, rfl⟩

theorem laplaceSup_nonneg (γ x : ℝ) (S : ℕ → Prop) : 0 ≤ laplaceSup.{u} γ x S := by
  refine Real.sSup_nonneg ?_
  rintro y ⟨Ω, _, P, hC, hcirc, hh, n, -, rfl⟩
  exact integral_nonneg fun _ => (Real.exp_pos _).le

theorem laplaceSup_le_one (γ : ℝ) {x : ℝ} (hx : 0 ≤ x) (S : ℕ → Prop) :
    laplaceSup.{u} γ x S ≤ 1 := by
  refine Real.sSup_le ?_ zero_le_one
  rintro y ⟨Ω, _, P, hC, hcirc, hh, n, -, rfl⟩
  exact hh.integral_exp_neg_mul_le_one γ n hx

theorem laplaceSup_anti (γ : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (S : ℕ → Prop) :
    laplaceSup.{u} γ y S ≤ laplaceSup.{u} γ x S := by
  refine Real.sSup_le ?_ (laplaceSup_nonneg γ x S)
  rintro v ⟨Ω, _, P, hC, hcirc, hh, n, hn, rfl⟩
  exact (hh.integral_exp_neg_mul_anti γ n hx hxy).trans (hh.integral_le_laplaceSup γ hx hn)

/-- **Polynomial decay of the Laplace transforms of the mass of the square.** For `0 < |γ| < 2` and
every `a > 0` there is `A ≥ 0` with `E exp (-λ Z_n) ≤ A λ^{-a}` for every `λ > 0`, every `n ≥ 1`
and every model of the whole-plane Gaussian free field on a probability space of the universe `u`. -/
theorem exists_laplace_decay_all (γ : ℝ) (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 4) {a : ℝ} (ha : 0 < a) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
        ∀ n : ℕ, 1 ≤ n → ∀ lam : ℝ, 0 < lam →
          ∫ ω, Real.exp (-(lam * (lqgApproxMass γ (hcirc ω) (lqgSquare.indicator 1) n).toReal)) ∂P ≤
            A * lam ^ (-a) := by
  by_cases hex : ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc
  swap
  · exact ⟨0, le_rfl, fun Ω _ P _ hC hcirc hh => absurd ⟨Ω, inferInstance, P, hC, hcirc, hh⟩ hex⟩
  obtain ⟨Ω0, _, P0, hC0, hcirc0, hh0⟩ := hex
  have hP0 := hh0.isProbabilityMeasure
  have hsub12 : lqgSquare ⊆ closedBall (0 : ℂ) (1 / 2) :=
    lqgSquare_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  -- the supremum functions
  obtain ⟨l, hl⟩ : ∃ l : ℝ → ℝ, ∀ x, l x = laplaceSup.{u} γ x (fun n => 1 ≤ n) := ⟨_, fun _ => rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ → ℝ,
      ∀ x, β x = laplaceSup.{u} γ x (fun n => 1 ≤ n ∧ n ≤ 4) := ⟨_, fun _ => rfl⟩
  have hl0 : ∀ x, 0 < x → 0 ≤ l x := fun x _ => by rw [hl]; exact laplaceSup_nonneg γ x _
  have hl1 : ∀ x, 0 < x → l x ≤ 1 := fun x hx => by rw [hl]; exact laplaceSup_le_one γ hx.le _
  have hanti : ∀ x y, 0 < x → x ≤ y → l y ≤ l x := fun x y hx hxy => by
    rw [hl, hl]; exact laplaceSup_anti γ hx.le hxy _
  have hb0 : ∀ x, 0 ≤ β x := fun x => by rw [hβdef]; exact laplaceSup_nonneg γ x _
  have hle : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
      ∫ ω, Real.exp (-(x * (lqgApproxMass γ (hcirc ω) (lqgSquare.indicator 1) n).toReal)) ∂P ≤
        l x := fun Ω _ P hC hcirc hh n hn x hx => by
    rw [hl]; exact hh.integral_le_laplaceSup γ hx.le hn
  -- the measurable truncation of `l`
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ → ℝ, ∀ x, L x = if 0 < x then l x else 1 := ⟨_, fun _ => rfl⟩
  have hLpos : ∀ x, 0 < x → L x = l x := fun x hx => by simp [hLdef, hx]
  have hLanti : Antitone L := by
    intro x y hxy
    by_cases hy : 0 < y
    · by_cases hx : 0 < x
      · rw [hLpos x hx, hLpos y hy]; exact hanti x y hx hxy
      · have : L x = 1 := by simp [hLdef, hx]
        rw [this, hLpos y hy]; exact hl1 y hy
    · have hx : ¬ 0 < x := fun h => hy (lt_of_lt_of_le h hxy)
      have h1 : L x = 1 := by simp [hLdef, hx]
      have h2 : L y = 1 := by simp [hLdef, hy]
      rw [h1, h2]
  have hLm : Measurable L := hLanti.measurable
  -- the recursion
  have hrec : ∀ lam, 0 < lam → l lam ≤ max (β lam) (∫ a : Ω0 × ℝ, ∏ s : Fin 2,
      l (lam * subSquareLognormal γ hcirc0 4 a s) ∂(P0.prod (gaussianReal 0 1))) := by
    intro lam hlam
    rw [hl lam]
    refine Real.sSup_le ?_ (le_max_of_le_left (hb0 lam))
    rintro y ⟨Ω, _, P, hC, hcirc, hh, n, hn, rfl⟩
    have := hh.isProbabilityMeasure
    by_cases h4 : n ≤ 4
    · refine le_max_of_le_left ?_
      rw [hβdef lam]
      exact hh.integral_le_laplaceSup γ hlam.le ⟨hn, h4⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
      refine le_max_of_le_right ?_
      have hGm : Measurable fun v : Fin 2 → ℝ => ∏ s : Fin 2, L (lam * v s) :=
        Finset.measurable_prod _ fun s _ => by
          have hfs : Measurable fun v : Fin 2 → ℝ => lam * v s :=
            measurable_const.mul (measurable_pi_apply s)
          exact hLm.comp hfs
      refine (hh.integral_exp_neg_lqgSquareMass_le_prod hγ (le_refl 4) (m := m) (by omega) L hLm
        (fun ν hν => (hLpos ν hν).le.trans (hl1 ν hν))
        (fun ν hν => (hle Ω P hC hcirc hh m (by omega) ν hν).trans (hLpos ν hν).ge) hlam).trans ?_
      refine le_of_eq ?_
      have hind := hh.integral_comp_subSquareLognormal_eq hh0 γ 4 _ hGm
      refine hind.trans ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      beta_reduce
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [hLpos _ (mul_pos hlam (subSquareLognormal_pos γ hcirc0 4 a s))]
  -- polynomial bound of every order for `β`
  have hβ : ∀ q : ℝ, 0 < q → ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ x : ℝ, 0 < x → β x ≤ Cb * x ^ (-q) := by
    intro q hq
    obtain ⟨C, hC0, hC⟩ := exists_laplace_small_scale_bound.{u} γ measurableSet_lqgSquare hsub12
      volume_lqgSquare_pos 4 hq
    refine ⟨C, hC0, fun x hx => ?_⟩
    rw [hβdef x]
    refine Real.sSup_le ?_ (mul_nonneg hC0 (Real.rpow_nonneg hx.le _))
    rintro y ⟨Ω, _, P, hC', hcirc, hh, n, ⟨hn1, hn4⟩, rfl⟩
    have := hh.isProbabilityMeasure
    exact hC Ω P hC' hcirc hh n hn1 hn4 x hx
  obtain ⟨C1, hC1, hβ1⟩ := hβ 1 one_pos
  have hβ1' : ∀ x, 0 < x → β x ≤ C1 * x⁻¹ := fun x hx => by
    have := hβ1 x hx
    rwa [Real.rpow_neg_one] at this
  -- the single-scale bound
  obtain ⟨η, lam0, hη, hlam0, hU⟩ := exists_laplace_uniform_bound.{u} hγ hγ2
    measurableSet_lqgSquare hsub12 volume_lqgSquare_pos
  have hρ0 : 0 ≤ 1 - η / 2 :=
    (integral_nonneg fun _ => (Real.exp_pos _).le).trans (hU Ω0 P0 hC0 hcirc0 hh0 1 le_rfl)
  have hρl : ∀ x, lam0 ≤ x → l x ≤ 1 - η / 2 := by
    intro x hx
    rw [hl x]
    refine Real.sSup_le ?_ hρ0
    rintro y ⟨Ω, _, P, hC', hcirc, hh, n, hn, rfl⟩
    have := hh.isProbabilityMeasure
    exact (hh.integral_exp_neg_mul_anti γ n hlam0.le hx).trans (hU Ω P hC' hcirc hh n hn)
  -- the splitting
  have hrecL : ∀ x, 0 < x → ∀ u, lognormalShift γ 4 ≤ u → l (x * Real.exp u) ≤
      max (β (x * Real.exp u)) (2 * Real.exp (-((1 / (2 * lognormalVariance γ 4)) *
        (u - lognormalShift γ 4) ^ 2)) + l x ^ 2) := by
    intro x hx u hu
    have h := rec_split (P := P0.prod (gaussianReal 0 1))
      (V := fun (i : Fin 2) (a : Ω0 × ℝ) => subSquareLognormal γ hcirc0 4 a i) (l := l) (β := β)
      (fun i => hh0.measurable_subSquareLognormal γ 4 i)
      (fun i a => subSquareLognormal_pos γ hcirc0 4 a i) hl0 hl1 hanti hrec hx
      (hh0.measureReal_exists_subSquareLognormal_lt_le hγ le_rfl hu)
    rwa [Fintype.card_fin] at h
  have hs : 0 < 1 / (2 * lognormalVariance γ 4) := by
    have := lognormalVariance_pos hγ 4
    positivity
  obtain ⟨a₀, C₀, ha₀, hC₀, hbd⟩ := exists_rpow_decay_of_recursion (N := 2) le_rfl
    (ρ := 1 - η / 2) (lam0 := lam0) (u0 := lognormalShift γ 4) (K0 := 2)
    (s := 1 / (2 * lognormalVariance γ 4)) (C1 := C1) (by linarith) hlam0
    (lognormalShift_nonneg γ 4) (by norm_num) hs hC1 hl0 hl1 hanti hρl hβ1' hrecL
  -- the bootstrap
  have hmom : ∀ a : ℝ, 0 ≤ a → ∃ M : ℝ, 0 ≤ M ∧
      Integrable (fun ω : Ω0 × ℝ => ∏ i : Fin 2, subSquareLognormal γ hcirc0 4 ω i ^ (-a))
        (P0.prod (gaussianReal 0 1)) ∧
      ∫ ω, ∏ i : Fin 2, subSquareLognormal γ hcirc0 4 ω i ^ (-a) ∂(P0.prod (gaussianReal 0 1)) ≤
        M := fun a _ => ⟨_, integral_nonneg fun ω => Finset.prod_nonneg fun i _ =>
    Real.rpow_nonneg (subSquareLognormal_pos γ hcirc0 4 ω i).le _,
    hh0.integrable_prod_rpow_neg_subSquareLognormal γ 4 a, le_rfl⟩
  obtain ⟨C, hC0, hCb⟩ := rpowDecay_of_recursion (P := P0.prod (gaussianReal 0 1))
    (V := fun (i : Fin 2) (a : Ω0 × ℝ) => subSquareLognormal γ hcirc0 4 a i) (l := l) (β := β)
    (fun i a => subSquareLognormal_pos γ hcirc0 4 a i) hl0 hl1 hrec hβ hmom (by simp) ha₀
    ⟨C₀, hC₀.le, hbd⟩ ha
  exact ⟨C, hC0, fun Ω _ P _ hC hcirc hh n hn lam hlam =>
    (hle Ω P hC hcirc hh n hn lam hlam).trans (hCb lam hlam)⟩

end LatticeProb.Gauss

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- **Negative moments of the mass of the unit ball.** For `γ ≠ 0` with `γ² < 4` and every `q > 0`,
`E μ_γ(B(0,1))^{-q}` is bounded uniformly in the model of the whole-plane Gaussian free field. -/
theorem ballMassNegMoment_of_lt.{v} {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 4) {q : ℝ} (hq : 0 < q) :
    BallMassNegMoment.{v} γ q :=
  ballMassNegMoment_of_laplace_all measurableSet_lqgSquare lqgSquare_subset_closedBall
    (fun _ ha => exists_laplace_decay_all.{v} γ hγ hγ2 ha) hq

end LatticeProb.LQG
