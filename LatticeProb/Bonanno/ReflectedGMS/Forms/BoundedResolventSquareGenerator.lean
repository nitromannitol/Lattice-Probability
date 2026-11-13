/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.BoundedResolventSquareGenerator at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventSquareGenerator
import LatticeProb.Bonanno.ReflectedGMS.Forms.BoundedDomainDensity
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventMarkov

/-!
# Weak square-generator identity for bounded resolvent inputs

This file extends the analytic square-generator identity from vertex-indicator
forcings to the one-resolvent of an arbitrary bounded vertex function.  All
tests remain in the full finite-energy domain.
-/

set_option autoImplicit false

open scoped BigOperators InnerProductSpace

namespace ReflectedGMS

open FullNetworkForm

variable {V : Type*}

/-- The analytic square-generator expression for the one-resolvent of `f`.
Here the generator drift is `u - f`, where `u = R₁ f`. -/
noncomputable def boundedResolventSquareGenerator
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (f : V → ℝ) (hf : HasSpeedL2 m f) (x : V) : ℝ :=
  let u := oneResolventFunction G m (weightedValue m f hf)
  2 * u x * (u x - f x) + vertexCarreDuChamp G m u x

/-- The speed pairing of two speed-`L²` functions is summable. -/
theorem summable_speed_mul_mul_of_hasSpeedL2
    (m : V → ℝ) (hm : ∀ x, 0 < m x) (f g : V → ℝ)
    (hf : HasSpeedL2 m f) (hg : HasSpeedL2 m g) :
    Summable (fun x : V ↦ m x * f x * g x) := by
  have hs := lp.summable_inner (𝕜 := ℝ) (G := fun _ : V => ℝ)
    (weightedValue m f hf) (weightedValue m g hg)
  refine hs.congr (fun x ↦ ?_)
  simp only [Real.inner_apply, weightedValue_apply]
  have hsqrt : Real.sqrt (m x) * Real.sqrt (m x) = m x :=
    Real.mul_self_sqrt (hm x).le
  rw [show Real.sqrt (m x) * f x * (Real.sqrt (m x) * g x) =
      (Real.sqrt (m x) * Real.sqrt (m x)) * f x * g x by ring,
    hsqrt]

/-- The one-resolvent of a bounded vertex input is bounded.  The conclusion is
stated existentially so it also covers the empty vertex type without an
artificial sign condition on the supplied bound. -/
theorem boundedInput_oneResolvent_bounded
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ x, 0 < m x) (hmsum : Summable m)
    (f : V → ℝ) {A : ℝ} (hfBound : ∀ x, |f x| ≤ A) :
    ∃ N : ℝ, ∀ x,
      |oneResolventFunction G m
        (weightedValue m f (hasSpeedL2_of_abs_le hm hmsum hfBound)) x| ≤ N := by
  let hfL2 : HasSpeedL2 m f := hasSpeedL2_of_abs_le hm hmsum hfBound
  obtain ⟨n, hn⟩ := exists_nat_ge (max A 0)
  have hfN (x : V) : |f x| ≤ (n : ℝ) :=
    (hfBound x).trans (le_max_left A 0) |>.trans hn
  have hfix (x : V) :
      boundedTruncation n
          (unweight m (weightedValue m f hfL2) x) =
        unweight m (weightedValue m f hfL2) x := by
    rw [unweight_weightedValue m hm]
    have hx := abs_le.mp (hfN x)
    simp [boundedTruncation, Set.coe_projIcc, hx.1, hx.2]
  have hinv := oneResolventFunction_contraction_fixed G m hm
    (weightedValue m f hfL2) (boundedTruncation_lipschitz n)
    (boundedTruncation_zero n) hfix
  refine ⟨n, fun x ↦ ?_⟩
  have hx := congrFun hinv x
  simp only [Function.comp_apply] at hx
  rw [← hx]
  exact abs_boundedTruncation_le n _

/-- A bounded input's one-resolvent belongs to the full finite-energy domain. -/
theorem boundedInput_oneResolvent_hasFiniteEnergy
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ x, 0 < m x) (hmsum : Summable m)
    (f : V → ℝ) {A : ℝ} (hfBound : ∀ x, |f x| ≤ A) :
    G.HasFiniteEnergy (oneResolventFunction G m
      (weightedValue m f (hasSpeedL2_of_abs_le hm hmsum hfBound))) :=
  oneResolventFunction_hasFiniteEnergy G m _

/-- Full-domain weak identity for the one-resolvent of a bounded input. -/
theorem boundedInput_oneResolvent_weak
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ x, 0 < m x) (hmsum : Summable m)
    (f : V → ℝ) {A : ℝ} (hfBound : ∀ x, |f x| ≤ A)
    (v : V → ℝ) {B : ℝ} (hvBound : ∀ x, |v x| ≤ B)
    (hv : G.HasFiniteEnergy v) :
    G.dirichletForm
        (oneResolventFunction G m
          (weightedValue m f (hasSpeedL2_of_abs_le hm hmsum hfBound))) v =
      -∑' x : V, m x *
        (oneResolventFunction G m
          (weightedValue m f (hasSpeedL2_of_abs_le hm hmsum hfBound)) x - f x) * v x := by
  let hfL2 : HasSpeedL2 m f := hasSpeedL2_of_abs_le hm hmsum hfBound
  let F := weightedValue m f hfL2
  let u := oneResolventFunction G m F
  have hvL2 : HasSpeedL2 m v := hasSpeedL2_of_abs_le hm hmsum hvBound
  have huL2 : HasSpeedL2 m u := oneResolventFunction_hasSpeedL2 G m hm F
  have hweak := oneResolventFunction_weak G m hm F v hvL2 hv
  have huweight : weightedValue m u huL2 = oneResolvent G m F := by
    exact weightedValue_unweight m hm (oneResolvent G m F)
  have hinneru : ⟪oneResolvent G m F, weightedValue m v hvL2⟫_ℝ =
      ∑' x : V, m x * u x * v x := by
    rw [← huweight]
    exact inner_weightedValue_eq_tsum m hm u v huL2 hvL2
  have hinnerf : ⟪F, weightedValue m v hvL2⟫_ℝ =
      ∑' x : V, m x * f x * v x :=
    inner_weightedValue_eq_tsum m hm f v hfL2 hvL2
  rw [hinneru, hinnerf] at hweak
  have husum : Summable (fun x : V ↦ m x * u x * v x) :=
    summable_speed_mul_mul_of_hasSpeedL2 m hm u v huL2 hvL2
  have hfsum : Summable (fun x : V ↦ m x * f x * v x) :=
    summable_speed_mul_mul_of_hasSpeedL2 m hm f v hfL2 hvL2
  have hdiff : (∑' x : V, m x * (u x - f x) * v x) =
      (∑' x : V, m x * u x * v x) - ∑' x : V, m x * f x * v x := by
    rw [← husum.tsum_sub hfsum]
    apply tsum_congr
    intro x
    ring
  dsimp only [u, F, hfL2] at hweak hdiff ⊢
  rw [hdiff]
  linarith

/-- The speed-weighted square-generator of a bounded input's one-resolvent is
absolutely summable. -/
theorem summable_speed_mul_boundedResolventSquareGenerator
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ x, 0 < m x) (hmsum : Summable m)
    (f : V → ℝ) {A : ℝ} (hfBound : ∀ x, |f x| ≤ A) :
    Summable (fun x : V ↦ m x * boundedResolventSquareGenerator G m f
      (hasSpeedL2_of_abs_le hm hmsum hfBound) x) := by
  let hfL2 : HasSpeedL2 m f := hasSpeedL2_of_abs_le hm hmsum hfBound
  let u := oneResolventFunction G m (weightedValue m f hfL2)
  let b := u - f
  obtain ⟨N, huBound⟩ := boundedInput_oneResolvent_bounded G m hm hmsum f hfBound
  have hfBound' (x : V) : |f x| ≤ max A 0 :=
    (hfBound x).trans (le_max_left A 0)
  have hbBound (x : V) : |b x| ≤ N + max A 0 := by
    dsimp only [b]
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (huBound x) (hfBound' x))
  have huL2 : HasSpeedL2 m u := oneResolventFunction_hasSpeedL2 G m hm _
  have hbL2 : HasSpeedL2 m b := hasSpeedL2_of_abs_le hm hmsum hbBound
  have hdriftBase : Summable (fun x : V ↦ m x * u x * b x) :=
    summable_speed_mul_mul_of_hasSpeedL2 m hm u b huL2 hbL2
  have hdrift : Summable (fun x : V ↦ m x * (2 * u x * b x)) := by
    refine (hdriftBase.mul_right 2).congr (fun x ↦ ?_)
    ring
  have huE : G.HasFiniteEnergy u := oneResolventFunction_hasFiniteEnergy G m _
  have hgamma := summable_speed_mul_vertexCarreDuChamp G m hm huE
  refine (hdrift.add hgamma).congr (fun x ↦ ?_)
  simp only [boundedResolventSquareGenerator, u, b, Pi.sub_apply]
  ring

/-- Exact weak square-generator identity for bounded inputs, tested against
every bounded member of the full finite-energy domain. -/
theorem boundedResolvent_squareGenerator_weak
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ x, 0 < m x) (hmsum : Summable m)
    (f : V → ℝ) {A : ℝ} (hfBound : ∀ x, |f x| ≤ A)
    (v : V → ℝ) {B : ℝ} (hvBound : ∀ x, |v x| ≤ B)
    (hv : G.HasFiniteEnergy v) :
    G.dirichletForm
        ((oneResolventFunction G m
          (weightedValue m f (hasSpeedL2_of_abs_le hm hmsum hfBound))) ^ 2) v =
      -∑' x : V, m x * boundedResolventSquareGenerator G m f
        (hasSpeedL2_of_abs_le hm hmsum hfBound) x * v x := by
  let hfL2 : HasSpeedL2 m f := hasSpeedL2_of_abs_le hm hmsum hfBound
  let u := oneResolventFunction G m (weightedValue m f hfL2)
  let b := u - f
  obtain ⟨N, huBound⟩ := boundedInput_oneResolvent_bounded G m hm hmsum f hfBound
  have hvBound' (x : V) : |v x| ≤ max B 0 :=
    (hvBound x).trans (le_max_left B 0)
  have hfBound' (x : V) : |f x| ≤ max A 0 :=
    (hfBound x).trans (le_max_left A 0)
  have hbBound (x : V) : |b x| ≤ N + max A 0 := by
    dsimp only [b]
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (huBound x) (hfBound' x))
  have hu : G.HasFiniteEnergy u := oneResolventFunction_hasFiniteEnergy G m _
  have huvBound (x : V) : |(u * v) x| ≤ N * max B 0 := by
    simp only [Pi.mul_apply, abs_mul]
    exact mul_le_mul (huBound x) (hvBound' x) (abs_nonneg _)
      ((abs_nonneg _).trans (huBound x))
  have huv : G.HasFiniteEnergy (u * v) :=
    hasFiniteEnergy_mul_of_bounded G huBound hvBound' hu hv
  have hresolvent := boundedInput_oneResolvent_weak G m hm hmsum f hfBound
    (u * v) huvBound huv
  have hcarre := fullEnergy_carreDuChamp_identity G m hm
    huBound hvBound' hu hv
  have hbL2 : HasSpeedL2 m b := hasSpeedL2_of_abs_le hm hmsum hbBound
  have huvL2 : HasSpeedL2 m (u * v) :=
    hasSpeedL2_of_abs_le hm hmsum huvBound
  have hdrift : Summable (fun x : V ↦ m x * b x * (u x * v x)) := by
    simpa only [Pi.mul_apply] using
      summable_speed_mul_mul_of_hasSpeedL2 m hm b (u * v) hbL2 huvL2
  have hgammaBase := summable_speed_mul_vertexCarreDuChamp G m hm hu
  have hgamma : Summable (fun x : V ↦
      m x * vertexCarreDuChamp G m u x * v x) := by
    apply Summable.of_norm_bounded (hgammaBase.mul_left (max B 0))
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (hm x),
      abs_of_nonneg (vertexCarreDuChamp_nonneg G m hm u x)]
    calc
      m x * vertexCarreDuChamp G m u x * |v x| ≤
          m x * vertexCarreDuChamp G m u x * max B 0 :=
        mul_le_mul_of_nonneg_left (hvBound' x)
          (mul_nonneg (hm x).le (vertexCarreDuChamp_nonneg G m hm u x))
      _ = max B 0 * (m x * vertexCarreDuChamp G m u x) := by ring
  have hsum :
      (∑' x : V, m x * boundedResolventSquareGenerator G m f hfL2 x * v x) =
        2 * (∑' x : V, m x * b x * (u x * v x)) +
          ∑' x : V, m x * vertexCarreDuChamp G m u x * v x := by
    rw [← hdrift.tsum_mul_left 2, ← hdrift.mul_left 2 |>.tsum_add hgamma]
    apply tsum_congr
    intro x
    simp only [boundedResolventSquareGenerator, u, b, Pi.sub_apply]
    ring
  have hresolvent' :
      G.dirichletForm u (u * v) =
        -∑' x : V, m x * b x * (u x * v x) := by
    simpa only [u, b, hfL2, Pi.mul_apply, Pi.sub_apply] using hresolvent
  have hcarre' :
      G.dirichletForm (u ^ 2) v =
        2 * G.dirichletForm u (u * v) -
          ∑' x : V, m x * vertexCarreDuChamp G m u x * v x := by
    simpa only [u, hfL2] using hcarre
  change G.dirichletForm (u ^ 2) v =
    -∑' x : V, m x * boundedResolventSquareGenerator G m f hfL2 x * v x
  rw [hcarre', hresolvent', hsum]
  ring

end ReflectedGMS
