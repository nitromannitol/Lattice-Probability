import Mathlib
import LatticeProb.Prob.PiDensity

/-!
# Decoupling of a product of integrals over separated pieces

An abstract Tonelli lemma: if two families of nonnegative functions `F x` and `G y` of a random
parameter decouple pointwise in `(x, y)`, with constant `c`, then the products of their
integrals in `x` and `y` decouple with the same constant.
-/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

section Tonelli

variable {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]

/-- **Tonelli form of a pointwise decoupling.** If `E[F x · G y] ≤ c E[F x] E[G y]` for all `x, y`,
then `E[(∫ F x dν₁)(∫ G y dν₂)] ≤ c E[∫ F x dν₁] E[∫ G y dν₂]`. -/
theorem lintegral_mul_lintegral_le_of_forall {P : Measure Ω} [SFinite P] {ν₁ : Measure X}
    {ν₂ : Measure Y} [SFinite ν₁] [SFinite ν₂] {F : X → Ω → ℝ≥0∞} {G : Y → Ω → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G)) (c : ℝ≥0∞)
    (h : ∀ x y, ∫⁻ ω, F x ω * G y ω ∂P ≤ c * ((∫⁻ ω, F x ω ∂P) * ∫⁻ ω, G y ω ∂P)) :
    ∫⁻ ω, (∫⁻ x, F x ω ∂ν₁) * (∫⁻ y, G y ω ∂ν₂) ∂P ≤
      c * ((∫⁻ ω, ∫⁻ x, F x ω ∂ν₁ ∂P) * ∫⁻ ω, ∫⁻ y, G y ω ∂ν₂ ∂P) := by
  have hFω : ∀ ω, Measurable fun x => F x ω := fun ω => hF.of_uncurry_right
  have hGω : ∀ ω, Measurable fun y => G y ω := fun ω => hG.of_uncurry_right
  have hFx : ∀ x, Measurable fun ω => F x ω := fun x => hF.of_uncurry_left
  have hGy : ∀ y, Measurable fun ω => G y ω := fun y => hG.of_uncurry_left
  have e1 : ∀ ω, (∫⁻ x, F x ω ∂ν₁) * (∫⁻ y, G y ω ∂ν₂) =
      ∫⁻ x, ∫⁻ y, F x ω * G y ω ∂ν₂ ∂ν₁ := fun ω => by
    calc (∫⁻ x, F x ω ∂ν₁) * (∫⁻ y, G y ω ∂ν₂)
        = ∫⁻ x, F x ω * ∫⁻ y, G y ω ∂ν₂ ∂ν₁ := (lintegral_mul_const _ (hFω ω)).symm
      _ = _ := lintegral_congr fun x => (lintegral_const_mul _ (hGω ω)).symm
  -- joint measurability of the integrand
  have hK : Measurable fun p : (Ω × X) × Y => F p.1.2 p.1.1 * G p.2 p.1.1 :=
    (hF.comp (by fun_prop : Measurable fun p : (Ω × X) × Y => (p.1.2, p.1.1))).mul
      (hG.comp (by fun_prop : Measurable fun p : (Ω × X) × Y => (p.2, p.1.1)))
  have hK1 : Measurable fun p : Ω × X => ∫⁻ y, F p.2 p.1 * G y p.1 ∂ν₂ :=
    hK.lintegral_prod_right'
  simp_rw [e1]
  rw [lintegral_lintegral_swap hK1.aemeasurable]
  have e2 : ∀ x, ∫⁻ ω, ∫⁻ y, F x ω * G y ω ∂ν₂ ∂P = ∫⁻ y, ∫⁻ ω, F x ω * G y ω ∂P ∂ν₂ :=
    fun x => by
      refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
      exact (hF.comp (by fun_prop : Measurable fun p : Ω × Y => (x, p.1))).mul
        (hG.comp (by fun_prop : Measurable fun p : Ω × Y => (p.2, p.1)))
  simp_rw [e2]
  calc ∫⁻ x, ∫⁻ y, ∫⁻ ω, F x ω * G y ω ∂P ∂ν₂ ∂ν₁
      ≤ ∫⁻ x, ∫⁻ y, c * ((∫⁻ ω, F x ω ∂P) * ∫⁻ ω, G y ω ∂P) ∂ν₂ ∂ν₁ :=
        lintegral_mono fun x => lintegral_mono fun y => h x y
    _ = c * ((∫⁻ x, ∫⁻ ω, F x ω ∂P ∂ν₁) * ∫⁻ y, ∫⁻ ω, G y ω ∂P ∂ν₂) := by
        have hFm : Measurable fun x => ∫⁻ ω, F x ω ∂P := hF.lintegral_prod_right'
        have hGm : Measurable fun y => ∫⁻ ω, G y ω ∂P := hG.lintegral_prod_right'
        have e3 : ∀ x, ∫⁻ y, c * ((∫⁻ ω, F x ω ∂P) * ∫⁻ ω, G y ω ∂P) ∂ν₂ =
            c * ((∫⁻ ω, F x ω ∂P) * ∫⁻ y, ∫⁻ ω, G y ω ∂P ∂ν₂) := fun x => by
          rw [lintegral_const_mul _ (hGm.const_mul _), lintegral_const_mul _ hGm]
        simp_rw [e3]
        rw [lintegral_const_mul _ (hFm.mul_const _), lintegral_mul_const _ hFm]
    _ = _ := by
        rw [lintegral_lintegral_swap (μ := ν₁) (ν := P) hF.aemeasurable,
          lintegral_lintegral_swap (μ := ν₂) (ν := P) hG.aemeasurable]

end Tonelli

section Pieces

universe u

variable {Ω : Type*} [MeasurableSpace Ω] {I : Type*}

/-- The mass of the piece `i` at the sample `ω`: `∫ w_i(x) m(x, ω) dx`. -/
noncomputable def pieceMass (w : I → ℂ → ℝ≥0∞) (m : ℂ → Ω → ℝ≥0∞) (i : I) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ x, w i x * m x ω

/-- A product of piece masses is a Lebesgue integral over a product space. -/
theorem prod_pieceMass_eq_lintegral {w : I → ℂ → ℝ≥0∞} {m : ℂ → Ω → ℝ≥0∞}
    (hw : ∀ i, Measurable (w i)) (hm : Measurable (Function.uncurry m)) {κ : Type*} [Fintype κ]
    (lab : κ → I) (ω : Ω) :
    ∏ s, pieceMass w m (lab s) ω =
      ∫⁻ x : κ → ℂ, ∏ s, (w (lab s) (x s) * m (x s) ω)
        ∂(Measure.pi fun _ : κ => (volume : Measure ℂ)) := by
  rw [lintegral_fintype_prod_eq_prod (ν := fun _ : κ => (volume : Measure ℂ))
    (fun s a => w (lab s) a * m a ω) (fun s => (hw _).mul hm.of_uncurry_right)]
  rfl

/-- Joint measurability of the product integrand in `(x, ω)`. -/
theorem measurable_uncurry_prod_weight_mul {w : I → ℂ → ℝ≥0∞} {m : ℂ → Ω → ℝ≥0∞}
    (hw : ∀ i, Measurable (w i)) (hm : Measurable (Function.uncurry m)) {κ : Type*} [Fintype κ]
    (lab : κ → I) :
    Measurable (Function.uncurry fun (x : κ → ℂ) (ω : Ω) => ∏ s, (w (lab s) (x s) * m (x s) ω)) := by
  refine Finset.measurable_prod _ fun j _ => ?_
  have h1 : Measurable fun a : (κ → ℂ) × Ω => a.1 j := (measurable_pi_apply j).comp measurable_fst
  exact ((hw _).comp h1).mul
    (show Measurable fun a : (κ → ℂ) × Ω => m (a.1 j) a.2 from hm.comp (h1.prodMk measurable_snd))

/-- **Decoupling of a product of piece masses.** -/
theorem lintegral_prod_pieceMass_le {P : Measure Ω} [IsProbabilityMeasure P]
    {w : I → ℂ → ℝ≥0∞} {m : ℂ → Ω → ℝ≥0∞} {Λ : ℝ≥0∞} (hΛ : 1 ≤ Λ)
    (hw : ∀ i, Measurable (w i)) (hm : Measurable (Function.uncurry m))
    (hdec : ∀ {κ₁ κ₂ : Type u} [Fintype κ₁] [Fintype κ₂] (lab₁ : κ₁ → I) (lab₂ : κ₂ → I),
      (∀ j k, lab₁ j ≠ lab₂ k) → ∀ (x : κ₁ → ℂ) (y : κ₂ → ℂ),
        (∀ j, w (lab₁ j) (x j) ≠ 0) → (∀ k, w (lab₂ k) (y k) ≠ 0) →
        ∫⁻ ω, (∏ j, m (x j) ω) * ∏ k, m (y k) ω ∂P ≤
          Λ ^ (Nat.card κ₁ * Nat.card κ₂) *
            ((∫⁻ ω, ∏ j, m (x j) ω ∂P) * ∫⁻ ω, ∏ k, m (y k) ω ∂P))
    [DecidableEq I] (T : Finset I) :
    ∀ (ι : Type u) [Fintype ι] (lab : ι → I), (∀ s, lab s ∈ T) →
      ∫⁻ ω, ∏ s, pieceMass w m (lab s) ω ∂P ≤
        Λ ^ (Nat.card ι * Nat.card ι) *
          ∏ i ∈ T, ∫⁻ ω, pieceMass w m i ω ^ Nat.card {s // lab s = i} ∂P := by
  induction T using Finset.induction_on with
  | empty =>
    intro ι _ lab hlab
    have : IsEmpty ι := ⟨fun s => absurd (hlab s) (Finset.notMem_empty _)⟩
    simp
  | insert i0 T hi0 ih =>
    intro ι _ lab hlab
    let p : ι → Prop := fun s => lab s = i0
    let lab₁ : {s // p s} → I := fun s => lab s.1
    let lab₂ : {s // ¬ p s} → I := fun s => lab s.1
    let F : ({s // p s} → ℂ) → Ω → ℝ≥0∞ := fun x ω => ∏ j, (w (lab₁ j) (x j) * m (x j) ω)
    let G : ({s // ¬ p s} → ℂ) → Ω → ℝ≥0∞ := fun y ω => ∏ k, (w (lab₂ k) (y k) * m (y k) ω)
    have hsplit : ∀ ω, ∏ s, pieceMass w m (lab s) ω =
        (∏ s : {s // p s}, pieceMass w m (lab₁ s) ω) *
          ∏ s : {s // ¬ p s}, pieceMass w m (lab₂ s) ω := fun ω =>
      (Fintype.prod_subtype_mul_prod_subtype p (fun s => pieceMass w m (lab s) ω)).symm
    have eA : ∀ ω, ∏ s : {s // p s}, pieceMass w m (lab₁ s) ω =
        ∫⁻ x, F x ω ∂(Measure.pi fun _ : {s // p s} => (volume : Measure ℂ)) := fun ω =>
      prod_pieceMass_eq_lintegral hw hm lab₁ ω
    have eB : ∀ ω, ∏ s : {s // ¬ p s}, pieceMass w m (lab₂ s) ω =
        ∫⁻ y, G y ω ∂(Measure.pi fun _ : {s // ¬ p s} => (volume : Measure ℂ)) := fun ω =>
      prod_pieceMass_eq_lintegral hw hm lab₂ ω
    have hF : Measurable (Function.uncurry F) := measurable_uncurry_prod_weight_mul hw hm lab₁
    have hG : Measurable (Function.uncurry G) := measurable_uncurry_prod_weight_mul hw hm lab₂
    have hpoint : ∀ x y, ∫⁻ ω, F x ω * G y ω ∂P ≤
        Λ ^ (Nat.card {s // p s} * Nat.card {s // ¬ p s}) *
          ((∫⁻ ω, F x ω ∂P) * ∫⁻ ω, G y ω ∂P) := by
      intro x y
      by_cases hx : ∀ j, w (lab₁ j) (x j) ≠ 0
      · by_cases hy : ∀ k, w (lab₂ k) (y k) ≠ 0
        · have hsepl : ∀ j k, lab₁ j ≠ lab₂ k := fun j k h => k.2 (h.symm.trans j.2)
          have hd := hdec lab₁ lab₂ hsepl x y hx hy
          have eF : ∀ ω, F x ω = (∏ j, w (lab₁ j) (x j)) * ∏ j, m (x j) ω := fun ω =>
            Finset.prod_mul_distrib
          have eG : ∀ ω, G y ω = (∏ k, w (lab₂ k) (y k)) * ∏ k, m (y k) ω := fun ω =>
            Finset.prod_mul_distrib
          have hMx : Measurable fun ω => ∏ j, m (x j) ω :=
            Finset.measurable_prod _ fun j _ => hm.of_uncurry_left
          have hMy : Measurable fun ω => ∏ k, m (y k) ω :=
            Finset.measurable_prod _ fun j _ => hm.of_uncurry_left
          have iF : ∫⁻ ω, F x ω ∂P = (∏ j, w (lab₁ j) (x j)) * ∫⁻ ω, ∏ j, m (x j) ω ∂P := by
            simp_rw [eF]; exact lintegral_const_mul _ hMx
          have iG : ∫⁻ ω, G y ω ∂P = (∏ k, w (lab₂ k) (y k)) * ∫⁻ ω, ∏ k, m (y k) ω ∂P := by
            simp_rw [eG]; exact lintegral_const_mul _ hMy
          calc ∫⁻ ω, F x ω * G y ω ∂P
              = ((∏ j, w (lab₁ j) (x j)) * ∏ k, w (lab₂ k) (y k)) *
                  ∫⁻ ω, (∏ j, m (x j) ω) * ∏ k, m (y k) ω ∂P := by
                rw [← lintegral_const_mul (f := fun ω => (∏ j, m (x j) ω) * ∏ k, m (y k) ω) _ (hMx.mul hMy)]
                exact lintegral_congr fun ω => by rw [eF, eG]; ring
            _ ≤ ((∏ j, w (lab₁ j) (x j)) * ∏ k, w (lab₂ k) (y k)) *
                  (Λ ^ (Nat.card {s // p s} * Nat.card {s // ¬ p s}) *
                    ((∫⁻ ω, ∏ j, m (x j) ω ∂P) * ∫⁻ ω, ∏ k, m (y k) ω ∂P)) :=
                mul_le_mul' le_rfl hd
            _ = _ := by rw [iF, iG]; ring
        · obtain ⟨k, hk⟩ := not_forall.1 hy
          have hk : w (lab₂ k) (y k) = 0 := not_not.1 hk
          have h0 : ∀ ω, G y ω = 0 := fun ω =>
            Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk, zero_mul])
          simp [h0]
      · obtain ⟨j, hj⟩ := not_forall.1 hx
        have hj : w (lab₁ j) (x j) = 0 := not_not.1 hj
        have h0 : ∀ ω, F x ω = 0 := fun ω =>
          Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, zero_mul])
        simp [h0]
    have hmain : ∫⁻ ω, ∏ s, pieceMass w m (lab s) ω ∂P ≤
        Λ ^ (Nat.card {s // p s} * Nat.card {s // ¬ p s}) *
          ((∫⁻ ω, ∏ s : {s // p s}, pieceMass w m (lab₁ s) ω ∂P) *
            ∫⁻ ω, ∏ s : {s // ¬ p s}, pieceMass w m (lab₂ s) ω ∂P) := by
      calc ∫⁻ ω, ∏ s, pieceMass w m (lab s) ω ∂P
          = ∫⁻ ω, (∫⁻ x, F x ω ∂(Measure.pi fun _ : {s // p s} => (volume : Measure ℂ))) *
              ∫⁻ y, G y ω ∂(Measure.pi fun _ : {s // ¬ p s} => (volume : Measure ℂ)) ∂P :=
            lintegral_congr fun ω => by rw [hsplit, eA, eB]
        _ ≤ _ := lintegral_mul_lintegral_le_of_forall hF hG _ hpoint
        _ = _ := by
            rw [lintegral_congr fun ω => (eA ω).symm, lintegral_congr fun ω => (eB ω).symm]
    have hA : ∀ ω, ∏ s : {s // p s}, pieceMass w m (lab₁ s) ω =
        pieceMass w m i0 ω ^ Nat.card {s // p s} := fun ω => by
      rw [Finset.prod_congr rfl (fun s _ => show pieceMass w m (lab₁ s) ω = pieceMass w m i0 ω from
        by show pieceMass w m (lab s.1) ω = _; rw [show lab s.1 = i0 from s.2]),
        Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
    have hB := ih {s // ¬ p s} lab₂ (fun s => by
      rcases Finset.mem_insert.1 (hlab s.1) with h | h
      · exact absurd h s.2
      · exact h)
    have hcard : ∀ i ∈ T, Nat.card {s : {s // ¬ p s} // lab₂ s = i} = Nat.card {s // lab s = i} :=
      fun i hi => Nat.card_congr
        { toFun := fun s => ⟨s.1.1, s.2⟩
          invFun := fun t => ⟨⟨t.1, fun h => hi0 (by
            have : i0 = i := h.symm.trans t.2
            rw [this]; exact hi)⟩, t.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hn : Nat.card ι = Nat.card {s // p s} + Nat.card {s // ¬ p s} := by
      rw [← Nat.card_sum]; exact (Nat.card_congr (Equiv.sumCompl p)).symm
    have hprodeq : ∏ i ∈ T, ∫⁻ ω, pieceMass w m i ω ^ Nat.card {s : {s // ¬ p s} // lab₂ s = i} ∂P =
        ∏ i ∈ T, ∫⁻ ω, pieceMass w m i ω ^ Nat.card {s // lab s = i} ∂P :=
      Finset.prod_congr rfl fun i hi => by rw [hcard i hi]
    rw [hprodeq] at hB
    rw [Finset.prod_insert hi0]
    calc ∫⁻ ω, ∏ s, pieceMass w m (lab s) ω ∂P
        ≤ _ := hmain
      _ ≤ Λ ^ (Nat.card {s // p s} * Nat.card {s // ¬ p s}) *
            ((∫⁻ ω, pieceMass w m i0 ω ^ Nat.card {s // p s} ∂P) *
              (Λ ^ (Nat.card {s // ¬ p s} * Nat.card {s // ¬ p s}) *
                ∏ i ∈ T, ∫⁻ ω, pieceMass w m i ω ^ Nat.card {s // lab s = i} ∂P)) := by
          rw [lintegral_congr hA]
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hB)
      _ = (Λ ^ (Nat.card {s // p s} * Nat.card {s // ¬ p s}) *
            Λ ^ (Nat.card {s // ¬ p s} * Nat.card {s // ¬ p s})) *
            ((∫⁻ ω, pieceMass w m i0 ω ^ Nat.card {s // p s} ∂P) *
              ∏ i ∈ T, ∫⁻ ω, pieceMass w m i ω ^ Nat.card {s // lab s = i} ∂P) := by ring
      _ ≤ Λ ^ (Nat.card ι * Nat.card ι) *
            ((∫⁻ ω, pieceMass w m i0 ω ^ Nat.card {s // lab s = i0} ∂P) *
              ∏ i ∈ T, ∫⁻ ω, pieceMass w m i ω ^ Nat.card {s // lab s = i} ∂P) := by
          refine mul_le_mul' ?_ le_rfl
          rw [← pow_add, hn]
          exact pow_le_pow_right₀ hΛ (by nlinarith)

end Pieces

end LatticeProb
