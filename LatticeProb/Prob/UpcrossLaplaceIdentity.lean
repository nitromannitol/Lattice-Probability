import Mathlib
import LatticeProb.Prob.UpcrossLebesgueDuality
import LatticeProb.Prob.UpcrossRenewal
import LatticeProb.Prob.UpcrossRenewalReturn
import LatticeProb.Prob.UpcrossReturnLaplace
import LatticeProb.Prob.LaplaceIndicator
import LatticeProb.Prob.BrownianLaplaceHitZero
import LatticeProb.Prob.ExpNegLimit

/-!
# Laplace identity for the first up-crossing piece

For a Brownian motion `B` with continuous paths, a drift `mu > 0`, a level `c > 0`, `q > 0` and a
functional `f` of the first up-crossing piece (a path from `0` to `c`), the weighted integrals
`∫ f(piece) e^{-q d₁} dμ₀` over the law `μ₀` of `B + mu s` coincide for `f` and for `f ∘ upcrossRev c`
(time reversal of the piece).  For `q → 0` the same holds without weight.

The proof multiplies the Lebesgue-start duality `lintegral_lebesgue_upcrossOnce_rev` by the density
`q e^{-qt}` and integrates in `t`; the window `d₁ ≤ t < d₂` integrates to `e^{-q d₁} - e^{-q d₂}`,
and the renewal identities at the first zero and at the end of the first up-crossing interval turn
this into a constant (independent of `f`) times `∫ f(piece) e^{-q d₁} dμ₀`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

section Pointwise

/-- Laplace transform in `t` of the window functional `upcrossOnce c t f w`. -/
theorem lintegral_laplace_upcrossOnce {q : ℝ} (hq : 0 < q) (c : ℝ) (f : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (w : ℝ≥0 → ℝ) :
    ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-(q * t))) *
        upcrossOnce c t.toNNReal f w
      = f (firstUpcrossPiece c w) * (expNeg q (upcrossEnd₁ c w) - expNeg q (upcrossEnd₂ c w)) := by
  have hle : upcrossEnd₁ c w ≤ upcrossEnd₂ c w :=
    (le_hitFrom : upcrossEnd₁ c w ≤ hitFrom 0 (upcrossEnd₁ c w) w).trans le_hitFrom
  set S : Set ℝ := {t : ℝ | upcrossEnd₁ c w ≤ ENNReal.ofReal t ∧
    ENNReal.ofReal t < upcrossEnd₂ c w} with hS
  have hSm : MeasurableSet S := by
    have h1 : Measurable fun t : ℝ => ENNReal.ofReal t := ENNReal.measurable_ofReal
    exact (measurableSet_le measurable_const h1).inter (measurableSet_lt h1 measurable_const)
  have key : ∀ t : ℝ, ENNReal.ofReal (q * Real.exp (-(q * t))) * upcrossOnce c t.toNNReal f w
      = f (firstUpcrossPiece c w) *
        S.indicator (fun t => ENNReal.ofReal (q * Real.exp (-(q * t)))) t := by
    intro t
    unfold upcrossOnce
    by_cases h : t ∈ S
    · have h' : upcrossEnd₁ c w ≤ ((t.toNNReal : ℝ≥0) : ℝ≥0∞) ∧
          ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < upcrossEnd₂ c w := h
      simp only [h', Set.indicator_of_mem h]
      exact mul_comm _ _
    · have h' : ¬ (upcrossEnd₁ c w ≤ ((t.toNNReal : ℝ≥0) : ℝ≥0∞) ∧
          ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < upcrossEnd₂ c w) := h
      simp only [h', ↓reduceIte, Set.indicator_of_notMem h, mul_zero]
  have hm : Measurable (S.indicator fun t : ℝ => ENNReal.ofReal (q * Real.exp (-(q * t)))) :=
    (ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg))).indicator
      hSm
  rw [lintegral_congr key, lintegral_const_mul _ hm, lintegral_laplace_Ico_ennreal hq hle]

end Pointwise

section Tonelli

/-- The density `t ↦ q e^{-qt}` is measurable. -/
theorem measurable_laplaceDensity (q : ℝ) :
    Measurable fun t : ℝ => ENNReal.ofReal (q * Real.exp (-(q * t))) :=
  ENNReal.measurable_ofReal.comp
    (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg))

variable {Z : Type*} [MeasurableSpace Z] {ν : Measure Z} [SFinite ν]

/-- Joint measurability in the time `t` and a path-valued random element of the window
functional. -/
theorem measurable_upcrossOnce_time {Φ : Z → C(ℝ≥0, ℝ)} (hΦ : Measurable Φ) {c : ℝ}
    {f : (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hf : Measurable fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ))) :
    Measurable fun p : ℝ × Z => upcrossOnce c p.1.toNNReal f (Φ p.2 : ℝ≥0 → ℝ) := by
  classical
  have ht : Measurable fun p : ℝ × Z => ((p.1.toNNReal : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.measurable_ofReal.comp measurable_fst
  have h1 : Measurable fun p : ℝ × Z => upcrossEnd₁ c (Φ p.2 : ℝ≥0 → ℝ) :=
    (measurable_upcrossEnd₁ c).comp (hΦ.comp measurable_snd)
  have h2 : Measurable fun p : ℝ × Z => upcrossEnd₂ c (Φ p.2 : ℝ≥0 → ℝ) :=
    (measurable_upcrossEnd₂ c).comp (hΦ.comp measurable_snd)
  have h3 : Measurable fun p : ℝ × Z => f (firstUpcrossPiece c (Φ p.2 : ℝ≥0 → ℝ)) :=
    hf.comp (hΦ.comp measurable_snd)
  unfold upcrossOnce
  exact Measurable.ite ((measurableSet_le h1 ht).inter (measurableSet_lt ht h2)) h3 measurable_const

/-- Laplace transform in `t` of the up-crossing window functional integrated against `ν`. -/
theorem lintegral_laplace_upcrossOnce_tonelli {Φ : Z → C(ℝ≥0, ℝ)} (hΦ : Measurable Φ) {q : ℝ}
    (hq : 0 < q) {c : ℝ} {f : (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hf : Measurable fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ))) :
    ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-(q * t))) *
        ∫⁻ z, upcrossOnce c t.toNNReal f (Φ z : ℝ≥0 → ℝ) ∂ν
      = ∫⁻ z, f (firstUpcrossPiece c (Φ z : ℝ≥0 → ℝ)) *
          (expNeg q (upcrossEnd₁ c (Φ z : ℝ≥0 → ℝ)) -
            expNeg q (upcrossEnd₂ c (Φ z : ℝ≥0 → ℝ))) ∂ν := by
  have hΨ' : Measurable fun p : ℝ × Z => upcrossOnce c p.1.toNNReal f (Φ p.2 : ℝ≥0 → ℝ) :=
    measurable_upcrossOnce_time hΦ hf
  have hJ : Measurable fun p : ℝ × Z =>
      ENNReal.ofReal (q * Real.exp (-(q * p.1))) * upcrossOnce c p.1.toNNReal f (Φ p.2 : ℝ≥0 → ℝ) :=
    ((measurable_laplaceDensity q).comp measurable_fst).mul hΨ'
  have e1 : ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-(q * t))) *
          ∫⁻ z, upcrossOnce c t.toNNReal f (Φ z : ℝ≥0 → ℝ) ∂ν
      = ∫⁻ t in Set.Ici (0 : ℝ), ∫⁻ z, ENNReal.ofReal (q * Real.exp (-(q * t))) *
          upcrossOnce c t.toNNReal f (Φ z : ℝ≥0 → ℝ) ∂ν :=
    lintegral_congr fun t => (lintegral_const_mul _ (hΨ'.comp measurable_prodMk_left)).symm
  have e2 := lintegral_lintegral_swap (μ := volume.restrict (Set.Ici (0 : ℝ))) (ν := ν)
    (f := fun t z => ENNReal.ofReal (q * Real.exp (-(q * t))) *
      upcrossOnce c t.toNNReal f (Φ z : ℝ≥0 → ℝ)) hJ.aemeasurable
  rw [e1, e2]
  exact lintegral_congr fun z => lintegral_laplace_upcrossOnce hq c f (Φ z : ℝ≥0 → ℝ)

end Tonelli

/-- The process `(x, ω) ↦ (s ↦ x + B s ω + mu * s)` as a map into path space. -/
theorem measurable_affinePath_pair (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ) :
    Measurable fun z : ℝ × Ω => affinePath z.1 mu (pathMap B hcont z.2) :=
  measurable_pathValued_of_eval fun s => by
    simp only [affinePath_apply, pathMap_apply]
    exact (measurable_fst.add ((hm s).comp measurable_snd)).add measurable_const

/-- **Laplace identity, `e^{-q d₁} - e^{-q d₂}` form.**  Integrating the Lebesgue-start duality
against `q e^{-qt}` in `t`, the weight `f(piece)(e^{-q d₁} - e^{-q d₂})` has the same integral over a
Lebesgue starting point and `ω` for `f` and for `f ∘ upcrossRev c`. -/
theorem lintegral_lebesgue_laplace_diff_rev [IsProbabilityMeasure P] (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ) {c : ℝ}
    (hc : 0 < c) {q : ℝ} (hq : 0 < q) {f : (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hf : Measurable fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)))
    (hf' : Measurable fun w : C(ℝ≥0, ℝ) => f (upcrossRev c (firstUpcrossPiece c (w : ℝ≥0 → ℝ)))) :
    ∫⁻ x : ℝ, ∫⁻ ω, f (firstUpcrossPiece c (fun s => x + B s ω + mu * (s : ℝ))) *
        (expNeg q (upcrossEnd₁ c (fun s => x + B s ω + mu * (s : ℝ))) -
          expNeg q (upcrossEnd₂ c (fun s => x + B s ω + mu * (s : ℝ)))) ∂P
      = ∫⁻ x : ℝ, ∫⁻ ω, f (upcrossRev c (firstUpcrossPiece c (fun s => x + B s ω + mu * (s : ℝ)))) *
        (expNeg q (upcrossEnd₁ c (fun s => x + B s ω + mu * (s : ℝ))) -
          expNeg q (upcrossEnd₂ c (fun s => x + B s ω + mu * (s : ℝ)))) ∂P := by
  set Φ : ℝ × Ω → C(ℝ≥0, ℝ) := fun z => affinePath z.1 mu (pathMap B hcont z.2) with hΦdef
  have hΦ : Measurable Φ := measurable_affinePath_pair hm hcont mu
  set g : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun p => f (upcrossRev c p) with hg
  have hg' : Measurable fun w : C(ℝ≥0, ℝ) => g (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) := hf'
  have hdiff : ∀ {h : (ℝ≥0 → ℝ) → ℝ≥0∞}
      (_ : Measurable fun w : C(ℝ≥0, ℝ) => h (firstUpcrossPiece c (w : ℝ≥0 → ℝ))),
      Measurable fun z : ℝ × Ω => h (firstUpcrossPiece c (Φ z)) *
        (expNeg q (upcrossEnd₁ c (Φ z)) - expNeg q (upcrossEnd₂ c (Φ z))) := fun {h} hh =>
    (hh.comp hΦ).mul
      (((measurable_expNeg q).comp ((measurable_upcrossEnd₁ c).comp hΦ)).sub
        ((measurable_expNeg q).comp ((measurable_upcrossEnd₂ c).comp hΦ)))
  have hmeasO : ∀ {h : (ℝ≥0 → ℝ) → ℝ≥0∞}
      (_ : Measurable fun w : C(ℝ≥0, ℝ) => h (firstUpcrossPiece c (w : ℝ≥0 → ℝ))) (t : ℝ≥0),
      Measurable fun z : ℝ × Ω => upcrossOnce c t h (Φ z) := fun {h} hh t =>
    (measurable_upcrossOnce hc t hh).comp hΦ
  have hdual : ∀ t : ℝ≥0, ∫⁻ z, upcrossOnce c t f (Φ z) ∂(volume.prod P)
      = ∫⁻ z, upcrossOnce c t g (Φ z) ∂(volume.prod P) := by
    intro t
    rw [lintegral_prod _ (hmeasO hf t).aemeasurable, lintegral_prod _ (hmeasO hg' t).aemeasurable]
    exact lintegral_lebesgue_upcrossOnce_rev hB hm hcont mu hc t hf
  have h1 := lintegral_laplace_upcrossOnce_tonelli (ν := volume.prod P) hΦ hq hf
  have h2 := lintegral_laplace_upcrossOnce_tonelli (ν := volume.prod P) hΦ hq hg'
  have hmain : ∫⁻ z, f (firstUpcrossPiece c (Φ z)) *
        (expNeg q (upcrossEnd₁ c (Φ z)) - expNeg q (upcrossEnd₂ c (Φ z))) ∂(volume.prod P)
      = ∫⁻ z, g (firstUpcrossPiece c (Φ z)) *
        (expNeg q (upcrossEnd₁ c (Φ z)) - expNeg q (upcrossEnd₂ c (Φ z))) ∂(volume.prod P) := by
    rw [← h1, ← h2]
    exact lintegral_congr fun t => by rw [hdual t.toNNReal]
  rw [lintegral_prod _ (hdiff hf).aemeasurable, lintegral_prod _ (hdiff hg').aemeasurable] at hmain
  exact hmain

/-- `e^{-q r}` is antitone in `r` for `q ≥ 0`. -/
theorem expNeg_le_expNeg_of_le {q : ℝ} (hq : 0 ≤ q) {r s : ℝ≥0∞} (h : r ≤ s) :
    expNeg q s ≤ expNeg q r := by
  by_cases hs : s = ⊤
  · simp [hs]
  have hr : r ≠ ⊤ := ne_top_of_le_ne_top hs h
  have hrs : r.toReal ≤ s.toReal := ENNReal.toReal_mono hs h
  simp only [expNeg, hs, hr, ↓reduceIte]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  nlinarith

/-- The end of the first up-crossing interval is before the end of the next one. -/
theorem upcrossEnd₁_le_upcrossEnd₂ (c : ℝ) (w : ℝ≥0 → ℝ) : upcrossEnd₁ c w ≤ upcrossEnd₂ c w :=
  (le_hitFrom : upcrossEnd₁ c w ≤ hitFrom 0 (upcrossEnd₁ c w) w).trans le_hitFrom

/-- Law on path space of Brownian motion with drift `mu` started at `0`. -/
abbrev driftLaw (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hcont : ∀ ω, Continuous fun t => B t ω)
    (mu : ℝ) : Measure C(ℝ≥0, ℝ) :=
  (P.map (pathMap B hcont)).map (driftMap mu)

section Algebra

/-- Algebra of the two renewal identities: with `∫ a G = L M` and `∫ b G = (∫ a G) φ`, and
`b ≤ a ≤ 1`, `G ≤ 1`, one has `∫ G (a - b) = L M (1 - φ)`. -/
theorem lintegral_mul_sub_of_renewal [IsProbabilityMeasure P] {G a b : Ω → ℝ≥0∞}
    (hG : Measurable G) (hb : Measurable b) (hG1 : ∀ ω, G ω ≤ 1) (ha1 : ∀ ω, a ω ≤ 1)
    (hba : ∀ ω, b ω ≤ a ω) {L M φ : ℝ≥0∞} (hA : ∫⁻ ω, a ω * G ω ∂P = L * M)
    (hB : ∫⁻ ω, b ω * G ω ∂P = (∫⁻ ω, a ω * G ω ∂P) * φ) :
    ∫⁻ ω, G ω * (a ω - b ω) ∂P = L * M * (1 - φ) := by
  have hAle : ∫⁻ ω, a ω * G ω ∂P ≤ 1 := by
    calc ∫⁻ ω, a ω * G ω ∂P ≤ ∫⁻ _ω, 1 ∂P := lintegral_mono fun ω => by
          simpa using mul_le_mul' (ha1 ω) (hG1 ω)
      _ = 1 := by simp
  have hAfin : ∫⁻ ω, a ω * G ω ∂P ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hAle
  have hpt : ∀ ω, G ω * (a ω - b ω) = a ω * G ω - b ω * G ω := fun ω => by
    rw [ENNReal.mul_sub (fun _ _ => ne_top_of_le_ne_top ENNReal.one_ne_top (hG1 ω)),
      mul_comm (G ω) (a ω), mul_comm (G ω) (b ω)]
  have hbG : Measurable fun ω => b ω * G ω := hb.mul hG
  have hle : ∀ ω, b ω * G ω ≤ a ω * G ω := fun ω => mul_le_mul' (hba ω) le_rfl
  have hBfin : ∫⁻ ω, b ω * G ω ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top hAfin (lintegral_mono hle)
  have hLM : L * M ≠ ⊤ := hA ▸ hAfin
  rw [lintegral_congr hpt, lintegral_sub hbG hBfin (Filter.Eventually.of_forall hle), hB, hA,
    ENNReal.mul_sub (fun _ _ => hLM), mul_one]

end Algebra

section Start

variable [IsProbabilityMeasure P]

/-- For a fixed starting point `x`, the weight `g(piece)(e^{-q d₁} - e^{-q d₂})` has expectation
`E[e^{-q τ₀}] · M(g) · (1 - φ_q)` where `M(g) = ∫ g(piece) e^{-q d₁} dμ₀` and `φ_q` is the Laplace
transform of the return time. -/
theorem lintegral_piece_expNeg_diff_start (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ) {c : ℝ} (hc : 0 < c) {q : ℝ}
    (hq : 0 < q) {g : (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hg : Measurable fun w : C(ℝ≥0, ℝ) => g (firstUpcrossPiece c (w : ℝ≥0 → ℝ)))
    (hg1 : ∀ p, g p ≤ 1) (x : ℝ) :
    ∫⁻ ω, g (firstUpcrossPiece c (fun s => x + B s ω + mu * (s : ℝ))) *
        (expNeg q (upcrossEnd₁ c (fun s => x + B s ω + mu * (s : ℝ))) -
          expNeg q (upcrossEnd₂ c (fun s => x + B s ω + mu * (s : ℝ)))) ∂P
      = (∫⁻ ω, expNeg q (hitFrom 0 0 (fun s => x + B s ω + mu * (s : ℝ))) ∂P) *
        (∫⁻ v : C(ℝ≥0, ℝ), g (firstUpcrossPiece c (v : ℝ≥0 → ℝ)) *
            expNeg q (upcrossEnd₁ c (v : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu)) *
        (1 - ∫⁻ v : C(ℝ≥0, ℝ), expNeg q (upcrossReturn c (v : ℝ≥0 → ℝ))
          ∂(driftLaw P B hcont mu)) := by
  have hXad : StronglyAdapted (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      (fun (s : ℝ≥0) (ω : Ω) => x + B s ω + mu * (s : ℝ)) := fun s =>
    ((stronglyAdapted_natFiltration_real hm s).const_add x).add_const (mu * (s : ℝ))
  have hXc : ∀ ω, Continuous fun t : ℝ≥0 => x + B t ω + mu * (t : ℝ) := fun ω =>
    (continuous_const.add (hcont ω)).add (continuous_const.mul NNReal.continuous_coe)
  have hXinc : ∀ (ω : Ω) (t s : ℝ≥0),
      (x + B (t + s) ω + mu * ((t + s : ℝ≥0) : ℝ)) - (x + B t ω + mu * (t : ℝ))
        = (B (t + s) ω - B t ω) + mu * (s : ℝ) := fun ω t s => by push_cast; ring
  have r1 := lintegral_expNeg_piece_upcrossEnd₁_restart hB hm hcont hXad hXc hXinc hc q hg
  have r2 := lintegral_expNeg_piece_upcrossEnd₂_restart hB hm hcont hXad hXc hXinc c q hg
  have hψ : Measurable fun ω => affinePath x mu (pathMap B hcont ω) :=
    measurable_pathValued_of_eval fun s => by
      simp only [affinePath_apply, pathMap_apply]
      exact ((hm s).const_add x).add_const _
  exact lintegral_mul_sub_of_renewal (hg.comp hψ)
    ((measurable_expNeg q).comp ((measurable_upcrossEnd₂ c).comp hψ)) (fun ω => hg1 _)
    (fun ω => expNeg_le_one hq.le _)
    (fun ω => expNeg_le_expNeg_of_le hq.le (upcrossEnd₁_le_upcrossEnd₂ c _)) r1 r2

end Start

/-- Cancellation of a factor in `(0, ∞)` in `ℝ≥0∞`. -/
theorem ennreal_eq_of_mul_eq_mul_left {a b c : ℝ≥0∞} (h0 : c ≠ 0) (ht : c ≠ ⊤)
    (h : c * a = c * b) : a = b := by
  calc a = (c⁻¹ * c) * a := by rw [mul_comm c⁻¹ c, ENNReal.mul_inv_cancel h0 ht, one_mul]
    _ = c⁻¹ * (c * a) := mul_assoc _ _ _
    _ = c⁻¹ * (c * b) := by rw [h]
    _ = (c⁻¹ * c) * b := (mul_assoc _ _ _).symm
    _ = b := by rw [mul_comm c⁻¹ c, ENNReal.mul_inv_cancel h0 ht, one_mul]

section Cancel

variable [IsProbabilityMeasure P]

/-- The law of Brownian motion with drift on path space is a probability measure. -/
theorem isProbabilityMeasure_driftLaw (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ) :
    IsProbabilityMeasure (driftLaw P B hcont mu) := by
  have hpm : Measurable (pathMap B hcont) := measurable_pathMap B hm hcont
  have : IsProbabilityMeasure (P.map (pathMap B hcont)) :=
    (Measure.isProbabilityMeasure_map_iff hpm.aemeasurable).2 inferInstance
  exact (Measure.isProbabilityMeasure_map_iff (measurable_driftMap mu).aemeasurable).2 inferInstance

/-- Integrating over the Lebesgue starting point: the weight `g(piece)(e^{-q d₁} - e^{-q d₂})`
has total mass `K_q · M(g) · (1 - φ_q)` with `K_q = ∫ dx E[e^{-q τ₀(x)}]`. -/
theorem lintegral_lebesgue_piece_diff (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ) {c : ℝ} (hc : 0 < c) {q : ℝ}
    (hq : 0 < q) {g : (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hg : Measurable fun w : C(ℝ≥0, ℝ) => g (firstUpcrossPiece c (w : ℝ≥0 → ℝ)))
    (hg1 : ∀ p, g p ≤ 1) :
    ∫⁻ x : ℝ, ∫⁻ ω, g (firstUpcrossPiece c (fun s => x + B s ω + mu * (s : ℝ))) *
        (expNeg q (upcrossEnd₁ c (fun s => x + B s ω + mu * (s : ℝ))) -
          expNeg q (upcrossEnd₂ c (fun s => x + B s ω + mu * (s : ℝ)))) ∂P
      = (∫⁻ x : ℝ, ∫⁻ ω, expNeg q (hitFrom 0 0 (fun s => x + B s ω + mu * (s : ℝ))) ∂P) *
        ((∫⁻ v : C(ℝ≥0, ℝ), g (firstUpcrossPiece c (v : ℝ≥0 → ℝ)) *
            expNeg q (upcrossEnd₁ c (v : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu)) *
        (1 - ∫⁻ v : C(ℝ≥0, ℝ), expNeg q (upcrossReturn c (v : ℝ≥0 → ℝ))
          ∂(driftLaw P B hcont mu))) := by
  have := isProbabilityMeasure_driftLaw (P := P) hm hcont mu
  have hM : (∫⁻ v : C(ℝ≥0, ℝ), g (firstUpcrossPiece c (v : ℝ≥0 → ℝ)) *
            expNeg q (upcrossEnd₁ c (v : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu)) *
        (1 - ∫⁻ v : C(ℝ≥0, ℝ), expNeg q (upcrossReturn c (v : ℝ≥0 → ℝ))
          ∂(driftLaw P B hcont mu)) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top ?_)
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
    calc _ ≤ ∫⁻ _v : C(ℝ≥0, ℝ), 1 ∂(driftLaw P B hcont mu) := lintegral_mono fun v => by
          simpa using mul_le_mul' (hg1 _) (expNeg_le_one hq.le _)
      _ = 1 := by simp
  rw [lintegral_congr fun x => lintegral_piece_expNeg_diff_start hB hm hcont mu hc hq hg hg1 x]
  simp only [mul_assoc]
  exact lintegral_mul_const' _ _ hM

/-- **Weighted Laplace identity.**  For `mu > 0`, `c > 0`, `q > 0` and `f ≤ 1` such that `f(piece)`
and `f(rev(piece))` are measurable on path space, the weighted integrals of `f(piece)` and of
`f(rev(piece))` against `e^{-q d₁}` under Brownian motion with drift coincide. -/
theorem lintegral_piece_expNeg_eq_rev (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu) {c : ℝ} (hc : 0 < c)
    {q : ℝ} (hq : 0 < q) {f : (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hf : Measurable fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)))
    (hf' : Measurable fun w : C(ℝ≥0, ℝ) => f (upcrossRev c (firstUpcrossPiece c (w : ℝ≥0 → ℝ))))
    (hf1 : ∀ p, f p ≤ 1) :
    ∫⁻ v : C(ℝ≥0, ℝ), f (firstUpcrossPiece c (v : ℝ≥0 → ℝ)) *
        expNeg q (upcrossEnd₁ c (v : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu)
      = ∫⁻ v : C(ℝ≥0, ℝ), f (upcrossRev c (firstUpcrossPiece c (v : ℝ≥0 → ℝ))) *
        expNeg q (upcrossEnd₁ c (v : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu) := by
  have hKK := lintegral_lebesgue_laplace_hit_zero_pos_lt_top hB hm hcont hmu hq
  have hφ := lintegral_expNeg_upcrossReturn_lt_one_brownian hB hm hcont mu hc hq
  have e1 := lintegral_lebesgue_piece_diff hB hm hcont mu hc hq hf hf1
  have e2 := lintegral_lebesgue_piece_diff hB hm hcont mu hc hq
    (g := fun p => f (upcrossRev c p)) hf' (fun p => hf1 _)
  have e3 := lintegral_lebesgue_laplace_diff_rev hB.toIsPreBrownianReal hm hcont mu hc hq hf hf'
  rw [e1, e2] at e3
  have hK0 : (∫⁻ x : ℝ, ∫⁻ ω, expNeg q (hitFrom 0 0 (fun s => x + B s ω + mu * (s : ℝ))) ∂P) ≠ 0 :=
    (show 0 < ∫⁻ x : ℝ, ∫⁻ ω, expNeg q (hitFrom 0 0 (fun s => x + B s ω + mu * (s : ℝ))) ∂P from
      hKK.1).ne'
  have hKt : (∫⁻ x : ℝ, ∫⁻ ω, expNeg q (hitFrom 0 0 (fun s => x + B s ω + mu * (s : ℝ))) ∂P) ≠ ⊤ :=
    (show (∫⁻ x : ℝ, ∫⁻ ω, expNeg q (hitFrom 0 0 (fun s => x + B s ω + mu * (s : ℝ))) ∂P) < ⊤ from
      hKK.2).ne
  have e4 := ennreal_eq_of_mul_eq_mul_left hK0 hKt e3
  exact ennreal_eq_of_mul_eq_mul_left (tsub_pos_of_lt hφ).ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
    (by rw [mul_comm (1 - _), mul_comm (1 - _)]; exact e4)

/-- **Reversal identity for the first up-crossing piece.**  If the end `d₁` of the first
up-crossing interval is almost surely finite under Brownian motion with positive drift, then
`∫ f(piece) dμ₀ = ∫ f(rev(piece)) dμ₀` for every `[0,1]`-valued `f` with `f(piece)` and
`f(rev(piece))` measurable. -/
theorem lintegral_piece_eq_rev (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu) {c : ℝ} (hc : 0 < c)
    (hfin : ∀ᵐ v : C(ℝ≥0, ℝ) ∂(driftLaw P B hcont mu), upcrossEnd₁ c (v : ℝ≥0 → ℝ) < ⊤)
    {f : (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hf : Measurable fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)))
    (hf' : Measurable fun w : C(ℝ≥0, ℝ) => f (upcrossRev c (firstUpcrossPiece c (w : ℝ≥0 → ℝ))))
    (hf1 : ∀ p, f p ≤ 1) :
    ∫⁻ v : C(ℝ≥0, ℝ), f (firstUpcrossPiece c (v : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu)
      = ∫⁻ v : C(ℝ≥0, ℝ), f (upcrossRev c (firstUpcrossPiece c (v : ℝ≥0 → ℝ)))
        ∂(driftLaw P B hcont mu) := by
  have := isProbabilityMeasure_driftLaw (P := P) hm hcont mu
  refine lintegral_eq_of_expNeg_eq
    (τ := fun v : C(ℝ≥0, ℝ) => upcrossEnd₁ c (v : ℝ≥0 → ℝ)) (measurable_upcrossEnd₁ c) hfin hf hf'
    (fun v => hf1 _) (fun v => hf1 _) fun q hq => ?_
  exact (lintegral_congr fun v => mul_comm _ _).trans
    ((lintegral_piece_expNeg_eq_rev hB hm hcont hmu hc hq hf hf' hf1).trans
      (lintegral_congr fun v => mul_comm _ _))

end Cancel

end LatticeProb
