/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P10Core at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6Final
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Node
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Push
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Indep
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Tail

/-!
# DDDF Proposition 10: the core comparison on the coupled space

DF (Dubédat–Falconet, arXiv:1809.02607, proofs of Props. 4.5–4.6, `LiouvilleMetricStarScale.tex`
l. 534–608), used by DDDF Prop 10 (arXiv:1904.08021, l. 725–736). On a space carrying two
independent white noises `W₁, W₂`, with `Wt = coupledNoise h W₁ W₂` (DDDF l. 541–543),
`φ = φ_{0,n}(W₁)`, `φ̃ = φ_{0,n}(Wt)` and the Lemma 6 decomposition `φ̃ ∘ F = φ + Y_L + Y_H` on `K`:

on `{L ≤ l} ∩ {‖Y_L‖_K < x} ∩ {L(φ + Y_H) ≤ e^s L(φ)}`,
`L' ≤ ‖F'‖_K L(φ̃ ∘ F) ≤ ‖F'‖_K e^{ξx} L(φ + Y_H) ≤ ‖F'‖_K e^{ξx} e^s l`
(DF l. 552–566 for the first step, `crossLenIn_image_le`; Lemma 6 for the second); the
probabilities of the two exceptional events are bounded by the Gaussian tail of `‖Y_L‖_K`
(Lemma 6) and by DDDF Lemma 9 / DF Lemma 4.7 for `L(A, B; K)` (`tail_cross`), using the
independence of `Y_H` from `φ` (Lemma 6, passed to the continuous versions by
`indepFun_modification`). So
`P(L ≤ l) ≤ P(L' ≤ ‖F'‖_K e^{ξx} e^s l) + C e^{−c x²} + ε₁` (`p10_core`).

Deviation (proposed D-DDDF-19): DF prove Prop 4.5 (`P(L ≤ l) ≥ ε ⇒ P(L' ≤ l') ≥ ε/4`) by a
conditional Markov inequality (first moment of the averaged length) and Prop 4.6 with Lemma 4.7;
we use the Lemma 4.7 tail bound for both parts (it gives the same form of `l'`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise WNPush

lemma P10Map.confHyp {K U : Set ℂ} {F : ℂ → ℂ} (hF : P10Map K U F) : ConfHyp F U := by
  obtain ⟨M, hM⟩ := hF.deriv_bd
  refine ⟨hF.isOpen, hF.diff, hF.inj, fun y hy h0 => ?_⟩
  have := (hM y hy).1
  rw [h0, norm_zero] at this
  linarith

/-- crossing lengths in `U` only depend on the field on `U` -/
lemma crossLenIn_congr_on {ξ : ℝ} {f g : ℂ → ℝ} {U A B : Set ℂ} (h : ∀ x ∈ U, f x = g x) :
    crossLenIn ξ f U A B = crossLenIn ξ g U A B := by
  rw [crossLenIn_eq_biInf, crossLenIn_eq_biInf]
  refine iInf_congr fun P => iInf_congr fun hP => ?_
  obtain ⟨z, -, w, -, -, hU⟩ := hP
  exact setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [h _ (hU t ht)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- the law of `φ_H^{(δ)}(x)` -/
lemma hasLaw_phiH {F : ℂ → ℂ} {U : Set ℂ} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (δ : ℝ) (x : ℂ) :
    HasLaw (phiH F U W δ x) (gaussianReal 0 (‖Real.sqrt Real.pi • hKer F U δ x‖ ^ 2).toNNReal) P := by
  have h := hW.hasLaw (fun _ : Unit => hKer F U δ x) (fun _ => Real.sqrt Real.pi)
  have e : phiH F U W δ x = fun ω => Real.sqrt Real.pi * W (hKer F U δ x) ω := rfl
  rw [e]; simpa using h

/-- **Core of DDDF Prop 10** (DF Props. 4.5–4.6) on a space with two independent white noises. -/
theorem p10_core {ξ : ℝ} (hξ : 0 < ξ) {K A B U : Set ℂ} {F : ℂ → ℂ} (hK : IsCompact K)
    (hF : P10Map K U F) {W₁ W₂ : WNSpace → Ω → ℝ} (hW₁ : IsWhiteNoise P W₁)
    (hW₂ : IsWhiteNoise P W₂) (hind : IndepFun (fun ω f => W₁ f ω) (fun ω f => W₂ f ω) P) :
    ∃ C₆ c₆ σ : ℝ, 0 < C₆ ∧ 0 < c₆ ∧ 0 < σ ∧ ∀ (n : ℕ) (l x ε₁ : ℝ), 0 < x → 0 < ε₁ →
      ε₁ < Real.exp (-(ξ * σ) ^ 2 / 2) →
      P {ω | crossLenIn ξ (fun y => phiMN W₁ P 0 n y ω) K A B ≤ ENNReal.ofReal l} ≤
        P {ω | crossLenIn ξ (fun y => phiMN (coupledNoise hF.confHyp W₁ W₂) P 0 n y ω)
            (F '' K) (F '' A) (F '' B) ≤ ENNReal.ofReal (derivSup F K * Real.exp (ξ * x) *
              Real.exp (Real.sqrt (2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹)) * l)} +
          ENNReal.ofReal (C₆ * Real.exp (-c₆ * x ^ 2)) + ENNReal.ofReal ε₁ := by
  classical
  have hP := hW₁.isProbabilityMeasure
  obtain ⟨M, hMb⟩ := hF.deriv_bd
  set h := hF.confHyp
  obtain ⟨C₆, c₆, σH, hC₆, hc₆, h6⟩ := lemma6 h hF.bdd (fun y hy => (hMb y hy).1)
    (fun y hy => (hMb y hy).2.1) (fun y hy => (hMb y hy).2.2) hK hF.sub hW₁ hW₂ hind
  set σ := Real.sqrt (max σH 1)
  have hσ : 0 < σ := Real.sqrt_pos.2 (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hσ2 : σ ^ 2 = max σH 1 := Real.sq_sqrt (le_trans zero_le_one (le_max_right _ _))
  refine ⟨C₆, c₆, σ, hC₆, hc₆, hσ, fun n l x ε₁ hx hε₁ hε₁' => ?_⟩
  set δ : ℝ := (2 : ℝ)⁻¹ ^ n
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨YL, YH, hdec, hLc, hHc, hLm, hHm, hLae, hHae, htail, hvar, hindH⟩ := h6 δ hδ hδ1
  set Wt := coupledNoise h W₁ W₂
  have hWt : IsWhiteNoise P Wt := isWhiteNoise_coupledNoise h hW₁ hW₂ hind
  have e1 : phiMN W₁ P 0 n = phiVer W₁ P δ 1 := by simp only [phiMN, pow_zero, δ]
  have e2 : phiMN Wt P 0 n = phiVer Wt P δ 1 := by simp only [phiMN, pow_zero, δ]
  rw [e1, e2]
  set φ := phiVer W₁ P δ 1
  set φt := phiVer Wt P δ 1
  have hv := isPhiVersion_phiVer hW₁ hδ hδ1
  -- the high-frequency field, extended off `K` by `φ_H`
  set Ψ : ℂ → Ω → ℝ := fun y ω => if y ∈ K then YH y ω else phiH F U W₁ δ y ω
  have hΨK : ∀ y ∈ K, ∀ ω, Ψ y ω = YH y ω := fun y hy ω => by simp [Ψ, hy]
  have hΨc : ∀ ω, ContinuousOn (fun y => Ψ y ω) K := fun ω =>
    (hHc ω).congr fun y hy => hΨK y hy ω
  have hphiHm : ∀ y, Measurable (phiH F U W₁ δ y) := fun y =>
    (hW₁.measurable _).const_mul _
  have hΨm : ∀ y, Measurable (Ψ y) := fun y => by
    by_cases hy : y ∈ K
    · have : Ψ y = YH y := funext fun ω => by simp [Ψ, hy]
      rw [this]; exact hHm y
    · have : Ψ y = phiH F U W₁ δ y := funext fun ω => by simp [Ψ, hy]
      rw [this]; exact hphiHm y
  have hind0 : IndepFun (fun ω y => phi W₁ δ 1 y ω) (fun ω y => phiH F U W₁ δ y ω) P :=
    (hindH.symm.comp (φ := fun (z : ℂ → ℝ × ℝ) y => (z y).1) (ψ := id)
      (measurable_pi_iff.2 fun y => measurable_fst.comp (measurable_pi_apply y)) measurable_id)
  have hindΨ : IndepFun (fun ω y => φ y ω) (fun ω y => Ψ y ω) P :=
    indepFun_modification (fun y => measurable_phi hW₁ δ 1 y) hv.meas hphiHm hΨm hv.ae_eq
      (fun y => by
        by_cases hy : y ∈ K
        · have : Ψ y = YH y := funext fun ω => by simp [Ψ, hy]
          rw [this]; exact hHae y hy
        · have : Ψ y = phiH F U W₁ δ y := funext fun ω => by simp [Ψ, hy]
          rw [this]) hind0
  have hgauss : ∀ y ∈ K, ∃ v : ℝ≥0, (v : ℝ) ≤ σ ^ 2 ∧ HasLaw (Ψ y) (gaussianReal 0 v) P := by
    intro y hy
    refine ⟨(‖Real.sqrt Real.pi • hKer F U δ y‖ ^ 2).toNNReal, ?_, ?_⟩
    · rw [Real.coe_toNNReal _ (sq_nonneg _), hσ2, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, Real.sq_sqrt Real.pi_pos.le, ← variance_phiH hW₁ δ y]
      exact (hvar y).trans (le_max_left _ _)
    · have : Ψ y = YH y := funext fun ω => by simp [Ψ, hy]
      rw [this]
      exact (hasLaw_phiH hW₁ δ y).congr (hHae y hy)
  have hT := tail_cross (A := A) (B := B) hξ hσ hε₁ hε₁' hK hv.cont hv.meas hΨc hΨm hindΨ hgauss
  have hT2 := htail x hx.le
  set s := Real.sqrt (2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹)
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp s)
  set S := derivSup F K
  have hsub : {ω | crossLenIn ξ (fun y => φ y ω) K A B ≤ ENNReal.ofReal l} ⊆
      ({ω | crossLenIn ξ (fun y => φt y ω) (F '' K) (F '' A) (F '' B) ≤
          ENNReal.ofReal (S * Real.exp (ξ * x) * Real.exp s * l)} ∪
        {ω | ENNReal.ofReal x ≤ ⨆ y ∈ K, ENNReal.ofReal |YL y ω|}) ∪
        {ω | c * crossLenIn ξ (fun y => φ y ω) K A B <
          crossLenIn ξ (fun y => φ y ω + Ψ y ω) K A B} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    by_contra hn
    simp only [mem_union, mem_ofPred_eq, not_or, not_le, not_lt] at hn
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · have htop : crossLenIn ξ (fun y => φ y ω) K A B = ⊤ := by
        rw [crossLenIn_eq_biInf]
        refine iInf₂_eq_top.2 fun Q hQ => ?_
        obtain ⟨z, -, w, -, -, hU⟩ := hQ
        have := hU 0 ⟨le_rfl, zero_le_one⟩
        rw [hKe] at this; exact absurd this (Set.notMem_empty _)
      rw [htop] at hω
      exact absurd hω (not_le.2 ENNReal.ofReal_lt_top)
    obtain ⟨y₀, hy₀⟩ := hKne
    have hbdd : BddAbove ((fun z => ‖deriv F z‖) '' K) :=
      ⟨M, by rintro _ ⟨z, hz, rfl⟩; exact (hMb z (hF.sub hz)).2.1⟩
    have hSb : ∀ y ∈ K, ‖deriv F y‖ ≤ S := fun y hy => le_csSup hbdd ⟨y, hy, rfl⟩
    have hS1 : 1 ≤ S := ((hMb y₀ (hF.sub hy₀)).1).trans (hSb y₀ hy₀)
    have hsup : ∀ y ∈ K, |YL y ω| ≤ x := fun y hy =>
      ((ENNReal.ofReal_lt_ofReal_iff hx).1 ((le_iSup₂ (f := fun y (_ : y ∈ K) =>
        ENNReal.ofReal |YL y ω|) y hy).trans_lt h2)).le
    have hcong : crossLenIn ξ (fun y => φ y ω + YH y ω) K A B =
        crossLenIn ξ (fun y => φ y ω + Ψ y ω) K A B :=
      crossLenIn_congr_on fun y hy => by rw [hΨK y hy ω]
    have hstep1 : crossLenIn ξ (fun y => φt (F y) ω) K A B ≤
        ENNReal.ofReal (Real.exp (|ξ| * x)) * crossLenIn ξ (fun y => φ y ω + YH y ω) K A B := by
      refine crossLenIn_le_of_abs_sub_le fun y hy => ?_
      rw [hdec y ω]
      have : φ y ω + YL y ω + YH y ω - (φ y ω + YH y ω) = YL y ω := by ring
      rw [this]; exact hsup y hy
    have hstep2 : crossLenIn ξ (fun z => φt z ω) (F '' K) (F '' A) (F '' B) ≤
        ENNReal.ofReal S * crossLenIn ξ ((fun z => φt z ω) ∘ F) K A B :=
      crossLenIn_image_le hF.isOpen hF.sub hF.diff (by linarith) hSb
    have hfin : crossLenIn ξ (fun z => φt z ω) (F '' K) (F '' A) (F '' B) ≤
        ENNReal.ofReal (S * Real.exp (ξ * x) * Real.exp s * l) := by
      calc _ ≤ ENNReal.ofReal S * crossLenIn ξ ((fun z => φt z ω) ∘ F) K A B := hstep2
        _ ≤ ENNReal.ofReal S * (ENNReal.ofReal (Real.exp (|ξ| * x)) *
            crossLenIn ξ (fun y => φ y ω + YH y ω) K A B) := mul_le_mul_right hstep1 _
        _ ≤ ENNReal.ofReal S * (ENNReal.ofReal (Real.exp (|ξ| * x)) *
            (c * ENNReal.ofReal l)) := by
          rw [hcong]
          exact mul_le_mul_right (mul_le_mul_right (h3.trans (mul_le_mul_right hω c)) _) _
        _ = ENNReal.ofReal (S * Real.exp (ξ * x) * Real.exp s * l) := by
          rw [abs_of_pos hξ, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity)]
          ring
    exact (not_lt.2 hfin) h1
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add le_rfl hT2) hT

end DDDF
end LQGMetric
