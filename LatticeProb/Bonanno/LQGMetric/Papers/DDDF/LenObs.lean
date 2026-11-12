/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.LenObs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenCountable
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseVersion
import LatticeProb.Bonanno.LQGMetric.Prob.Median

/-!
# DDDF length observables of the white-noise field (task P2-DDDFLEN; blueprint DDDF.D2.len)

DDDF = arXiv:1904.08021, `literature/src/1904.08021/tightness.tex` l. 449–498 and l. 153.
For the continuous version of DDDF's field `φ_{a,b}` (`WhiteNoise.phi`, built in
`Field/WhiteNoise*.lean`; continuous modification `WhiteNoise.exists_continuous_modification_phi`):

* `phiVer W P a b`: a chosen continuous measurable modification of `φ_{a,b}` (junk `0` if none);
  `phiMN W P m n := phiVer W P 2^{-n} 2^{-m}` is DDDF's `φ_{m,n}` (l. 293), `φ_{0,n} = φ_{2^{-n}}`.
* `lenObs ξ Y R ω := L(R, Y(·, ω))` (real valued), so
  `lenMN ξ W P a b m n = L^{(m,n)}_{a,b}(φ)` and `lenN ξ W P a b n = L^{(n)}_{a,b}(φ)` (l. 457, 474),
  `lenObs ξ (phiMN W P 0 n) R = L^{(n)}(R, φ)` for a marked rectangle `R` (l. 494).
* Quantiles (decision D22 / deviation D-DDDF-4: generalized quantiles, no atomlessness):
  `ellQ ξ P Y R p := lowerQuantile (law of L(R)) p` (DDDF `ℓ`, l. 465), `ellBarQ … p := ellQ … (1−p)`
  (DDDF `ℓ̄`, l. 465), `ellN`, `ellBarN` (`ℓ_k`, `ℓ̄_k`), `LambdaN` (`Λ_n`, (2.22) = `DefQuant`,
  l. 468–470), `lambdaDelta` (`λ_δ` = lower median, l. 153), `XAB` (`X_{a,b}`, (2.20) =
  `DefX`, l. 449–452, for arbitrary field sequences `φ_{0,n}`, `ψ_{0,n}`).

Results: measurability (`measurable_lenObs`), finiteness and positivity, the quantile property
`isQuantile_ellQ` (`P(L ≤ ℓ(p)) ≥ p`, `P(L ≥ ℓ(p)) ≥ 1 − p`, `prob_le_ellQ`, `prob_ge_ellQ`),
monotonicity of `ℓ` in `p` (`ellQ_mono`), DDDF.S2.c for the random field (`lenObs_le_exp`,
`exp_neg_le_lenObs`; medians: `lowerMedian_lenObs_le`, `le_lowerMedian_lenObs` given
`P(sup_R |φ| > M) < 1/2`, the input DDDF.P2 will supply), and the comparison through `X_{a,b}`
(DDDF l. 482–485, `rectLen_le_XAB`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `Y` is a continuous (every `ω`) measurable (every `x`) modification of `φ_{a,b}`. -/
structure IsPhiVersion (W : WNSpace → Ω → ℝ) (P : Measure Ω) (a b : ℝ) (Y : ℂ → Ω → ℝ) :
    Prop where
  cont : ∀ ω, Continuous fun x => Y x ω
  meas : ∀ x, Measurable (Y x)
  ae_eq : ∀ x, (fun ω => Y x ω) =ᵐ[P] phi W a b x

open Classical in
/-- a chosen continuous version of `φ_{a,b}` (junk `0` if there is none) -/
def phiVer (W : WNSpace → Ω → ℝ) (P : Measure Ω) (a b : ℝ) : ℂ → Ω → ℝ :=
  if h : ∃ Y, IsPhiVersion W P a b Y then h.choose else 0

theorem isPhiVersion_phiVer {W : WNSpace → Ω → ℝ} {P : Measure Ω} (hW : IsWhiteNoise P W)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : IsPhiVersion W P a b (phiVer W P a b) := by
  have h : ∃ Y, IsPhiVersion W P a b Y := by
    obtain ⟨Y, h1, h2, h3⟩ := exists_continuous_modification_phi hW ha hab
    exact ⟨Y, h1, h2, h3⟩
  rw [phiVer, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- DDDF's `φ_{m,n} = φ_{2^{-n}, 2^{-m}}` (continuous version; l. 293) -/
def phiMN (W : WNSpace → Ω → ℝ) (P : Measure Ω) (m n : ℕ) : ℂ → Ω → ℝ :=
  phiVer W P ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m)

theorem isPhiVersion_phiMN {W : WNSpace → Ω → ℝ} {P : Measure Ω} (hW : IsWhiteNoise P W)
    {m n : ℕ} (hmn : m ≤ n) :
    IsPhiVersion W P ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) (phiMN W P m n) :=
  isPhiVersion_phiVer hW (by positivity) (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn)

/-- the real-valued crossing length `L(R, Y(·, ω))` of the marked rectangle `R` -/
def lenObs (ξ : ℝ) (Y : ℂ → Ω → ℝ) (R : MarkedRect) (ω : Ω) : ℝ :=
  (rectLen ξ (fun x => Y x ω) R).toReal

/-- DDDF's `L^{(m,n)}_{a,b}(φ)` (l. 474) -/
def lenMN (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (a b : ℝ) (m n : ℕ) : Ω → ℝ :=
  lenObs ξ (phiMN W P m n) (rectAB a b)

/-- DDDF's `L^{(n)}_{a,b}(φ)` (l. 457) -/
def lenN (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (a b : ℝ) (n : ℕ) : Ω → ℝ :=
  lenMN ξ W P a b 0 n

/-- generalized `p`-quantile `ℓ` of `L(R)` (DDDF l. 465; D22, D-DDDF-4) -/
def ellQ (ξ : ℝ) (P : Measure Ω) (Y : ℂ → Ω → ℝ) (R : MarkedRect) (p : ℝ≥0∞) : ℝ :=
  lowerQuantile (P.map (lenObs ξ Y R)) p

/-- high quantile `ℓ̄(p) := ℓ(1 − p)` (DDDF l. 465) -/
def ellBarQ (ξ : ℝ) (P : Measure Ω) (Y : ℂ → Ω → ℝ) (R : MarkedRect) (p : ℝ≥0∞) : ℝ :=
  ellQ ξ P Y R (1 - p)

/-- `ℓ_k(φ, p) := ℓ^{(k)}_{1,1}(φ, p)` (DDDF (2.22)) -/
def ellN (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (k : ℕ) (p : ℝ≥0∞) : ℝ :=
  ellQ ξ P (phiMN W P 0 k) (rectAB 1 1) p

/-- `ℓ̄_k(φ, p) := ℓ̄^{(k)}_{1,1}(φ, p)` (DDDF (2.22)) -/
def ellBarN (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (k : ℕ) (p : ℝ≥0∞) : ℝ :=
  ellBarQ ξ P (phiMN W P 0 k) (rectAB 1 1) p

/-- `Λ_n(φ, p) := max_{k ≤ n} ℓ̄_k(φ, p) / ℓ_k(φ, p)` (DDDF (2.22) = `DefQuant`) -/
def LambdaN (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (n : ℕ) (p : ℝ≥0∞) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun k => ellBarN ξ W P k p / ellN ξ W P k p

/-- `λ_δ`: the (lower) median of the left–right distance of `[0,1]²` for `e^{ξ φ_δ} ds`,
`φ_δ = φ_{δ,1}` (DDDF l. 153) -/
def lambdaDelta (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (δ : ℝ) : ℝ :=
  lowerMedianLaw (P.map (lenObs ξ (phiVer W P δ 1) (rectAB 1 1)))

/-- `λ_n`: the (lower) median of `L^{(n)}_{1,1}` (DDDF l. 964) -/
def lambdaN (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (n : ℕ) : ℝ :=
  lowerMedianLaw (P.map (lenN ξ W P 1 1 n))

/-- `X_{a,b} := sup_n ‖φ_{0,n} − ψ_{0,n}‖_{R_{a,b}}` (DDDF (2.20) = `DefX`) for two sequences of
fields, in `[0, ∞]` -/
def XAB (φ ψ : ℕ → ℂ → ℝ) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ n, ⨆ x ∈ (rectAB a b).toSet, ENNReal.ofReal |φ n x - ψ n x|

/-! ### Basic properties -/

variable {ξ : ℝ} {Y : ℂ → Ω → ℝ}

theorem measurable_lenObs (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    (R : MarkedRect) : Measurable (lenObs ξ Y R) :=
  (measurable_crossLenIn R.isCompact_toSet hYc hYm).ennreal_toReal

theorem measurable_lenMN {W : WNSpace → Ω → ℝ} {P : Measure Ω} (hW : IsWhiteNoise P W)
    (a b : ℝ) {m n : ℕ} (hmn : m ≤ n) : Measurable (lenMN ξ W P a b m n) :=
  measurable_lenObs (isPhiVersion_phiMN hW hmn).cont (isPhiVersion_phiMN hW hmn).meas _

omit [MeasurableSpace Ω] in
theorem ofReal_lenObs (hYc : ∀ ω, Continuous fun x => Y x ω) (R : MarkedRect) (hw : 0 ≤ R.w)
    (hh : 0 ≤ R.h) (ω : Ω) :
    ENNReal.ofReal (lenObs ξ Y R ω) = rectLen ξ (fun x => Y x ω) R :=
  ENNReal.ofReal_toReal (rectLen_ne_top R hw hh (hYc ω))

omit [MeasurableSpace Ω] in
theorem lenObs_pos (hYc : ∀ ω, Continuous fun x => Y x ω) (R : MarkedRect) (hw : 0 ≤ R.w)
    (hh : 0 ≤ R.h) (hc : 0 < R.crossWidth) (ω : Ω) : 0 < lenObs ξ Y R ω :=
  ENNReal.toReal_pos (rectLen_pos R hc (hYc ω)).ne' (rectLen_ne_top R hw hh (hYc ω))

omit [MeasurableSpace Ω] in
/-- **DDDF.S2.c, upper bound** (l. 908) for the random field: `L(R) ≤ e^{|ξ| M} crossWidth R`
when `|Y(·, ω)| ≤ M` on `R`. -/
theorem lenObs_le_exp (R : MarkedRect) (hw : 0 ≤ R.w) (hh : 0 ≤ R.h) {ω : Ω} {M : ℝ}
    (hb : ∀ x ∈ R.toSet, |Y x ω| ≤ M) :
    lenObs ξ Y R ω ≤ Real.exp (|ξ| * M) * R.crossWidth := by
  have hc : 0 ≤ R.crossWidth := by unfold MarkedRect.crossWidth; split_ifs <;> assumption
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (rectLen_le R hw hh hb)

omit [MeasurableSpace Ω] in
/-- **DDDF.S2.c, lower bound** (l. 908) for the random field. -/
theorem exp_neg_le_lenObs (hYc : ∀ ω, Continuous fun x => Y x ω) (R : MarkedRect)
    (hw : 0 ≤ R.w) (hh : 0 ≤ R.h) {ω : Ω} {M : ℝ} (hb : ∀ x ∈ R.toSet, |Y x ω| ≤ M) :
    Real.exp (-(|ξ| * M)) * R.crossWidth ≤ lenObs ξ Y R ω := by
  have hc : 0 ≤ R.crossWidth := by unfold MarkedRect.crossWidth; split_ifs <;> assumption
  refine (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 ?_
  rw [ENNReal.ofReal_toReal (rectLen_ne_top R hw hh (hYc ω))]
  exact rectLen_ge R hb

/-! ### Quantiles (D22, D-DDDF-4) -/

variable {P : Measure Ω} [IsProbabilityMeasure P]

theorem isQuantile_ellQ (R : MarkedRect) {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    IsQuantile (P.map (lenObs ξ Y R)) p (ellQ ξ P Y R p) :=
  isQuantile_lowerQuantile hp0 hp1

/-- `P(L(R) ≤ ℓ(p)) ≥ p` -/
theorem prob_le_ellQ (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    (R : MarkedRect) {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    p ≤ P {ω | lenObs ξ Y R ω ≤ ellQ ξ P Y R p} := by
  have h := (isQuantile_ellQ (ξ := ξ) (Y := Y) (P := P) R hp0 hp1).1
  rwa [Measure.map_apply (measurable_lenObs hYc hYm R) measurableSet_Iic] at h

/-- `P(L(R) ≥ ℓ(p)) ≥ 1 − p` -/
theorem prob_ge_ellQ (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    (R : MarkedRect) {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    1 - p ≤ P {ω | ellQ ξ P Y R p ≤ lenObs ξ Y R ω} := by
  have h := (isQuantile_ellQ (ξ := ξ) (Y := Y) (P := P) R hp0 hp1).2
  rwa [Measure.map_apply (measurable_lenObs hYc hYm R) measurableSet_Ici] at h

/-- `ℓ(p)` is nondecreasing in `p` (DDDF l. 465) -/
theorem ellQ_mono (R : MarkedRect) {p p' : ℝ≥0∞} (hp0 : 0 < p) (hp' : p' < 1) (hpp : p ≤ p') :
    ellQ ξ P Y R p ≤ ellQ ξ P Y R p' := by
  have hp1 : p < 1 := hpp.trans_lt hp'
  have hp'0 : 0 < p' := hp0.trans_le hpp
  refine (le_measure_Iic_iff_lowerQuantile_le hp0 hp1).1 (hpp.trans ?_)
  exact (le_measure_Iic_iff_lowerQuantile_le hp'0 hp').2 le_rfl

/-! ### Comparison through `X_{a,b}` (DDDF l. 482–485) -/

/-- If `X_{a,b}(φ, ψ) ≤ c` then `L^{(n)}_{a,b}(φ) ≤ e^{|ξ| c} L^{(n)}_{a,b}(ψ)` (and symmetrically,
swapping `φ` and `ψ`, since `XAB` is symmetric). -/
theorem rectLen_le_XAB {φ ψ : ℕ → ℂ → ℝ} {a b c : ℝ} (hc : 0 ≤ c)
    (hX : XAB φ ψ a b ≤ ENNReal.ofReal c) (n : ℕ) :
    rectLen ξ (φ n) (rectAB a b) ≤ ENNReal.ofReal (Real.exp (|ξ| * c)) *
      rectLen ξ (ψ n) (rectAB a b) := by
  refine crossLenIn_le_of_abs_sub_le fun x hx => ?_
  have h : ENNReal.ofReal |φ n x - ψ n x| ≤ ENNReal.ofReal c :=
    le_trans (le_trans (le_iSup₂_of_le (f := fun x (_ : x ∈ (rectAB a b).toSet) =>
      ENNReal.ofReal |φ n x - ψ n x|) x hx le_rfl) (le_iSup (fun n =>
        ⨆ x ∈ (rectAB a b).toSet, ENNReal.ofReal |φ n x - ψ n x|) n)) hX
  exact (ENNReal.ofReal_le_ofReal_iff hc).1 h

theorem XAB_comm (φ ψ : ℕ → ℂ → ℝ) (a b : ℝ) : XAB φ ψ a b = XAB ψ φ a b := by
  simp only [XAB, abs_sub_comm]

/-! ### Medians from sup bounds (DDDF.S2.c, "hence with P2", l. 908) -/

theorem lambdaN_eq_lambdaDelta (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (n : ℕ) :
    lambdaN ξ W P n = lambdaDelta ξ W P ((2 : ℝ)⁻¹ ^ n) := by
  simp only [lambdaN, lambdaDelta, lenN, lenMN, phiMN, pow_zero]

/-- If `P(sup_R |Y| > M) < 1/2`, the lower median of `L(R)` is at least `e^{−|ξ| M} crossWidth R`
(combined with DDDF.P2 this gives `λ_n ≥ 2^{−n(2ξ + o(1))}`, DDDF.S2.c). -/
theorem le_lowerMedian_lenObs (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x)) (R : MarkedRect) (hw : 0 ≤ R.w) (hh : 0 ≤ R.h) {M : ℝ}
    (hM : P {ω | ¬ ∀ x ∈ R.toSet, |Y x ω| ≤ M} < 2⁻¹) :
    Real.exp (-(|ξ| * M)) * R.crossWidth ≤ lowerMedianLaw (P.map (lenObs ξ Y R)) := by
  by_contra hlt
  rw [not_le] at hlt
  have h := (isQuantile_lowerQuantile (μ := P.map (lenObs ξ Y R)) inv_two_pos'
    inv_two_lt_one').1
  rw [Measure.map_apply (measurable_lenObs hYc hYm R) measurableSet_Iic] at h
  refine absurd (h.trans (measure_mono fun ω hω => ?_)) (not_le.2 hM)
  intro hb
  have := exp_neg_le_lenObs (ξ := ξ) hYc R hw hh hb
  exact absurd (lt_of_le_of_lt (mem_preimage.1 hω) hlt) (not_lt.2 this)

end DDDF
end LQGMetric
