/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P17L1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L21R
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L19Det
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L4Max
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L12

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.17, Step 3: the lower bound `D^ε_ĥ(K', ∂U') ≥ ε^{-1/(d+ζ)}` (P2-DGLB)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.17,
Step 3 (DG:1588–1589): "choose a compact set `K'` containing `K` in its interior and an open set
`U'` with `K' ⊂ U' ⊂ Ū' ⊂ U` … we have `D^ε_ĥ(S_0, S_k; 𝕊(1/2)) ≥ D^ε_ĥ(K', ∂U')`. We may
therefore apply Lemma 3.2 and Theorem 1.3 [thm-diam] to find that with polynomially high
probability as `ε → 0`, the left side … is at least `ε^{-1/(d_γ + ζ̃)}`."

DG's proof of the lower half of Theorem 1.3 (DG:1393–1397): every path from `K` to `∂U` crosses
an annulus `S_j(1/2) ∖ S_j` of one of finitely many squares covering `K`, and for each square
the crossing distance is `≥ ε^{-1/(d+ζ)}` with polynomially high probability.

Formalization (`DGP317LbReg`, `dgP317Lb_of`): the squares are the grid squares `S` of side
`δ_ε = 2^{-⌈log₂ ε^{-β}⌉}` (DG Lemma 3.21's family, `l321Grid`), and the annulus bound for all of
them at once is DG Lemma 3.21 (`dg_lemma321`, DG:1678–1687, polynomially high probability):
`D^ε(S, ∂S(1)) ≥ ε^{-1/d + β(2+γ²/2)/d + ζ₁} e^{(γ/d) max_{S(1)} ĥ_{ε^β}}`; with DG Lemma 3.5
(`dg_lemma35`) `max_{S(1)} ĥ_{ε^β} ≥ −3β log ε⁻¹`, and for `β`, `ζ₁` small this is
`≥ ε^{-1/(d+ζ)}`. A path from `y` to `y'` with `|y − y'| ≥ a > 6δ_ε` leaves `S(1)` for the square
`S ∋ y` (`dgLGDSet_half_le`). This replaces DG's "Theorem 1.3 + Lemma 3.2" (DZZ Lemma 6.1 at a
fixed square, transported to every square by scaling) by DG's own Lemma 3.21 (proposed
DEVIATIONS entry DV-DGLB-1): the library's version of the fixed-square input, DG Lemma 3.20
(`dg_lemma320`), only holds with probability tending to `1`, while Step 3 needs a polynomial
rate. The input of Lemma 3.21 is `DGLem319Scaled` (DG Lemma 3.19 transported by (3.7)), the same
hypothesis as in DG Proposition 3.22 (`dg_prop322_sqOne_muHat`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the half-open square `c + [0,1)²` tiled by the grids of `l321Grid Q c β ε` -/
def p17lReg (c : ℂ) : Set ℂ := Ico c.re (c.re + 1) ×ℂ Ico c.im (c.im + 1)

/-- **The lower bound of DG Prop 3.17 Step 3** (DG:1588–1589, Theorem 1.3 lower half
DG:1393–1397): for `A ⊆ c + [0,1)²` with `A_a ⊆ Q`, with polynomially high probability as
`ε → 0`, `D^ε_μ(y, y'; U) ≥ ε^{-1/(d+ζ)}` for all `y ∈ A`, `|y' − y| ≥ a` and every domain `U`
(DG: `y ∈ K'`, `y' ∉ U'`). -/
def DGP317LbReg (P : Measure Ω) (μ : Ω → Measure ℂ) (d : ℝ) (Q : Set ℂ) (c : ℂ) : Prop :=
  ∀ (A : Set ℂ) (a : ℝ), 0 < a → A ⊆ p17lReg c → cthickening a A ⊆ Q →
    ∀ ζ ∈ Ioo (0 : ℝ) 1, ∃ p C ε₀ : ℝ, 0 < p ∧ 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      P {ω | ¬ ∀ y ∈ A, ∀ y' : ℂ, a ≤ ‖y' - y‖ → ∀ U : Set ℂ,
        ENNReal.ofReal (ε ^ (-(1 / (d + ζ)))) ≤ (dgLGD (μ ω) ε U y y' : ℝ≥0∞)} ≤
        ENNReal.ofReal (C * ε ^ p)

lemma p17l_coord {r c : ℝ} (h0 : c ≤ r) (h1 : r < c + 1) (M : ℕ) :
    ⌊(r - c) * 2 ^ M⌋₊ < 2 ^ M ∧ c + (2 : ℝ)⁻¹ ^ M * (⌊(r - c) * 2 ^ M⌋₊ : ℝ) ≤ r ∧
      r ≤ c + (2 : ℝ)⁻¹ ^ M * (⌊(r - c) * 2 ^ M⌋₊ : ℝ) + (2 : ℝ)⁻¹ ^ M * 1 := by
  obtain ⟨u, hu⟩ : ∃ u, u = (r - c) * 2 ^ M := ⟨_, rfl⟩
  rw [← hu]
  have hp : (0 : ℝ) < 2 ^ M := by positivity
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ M := by positivity
  have hu0 : 0 ≤ u := by rw [hu]; exact mul_nonneg (by linarith) hp.le
  have hu1 : u < 2 ^ M := by
    rw [hu]; have : r - c < 1 := by linarith
    nlinarith
  have e : (2 : ℝ)⁻¹ ^ M * 2 ^ M = 1 := by rw [← mul_pow]; norm_num
  have hr : r = c + (2 : ℝ)⁻¹ ^ M * u := by
    rw [hu, mul_comm (r - c), ← mul_assoc, e, one_mul]; ring
  refine ⟨(Nat.floor_lt hu0).2 (by exact_mod_cast hu1), ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left (Nat.floor_le hu0) ha.le
    linarith
  · have := mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one u).le ha.le
    rw [mul_add] at this
    linarith

/-- every point of `c + [0,1)²` lies in a grid square of level `M` -/
lemma p17l_exists_sq {c y : ℂ} (hy : y ∈ p17lReg c) (M : ℕ) :
    ∃ x ∈ Finset.range (2 ^ M) ×ˢ Finset.range (2 ^ M),
      y ∈ l321In ((2 : ℝ)⁻¹ ^ M) (l313Corner c M x) 1 := by
  simp only [p17lReg, Complex.mem_reProdIm, mem_Ico] at hy
  obtain ⟨a1, a2, a3⟩ := p17l_coord hy.1.1 hy.1.2 M
  obtain ⟨b1, b2, b3⟩ := p17l_coord hy.2.1 hy.2.2 M
  refine ⟨(⌊(y.re - c.re) * 2 ^ M⌋₊, ⌊(y.im - c.im) * 2 ^ M⌋₊),
    Finset.mem_product.2 ⟨Finset.mem_range.2 a1, Finset.mem_range.2 b1⟩, ?_⟩
  simp only [l321In, l313Corner, Complex.mem_reProdIm, mem_Icc, Nat.cast_one]
  exact ⟨⟨a2, a3⟩, ⟨b2, b3⟩⟩

lemma p17l_isClosed_in (s : ℝ) (b : ℂ) : IsClosed (l321In s b 1) :=
  isClosed_Icc.reProdIm isClosed_Icc

lemma p17l_in_sub {s : ℝ} (hs : 0 < s) (b : ℂ) : l321In s b 1 ⊆ interior (l321Out s b 1) := by
  rw [l321Out, Complex.interior_reProdIm, interior_Icc, interior_Icc]
  intro z hz
  simp only [l321In, Complex.mem_reProdIm, mem_Icc, Nat.cast_one, mul_one] at hz
  simp only [Complex.mem_reProdIm, mem_Ioo, Nat.cast_one, mul_one]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]

/-- a path from `y ∈ S` to `y' ∉ int S(1)` crosses the annulus (DG:1396, via
`dgLGDSet_half_le`) -/
lemma p17l_cross {μ : Measure ℂ} {ε : ℝ} {S T : Set ℂ} (hS : IsClosed S)
    (hST : S ⊆ interior T) {y y' : ℂ} (hy : y ∈ S) (hy' : y' ∉ interior T) :
    dgLGDSet μ ε univ S (frontier T) ≤ dgLGD μ ε univ y y' := by
  unfold dgLGD
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨x, ρ, Pa, hb, hc⟩ := hN
  exact dgLGDSet_half_le hS hST Pa hb hc (t := 0) (by rw [Path.extend_zero]; exact hy) hy'

lemma p17l_pow_lt {ε t β : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) (hβ : 0 < β) (h : ε < t ^ (1 / β)) :
    ε ^ β < t := by
  have := Real.rpow_lt_rpow hε h hβ
  rwa [← Real.rpow_mul ht.le, one_div_mul_cancel hβ.ne', Real.rpow_one] at this

/-- the exponent algebra: `l321Tgt ≥ ε^{-1/(d+ζ)}` once `max ĥ_{ε^β} ≥ −3 log ε^{-β}` and
`β(2 + γ²/2 + 3γ)/d + ζ₁ ≤ 1/d − 1/(d+ζ)` -/
lemma p17l_tgt {γ d ζ ζ₁ β ε x : ℝ} (hγ : 0 < γ) (hd : 0 < d) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hx : -(3 * Real.log (ε ^ β)⁻¹) ≤ x)
    (hβ : β * (2 + γ ^ 2 / 2 + 3 * γ) / d + ζ₁ ≤ 1 / d - 1 / (d + ζ)) :
    ε ^ (-(1 / (d + ζ))) ≤ l321Tgt γ d ζ₁ β ε x := by
  unfold l321Tgt
  have hl : Real.log (ε ^ β)⁻¹ = -(β * Real.log ε) := by
    rw [Real.log_inv, Real.log_rpow hε0]
  rw [hl] at hx
  have hexp : ε ^ (3 * γ * β / d) ≤ Real.exp (γ / d * x) := by
    rw [Real.rpow_def_of_pos hε0]
    refine Real.exp_le_exp.2 ?_
    have hx' : 3 * (β * Real.log ε) ≤ x := by linarith
    have := mul_le_mul_of_nonneg_left hx' (div_pos hγ hd).le
    have key : γ / d * (3 * (β * Real.log ε)) = Real.log ε * (3 * γ * β / d) := by ring
    linarith
  calc ε ^ (-(1 / (d + ζ)))
      ≤ ε ^ (-(1 / d) + β * (2 + γ ^ 2 / 2) / d + ζ₁ + 3 * γ * β / d) := by
        refine Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le ?_
        have : β * (2 + γ ^ 2 / 2) / d + 3 * γ * β / d = β * (2 + γ ^ 2 / 2 + 3 * γ) / d := by
          ring
        linarith
    _ = ε ^ (-(1 / d) + β * (2 + γ ^ 2 / 2) / d + ζ₁) * ε ^ (3 * γ * β / d) :=
        Real.rpow_add hε0 _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hε0.le _)

open Classical in
/-- **`DGP317LbReg` from DG Lemmas 3.21 and 3.5** (DG:1588–1589, DG:1393–1397; DV-DGLB-1) -/
theorem dgP317Lb_of (hW : IsWhiteNoise P W) {γ d : ℝ} (hγ : 0 < γ) (hd : 1 ≤ d)
    {μ : Ω → Measure ℂ} {Q : Set ℂ} (hQ : Bornology.IsBounded Q) (c : ℂ)
    (h319 : DGLem319Scaled P W μ γ d Q) : DGP317LbReg P μ d Q c := by
  intro A a ha hA hAQ ζ hζ
  have hd0 : 0 < d := by linarith
  set g := 1 / d - 1 / (d + ζ) with hgd
  have hg : 0 < g := by
    have := one_div_lt_one_div_of_lt hd0 (by linarith [hζ.1] : d < d + ζ)
    linarith
  set s := 2 + γ ^ 2 / 2 + 3 * γ with hsd
  have hs : 0 < s := by positivity
  set β := min (1 / (2 + γ) ^ 2) (g * d / (2 * s)) with hβd
  have hβ : 0 < β := lt_min (by positivity) (by positivity)
  have hβγ : β < 2 / (2 + γ) ^ 2 :=
    (min_le_left _ _).trans_lt (div_lt_div_of_pos_right (by norm_num) (by positivity))
  have hβg : β * s / d + g / 2 ≤ g := by
    have hb : β * s ≤ g * d / (2 * s) * s :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le
    have e : g * d / (2 * s) * s = g / 2 * d := by field_simp
    rw [e] at hb
    have : β * s / d ≤ g / 2 := by rw [div_le_iff₀ hd0]; exact hb
    linarith
  obtain ⟨p, C, ε₀, hp, hε₀, h321⟩ :=
    dg_lemma321 hW hγ hd hβ hβγ hQ c h319 (ζ := g / 2) (by positivity)
  obtain ⟨K, δ₀, hδ₀, h35⟩ := dg_lemma35 hW hQ (ζ := 1) one_pos
  have ha6 : 0 < a / 6 := by positivity
  refine ⟨min p β, |C| + |K|, min (min ε₀ 1) (min (δ₀ ^ (1 / β)) ((a / 6) ^ (1 / β))),
    lt_min hp hβ, lt_min (lt_min hε₀ one_pos)
      (lt_min (Real.rpow_pos_of_pos hδ₀ _) (Real.rpow_pos_of_pos ha6 _)), fun ε hε => ?_⟩
  obtain ⟨hε0, hεm⟩ := hε
  have hεε₀ : ε < ε₀ := hεm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε1 : ε < 1 := hεm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hεδ : ε ^ β < δ₀ := p17l_pow_lt hε0.le hδ₀ hβ
    (hεm.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hεa : ε ^ β < a / 6 := p17l_pow_lt hε0.le ha6 hβ
    (hεm.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hεβ : 0 < ε ^ β := Real.rpow_pos_of_pos hε0 β
  have hsub : {ω | ¬ ∀ y ∈ A, ∀ y' : ℂ, a ≤ ‖y' - y‖ → ∀ U : Set ℂ,
        ENNReal.ofReal (ε ^ (-(1 / (d + ζ)))) ≤ (dgLGD (μ ω) ε U y y' : ℝ≥0∞)} ⊆
      {ω | ∃ x ∈ l321Grid Q c β ε, (l313Set (μ ω) ε univ
          (l321In ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner c (l321M β ε) x) 1)
          (frontier (l321Out ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner c (l321M β ε) x) 1)) : ℝ≥0∞) <
        ENNReal.ofReal (l321Tgt γ d (g / 2) β ε (sSup ((fun z => DDDF.phiVer W P (ε ^ β) 1 z ω) ''
          l321Out ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner c (l321M β ε) x) 1)))} ∪
      {ω | ∃ z ∈ Q, (2 + 1) * Real.log (ε ^ β)⁻¹ < |DDDF.phiVer W P (ε ^ β) 1 z ω|} := by
    intro ω hω
    by_contra hn
    simp only [mem_union, mem_ofPred_eq, not_or, not_exists, not_and, not_lt] at hn
    obtain ⟨n1, n2⟩ := hn
    apply hω
    intro y hy y' hy' U
    set M := l321M β ε
    set δ := (2 : ℝ)⁻¹ ^ M with hδd
    have hδ0 : 0 < δ := by positivity
    have hδ : δ ≤ ε ^ β := (l321M_le hβ hε0 hε1).1
    obtain ⟨x, hx, hyS⟩ := p17l_exists_sq (hA hy) M
    set b := l313Corner c M x
    have hST := p17l_in_sub hδ0 b
    have hyT : y ∈ l321Out δ b 1 := interior_subset (hST hyS)
    have hS1 : l321Out δ b 1 ⊆ cthickening a A := fun z hz =>
      mem_cthickening_of_dist_le z y a A hy (by
        rw [dist_eq_norm]; exact (l321Out_diam b hz hyT).trans (by linarith))
    have hxG : x ∈ l321Grid Q c β ε := Finset.mem_filter.2 ⟨hx, hS1.trans hAQ⟩
    have hy'T : y' ∉ interior (l321Out δ b 1) := fun h => by
      have := l321Out_diam b (interior_subset h) hyT
      linarith
    have hcross := p17l_cross (μ := μ ω) (ε := ε) (p17l_isClosed_in δ b) hST hyS hy'T
    have hmono := dgLGD_mono_dom (μ := μ ω) (ε := ε) (U := U) (U' := univ)
      (by rw [closure_univ]; exact subset_univ _) y y'
    have h1 := n1 x hxG
    have hbd : ∀ z ∈ Q, |DDDF.phiVer W P (ε ^ β) 1 z ω| ≤ 3 * Real.log (ε ^ β)⁻¹ := by
      intro z hz; have := n2 z hz; norm_num at this ⊢; linarith
    have hbQ : b ∈ Q := hAQ (hS1 (l321_corner_mem δ hδ0.le b))
    have hBdd : BddAbove ((fun z => DDDF.phiVer W P (ε ^ β) 1 z ω) '' l321Out δ b 1) := by
      refine ⟨3 * Real.log (ε ^ β)⁻¹, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (le_abs_self _).trans (hbd z (hAQ (hS1 hz)))
    have hsup : -(3 * Real.log (ε ^ β)⁻¹) ≤
        sSup ((fun z => DDDF.phiVer W P (ε ^ β) 1 z ω) '' l321Out δ b 1) :=
      (neg_le_of_abs_le (hbd b hbQ)).trans
        (le_csSup hBdd ⟨b, l321_corner_mem δ hδ0.le b, rfl⟩)
    have hT := p17l_tgt (ζ₁ := g / 2) hγ hd0 hε0 hε1 hsup (by rw [← hgd]; linarith)
    calc ENNReal.ofReal (ε ^ (-(1 / (d + ζ)))) ≤ ENNReal.ofReal (l321Tgt γ d (g / 2) β ε
          (sSup ((fun z => DDDF.phiVer W P (ε ^ β) 1 z ω) '' l321Out δ b 1))) :=
          ENNReal.ofReal_le_ofReal hT
      _ ≤ _ := h1
      _ ≤ (dgLGD (μ ω) ε univ y y' : ℝ≥0∞) := ENat.toENNReal_le.2 hcross
      _ ≤ _ := ENat.toENNReal_le.2 hmono
  have hp' : ε ^ p ≤ ε ^ (min p β) :=
    Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (min_le_left _ _)
  have hβ' : ε ^ β ≤ ε ^ (min p β) :=
    Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (min_le_right _ _)
  calc P _ ≤ P _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C * ε ^ p) + ENNReal.ofReal (K * (ε ^ β) ^ (1 : ℝ)) :=
        add_le_add (h321 ε hε0 hεε₀) (h35 (ε ^ β) ⟨hεβ, hεδ⟩)
    _ ≤ ENNReal.ofReal (|C| * ε ^ (min p β)) + ENNReal.ofReal (|K| * ε ^ (min p β)) := by
        rw [Real.rpow_one]
        exact add_le_add
          (ENNReal.ofReal_le_ofReal (mul_le_mul (le_abs_self _) hp' (by positivity)
            (abs_nonneg _)))
          (ENNReal.ofReal_le_ofReal (mul_le_mul (le_abs_self _) hβ' hεβ.le (abs_nonneg _)))
    _ = ENNReal.ofReal ((|C| + |K|) * ε ^ (min p β)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

end DG
end LQGMetric
