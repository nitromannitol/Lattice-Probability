/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P9 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P9Good
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3MuL8

/-!
# DG Proposition 3.9 (P2-DG105j)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Proposition 3.9 (DG:1159–1167,
proof DG:1346–1391): for each `ζ ∈ (0,1)`, with polynomially high probability as `ε → 0`,
`max_{z,w ∈ 𝕊} D^ε(z, w; 𝕊(1/2)) ≤ ε^{-1/(d−ζ)}`.

Formalized at `𝕍`-scale (DV-D105-3) for a square `𝕊 = c + [0,L]²` and a set `Q ⊇ c + [−r, L+r]²`
(`L + r ≤ 1`; DG: `𝕊 = [0,1]²`, `𝕊(1/2) = [−1/2,3/2]²`, here e.g. `𝕊 = [1/3,2/3]²`,
`Q = [1/6,5/6]²`), from
* DG Lemma 3.14 in both orientations (`dg_lemma314`, `dg_lemma314V`, i.e. from DG Lemma 3.11
  transported by (3.7): hypotheses `DGLem311Scaled`, `DGLem311ScaledV`), and
* the second estimate of DG Lemma 3.8 (`DGL38Upper` on `𝕊` for one `β̄ > 0`; DG:1371, "each
  Euclidean ball of mass `ε` intersecting `𝕊` has radius at least `2ε^A`", used only through
  "`D(u, v) = 1` for `u, v` in a dyadic square of side `≤ ε^A`").
The proof is DG's (deterministic part `p39_good`, files S3P9Top–S3P9Good).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DG Proposition 3.9** (DG:1159–1167) -/
theorem dg_prop39 (hW : IsWhiteNoise P W) {γ d : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hd : 1 ≤ d)
    {μ : Ω → Measure ℂ} {Q : Set ℂ} (hQb : Bornology.IsBounded Q) (c : ℂ) {L r : ℝ}
    (hL0 : 0 ≤ L) (hr : 0 < r) (hLr : L + r ≤ 1) (hQ : p39Box c L r ⊆ Q)
    (h311 : DGLem311Scaled P W μ γ d Q) (h311v : DGLem311ScaledV P W μ γ d Q) {βb : ℝ}
    (hβb : 0 < βb) (hL38 : DGL38Upper P μ (p39Sq c L) βb) {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ p C ε₀ : ℝ, 0 < p ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      P {ω | ¬ ∀ z ∈ p39Sq c L, ∀ w ∈ p39Sq c L,
        (dgLGD (μ ω) ε Q z w : ℝ≥0∞) ≤ ENNReal.ofReal (ε ^ (-(1 / (d - ζ))))} ≤
        ENNReal.ofReal (C * ε ^ p) := by
  -- the parameters `ζ̃`, `β` (DG:1347)
  set ζt := min (ζ / 2) ((2 - γ) ^ 2 / 4) with hζt
  have hγ' : 0 < (2 - γ) ^ 2 := by nlinarith
  have hζt0 : 0 < ζt := lt_min (by linarith) (by linarith)
  have hζtζ : ζt < ζ := (min_le_left _ _).trans_lt (by linarith)
  have hζt1 : ζt < 1 := hζtζ.trans hζ1
  have hc : 0 ≤ 2 + γ ^ 2 / 2 - 2 * γ - ζt := by
    have := min_le_right (ζ / 2) ((2 - γ) ^ 2 / 4); nlinarith
  have hdz : 0 < d - ζ := by linarith
  have hdzt : 0 < d - ζt := by linarith
  have hgap : 0 < 1 / (d - ζ) - 1 / (d - ζt) := by
    have := one_div_lt_one_div_of_lt hdz (show d - ζ < d - ζt by linarith); linarith
  set β := (1 / (d - ζ) - 1 / (d - ζt)) / 2 with hβ_def
  have hβ : 0 < β := by positivity
  have hg : 1 / (d - ζ) = 2 * β + 1 / (d - ζt) := by rw [hβ_def]; ring
  -- the three estimates
  obtain ⟨p₁, C₁, ε₁, hp₁, hε₁, h1⟩ := dg_lemma314 hW hγ hd hQb c h311 hζt0 hζt1 hβ
  obtain ⟨p₂, C₂, ε₂, hp₂, hε₂, h2⟩ := dg_lemma314V hW hγ hd hQb c h311v hζt0 hζt1 hβ
  obtain ⟨p₃, C₃, ε₃, hp₃, hε₃, h3⟩ := hL38
  set A := (β + βb) * (2 / (β / 8)) + 5 with hA_def
  have hA0 : 0 < 120 * A ^ 4 := by positivity
  set ε₄ := (120 * A ^ 4) ^ (-(2 / β)) with hε₄
  have hε₄0 : 0 < ε₄ := Real.rpow_pos_of_pos hA0 _
  set ε₅ := (r / 4) ^ β⁻¹
  have hε₅0 : 0 < ε₅ := Real.rpow_pos_of_pos (by positivity) _
  set ε₆ := r ^ βb⁻¹
  have hε₆0 : 0 < ε₆ := Real.rpow_pos_of_pos hr _
  refine ⟨min p₁ (min p₂ p₃), |C₁| + |C₂| + |C₃|,
    min (min 1 (min ε₁ ε₂)) (min (min ε₃ ε₄) (min ε₅ ε₆)), lt_min hp₁ (lt_min hp₂ hp₃),
    lt_min (lt_min one_pos (lt_min hε₁ hε₂)) (lt_min (lt_min hε₃ hε₄0) (lt_min hε₅0 hε₆0)),
    fun ε hε hεlt => ?_⟩
  simp only [lt_min_iff] at hεlt
  obtain ⟨⟨hε1, hεa, hεb⟩, ⟨hεc, hεd⟩, hεe, hεf⟩ := hεlt
  -- the deterministic conditions
  have hεβ : ε ^ β ≤ r / 4 := by
    calc ε ^ β ≤ ε₅ ^ β := Real.rpow_le_rpow hε.le hεe.le hβ.le
      _ = r / 4 := Real.rpow_inv_rpow (by positivity) hβ.ne'
  have hεβb : ε ^ βb ≤ r := by
    calc ε ^ βb ≤ ε₆ ^ βb := Real.rpow_le_rpow hε.le hεf.le hβb.le
      _ = r := Real.rpow_inv_rpow hr.le hβb.ne'
  have hAε : 120 * A ^ 4 ≤ (ε ^ (-(β / 8))) ^ 4 := by
    rw [← Real.rpow_natCast (ε ^ (-(β / 8))) 4, ← Real.rpow_mul hε.le]
    calc 120 * A ^ 4 = ε₄ ^ (-(β / 8) * ((4 : ℕ) : ℝ)) := by
          rw [hε₄, ← Real.rpow_mul hA0.le]
          have : -(2 / β) * (-(β / 8) * ((4 : ℕ) : ℝ)) = 1 := by
            push_cast; field_simp; ring
          rw [this, Real.rpow_one]
      _ ≤ ε ^ (-(β / 8) * ((4 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hε hεd.le (by push_cast; nlinarith)
  -- the union bound
  have hsub : {ω | ¬ ∀ z ∈ p39Sq c L, ∀ w ∈ p39Sq c L,
      (dgLGD (μ ω) ε Q z w : ℝ≥0∞) ≤ ENNReal.ofReal (ε ^ (-(1 / (d - ζ))))} ⊆
      ({ω | ∃ m : ℕ, (2 : ℝ)⁻¹ ^ m ≤ ε ^ β ∧ ∃ x ∈ l313Grid Q c m, ¬ (l313Set (μ ω) ε
          (l313Str ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
          (l313Left ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
          (l313Right ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1) : ℝ≥0∞) ≤ ENNReal.ofReal
        (max ((m : ℝ) ^ 3) (ε ^ (-(1 / (d - ζt))) *
          (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - 2 * γ - ζt) * m / d))))} ∪
      {ω | ∃ m : ℕ, (2 : ℝ)⁻¹ ^ m ≤ ε ^ β ∧ ∃ x ∈ l313GridV Q c m, ¬ (l313Set (μ ω) ε
          (l313StrV ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
          (l313Bot ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1)
          (l313Top ((2 : ℝ)⁻¹ ^ m) (l313Corner c m x) 1) : ℝ≥0∞) ≤ ENNReal.ofReal
        (max ((m : ℝ) ^ 3) (ε ^ (-(1 / (d - ζt))) *
          (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - 2 * γ - ζt) * m / d))))}) ∪
      {ω | ¬ ∀ z ∈ p39Sq c L, μ ω (Metric.ball z (ε ^ βb)) ≤ ENNReal.ofReal ε} := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨n1, n2⟩, n3⟩ := hcon
    apply hω
    exact p39_good hL0 hr hLr hQ hε hε1 hβ hβb hεβ hεβb (by linarith) hdzt hg hc hAε
      (fun m hm x hx => by by_contra hne; exact n1 ⟨m, hm, x, hx, hne⟩)
      (fun m hm x hx => by by_contra hne; exact n2 ⟨m, hm, x, hx, hne⟩)
      (not_not.1 n3)
  have hpow : ∀ q : ℝ, min p₁ (min p₂ p₃) ≤ q → ε ^ q ≤ ε ^ min p₁ (min p₂ p₃) :=
    fun q hq => Real.rpow_le_rpow_of_exponent_ge hε hε1.le hq
  have hb : ∀ (Ci q : ℝ), min p₁ (min p₂ p₃) ≤ q →
      ENNReal.ofReal (Ci * ε ^ q) ≤ ENNReal.ofReal (|Ci| * ε ^ min p₁ (min p₂ p₃)) := by
    intro Ci q hq
    apply ENNReal.ofReal_le_ofReal
    have := hpow q hq
    have h0 : 0 ≤ ε ^ q := (Real.rpow_pos_of_pos hε q).le
    calc Ci * ε ^ q ≤ |Ci| * ε ^ q := mul_le_mul_of_nonneg_right (le_abs_self Ci) h0
      _ ≤ _ := mul_le_mul_of_nonneg_left this (abs_nonneg Ci)
  have hpp : 0 ≤ ε ^ min p₁ (min p₂ p₃) := (Real.rpow_pos_of_pos hε _).le
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ENNReal.ofReal (C₁ * ε ^ p₁) + ENNReal.ofReal (C₂ * ε ^ p₂) +
        ENNReal.ofReal (C₃ * ε ^ p₃) :=
        add_le_add (add_le_add (h1 ε hε hεa) (h2 ε hε hεb)) (h3 ε hε hεc)
    _ ≤ ENNReal.ofReal (|C₁| * ε ^ min p₁ (min p₂ p₃)) +
        ENNReal.ofReal (|C₂| * ε ^ min p₁ (min p₂ p₃)) +
        ENNReal.ofReal (|C₃| * ε ^ min p₁ (min p₂ p₃)) :=
        add_le_add (add_le_add (hb _ _ (min_le_left _ _))
          (hb _ _ ((min_le_right _ _).trans (min_le_left _ _))))
          (hb _ _ ((min_le_right _ _).trans (min_le_right _ _)))
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end DG
end LQGMetric
