/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P17V2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17V1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L4Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.17 at `𝕍`-scale, part 2: Lemma 3.13 carried from `𝕍` to `𝕊` (P2-DG317V)

Ding–Gwynne arXiv:1807.01072 (`metric-comparison-final.tex`), Lemma 3.13 (DG:1282–1291) as used
in Step 1 of the proof of Prop 3.17 (DG:1541–1555), D121. With `W' = p17vW W`, `μ` at `𝕍`-scale
and `μ' = (T⁻¹)_* μ` (`p17vMu`): DG Lemma 3.13 for `(W', μ)` on the `𝕍`-scale grid of level
`m + 1` with corner `(1+i)/4` inside `[1/6,5/6]²` (`dg_lemma313`, `dg_lemma313V`, from
`DGLem311Scaled(V) P W' μ` on `[1/6,5/6]²`) gives Lemma 3.13 for `μ'` on the `𝕊`-scale grid of
level `m` inside `[−1/6,7/6]²`, with the field `φ_t = ĥ_{2^{-m-1}}[W'] ∘ T` (`p17v_lemma313`,
`p17v_lemma313V`): the rectangles correspond exactly under `T` (`p17v_pre_str`), the LGD only
decreases (`p17v_set_le`), and the target of level `m + 1` is at most the target of level `m`
once the `m³` term is dominated (hypothesis `hcub`, checked by the consumer for `ε = δ^{(2+γ)²}`),
using DG Lemma 3.5 for `W'` (`dg_lemma35`, `|ĥ_{2^{-m-1}}[W']| ≤ 3 log 2^{m+1}` on `[1/6,5/6]²`).
Own elementary glue (proposed DV-DG317V-1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma p17v_QV_bdd : Bornology.IsBounded (p39Box p18c0 (1 / 3) (1 / 6)) :=
  (Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _)

/-- the target of level `m + 1` is at most the target of level `m` once `(m+1)³` is dominated -/
lemma p17v_tgt_succ {γ d η ε X : ℝ} {m : ℕ} (hd : 0 < d) (hη : η < 2 + γ ^ 2 / 2)
    (h : ((m + 1 : ℕ) : ℝ) ^ 3 ≤ ε ^ (-(1 / (d - η))) *
      (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - η) * m / d)) * Real.exp (γ / d * X)) (hε : 0 ≤ ε) :
    l313Tgt γ d η ε (m + 1) X ≤ l313Tgt γ d η ε m X := by
  unfold l313Tgt
  refine max_le (h.trans (le_max_right _ _)) (le_trans ?_ (le_max_right _ _))
  have hc : 0 ≤ 2 + γ ^ 2 / 2 - η := by linarith
  have : (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - η) * ((m + 1 : ℕ) : ℝ) / d)) ≤
      (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - η) * m / d)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [neg_le_neg_iff]
    refine div_le_div_of_nonneg_right ?_ hd.le
    push_cast
    nlinarith
  have h0 : 0 ≤ ε ^ (-(1 / (d - η))) := Real.rpow_nonneg hε _
  gcongr

/-- lower bound on `inf_S φ'∘T` from `|φ'| ≤ 3 log s⁻¹` on `T(S)` -/
lemma p17v_sInf_ge {f : ℂ → ℝ} {S Q : Set ℂ} {B : ℝ} (hS : S.Nonempty)
    (hSQ : p17vT '' S ⊆ Q) (hf : ∀ z ∈ Q, |f z| ≤ B) :
    -B ≤ sInf ((fun z => f (p17vT z)) '' S) :=
  le_csInf (hS.image _) (forall_mem_image.2 fun z hz => by
    have := hf _ (hSQ ⟨z, hz, rfl⟩); have := neg_abs_le (f (p17vT z)); linarith)

lemma p17v_log_p39d (m : ℕ) : Real.log (p39d m)⁻¹ = m * Real.log 2 := by
  rw [p39d, inv_pow, inv_inv, Real.log_pow]

/-- the probability bookkeeping: two exponential tails, or the trivial bound for small `m` -/
lemma p17v_prob [IsProbabilityMeasure P] {E E1 E3 : Set Ω} {C1 K3 d3 lam1 : ℝ} (hd3 : 0 < d3)
    (hlam1 : 0 < lam1) (m : ℕ)
    (hgood : p39d (m + 1) < d3 → E ⊆ E1 ∪ E3)
    (h1 : P E1 ≤ ENNReal.ofReal (C1 * Real.exp (-(lam1 * ((m + 1 : ℕ) : ℝ)))))
    (h3 : p39d (m + 1) < d3 → P E3 ≤ ENNReal.ofReal (K3 * p39d (m + 1) ^ (1 : ℝ))) :
    P E ≤ ENNReal.ofReal ((|C1| + |K3| + 1 / d3) *
      Real.exp (-(min lam1 (Real.log 2) * m))) := by
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  set lam := min lam1 (Real.log 2)
  have hlam : 0 < lam := lt_min hlam1 hl2
  have hE : Real.exp (-(Real.log 2 * m)) = p39d m := by
    rw [p39d, inv_pow, ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ m), ← Real.exp_neg,
      Real.log_pow]; ring_nf
  have hmono : ∀ a : ℝ, lam ≤ a → Real.exp (-(a * m)) ≤ Real.exp (-(lam * m)) := fun a ha =>
    Real.exp_le_exp.2 (by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hE0 := Real.exp_pos (-(lam * m))
  by_cases hm : p39d (m + 1) < d3
  · refine (measure_mono (hgood hm)).trans ((measure_union_le _ _).trans ?_)
    have b1 : P E1 ≤ ENNReal.ofReal (|C1| * Real.exp (-(lam * m))) := by
      refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
      have hl : lam ≤ lam1 := min_le_left _ _
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have he : Real.exp (-(lam1 * ((m + 1 : ℕ) : ℝ))) ≤ Real.exp (-(lam * m)) := by
        refine Real.exp_le_exp.2 ?_
        push_cast
        nlinarith
      exact mul_le_mul (le_abs_self _) he (Real.exp_pos _).le (abs_nonneg _)
    have b3 : P E3 ≤ ENNReal.ofReal (|K3| * Real.exp (-(lam * m))) := by
      refine (h3 hm).trans (ENNReal.ofReal_le_ofReal (mul_le_mul (le_abs_self _) ?_
        (by positivity) (abs_nonneg _)))
      rw [Real.rpow_one, p39d_succ, ← hE]
      have := Real.exp_pos (-(Real.log 2 * m))
      exact (half_le_self this.le).trans (hmono _ (min_le_right _ _))
    refine (add_le_add b1 b3).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ 1 / d3 * Real.exp (-(lam * m)) := by positivity
    nlinarith
  · have h1le : (1 : ℝ) ≤ 1 / d3 * Real.exp (-(lam * m)) := by
      have : d3 ≤ p39d m := by
        rw [not_lt, p39d_succ] at hm; have := p39d_pos m; linarith
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hd3, one_mul]
      exact this.trans (hE ▸ hmono _ (min_le_right _ _))
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (h1le.trans ?_)
    gcongr
    linarith [abs_nonneg C1, abs_nonneg K3]

/-- the cubic condition with the field bound `X ≥ −3 (m+1) log 2` -/
lemma p17v_cub_mono {γ d η ε X : ℝ} {m : ℕ} (hγ : 0 < γ) (hd : 0 < d)
    (hX : -(3 * (((m + 1 : ℕ) : ℝ) * Real.log 2)) ≤ X)
    (h : ((m + 1 : ℕ) : ℝ) ^ 3 ≤ ε ^ (-(1 / (d - η))) *
      (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - η) * m / d)) *
        Real.exp (γ / d * (-(3 * (((m + 1 : ℕ) : ℝ) * Real.log 2))))) (hε : 0 ≤ ε) :
    ((m + 1 : ℕ) : ℝ) ^ 3 ≤ ε ^ (-(1 / (d - η))) *
      (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - η) * m / d)) * Real.exp (γ / d * X) := by
  refine h.trans ?_
  have h0 : 0 ≤ ε ^ (-(1 / (d - η))) * (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - η) * m / d)) :=
    mul_nonneg (Real.rpow_nonneg hε _) (Real.rpow_nonneg (by norm_num) _)
  have hg : 0 ≤ γ / d := (div_pos hγ hd).le
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hX hg)) h0

/-- **DG Lemma 3.13 carried from `𝕍` to `𝕊`** (horizontal rectangles; DG:1282–1291) -/
theorem p17v_lemma313 (hW : IsWhiteNoise P W) {γ d : ℝ} (hγ : 0 < γ) (hd : 1 ≤ d)
    {μ : Ω → Measure ℂ}
    (h311 : DGLem311Scaled P (p17vW W) μ γ d (p39Box p18c0 (1 / 3) (1 / 6)))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ lam C : ℝ, 0 < lam ∧ ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ((m + 1 : ℕ) : ℝ) ^ 3 ≤ ε ^ (-(1 / (d - η))) *
        (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - η) * m / d)) *
          Real.exp (γ / d * (-(3 * (((m + 1 : ℕ) : ℝ) * Real.log 2)))) →
      P {ω | ∃ x ∈ l313Grid (p39Box 0 1 (1 / 6)) 0 m, ¬ (l313Set (p17vMu μ ω) ε
          (l313Str (p39d m) (l313Corner 0 m x) 1) (l313Left (p39d m) (l313Corner 0 m x) 1)
          (l313Right (p39d m) (l313Corner 0 m x) 1) : ℝ≥0∞) ≤
        ENNReal.ofReal (l313Tgt γ d η ε m (sInf ((fun z =>
          DDDF.phiVer (p17vW W) P (p39d (m + 1)) 1 (p17vT z) ω) ''
            l313Str (p39d m) (l313Corner 0 m x) 1)))} ≤
        ENNReal.ofReal (C * Real.exp (-(lam * m))) := by
  classical
  have hP := hW.isProbabilityMeasure
  have hW' := isWhiteNoise_p17vW hW
  have hd0 : 0 < d := by linarith
  obtain ⟨lam1, C1, hlam1, h1⟩ := dg_lemma313 hW' hγ hd p17v_QV_bdd p17vc0 h311 hη hη1
  obtain ⟨K3, d3, hd3, h3⟩ := dg_lemma35 hW' p17v_QV_bdd (ζ := 1) one_pos
  refine ⟨min lam1 (Real.log 2), |C1| + |K3| + 1 / d3,
    lt_min hlam1 (Real.log_pos (by norm_num)), fun m ε hε hε1 hcub => ?_⟩
  refine p17v_prob hd3 hlam1 m (fun hm => ?_) (h1 (m + 1) ε hε hε1)
    (fun hm => h3 _ ⟨p39d_pos _, hm⟩)
  intro ω hω
  by_contra hn
  simp only [mem_union, not_or, mem_ofPred_eq, not_exists, not_and, not_not, not_lt] at hn hω
  obtain ⟨n1, n3⟩ := hn
  obtain ⟨x, hx, hxb⟩ := hω
  apply hxb
  have hx' := p17v_grid_mem hx
  have hb := n1 x hx'
  have hd2 : p39d m / 2 = (2 : ℝ)⁻¹ ^ (m + 1) := by rw [p39d, pow_succ]; ring
  have hpre : p17vTinv ⁻¹' l313Str (p39d m) (l313Corner 0 m x) 1 =
      l313Str ((2 : ℝ)⁻¹ ^ (m + 1)) (l313Corner p17vc0 (m + 1) x) 1 := by
    rw [← p17vTinv_corner, p17v_pre_str, hd2]
  have hset : l313Set ((μ ω).map p17vTinv) ε (l313Str (p39d m) (l313Corner 0 m x) 1)
      (l313Left (p39d m) (l313Corner 0 m x) 1) (l313Right (p39d m) (l313Corner 0 m x) 1) ≤
      l313Set (μ ω) ε (l313Str ((2 : ℝ)⁻¹ ^ (m + 1)) (l313Corner p17vc0 (m + 1) x) 1)
        (l313Left ((2 : ℝ)⁻¹ ^ (m + 1)) (l313Corner p17vc0 (m + 1) x) 1)
        (l313Right ((2 : ℝ)⁻¹ ^ (m + 1)) (l313Corner p17vc0 (m + 1) x) 1) := by
    refine p17v_set_le hpre (fun z hz => ?_) (fun z hz => ?_)
    · have := p17v_mem_left (s := p39d m) (b := l313Corner p17vc0 (m + 1) x) (n := 1)
        (z := z) (by rwa [hd2])
      rwa [p17vTinv_corner] at this
    · have := p17v_mem_right (s := p39d m) (b := l313Corner p17vc0 (m + 1) x) (n := 1)
        (z := z) (by rwa [hd2])
      rwa [p17vTinv_corner] at this
  have himg : (fun z => DDDF.phiVer (p17vW W) P (p39d (m + 1)) 1 (p17vT z) ω) ''
        l313Str (p39d m) (l313Corner 0 m x) 1 =
      (fun z => DDDF.phiVer (p17vW W) P ((2 : ℝ)⁻¹ ^ (m + 1)) 1 z ω) ''
        l313Str ((2 : ℝ)⁻¹ ^ (m + 1)) (l313Corner p17vc0 (m + 1) x) 1 := by
    rw [← hpre, ← p17vT_image_eq, image_image]
  have hQ : p17vT '' l313Str (p39d m) (l313Corner 0 m x) 1 ⊆ p39Box p18c0 (1 / 3) (1 / 6) := by
    rw [p17vT_image_eq, hpre]; exact (Finset.mem_filter.1 hx').2
  have hX := p17v_sInf_ge (f := fun z => DDDF.phiVer (p17vW W) P (p39d (m + 1)) 1 z ω)
    ⟨_, l313_corner_mem _ (by positivity) _⟩ hQ
    (fun z hz => n3 z hz)
  rw [p17v_log_p39d] at hX
  have hX' : -(3 * (((m + 1 : ℕ) : ℝ) * Real.log 2)) ≤
      sInf ((fun z => DDDF.phiVer (p17vW W) P (p39d (m + 1)) 1 (p17vT z) ω) ''
        l313Str (p39d m) (l313Corner 0 m x) 1) := by
    refine le_trans (le_of_eq ?_) hX; push_cast; ring
  refine (ENat.toENNReal_le.2 hset).trans (hb.trans ?_)
  rw [← himg]
  exact ENNReal.ofReal_le_ofReal (p17v_tgt_succ hd0 (by nlinarith)
    (p17v_cub_mono hγ hd0 hX' hcub hε.le) hε.le)

/-- **DG Lemma 3.13 carried from `𝕍` to `𝕊`** (vertical rectangles; DG:1282–1291) -/
theorem p17v_lemma313V (hW : IsWhiteNoise P W) {γ d : ℝ} (hγ : 0 < γ) (hd : 1 ≤ d)
    {μ : Ω → Measure ℂ}
    (h311 : DGLem311ScaledV P (p17vW W) μ γ d (p39Box p18c0 (1 / 3) (1 / 6)))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ lam C : ℝ, 0 < lam ∧ ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ((m + 1 : ℕ) : ℝ) ^ 3 ≤ ε ^ (-(1 / (d - η))) *
        (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - η) * m / d)) *
          Real.exp (γ / d * (-(3 * (((m + 1 : ℕ) : ℝ) * Real.log 2)))) →
      P {ω | ∃ x ∈ l313GridV (p39Box 0 1 (1 / 6)) 0 m, ¬ (l313Set (p17vMu μ ω) ε
          (l313StrV (p39d m) (l313Corner 0 m x) 1) (l313Bot (p39d m) (l313Corner 0 m x) 1)
          (l313Top (p39d m) (l313Corner 0 m x) 1) : ℝ≥0∞) ≤
        ENNReal.ofReal (l313Tgt γ d η ε m (sInf ((fun z =>
          DDDF.phiVer (p17vW W) P (p39d (m + 1)) 1 (p17vT z) ω) ''
            l313StrV (p39d m) (l313Corner 0 m x) 1)))} ≤
        ENNReal.ofReal (C * Real.exp (-(lam * m))) := by
  classical
  have hP := hW.isProbabilityMeasure
  have hW' := isWhiteNoise_p17vW hW
  have hd0 : 0 < d := by linarith
  obtain ⟨lam1, C1, hlam1, h1⟩ := dg_lemma313V hW' hγ hd p17v_QV_bdd p17vc0 h311 hη hη1
  obtain ⟨K3, d3, hd3, h3⟩ := dg_lemma35 hW' p17v_QV_bdd (ζ := 1) one_pos
  refine ⟨min lam1 (Real.log 2), |C1| + |K3| + 1 / d3,
    lt_min hlam1 (Real.log_pos (by norm_num)), fun m ε hε hε1 hcub => ?_⟩
  refine p17v_prob hd3 hlam1 m (fun hm => ?_) (h1 (m + 1) ε hε hε1)
    (fun hm => h3 _ ⟨p39d_pos _, hm⟩)
  intro ω hω
  by_contra hn
  simp only [mem_union, not_or, mem_ofPred_eq, not_exists, not_and, not_not, not_lt] at hn hω
  obtain ⟨n1, n3⟩ := hn
  obtain ⟨x, hx, hxb⟩ := hω
  apply hxb
  have hx' := p17v_gridV_mem hx
  have hb := n1 x hx'
  have hd2 : p39d m / 2 = (2 : ℝ)⁻¹ ^ (m + 1) := by rw [p39d, pow_succ]; ring
  have hpre : p17vTinv ⁻¹' l313StrV (p39d m) (l313Corner 0 m x) 1 =
      l313StrV ((2 : ℝ)⁻¹ ^ (m + 1)) (l313Corner p17vc0 (m + 1) x) 1 := by
    rw [← p17vTinv_corner, p17v_pre_strV, hd2]
  have hset : l313Set ((μ ω).map p17vTinv) ε (l313StrV (p39d m) (l313Corner 0 m x) 1)
      (l313Bot (p39d m) (l313Corner 0 m x) 1) (l313Top (p39d m) (l313Corner 0 m x) 1) ≤
      l313Set (μ ω) ε (l313StrV ((2 : ℝ)⁻¹ ^ (m + 1)) (l313Corner p17vc0 (m + 1) x) 1)
        (l313Bot ((2 : ℝ)⁻¹ ^ (m + 1)) (l313Corner p17vc0 (m + 1) x) 1)
        (l313Top ((2 : ℝ)⁻¹ ^ (m + 1)) (l313Corner p17vc0 (m + 1) x) 1) := by
    refine p17v_set_le hpre (fun z hz => ?_) (fun z hz => ?_)
    · have := p17v_mem_bot (s := p39d m) (b := l313Corner p17vc0 (m + 1) x) (n := 1)
        (z := z) (by rwa [hd2])
      rwa [p17vTinv_corner] at this
    · have := p17v_mem_top (s := p39d m) (b := l313Corner p17vc0 (m + 1) x) (n := 1)
        (z := z) (by rwa [hd2])
      rwa [p17vTinv_corner] at this
  have himg : (fun z => DDDF.phiVer (p17vW W) P (p39d (m + 1)) 1 (p17vT z) ω) ''
        l313StrV (p39d m) (l313Corner 0 m x) 1 =
      (fun z => DDDF.phiVer (p17vW W) P ((2 : ℝ)⁻¹ ^ (m + 1)) 1 z ω) ''
        l313StrV ((2 : ℝ)⁻¹ ^ (m + 1)) (l313Corner p17vc0 (m + 1) x) 1 := by
    rw [← hpre, ← p17vT_image_eq, image_image]
  have hQ : p17vT '' l313StrV (p39d m) (l313Corner 0 m x) 1 ⊆ p39Box p18c0 (1 / 3) (1 / 6) := by
    rw [p17vT_image_eq, hpre]; exact (Finset.mem_filter.1 hx').2
  have hX := p17v_sInf_ge (f := fun z => DDDF.phiVer (p17vW W) P (p39d (m + 1)) 1 z ω)
    ⟨_, l313_corner_memV _ (by positivity) _⟩ hQ
    (fun z hz => n3 z hz)
  rw [p17v_log_p39d] at hX
  have hX' : -(3 * (((m + 1 : ℕ) : ℝ) * Real.log 2)) ≤
      sInf ((fun z => DDDF.phiVer (p17vW W) P (p39d (m + 1)) 1 (p17vT z) ω) ''
        l313StrV (p39d m) (l313Corner 0 m x) 1) := by
    refine le_trans (le_of_eq ?_) hX; push_cast; ring
  refine (ENat.toENNReal_le.2 hset).trans (hb.trans ?_)
  rw [← himg]
  exact ENNReal.ofReal_le_ofReal (p17v_tgt_succ hd0 (by nlinarith)
    (p17v_cub_mono hγ hd0 hX' hcub hε.le) hε.le)

end DG
end LQGMetric
