/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_4Incr at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4Leaf
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.HarmGrad

/-!
# LM Lemma 3.4: the harmonic decay step and the increment input

Source: MQ arXiv:1812.03913 (`lqg_geodesics.tex`), proof of Prop 4.3: l. 677–681 ("by applying the
derivative estimate (4.1) to the harmonic function `𝔥_{0,1}` ... `sup_{B(0,r_ℓ)} |𝔥_{0,1} −
𝔥_{0,1}(0)| ≤ C`") and l. 693–700 (`𝔥_{0,r_ℓ} = 𝔥_{0,1} + 𝔥̃_{0,r_ℓ}`, `𝔥̃_{0,r_ℓ}` independent of
`𝓕_{0,1}`, Gaussian tail by Remark eq. `(zero-boundary)`); LM arXiv:1905.00379 Lemma 3.4
(l. 696–706).

* `harm_decay` — the derivative estimate along a segment: if `g` is harmonic on `B_R(0)` with
  `|g − g(0)| ≤ X` there, then `|g(w) − g(0)| ≤ 8X|w|/(R − ρ)` for `|w| ≤ ρ < R` (from
  `MQ.norm_fderiv_le_of_harmonic` and the mean value inequality).
* `LMIncrLeaf` — the remaining GFF input (exact): the scaled harmonic part at scale `r_k`, centred,
  is the sum over `j ≤ k` of the scaled increments `d_j = (𝔥^{r_j} − 𝔥^{r_{j−1}})(r_j ·)`
  (`d_0 = 𝔥^{r_0}(r_0 ·) − h_{r_0}(0)`), harmonic on `B_{s₃}`, whose oscillations `W_j` on `B_{s₃}`
  are adapted, independent of the past and have a uniform exponential moment.
* `lmScaleDomLeaf_of_incr` — `LMScaleDomLeaf` from `LMIncrLeaf` (`q = s₁`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Finset Metric InnerProductSpace
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

/-- **Derivative estimate along a segment** (MQ l. 677–681, eq. (4.1)). -/
theorem harm_decay {g : ℂ → ℝ} {R ρ X : ℝ} (hρR : ρ < R) (hX : 0 ≤ X)
    (hg : HarmonicOnNhd g (ball (0 : ℂ) R)) (hb : ∀ y ∈ ball (0 : ℂ) R, |g y - g 0| ≤ X)
    {w : ℂ} (hw : ‖w‖ ≤ ρ) : |g w - g 0| ≤ 8 * X * ‖w‖ / (R - ρ) := by
  have hRρ : 0 < R - ρ := by linarith
  have hρ0 : 0 ≤ ρ := (norm_nonneg w).trans hw
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ := mem_closedBall_self hρ0
  have hwm : w ∈ closedBall (0 : ℂ) ρ := by rwa [mem_closedBall, dist_zero_right]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set η := ε * (R - ρ) / (8 * (‖w‖ + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hsub : ∀ x ∈ closedBall (0 : ℂ) ρ, ball x (R - ρ) ⊆ ball (0 : ℂ) R := fun x hx y hy => by
    rw [mem_closedBall, dist_zero_right] at hx
    rw [mem_ball] at hy ⊢
    linarith [dist_triangle y x 0, dist_zero_right x]
  have hin : ∀ x ∈ closedBall (0 : ℂ) ρ, x ∈ ball (0 : ℂ) R := fun x hx =>
    hsub x hx (mem_ball_self hRρ)
  have key : ∀ x ∈ closedBall (0 : ℂ) ρ, ‖fderiv ℝ g x‖ ≤ 8 * (X + η) / (R - ρ) := fun x hx =>
    MQ.norm_fderiv_le_of_harmonic hRρ (by positivity) (hg.mono (hsub x hx))
      fun y hy => (hb y (hsub x hx hy)).trans (by linarith)
  have hdiff : ∀ x ∈ closedBall (0 : ℂ) ρ, DifferentiableAt ℝ g x := fun x hx =>
    (hg x (hin x hx)).1.differentiableAt (by norm_num)
  have H := (convex_closedBall (0 : ℂ) ρ).norm_image_sub_le_of_norm_fderiv_le hdiff key h0 hwm
  rw [Real.norm_eq_abs, sub_zero] at H
  refine H.trans ?_
  have he : 8 * (X + η) / (R - ρ) * ‖w‖ = 8 * X * ‖w‖ / (R - ρ) + ε * (‖w‖ / (‖w‖ + 1)) := by
    rw [hη]; field_simp
  have hq : ‖w‖ / (‖w‖ + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  rw [he]; nlinarith

/-- `r_k / r_j ≤ s₁^{k-j}` -/
lemma ratio_le_pow {r : ℕ → ℝ} {s₁ : ℝ} (hr0 : ∀ k, 0 < r k) (hrs : ∀ k, r (k + 1) / r k ≤ s₁)
    (j : ℕ) : ∀ m, r (j + m) / r j ≤ s₁ ^ m := by
  intro m
  induction m with
  | zero => rw [add_zero, div_self (hr0 j).ne', pow_zero]
  | succ m ih =>
    have h1 := hrs (j + m)
    have hs : 0 ≤ s₁ := (div_pos (hr0 _) (hr0 _)).le.trans h1
    rw [div_le_iff₀ (hr0 _)] at h1
    rw [div_le_iff₀ (hr0 j)] at ih ⊢
    rw [← add_assoc, pow_succ]
    calc r (j + m + 1) ≤ s₁ * r (j + m) := h1
      _ ≤ s₁ * (s₁ ^ m * r j) := mul_le_mul_of_nonneg_left ih hs
      _ = s₁ ^ m * s₁ * r j := by ring

/-- the radius `s₃ = (3 + s₂)/4` on which the increments are controlled -/
def lmS3 (s₂ : ℝ) : ℝ := (3 + s₂) / 4

/-- **The GFF input of MQ Prop 4.3** (MQ l. 693–700, Lemma 4.4, Remark eq. `(zero-boundary)`;
LM Lemma 2.1 at the nested scales): increments `d_j` (MQ's `𝔥̃`, scaled by `r_j`) of the harmonic
parts, harmonic on `B_{s₃}` with oscillation `≤ W_j`, where `W_j ≥ 0` are adapted to a filtration
(LM's `𝓕_{r_j}`), `W_{j+1}` is independent of `𝓕_{r_j}`, and `E e^{W_j} ≤ A`. -/
def LMIncrLeaf (s₁ s₂ : ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ r : ℕ → ℝ, (∀ k, 0 < r k) → Antitone r →
      (∀ k, r (k + 1) / r k ≤ s₁) →
      ∃ (F : ℕ → MeasurableSpace Ω) (W : ℕ → Ω → ℝ), Monotone F ∧ (∀ j, F j ≤ mΩ) ∧
        (∀ j ω, 0 ≤ W j ω) ∧ (∀ j, Measurable[F j] (W j)) ∧
        (∀ j, Indep (MeasurableSpace.comap (W (j + 1)) inferInstance) (F j) P) ∧
        (∀ j, ∫⁻ ω, ENNReal.ofReal (Real.exp (W j ω)) ∂P ≤ ENNReal.ofReal A) ∧
        ∀ hh0 hz G : ℕ → Ω → DistC, (∀ k, IsLMRep P h (r k) (hh0 k) (hz k) (G k)) →
          ∀ k, ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, HarmonicOnNhd g (ball (0 : ℂ) 1) ∧
            (∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) (G k ω) φ = ∫ x, g x * φ x) ∧
            ∃ d : ℕ → ℂ → ℝ, (∀ j ≤ k, HarmonicOnNhd (d j) (ball (0 : ℂ) (lmS3 s₂)) ∧
              ∀ y ∈ ball (0 : ℂ) (lmS3 s₂), |d j y - d j 0| ≤ W j ω) ∧
            ∀ u ∈ ball (0 : ℂ) ((1 + s₂) / 2),
              g u - circleAvg (lmScaled h (r k) ω) 1 0 =
                ∑ j ∈ range (k + 1), (d j ((r k / r j : ℝ) • u) - d j 0)

/-- **`LMScaleDomLeaf` from the increment input** (MQ l. 677–700): the oscillation of the
scaled harmonic part at a bad scale is at most `C ∑_{j ≤ k} s₁^{k-j} W_j`. -/
theorem lmScaleDomLeaf_of_incr {s₁ s₂ : ℝ} (hs₁0 : 0 < s₁) (hs₁₂ : s₁ < s₂) (hs₂ : s₂ < 1)
    (hI : LMIncrLeaf s₁ s₂) : LMScaleDomLeaf s₁ s₂ := by
  obtain ⟨A, hA0, HI⟩ := hI
  set ρ₂ := (1 + s₂) / 2 with hρ₂
  have hρs : ρ₂ < lmS3 s₂ := by unfold lmS3; linarith
  have hρ0 : 0 < ρ₂ := by linarith
  set C := max 1 (8 * ρ₂ / (lmS3 s₂ - ρ₂))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC2 : 8 * ρ₂ / (lmS3 s₂ - ρ₂) ≤ C := le_max_right _ _
  have hδe : lmδ s₂ = (1 - s₂) / 8 := by unfold lmδ; rw [abs_of_pos (by linarith)]
  have hδ : 0 < lmδ s₂ := by rw [hδe]; linarith
  have hρδ : ρ₂ * 1 + lmδ s₂ < 1 := by rw [hδe]; linarith
  have hIp := GM.integral_radProf_pos hδ
  refine ⟨C, s₁, A, by linarith, hs₁0.le, by linarith, hA0, ?_⟩
  intro Ω _ P _ h hh r hr0 hrA hrs
  obtain ⟨F, W, hF, hFle, hW0, hWm, hWi, hA, hdec⟩ := HI P h hh r hr0 hrA hrs
  refine ⟨F, W, hF, hFle, hW0, hWm, hWi, hA, fun hh0 hz G hrep k _ M => ?_⟩
  filter_upwards [hdec hh0 hz G hrep k] with ω ⟨g, hg, hrepg, d, hd, hsum⟩ hbad
  -- a bad centre `u`
  simp only [lmGood, GM.goodD, Set.mem_ofPred_eq, not_forall, not_le] at hbad
  obtain ⟨u, -, hu, hlt⟩ := hbad
  rw [mul_one] at hu
  have hB : closedBall u (lmδ s₂) ⊆ ((ballO 0 1 : TopologicalSpace.Opens ℂ) : Set ℂ) :=
    GM.closedBall_sub_of_mem (by simpa using hρδ) hu
  rw [GM.pair_addConst_radBump (U := ballO 0 1) hg hrepg hδ hB, abs_mul,
    abs_of_pos hIp] at hlt
  have hM : M < |g u - circleAvg (lmScaled h (r k) ω) 1 0| :=
    lt_of_mul_lt_mul_right hlt hIp.le
  refine hM.trans_le ?_
  rw [hsum u hu, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  obtain ⟨hdh, hdb⟩ := hd j hjk
  have hun : ‖u‖ < ρ₂ := by simpa using hu
  have hrat : r k / r j ≤ s₁ ^ (k - j) := by
    have := ratio_le_pow hr0 hrs j (k - j)
    rwa [Nat.add_sub_cancel' hjk] at this
  have hrat0 : 0 < r k / r j := div_pos (hr0 k) (hr0 j)
  have hnorm : ‖(r k / r j : ℝ) • u‖ ≤ s₁ ^ (k - j) * ρ₂ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrat0]
    exact mul_le_mul hrat hun.le (norm_nonneg _) (pow_nonneg hs₁0.le _)
  have hW := hW0 j ω
  rcases Nat.eq_zero_or_pos (k - j) with h0 | hpos
  · -- `j = k`: the increment itself
    have hkj : k = j := by omega
    subst hkj
    rw [div_self (hr0 k).ne', one_smul, h0, pow_zero, one_mul]
    exact (hdb u (mem_ball_zero_iff.2 (hun.trans hρs))).trans (le_mul_of_one_le_left hW hC1)
  · -- `j < k`: geometric decay of the outer increment
    have hp1 : s₁ ^ (k - j) ≤ 1 := pow_le_one₀ hs₁0.le (by linarith)
    have hnorm' : ‖(r k / r j : ℝ) • u‖ ≤ ρ₂ := hnorm.trans (by nlinarith)
    refine (harm_decay hρs hW hdh hdb hnorm').trans ?_
    have hden : 0 < lmS3 s₂ - ρ₂ := by linarith
    calc 8 * W j ω * ‖(r k / r j : ℝ) • u‖ / (lmS3 s₂ - ρ₂)
        ≤ 8 * W j ω * (s₁ ^ (k - j) * ρ₂) / (lmS3 s₂ - ρ₂) := by
          gcongr
      _ = 8 * ρ₂ / (lmS3 s₂ - ρ₂) * (s₁ ^ (k - j) * W j ω) := by ring
      _ ≤ C * (s₁ ^ (k - j) * W j ω) :=
          mul_le_mul_of_nonneg_right hC2 (mul_nonneg (pow_nonneg hs₁0.le _) hW)
      _ = C * (s₁ ^ (k - j) * W j ω) := rfl

/-- **LM Lemma 3.1 (1)** (`N = 0`) from the increment input `LMIncrLeaf`. -/
theorem lmLem3_1a_of_incr
    (hI : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → LMIncrLeaf s₁ s₂) : LMLem3_1a :=
  lmLem3_1a_of_dom fun s₁ s₂ h1 h2 h3 => lmScaleDomLeaf_of_incr h1 h2 h3 (hI s₁ s₂ h1 h2 h3)

end LQGMetric.LM
