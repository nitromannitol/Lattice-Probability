/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412bScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412Step12
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityDet

/-!
# GM L4.15 Step 1: the time gap `t_k − s_k` dominates `N^{-β}𝔠_{ℓ𝕣}e^{ξh_{ℓ𝕣}(𝕫)}` on `ℰ_𝕣`

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, L4.15 Step 1 (l. 2125–2128):
Theorem 3.9 is applied with `τ = s_k`, whose horizon `τ + N^{-β}𝔠_{ℓ𝕣}e^{ξh_{ℓ𝕣}(𝕫)}` must not
exceed `t_k = s_k + ε^{2β}τ_{ℓ𝕣}` (D16) — GM: "if `β` is chosen sufficiently small, in a manner
depending only on `ω` and `D`". GM leave the comparison of the normalizations implicit
(Remark 4.10 / "by condition 2"); the write-up below uses only conditions 2 and 3 of `ℰ_𝕣`
(own elementary argument, proposed DEVIATIONS entry):

* `𝔠_{ℓ𝕣}e^{ξh_{ℓ𝕣}(𝕫)} ≤ a⁻¹(τ_{2ℓ𝕣} − τ_{ℓ𝕣})` (condition 2);
* `τ_{2ℓ𝕣} ≤ D_h(𝕫, 𝕫 + 2ℓ𝕣) ≤ ⌈2ℓ/a⌉ 𝔠_𝕣e^{ξh_𝕣(0)}` (chain of condition 3, as in
  `gm_chain_dist`, with steps `≤ a𝕣`);
* `τ_{ℓ𝕣} ≥ (a/2)^{χ'} 𝔠_𝕣e^{ξh_𝕣(0)}` (lower Hölder bound of condition 3, as in `p412_eq439`).

Hence `𝔠_{ℓ𝕣}e^{ξh_{ℓ𝕣}(𝕫)} ≤ p412bC · τ_{ℓ𝕣}` with `p412bC = (2ℓ/a + 1)/(a (a/2)^{χ'})`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the constant `(2ℓ/a + 1)/(a (a/2)^{χ'})` -/
def p412bC (ℓ a χ' : ℝ) : ℝ := (2 * ℓ / a + 1) / (a * (a / 2) ^ χ')

section Scale
variable {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : MeasureTheory.Measure Ω}
  {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ} {R : RegPar} {𝕣 a : ℝ}

omit [MeasurableSpace Ω] in
/-- the chain of condition 3 for a horizontal segment of length `L < 4ℓ𝕣` from `𝕫 ∈ 𝕣V`:
`D_h(𝕫, 𝕫 + L) ≤ n 𝔠_𝕣e^{ξh_𝕣(0)}` for `n ≥ L/(a𝕣)` (`gm_chain_dist` with `L` for `ℓ𝕣`) -/
theorem p412b_chain_dist {ω : Ω} (hω : ω ∈ regC3 D h R 𝕣 a)
    (hsf : 0 < scaleFac R.ξ R.c (h ω) 𝕣 0) (h𝕣 : 0 < 𝕣) (ha1 : a < 1)
    (hχ : 0 ≤ R.χ) {𝕫 : ℂ} (h𝕫 : 𝕫 ∈ rScale 𝕣 R.V) {L : ℝ} (hLpos : 0 < L)
    (hL4 : L < 4 * (R.ℓ * 𝕣)) {n : ℕ} (hn : L / (a * 𝕣) ≤ n) (ha0 : 0 < a) :
    (D (h ω)).1 (𝕫, 𝕫 + ((L : ℝ) : ℂ)) ≤ n * scaleFac R.ξ R.c (h ω) 𝕣 0 := by
  have har : 0 < a * 𝕣 := mul_pos ha0 h𝕣
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (div_pos hLpos har) hn
  set z : ℕ → ℂ := fun i => 𝕫 + ((i * L / n : ℝ) : ℂ) with hz
  have hdist : ∀ i j : ℕ, ‖z i - z j‖ = |((i : ℝ) - j)| * L / n := by
    intro i j
    simp only [hz, add_sub_add_left_eq_sub, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    rw [show (i : ℝ) * L / n - j * L / n = ((i : ℝ) - j) * (L / n) by ring, abs_mul,
      abs_of_pos (div_pos hLpos hnpos)]
    ring
  have hmem : ∀ i ≤ n, z i ∈ regRegion R 𝕣 := by
    intro i hi
    refine Metric.mem_thickening_iff.2 ⟨𝕫, h𝕫, ?_⟩
    rw [dist_eq_norm, show z i - 𝕫 = z i - z 0 by simp [hz]]
    rw [hdist, Nat.cast_zero, sub_zero, abs_of_nonneg (Nat.cast_nonneg _)]
    have : (i : ℝ) ≤ n := by exact_mod_cast hi
    calc (i : ℝ) * L / n ≤ n * L / n := by gcongr
      _ = L := by field_simp
      _ < 4 * (R.ℓ * 𝕣) := hL4
  have hLn : L / n ≤ a * 𝕣 := by
    rw [div_le_iff₀ hnpos]
    have := (div_le_iff₀ har).1 hn
    linarith
  have hstep : ∀ i < n, (D (h ω)).1 (z i, z (i + 1)) ≤ scaleFac R.ξ R.c (h ω) 𝕣 0 := by
    intro i hi
    have hd : ‖z i - z (i + 1)‖ = L / n := by
      rw [hdist]; push_cast
      rw [show (i : ℝ) - (i + 1) = -1 by ring, abs_neg, abs_one, one_mul]
    have hne : z i ≠ z (i + 1) := by
      intro he; rw [he, sub_self, norm_zero] at hd; exact (div_pos hLpos hnpos).ne' hd.symm
    refine (gm_dist_le_of_regC3 hω hsf (hmem i hi.le) (hmem (i + 1) hi) (hd ▸ hLn) hne).trans ?_
    have h1 : ‖(z i - z (i + 1)) / 𝕣‖ ≤ 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣, hd, div_le_one h𝕣]
      nlinarith
    have : ‖(z i - z (i + 1)) / 𝕣‖ ^ R.χ ≤ 1 := Real.rpow_le_one (norm_nonneg _) h1 hχ
    nlinarith
  have hchain : ∀ m ≤ n, (D (h ω)).1 (𝕫, z m) ≤ m * scaleFac R.ξ R.c (h ω) 𝕣 0 := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [hz, (D (h ω)).2.self_eq_zero]
    | succ m ih =>
      intro hm
      have := (D (h ω)).2.triangle 𝕫 (z m) (z (m + 1))
      have := ih (Nat.le_of_succ_le hm)
      have := hstep m hm
      push_cast
      linarith
  have hzn : z n = 𝕫 + ((L : ℝ) : ℂ) := by
    simp only [hz]; congr 2; field_simp
  rw [← hzn]
  exact hchain n le_rfl

omit [MeasurableSpace Ω] in
/-- on condition 3, `τ_{ℓ𝕣}(𝕫) ≥ (a/2)^{χ'} 𝔠_𝕣e^{ξh_𝕣(0)}` for `𝕫 ∈ 𝕣U` (lower Hölder bound on
`∂B_{a𝕣/2}(𝕫)`, as in `p412_eq439`) -/
theorem p412b_tau_ge {ω : Ω} (h3 : ω ∈ regC3 D h R 𝕣 a) (h𝕣 : 0 < 𝕣) (ha0 : 0 < a)
    (haℓ : a ≤ R.ℓ) (hUV : R.U ⊆ R.V) (hc : 0 < R.c 𝕣) {𝕫 : ℂ} (h𝕫 : 𝕫 ∈ rScale 𝕣 R.U)
    (hL : (D (h ω)).IsLength) :
    (a / 2) ^ R.χ' * scaleFac R.ξ R.c (h ω) 𝕣 0 ≤ tauR D h 𝕫 (R.ℓ * 𝕣) ω := by
  have hℓ : 0 < R.ℓ := lt_of_lt_of_le ha0 haℓ
  have hS : 0 < scaleFac R.ξ R.c (h ω) 𝕣 0 := mul_pos hc (Real.exp_pos _)
  have h𝕫V : 𝕫 ∈ rScale 𝕣 R.V := image_mono hUV h𝕫
  have hreg : ∀ x : ℂ, dist x 𝕫 < 4 * (R.ℓ * 𝕣) → x ∈ regRegion R 𝕣 := fun x hx =>
    Metric.mem_thickening_iff.2 ⟨𝕫, h𝕫V, hx⟩
  have h𝕫R : 𝕫 ∈ regRegion R 𝕣 := hreg 𝕫 (by rw [dist_self]; positivity)
  have har : 0 < a * 𝕣 := mul_pos ha0 h𝕣
  have hal : a * 𝕣 ≤ R.ℓ * 𝕣 := mul_le_mul_of_nonneg_right haℓ h𝕣.le
  refine gm_tauR_ge_of_sphere hL (by positivity : 0 < a * 𝕣 / 2) (by linarith) fun w hw => ?_
  have hw' : ‖𝕫 - w‖ = a * 𝕣 / 2 := by rw [← dist_eq_norm, dist_comm]; exact mem_sphere.1 hw
  have := gm_regC3_lower h3 h𝕣 hS h𝕫R (hreg w (by rw [mem_sphere.1 hw]; linarith))
    (by rw [hw']; linarith)
  rwa [hw', show a * 𝕣 / 2 / 𝕣 = a / 2 by field_simp] at this

/-- **GM L4.15 Step 1, normalization**: on `ℰ_𝕣`, for `𝕫 ∈ 𝕣U`,
`𝔠_{ℓ𝕣}e^{ξh_{ℓ𝕣}(𝕫)} ≤ p412bC ℓ a χ' · τ_{ℓ𝕣}(𝕫)`. -/
theorem p412b_scale_le_tau {ω : Ω} (hω : ω ∈ regEvent D P h H R 𝕣 a)
    (h𝕣 : 0 < 𝕣) (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ R.ℓ) (hχ : 0 ≤ R.χ)
    (hUV : R.U ⊆ R.V) (hc : 0 < R.c 𝕣) {𝕫 : ℂ} (h𝕫 : 𝕫 ∈ rScale 𝕣 R.U)
    (hHℓ : H (R.ℓ * 𝕣) 𝕫 ω = circleAvg (h ω) (R.ℓ * 𝕣) 𝕫) (hL : (D (h ω)).IsLength) :
    scaleFac R.ξ R.c (h ω) (R.ℓ * 𝕣) 𝕫 ≤ p412bC R.ℓ a R.χ' * tauR D h 𝕫 (R.ℓ * 𝕣) ω := by
  have hℓ : 0 < R.ℓ := lt_of_lt_of_le ha0 haℓ
  obtain ⟨_, h2, h3, _, _, _, _⟩ := gm_regEvent_mem.1 hω
  set S := scaleFac R.ξ R.c (h ω) 𝕣 0 with hSdef
  have hS : 0 < S := mul_pos hc (Real.exp_pos _)
  have h𝕫V : 𝕫 ∈ rScale 𝕣 R.V := image_mono hUV h𝕫
  have hreg : ∀ x : ℂ, dist x 𝕫 < 4 * (R.ℓ * 𝕣) → x ∈ regRegion R 𝕣 := fun x hx =>
    Metric.mem_thickening_iff.2 ⟨𝕫, h𝕫V, hx⟩
  have h𝕫R : 𝕫 ∈ regRegion R 𝕣 := hreg 𝕫 (by rw [dist_self]; positivity)
  set τ := tauR D h 𝕫 (R.ℓ * 𝕣) ω with hτdef
  have hτ : (a / 2) ^ R.χ' * S ≤ τ := p412b_tau_ge h3 h𝕣 ha0 haℓ hUV hc h𝕫 hL
  have hτ0 : 0 ≤ τ := Real.sInf_nonneg (fun _ hx => hx.1.le)
  -- `τ_{2ℓ𝕣} ≤ ⌈2ℓ/a⌉ S`
  set n := ⌈2 * R.ℓ / a⌉₊ with hn
  have hn1 : 2 * (R.ℓ * 𝕣) / (a * 𝕣) ≤ n := by
    rw [show 2 * (R.ℓ * 𝕣) / (a * 𝕣) = 2 * R.ℓ / a by field_simp]; exact Nat.le_ceil _
  have hn2 : (n : ℝ) ≤ 2 * R.ℓ / a + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hτ2 : tauR D h 𝕫 (2 * (R.ℓ * 𝕣)) ω ≤ n * S := by
    have h1 := gm_tauR_le_dist (D := D) (h := h) (z := 𝕫)
      (w := 𝕫 + (((2 * (R.ℓ * 𝕣)) : ℝ) : ℂ)) (Rad := 2 * (R.ℓ * 𝕣))
      (by simp [abs_of_pos hℓ, abs_of_pos h𝕣]) ω
    exact h1.trans (p412b_chain_dist h3 hS h𝕣 ha1 hχ h𝕫V (by positivity) (by nlinarith [mul_pos hℓ h𝕣])
      hn1 ha0)
  -- condition 2
  have h2z := (h2 𝕫 h𝕫R).2
  rw [hHℓ] at h2z
  have hsc : a * scaleFac R.ξ R.c (h ω) (R.ℓ * 𝕣) 𝕫 ≤ tauR D h 𝕫 (2 * (R.ℓ * 𝕣)) ω - τ :=
    (mul_le_mul_of_nonneg_left (le_max_right _ _) ha0.le).trans (h2z.trans (min_le_left _ _))
  have ha2 : 0 < (a / 2) ^ R.χ' := by positivity
  have hS' : S ≤ τ / (a / 2) ^ R.χ' := by rw [le_div_iff₀ ha2]; linarith
  have key : a * scaleFac R.ξ R.c (h ω) (R.ℓ * 𝕣) 𝕫 ≤ (2 * R.ℓ / a + 1) * (τ / (a / 2) ^ R.χ') :=
    calc a * scaleFac R.ξ R.c (h ω) (R.ℓ * 𝕣) 𝕫 ≤ n * S := by linarith
      _ ≤ (2 * R.ℓ / a + 1) * (τ / (a / 2) ^ R.χ') :=
        mul_le_mul hn2 hS' hS.le (by positivity)
  rw [p412bC, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have : (2 * R.ℓ / a + 1) * (τ / (a / 2) ^ R.χ') * (a / 2) ^ R.χ' = (2 * R.ℓ / a + 1) * τ := by
    field_simp
  nlinarith
end Scale

end LQGMetric.GM
