/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.RegularityDet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Regularity
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Setup
import LatticeProb.Bonanno.LQGMetric.Metric.LengthSpace

/-!
# Deterministic consequences of `ℰ_𝕣`: GM.S4.11 (ii) and GM (4.36) (= GM.S4.3)

Source: GM (arXiv:1905.00383v3) `uniqueness-final.tex` l. 2005–2010: "The significance of the value
`K` is that condition 2 (comparison of balls) in the definition of `ℰ_𝕣` implies that
`s_{K+1} ≤ τ_{2ℓ𝕣}` on `ℰ_𝕣`" (4.36); with the time unit `𝔲 = τ_{ℓ𝕣}(𝕫)` of decision D16 /
D-B1 (`decisions/DEC-B.md` (a), DV-B12) this needs the comparison `𝔲 ≤ c₂ 𝔠_𝕣e^{ξh_𝕣(𝕫)}`,
`c₂ = (ℓ/a + 1)e^{ξ/a}`, which is GM.S4.11 (ii) of DEC-B ("chain of `⌈ℓ/a⌉` steps of length `≤ a𝕣`
on a ray, condition 3 upper bound, condition 4"). We follow DEC-B's argument:

* `gm_tauR_le_dist`: `τ_R(z) ≤ D(z,w)` whenever `|w − z| ≥ R` (`w ∈ 𝓑^•_s ⊄ B_R(z)` for
  `s > D(z,w)`);
* `gm_dist_le_of_regC3`: one step, `D(u,v) ≤ 𝔠_𝕣e^{ξh_𝕣(0)}` for `u ≠ v` in `B_{4ℓ𝕣}(𝕣V)` with
  `|u−v| ≤ a𝕣` (condition 3 upper bound and `D ≤ D(·,·;B)`);
* `gm_S4_11_ii`: `τ_{ℓ𝕣}(𝕫) ≤ (ℓ/a + 1) e^{ξ/a} 𝔠_𝕣 e^{ξh_𝕣(𝕫)}` for `𝕫 ∈ 𝕣U` (conditions 3, 4;
  condition 4 is read through the continuous circle-average process `H` (D60), so the lemma
  assumes `H_𝕣(0) = h_𝕣(0)` and `H_𝕣(𝕫) = h_𝕣(𝕫)` at `ω`, which hold a.s. for each fixed `𝕫`);
* `gm_S4_3`: `s_k ≤ τ_{2ℓ𝕣}(𝕫)` whenever `k ε^β ≤ a/c₂` (condition 2); in particular for
  `k = K + 1 = ⌊(a/c₂)ε^{-β}⌋` (`gm_S4_3_K`, DEC-B's `K := ⌊(a/c₂)ε^{-β}⌋ − 1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

section Det
variable {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω}
  {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ} {R : RegPar} {𝕣 a : ℝ}

omit [MeasurableSpace Ω] in
/-- `τ_R(z) ≤ D_h(z, w)` for every `w ∉ B_R(z)` -/
theorem gm_tauR_le_dist {z w : ℂ} {Rad : ℝ} (hw : Rad ≤ ‖w - z‖) (ω : Ω) :
    tauR D h z Rad ω ≤ (D (h ω)).1 (z, w) := by
  refine le_of_forall_gt_imp_ge_of_dense fun s hs => ?_
  have hD0 : 0 ≤ (D (h ω)).1 (z, w) := by
    have := (D (h ω)).2.triangle z w z
    rw [(D (h ω)).2.self_eq_zero, (D (h ω)).2.symm w z] at this
    linarith
  have hmem : s ∈ {s | 0 < s ∧ ¬ filledBall (D (h ω)) z s ⊆ Metric.ball z Rad} := by
    refine ⟨lt_of_le_of_lt hD0 hs, fun hsub => ?_⟩
    have hw' : w ∈ filledBall (D (h ω)) z s :=
      Or.inl (subset_closure (show w ∈ ballM _ z s from hs))
    have := hsub hw'
    rw [Metric.mem_ball, dist_eq_norm] at this
    linarith
  exact csInf_le ⟨0, fun _ hx => hx.1.le⟩ hmem

omit [MeasurableSpace Ω] in
/-- one step of the chain: on condition 3, `D_h(u,v) ≤ 𝔠_𝕣e^{ξh_𝕣(0)} |(u−v)/𝕣|^χ` for distinct
`u, v ∈ B_{4ℓ𝕣}(𝕣V)` with `|u − v| ≤ a𝕣` -/
theorem gm_dist_le_of_regC3 {ω : Ω} (hω : ω ∈ regC3 D h R 𝕣 a)
    (hsf : 0 < scaleFac R.ξ R.c (h ω) 𝕣 0) {u v : ℂ} (hu : u ∈ regRegion R 𝕣)
    (hv : v ∈ regRegion R 𝕣) (huv : ‖u - v‖ ≤ a * 𝕣) (hne : u ≠ v) :
    (D (h ω)).1 (u, v) ≤ scaleFac R.ξ R.c (h ω) 𝕣 0 * ‖(u - v) / 𝕣‖ ^ R.χ := by
  have H := (hω u hu v hv huv).2 hne
  have hE : ENNReal.ofReal ((D (h ω)).1 (u, v)) ≤
      (D (h ω)).internal (Metric.ball u (2 * ‖u - v‖)) u v := by
    have := MetricGeometry.edist_le_internalEDist (X := (D (h ω)).Space)
      ((D (h ω)).pt '' Metric.ball u (2 * ‖u - v‖)) ((D (h ω)).pt u) ((D (h ω)).pt v)
    rw [edist_dist] at this
    exact this
  have H2 : ENNReal.ofReal ((scaleFac R.ξ R.c (h ω) 𝕣 0)⁻¹ * (D (h ω)).1 (u, v)) ≤
      ENNReal.ofReal (‖(u - v) / 𝕣‖ ^ R.χ) := by
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hsf.le)]
    exact (mul_le_mul (le_refl _) hE bot_le bot_le).trans H
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at H2
  rw [inv_mul_le_iff₀ hsf] at H2
  exact H2

omit [MeasurableSpace Ω] in
/-- the chain of DEC-B S4.11 (ii): on condition 3, for `𝕫 ∈ 𝕣V` and `n ≥ ℓ/a`,
`D_h(𝕫, 𝕫 + ℓ𝕣) ≤ n 𝔠_𝕣e^{ξh_𝕣(0)}` (steps `𝕫 + (i/n)ℓ𝕣` of length `ℓ𝕣/n ≤ a𝕣`) -/
theorem gm_chain_dist {ω : Ω} (hω : ω ∈ regC3 D h R 𝕣 a)
    (hsf : 0 < scaleFac R.ξ R.c (h ω) 𝕣 0) (h𝕣 : 0 < 𝕣) (hℓ : 0 < R.ℓ) (ha1 : a < 1)
    (hχ : 0 ≤ R.χ) {𝕫 : ℂ} (h𝕫 : 𝕫 ∈ rScale 𝕣 R.V) {n : ℕ} (hn : R.ℓ / a ≤ n) (ha0 : 0 < a) :
    (D (h ω)).1 (𝕫, 𝕫 + ((R.ℓ * 𝕣 : ℝ) : ℂ)) ≤ n * scaleFac R.ξ R.c (h ω) 𝕣 0 := by
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (div_pos hℓ ha0) hn
  set L := R.ℓ * 𝕣 with hL
  have hLpos : 0 < L := mul_pos hℓ h𝕣
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
      _ < 4 * L := by linarith
  have hstep : ∀ i < n, (D (h ω)).1 (z i, z (i + 1)) ≤ scaleFac R.ξ R.c (h ω) 𝕣 0 := by
    intro i hi
    have hd : ‖z i - z (i + 1)‖ = L / n := by
      rw [hdist]; push_cast
      rw [show (i : ℝ) - (i + 1) = -1 by ring, abs_neg, abs_one, one_mul]
    have hLn : L / n ≤ a * 𝕣 := by
      rw [div_le_iff₀ hnpos, hL]
      have := (div_le_iff₀ ha0).1 hn
      nlinarith
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
/-- **GM.S4.11 (ii)** (DEC-B, `j = 1`): on conditions 3 and 4 of `ℰ_𝕣`, for `𝕫 ∈ 𝕣U ⊂ 𝕣V`,
`τ_{ℓ𝕣}(𝕫) ≤ (ℓ/a + 1) e^{ξ/a} 𝔠_𝕣 e^{ξh_𝕣(𝕫)}` -/
theorem gm_S4_11_ii {ω : Ω} (h3 : ω ∈ regC3 D h R 𝕣 a) (h4 : ω ∈ regC4 H R 𝕣 a)
    (hc : 0 < R.c 𝕣) (hξ : 0 ≤ R.ξ) (h𝕣 : 0 < 𝕣) (hℓ : 0 < R.ℓ) (ha0 : 0 < a) (ha1 : a < 1)
    (hχ : 0 ≤ R.χ) (hUV : R.U ⊆ R.V) {𝕫 : ℂ} (h𝕫 : 𝕫 ∈ rScale 𝕣 R.U)
    (hH0 : H 𝕣 0 ω = circleAvg (h ω) 𝕣 0) (hH𝕫 : H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫) :
    tauR D h 𝕫 (R.ℓ * 𝕣) ω ≤
      (R.ℓ / a + 1) * Real.exp (R.ξ / a) * scaleFac R.ξ R.c (h ω) 𝕣 𝕫 := by
  have h𝕫V : 𝕫 ∈ rScale 𝕣 R.V := image_mono hUV h𝕫
  have hsf : 0 < scaleFac R.ξ R.c (h ω) 𝕣 0 := mul_pos hc (Real.exp_pos _)
  set n := ⌈R.ℓ / a⌉₊ with hn
  have hn1 : R.ℓ / a ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) ≤ R.ℓ / a + 1 := (Nat.ceil_lt_add_one (div_pos hℓ ha0).le).le
  have hτ := gm_tauR_le_dist (D := D) (h := h) (z := 𝕫) (w := 𝕫 + ((R.ℓ * 𝕣 : ℝ) : ℂ))
    (Rad := R.ℓ * 𝕣) (by simp [abs_of_pos hℓ, abs_of_pos h𝕣]) ω
  have hch := gm_chain_dist h3 hsf h𝕣 hℓ ha1 hχ h𝕫V hn1 ha0
  have hsf0 : scaleFac R.ξ R.c (h ω) 𝕣 0 ≤ Real.exp (R.ξ / a) * scaleFac R.ξ R.c (h ω) 𝕣 𝕫 := by
    have hz := h4 𝕫 h𝕫V
    rw [hH0, hH𝕫] at hz
    have : circleAvg (h ω) 𝕣 0 ≤ circleAvg (h ω) 𝕣 𝕫 + a⁻¹ := by
      have := (abs_le.1 hz).1; linarith
    simp only [scaleFac]
    rw [mul_left_comm, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc.le
    rw [div_eq_mul_inv]
    nlinarith
  calc tauR D h 𝕫 (R.ℓ * 𝕣) ω ≤ n * scaleFac R.ξ R.c (h ω) 𝕣 0 := hτ.trans hch
    _ ≤ (R.ℓ / a + 1) * (Real.exp (R.ξ / a) * scaleFac R.ξ R.c (h ω) 𝕣 𝕫) :=
      mul_le_mul hn2 hsf0 hsf.le (by positivity)
    _ = _ := by ring

/-- DEC-B's constant `c₂ := (ℓ/a + 1) e^{ξ/a}` -/
def regC2const (R : RegPar) (a : ℝ) : ℝ := (R.ℓ / a + 1) * Real.exp (R.ξ / a)

/-- **GM (4.36)** (`s_{K+1} ≤ τ_{2ℓ𝕣}` on `ℰ_𝕣`, l. 2008–2010), in the form of D16 / DEC-B:
on `ℰ_𝕣`, for `𝕫 ∈ 𝕣U`, every `k` with `k ε^β ≤ a/c₂` has `s_k ≤ τ_{2ℓ𝕣}(𝕫)` -/
theorem gm_S4_3 {ω : Ω} (hω : ω ∈ regEvent D P h H R 𝕣 a)
    (hc : 0 < R.c 𝕣) (hξ : 0 ≤ R.ξ) (h𝕣 : 0 < 𝕣) (hℓ : 0 < R.ℓ) (ha0 : 0 < a) (ha1 : a < 1)
    (hχ : 0 ≤ R.χ) (hUV : R.U ⊆ R.V) {𝕫 : ℂ} (h𝕫 : 𝕫 ∈ rScale 𝕣 R.U)
    (hH0 : H 𝕣 0 ω = circleAvg (h ω) 𝕣 0) (hH𝕫 : H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫) {ε β : ℝ} {k : ℕ}
    (hk : k * ε ^ β ≤ a / regC2const R a) :
    s4S D h 𝕫 R.ℓ 𝕣 ε β k ω ≤ tauR D h 𝕫 (2 * (R.ℓ * 𝕣)) ω := by
  obtain ⟨_, h2, h3, h4, _⟩ := gm_regEvent_mem.1 hω
  have hu := gm_S4_11_ii h3 h4 hc hξ h𝕣 hℓ ha0 ha1 hχ hUV h𝕫 hH0 hH𝕫
  have h𝕫R : 𝕫 ∈ regRegion R 𝕣 :=
    Metric.self_subset_thickening (by positivity) _ (image_mono hUV h𝕫)
  have h2z := (h2 𝕫 h𝕫R).2
  rw [hH𝕫] at h2z
  have hc2 : 0 < regC2const R a := by unfold regC2const; positivity
  set u := tauR D h 𝕫 (R.ℓ * 𝕣) ω with hu_def
  have hu0 : 0 ≤ u := Real.sInf_nonneg (fun _ hx => hx.1.le)
  set sf := scaleFac R.ξ R.c (h ω) 𝕣 𝕫
  have hmax : a * sf ≤ tauR D h 𝕫 (2 * (R.ℓ * 𝕣)) ω - u :=
    (mul_le_mul_of_nonneg_left (le_max_left _ _) ha0.le).trans (h2z.trans (min_le_left _ _))
  have hku : (k * ε ^ β) * u ≤ a * sf := by
    calc (k * ε ^ β) * u ≤ (a / regC2const R a) * (regC2const R a * sf) := by
          refine mul_le_mul hk ?_ hu0 (by positivity)
          simpa [regC2const] using hu
      _ = a * sf := by field_simp
  simp only [s4S, s4Unit]
  rw [← hu_def]
  nlinarith

end Det

end LQGMetric.GM
