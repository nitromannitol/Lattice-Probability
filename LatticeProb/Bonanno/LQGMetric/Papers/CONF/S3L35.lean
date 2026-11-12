/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L35 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFResults

/-!
# CONF Lemma 3.5 from CONF Lemma 3.4 (union bound over the grid)

Gwynne–Miller, *Confluence of geodesics in Liouville quantum gravity for γ ∈ (0,2)*
(arXiv:1905.00381), `literature/src/1905.00381/confluence-final.tex`:

* `CONFLem3_4` : **CONF Lemma 3.4** (`lem-clsce-iterate`, C:1262–1268), verbatim: for each
  `q > 0` there are parameters `c, δ ∈ (0,1)`, `A > 0`, `η > 0` such that, uniformly over `𝕣 > 0`
  and `z ∈ ℂ`, `P[ρ^{⌊η log C⌋}_𝕣(z) > C𝕣] = O_C(C^{−q})` as `C → ∞`. (Open here; its proof,
  C:1269–1271, is from Lemma 3.2 and Lemma 2.12; see `blueprint/CONF3-STATUS.md`.)
* `confLem3_5_of_3_4` : **CONF Lemma 3.5** (`lem-clsce-all`, C:1276–1282), in the Blueprint form
  `CONFLem3_5At` (centre `𝕫`, uniform in `𝕣` and `𝕫`), from Lemma 3.4.

Proof (C:1284–1285): Lemma 3.4 at scale `ε𝕣` and a union bound over the `O_ε(ε^{−2})` points of
`(ε𝕣/4)ℤ² ∩ B_{ε𝕣}(𝕣K + 𝕫)`. CONF writes "with `C = ε^{−3/2}` and `q = 6`"; this gives neither the
radius `ε^{1/2}𝕣` nor the rate `ε²`. We use `C = ε^{−1/2}` (so `C·ε𝕣 = ε^{1/2}𝕣`) and `q = 8`
(`O(ε^{−2})·ε⁴ = O(ε²)`), and `η_{3.5} = η_{3.4}/2` since `log ε^{−1/2} = ½ log ε^{−1}`
(proposed deviation DV-CONF-35). The points are counted in a box of `ℤ²` indices.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **CONF Lemma 3.4** (`lem-clsce-iterate`, C:1262–1268), for the metric `D`: "For each `q > 0`,
we can find parameters `c, δ ∈ (0,1)` and `A > 0` and another parameter `η > 0`, all depending
on `q`, such that … uniformly over all `𝕣 > 0` and `z ∈ ℂ`,
`P[ρ^{⌊η log C⌋}_𝕣(z) > C𝕣] = O_C(C^{−q})` as `C → ∞`." -/
def CONFLem3_4 (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) : Prop :=
  ∀ q : ℝ, 0 < q → ∃ p : CONFParams, p.Valid ∧ p.δ < 1 / 8 ∧ ∃ C₁ M : ℝ, 1 ≤ C₁ ∧ 0 < M ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ∀ (z : ℂ) (R : ℝ), 0 < R → ∀ C : ℝ, C₁ ≤ C →
        P {ω | ENNReal.ofReal (C * R) <
          confRho (xiGamma γ) c D P h p R z ⌊p.η * Real.log C⌋₊ ω} ≤
            ENNReal.ofReal (M * C ^ (-q))

/-- `ρ^n` depends on the parameters only through `c, δ, A` (not on `η`). -/
theorem confRho_congr_params {Ω : Type} [MeasurableSpace Ω] (ξ : ℝ) (cc : ℝ → ℝ)
    (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC) {p p' : CONFParams}
    (hc : p.c = p'.c) (hδ : p.δ = p'.δ) (hA : p.A = p'.A) (R : ℝ) (z : ℂ) :
    ∀ n, confRho ξ cc D P h p R z n = confRho ξ cc D P h p' R z n := by
  have hE : ∀ r, confE ξ cc D P h p r z = confE ξ cc D P h p' r z := by
    intro r; simp only [confE, confEU, hc, hδ, hA]
  intro n
  induction n with
  | zero => rfl
  | succ n ih => funext ω; simp only [confRho, ih, hE]

/-- the index box `[⌊x/m⌋ − N, ⌊x/m⌋ + N] × [⌊y/m⌋ − N, ⌊y/m⌋ + N]`, `N = ⌈ρ/m⌉`, `z₀ = x + iy` -/
def gridBox (m ρ : ℝ) (z₀ : ℂ) : Finset (ℤ × ℤ) :=
  Finset.Icc (⌊z₀.re / m⌋ - ⌈ρ / m⌉₊) (⌊z₀.re / m⌋ + ⌈ρ / m⌉₊) ×ˢ
    Finset.Icc (⌊z₀.im / m⌋ - ⌈ρ / m⌉₊) (⌊z₀.im / m⌋ + ⌈ρ / m⌉₊)

theorem gridBox_card (m ρ : ℝ) (z₀ : ℂ) :
    (gridBox m ρ z₀).card = (2 * ⌈ρ / m⌉₊ + 1) ^ 2 := by
  simp only [gridBox, Finset.card_product, Int.card_Icc]
  have : ∀ a : ℤ, a + ⌈ρ / m⌉₊ + 1 - (a - ⌈ρ / m⌉₊) = ((2 * ⌈ρ / m⌉₊ + 1 : ℕ) : ℤ) := by
    intro a; push_cast; ring
  rw [this, this, Int.toNat_natCast, sq]

/-- one coordinate: `|a m − x| < ρ` puts `a` in `[⌊x/m⌋ − N, ⌊x/m⌋ + N]` -/
theorem mem_Icc_of_abs_lt {m ρ x : ℝ} (hm : 0 < m) {a : ℤ} (ha : |a * m - x| < ρ) :
    a ∈ Finset.Icc (⌊x / m⌋ - ⌈ρ / m⌉₊) (⌊x / m⌋ + ⌈ρ / m⌉₊) := by
  have h1 : |(a : ℝ) - x / m| < ρ / m := by
    rw [lt_div_iff₀ hm, ← abs_of_pos hm, ← abs_mul, abs_of_pos hm, sub_mul,
      div_mul_cancel₀ _ hm.ne']
    exact ha
  rw [abs_lt] at h1
  have hf := Int.floor_le (x / m)
  have hf' := Int.lt_floor_add_one (x / m)
  have hc := Nat.le_ceil (ρ / m)
  rw [Finset.mem_Icc]
  constructor
  · have : ((⌊x / m⌋ - ⌈ρ / m⌉₊ : ℤ) : ℝ) < (a : ℝ) + 1 := by push_cast; linarith
    exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)
  · have : (a : ℝ) < ((⌊x / m⌋ + ⌈ρ / m⌉₊ : ℤ) : ℝ) + 1 := by push_cast; linarith
    exact Int.lt_add_one_iff.mp (by exact_mod_cast this)

theorem grid_ball_subset {m ρ : ℝ} (hm : 0 < m) (z₀ : ℂ) :
    gridPts m ∩ ball z₀ ρ ⊆
      (fun k : ℤ × ℤ => (⟨k.1 * m, k.2 * m⟩ : ℂ)) '' ↑(gridBox m ρ z₀) := by
  rintro w ⟨⟨a, b, rfl⟩, hw⟩
  rw [mem_ball, dist_eq_norm] at hw
  refine ⟨(a, b), ?_, rfl⟩
  simp only [gridBox, Finset.coe_product, Set.mem_prod, Finset.mem_coe]
  refine ⟨mem_Icc_of_abs_lt hm ?_, mem_Icc_of_abs_lt hm ?_⟩
  · have := Complex.abs_re_le_norm ((⟨a * m, b * m⟩ : ℂ) - z₀)
    simp only [Complex.sub_re] at this; linarith
  · have := Complex.abs_im_le_norm ((⟨a * m, b * m⟩ : ℂ) - z₀)
    simp only [Complex.sub_im] at this; linarith

/-- the grid points near `𝕣K + 𝕫` lie in `B_{𝕣(B+1)}(𝕫)` when `K ⊆ closedBall 0 B`, `ε ≤ 1` -/
theorem thickening_subset_ball {K : Set ℂ} {B : ℝ} (hK : K ⊆ closedBall 0 B) (z₀ : ℂ) {R ε : ℝ}
    (hR : 0 < R) (hε : ε ≤ 1) :
    thickening (ε * R) ((fun x => R * x + z₀) '' K) ⊆ ball z₀ (R * (B + 1)) := by
  intro w hw
  obtain ⟨y, ⟨x, hx, rfl⟩, hd⟩ := mem_thickening_iff.mp hw
  have hx' : ‖x‖ ≤ B := by simpa using hK hx
  rw [mem_ball]
  calc dist w z₀ ≤ dist w (R * x + z₀) + dist (R * x + z₀) z₀ := dist_triangle _ _ _
    _ < ε * R + R * B := by
        refine add_lt_add_of_lt_of_le hd ?_
        rw [dist_eq_norm, add_sub_cancel_right, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hR.le]
        exact mul_le_mul_of_nonneg_left hx' hR.le
    _ ≤ R * (B + 1) := by nlinarith

/-- `((√ε)⁻¹)^{−8} = ε⁴` -/
theorem inv_sqrt_rpow_neg_eight {ε : ℝ} (hε : 0 ≤ ε) : ((√ε)⁻¹) ^ (-(8 : ℝ)) = ε ^ 4 := by
  rw [Real.inv_rpow (Real.sqrt_nonneg _), Real.rpow_neg (Real.sqrt_nonneg _), inv_inv,
    show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, Real.sq_sqrt hε]

/-- **CONF Lemma 3.5** (C:1276–1282) from **CONF Lemma 3.4** (C:1262), proof C:1284–1285. -/
theorem confLem3_5_of_3_4 {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (H : CONFLem3_4 γ D c) :
    ∃ p : CONFParams, p.Valid ∧ p.δ < 1 / 8 ∧ CONFLem3_5At γ D c p := by
  obtain ⟨p, ⟨h1, h2, h3, h4, h5, h6⟩, hδ8, C₁, M, hC₁, hM, hP⟩ := H 8 (by norm_num)
  let p₅ : CONFParams := ⟨p.c, p.δ, p.A, p.η / 2⟩
  refine ⟨p₅, ⟨h1, h2, h3, h4, h5, by simp only [p₅]; linarith⟩, hδ8, ?_⟩
  intro K hK
  obtain ⟨B₀, hB₀⟩ := hK.isBounded.subset_closedBall 0
  set B := max B₀ 0 with hBdef
  have hB : 0 ≤ B := le_max_right _ _
  have hKB : K ⊆ closedBall 0 B := hB₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  refine ⟨M * (8 * B + 11) ^ 2, ((C₁ ^ 2)⁻¹), by positivity, by positivity, ?_⟩
  intro Ω _ P _ h hh z₀ R hR ε hε
  obtain ⟨hε0, hε1⟩ := hε
  have hC1sq : 1 ≤ C₁ ^ 2 := by nlinarith
  have hεle1 : ε ≤ 1 := (hε1.trans_le (inv_le_one_of_one_le₀ hC1sq)).le
  set C : ℝ := (√ε)⁻¹ with hCdef
  have hsq : 0 < √ε := Real.sqrt_pos.mpr hε0
  have hCC : C₁ ≤ C := by
    rw [hCdef, le_inv_comm₀ (by linarith) hsq]
    rw [show C₁⁻¹ = √((C₁ ^ 2)⁻¹) by rw [Real.sqrt_inv, Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt hε1.le
  have hm : 0 < ε * R / 4 := by positivity
  -- each grid point is bad with probability at most `M ε⁴`
  have hpt : ∀ z : ℂ, P {ω | ENNReal.ofReal (ε ^ (1 / 2 : ℝ) * R) <
      confRho (xiGamma γ) c D P h p₅ (ε * R) z (confN p₅ ε) ω} ≤ ENNReal.ofReal (M * ε ^ 4) := by
    intro z
    have hrho := confRho_congr_params (xiGamma γ) c D P h (p := p₅) (p' := p) rfl rfl rfl
      (ε * R) z
    have hidx : confN p₅ ε = ⌊p.η * Real.log C⌋₊ := by
      simp only [confN, p₅, hCdef, Real.log_inv, Real.log_sqrt hε0.le]
      congr 1; ring
    have hrad : ε ^ (1 / 2 : ℝ) * R = C * (ε * R) := by
      rw [← Real.sqrt_eq_rpow, hCdef]
      field_simp
      rw [Real.sq_sqrt hε0.le]
    have := hP P h hh z (ε * R) (by positivity) C hCC
    rw [inv_sqrt_rpow_neg_eight hε0.le] at this
    simpa only [hidx, hrad, hrho] using this
  set I := gridBox (ε * R / 4) (R * (B + 1)) z₀
  have hsub : {ω | ∃ z ∈ gridPts (ε * R / 4) ∩ thickening (ε * R) ((fun x => R * x + z₀) '' K),
      ENNReal.ofReal (ε ^ (1 / 2 : ℝ) * R) <
        confRho (xiGamma γ) c D P h p₅ (ε * R) z (confN p₅ ε) ω} ⊆
      ⋃ k ∈ I, {ω | ENNReal.ofReal (ε ^ (1 / 2 : ℝ) * R) <
        confRho (xiGamma γ) c D P h p₅ (ε * R) (⟨k.1 * (ε * R / 4), k.2 * (ε * R / 4)⟩ : ℂ)
          (confN p₅ ε) ω} := by
    rintro ω ⟨z, ⟨hzg, hzt⟩, hz⟩
    obtain ⟨k, hk, rfl⟩ := grid_ball_subset hm z₀
      ⟨hzg, thickening_subset_ball hKB z₀ hR hεle1 hzt⟩
    exact mem_biUnion (x := k) hk hz
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le I _).trans ?_)
  refine (Finset.sum_le_sum fun k _ => hpt _).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [gridBox_card]
  set N := ⌈R * (B + 1) / (ε * R / 4)⌉₊
  have ht : R * (B + 1) / (ε * R / 4) = 4 * (B + 1) / ε := by field_simp
  have hN : (N : ℝ) ≤ 4 * (B + 1) / ε + 1 := by
    rw [← ht]; exact (Nat.ceil_lt_add_one (by positivity)).le
  have hNε : (2 * (N : ℝ) + 1) * ε ≤ 8 * B + 11 := by
    have : (N : ℝ) * ε ≤ 4 * (B + 1) + ε := by
      have := mul_le_mul_of_nonneg_right hN hε0.le
      rwa [add_mul, div_mul_cancel₀ _ hε0.ne', one_mul] at this
    nlinarith
  push_cast
  have h0 : 0 ≤ (2 * (N : ℝ) + 1) * ε := by positivity
  calc ((2 * (N : ℝ) + 1) ^ 2) * (M * ε ^ 4) = M * ((2 * (N : ℝ) + 1) * ε) ^ 2 * ε ^ 2 := by ring
    _ ≤ M * (8 * B + 11) ^ 2 * ε ^ 2 := by gcongr

end LQGMetric.CONF
