/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53N4F1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53FN2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53GA1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53UF5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Main

/-!
# DZZ Lemma 5.3 part 1, node 4: the domination of the node-4 proxy at the chain boxes
(P2-DZZ53N4F)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, (eq-M-A-upper-bound-bis)
l. 2453–2456 (the proxy `c_B M̃^η` dominates `μ` on `𝓔₄`) used in node 4, l. 2516–2522.
On `E = l53E4 ∩ cellSizeEvent`, every box `b` of the selected chain `𝒞(ω)` (S5L53L5) for the
region `R'' = cthick(2δ^{C_Mc}) (cthick(8δ^{C_Mc}) l53Region)` satisfies the domination clause of
`L53WData` (S5L53M4) for the node-4 proxy `l53fnM` (S5L53FN2): `dzzMuIn(B(c, r)) ≤ l53fnM b (c, r)`
on the rational balls of `sqBox(c_b, 5 s_b)`.

* `l53n4_sq_sub`: `sqBox(c_b, 5 s_b)` lies within `3 s_𝖢` of `c_𝖢` when `b ⊆ 𝖢`, `s_b ≤ s_𝖢/4`.
* `l53n4_two_pow_le`: `2^{4 n_{ε*} + 12} ≤ e^{L^{0.55}}` for large `L` (own elementary estimate,
  via `four_pow_epsStarN_le`, S3L12S3, and `l53uf_ev_log`, S5L53UF4).
* **`l53n4_dom`**: the domination, from Z3's `l53_domination` (`B := 𝖢`, `j := 4 n_{ε*} + 12`,
  `s := s_b`, `S := sqBox(c_b, 5 s_b)`) and G-G1 `l53_sqBox_five_subset_tildeBox` (S5L53GA1) for
  `ball ⊆ 𝕍°`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- `sqBox(c_b, 5 s_b)` lies within `3 s_𝖢` of the centre of `𝖢 ⊇ b` if `s_b ≤ s_𝖢 / 4`. -/
lemma l53n4_sq_sub {b C : DyBox} (hbC : b.closedBox ⊆ C.closedBox)
    (hbs : b.side ≤ C.side / 4) :
    ∀ z ∈ sqBox b.center (5 * b.side), ‖z - C.center‖ ≤ 3 * C.side := by
  obtain ⟨a1, a2, a3, a4⟩ := corners_of_subset hbC
  have hb0 := DyBox.side_pos' b
  rintro z ⟨hz1, hz2⟩
  have hn := Complex.norm_le_abs_re_add_abs_im (z - C.center)
  rw [Complex.sub_re, Complex.sub_im] at hn
  have e1 : b.center.re = b.j * b.side + b.side / 2 := by simp only [DyBox.center]; ring
  have e2 : b.center.im = b.k * b.side + b.side / 2 := by simp only [DyBox.center]; ring
  have e3 : C.center.re = C.j * C.side + C.side / 2 := by simp only [DyBox.center]; ring
  have e4 : C.center.im = C.k * C.side + C.side / 2 := by simp only [DyBox.center]; ring
  have h1 : |z.re - C.center.re| ≤ 5 * b.side / 2 + C.side / 2 := by
    rw [abs_le] at hz1 ⊢
    constructor <;> nlinarith
  have h2 : |z.im - C.center.im| ≤ 5 * b.side / 2 + C.side / 2 := by
    rw [abs_le] at hz2 ⊢
    constructor <;> nlinarith
  linarith

/-- `2^{4 n_{ε*} + 12} ≤ e^{L^{0.55}}` for large `L = log δ⁻¹` (own elementary estimate). -/
lemma l53n4_two_pow_le (αs : ℝ) (hαs : 0 ≤ αs) :
    ∃ L₀ : ℝ, ∀ δ : ℝ, L₀ ≤ Real.log δ⁻¹ →
      (2 : ℝ) ^ (4 * epsStarN αs δ + 12) ≤ Real.exp (Real.log δ⁻¹ ^ (0.55 : ℝ)) := by
  have ev := ((l53uf_ev_log αs hαs).and ((tendsto_rpow_atTop (show (0 : ℝ) < 0.51 by
    norm_num)).eventually (eventually_ge_atTop (24 : ℝ)))).and (eventually_ge_atTop (1 : ℝ))
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 ev
  refine ⟨L₀, fun δ hδ => ?_⟩
  obtain ⟨⟨⟨hX, -⟩, h24⟩, hL1⟩ := hL₀ _ hδ
  set L := Real.log δ⁻¹ with hL
  set n := epsStarN αs δ with hn
  set X := αs * Real.sqrt L * Real.log L with hXd
  have hX0 : 0 ≤ X := mul_nonneg (mul_nonneg hαs (Real.sqrt_nonneg _)) (Real.log_nonneg hL1)
  have h4 : (4 : ℝ) ^ n ≤ 4 * Real.exp (2 * X) := four_pow_epsStarN_le αs δ hX0
  have e : (2 : ℝ) ^ (4 * n + 12) = 2 ^ 12 * ((4 : ℝ) ^ n) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  have h55 : L ^ (0.51 : ℝ) ≤ L ^ (0.55 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have e16 : Real.exp (16 * Real.log 2) = 2 ^ 16 := by
    rw [show (16 : ℝ) * Real.log 2 = Real.log (2 ^ 16) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by norm_num)]
  have hl2 := Real.log_two_lt_d9
  have hexp : Real.exp (2 * X) ^ 2 = Real.exp (4 * X) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [e]
  calc (2 : ℝ) ^ 12 * ((4 : ℝ) ^ n) ^ 2 ≤ 2 ^ 12 * (4 * Real.exp (2 * X)) ^ 2 := by
        gcongr
    _ = Real.exp (16 * Real.log 2) * Real.exp (4 * X) := by
        rw [e16, mul_pow, hexp]; ring
    _ = Real.exp (16 * Real.log 2 + 4 * X) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (L ^ (0.55 : ℝ)) := Real.exp_le_exp.2 (by linarith)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Domination of the node-4 proxy at the chain boxes** (DZZ (eq-M-A-upper-bound-bis)
l. 2453–2456): for large `k`, on `l53E4 ∩ cellSizeEvent`, every box `b` of the selected chain for
the region `R''` has `dzzMuIn(B) ≤ l53fnM b (B)` for the rational balls `B ⊆ sqBox(c_b, 5 s_b)`. -/
theorem l53n4_dom (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {αs : ℝ}
    (hαs : 0 < αs) {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ T₁ : ℝ,
      ∀ ω ∈ l53E4 hW γ ((2 : ℝ)⁻¹ ^ k) ∩ cellSizeEvent γ W ((2 : ℝ)⁻¹ ^ k),
      ∀ b ∈ l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v
          (Metric.cthickening (2 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ)
            (Metric.cthickening (8 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ) (l53Region u v))) T₁ ω,
      ∀ (c : ℚ × ℚ) (r : ℚ), Metric.ball (ratPt c) r ⊆ sqBox b.center (5 * b.side) →
        dzzMuIn γ W ω (Metric.ball (ratPt c) r) ≤ l53fnM W γ αs k b ω c r := by
  obtain ⟨δ₁, hδ₁, hdom⟩ := l53_domination hW hγ hγ2
  obtain ⟨k₁, hk₁⟩ := l53_sqBox_five_subset_tildeBox γ huv
  obtain ⟨L₂, hL₂⟩ := l53n4_two_pow_le αs hαs.le
  have hl2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hLk : Tendsto (fun k : ℕ => (k : ℝ) * Real.log 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hl2
  have hδk : Tendsto (fun k : ℕ => (2 : ℝ)⁻¹ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (((hδk.eventually (gt_mem_nhds hδ₁)).and
    (hLk.eventually (eventually_ge_atTop (max L₂ 2)))).and (eventually_ge_atTop k₁))
  refine ⟨k₀, fun k hk T₁ ω hω b hb c r hball => ?_⟩
  obtain ⟨⟨hδlt, hLge⟩, hkk⟩ := hk₀ k hk
  set δ : ℝ := (2 : ℝ)⁻¹ ^ k with hδ
  have hlogδ : Real.log δ⁻¹ = (k : ℝ) * Real.log 2 := by
    rw [hδ, inv_pow, inv_inv, Real.log_pow]
  have hne : l53Chain γ W αs δ u v
      (Metric.cthickening (2 * δ ^ dzzCMc γ)
        (Metric.cthickening (8 * δ ^ dzzCMc γ) (l53Region u v))) T₁ ω ≠ [] :=
    List.ne_nil_of_mem hb
  have hQ := l53Chain_spec hne
  obtain ⟨C, hC, hbC, hside⟩ := hQ.1.2.1 b hb
  have hbn := l53fn_n_eq hside
  have hsz := hω.2.2 C hC
  have hn1 : 1 ≤ epsStarN αs δ :=
    one_le_epsStarN hαs (by rw [hlogδ]; linarith [le_max_right L₂ 2])
  have hεs : epsStar αs δ ≤ 1 / 2 := by
    unfold epsStar
    calc (2 : ℝ)⁻¹ ^ epsStarN αs δ ≤ (2 : ℝ)⁻¹ ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hn1
      _ = 1 / 2 := by norm_num
  have hε0 := epsStar_pos' αs δ
  have hC0 := DyBox.side_pos' C
  have hb0 := DyBox.side_pos' b
  have hε2 : epsStar αs δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hbs : b.side ≤ C.side / 4 := by rw [hside]; nlinarith
  have hS := l53n4_sq_sub hbC hbs
  have hsub5 := hk₁ k hkk b (show b.side ≤ δ ^ dzzCMc γ by linarith [hsz.2]) (hQ.2.1 b hb)
  have hopen : Metric.ball (ratPt c) r ⊆ openSquare :=
    l53_sub_openSquare_of_tildeBox hu hv huv (hball.trans hsub5)
  have hj := hL₂ δ (by rw [hlogδ]; linarith [le_max_left L₂ 2])
  have h := hdom δ ⟨by positivity, hδlt⟩ ω hω.1 C hsz.1 hC.1.le (4 * epsStarN αs δ + 12) hj
    b.side hb0 (by linarith) _ hS c r hopen
  have e1 : C.n + (4 * epsStarN αs δ + 12) = b.n + 2 * epsStarN αs δ + 12 := by omega
  have hexp : Real.exp (((k : ℝ) * Real.log 2) ^ (0.91 : ℝ) / 2) ^ 2 =
      Real.exp (((k : ℝ) * Real.log 2) ^ (0.91 : ℝ)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have e2 : ENNReal.ofReal (δ ^ 2 / b.side ^ 2 * Real.exp (Real.log δ⁻¹ ^ (0.91 : ℝ))) =
      ENNReal.ofReal ((δ / b.side * Real.exp (((k : ℝ) * Real.log 2) ^ (0.91 : ℝ) / 2)) ^ 2) := by
    rw [hlogδ, mul_pow, div_pow, hexp]
  rw [e1, e2] at h
  exact h

end DZZ
end LQGMetric
