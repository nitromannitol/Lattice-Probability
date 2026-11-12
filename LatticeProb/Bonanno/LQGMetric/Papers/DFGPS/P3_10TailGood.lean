/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_10TailGood at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_10TailProb

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
proof of Proposition 3.10 (T:1880–1904). On the event where
* the circle averages satisfy `h_{2^{-n}𝕣}(w) − h_𝕣(0) ≤ log(C 2^{qn})` at all dyadic corners
  (Lemma 3.11, eqn-use-circle-avg-all),
* the crossings of Prop 3.1 at every dyadic square have `D`-distance
  `≤ A_n 𝔠_{2^{-n}𝕣} e^{ξh_{2^{-n}𝕣}(w)}` with `A_n = C^{ζ} 2^{ζn}`, `ζ = ξ(Q-q)/4`,
* `𝔠_{2^{-n}𝕣} ≤ K₀ 2^{-n(ξQ-ζ)} 𝔠_𝕣` (Theorem 1.5),
every crossing has length `≤ 2K₀ C^{ζ+ξ} 𝔠_𝕣 e^{ξh_𝕣(0)} θⁿ` with `θ = 2^{-ξ(Q-q)/2}`
(T:1888–1892), and the chaining gives the internal diameter bound (T:1904).

Deviation (proposed DEVIATIONS entry): the paper uses `A = 2^{ζξn}` for `n ≥ N_C` only and handles
`n < N_C` by Step 3; we use `A_n = C^{ζ} 2^{ζn}` at every level `n ≥ 0` (the union bound still
decays superpolynomially in `C`) and no Step 3.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology Complex
open scoped ENNReal ComplexOrder

namespace LQGMetric.DFGPS
open Blueprint MetricGeometry

lemma bracket_eq {ξ Q q : ℝ} (n : ℕ) :
    ((2 : ℝ) ^ n) ^ (ξ * (Q - q) / 4) * ((1 / 2 : ℝ) ^ n) ^ (ξ * Q - ξ * (Q - q) / 4) *
      ((2 : ℝ) ^ (q * n)) ^ ξ = ((1 / 2 : ℝ) ^ (ξ * (Q - q) / 2)) ^ n := by
  have h2 : (0 : ℝ) < 2 := two_pos
  have e1 : ((2 : ℝ) ^ n) ^ (ξ * (Q - q) / 4) = (2 : ℝ) ^ ((n : ℝ) * (ξ * (Q - q) / 4)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2.le]
  have e2 : ((1 / 2 : ℝ) ^ n) ^ (ξ * Q - ξ * (Q - q) / 4) =
      (2 : ℝ) ^ (-(n : ℝ) * (ξ * Q - ξ * (Q - q) / 4)) := by
    rw [Real.rpow_mul h2.le, Real.rpow_neg h2.le, Real.rpow_natCast, one_div, inv_pow]
  have e3 : ((2 : ℝ) ^ (q * n)) ^ ξ = (2 : ℝ) ^ (q * n * ξ) := by
    rw [← Real.rpow_mul h2.le]
  have e4 : ((1 / 2 : ℝ) ^ (ξ * (Q - q) / 2)) ^ n = (2 : ℝ) ^ (-(ξ * (Q - q) / 2) * n) := by
    rw [one_div, Real.inv_rpow h2.le, ← Real.rpow_neg h2.le, ← Real.rpow_natCast,
      ← Real.rpow_mul h2.le]
  rw [e1, e2, e3, e4, ← Real.rpow_add h2, ← Real.rpow_add h2]
  congr 1
  ring

/-- **Steps 1–2 on the good event** (T:1880–1904): deterministic. -/
theorem diam_le_on_good {D' : ContMetric} (hDl : D'.IsLength) {ξ Q q C K₀ 𝕣 : ℝ}
    {c : ℝ → ℝ} {g : DistC} (hξ : 0 < ξ) (hqQ : q < Q) (hC : 1 ≤ C) (hK₀ : 1 ≤ K₀) (h𝕣 : 0 < 𝕣)
    (hc : ∀ r, 0 < r → 0 < c r)
    (hscale : ∀ n : ℕ, c (𝕣 / 2 ^ n) ≤ K₀ * ((1 / 2 : ℝ) ^ n) ^ (ξ * Q - ξ * (Q - q) / 4) * c 𝕣)
    (hcirc : ∀ n j k : ℕ, j < 2 ^ n → k < 2 ^ n →
      circleAvg g (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k) - circleAvg g 𝕣 0 ≤
        Real.log (C * (2 : ℝ) ^ (q * n)))
    (hHg : ∀ n j k : ℕ, j < 2 ^ n → k < 2 ^ n → ∀ b : ℕ, b ≤ 1 →
      setDistIn D' (scaleSet (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k)
          (Icc (1 / 16) (1 / 16) ×ℂ Icc (3 / 16 + (b : ℝ) / 2) (5 / 16 + (b : ℝ) / 2)))
        (scaleSet (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k)
          (Icc (15 / 16) (15 / 16) ×ℂ Icc (3 / 16 + (b : ℝ) / 2) (5 / 16 + (b : ℝ) / 2)))
        (scaleSet (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k)
          (Ioo 0 1 ×ℂ Ioo (1 / 8 + (b : ℝ) / 2) (3 / 8 + (b : ℝ) / 2))) ≤
      ENNReal.ofReal (C ^ (ξ * (Q - q) / 4) * ((2 : ℝ) ^ n) ^ (ξ * (Q - q) / 4) *
        scaleFac ξ c g (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k)))
    (hVg : ∀ n j k : ℕ, j < 2 ^ n → k < 2 ^ n →
      setDistIn D' (scaleSet (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k)
          (Icc (3 / 16) (5 / 16) ×ℂ Icc (1 / 16) (1 / 16)))
        (scaleSet (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k)
          (Icc (3 / 16) (5 / 16) ×ℂ Icc (15 / 16) (15 / 16)))
        (scaleSet (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k) (Ioo (1 / 8) (3 / 8) ×ℂ Ioo 0 1)) ≤
      ENNReal.ofReal (C ^ (ξ * (Q - q) / 4) * ((2 : ℝ) ^ n) ^ (ξ * (Q - q) / 4) *
        scaleFac ξ c g (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k))) :
    internalDiam D' (rS 𝕣) (rS 𝕣) ≤ ENNReal.ofReal (2 * (5 * (2 * K₀ *
      C ^ (ξ * (Q - q) / 4 + ξ) * scaleFac ξ c g 𝕣 0) / (1 - (1 / 2 : ℝ) ^ (ξ * (Q - q) / 2)))) := by
  set ζ := ξ * (Q - q) / 4 with hζ
  have hζ0 : 0 < ζ := by rw [hζ]; have := sub_pos.2 hqQ; positivity
  set θ := (1 / 2 : ℝ) ^ (ξ * (Q - q) / 2) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by
    have := sub_pos.2 hqQ; positivity)
  have hC0 : 0 < C := by linarith
  have hN : 0 < scaleFac ξ c g 𝕣 0 := mul_pos (hc 𝕣 h𝕣) (Real.exp_pos _)
  set B := 2 * K₀ * C ^ (ζ + ξ) * scaleFac ξ c g 𝕣 0 with hB
  have hB0 : 0 ≤ B := by positivity
  have hpos : ∀ n : ℕ, ∀ w : ℂ, 0 < C ^ ζ * ((2 : ℝ) ^ n) ^ ζ * scaleFac ξ c g (𝕣 / 2 ^ n) w :=
    fun n w => mul_pos (by positivity) (mul_pos (hc _ (by positivity)) (Real.exp_pos _))
  have key : ∀ n j k : ℕ, j < 2 ^ n → k < 2 ^ n →
      2 * (C ^ ζ * ((2 : ℝ) ^ n) ^ ζ * scaleFac ξ c g (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k)) ≤
        B * θ ^ n := by
    intro n j k hj hk
    set X := C * (2 : ℝ) ^ (q * n)
    have hX : 0 < X := by positivity
    have hexp : Real.exp (ξ * circleAvg g (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k)) ≤
        Real.exp (ξ * circleAvg g 𝕣 0) * X ^ ξ := by
      rw [Real.rpow_def_of_pos hX, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left (hcirc n j k hj hk) hξ.le
      linarith
    have hsf : scaleFac ξ c g (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k) ≤
        K₀ * ((1 / 2 : ℝ) ^ n) ^ (ξ * Q - ζ) * c 𝕣 *
          (Real.exp (ξ * circleAvg g 𝕣 0) * X ^ ξ) :=
      mul_le_mul (hscale n) hexp (Real.exp_pos _).le (by
        have := hc 𝕣 h𝕣; positivity)
    calc _ ≤ 2 * (C ^ ζ * ((2 : ℝ) ^ n) ^ ζ * (K₀ * ((1 / 2 : ℝ) ^ n) ^ (ξ * Q - ζ) * c 𝕣 *
          (Real.exp (ξ * circleAvg g 𝕣 0) * X ^ ξ))) := by gcongr
      _ = B * θ ^ n := by
        rw [hB, hθ, ← bracket_eq (ξ := ξ) (Q := Q) (q := q) n, Real.mul_rpow hC0.le (by positivity),
          Real.rpow_add hC0]
        simp only [scaleFac, ← hζ]
        ring
  have h := internalDiam_le_of_crossings (D := D') hDl h𝕣 hB0 hθ0 hθ1
    (fun n j k hj hk b hb => by
      have hb' : (b : ℝ) ≤ 1 := by exact_mod_cast hb
      obtain ⟨P, hP⟩ := hcr_of_good (Y := rS 𝕣) (by positivity : (0 : ℝ) < 𝕣 / 2 ^ n)
        (hpos n _) (dySq_sub h𝕣 hj hk) (by positivity) (by linarith) (hHg n j k hj hk b hb)
      exact ⟨P, hP.mono (key n j k hj hk)⟩)
    (fun n j k hj hk => by
      obtain ⟨P, hP⟩ := vcr_of_good (Y := rS 𝕣) (by positivity : (0 : ℝ) < 𝕣 / 2 ^ n)
        (hpos n _) (dySq_sub h𝕣 hj hk) (hVg n j k hj hk)
      exact ⟨P, hP.mono (key n j k hj hk)⟩)
  exact h

end LQGMetric.DFGPS
