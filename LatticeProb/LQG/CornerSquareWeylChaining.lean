import LatticeProb.LQG.InternalMetricSquareBorelCantelli
import LatticeProb.LQG.WeylShellChaining
import LatticeProb.LQG.InternalMetricFiniteUnion
import LatticeProb.Topology.CornerSquareShells
import LatticeProb.Prob.TsumEventuallyGeometric

/-!
# Distance to the corner of a corner square for a Weyl-scaled γ-LQG metric

Let `𝔇` be a γ-LQG metric, `h` a whole-plane GFF and `S = [a, a + s] × [b, b + s]` a closed square with the origin as
a corner (`a, b ∈ {0, -s}`). Cover `S \ {0}` by the dyadic shells `⋃ᵢ Q k i` of
`exists_cornerSquareShells` (three squares of side `tₖ = s / 2^(k+1)` at distance between `tₖ` and `3 tₖ` from the
origin). Suppose that

* the internal diameter of the unit square for every whole-plane GFF exceeds `e^{εk}` with probability at most `ψₖ`,
  `∑ ψₖ < ∞` (a uniform unit-square tail);
* for every sequence of corners `cₖ` with `‖cₖ‖ ≤ 3 tₖ`, `∑ₖ P[ξ (h_{tₖ}(cₖ) + Q log tₖ) > lₖ] < ∞`;
* a weight `ξ f` is bounded above by `Bₖ ≥ 0` on the `k`-th shell, and `Bₖ + lₖ + εk ≤ c₀ - ηk` for large `k`,
  with `η > 0`.

Then almost surely there is a finite `A` such that `E(u, 0; S) ≤ A` for every `u ∈ S \ {0}` and every metric `E`
with `E = e^{ξ f} · D_h` (Weyl scaling). The proof applies the Borel-Cantelli bound over squares to each of the three
squares of a shell, bounds the internal `D_h`-diameter of the shell by the sum over its squares, and chains the shells
to the origin at the level of `D_h`, paying the weight `e^{Bₖ}` on the `k`-th shell.

## Main statements

* `IsLQGMetric.ae_internalMetric_weylScaling_cornerSquare_le`
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal Topology

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Distance to the corner of a corner square for a Weyl-scaled LQG metric.** Under a uniform unit-square tail
`ψ`, summable circle-average tails along the shells of the corner square `S = [a, a + s] × [b, b + s]`
(`a, b ∈ {0, -s}`), and a weight `ξ f ≤ Bₖ` on the `k`-th shell with `Bₖ + lₖ + εk ≤ c₀ - ηk` eventually, almost
surely the distances `E(u, 0; S)`, `u ∈ S \ {0}`, are bounded by one finite constant for every Weyl scaling
`E = e^{ξ f} · D_h`. -/
theorem IsLQGMetric.ae_internalMetric_weylScaling_cornerSquare_le (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {ε : ℝ} {ψ : ℕ → ℝ≥0∞} (hψ : ∑' k, ψ k ≠ ⊤)
    (htail : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' → ∀ k : ℕ,
      P {ω | ¬ ∀ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
        internalMetric (𝔇 (hC' ω)) (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) u v ≤
          ENNReal.ofReal (Real.exp (ε * k))} ≤ ψ k)
    {s a b : ℝ} (hs : 0 < s) (ha : a = 0 ∨ a = -s) (hb : b = 0 ∨ b = -s)
    {f : ℂ → ℝ} {B : ℕ → ℝ} (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ k, ∀ w : ℂ, s / 2 ^ (k + 1) ≤ ‖w‖ → ‖w‖ ≤ 3 * (s / 2 ^ (k + 1)) → ξ * f w ≤ B k)
    {l : ℕ → ℝ}
    (hl : ∀ c : ℕ → ℂ, (∀ k, ‖c k‖ ≤ 3 * (s / 2 ^ (k + 1))) →
      ∑' k, P {ω | l k < ξ * (hcirc ω (s / 2 ^ (k + 1)) (c k) +
        lqgQ γ * Real.log (s / 2 ^ (k + 1)))} ≠ ⊤)
    {η c₀ : ℝ} (hη : 0 < η) (hev : ∀ᶠ k : ℕ in atTop, B k + l k + ε * k ≤ c₀ - η * k) :
    ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ E : ℂ → ℂ → ℝ,
      (∀ x y, ENNReal.ofReal (E x y) = weylScaling (𝔇 (hC ω)) ξ f x y) →
      ∀ u ∈ Icc a (a + s) ×ℂ Icc b (b + s), u ≠ 0 →
        internalMetric E (Icc a (a + s) ×ℂ Icc b (b + s)) u 0 ≤ ENNReal.ofReal A := by
  obtain ⟨x, y, Q, hQ, hQS, hQn, hc, hcover, hpre, hmeet⟩ := LatticeProb.Topology.exists_cornerSquareShells hs ha hb
  have ht : ∀ k : ℕ, 0 < s / 2 ^ (k + 1) := fun k => div_pos hs (pow_pos two_pos _)
  -- the Borel-Cantelli bound and the finiteness of every internal diameter, square by square
  have hev_i : ∀ i : Fin 3, ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ u ∈ Q k i, ∀ v ∈ Q k i,
      internalMetric (𝔇 (hC ω)) (Q k i) u v ≤ ENNReal.ofReal (Real.exp (l k + ε * k)) := by
    intro i
    filter_upwards [h𝔇.ae_eventually_internalMetric_square_le hG hψ htail ht
      (c := fun k => ⟨x k i, y k i⟩) (a := l) (hl _ fun k => hc k i)] with ω hω
    filter_upwards [hω] with k hk
    rw [hQ k i]
    exact hk
  have hall_i : ∀ i : Fin 3, ∀ᵐ ω ∂P, ∀ k, ∃ A : ℝ, ∀ u ∈ Q k i, ∀ v ∈ Q k i,
      internalMetric (𝔇 (hC ω)) (Q k i) u v ≤ ENNReal.ofReal A := by
    intro i
    filter_upwards [h𝔇.ae_forall_exists_internalMetric_square_le hG hψ htail ht
      (fun k => ⟨x k i, y k i⟩)] with ω hω k
    rw [hQ k i]
    exact hω k
  filter_upwards [ae_all_iff.2 hev_i, ae_all_iff.2 hall_i, h𝔇.ae_isEuclideanLengthMetric_self hG]
    with ω hevω hallω hD
  -- the internal `D_h`-diameters of the shell squares
  obtain ⟨d, hd⟩ : ∃ d : ℕ → Fin 3 → ℝ≥0∞,
      ∀ k i, d k i = ⨆ u ∈ Q k i, ⨆ v ∈ Q k i, internalMetric (𝔇 (hC ω)) (Q k i) u v :=
    ⟨_, fun _ _ => rfl⟩
  have hd_le : ∀ k i, ∀ u ∈ Q k i, ∀ v ∈ Q k i, internalMetric (𝔇 (hC ω)) (Q k i) u v ≤ d k i :=
    fun k i u hu v hv => by
      rw [hd k i]
      exact le_iSup₂_of_le u hu (le_iSup₂_of_le v hv le_rfl)
  have hd_fin : ∀ k i, d k i ≠ ⊤ := by
    intro k i
    obtain ⟨A, hA⟩ := hallω i k
    rw [hd k i]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup₂_le fun u hu => iSup₂_le fun v hv => hA u hu v hv)
  -- the internal diameter of a shell is at most the sum over its three squares
  have hMR : ∀ k, ∀ u ∈ ⋃ i, Q k i, ∀ v ∈ ⋃ i, Q k i,
      internalMetric (𝔇 (hC ω)) (⋃ i, Q k i) u v ≤ ∑ i, d k i := by
    intro k
    have e : (⋃ i ∈ (Finset.univ : Finset (Fin 3)), Q k i) = ⋃ i, Q k i := by simp
    have h := hD.internalMetric_biUnion_le_sum (F := Finset.univ) (R := Q k) (by rw [e]; exact hpre k)
      (fun i _ => by rw [hQ k i]; exact isClosed_Icc.reProdIm isClosed_Icc) (A := d k)
      (fun i _ => hd_le k i)
    rw [e] at h
    exact h
  -- the weighted shell sum is finite
  have hLfin : ∀ k, ENNReal.ofReal (Real.exp (B k)) * ∑ i, d k i ≠ ⊤ := fun k =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.2 fun i _ => hd_fin k i)
  have hLev : ∀ᶠ k : ℕ in atTop, ENNReal.ofReal (Real.exp (B k)) * ∑ i, d k i ≤
      ENNReal.ofReal (3 * Real.exp c₀ * Real.exp (-(η * k))) := by
    have h3 : ∀ᶠ k in atTop, ∀ i, d k i ≤ ENNReal.ofReal (Real.exp (l k + ε * k)) := by
      rw [Filter.eventually_all]
      intro i
      filter_upwards [hevω i] with k hk
      rw [hd k i]
      exact iSup₂_le fun u hu => iSup₂_le fun v hv => hk u hu v hv
    filter_upwards [h3, hev] with k hk hkB
    have hsum : ∑ i, d k i ≤ ENNReal.ofReal (3 * Real.exp (l k + ε * k)) := by
      calc ∑ i, d k i ≤ ∑ _i : Fin 3, ENNReal.ofReal (Real.exp (l k + ε * k)) :=
            Finset.sum_le_sum fun i _ => hk i
        _ = ENNReal.ofReal (3 * Real.exp (l k + ε * k)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ENNReal.ofReal_mul (by norm_num)]
            norm_num
    calc ENNReal.ofReal (Real.exp (B k)) * ∑ i, d k i
        ≤ ENNReal.ofReal (Real.exp (B k)) * ENNReal.ofReal (3 * Real.exp (l k + ε * k)) := by
          gcongr
      _ = ENNReal.ofReal (3 * Real.exp (B k + (l k + ε * k))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1
          rw [Real.exp_add (B k)]
          ring
      _ ≤ ENNReal.ofReal (3 * Real.exp c₀ * Real.exp (-(η * k))) := by
          apply ENNReal.ofReal_le_ofReal
          have hexp : Real.exp (B k + (l k + ε * k)) ≤ Real.exp c₀ * Real.exp (-(η * k)) := by
            rw [← Real.exp_add]
            exact Real.exp_le_exp.2 (by linarith)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hexp (by norm_num)
  have hsum := tsum_ne_top_of_eventually_le_exp hLfin hη hLev
  refine ⟨(∑' k, ENNReal.ofReal (Real.exp (B k)) * ∑ i, d k i).toReal, fun E hE u hu hu0 => ?_⟩
  have hz : (0 : ℂ) ∈ Icc a (a + s) ×ℂ Icc b (b + s) := by
    rw [Complex.mem_reProdIm, Complex.zero_re, Complex.zero_im, mem_Icc, mem_Icc]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨m, hm⟩ : ∃ m, u ∈ ⋃ i, Q m i := by
    rcases hcover hu with h | h
    · exact absurd h hu0
    · exact mem_iUnion.1 h
  have hρ : Tendsto (fun k : ℕ => 4 * (s / 2 ^ (k + 1))) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => (2 * s) * (1 / 2 : ℝ) ^ k) atTop (𝓝 ((2 * s) * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
    rw [mul_zero] at h
    refine h.congr fun k => ?_
    rw [pow_succ, one_div, inv_pow]
    field_simp
    ring
  have hRρ : ∀ k, (⋃ i, Q k i) ⊆ Metric.ball 0 (4 * (s / 2 ^ (k + 1))) := fun k w hw => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hw
    rw [mem_ball_zero_iff]
    have := (hQn k i w hi).2
    linarith [ht k]
  have hBR : ∀ k, ∀ w ∈ ⋃ i, Q k i, ξ * f w ≤ B k := fun k w hw => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hw
    exact hB k w (hQn k i w hi).1 (hQn k i w hi).2
  have hW := hD.internalMetric_weylScaling_le_tsum_of_shells hE hz (R := fun k => ⋃ i, Q k i)
    (fun k => iUnion_subset fun i => hQS k i) hmeet hρ hRρ hB0 hBR (M := fun k => ∑ i, d k i) hMR hm
  refine hW.trans ?_
  rw [ENNReal.ofReal_toReal hsum]
  exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun k => m + k) (add_right_injective m)
    (fun k => ENNReal.ofReal (Real.exp (B k)) * ∑ i, d k i)

end LatticeProb.LQG
