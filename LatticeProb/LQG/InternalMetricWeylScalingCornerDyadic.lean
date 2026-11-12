import LatticeProb.LQG.InternalMetricWeylScalingCornerSquare
import LatticeProb.LQG.ClosedDyadicShellIndex
import LatticeProb.LQG.ClosedDyadicCornerSquareEq

/-!
# Small internal diameters of all dyadic cells of a square with a log singularity at a corner

Let `D_h` be a γ-LQG metric of a whole-plane GFF `h` and let `E` be the Weyl scaling of `D_h` by
`ξ f`, `f = -α log |·|` with `α < Q`. Let `S = [a, a + s] × [b, b + s]` with `s > 0` and `a, b ∈ {0, -s}`, so that the
log singularity sits at a corner of `S`. We show that, with probability tending to one as `m → ∞`, every closed dyadic
subsquare of `S` of level `m` has `E`-internal diameter at most `ε`
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, the proof of Proposition 3.17, with their Proposition 3.1 as
the hypothesis `huniv`).

The proof fixes a level `K` and splits the cells of level `m ≥ K` into three classes:
* cells whose level-`K` ancestor avoids the singularity, where the weight `f` is continuous;
* the cell containing the singularity, which is the corner square of side `s 2^{-m}`;
* the remaining cells, which lie in the shells `2^{-k} C` (`k ≥ K`) around the corner, for a level-`1` cell `C` of `S`
  avoiding the singularity.

## Main statement
* `LatticeProb.LQG.IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_corner`.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Small internal diameters of the dyadic cells of a square with the log singularity at a corner.**
Let `𝔇` be a γ-LQG metric with `ξ > 0`, `h` a whole-plane GFF, `α < Q`, and `E` a.s. the Weyl scaling of `D_h` by
`ξ f`, `f = -α log |·|`. Let `0 < δ < θ < ξ (Q - 2) log 2` and suppose that the unit-square crossing tail `p` of every
whole-plane GFF on `(Ω, P)` satisfies `∑ₙ 4ⁿ p n < ∞`. Let `S = [a, a + s] × [b, b + s]` with `s > 0` and
`a, b ∈ {0, -s}`. Then for every `ε > 0` the (outer) probability that some closed dyadic subsquare `S_{m,i,j}` of `S` of
level `m` contains two points at `E`-internal distance in `S_{m,i,j}` larger than `ε` tends to `0` as `m → ∞`. -/
theorem IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_corner
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) (hξ : 0 < ξ) {θ δ : ℝ}
    (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) (hδ0 : 0 < δ) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) {α : ℝ} (hα : α < lqgQ γ) {E : Ω → ℂ → ℂ → ℝ}
    (hE : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (𝔇 (hC ω)) ξ (fun w => -α * Real.log ‖w‖) x y)
    {a b s : ℝ} (hs : 0 < s) (ha : a = 0 ∨ a = -s) (hb : b = 0 ∨ b = -s) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m : ℕ => P {ω | ¬ ∀ i j : ℕ, i < 2 ^ m → j < 2 ^ m →
      ∀ z ∈ closedDyadicSubsquare a b s m i j, ∀ w ∈ closedDyadicSubsquare a b s m i j,
        internalMetric (E ω) (closedDyadicSubsquare a b s m i j) z w ≤ ENNReal.ofReal ε}) atTop (𝓝 0) := by
  classical
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη8 : 0 < η / 8 := ENNReal.div_pos hη.ne' (by norm_num)
  -- the shell events of the level-`1` cells `(I, J)` of `S`
  obtain ⟨Sh, hSh⟩ : ∃ Sh : ℕ → ℕ → ℕ → Set Ω, Sh = fun (I J K : ℕ) => {ω | ¬ ∀ k : ℕ, K ≤ k →
      ∀ n i j : ℕ, i < 2 ^ n → j < 2 ^ n →
      ∀ u ∈ closedDyadicSubsquare 0 0 1 n i j, ∀ v ∈ closedDyadicSubsquare 0 0 1 n i j,
        internalMetric (E ω)
          ((fun x : ℂ => ((s / 2 / 2 ^ k : ℝ) : ℂ) * x +
            (2 ^ k : ℂ)⁻¹ * (⟨a + I * (s / 2), b + J * (s / 2)⟩ : ℂ)) '' closedDyadicSubsquare 0 0 1 n i j)
          (((s / 2 / 2 ^ k : ℝ) : ℂ) * u + (2 ^ k : ℂ)⁻¹ * (⟨a + I * (s / 2), b + J * (s / 2)⟩ : ℂ))
          (((s / 2 / 2 ^ k : ℝ) : ℂ) * v + (2 ^ k : ℂ)⁻¹ * (⟨a + I * (s / 2), b + J * (s / 2)⟩ : ℂ)) ≤
            ENNReal.ofReal ε} := ⟨_, rfl⟩
  have hev : ∀ I J : ℕ, I < 2 → J < 2 → ∀ᶠ K in atTop,
      (0 : ℂ) ∉ closedDyadicSubsquare a b s 1 I J → P (Sh I J K) ≤ η / 8 := by
    intro I J hI hJ
    by_cases h0 : (0 : ℂ) ∈ closedDyadicSubsquare a b s 1 I J
    · exact Eventually.of_forall fun _ h => absurd h0 h
    · have ht := h𝔇.tendsto_measure_not_forall_internalMetric_weylScaling_shell_le hG hξ hθ hδ hδ0 huniv hp hα
        hE (half_pos hs) (le_norm_and_norm_le_of_zero_not_mem_closedDyadicSubsquare_one hs ha hb hI hJ h0) hε
      rw [hSh]
      exact (ENNReal.tendsto_nhds_zero.1 ht _ hη8).mono fun _ h _ => h
  -- a level `K` beyond which all shell events are small
  obtain ⟨K, hK00, hK01, hK10, hK11⟩ := ((hev 0 0 two_pos two_pos).and ((hev 0 1 two_pos one_lt_two).and
    ((hev 1 0 one_lt_two two_pos).and (hev 1 1 one_lt_two one_lt_two)))).exists
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → ℕ → Set Ω,
      G = fun (I J : ℕ) => {ω | (0 : ℂ) ∉ closedDyadicSubsquare a b s 1 I J ∧ ω ∈ Sh I J K} := ⟨_, rfl⟩
  have hGle : ∀ I J : ℕ, I < 2 → J < 2 → P (G I J) ≤ η / 8 := by
    intro I J hI hJ
    have hKIJ : (0 : ℂ) ∉ closedDyadicSubsquare a b s 1 I J → P (Sh I J K) ≤ η / 8 := by
      interval_cases I <;> interval_cases J <;> assumption
    rw [hGdef]
    beta_reduce
    by_cases h0 : (0 : ℂ) ∈ closedDyadicSubsquare a b s 1 I J
    · have hempty : {ω | (0 : ℂ) ∉ closedDyadicSubsquare a b s 1 I J ∧ ω ∈ Sh I J K} = ∅ :=
        eq_empty_of_forall_notMem fun ω hω => hω.1 h0
      rw [hempty, measure_empty]
      exact hη8.le
    · exact (measure_mono fun ω hω => hω.2).trans (hKIJ h0)
  -- the level-`K` cells avoiding the singularity, where the weight is continuous
  obtain ⟨T, hT⟩ : ∃ T : Finset (ℕ × ℕ), T = (Finset.range (2 ^ K) ×ˢ Finset.range (2 ^ K)).filter
      (fun q => (0 : ℂ) ∉ closedDyadicSubsquare a b s K q.1 q.2) := ⟨_, rfl⟩
  have hf : ∀ q ∈ T, ContinuousOn (fun w : ℂ => -α * Real.log ‖w‖)
      (closedDyadicSubsquare a b s K q.1 q.2) := by
    intro q hq
    rw [hT, Finset.mem_filter] at hq
    refine continuousOn_const.mul (continuous_norm.continuousOn.log fun w hw => ?_)
    exact norm_ne_zero_iff.2 fun h => hq.2 (h ▸ hw)
  obtain ⟨B1, hB1⟩ : ∃ B1 : ℕ → Set Ω, B1 = fun (m : ℕ) => {ω | ¬ ∀ i j : ℕ, i < 2 ^ m → j < 2 ^ m →
      (i / 2 ^ (m - K), j / 2 ^ (m - K)) ∈ T →
      ∀ z ∈ closedDyadicSubsquare a b s m i j, ∀ w ∈ closedDyadicSubsquare a b s m i j,
        internalMetric (E ω) (closedDyadicSubsquare a b s m i j) z w ≤ ENNReal.ofReal ε} := ⟨_, rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ B2 : ℕ → Set Ω, B2 = fun (m : ℕ) => {ω | ¬ ∀ u ∈ Icc (a / 2 ^ m) (a / 2 ^ m + s / 2 ^ m) ×ℂ
      Icc (b / 2 ^ m) (b / 2 ^ m + s / 2 ^ m), ∀ v ∈ Icc (a / 2 ^ m) (a / 2 ^ m + s / 2 ^ m) ×ℂ
      Icc (b / 2 ^ m) (b / 2 ^ m + s / 2 ^ m),
        internalMetric (E ω) (Icc (a / 2 ^ m) (a / 2 ^ m + s / 2 ^ m) ×ℂ
          Icc (b / 2 ^ m) (b / 2 ^ m + s / 2 ^ m)) u v ≤ ENNReal.ofReal ε} := ⟨_, rfl⟩
  have h1 : ∀ᶠ m in atTop, P (B1 m) ≤ η / 8 := by
    rw [hB1]
    exact ENNReal.tendsto_nhds_zero.1
      (h𝔇.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_continuousOn_cells
        hG hs hξ hθ hδ huniv hp hE K T hf hε) _ hη8
  have h2 : ∀ᶠ m in atTop, P (B2 m) ≤ η / 8 := by
    rw [hB2]
    exact ENNReal.tendsto_nhds_zero.1
      (h𝔇.tendsto_measure_not_forall_internalMetric_weylScaling_cornerSquare_le hG hξ hθ hδ hδ0 huniv hp hα hE
        hs ha hb hε) _ hη8
  filter_upwards [h1, h2, eventually_ge_atTop K] with m h1m h2m hKm
  refine (measure_mono (μ := P) (t := B1 m ∪ B2 m ∪ (G 0 0 ∪ G 0 1 ∪ (G 1 0 ∪ G 1 1))) ?_).trans ?_
  · intro ω hω
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨⟨hn1, hn2⟩, ⟨g00, g01⟩, g10, g11⟩ := hnot
    rw [hB1] at hn1
    rw [hB2] at hn2
    simp only [mem_ofPred_eq, not_not] at hn1 hn2
    rw [hGdef] at g00 g01 g10 g11
    simp only [mem_ofPred_eq, not_and] at g00 g01 g10 g11
    simp only [mem_ofPred_eq] at hω
    apply hω
    intro i j hi hj z hz w hw
    by_cases hA : (0 : ℂ) ∈ closedDyadicSubsquare a b s K (i / 2 ^ (m - K)) (j / 2 ^ (m - K))
    · by_cases hB : (0 : ℂ) ∈ closedDyadicSubsquare a b s m i j
      · -- the cell containing the singularity is the corner square
        rw [closedDyadicSubsquare_cornerIndex_eq hs ha hb hi hj hB] at hz hw ⊢
        exact hn2 z hz w hw
      · -- a cell in a shell around the corner
        obtain ⟨k, hKk, I, J, hI, hJ, h0', n, i₀, j₀, hi₀, hj₀, heq⟩ :=
          exists_shell_image_closedDyadicSubsquare hs ha hb hKm hi hj hA hB
        rw [heq] at hz hw ⊢
        obtain ⟨u, hu, rfl⟩ := hz
        obtain ⟨v, hv, rfl⟩ := hw
        have hS : ω ∉ Sh I J K := by
          interval_cases I <;> interval_cases J
          · exact g00 h0'
          · exact g01 h0'
          · exact g10 h0'
          · exact g11 h0'
        rw [hSh] at hS
        simp only [mem_ofPred_eq, not_not] at hS
        exact hS k hKk n i₀ j₀ hi₀ hj₀ u hu v hv
    · -- a cell whose level-`K` ancestor avoids the singularity
      have hlt : ∀ l : ℕ, l < 2 ^ m → l / 2 ^ (m - K) < 2 ^ K := fun l hl =>
        Nat.div_lt_of_lt_mul (by rw [← pow_add, Nat.sub_add_cancel hKm]; exact hl)
      refine hn1 i j hi hj ?_ z hz w hw
      simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hlt i hi, hlt j hj⟩, hA⟩
  · calc P (B1 m ∪ B2 m ∪ (G 0 0 ∪ G 0 1 ∪ (G 1 0 ∪ G 1 1)))
        ≤ P (B1 m) + P (B2 m) + (P (G 0 0) + P (G 0 1) + (P (G 1 0) + P (G 1 1))) := by
          refine (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) ?_)
          exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) (measure_union_le _ _))
      _ ≤ η / 8 + η / 8 + (η / 8 + η / 8 + (η / 8 + η / 8)) :=
          add_le_add (add_le_add h1m h2m) (add_le_add
            (add_le_add (hGle 0 0 two_pos two_pos) (hGle 0 1 two_pos one_lt_two))
            (add_le_add (hGle 1 0 one_lt_two two_pos) (hGle 1 1 one_lt_two one_lt_two)))
      _ = 6 * (η / 8) := by ring
      _ ≤ 8 * (η / 8) := by gcongr; norm_num
      _ = η := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

end LatticeProb.LQG
