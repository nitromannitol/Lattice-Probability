/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Exist.Lemma33 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Exist.GoodEvent

/-!
# DGZ Lemma 3.3: near-subadditivity of the quantiles `λ_n` (packet P-X8, target T1)

Source: DGZ arXiv:2310.03996, Lemma 3.3 (and Lemma 3.2 for the median form); planning audit HA5,
Details D9 (complete proof, including "Events", "Percolation events", "Probability" and
"Remaining cases (G12)"), D3, D5, D6, D7, D14.

Notation (HA5): `h_n = H_{2^{-n},1}`, `D_n = D^ξ(h_n)` (`lfppDistance d ξ`), `a^{(p)}_n` the lower
`p`-quantile of the law of `D_n` (`LQGMetric.lowerQuantile`), `λ_n = a^{(1/2)}_n`. These numbers do
not depend on the realization (`IsBandVersion.lowerQuantile_lfppDistance_eq`).

**Statement** (`lemma33`). For `d ≥ 2`, an admissible kernel `κ` and `ξ > 0` there are
`p* ∈ (0,1)` and `C ≥ 0` such that for all `n > m ≥ 1`, every white noise and continuous versions
of `h_n`, `h_m`, `h_{n-m}` on its probability space,
`λ_n ≤ e^{C n^{2/3}} a^{(p*)}_m a^{(p*)}_{n-m}`; and (`lemma33_median`, by DGZ Lemma 3.2)
`λ_n ≤ e^{C n^{2/3}} λ_m λ_{n-m}`, i.e. (`lemma33_log`, HA5 (c) `NearSubadditive`)
`log λ_n ≤ log λ_m + log λ_{n-m} + C n^{2/3}`.

**Proof** (HA5 D9).

* *Main case* (`lemma33_main`, `m ≥ m₀`, `n > m + k`, `k = ⌊(log m)²⌋`): on the white noise of
  `h_n`, take versions `Y₁` of the middle band `h_{m,m+k}` and `Y₂` of the fine band `h_{m+k,n}`;
  `h_m + Y₁ + Y₂` is a version of `h_n` (`IsBandVersion.add3`), so it has the law of `h_n`. The
  fine sites `y ∈ 2^{-m-k} ℤ^d` are closed (`DGZ.closedSite`, threshold `b = a^{(p)}_{n-m-k}`) with
  probability `≤ 2d(1-p)` and satisfy the product bound with range `r = ⌈2(2+ρ)⌉`
  (`DGZ.measure_closedSite_le_lowerQuantile_of_band`, `DGZ.productBound_closedSite`). The good event
  `E = E₂ \ (B₁ ∪ … ∪ B₅)` consists of
  - `E₂ = {D_m ≤ a^{(p)}_m}` (probability `≥ p = 1 - η`);
  - `B₁ = L33.oscBad` (oscillation of `h_m` above `n^{2/3}`; `≤ 1/10` by Lemma O);
  - `B₂ = {sup_{[-2,2]^d} |Y₁| ≥ t √(k(m+k))}` (`≤ 1/10` by Lemma 3.4′);
  - `B₃` = some closed cluster meeting `[-2^{m+k+1}, 2^{m+k+1}]^d` has diameter `> 2^{k-2}`
    (`≤ 1/10` by `Perc.diameterBound`);
  - `B₄`, `B₅` = a site within distance 5 of `0` (resp. of `2^{m+k} e₁`) is closed, or a closed
    cluster encloses it (each `≤ 1/20` by `Perc.enclosureBound`, `d ≥ 2`).
  So `P(E) ≥ 1 - η - 2/5 ≥ 1/2` (`L33.half_le_measure_diff`), and on `E` the deterministic
  construction (`DGZ.lfppDistance_le_of_good_sites_exp`: discretization, surgery, chain bound)
  gives `D_n ≤ e^{(14d+1+2ξ) n^{2/3} + ξ S} a^{(p)}_m a^{(p)}_{n-m-k}`. Hence `λ_n` is at most the
  right side. Finally Lemma 3.5 at scale `k` (`lemma35`) gives
  `a^{(p)}_{n-m-k} ≤ e^{C √(k(n-m))} a^{(p)}_{n-m}`, and `ξ S ≤ 37 ξ t n^{2/3}`,
  `√(k(n-m)) ≤ 6 n^{2/3}` (`L33.sqrt_kpar_mul_add_le`, `L33.sqrt_kpar_mul_le`).
* *Remaining cases* (`lemma33_rest`, HA5 G12): `λ_n ≤ e^{c √n} a^{(p)}_n` (DGZ Lemma 3.2); if
  `m < m₀`, Lemma 3.5 gives `a^{(p)}_n ≤ e^{C√(mn)} a^{(p)}_{n-m}` and the crude bound
  `a^{(p)}_m ≥ e^{-ξ A m₀}`; if `n ≤ m + k`, Lemma 3.5 gives `a^{(p)}_n ≤ e^{C √((n-m)n)} a^{(p)}_m`
  and `a^{(p)}_{n-m} ≥ e^{-ξ A k}`, with `k ≤ 36 n^{1/3}`.

The percolation bounds of packet P-X6 are stated for probability spaces in `Type`, so the main case
is proved there (`lemma33_type0`); `lemma33` transfers it to every universe through a canonical
realization (`field_exists_impl`) and the realization independence of the quantiles.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal
open HigherDimLFPP.Perc (Zd LAdj WithinInf ProductBound IsClosedCluster Encloses)

namespace HigherDimLFPP

open L33

namespace L33

/-- `2^{-j} / 2^{-i} = 2^{-(j-i)}` for `i ≤ j`. -/
theorem dyadic_div_dyadic_sub {i j : ℕ} (h : i ≤ j) :
    ((2 : ℝ) ^ j)⁻¹ / ((2 : ℝ) ^ i)⁻¹ = ((2 : ℝ) ^ (j - i))⁻¹ := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  exact dyadic_div_dyadic i l

end L33
/-- The lower `p`-quantile of the frozen distance of a continuous version is positive. -/
theorem IsBandVersion.lowerQuantile_lfppDistance_pos {d : ℕ} (hd : 0 < d) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {κ : Rd d → ℝ} {a b : ℝ}
    {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H) (hW : IsWhiteNoise P W) (ξ : ℝ)
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H z ω)) p := by
  have := hW.isProbabilityMeasure
  exact Conc.lowerQuantile_map_pos (hH.measurable_lfppDistance ξ).aemeasurable
    (ae_of_all _ fun ω => lfppDistance_pos hd (hH.continuous ω)) hp0 hp1

/-- **DGZ Lemma 3.3, main case** (HA5 D9; probability spaces in `Type`): there are a level
`p ∈ (0,1)`, a threshold `m₀ ≥ 8` and `C ≥ 0` (depending on `d`, `κ`, `ξ`) such that for all
`m ≥ m₀` and `n > m + ⌊(log m)²⌋`, `λ_n ≤ e^{C n^{2/3}} a^{(p)}_m a^{(p)}_{n-m}`. -/
theorem lemma33_main {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ : ℝ}
    (hξ : 0 < ξ) :
    ∃ p : ℝ≥0∞, 0 < p ∧ p < 1 ∧ ∃ m₀ : ℕ, 8 ≤ m₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {n m : ℕ}, m₀ ≤ m → m + kpar m < n → ∀ {H₁ H₂ H₃ : Rd d → Ω → ℝ},
        IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ 1 H₁ → IsBandVersion P W κ ((2 : ℝ) ^ m)⁻¹ 1 H₂ →
        IsBandVersion P W κ ((2 : ℝ) ^ (n - m))⁻¹ 1 H₃ →
        LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₁ z ω)) 2⁻¹ ≤
          Real.exp (C * (n : ℝ) ^ (2 / 3 : ℝ)) *
            LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω)) p *
            LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₃ z ω)) p := by
  have : NeZero d := ⟨by omega⟩
  have hd0 : 0 < d := by omega
  -- the range of the product bound and the level `p` (HA5 D9, "Percolation events")
  obtain ⟨ρ, hρ0, hρ⟩ := hκ.exists_radius
  set r : ℕ := ⌈2 * (2 + ρ)⌉₊ with hr
  obtain ⟨η, hη0, hη1, hεθ, hencl⟩ := exists_level d r hd0
  set p : ℝ≥0∞ := ENNReal.ofReal (1 - η) with hp
  have hp0 : 0 < p := ENNReal.ofReal_pos.2 (by linarith)
  have hp1 : p < 1 := by
    rw [hp, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)
  have h1p : 1 - p = ENNReal.ofReal η := one_sub_ofReal_one_sub (by linarith)
  set θ : ℝ≥0∞ := ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ with hθ
  have hθ1 : θ ≤ 1 := theta_le_one d
  have h3θ : (3 : ℝ≥0∞) ^ d * θ ≤ 2⁻¹ := three_pow_mul_theta_le d
  -- Lemma O constants
  obtain ⟨L, hL0, hL⟩ := exists_norm_bandVec_sub_sq_le hκ
  set L' : ℝ := L + 1 with hL'
  have hL'0 : 0 < L' := by linarith
  have hL'b : ∀ (a : ℝ), 0 < a → ∀ (b : ℝ) (z w : Rd d),
      ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L' * ‖z - w‖ ^ 2 / a ^ 2 :=
    fun a ha b z w => (hL a ha b z w).trans (by gcongr; linarith)
  set Bc : ℝ := Osc.blockConst d L' (√(d : ℝ) * 3) with hBc
  have hBc0 : 0 ≤ Bc := Osc.blockConst_nonneg d (by positivity)
  set c : ℝ := 2 * ((√(d : ℝ) * 3) ^ 2 * L') with hc
  have hsd : 0 < √(d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd0)
  have hc0 : 0 < c := by positivity
  obtain ⟨n₁, hn₁⟩ := exists_osc_threshold d hBc0 hc0
  -- the diameter threshold
  obtain ⟨m₃, hm₃8, hm₃⟩ := exists_diam_threshold d
  -- the middle band (Lemma 3.4′)
  obtain ⟨tδ, htδ, htail⟩ := lemma34'_small_exists hκ (δ := 1 / 10) (by norm_num)
  -- Lemma 3.5
  obtain ⟨C₃₅, hC₃₅0, hC₃₅⟩ := lemma35 hκ hξ hp0 hp1
  refine ⟨p, hp0, hp1, max n₁ m₃, hm₃8.trans (le_max_right _ _),
    14 * d + 1 + 2 * ξ + 37 * ξ * tδ + 6 * C₃₅, by positivity, ?_⟩
  intro Ω _ P W hW n m hm hmkn H₁ H₂ H₃ h₁ h₂ h₃
  have := hW.isProbabilityMeasure
  have hmn₁ : n₁ ≤ m := (le_max_left _ _).trans hm
  have hmm₃ : m₃ ≤ m := (le_max_right _ _).trans hm
  obtain ⟨hk4, hdiamp⟩ := hm₃ m hmm₃
  set k : ℕ := kpar m with hk
  have hm8 : 8 ≤ m := hm₃8.trans hmm₃
  have hmn : m < n := by omega
  have hmkn' : m + k ≤ n := hmkn.le
  -- scales
  set s : ℝ := (2 : ℝ)⁻¹ ^ (m + k) with hs
  have hs0 : 0 < s := by positivity
  have hs_eq : s = ((2 : ℝ) ^ (m + k))⁻¹ := inv_pow 2 (m + k)
  set ϱ : ℝ := 2 - (2 : ℝ)⁻¹ ^ (m + 3) with hϱ
  have hns : ((2 : ℝ) ^ n)⁻¹ ≤ s := by
    rw [hs_eq]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hmkn')
  have hsm : s ≤ ((2 : ℝ) ^ m)⁻¹ := by
    rw [hs_eq]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  have hm1' : ((2 : ℝ) ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  -- the middle and fine bands, and the field defining the threshold of the fine sites
  obtain ⟨Y₁, hY₁⟩ := exists_isBandVersion hκ hW hs0 ((2 : ℝ) ^ m)⁻¹
  obtain ⟨Y₂, hY₂⟩ := exists_isBandVersion hκ hW (dyadic_pos n) s
  obtain ⟨H', hH'⟩ := exists_isBandVersion hκ hW (div_pos (dyadic_pos n) hs0) 1
  -- `h_m + Y₁ + Y₂` is a version of `h_n`
  have hsum := IsBandVersion.add3 hκ hW (dyadic_pos n) hns hsm hm1' h₂ hY₁ hY₂
  -- the quantiles
  set a : ℝ := LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω)) p
    with ha
  set b : ℝ := LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H' z ω)) p
    with hb
  set q₃ : ℝ := LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₃ z ω)) p
    with hq₃
  have ha0 : 0 < a := h₂.lowerQuantile_lfppDistance_pos hd0 hW ξ hp0 hp1
  have hb0 : 0 < b := hH'.lowerQuantile_lfppDistance_pos hd0 hW ξ hp0 hp1
  have hq₃0 : 0 < q₃ := h₃.lowerQuantile_lfppDistance_pos hd0 hW ξ hp0 hp1
  -- the closed fine sites
  set closed : Zd d → Set Ω := DGZ.closedSite ξ Y₂ s b ϱ with hclosed
  have hcl : ∀ y, P (closed y) ≤ 2 * d * (1 - p) := fun y =>
    DGZ.measure_closedSite_le_lowerQuantile_of_band hκ hW hW (dyadic_pos n) hs0 hY₂ hH' ξ hp0
      hp1 ϱ y
  have hPB : ProductBound P closed (r : ℤ) :=
    DGZ.productBound_closedSite hκ hW hρ (dyadic_pos n) hY₂ hs0 le_rfl ξ b ϱ
  have hεθ' : 2 * (d : ℝ≥0∞) * (1 - p) ≤ θ ^ ((r + 1) ^ d) := by
    rw [h1p]
    exact hεθ
  -- `E₃ₐ`: diameters of the closed clusters
  set B₃ : Set Ω := {ω | ∃ C, IsClosedCluster {y | ω ∉ closed y} C ∧
    (∃ z ∈ C, WithinInf ((2 ^ (m + k + 1) : ℕ) : ℤ) z 0) ∧
      ∃ y ∈ C, ∃ y' ∈ C, ¬ WithinInf ((2 ^ (k - 2) : ℕ) : ℤ) y y'} with hB₃def
  have hB₃ : P B₃ ≤ ENNReal.ofReal (1 / 10) :=
    (Perc.diameterBound d P closed r _ θ hcl hPB hθ1 hεθ' h3θ 0 (2 ^ (m + k + 1))
      (2 ^ (k - 2))).trans hdiamp
  -- `E₃ᵦ`: `0` and `2^{m+k} e₁` are open and not enclosed
  set x₁ : Zd d := DGZ.latE1 d (2 ^ (m + k)) with hx₁
  set B₄ : Set Ω := {ω | (∃ y, WithinInf ((5 : ℕ) : ℤ) y 0 ∧ ω ∈ closed y) ∨
    ∃ C, IsClosedCluster {y | ω ∉ closed y} C ∧ Encloses C 0} with hB₄def
  have hB₄ : P B₄ ≤ ENNReal.ofReal (1 / 20) := by
    refine (Perc.enclosureBound d hd P closed r _ θ hcl hPB hθ1 hεθ' h3θ 0 5).trans ?_
    rw [h1p]
    exact hencl
  set B₅ : Set Ω := {ω | (∃ y, WithinInf ((5 : ℕ) : ℤ) y x₁ ∧ ω ∈ closed y) ∨
    ∃ C, IsClosedCluster {y | ω ∉ closed y} C ∧ Encloses C x₁} with hB₅def
  have hB₅ : P B₅ ≤ ENNReal.ofReal (1 / 20) := by
    refine (Perc.enclosureBound d hd P closed r _ θ hcl hPB hθ1 hεθ' h3θ x₁ 5).trans ?_
    rw [h1p]
    exact hencl
  -- `E₁`: oscillation of the coarse field
  obtain ⟨hu0, hubound⟩ := hn₁ n m (hmn₁.trans hmn.le) hmn.le
  set u : ℝ := (n : ℝ) ^ (2 / 3 : ℝ) / 2 - Bc with hu
  set B₁ : Set Ω := oscBad H₂ m (2 * (Bc + u)) with hB₁def
  have hB₁ : P B₁ ≤ ENNReal.ofReal (1 / 10) :=
    (measure_oscBad_le hW h₂ hL'0.le (hL'b _ (dyadic_pos m) 1) hu0).trans
      (ENNReal.ofReal_le_ofReal hubound)
  -- `E₁`: the middle band
  have hY₁' : IsBandVersion P W κ ((2 : ℝ) ^ (m + k))⁻¹ ((2 : ℝ) ^ (m + k - k))⁻¹ Y₁ :=
    hY₁.congr_band hs_eq (by rw [Nat.add_sub_cancel])
  set S : ℝ := tδ * √((k : ℝ) * ((m + k : ℕ) : ℝ)) with hS
  set B₂ : Set Ω := {ω | ∃ z ∈ Osc.box (0 : Rd d) 2, S ≤ |Y₁ z ω|} with hB₂def
  have hB₂ : P B₂ ≤ ENNReal.ofReal (1 / 10) :=
    htail hW (m := k) (n := m + k) (by omega) (by omega) hY₁' le_rfl
  -- `E₂`: the coarse distance is below its quantile
  set E₂ : Set Ω := {ω | lfppDistance d ξ (fun z => H₂ z ω) ≤ a} with hE₂def
  have hE₂ : p ≤ P E₂ := by
    have h := (LQGMetric.le_measure_Iic_iff_lowerQuantile_le
      (μ := P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω)) hp0 hp1).2 le_rfl
    rwa [Measure.map_apply (h₂.measurable_lfppDistance ξ) measurableSet_Iic] at h
  -- the probability of the good event
  have hBsum : P (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅) ≤ ENNReal.ofReal (2 / 5) := by
    calc P (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅) ≤ P B₁ + P B₂ + P B₃ + P B₄ + P B₅ := by
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (1 / 10) + ENNReal.ofReal (1 / 10) + ENNReal.ofReal (1 / 10) +
            ENNReal.ofReal (1 / 20) + ENNReal.ofReal (1 / 20) := by gcongr
      _ = ENNReal.ofReal (2 / 5) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  set G : Set Ω := E₂ \ (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅) with hGdef
  have hG : 2⁻¹ ≤ P G := half_le_measure_diff hE₂ hBsum (by norm_num) (by linarith)
  -- the deterministic bound on the good event
  set X : ℝ := Real.exp ((14 * d + 1 + 2 * ξ) * (n : ℝ) ^ (2 / 3 : ℝ) + ξ * S) * a * b with hX
  have hGX : ∀ ω ∈ G, lfppDistance d ξ (fun z => H₂ z ω + Y₁ z ω + Y₂ z ω) ≤ X := by
    intro ω hω
    obtain ⟨hωE₂, hωB⟩ := hω
    simp only [mem_union, not_or] at hωB
    obtain ⟨⟨⟨⟨hω₁, hω₂⟩, hω₃⟩, hω₄⟩, hω₅⟩ := hωB
    have hlt : lfppDistance d ξ (fun z => H₂ z ω) < 2 * a := by
      have h1 : lfppDistance d ξ (fun z => H₂ z ω) ≤ a := hωE₂
      have h2 := lfppDistance_pos hd0 (ζ := ξ) (h₂.continuous ω)
      linarith
    obtain ⟨γ, hγ, hγL⟩ := exists_isAdmissiblePath_lfppLength_lt hlt
    refine DGZ.lfppDistance_le_of_good_sites_exp hd0 hm8 hmn.le rfl hξ.le (h₂.continuous ω)
      (hY₁.continuous ω) (hY₂.continuous ω) ?_ ?_ hγ hγL.le ?_ ?_ ?_ ?_ ?_
    · intro x hx z hz
      have h := osc_le_of_not_mem_oscBad hω₁ x hx z hz
      have e : 2 * (Bc + u) = (n : ℝ) ^ (2 / 3 : ℝ) := by rw [hu]; ring
      rwa [e] at h
    · intro z hz
      by_contra hlt'
      push Not at hlt'
      exact hω₂ ⟨z, cube_subset_box d hz, hlt'.le.trans (le_abs_self _)⟩
    · intro C hC hz y hy y' hy'
      by_contra hn
      exact hω₃ ⟨C, hC, hz, y, hy, y', hy', hn⟩
    · intro hc
      exact hω₄ (Or.inl ⟨0, Perc.withinInf_refl (by norm_num) 0, hc⟩)
    · intro hc
      exact hω₅ (Or.inl ⟨x₁, Perc.withinInf_refl (by norm_num) x₁, hc⟩)
    · intro C hC hE
      exact hω₄ (Or.inr ⟨C, hC, hE⟩)
    · intro C hC hE
      exact hω₅ (Or.inr ⟨C, hC, hE⟩)
  have hq_sum : LQGMetric.lowerQuantile
      (P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω + Y₁ z ω + Y₂ z ω)) 2⁻¹ ≤ X :=
    lowerQuantile_le_of_le_on (hsum.measurable_lfppDistance ξ) (by norm_num) (by norm_num) hGX hG
  have hq₁ : LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₁ z ω)) 2⁻¹ =
      LQGMetric.lowerQuantile
        (P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω + Y₁ z ω + Y₂ z ω)) 2⁻¹ :=
    h₁.lowerQuantile_lfppDistance_eq hsum hW hW ξ 2⁻¹
  -- Lemma 3.5 at scale `k`: `a^{(p)}_{n-m-k} ≤ e^{C √(k(n-m))} a^{(p)}_{n-m}`
  have hH'' : IsBandVersion P W κ ((2 : ℝ) ^ (n - m - k))⁻¹ 1 H' := by
    refine hH'.congr_band ?_ rfl
    rw [hs_eq, dyadic_div_dyadic_sub hmkn', Nat.sub_sub]
  obtain ⟨hb_low, -⟩ := hC₃₅ hW hW (m := k) (n := n - m) (by omega) (by omega) h₃ hH''
  have hb_le : b ≤ Real.exp (C₃₅ * √((k : ℝ) * ((n - m : ℕ) : ℝ))) * q₃ := by
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)] at hb_low
    exact hb_low
  -- the exponents
  have hS_le : ξ * S ≤ 37 * ξ * tδ * (n : ℝ) ^ (2 / 3 : ℝ) := by
    have h := sqrt_kpar_mul_add_le (m := m) (n := n) (by omega) hmn.le
    rw [← hk] at h
    have e : ((m + k : ℕ) : ℝ) = (m : ℝ) + k := by push_cast; ring
    have h' : S ≤ tδ * (37 * (n : ℝ) ^ (2 / 3 : ℝ)) := by
      rw [hS, e]
      exact mul_le_mul_of_nonneg_left h htδ.le
    have := mul_le_mul_of_nonneg_left h' hξ.le
    linarith
  have hK : C₃₅ * √((k : ℝ) * ((n - m : ℕ) : ℝ)) ≤ 6 * C₃₅ * (n : ℝ) ^ (2 / 3 : ℝ) := by
    have h1 : √((k : ℝ) * ((n - m : ℕ) : ℝ)) ≤ √((k : ℝ) * n) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le n m)
        (Nat.cast_nonneg _))
    have h2 := sqrt_kpar_mul_le (m := m) (n := n) (by omega) hmn.le
    rw [← hk] at h2
    have := mul_le_mul_of_nonneg_left (h1.trans h2) hC₃₅0
    linarith
  have hb_le' : b ≤ Real.exp (6 * C₃₅ * (n : ℝ) ^ (2 / 3 : ℝ)) * q₃ :=
    hb_le.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hK) hq₃0.le)
  rw [hq₁]
  calc LQGMetric.lowerQuantile
        (P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω + Y₁ z ω + Y₂ z ω)) 2⁻¹ ≤ X := hq_sum
    _ ≤ Real.exp ((14 * d + 1 + 2 * ξ) * (n : ℝ) ^ (2 / 3 : ℝ) +
            37 * ξ * tδ * (n : ℝ) ^ (2 / 3 : ℝ)) * a *
          (Real.exp (6 * C₃₅ * (n : ℝ) ^ (2 / 3 : ℝ)) * q₃) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) ha0.le) hb_le'
          hb0.le (by positivity)
    _ = Real.exp ((14 * d + 1 + 2 * ξ + 37 * ξ * tδ + 6 * C₃₅) * (n : ℝ) ^ (2 / 3 : ℝ)) * a *
          q₃ := by
        have e : (14 * (d : ℝ) + 1 + 2 * ξ + 37 * ξ * tδ + 6 * C₃₅) * (n : ℝ) ^ (2 / 3 : ℝ) =
            ((14 * d + 1 + 2 * ξ) * (n : ℝ) ^ (2 / 3 : ℝ) +
              37 * ξ * tδ * (n : ℝ) ^ (2 / 3 : ℝ)) + 6 * C₃₅ * (n : ℝ) ^ (2 / 3 : ℝ) := by ring
        rw [e, Real.exp_add ((14 * (d : ℝ) + 1 + 2 * ξ) * (n : ℝ) ^ (2 / 3 : ℝ) +
          37 * ξ * tδ * (n : ℝ) ^ (2 / 3 : ℝ)) (6 * C₃₅ * (n : ℝ) ^ (2 / 3 : ℝ))]
        ring

namespace L33

/-- `√(log(1/2^{-j})) = √(j log 2) ≤ √(log 2) n^{2/3}` for `j ≤ n`, `n ≥ 1`. -/
theorem sqrt_log_dyadic_le {j n : ℕ} (hjn : j ≤ n) (hn : 1 ≤ n) :
    √(Real.log (1 / ((2 : ℝ) ^ j)⁻¹)) ≤ √(Real.log 2) * (n : ℝ) ^ (2 / 3 : ℝ) := by
  rw [one_div, inv_inv, Real.log_pow, Real.sqrt_mul (Nat.cast_nonneg j), mul_comm]
  have h1 : √(j : ℝ) ≤ √(n : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hjn)
  have h2 : √(n : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) := sqrt_le_rpow_two_thirds (by exact_mod_cast hn)
  exact mul_le_mul_of_nonneg_left (h1.trans h2) (Real.sqrt_nonneg _)

end L33
/-- **DGZ Lemma 3.2 at a dyadic band, `n^{2/3}` form**: for a continuous version of `h_j`
(`1 ≤ j ≤ n`) and two levels, `q_{p₂} ≤ e^{c n^{2/3}} q_{p₁}` with
`c = (quantileConst p₁ + quantileConst p₂) ξ √(log 2)`. -/
theorem IsBandVersion.lowerQuantile_le_exp_two_thirds_mul {d : ℕ} (hd : 0 < d) {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    (hW : IsWhiteNoise P W) {j n : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) {H : Rd d → Ω → ℝ}
    (hH : IsBandVersion P W κ ((2 : ℝ) ^ j)⁻¹ 1 H) {ξ : ℝ} (hξ : 0 < ξ) {p₁ p₂ : ℝ≥0∞}
    (hp₁0 : 0 < p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 < p₂) (hp₂1 : p₂ < 1) :
    LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H z ω)) p₂ ≤
      Real.exp ((Conc.quantileConst p₁.toReal + Conc.quantileConst p₂.toReal) * ξ *
          √(Real.log 2) * (n : ℝ) ^ (2 / 3 : ℝ)) *
        LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H z ω)) p₁ := by
  have hlt : ((2 : ℝ) ^ j)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by norm_num) (by omega))
  refine (hH.lowerQuantile_lfppDistance_le_exp_mul hd hκ hW (dyadic_pos j) hlt hξ hp₁0 hp₁1
    hp₂0 hp₂1).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
      (hH.lowerQuantile_lfppDistance_pos hd hW ξ hp₁0 hp₁1).le)
  have hc : 0 ≤ (Conc.quantileConst p₁.toReal + Conc.quantileConst p₂.toReal) * ξ :=
    mul_nonneg (add_nonneg (Conc.quantileConst_nonneg _) (Conc.quantileConst_nonneg _)) hξ.le
  have h := mul_le_mul_of_nonneg_left (sqrt_log_dyadic_le hjn (hj.trans hjn)) hc
  linarith

namespace L33

/-- From `exp(-x) ≤ q`: `1 ≤ exp(x) q`. -/
theorem one_le_exp_mul_of_exp_neg_le {x q : ℝ} (h : Real.exp (-x) ≤ q) : 1 ≤ Real.exp x * q := by
  have := mul_le_mul_of_nonneg_left h (Real.exp_pos x).le
  rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this

/-- Combination of two exponential bounds. -/
theorem le_exp_mul_mul_of_le {l Q R E₁ E₂ K : ℝ} (hQ : 0 ≤ Q) (h1 : l ≤ Real.exp E₁ * Q)
    (h2 : 1 ≤ Real.exp E₂ * R) (hK : E₁ + E₂ ≤ K) : l ≤ Real.exp K * Q * R := by
  calc l ≤ Real.exp E₁ * Q := h1
    _ ≤ Real.exp E₁ * Q * (Real.exp E₂ * R) := le_mul_of_one_le_right (by positivity) h2
    _ = Real.exp (E₁ + E₂) * Q * R := by rw [Real.exp_add]; ring
    _ ≤ Real.exp K * Q * R := by
        have hR : 0 ≤ R := by
          by_contra hR
          push Not at hR
          have : Real.exp E₂ * R < 0 := mul_neg_of_pos_of_neg (Real.exp_pos _) hR
          linarith
        gcongr

end L33

/-- **DGZ Lemma 3.3, remaining cases** (HA5 D9, "Remaining cases (G12)"): for every level
`p ∈ (0,1)` and threshold `m₀` there is `C ≥ 0` such that `λ_n ≤ e^{C n^{2/3}} a^{(p)}_m a^{(p)}_{n-m}`
whenever `1 ≤ m < n` and either `m < m₀` or `n ≤ m + ⌊(log m)²⌋`. Proof: DGZ Lemma 3.2
(`λ_n ≤ e^{c n^{2/3}} a^{(p)}_n`), Lemma 3.5 (`lemma35`) and the crude bounds
(`exists_crude_lowerQuantile_bounds`). -/
theorem lemma33_rest {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ : ℝ}
    (hξ : 0 < ξ) {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) (m₀ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {n m : ℕ}, 1 ≤ m → m < n → (m < m₀ ∨ n ≤ m + kpar m) →
      ∀ {H₁ H₂ H₃ : Rd d → Ω → ℝ},
        IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ 1 H₁ → IsBandVersion P W κ ((2 : ℝ) ^ m)⁻¹ 1 H₂ →
        IsBandVersion P W κ ((2 : ℝ) ^ (n - m))⁻¹ 1 H₃ →
        LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₁ z ω)) 2⁻¹ ≤
          Real.exp (C * (n : ℝ) ^ (2 / 3 : ℝ)) *
            LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω)) p *
            LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₃ z ω)) p := by
  have : NeZero d := ⟨by omega⟩
  have hd0 : 0 < d := by omega
  obtain ⟨A, hA0, hA⟩ := exists_crude_lowerQuantile_bounds hκ hp0 hp1
  obtain ⟨C₃₅, hC₃₅0, hC₃₅⟩ := lemma35 hκ hξ hp0 hp1
  have h20 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have h21 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 (by norm_num)
  set c₁ : ℝ := (Conc.quantileConst p.toReal + Conc.quantileConst (2⁻¹ : ℝ≥0∞).toReal) * ξ *
    √(Real.log 2) with hc₁
  have hc₁0 : 0 ≤ c₁ :=
    mul_nonneg (mul_nonneg (add_nonneg (Conc.quantileConst_nonneg _)
      (Conc.quantileConst_nonneg _)) hξ.le) (Real.sqrt_nonneg _)
  refine ⟨c₁ + C₃₅ * √(m₀ : ℝ) + ξ * A * m₀ + 6 * C₃₅ + 36 * ξ * A, by positivity, ?_⟩
  intro Ω _ P W hW n m hm hmn hcase H₁ H₂ H₃ h₁ h₂ h₃
  have := hW.isProbabilityMeasure
  have hn1 : 1 ≤ n := by omega
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn23 : 1 ≤ (n : ℝ) ^ (2 / 3 : ℝ) := one_le_rpow_two_thirds hn1'
  have hq₂0 := h₂.lowerQuantile_lfppDistance_pos hd0 hW ξ hp0 hp1
  have hq₃0 := h₃.lowerQuantile_lfppDistance_pos hd0 hW ξ hp0 hp1
  have hq₁0 := h₁.lowerQuantile_lfppDistance_pos hd0 hW ξ hp0 hp1
  -- DGZ Lemma 3.2: `λ_n ≤ e^{c₁ n^{2/3}} a^{(p)}_n`
  have hl : LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₁ z ω)) 2⁻¹ ≤
      Real.exp (c₁ * (n : ℝ) ^ (2 / 3 : ℝ)) *
        LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₁ z ω)) p :=
    h₁.lowerQuantile_le_exp_two_thirds_mul hd0 hκ hW hn1 le_rfl hξ hp0 hp1 h20 h21
  rcases hcase with hsmall | hmid
  · -- `m < m₀`: Lemma 3.5 at `(n, m)` and the crude lower bound for `a^{(p)}_m`
    obtain ⟨-, hup⟩ := hC₃₅ hW hW hm hmn h₁ h₃
    have hcr := one_le_exp_mul_of_exp_neg_le (hA ξ hW hm h₂).1
    have hl' := hl.trans (mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le)
    rw [← mul_assoc, ← Real.exp_add] at hl'
    have hK : c₁ * (n : ℝ) ^ (2 / 3 : ℝ) + C₃₅ * √((m : ℝ) * n) + |ξ| * A * m ≤
        (c₁ + C₃₅ * √(m₀ : ℝ) + ξ * A * m₀ + 6 * C₃₅ + 36 * ξ * A) * (n : ℝ) ^ (2 / 3 : ℝ) := by
      rw [abs_of_pos hξ]
      have hm0 : (m : ℝ) ≤ m₀ := by exact_mod_cast hsmall.le
      have h1 : √((m : ℝ) * n) ≤ √(m₀ : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg m)]
        exact mul_le_mul (Real.sqrt_le_sqrt hm0) (sqrt_le_rpow_two_thirds hn1')
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have h2 : ξ * A * m ≤ ξ * A * m₀ * (n : ℝ) ^ (2 / 3 : ℝ) := by
        have : ξ * A * m ≤ ξ * A * m₀ := mul_le_mul_of_nonneg_left hm0 (by positivity)
        have h0 : 0 ≤ ξ * A * m₀ := by positivity
        nlinarith
      have h3 := mul_le_mul_of_nonneg_left h1 hC₃₅0
      have h4 : 0 ≤ (6 * C₃₅ + 36 * ξ * A) * (n : ℝ) ^ (2 / 3 : ℝ) := by positivity
      nlinarith
    have := le_exp_mul_mul_of_le hq₃0.le hl' hcr hK
    linarith [mul_right_comm (Real.exp ((c₁ + C₃₅ * √(m₀ : ℝ) + ξ * A * m₀ + 6 * C₃₅ +
      36 * ξ * A) * (n : ℝ) ^ (2 / 3 : ℝ)))
      (LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₃ z ω)) p)
      (LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω)) p)]
  · -- `n ≤ m + k`: Lemma 3.5 at `(n, n - m)` and the crude lower bound for `a^{(p)}_{n-m}`
    have h₂' : IsBandVersion P W κ ((2 : ℝ) ^ (n - (n - m)))⁻¹ 1 H₂ :=
      h₂.congr_band (by rw [Nat.sub_sub_self hmn.le]) rfl
    obtain ⟨-, hup⟩ := hC₃₅ hW hW (m := n - m) (n := n) (by omega) (by omega) h₁ h₂'
    have hcr := one_le_exp_mul_of_exp_neg_le (hA ξ hW (n := n - m) (by omega) h₃).1
    have hl' := hl.trans (mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le)
    rw [← mul_assoc, ← Real.exp_add] at hl'
    have hK : c₁ * (n : ℝ) ^ (2 / 3 : ℝ) + C₃₅ * √(((n - m : ℕ) : ℝ) * n) +
        |ξ| * A * ((n - m : ℕ) : ℝ) ≤
        (c₁ + C₃₅ * √(m₀ : ℝ) + ξ * A * m₀ + 6 * C₃₅ + 36 * ξ * A) * (n : ℝ) ^ (2 / 3 : ℝ) := by
      rw [abs_of_pos hξ]
      have hnmk : ((n - m : ℕ) : ℝ) ≤ kpar m := by exact_mod_cast (by omega : n - m ≤ kpar m)
      have h1 : √(((n - m : ℕ) : ℝ) * n) ≤ 6 * (n : ℝ) ^ (2 / 3 : ℝ) :=
        (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hnmk (Nat.cast_nonneg n))).trans
          (sqrt_kpar_mul_le hm hmn.le)
      have h2 : ((n - m : ℕ) : ℝ) ≤ 36 * (n : ℝ) ^ (2 / 3 : ℝ) :=
        hnmk.trans (kpar_le_two_thirds hm hmn.le)
      have h3 := mul_le_mul_of_nonneg_left h1 hC₃₅0
      have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ ξ * A)
      have h5 : 0 ≤ (C₃₅ * √(m₀ : ℝ) + ξ * A * m₀) * (n : ℝ) ^ (2 / 3 : ℝ) := by positivity
      nlinarith
    exact le_exp_mul_mul_of_le hq₂0.le hl' hcr hK

/-- **DGZ Lemma 3.3 for probability spaces in `Type`** (HA5 D9): main case and remaining cases. -/
theorem lemma33_type0 {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ : ℝ}
    (hξ : 0 < ξ) :
    ∃ p : ℝ≥0∞, 0 < p ∧ p < 1 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {n m : ℕ}, 1 ≤ m → m < n → ∀ {H₁ H₂ H₃ : Rd d → Ω → ℝ},
        IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ 1 H₁ → IsBandVersion P W κ ((2 : ℝ) ^ m)⁻¹ 1 H₂ →
        IsBandVersion P W κ ((2 : ℝ) ^ (n - m))⁻¹ 1 H₃ →
        LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₁ z ω)) 2⁻¹ ≤
          Real.exp (C * (n : ℝ) ^ (2 / 3 : ℝ)) *
            LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω)) p *
            LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₃ z ω)) p := by
  have hd0 : 0 < d := by omega
  obtain ⟨p, hp0, hp1, m₀, -, C₁, hC₁0, hC₁⟩ := lemma33_main hd hκ hξ
  obtain ⟨C₂, hC₂0, hC₂⟩ := lemma33_rest hd hκ hξ hp0 hp1 m₀
  refine ⟨p, hp0, hp1, C₁ + C₂, by positivity, ?_⟩
  intro Ω _ P W hW n m hm hmn H₁ H₂ H₃ h₁ h₂ h₃
  have hq₂0 := h₂.lowerQuantile_lfppDistance_pos hd0 hW ξ hp0 hp1
  have hq₃0 := h₃.lowerQuantile_lfppDistance_pos hd0 hW ξ hp0 hp1
  have hn23 : 0 ≤ (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hmono : ∀ C' : ℝ, C' ≤ C₁ + C₂ →
      Real.exp (C' * (n : ℝ) ^ (2 / 3 : ℝ)) *
          LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω)) p *
          LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₃ z ω)) p ≤
        Real.exp ((C₁ + C₂) * (n : ℝ) ^ (2 / 3 : ℝ)) *
          LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω)) p *
          LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₃ z ω)) p := by
    intro C' hC'
    gcongr
  by_cases hcase : m₀ ≤ m ∧ m + kpar m < n
  · exact (hC₁ hW hcase.1 hcase.2 h₁ h₂ h₃).trans (hmono C₁ (by linarith))
  · have hor : m < m₀ ∨ n ≤ m + kpar m := by omega
    exact (hC₂ hW hm hmn hor h₁ h₂ h₃).trans (hmono C₂ (by linarith))

/-- **DGZ Lemma 3.3** (HA5 D9; target T1 of packet P-X8). For `d ≥ 2`, an admissible kernel `κ`
and `ξ > 0` there are a level `p* ∈ (0,1)` and `C ≥ 0` (depending only on `d`, `κ`, `ξ`) such
that for all `n > m ≥ 1`, every white noise `W` (on any probability space) and continuous versions
`H₁`, `H₂`, `H₃` of `h_n`, `h_m`, `h_{n-m}`,
`λ_n ≤ e^{C n^{2/3}} a^{(p*)}_m a^{(p*)}_{n-m}`, where `λ_n` is the lower median of
`D_n = D^ξ(h_n)` and `a^{(p*)}_j` the lower `p*`-quantile of `D_j`. -/
theorem lemma33 {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ : ℝ}
    (hξ : 0 < ξ) :
    ∃ p : ℝ≥0∞, 0 < p ∧ p < 1 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {n m : ℕ}, 1 ≤ m → m < n → ∀ {H₁ H₂ H₃ : Rd d → Ω → ℝ},
        IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ 1 H₁ → IsBandVersion P W κ ((2 : ℝ) ^ m)⁻¹ 1 H₂ →
        IsBandVersion P W κ ((2 : ℝ) ^ (n - m))⁻¹ 1 H₃ →
        LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₁ z ω)) 2⁻¹ ≤
          Real.exp (C * (n : ℝ) ^ (2 / 3 : ℝ)) *
            LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω)) p *
            LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₃ z ω)) p := by
  obtain ⟨p, hp0, hp1, C, hC0, hC⟩ := lemma33_type0 hd hκ hξ
  refine ⟨p, hp0, hp1, C, hC0, ?_⟩
  intro Ω _ P W hW n m hm hmn H₁ H₂ H₃ h₁ h₂ h₃
  obtain ⟨Ω₀, _, P₀, W₀, -, -, hW₀, -⟩ := (field_exists_impl d (by omega)).2 κ hκ
  obtain ⟨G₁, hG₁⟩ := exists_isBandVersion hκ hW₀ (dyadic_pos n) 1
  obtain ⟨G₂, hG₂⟩ := exists_isBandVersion hκ hW₀ (dyadic_pos m) 1
  obtain ⟨G₃, hG₃⟩ := exists_isBandVersion hκ hW₀ (dyadic_pos (n - m)) 1
  rw [h₁.lowerQuantile_lfppDistance_eq hG₁ hW hW₀ ξ 2⁻¹,
    h₂.lowerQuantile_lfppDistance_eq hG₂ hW hW₀ ξ p,
    h₃.lowerQuantile_lfppDistance_eq hG₃ hW hW₀ ξ p]
  exact hC hW₀ hm hmn hG₁ hG₂ hG₃

/-- **DGZ Lemma 3.3, median form** (HA5 D9 with D3): for `d ≥ 2`, an admissible kernel `κ` and
`ξ > 0` there is `C ≥ 0` such that for all `n > m ≥ 1`, every white noise and continuous versions
`H₁`, `H₂`, `H₃` of `h_n`, `h_m`, `h_{n-m}`, `λ_n ≤ e^{C n^{2/3}} λ_m λ_{n-m}`. -/
theorem lemma33_median {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ : ℝ}
    (hξ : 0 < ξ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {n m : ℕ}, 1 ≤ m → m < n → ∀ {H₁ H₂ H₃ : Rd d → Ω → ℝ},
        IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ 1 H₁ → IsBandVersion P W κ ((2 : ℝ) ^ m)⁻¹ 1 H₂ →
        IsBandVersion P W κ ((2 : ℝ) ^ (n - m))⁻¹ 1 H₃ →
        LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₁ z ω)) 2⁻¹ ≤
          Real.exp (C * (n : ℝ) ^ (2 / 3 : ℝ)) *
            LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω)) 2⁻¹ *
            LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₃ z ω)) 2⁻¹ := by
  have hd0 : 0 < d := by omega
  obtain ⟨p, hp0, hp1, C, hC0, hC⟩ := lemma33 hd hκ hξ
  have h20 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have h21 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 (by norm_num)
  set c₂ : ℝ := (Conc.quantileConst (2⁻¹ : ℝ≥0∞).toReal + Conc.quantileConst p.toReal) * ξ *
    √(Real.log 2) with hc₂
  have hc₂0 : 0 ≤ c₂ :=
    mul_nonneg (mul_nonneg (add_nonneg (Conc.quantileConst_nonneg _)
      (Conc.quantileConst_nonneg _)) hξ.le) (Real.sqrt_nonneg _)
  refine ⟨C + 2 * c₂, by positivity, ?_⟩
  intro Ω _ P W hW n m hm hmn H₁ H₂ H₃ h₁ h₂ h₃
  have h := hC hW hm hmn h₁ h₂ h₃
  have e₂ := h₂.lowerQuantile_le_exp_two_thirds_mul hd0 hκ hW hm hmn.le hξ h20 h21 hp0 hp1
  have e₃ := h₃.lowerQuantile_le_exp_two_thirds_mul hd0 hκ hW (j := n - m) (by omega)
    (Nat.sub_le n m) hξ h20 h21 hp0 hp1
  have hl₂ := h₂.lowerQuantile_lfppDistance_pos hd0 hW ξ h20 h21
  have hl₃ := h₃.lowerQuantile_lfppDistance_pos hd0 hW ξ h20 h21
  have hq₂ := h₂.lowerQuantile_lfppDistance_pos hd0 hW ξ hp0 hp1
  have hq₃ := h₃.lowerQuantile_lfppDistance_pos hd0 hW ξ hp0 hp1
  calc LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₁ z ω)) 2⁻¹
      ≤ Real.exp (C * (n : ℝ) ^ (2 / 3 : ℝ)) *
          LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω)) p *
          LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₃ z ω)) p := h
    _ ≤ Real.exp (C * (n : ℝ) ^ (2 / 3 : ℝ)) *
          (Real.exp (c₂ * (n : ℝ) ^ (2 / 3 : ℝ)) *
            LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω)) 2⁻¹) *
          (Real.exp (c₂ * (n : ℝ) ^ (2 / 3 : ℝ)) *
            LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₃ z ω))
              2⁻¹) := by
        gcongr
    _ = Real.exp ((C + 2 * c₂) * (n : ℝ) ^ (2 / 3 : ℝ)) *
          LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₂ z ω)) 2⁻¹ *
          LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H₃ z ω)) 2⁻¹ := by
        have e : (C + 2 * c₂) * (n : ℝ) ^ (2 / 3 : ℝ) =
            (C * (n : ℝ) ^ (2 / 3 : ℝ) + c₂ * (n : ℝ) ^ (2 / 3 : ℝ)) +
              c₂ * (n : ℝ) ^ (2 / 3 : ℝ) := by ring
        rw [e, Real.exp_add, Real.exp_add]
        ring

end HigherDimLFPP
