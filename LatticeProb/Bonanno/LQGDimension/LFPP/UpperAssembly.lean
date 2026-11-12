/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.UpperAssembly at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.UpperAssemblyAux2

/-!
# Conditional assembly of the upper bound (1.7)

We prove `Blueprint.Draft.UpperAssembly`: the node statements of Section 4 (and `P1`, `L37`,
`EX`, `ZL`) imply `Blueprint.Prop12Upper`.

Outline (paper §4.3).  Fix `n`, `M = 16ⁿ`, `η > 0`, and put `δ = ξ^{2/3}`.

* **Mean bounds.**  `m_δ(k)` is the supremum of the normalized log-kernel expected maxima over
  all finite subfamilies of the local families of bin `k` (`meanBound`); by `RecordMeanCrude`
  it is at most `C_n (k+1)^{1/4} - k` for `δ ∈ (0,1)`, and by `RecordMeanLimit` it satisfies
  the limiting bound (4.6) (large-excess bins disappear for small `δ`).  With
  `RecordMeanTransfer` it bounds the local-supremum means of every record.
* **Chain bound.**  `ChainUnionBound`, fed with the counts of `RecordSystem.Good`, the mean
  bound, the variance bound of `RecordVariance` (through `SegCombLaw`), and the summability of
  the series (4.8), gives `P(bad chain of length l) ≤ e^{-l}` with `B = (log Z + 1)/t`.
* **Deterministic step** (`det_bound`).  On the good event, `PathTreeExists`,
  `TreeInequality`, `RecordAssignment` and `ChainLengthBounds` give
  `log D_ε ≥ ξ H_root - ξ osc - δ² B⁺ (log(1/ε)/log(2M/3) + 1)`.
* **Probability** (`prob_tendsto`).  With `Oscillation37`, `log D_ε / log ε ≤ δ² B⁺/log(2M/3) + θ`
  outside an event of probability `→ 0`; `ExponentFromProb` gives `λ ≤ δ² B⁺ / log(2M/3)`.
* **Conclusion.**  `ZLimitBound` bounds `B` for small `δ`, and `δ² = ξ^{4/3}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped Classical

namespace LQGDimension

namespace UpperAssemblyAux

open Blueprint.Draft

/-! ### Shapes of the node statements at fixed parameters -/

/-- `RecordMeanCrude` at a fixed `n` with constant `Cn`. -/
def CrudeAt (n : ℕ) (Cn : ℝ) : Prop :=
  ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ (large : Bool) (k : ℕ),
    (large = true → k = ⌊δ ^ (-2 : ℤ)⌋₊) →
    ∀ F : Finset Config, F.Nonempty → ↑F ⊆ localFamily (16 ^ n) δ large k →
      gaussianExpectedMax F (fun c c' => δ⁻¹ * (cfgComb c).logCov (cfgComb c'))
          (fun _ => -(k : ℝ)) ≤ Cn * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k

/-- `RecordMeanLimit` at a fixed `n` with constant `C`. -/
def LimitAt (n : ℕ) (C : ℝ) : Prop :=
  ∀ k : ℕ, ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0,
    ∀ F : Finset Config, F.Nonempty → ↑F ⊆ smallFamily (16 ^ n) δ k →
      gaussianExpectedMax F (fun c c' => δ⁻¹ * (cfgComb c).logCov (cfgComb c'))
          (fun _ => -(k : ℝ)) ≤
        min (a n + C) (C * (n : ℝ) ^ (3 / 4 : ℝ) * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k + C) + θ

/-- `RecordVariance` at fixed `n, δ, ε` with constants `C, c₀`. -/
def VarAt (n : ℕ) (δ ε C c₀ : ℝ) : Prop :=
  ∀ l : ℕ, ∀ (s : ℕ → ℂ × ℂ) (large : ℕ → Bool) (k : ℕ → ℕ) (c : ℕ → Config),
    (∀ i < l, (s i).1 ≠ 0) →
    (∀ i, i + 1 < l → ‖(s (i + 1)).1‖ ≤ 4 / (16 : ℝ) ^ n * ‖(s i).1‖) →
    (∀ i < l, large i = true → k i = ⌊δ ^ (-2 : ℤ)⌋₊) →
    (∀ i < l, c i ∈ cfgMap (s i) '' localFamily (16 ^ n) δ (large i) (k i)) →
    δ⁻¹ * (sumComb c l).circCov ε (sumComb c l) ≤
      C * ∑ i ∈ Finset.range l, gFactor (16 ^ n) δ c₀ (k i) ^ 2 * Real.sqrt ((k i : ℝ) + 1)

/-- `ChainUnionBound` at fixed `κ, P, h, ε, δ`. -/
def ChainAt {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ)
    (κ ε δ : ℝ) : Prop :=
  ∀ (RS : RecordSystem) (N m v : ℕ → ℝ),
    (∀ k, (Set.ncard {r | RS.isRoot r ∧ RS.bin r = k} : ℝ) ≤ N k) →
    (∀ r k, (Set.ncard {r' | RS.next r r' ∧ RS.bin r' = k} : ℝ) ≤ N k) →
    (∀ r, ∀ c ∈ RS.family r, 0 < polyLen c.1 ∧ 0 < polyLen c.2) →
    (∀ r, ∀ F : Finset Config, F.Nonempty → ↑F ⊆ RS.family r →
      ∫ ω, (⨆ c : F, cfgVal (fun z => h ε z ω) δ (RS.bin r) c) ∂P ≤ m (RS.bin r)) →
    (∀ (l : ℕ) (r : ℕ → RS.Rec) (c : ℕ → Config), RS.IsChain r l →
      (∀ i < l, c i ∈ RS.family (r i)) →
      Var[fun ω => ∑ i ∈ Finset.range l, cfgVal (fun z => h ε z ω) δ (RS.bin (r i)) (c i); P] ≤
        ∑ i ∈ Finset.range l, v (RS.bin (r i))) →
    ∀ t > 0, Summable (fun k => N k * Real.exp (t * m k + κ * t ^ 2 * v k)) →
    ∀ l : ℕ, P {ω | ∃ (r : ℕ → RS.Rec) (c : ℕ → Config), RS.IsChain r l ∧
        (∀ i < l, c i ∈ RS.family (r i)) ∧
        (Real.log (chainZ N m v κ t) + 1) / t * l <
          ∑ i ∈ Finset.range l, cfgVal (fun z => h ε z ω) δ (RS.bin (r i)) (c i)} ≤
      ENNReal.ofReal (Real.exp (-(l : ℝ)))

/-- The record-assignment property of `RecordAssignment` for a given record system. -/
def AssignAt (RS : RecordSystem) (M : ℕ) (δ ε : ℝ) : Prop :=
  ∀ γ : ℝ → ℂ, IsAdmissiblePath γ → ∀ T : CutTree, T.WF γ M ε →
    ∀ φ : ℂ → ℝ, Continuous φ → ∀ v ∈ T.leaves,
      ∃ (r : ℕ → RS.Rec) (c : ℕ → Config), RS.IsChain r v.length ∧
        ∀ j < v.length, c j ∈ RS.family (r j) ∧ RS.bin (r j) = T.kbin γ δ (v.take j) ∧
          δ ^ (-(1 / 2 : ℝ)) * T.G γ φ (v.take j) - T.kbin γ δ (v.take j) ≤
            cfgVal φ δ (RS.bin (r j)) (c j)

/-- Counts `N(k) = C M^D (k+1)^D` of (4.8). -/
abbrev cntN (n : ℕ) (C D : ℝ) : ℕ → ℝ := fun k => C * ((16 : ℝ) ^ n) ^ D * ((k : ℝ) + 1) ^ D

/-- Variance bounds `v(k) = C g(k)² √(k+1)` of (4.7)–(4.8). -/
abbrev varV (n : ℕ) (δ c₀ C : ℝ) : ℕ → ℝ :=
  fun k => C * gFactor (16 ^ n) δ c₀ k ^ 2 * Real.sqrt ((k : ℝ) + 1)

/-! ### The mean bounds `m_δ(k)` -/

/-- The normalized log-kernel expected maxima over finite subfamilies of the local families of
bin `k` (large-excess families only when `k = ⌊δ^{-2}⌋`). -/
def meanSet (n : ℕ) (δ : ℝ) (k : ℕ) : Set ℝ :=
  {x | ∃ (large : Bool) (F : Finset Config), (large = true → k = ⌊δ ^ (-2 : ℤ)⌋₊) ∧
    F.Nonempty ∧ ↑F ⊆ localFamily (16 ^ n) δ large k ∧
    x = gaussianExpectedMax F (fun c c' => δ⁻¹ * (cfgComb c).logCov (cfgComb c'))
      (fun _ => -(k : ℝ))}

/-- Value of `m_δ(k)` for bins without any local family (harmless: such bins carry no
records). -/
def meanFloor (n : ℕ) (Cn C : ℝ) (k : ℕ) : ℝ :=
  min (Cn * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k)
    (min (a n + C) (C * (n : ℝ) ^ (3 / 4 : ℝ) * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k + C))

/-- The common mean bound `m_δ(k)` of Lemma 4.1, defined for every `δ`. -/
def meanBound (n : ℕ) (Cn C δ : ℝ) (k : ℕ) : ℝ :=
  if (meanSet n δ k).Nonempty then sSup (meanSet n δ k) else meanFloor n Cn C k

theorem meanSet_le {n : ℕ} {Cn : ℝ} (hCn : CrudeAt n Cn) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (k : ℕ) : ∀ x ∈ meanSet n δ k, x ≤ Cn * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k := by
  rintro x ⟨large, F, hl, hF, hFs, rfl⟩
  exact hCn δ hδ large k hl F hF hFs

theorem meanBound_crude {n : ℕ} {Cn : ℝ} (hCn : CrudeAt n Cn) (C : ℝ) {δ : ℝ}
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    meanBound n Cn C δ k ≤ Cn * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k := by
  unfold meanBound
  split_ifs with hne
  · exact csSup_le hne (meanSet_le hCn hδ k)
  · exact min_le_left _ _

theorem le_meanBound {n : ℕ} {Cn : ℝ} (hCn : CrudeAt n Cn) (C : ℝ) {δ : ℝ}
    (hδ : δ ∈ Ioo (0 : ℝ) 1) {k : ℕ} {x : ℝ} (hx : x ∈ meanSet n δ k) :
    x ≤ meanBound n Cn C δ k := by
  unfold meanBound
  rw [ite_eq_left (show (meanSet n δ k).Nonempty from ⟨x, hx⟩)]
  exact le_csSup ⟨_, meanSet_le hCn hδ k⟩ hx

theorem eventually_lt_floor (k : ℕ) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), k < ⌊δ ^ (-2 : ℤ)⌋₊ := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
  have hδ0 := hδ.1
  have hk2 : 1 / ((k : ℝ) + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hδ1 : δ < 1 := lt_of_lt_of_le hδ.2 hk2
  apply Nat.lt_of_succ_le
  apply Nat.le_floor
  have e : δ ^ (-2 : ℤ) = (δ ^ 2)⁻¹ := by rw [zpow_neg, zpow_two, sq]
  rw [e]
  push_cast
  rw [le_inv_comm₀ (by positivity) (by positivity)]
  have h1 : δ ^ 2 ≤ δ := by nlinarith
  have h2 : 1 / ((k : ℝ) + 2) ≤ ((k : ℝ) + 1)⁻¹ := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith [hδ.2]

theorem meanBound_limit {n : ℕ} {Cn C : ℝ} (hL : LimitAt n C) :
    ∀ k : ℕ, ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0, meanBound n Cn C δ k ≤
      min (a n + C) (C * (n : ℝ) ^ (3 / 4 : ℝ) * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k + C) + θ := by
  intro k θ hθ
  filter_upwards [hL k θ hθ, eventually_lt_floor k] with δ hδL hfl
  unfold meanBound
  split_ifs with hne
  · refine csSup_le hne ?_
    rintro x ⟨large, F, hl, hF, hFs, rfl⟩
    cases large with
    | true => exact absurd (hl rfl) (Nat.ne_of_lt hfl)
    | false =>
      apply hδL F hF
      simpa [localFamily] using hFs
  · exact (min_le_right _ _).trans (le_add_of_nonneg_right hθ.le)

/-! ### The hypotheses of `ChainUnionBound` for a good record system -/

theorem sixteen_le_pow {n : ℕ} (hn : 1 ≤ n) : 16 ≤ 16 ^ n :=
  calc 16 = 16 ^ 1 := by norm_num
    _ ≤ 16 ^ n := Nat.pow_le_pow_right (by norm_num) hn

/-- Mean hypothesis: the local-supremum means of every record are bounded by `m_δ(bin)`. -/
theorem mean_hyp (hMT : RecordMeanTransfer) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : ℝ → ℂ → Ω → ℝ} (hG : IsGFFCircleAverage h P) {n : ℕ} (hn : 1 ≤ n) {Cn : ℝ}
    (hCn : CrudeAt n Cn) (C : ℝ) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε)
    (RS : RecordSystem) (hsim : ∀ r, (RS.sim r).1 ≠ 0)
    (hfam : ∀ r, RS.family r ⊆
      cfgMap (RS.sim r) '' localFamily (16 ^ n) δ (RS.large r) (RS.bin r))
    (hbin : ∀ r, RS.large r = true → RS.bin r = ⌊δ ^ (-2 : ℤ)⌋₊) :
    ∀ r, ∀ F : Finset Config, F.Nonempty → ↑F ⊆ RS.family r →
      ∫ ω, (⨆ c : F, cfgVal (fun z => h ε z ω) δ (RS.bin r) c) ∂P ≤
        meanBound n Cn C δ (RS.bin r) := by
  intro r F hF hFs
  have hpre : ∀ c ∈ F, c ∈ cfgMap (RS.sim r) ''
      localFamily (16 ^ n) δ (RS.large r) (RS.bin r) := fun c hc => hfam r (hFs hc)
  let g : Config → Config := fun c =>
    if hc : c ∈ cfgMap (RS.sim r) '' localFamily (16 ^ n) δ (RS.large r) (RS.bin r)
    then hc.choose else c
  have hg : ∀ c ∈ F, g c ∈ localFamily (16 ^ n) δ (RS.large r) (RS.bin r) ∧
      cfgMap (RS.sim r) (g c) = c := by
    intro c hc
    have hc' := hpre c hc
    have e : g c = hc'.choose := dite_eq_left hc'
    rw [e]
    exact hc'.choose_spec
  have hF₀L : ∀ c ∈ F.image g, c ∈ localFamily (16 ^ n) δ (RS.large r) (RS.bin r) := by
    intro c hc
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hc
    exact (hg c' hc').1
  have hF₀img : (F.image g).image (cfgMap (RS.sim r)) = F := by
    ext c
    simp only [Finset.image_image, Finset.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨c', hc', rfl⟩
      rw [(hg c' hc').2]
      exact hc'
    · intro hc
      exact ⟨c, hc, (hg c hc).2⟩
  have hpos : ∀ c ∈ F.image g, 0 < polyLen c.1 ∧ 0 < polyLen c.2 :=
    fun c hc => localFamily_polyLen_pos (sixteen_le_pow hn) hδ (hF₀L c hc)
  have hmt := hMT Ω P h hG ε hε δ hδ.1 (RS.sim r) (hsim r) (RS.bin r) (F.image g) hpos
  rw [hF₀img] at hmt
  refine hmt.trans (le_meanBound hCn C hδ ⟨RS.large r, F.image g, hbin r, hF.image g, ?_, rfl⟩)
  intro c hc
  exact hF₀L c hc

theorem gFactor_sq_le {M : ℕ} (hM : 1 ≤ M) (δ c₀ : ℝ) (k : ℕ) :
    gFactor M δ c₀ k ^ 2 ≤ (M : ℝ) ^ 2 := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  unfold gFactor
  split_ifs
  · nlinarith
  · exact le_refl _

/-- The chain union bound for a good record system, with the explicit `N, m, v` of (4.8). -/
theorem chain_prob (hP1 : SegCombLaw) (hMT : RecordMeanTransfer) {κ : ℝ} (hκ : 0 < κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : ℝ → ℂ → Ω → ℝ}
    (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hU : ChainAt P h κ ε δ) {n : ℕ} (hn : 1 ≤ n) {CV c₀ : ℝ} (hV : VarAt n δ ε CV c₀)
    {Cn CL : ℝ} (hCn : CrudeAt n Cn) {CR DR : ℝ} (RS : RecordSystem)
    (hGood : RS.Good (16 ^ n) δ CR DR) (l : ℕ) :
    P {ω | ∃ (r : ℕ → RS.Rec) (c : ℕ → Config), RS.IsChain r l ∧
        (∀ i < l, c i ∈ RS.family (r i)) ∧
        (Real.log (chainZ (cntN n (max CR 1) (max DR 0)) (meanBound n Cn CL δ)
            (varV n δ c₀ (max CV 0)) κ ((n : ℝ) ^ (1 / 4 : ℝ))) + 1) /
            ((n : ℝ) ^ (1 / 4 : ℝ)) * l <
          ∑ i ∈ Finset.range l, cfgVal (fun z => h ε z ω) δ (RS.bin (r i)) (c i)} ≤
      ENNReal.ofReal (Real.exp (-(l : ℝ))) := by
  obtain ⟨hsim, hfam, hbin, hnext, hroot, hnextc⟩ := hGood
  have hM16 := sixteen_le_pow hn
  have h16 : (1 : ℝ) ≤ (16 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hC2 : 0 < max CR 1 := lt_max_of_lt_right one_pos
  have hcnt : ∀ k : ℕ, CR * (((16 ^ n : ℕ) : ℝ)) ^ DR * ((k : ℝ) + 1) ^ DR ≤
      cntN n (max CR 1) (max DR 0) k := by
    intro k
    simp only [cntN]
    push_cast
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) k; linarith
    have e1 : ((16 : ℝ) ^ n) ^ DR ≤ ((16 : ℝ) ^ n) ^ (max DR 0) :=
      Real.rpow_le_rpow_of_exponent_le h16 (le_max_left _ _)
    have e2 : ((k : ℝ) + 1) ^ DR ≤ ((k : ℝ) + 1) ^ (max DR 0) :=
      Real.rpow_le_rpow_of_exponent_le hk (le_max_left _ _)
    have p1 : 0 ≤ ((16 : ℝ) ^ n) ^ DR := by positivity
    have p2 : 0 ≤ ((k : ℝ) + 1) ^ DR := by positivity
    have p3 : 0 ≤ ((16 : ℝ) ^ n) ^ (max DR 0) := by positivity
    calc CR * ((16 : ℝ) ^ n) ^ DR * ((k : ℝ) + 1) ^ DR
        ≤ max CR 1 * ((16 : ℝ) ^ n) ^ DR * ((k : ℝ) + 1) ^ DR :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) p1) p2
      _ ≤ max CR 1 * ((16 : ℝ) ^ n) ^ (max DR 0) * ((k : ℝ) + 1) ^ (max DR 0) :=
          mul_le_mul (mul_le_mul_of_nonneg_left e1 hC2.le) e2 p2 (mul_nonneg hC2.le p3)
  have ht : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.rpow_pos_of_pos this _
  refine hU RS (cntN n (max CR 1) (max DR 0)) (meanBound n Cn CL δ) (varV n δ c₀ (max CV 0))
    (fun k => (hroot k).trans (hcnt k)) (fun r k => (hnextc r k).trans (hcnt k))
    (fun r c hc => cfgMap_polyLen_pos hM16 hδ (hsim r) (hfam r hc))
    (mean_hyp hMT hG hn hCn CL hδ hε RS hsim hfam hbin) ?_ _ ht ?_ l
  · -- variance
    intro l r c hch hc
    have h1 := variance_chain_le hP1 hG hε hδ.1 (fun i => RS.bin (r i)) c l
    have h2 := hV l (fun i => RS.sim (r i)) (fun i => RS.large (r i)) (fun i => RS.bin (r i)) c
      (fun i _ => hsim _)
      (fun i hi => by
        have := hnext _ _ (hch.2 i hi)
        push_cast at this
        exact this)
      (fun i _ => hbin _) (fun i hi => hfam _ (hc i hi))
    have hS : 0 ≤ ∑ i ∈ Finset.range l,
        gFactor (16 ^ n) δ c₀ (RS.bin (r i)) ^ 2 * Real.sqrt ((RS.bin (r i) : ℝ) + 1) :=
      Finset.sum_nonneg (fun i _ => by positivity)
    calc Var[fun ω => ∑ i ∈ Finset.range l,
            cfgVal (fun z => h ε z ω) δ (RS.bin (r i)) (c i); P]
        ≤ max (δ⁻¹ * (sumComb c l).circCov ε (sumComb c l)) 0 := h1
      _ ≤ max CV 0 * ∑ i ∈ Finset.range l,
            gFactor (16 ^ n) δ c₀ (RS.bin (r i)) ^ 2 * Real.sqrt ((RS.bin (r i) : ℝ) + 1) :=
          max_le (h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hS))
            (mul_nonneg (le_max_right _ _) hS)
      _ = ∑ i ∈ Finset.range l, varV n δ c₀ (max CV 0) (RS.bin (r i)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [varV]
          ring
  · -- summability
    have hb : 0 ≤ κ * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * (max CV 0 * ((16 : ℝ) ^ n) ^ 2) :=
      mul_nonneg (by positivity) (mul_nonneg (le_max_right _ _) (by positivity))
    refine summable_chain_terms (max CR 1 * ((16 : ℝ) ^ n) ^ (max DR 0)) (max DR 0) Cn
      (κ * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * (max CV 0 * ((16 : ℝ) ^ n) ^ 2)) κ _
      (mul_nonneg hC2.le (by positivity)) hb ht _ _
      (fun k => meanBound_crude hCn CL hδ k) (fun k => ?_)
    have hg := gFactor_sq_le (Nat.one_le_iff_ne_zero.2 (by positivity)) δ c₀ k (M := 16 ^ n)
    push_cast at hg
    have hK : 0 ≤ κ * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * max CV 0 :=
      mul_nonneg (by positivity) (le_max_right _ _)
    calc κ * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * varV n δ c₀ (max CV 0) k
        = (κ * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * max CV 0) * gFactor (16 ^ n) δ c₀ k ^ 2 *
            Real.sqrt ((k : ℝ) + 1) := by simp only [varV]; ring
      _ ≤ (κ * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * max CV 0) * ((16 : ℝ) ^ n) ^ 2 *
            Real.sqrt ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hK) (Real.sqrt_nonneg _)
      _ = κ * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * (max CV 0 * ((16 : ℝ) ^ n) ^ 2) *
            Real.sqrt ((k : ℝ) + 1) := by ring

/-! ### The deterministic step -/

/-- On the event where every chain of length at least `⌈log(1/ε)/log(2M)⌉` has local sum at most
`B l`, the LFPP distance satisfies
`log D ≥ ξ H_root - ξ ω_ε - δ² B⁺ (log(1/ε)/log(2M/3) + 1)`, `ξ = δ^{3/2}`. -/
theorem det_bound (hT41 : PathTreeExists) (hCL : ChainLengthBounds) (hJ42 : TreeInequality)
    {M : ℕ} (hM : 16 ≤ M) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) {δ : ℝ} (hδ : 0 < δ)
    (RS : RecordSystem) (hRA : AssignAt RS M δ ε)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (B : ℝ)
    (hgood : ∀ l : ℕ, ⌈Real.log (1 / ε) / Real.log (2 * M)⌉₊ ≤ l →
      ∀ (r : ℕ → RS.Rec) (c : ℕ → Config), RS.IsChain r l →
        (∀ i < l, c i ∈ RS.family (r i)) →
        ∑ i ∈ Finset.range l, cfgVal φ δ (RS.bin (r i)) (c i) ≤ B * l) :
    δ ^ (3 / 2 : ℝ) * segAvg φ 0 1 - δ ^ (3 / 2 : ℝ) * osc φ (8 * ε)
        - δ ^ 2 * (max B 0 * (Real.log (1 / ε) / Real.log (2 * M / 3) + 1)) ≤
      Real.log (lfppDistance (δ ^ (3 / 2 : ℝ)) φ) := by
  have hpath : ∀ γ : ℝ → ℂ, IsAdmissiblePath γ →
      Real.exp (δ ^ (3 / 2 : ℝ) * segAvg φ 0 1 - δ ^ (3 / 2 : ℝ) * osc φ (8 * ε)
        - δ ^ 2 * (max B 0 * (Real.log (1 / ε) / Real.log (2 * M / 3) + 1))) ≤
        lfppLength (δ ^ (3 / 2 : ℝ)) φ γ := by
    intro γ hγ
    obtain ⟨T, hT⟩ := hT41 γ hγ M hM ε hε
    obtain ⟨hpos, hineq, hflow0, hflow1⟩ := hJ42 γ hγ M hM ε hε T hT φ hφ δ hδ
    have hCLv := hCL γ hγ M hM ε hε T hT
    have hH : T.H γ φ [] = segAvg φ 0 1 := by
      simp only [CutTree.H, CutTree.x, CutTree.y, hT.root_time.1, hT.root_time.2, hγ.source,
        hγ.target]
    have hS : ∀ v ∈ T.leaves, ∑ j ∈ Finset.range v.length,
        (δ ^ (-(1 / 2 : ℝ)) * T.G γ φ (v.take j) - T.kbin γ δ (v.take j)) ≤
          max B 0 * (Real.log (1 / ε) / Real.log (2 * M / 3) + 1) := by
      intro v hv
      obtain ⟨r, c, hch, hrc⟩ := hRA γ hγ T hT φ hφ v hv
      have hlen := hCLv v hv
      calc ∑ j ∈ Finset.range v.length,
            (δ ^ (-(1 / 2 : ℝ)) * T.G γ φ (v.take j) - T.kbin γ δ (v.take j))
          ≤ ∑ j ∈ Finset.range v.length, cfgVal φ δ (RS.bin (r j)) (c j) :=
            Finset.sum_le_sum (fun j hj => (hrc j (Finset.mem_range.1 hj)).2.2)
        _ ≤ B * v.length :=
            hgood v.length (Nat.ceil_le.2 hlen.1) r c hch (fun i hi => (hrc i hi).1)
        _ ≤ max B 0 * v.length :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
        _ ≤ max B 0 * (Real.log (1 / ε) / Real.log (2 * M / 3) + 1) :=
            mul_le_mul_of_nonneg_left hlen.2 (le_max_right _ _)
    have hsum : ∑ v ∈ T.leaves, T.flow γ v * ∑ j ∈ Finset.range v.length,
        (δ ^ (-(1 / 2 : ℝ)) * T.G γ φ (v.take j) - T.kbin γ δ (v.take j)) ≤
          max B 0 * (Real.log (1 / ε) / Real.log (2 * M / 3) + 1) := by
      calc _ ≤ ∑ v ∈ T.leaves, T.flow γ v *
              (max B 0 * (Real.log (1 / ε) / Real.log (2 * M / 3) + 1)) :=
            Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (hS v hv) (hflow0 v hv))
        _ = max B 0 * (Real.log (1 / ε) / Real.log (2 * M / 3) + 1) := by
            rw [← Finset.sum_mul, hflow1, one_mul]
    have hmul := mul_le_mul_of_nonneg_left hsum (sq_nonneg δ)
    rw [hH] at hineq
    have hQle : δ ^ (3 / 2 : ℝ) * segAvg φ 0 1 - δ ^ (3 / 2 : ℝ) * osc φ (8 * ε)
        - δ ^ 2 * (max B 0 * (Real.log (1 / ε) / Real.log (2 * M / 3) + 1)) ≤
        Real.log (lfppLength (δ ^ (3 / 2 : ℝ)) φ γ) := by linarith
    calc _ ≤ Real.exp (Real.log (lfppLength (δ ^ (3 / 2 : ℝ)) φ γ)) := Real.exp_le_exp.2 hQle
      _ = lfppLength (δ ^ (3 / 2 : ℝ)) φ γ := Real.exp_log hpos
  have hne : Nonempty {γ : ℝ → ℂ // IsAdmissiblePath γ} := ⟨⟨_, straight_admissible⟩⟩
  have hD : Real.exp (δ ^ (3 / 2 : ℝ) * segAvg φ 0 1 - δ ^ (3 / 2 : ℝ) * osc φ (8 * ε)
        - δ ^ 2 * (max B 0 * (Real.log (1 / ε) / Real.log (2 * M / 3) + 1))) ≤
      lfppDistance (δ ^ (3 / 2 : ℝ)) φ := by
    unfold lfppDistance
    exact le_ciInf (fun γ => hpath γ.1 γ.2)
  calc _ = Real.log (Real.exp (δ ^ (3 / 2 : ℝ) * segAvg φ 0 1 - δ ^ (3 / 2 : ℝ) * osc φ (8 * ε)
        - δ ^ 2 * (max B 0 * (Real.log (1 / ε) / Real.log (2 * M / 3) + 1)))) :=
        (Real.log_exp _).symm
    _ ≤ Real.log (lfppDistance (δ ^ (3 / 2 : ℝ)) φ) := Real.log_le_log (Real.exp_pos _) hD

/-! ### The probabilistic step -/

/-- Outside an event of vanishing probability, `log D_ε / log ε ≤ δ² B⁺ / log(2M/3) + θ`. -/
theorem prob_tendsto (hT41 : PathTreeExists) (hCL : ChainLengthBounds) (hJ42 : TreeInequality)
    (hL37 : Oscillation37) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : ℝ → ℂ → Ω → ℝ} (hG : IsGFFCircleAverage h P)
    {M : ℕ} (hM : 16 ≤ M) {δ : ℝ} (hδ : 0 < δ) (B : ℝ) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hRS : ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∃ RS : RecordSystem, AssignAt RS M δ ε ∧
      ∀ l : ℕ, P {ω | ∃ (r : ℕ → RS.Rec) (c : ℕ → Config), RS.IsChain r l ∧
          (∀ i < l, c i ∈ RS.family (r i)) ∧
          B * l < ∑ i ∈ Finset.range l, cfgVal (fun z => h ε z ω) δ (RS.bin (r i)) (c i)} ≤
        ENNReal.ofReal (Real.exp (-(l : ℝ))))
    {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun ε => P {ω | δ ^ 2 * max B 0 / Real.log (2 * M / 3) + θ <
        Real.log (lfppDistance (δ ^ (3 / 2 : ℝ)) (fun z => h ε z ω)) / Real.log ε})
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hosc, hHb⟩ := hL37 Ω P h hG
  have hξ0 : 0 < δ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hδ _
  have hMR : (16 : ℝ) ≤ M := by exact_mod_cast hM
  have hlg0 : 0 < Real.log (2 * (M : ℝ) / 3) := Real.log_pos (by linarith)
  have hlg2 : 0 < Real.log (2 * (M : ℝ)) := Real.log_pos (by linarith)
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  obtain ⟨ρ', -, hρ'pos, hρ'e⟩ := ENNReal.lt_iff_exists_real_btwn.1 he
  have hρ' : 0 < ρ' := ENNReal.ofReal_pos.1 hρ'pos
  have hρ : 0 < ρ' / 3 := by positivity
  obtain ⟨K, hK⟩ := hHb (ρ' / 3) hρ
  have hκ' : 0 < θ / (2 * δ ^ (3 / 2 : ℝ)) := by positivity
  have hosc' := (ENNReal.tendsto_nhds_zero.1 (hosc _ hκ')) (ENNReal.ofReal (ρ' / 3))
    (ENNReal.ofReal_pos.2 hρ)
  have hlog : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      max (2 * (δ ^ (3 / 2 : ℝ) * max K 0 + δ ^ 2 * max B 0) / θ)
        (Real.log (2 * (M : ℝ)) * Real.log (2 / (ρ' / 3))) ≤ Real.log (1 / ε) := by
    have := (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).eventually
      (eventually_ge_atTop (max (2 * (δ ^ (3 / 2 : ℝ) * max K 0 + δ ^ 2 * max B 0) / θ)
        (Real.log (2 * (M : ℝ)) * Real.log (2 / (ρ' / 3)))))
    filter_upwards [this] with ε hε
    rw [one_div, Real.log_inv]
    exact hε
  filter_upwards [hosc', hlog, Ioo_mem_nhdsGT (lt_min hε₀ one_pos)] with ε hεosc hεlog hε
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩
  have hεε₀ : ε ∈ Ioo (0 : ℝ) ε₀ := ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  obtain ⟨RS, hRA, hbad⟩ := hRS ε hεε₀
  have hℓ : 0 < Real.log (1 / ε) := by
    apply Real.log_pos
    rw [one_div]
    exact one_lt_inv_iff₀.2 ⟨hε1.1, hε1.2⟩
  have hlogε : Real.log ε = -Real.log (1 / ε) := by rw [one_div, Real.log_inv, neg_neg]
  -- the three bad events
  have hsub : {ω | δ ^ 2 * max B 0 / Real.log (2 * M / 3) + θ <
        Real.log (lfppDistance (δ ^ (3 / 2 : ℝ)) (fun z => h ε z ω)) / Real.log ε} ⊆
      ((⋃ l' : ℕ, {ω | ∃ (r : ℕ → RS.Rec) (c : ℕ → Config),
          RS.IsChain r (l' + ⌈Real.log (1 / ε) / Real.log (2 * M)⌉₊) ∧
          (∀ i < l' + ⌈Real.log (1 / ε) / Real.log (2 * M)⌉₊, c i ∈ RS.family (r i)) ∧
          B * ((l' + ⌈Real.log (1 / ε) / Real.log (2 * M)⌉₊ : ℕ) : ℝ) <
            ∑ i ∈ Finset.range (l' + ⌈Real.log (1 / ε) / Real.log (2 * M)⌉₊),
              cfgVal (fun z => h ε z ω) δ (RS.bin (r i)) (c i)}) ∪
        {ω | θ / (2 * δ ^ (3 / 2 : ℝ)) * Real.log (1 / ε) < osc (fun z => h ε z ω) (8 * ε)}) ∪
        {ω | K < |segAvg (fun z => h ε z ω) 0 1|} := by
    intro ω hω
    by_contra hnot
    have hgood : ∀ l : ℕ, ⌈Real.log (1 / ε) / Real.log (2 * M)⌉₊ ≤ l →
        ∀ (r : ℕ → RS.Rec) (c : ℕ → Config), RS.IsChain r l →
          (∀ i < l, c i ∈ RS.family (r i)) →
          ∑ i ∈ Finset.range l, cfgVal (fun z => h ε z ω) δ (RS.bin (r i)) (c i) ≤ B * l := by
      intro l hl r c hch hc
      by_contra hlt
      apply hnot
      left; left
      refine Set.mem_iUnion.2 ⟨l - ⌈Real.log (1 / ε) / Real.log (2 * M)⌉₊, ?_⟩
      rw [Nat.sub_add_cancel hl]
      exact ⟨r, c, hch, hc, lt_of_not_ge hlt⟩
    have h2 : osc (fun z => h ε z ω) (8 * ε) ≤ θ / (2 * δ ^ (3 / 2 : ℝ)) * Real.log (1 / ε) :=
      not_lt.1 (fun hh => hnot (Or.inl (Or.inr hh)))
    have h3 : |segAvg (fun z => h ε z ω) 0 1| ≤ K := not_lt.1 (fun hh => hnot (Or.inr hh))
    have hdet := det_bound hT41 hCL hJ42 hM hε1 hδ RS hRA (hG.continuous ε hε1.1 ω) B hgood
    have hHK := (abs_le.1 (h3.trans (le_max_left K 0))).1
    have ha : δ ^ (3 / 2 : ℝ) * osc (fun z => h ε z ω) (8 * ε) ≤ θ / 2 * Real.log (1 / ε) := by
      calc δ ^ (3 / 2 : ℝ) * osc (fun z => h ε z ω) (8 * ε)
          ≤ δ ^ (3 / 2 : ℝ) * (θ / (2 * δ ^ (3 / 2 : ℝ)) * Real.log (1 / ε)) :=
            mul_le_mul_of_nonneg_left h2 hξ0.le
        _ = θ / 2 * Real.log (1 / ε) := by field_simp
    have hb : -(δ ^ (3 / 2 : ℝ) * segAvg (fun z => h ε z ω) 0 1) ≤
        δ ^ (3 / 2 : ℝ) * max K 0 := by
      have := mul_le_mul_of_nonneg_left hHK hξ0.le
      linarith
    have hc : δ ^ (3 / 2 : ℝ) * max K 0 + δ ^ 2 * max B 0 ≤ θ / 2 * Real.log (1 / ε) := by
      have h4 := (div_le_iff₀ hθ).1 ((le_max_left _ _).trans hεlog)
      linarith
    have e1 : δ ^ 2 * (max B 0 * (Real.log (1 / ε) / Real.log (2 * M / 3) + 1)) =
        δ ^ 2 * max B 0 * (Real.log (1 / ε) / Real.log (2 * M / 3)) + δ ^ 2 * max B 0 := by
      ring
    have e2 : (δ ^ 2 * max B 0 / Real.log (2 * M / 3) + θ) * -Real.log (1 / ε) =
        -(δ ^ 2 * max B 0 * (Real.log (1 / ε) / Real.log (2 * M / 3))) -
          θ * Real.log (1 / ε) := by
      ring
    simp only [Set.mem_ofPred_eq] at hω
    rw [hlogε, lt_div_iff_of_neg (by linarith)] at hω
    linarith
  -- probability bounds
  have hP1 : P (⋃ l' : ℕ, {ω | ∃ (r : ℕ → RS.Rec) (c : ℕ → Config),
          RS.IsChain r (l' + ⌈Real.log (1 / ε) / Real.log (2 * M)⌉₊) ∧
          (∀ i < l' + ⌈Real.log (1 / ε) / Real.log (2 * M)⌉₊, c i ∈ RS.family (r i)) ∧
          B * ((l' + ⌈Real.log (1 / ε) / Real.log (2 * M)⌉₊ : ℕ) : ℝ) <
            ∑ i ∈ Finset.range (l' + ⌈Real.log (1 / ε) / Real.log (2 * M)⌉₊),
              cfgVal (fun z => h ε z ω) δ (RS.bin (r i)) (c i)}) ≤
      ENNReal.ofReal (ρ' / 3) := by
    refine (measure_iUnion_le _).trans ?_
    refine (ENNReal.tsum_le_tsum (fun l' => hbad _)).trans ?_
    refine (tsum_exp_tail_le _).trans (ENNReal.ofReal_le_ofReal ?_)
    -- `2 e^{-L} ≤ ρ'/3`
    have hL : Real.log (1 / ε) / Real.log (2 * M) ≤
        (⌈Real.log (1 / ε) / Real.log (2 * M)⌉₊ : ℝ) := Nat.le_ceil _
    have hT : Real.log (2 / (ρ' / 3)) ≤ Real.log (1 / ε) / Real.log (2 * M) := by
      rw [le_div_iff₀ hlg2]
      nlinarith [(le_max_right _ _).trans hεlog]
    have hexp : Real.exp (-(⌈Real.log (1 / ε) / Real.log (2 * M)⌉₊ : ℝ)) ≤
        Real.exp (-Real.log (2 / (ρ' / 3))) := Real.exp_le_exp.2 (by linarith)
    have hexp2 : Real.exp (-Real.log (2 / (ρ' / 3))) = ρ' / 3 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
    linarith
  calc P {ω | δ ^ 2 * max B 0 / Real.log (2 * M / 3) + θ <
        Real.log (lfppDistance (δ ^ (3 / 2 : ℝ)) (fun z => h ε z ω)) / Real.log ε}
      ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add_left (measure_union_le _ _) _
    _ ≤ ENNReal.ofReal (ρ' / 3) + ENNReal.ofReal (ρ' / 3) + ENNReal.ofReal (ρ' / 3) :=
        add_le_add (add_le_add hP1 hεosc) (hK ε hε1)
    _ = ENNReal.ofReal ρ' := by
        rw [← ENNReal.ofReal_add hρ.le hρ.le, ← ENNReal.ofReal_add (by positivity) hρ.le]
        congr 1
        ring
    _ ≤ e := hρ'e.le

/-! ### The exponent bound at a fixed `δ` -/

/-- For fixed `n` and `δ ∈ (0,1)` with good record systems, every LFPP exponent at
`ξ = δ^{3/2}` satisfies `λ ≤ δ² B⁺ / log(2M/3)`, `B = (log Z + 1)/t`, `t = n^{1/4}`. -/
theorem lam_le_at_delta (hP1 : SegCombLaw) (hL37 : Oscillation37) (hMT : RecordMeanTransfer)
    (hT41 : PathTreeExists) (hCL : ChainLengthBounds) (hJ42 : TreeInequality)
    (hEX : ExponentFromProb) {κ : ℝ} (hκ : 0 < κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : ℝ → ℂ → Ω → ℝ}
    (hG : IsGFFCircleAverage h P) (hU : ∀ ε > 0, ∀ δ > 0, ChainAt P h κ ε δ)
    {n : ℕ} (hn : 1 ≤ n) {CV c₀ : ℝ} (hV : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ ε > 0, VarAt n δ ε CV c₀)
    {Cn CL CR DR : ℝ} (hCn : CrudeAt n Cn) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hRA : ∃ ε₀ > 0, ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∃ RS : RecordSystem,
      RS.Good (16 ^ n) δ CR DR ∧ AssignAt RS (16 ^ n) δ ε)
    {lam : ℝ} (hlam : IsLFPPExponent h P (δ ^ (3 / 2 : ℝ)) lam) :
    lam ≤ δ ^ 2 * max ((Real.log (chainZ (cntN n (max CR 1) (max DR 0)) (meanBound n Cn CL δ)
          (varV n δ c₀ (max CV 0)) κ ((n : ℝ) ^ (1 / 4 : ℝ))) + 1) / ((n : ℝ) ^ (1 / 4 : ℝ))) 0 /
        Real.log (2 * ((16 ^ n : ℕ) : ℝ) / 3) := by
  have hPr := hG.isProbabilityMeasure
  obtain ⟨ε₀, hε₀, hR⟩ := hRA
  apply (hEX Ω P h (δ ^ (3 / 2 : ℝ)) lam _ hPr hlam).1
  intro θ hθ
  have hu : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Eventually.of_forall (fun j => by simp only [Set.mem_Ioi]; positivity)
  refine ⟨_, hu, ?_⟩
  refine (prob_tendsto hT41 hCL hJ42 hL37 hG (sixteen_le_pow hn) hδ.1
    ((Real.log (chainZ (cntN n (max CR 1) (max DR 0)) (meanBound n Cn CL δ)
          (varV n δ c₀ (max CV 0)) κ ((n : ℝ) ^ (1 / 4 : ℝ))) + 1) / ((n : ℝ) ^ (1 / 4 : ℝ)))
    hε₀ ?_ hθ).comp hu
  intro ε hε
  obtain ⟨RS, hGood, hAssign⟩ := hR ε hε
  exact ⟨RS, hAssign, fun l => chain_prob hP1 hMT hκ hG hε.1 hδ (hU ε hε.1 δ hδ.1) hn
    (hV δ hδ ε hε.1) hCn RS hGood l⟩

end UpperAssemblyAux

open UpperAssemblyAux Blueprint.Draft in
/-- **Conditional assembly of (1.7)** (`Blueprint.Draft.UpperAssembly`): the Section 3–4 nodes
imply Proposition 1.2's upper bound `Blueprint.Prop12Upper`. -/
theorem upperAssembly : Blueprint.Draft.UpperAssembly := by
  intro _hA1 _hAS hP1 hL37 hM45 hM46 hV47 hMT hT41 hCL hJ42 hR44 hU49 hZL hEX Ω _ P h hG
  obtain ⟨CR, DR, hR⟩ := hR44
  obtain ⟨CV, c₀, hc₀, hV⟩ := hV47
  obtain ⟨CL, NL, hL⟩ := hM46
  obtain ⟨κ, hκ, hU⟩ := hU49
  obtain ⟨CZ, hZ⟩ := hZL κ CL (max CR 1) (max CV 0) (max DR 0) c₀ hκ
    (lt_max_of_lt_right one_pos) (le_max_right _ _) (le_max_right _ _) hc₀
  refine ⟨max CZ 0, max NL 1, fun n hn η hη => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnL : NL ≤ n := le_trans (le_max_left _ _) hn
  obtain ⟨Cn, hCn⟩ := hM45 n hn1
  have hCn' : CrudeAt n Cn := hCn
  have hLn : LimitAt n CL := hL n hnL
  have hZn := hZ n hn1 (a n) Cn (a_nonneg' n) (meanBound n Cn CL)
    (fun δ hδ k => meanBound_crude hCn' CL hδ k) (meanBound_limit hLn)
  obtain ⟨δ₀, hδ₀, hR'⟩ := hR n hn1
  have h16 : (16 : ℝ) ≤ (16 : ℝ) ^ n := by
    calc (16 : ℝ) = 16 ^ 1 := by norm_num
      _ ≤ 16 ^ n := pow_le_pow_right₀ (by norm_num) hn1
  have hlg : 0 < Real.log (2 * 16 ^ n / 3 : ℝ) := Real.log_pos (by linarith)
  have hev := hZn (η * Real.log (2 * 16 ^ n / 3)) (by positivity)
  have hf : Tendsto (fun ξ : ℝ => ξ ^ (2 / 3 : ℝ)) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · have h0 := (Real.continuousAt_rpow_const 0 (2 / 3) (Or.inr (by norm_num))).tendsto
      rw [Real.zero_rpow (by norm_num)] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ξ hξ
      exact Real.rpow_pos_of_pos hξ _
  filter_upwards [hf.eventually hev, hf.eventually (Ioo_mem_nhdsGT (lt_min hδ₀ one_pos)),
    self_mem_nhdsWithin] with ξ hBξ hδr hξ
  intro lam hlam
  have hξ0 : 0 < ξ := hξ
  have hδ : ξ ^ (2 / 3 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨hδr.1, hδr.2.trans_le (min_le_right _ _)⟩
  have hδ32 : (ξ ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = ξ := by
    rw [← Real.rpow_mul hξ0.le]; norm_num
  have hδ2 : (ξ ^ (2 / 3 : ℝ)) ^ 2 = ξ ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hξ0.le]; norm_num
  rw [← hδ32] at hlam
  have hRA := hR' _ ⟨hδ.1, hδr.2.trans_le (min_le_left _ _)⟩
  have hlamΛ := lam_le_at_delta (CL := CL) hP1 hL37 hMT hT41 hCL hJ42 hEX hκ hG
    (fun ε hε δ hδ => hU Ω P h hG ε hε δ hδ) hn1 (fun δ hδ ε hε => hV n hn1 δ hδ ε hε) hCn' hδ
    hRA hlam
  obtain ⟨B, hBdef⟩ : ∃ B, B = (Real.log (chainZ (cntN n (max CR 1) (max DR 0))
      (meanBound n Cn CL (ξ ^ (2 / 3 : ℝ))) (varV n (ξ ^ (2 / 3 : ℝ)) c₀ (max CV 0)) κ
      ((n : ℝ) ^ (1 / 4 : ℝ))) + 1) / ((n : ℝ) ^ (1 / 4 : ℝ)) := ⟨_, rfl⟩
  rw [← hBdef] at hlamΛ
  have hB : B ≤ a n + CZ * (n : ℝ) ^ (3 / 4 : ℝ) + η * Real.log (2 * 16 ^ n / 3) := by
    rw [hBdef]; exact hBξ
  have hcast : ((16 ^ n : ℕ) : ℝ) = (16 : ℝ) ^ n := by push_cast; ring
  rw [hcast, hδ2] at hlamΛ
  have hξ43 : 0 < ξ ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hξ0 _
  have hn34 : 0 ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by positivity
  have hBp : max B 0 ≤ a n + max CZ 0 * (n : ℝ) ^ (3 / 4 : ℝ) + η * Real.log (2 * 16 ^ n / 3) := by
    have h1 : CZ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ max CZ 0 * (n : ℝ) ^ (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hn34
    have h2 : 0 ≤ max CZ 0 * (n : ℝ) ^ (3 / 4 : ℝ) := mul_nonneg (le_max_right _ _) hn34
    have h3 := a_nonneg' n
    have h4 : 0 ≤ η * Real.log (2 * 16 ^ n / 3) := by positivity
    exact max_le (by linarith) (by linarith)
  calc lam / ξ ^ (4 / 3 : ℝ)
      ≤ (ξ ^ (4 / 3 : ℝ) * max B 0 / Real.log (2 * 16 ^ n / 3)) / ξ ^ (4 / 3 : ℝ) :=
        div_le_div_of_nonneg_right hlamΛ hξ43.le
    _ = max B 0 / Real.log (2 * 16 ^ n / 3) := by field_simp
    _ ≤ (a n + max CZ 0 * (n : ℝ) ^ (3 / 4 : ℝ) + η * Real.log (2 * 16 ^ n / 3)) /
          Real.log (2 * 16 ^ n / 3) := div_le_div_of_nonneg_right hBp hlg.le
    _ = (a n + max CZ 0 * (n : ℝ) ^ (3 / 4 : ℝ)) / Real.log (2 * 16 ^ n / 3) + η := by
        field_simp

end LQGDimension
