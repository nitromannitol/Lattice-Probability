/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ApproximateBracketCLT at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.RandomVarianceTaylor
import LatticeProb.Bonanno.ReflectedGMS.Limit.MultiTimeCharFunFromIncrements
import LatticeProb.Bonanno.ReflectedGMS.Limit.UnstoppedContinuousLindeberg

/-!
# The approximate-bracket martingale CLT (one increment, conditional, `L¹`)

Let `N k` be square-integrable martingales with **random** brackets `A k` (so that
`P[(N_b - N_a)² | 𝔽_a] = P[A_b - A_a | 𝔽_a]`), whose bracket increments over `[s, t]` are
bounded by a common `K`, converge in probability to the deterministic `C (t - s)`, have
continuous paths (so that the quadratic oscillation `∑ᵢ E[(ΔA_i)²]` along the uniform partitions
vanishes), and whose Lindeberg sums vanish in the double limit.  Then the conditional
characteristic function of the increment `N_t - N_s` given `𝔽_s` converges in `L¹` to
`exp (-u² C (t - s) / 2)`:

  `∫ ‖ P[e^{iu(N_t - N_s)} | 𝔽_s] - e^{-u² C (t-s)/2} ‖ dP ⟶ 0`

(`tendsto_integral_norm_condExp_cexp_sub_of_localized`).  This is the abstract statement
behind `RescaledFddCharFunReduction.RescaledIncrementCharFunLimit`; nothing about the reflected
walk appears here.

## Route

1. `condExp_increment_sq_eq_condExp_bracket` — the bracket identity for a random compensator.
2. `norm_integral_test_mul_cexp_increment_mul_exp_sub_le` — the compensated telescoping of
   `RandomVarianceTaylor` along the uniform partition of `[s, t]`: for every bounded
   `𝔽_s`-measurable `W`,
   `‖E[W e^{iuΔN} e^{u²ΔA/2}] - E[W]‖ ≤ e^{u²K/2}(…δ K + … Lindeberg + … oscillation + … η K)`.
3. `tendsto_bracketOscillation` — the oscillation vanishes for continuous monotone brackets.
4. `exists_test_integral_norm_condExp_sub` — the `L¹` norm of `P[f | m] - c` is realised by
   the test function `W = ‖Y‖ / Y`, `Y = P[f | m] - c`, so the tested bound suffices.
5. `tendsto_integral_abs_exp_neg_sub` — `E|e^{-u²ΔA_k/2} - e^{-u²C(t-s)/2}| → 0` from the
   bracket limit in probability (bounded convergence, no uniform integrability).
6. `tendsto_integral_norm_condExp_cexp_sub_of_localized` — the limit: first `n → ∞` (kills the
   oscillation), then `k → ∞` (Lindeberg), then `δ, η → 0`.
7. `tendsto_integral_norm_condExp_cexp_sub_of_exists_localized` — unlocalisation: the
   conditional characteristic functions of two processes agreeing outside an event of
   vanishing probability have the same `L¹` limit.

The bounded-bracket hypothesis is a **localisation**: in the application it is produced by
stopping at the first time the bracket reaches `K` (`UCPBracketLocalization`), and the exit
probability tends to zero because the bracket converges in probability to `C (t - s) < K`.

## Satisfiability

`localizedBracketArray_of_square_martingale_const`: every continuous square-integrable
martingale with the exact deterministic bracket `C v` is a `LocalizedBracketArray` (constant
in `k`), so the main theorem reproduces the exact-bracket identification of
`UnstoppedContinuousLindeberg` in its `L¹`-limit form (`example` at the end).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.ApproximateBracketCLT

open ReflectedGMS.MartingaleLimit ReflectedGMS.MultiTimeCharFun

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## The bracket identity with a random compensator -/

/-- Conditional variance of an increment from a conditional square with a random
correction `V`: the random-`c` form of
`GaussianIdentificationUnlocalization.condExp_sub_sq_eq_of_condExp_sq`. -/
theorem condExp_sub_sq_eq_of_condExp_sq' [IsFiniteMeasure P] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {X Y V : Ω → ℝ}
    (hX : StronglyMeasurable[m] X) (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P)
    (hcond : P[Y | m] =ᵐ[P] X)
    (hcondsq : P[fun ω => Y ω ^ 2 | m] =ᵐ[P] fun ω => X ω ^ 2 + V ω) :
    P[fun ω => (Y ω - X ω) ^ 2 | m] =ᵐ[P] V := by
  have hYint : Integrable Y P := hY2.integrable (by norm_num)
  have hXY : Integrable (X * Y) P := hX2.integrable_mul hY2
  have iY2 : Integrable (fun ω => Y ω ^ 2) P := hY2.integrable_sq
  have iX2 : Integrable (fun ω => X ω ^ 2) P := hX2.integrable_sq
  have hdec : (fun ω => (Y ω - X ω) ^ 2)
      = (fun ω => Y ω ^ 2) - X * Y - X * Y + (fun ω => X ω ^ 2) := by
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  have e1 : P[(fun ω => Y ω ^ 2) - X * Y - X * Y + (fun ω => X ω ^ 2) | m]
      =ᵐ[P] P[(fun ω => Y ω ^ 2) - X * Y - X * Y | m] + P[fun ω => X ω ^ 2 | m] :=
    condExp_add ((iY2.sub hXY).sub hXY) iX2 m
  have e2 : P[(fun ω => Y ω ^ 2) - X * Y - X * Y | m]
      =ᵐ[P] P[(fun ω => Y ω ^ 2) - X * Y | m] - P[X * Y | m] :=
    condExp_sub (iY2.sub hXY) hXY m
  have e3 : P[(fun ω => Y ω ^ 2) - X * Y | m]
      =ᵐ[P] P[fun ω => Y ω ^ 2 | m] - P[X * Y | m] :=
    condExp_sub iY2 hXY m
  have e4 : P[X * Y | m] =ᵐ[P] X * P[Y | m] :=
    condExp_mul_of_stronglyMeasurable_left hX hXY hYint
  have e5 : P[fun ω => X ω ^ 2 | m] = fun ω => X ω ^ 2 :=
    condExp_of_stronglyMeasurable hm (hX.pow 2) iX2
  rw [hdec]
  filter_upwards [e1, e2, e3, e4, hcond, hcondsq] with ω a1 a2 a3 a4 a5 a6
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, e5] at a1 a2 a3 a4 ⊢
  rw [a1, a2, a3, a4, a5, a6]
  ring

/-- **The bracket identity.**  If `N` is a square-integrable martingale and `N² - A` is a
martingale, then `P[(N b - N a)² | 𝔽 a] = P[A b - A a | 𝔽 a]` for `a ≤ b`.  The bracket `A`
is random; nothing else is assumed about it. -/
theorem condExp_increment_sq_eq_condExp_bracket [IsFiniteMeasure P]
    {𝔽 : Filtration ℝ≥0 mΩ} {N A : ℝ≥0 → Ω → ℝ}
    (hN : Martingale N 𝔽 P) (hNA : Martingale (fun v ω => N v ω ^ 2 - A v ω) 𝔽 P)
    (h2 : ∀ v : ℝ≥0, MemLp (N v) 2 P) {a b : ℝ≥0} (hab : a ≤ b) :
    P[fun ω => (N b ω - N a ω) ^ 2 | 𝔽 a] =ᵐ[P] P[fun ω => A b ω - A a ω | 𝔽 a] := by
  have hAint : ∀ v, Integrable (A v) P := by
    intro v
    have := (h2 v).integrable_sq.sub (hNA.integrable v)
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]
    ring
  have hAa : StronglyMeasurable[𝔽 a] (A a) := by
    have h1 : StronglyMeasurable[𝔽 a] (fun ω => N a ω ^ 2 - A a ω) := hNA.stronglyMeasurable a
    have h2' : StronglyMeasurable[𝔽 a] (fun ω => N a ω ^ 2) := (hN.stronglyMeasurable a).pow 2
    have heq : A a = fun ω => N a ω ^ 2 - (N a ω ^ 2 - A a ω) := by
      funext ω
      ring
    rw [heq]
    exact h2'.sub h1
  have hsq : P[fun ω => N b ω ^ 2 | 𝔽 a] =ᵐ[P]
      fun ω => N a ω ^ 2 + ((P[A b | 𝔽 a]) ω - A a ω) := by
    have hdec : (fun ω => N b ω ^ 2) = (fun ω => N b ω ^ 2 - A b ω) + A b := by
      funext ω
      simp only [Pi.add_apply]
      ring
    have e1 : P[(fun ω => N b ω ^ 2 - A b ω) + A b | 𝔽 a]
        =ᵐ[P] P[fun ω => N b ω ^ 2 - A b ω | 𝔽 a] + P[A b | 𝔽 a] :=
      condExp_add (hNA.integrable b) (hAint b) (𝔽 a)
    rw [hdec]
    filter_upwards [e1, hNA.condExp_ae_eq hab] with ω h1 h2
    have h2' : (P[fun ω => N b ω ^ 2 - A b ω | 𝔽 a]) ω = N a ω ^ 2 - A a ω := h2
    simp only [Pi.add_apply] at h1
    rw [h1, h2']
    ring
  have hV : P[fun ω => A b ω - A a ω | 𝔽 a] =ᵐ[P] fun ω => (P[A b | 𝔽 a]) ω - A a ω := by
    have e1 : P[fun ω => A b ω - A a ω | 𝔽 a] =ᵐ[P] P[A b | 𝔽 a] - P[A a | 𝔽 a] :=
      condExp_sub (hAint b) (hAint a) (𝔽 a)
    have e2 : P[A a | 𝔽 a] = A a := condExp_of_stronglyMeasurable (𝔽.le a) hAa (hAint a)
    filter_upwards [e1] with ω h1
    rw [h1, Pi.sub_apply, e2]
  exact (condExp_sub_sq_eq_of_condExp_sq' (𝔽.le a) (hN.stronglyMeasurable a) (h2 a) (h2 b)
    (hN.condExp_ae_eq hab) hsq).trans hV.symm

/-! ## The estimate along the uniform partition -/

/-- The quadratic oscillation of a bracket along the uniform partition of `[s, t]` into `n`
pieces: `∑ᵢ E[(A(tᵢ₊₁) - A(tᵢ))²]`. -/
noncomputable def bracketOscillation (P : Measure Ω) (A : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n : ℕ) :
    ℝ :=
  ∑ i ∈ Finset.range n,
    ∫ ω, (A (uniformPartition s t n (i + 1)) ω - A (uniformPartition s t n i) ω) ^ 2 ∂P

/-- **The compensated estimate along the uniform partition of `[s, t]`.**  For a
square-integrable martingale `N` with an adapted, monotone bracket `A` satisfying the bracket
identity and `A t - A s ≤ K`, and every bounded `𝔽 s`-measurable `W`,
the compensated tested Fourier integral is within an explicit error of `E[W]`. -/
theorem norm_integral_test_mul_cexp_increment_mul_exp_sub_le [IsProbabilityMeasure P]
    {𝔽 : Filtration ℝ≥0 mΩ} {N A : ℝ≥0 → Ω → ℝ}
    (hN : Martingale N 𝔽 P) (h2 : ∀ v : ℝ≥0, MemLp (N v) 2 P)
    (hAad : ∀ v : ℝ≥0, Measurable[𝔽 v] (A v))
    {s t : ℝ≥0} (hst : s ≤ t)
    (hAmono : ∀ᵐ ω ∂P, MonotoneOn (fun v => A v ω) (Set.Icc s t))
    {K : ℝ} (hAK : ∀ᵐ ω ∂P, A t ω - A s ω ≤ K)
    (hbr : ∀ a b : ℝ≥0, s ≤ a → a ≤ b → b ≤ t →
      P[fun ω => (N b ω - N a ω) ^ 2 | 𝔽 a] =ᵐ[P] P[fun ω => A b ω - A a ω | 𝔽 a])
    {W : Ω → ℂ} (hWmeas : StronglyMeasurable[𝔽 s] W) (hWbdd : ∀ ω, ‖W ω‖ ≤ 1)
    {u δ η : ℝ} (hδ : 0 ≤ δ) (huδ : |u| * δ ≤ 1) (hη : 0 < η) {n : ℕ} (hn : n ≠ 0) :
    ‖(∫ ω, W ω * Complex.exp ((u * (N t ω - N s ω) : ℝ) * Complex.I)
          * ((Real.exp (u ^ 2 * (A t ω - A s ω) / 2) : ℝ) : ℂ) ∂P) - ∫ ω, W ω ∂P‖
      ≤ Real.exp (u ^ 2 * K / 2) * (Real.exp (u ^ 2 * K / 2) * (u ^ 4 / 4)
            * bracketOscillation P A s t n
          + u ^ 2 / 2 * (η / 2 * u ^ 2 * K + η⁻¹ / 2 * bracketOscillation P A s t n)
          + 2 / 9 * |u| ^ 3 * δ * K + 4 * u ^ 2 * lindebergSum P N δ s t n) := by
  classical
  -- the clamped grid, constant after the last partition point
  set g : ℕ → ℝ≥0 := fun k => uniformPartition s t n (min k n) with hgdef
  have hgapp : ∀ k, g k = uniformPartition s t n (min k n) := fun _ => rfl
  have hupmono : Monotone (uniformPartition s t n) := uniformPartition_mono s t n
  have hgmono : Monotone g := fun i j hij => hupmono (min_le_min hij le_rfl)
  have hg0 : g 0 = s := by rw [hgapp, Nat.zero_min, uniformPartition_zero]
  have hgn : g n = t := by rw [hgapp, min_self, uniformPartition_self hn hst]
  have hgle : ∀ k, g k ≤ t := by
    intro k
    have h := hupmono (min_le_right k n)
    rw [uniformPartition_self hn hst] at h
    rw [hgapp]
    exact h
  have hsg : ∀ k, s ≤ g k := fun k => by rw [← hg0]; exact hgmono (Nat.zero_le k)
  have hgmem : ∀ k, g k ∈ Set.Icc s t := fun k => ⟨hsg k, hgle k⟩
  -- the discrete data
  set F : ℕ → MeasurableSpace Ω := fun k => 𝔽 (g k) with hFdef
  have hFle : ∀ k, F k ≤ mΩ := fun k => 𝔽.le _
  have hFmono : Monotone F := fun i j hij => 𝔽.mono (hgmono hij)
  set Z : ℕ → Ω → ℝ := fun k ω => N (g (k + 1)) ω - N (g k) ω with hZdef
  set D : ℕ → Ω → ℝ := fun k ω => A (g (k + 1)) ω - A (g k) ω with hDdef
  have hZadapt : ∀ k, Measurable[F (k + 1)] (Z k) := by
    intro k
    have h1 : StronglyMeasurable[𝔽 (g (k + 1))] (N (g (k + 1))) := hN.stronglyMeasurable _
    have h2' : StronglyMeasurable[𝔽 (g (k + 1))] (N (g k)) :=
      (hN.stronglyMeasurable (g k)).mono (𝔽.mono (hgmono (Nat.le_succ k)))
    exact (h1.sub h2').measurable
  have hDadapt : ∀ k, Measurable[F (k + 1)] (D k) := by
    intro k
    have h1 : Measurable[𝔽 (g (k + 1))] (A (g (k + 1))) := hAad _
    have h2' : Measurable[𝔽 (g (k + 1))] (A (g k)) :=
      (hAad (g k)).mono (𝔽.mono (hgmono (Nat.le_succ k))) le_rfl
    exact h1.sub h2'
  have hZ1 : ∀ k, Integrable (Z k) P := fun k =>
    (hN.integrable (g (k + 1))).sub (hN.integrable (g k))
  have hZ2 : ∀ k, Integrable (fun ω => Z k ω ^ 2) P := fun k =>
    integrable_increment_sq_of_memLp h2 (g k) (g (k + 1))
  have hDm : ∀ k, Measurable (D k) := fun k => (hDadapt k).mono (hFle (k + 1)) le_rfl
  have hD0 : ∀ k, ∀ᵐ ω ∂P, 0 ≤ D k ω := by
    intro k
    filter_upwards [hAmono] with ω hω
    exact sub_nonneg.2 (hω (hgmem k) (hgmem (k + 1)) (hgmono (Nat.le_succ k)))
  have hDK : ∀ k, ∀ᵐ ω ∂P, D k ω ≤ K := by
    intro k
    filter_upwards [hAmono, hAK] with ω hω hK
    have h1 : A (g (k + 1)) ω ≤ A t ω := hω (hgmem (k + 1)) ⟨hst, le_rfl⟩ (hgle (k + 1))
    have h2' : A s ω ≤ A (g k) ω := hω ⟨le_rfl, hst⟩ (hgmem k) (hsg k)
    show A (g (k + 1)) ω - A (g k) ω ≤ K
    linarith
  have hD1 : ∀ k, Integrable (D k) P := by
    intro k
    refine Integrable.of_bound (hDm k).aestronglyMeasurable |K| ?_
    filter_upwards [hD0 k, hDK k] with ω h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    exact h2.trans (le_abs_self K)
  have hD2 : ∀ k, Integrable (fun ω => D k ω ^ 2) P := by
    intro k
    refine Integrable.of_bound ((hDm k).pow_const 2).aestronglyMeasurable (K ^ 2) ?_
    filter_upwards [hD0 k, hDK k] with ω h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hmean : ∀ k, P[Z k | F k] =ᵐ[P] 0 := by
    intro k
    have hZeq : Z k = N (g (k + 1)) - N (g k) := rfl
    rw [hZeq]
    have hsub := condExp_sub (hN.integrable (g (k + 1))) (hN.integrable (g k)) (F k)
    refine hsub.trans ?_
    filter_upwards [hN.condExp_ae_eq (hgmono (Nat.le_succ k)),
      hN.condExp_ae_eq (le_refl (g k))] with ω h1 h2
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [h1, h2, sub_self]
  have hvar : ∀ k, P[fun ω => Z k ω ^ 2 | F k] =ᵐ[P] P[D k | F k] := fun k =>
    hbr (g k) (g (k + 1)) (hsg k) (hgmono (Nat.le_succ k)) (hgle (k + 1))
  have hWmeas' : StronglyMeasurable[F 0] W := by
    have hF0 : F 0 = 𝔽 s := by rw [hFdef]; simp only [hg0]
    rw [hF0]
    exact hWmeas
  have hsumZ : ∀ ω, ∑ k ∈ Finset.range n, Z k ω = N t ω - N s ω := by
    intro ω
    calc ∑ k ∈ Finset.range n, Z k ω
        = ∑ k ∈ Finset.range n,
            ((fun j => N (g j) ω) (k + 1) - (fun j => N (g j) ω) k) := rfl
      _ = N (g n) ω - N (g 0) ω := Finset.sum_range_sub (fun j => N (g j) ω) n
      _ = N t ω - N s ω := by rw [hgn, hg0]
  have hsumD : ∀ ω, ∑ k ∈ Finset.range n, D k ω = A t ω - A s ω := by
    intro ω
    calc ∑ k ∈ Finset.range n, D k ω
        = ∑ k ∈ Finset.range n,
            ((fun j => A (g j) ω) (k + 1) - (fun j => A (g j) ω) k) := rfl
      _ = A (g n) ω - A (g 0) ω := Finset.sum_range_sub (fun j => A (g j) ω) n
      _ = A t ω - A s ω := by rw [hgn, hg0]
  have hDKsum : ∀ᵐ ω ∂P, ∑ k ∈ Finset.range n, D k ω ≤ K := by
    filter_upwards [hAK] with ω hω
    rw [hsumD]
    exact hω
  have hmain := norm_integral_test_mul_cexp_mul_exp_sub_le' (P := P) hFle hFmono hZadapt hDadapt
    hZ1 hZ2 hD1 hD2 hD0 hmean hvar hWmeas' hWbdd hδ huδ hη n hDKsum
  -- identify the grid quantities with the unclamped uniform partition
  have hgk : ∀ k, k < n → g k = uniformPartition s t n k := fun k hk => by
    rw [hgapp, min_eq_left hk.le]
  have hgk1 : ∀ k, k < n → g (k + 1) = uniformPartition s t n (k + 1) := fun k hk => by
    rw [hgapp, min_eq_left (Nat.succ_le_of_lt hk)]
  have hosc : (∑ i ∈ Finset.range n, ∫ ω, D i ω ^ 2 ∂P) = bracketOscillation P A s t n := by
    unfold bracketOscillation
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n := Finset.mem_range.1 hk
    simp only [hDdef, hgk k hk', hgk1 k hk']
  have hlind : (∑ i ∈ Finset.range n,
      ∫ ω, Set.indicator {ω | δ < |Z i ω|} (fun ω => Z i ω ^ 2) ω ∂P)
      = lindebergSum P N δ s t n := by
    rw [lindebergSum_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n := Finset.mem_range.1 hk
    simp only [hZdef, hgk k hk', hgk1 k hk']
  simp only [hsumZ, hsumD] at hmain
  rw [hosc, hlind] at hmain
  exact hmain

/-! ## The oscillation of a continuous monotone bracket vanishes -/

/-- **The quadratic oscillation of a continuous monotone bracket vanishes** along the uniform
partitions: `∑ᵢ E[(ΔA_i)²] ≤ E[max_i ΔA_i · (A t - A s)] → 0` by uniform continuity and
bounded convergence. -/
theorem tendsto_bracketOscillation [IsProbabilityMeasure P]
    {A : ℝ≥0 → Ω → ℝ} (hAm : ∀ v : ℝ≥0, Measurable (A v)) {s t : ℝ≥0} (hst : s ≤ t)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun v : ℝ≥0 => A v ω) (Set.Icc s t))
    (hmono : ∀ᵐ ω ∂P, MonotoneOn (fun v : ℝ≥0 => A v ω) (Set.Icc s t))
    {K : ℝ} (hK : ∀ᵐ ω ∂P, A t ω - A s ω ≤ K) :
    Tendsto (fun n => bracketOscillation P A s t n) atTop (𝓝 0) := by
  classical
  set f : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n,
    (A (uniformPartition s t n (i + 1)) ω - A (uniformPartition s t n i) ω) ^ 2 with hfdef
  have hfmeas : ∀ n, Measurable (f n) := fun n =>
    Finset.measurable_sum _ fun i _ => ((hAm _).sub (hAm _)).pow_const 2
  have hpartmem : ∀ n i, i ≤ n → uniformPartition s t n i ∈ Set.Icc s t := by
    intro n i hi
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hi0 : i = 0 := Nat.le_zero.1 hi
      subst hi0
      rw [uniformPartition_zero]
      exact ⟨le_rfl, hst⟩
    · constructor
      · have h := uniformPartition_mono s t n (Nat.zero_le i)
        rwa [uniformPartition_zero] at h
      · have h := uniformPartition_mono s t n hi
        rwa [uniformPartition_self hn.ne' hst] at h
  have hincr : ∀ᵐ ω ∂P, ∀ n i, i < n →
      0 ≤ A (uniformPartition s t n (i + 1)) ω - A (uniformPartition s t n i) ω ∧
      A (uniformPartition s t n (i + 1)) ω - A (uniformPartition s t n i) ω ≤ K := by
    filter_upwards [hmono, hK] with ω hω hωK
    intro n i hi
    have hmem1 := hpartmem n i hi.le
    have hmem2 := hpartmem n (i + 1) (Nat.succ_le_of_lt hi)
    refine ⟨sub_nonneg.2 (hω hmem1 hmem2 (uniformPartition_mono s t n (Nat.le_succ i))), ?_⟩
    have h1 : A (uniformPartition s t n (i + 1)) ω ≤ A t ω := hω hmem2 ⟨hst, le_rfl⟩ hmem2.2
    have h2 : A s ω ≤ A (uniformPartition s t n i) ω := hω ⟨le_rfl, hst⟩ hmem1 hmem1.1
    linarith
  have hsumtel : ∀ ω n, n ≠ 0 → ∑ i ∈ Finset.range n,
      (A (uniformPartition s t n (i + 1)) ω - A (uniformPartition s t n i) ω)
        = A t ω - A s ω := by
    intro ω n hn
    calc ∑ i ∈ Finset.range n,
          (A (uniformPartition s t n (i + 1)) ω - A (uniformPartition s t n i) ω)
        = ∑ i ∈ Finset.range n, ((fun j => A (uniformPartition s t n j) ω) (i + 1)
            - (fun j => A (uniformPartition s t n j) ω) i) := rfl
      _ = (fun j => A (uniformPartition s t n j) ω) n
          - (fun j => A (uniformPartition s t n j) ω) 0 :=
          Finset.sum_range_sub (fun j => A (uniformPartition s t n j) ω) n
      _ = A t ω - A s ω := by
          simp only [uniformPartition_self hn hst, uniformPartition_zero]
  -- domination
  have hdom : ∀ n, ∀ᵐ ω ∂P, ‖f n ω‖ ≤ K ^ 2 := by
    intro n
    filter_upwards [hincr, hK] with ω hω hωK
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [hfdef, Finset.sum_range_zero, norm_zero]
      positivity
    · have hK0 : 0 ≤ K := (hω n 0 hn).1.trans (hω n 0 hn).2
      have hnn : 0 ≤ f n ω := Finset.sum_nonneg fun i _ => sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      calc f n ω ≤ ∑ i ∈ Finset.range n,
            K * (A (uniformPartition s t n (i + 1)) ω - A (uniformPartition s t n i) ω) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have h := hω n i (Finset.mem_range.1 hi)
            nlinarith [h.1, h.2]
        _ = K * (A t ω - A s ω) := by rw [← Finset.mul_sum, hsumtel ω n hn.ne']
        _ ≤ K * K := mul_le_mul_of_nonneg_left hωK hK0
        _ = K ^ 2 := by ring
  -- pointwise convergence
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 0) := by
    filter_upwards [hincr, hc, hK] with ω hω hωc hωK
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun n =>
      lt_of_lt_of_le ha (Finset.sum_nonneg fun i _ => sq_nonneg _), fun ε hε => ?_⟩
    have hρ : (0 : ℝ) < ε / (|K| + 1) := by positivity
    obtain ⟨d, hd, hdlt⟩ := Metric.uniformContinuousOn_iff.1
      ((isCompact_Icc (a := s) (b := t)).uniformContinuousOn_of_continuous hωc) _ hρ
    have hmesh : Tendsto (fun n : ℕ => ((t : ℝ) - (s : ℝ)) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    filter_upwards [hmesh.eventually (gt_mem_nhds hd), eventually_gt_atTop 0] with n hn hn0
    have hsmall : ∀ i, i < n →
        A (uniformPartition s t n (i + 1)) ω - A (uniformPartition s t n i) ω
          < ε / (|K| + 1) := by
      intro i hi
      have hnn : (0 : ℝ) ≤ ((t : ℝ) - (s : ℝ)) / (n : ℝ) :=
        div_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hst)) (Nat.cast_nonneg n)
      have hdist : dist (uniformPartition s t n (i + 1)) (uniformPartition s t n i) < d := by
        rw [NNReal.dist_eq, coe_uniformPartition_succ_sub hst n i, abs_of_nonneg hnn]
        exact hn
      have hclose := hdlt _ (hpartmem n (i + 1) (Nat.succ_le_of_lt hi)) _ (hpartmem n i hi.le)
        hdist
      rw [Real.dist_eq] at hclose
      exact lt_of_le_of_lt (le_abs_self _) hclose
    calc f n ω ≤ ∑ i ∈ Finset.range n, ε / (|K| + 1)
          * (A (uniformPartition s t n (i + 1)) ω - A (uniformPartition s t n i) ω) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have h1 := hω n i (Finset.mem_range.1 hi)
          have h2 := hsmall i (Finset.mem_range.1 hi)
          nlinarith [h1.1, h2]
      _ = ε / (|K| + 1) * (A t ω - A s ω) := by rw [← Finset.mul_sum, hsumtel ω n hn0.ne']
      _ ≤ ε / (|K| + 1) * |K| :=
          mul_le_mul_of_nonneg_left (hωK.trans (le_abs_self K)) hρ.le
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [abs_nonneg K]
  -- integrability of the terms
  have hterm : ∀ n i, i < n → Integrable (fun ω =>
      (A (uniformPartition s t n (i + 1)) ω - A (uniformPartition s t n i) ω) ^ 2) P := by
    intro n i hi
    refine Integrable.of_bound (((hAm _).sub (hAm _)).pow_const 2).aestronglyMeasurable
      (K ^ 2) ?_
    filter_upwards [hincr] with ω hω
    have h := hω n i hi
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [h.1, h.2]
  have heq : ∀ n, bracketOscillation P A s t n = ∫ ω, f n ω ∂P := by
    intro n
    unfold bracketOscillation
    rw [integral_finsetSum _ fun i hi => hterm n i (Finset.mem_range.1 hi)]
  have hconv := tendsto_integral_of_dominated_convergence (fun _ => K ^ 2)
    (fun n => (hfmeas n).aestronglyMeasurable) (integrable_const _) hdom hlim
  simp only [heq]
  simpa using hconv

/-! ## Dualisation: the `L¹` norm of `P[f | m] - c` is a tested integral -/

/-- **The `L¹` norm of `P[f | m] - c` is realised by a bounded `m`-measurable test function.**
With `Y = P[f | m] - c` and `W = ‖Y‖ Y⁻¹`, one has `‖W‖ ≤ 1` and
`∫ ‖Y‖ = ∫ W f - c ∫ W`. -/
theorem exists_test_integral_norm_condExp_sub [IsProbabilityMeasure P]
    (m : {q : MeasurableSpace Ω // q ≤ mΩ}) {f : Ω → ℂ} (hf : Integrable f P) (c : ℂ) :
    ∃ W : Ω → ℂ, StronglyMeasurable[m.1] W ∧ (∀ ω, ‖W ω‖ ≤ 1) ∧
      ((∫ ω, ‖(P[f | m.1]) ω - c‖ ∂P : ℝ) : ℂ)
        = (∫ ω, W ω * f ω ∂P) - c * ∫ ω, W ω ∂P := by
  classical
  set Y : Ω → ℂ := fun ω => (P[f | m.1]) ω - c with hYdef
  have hYm : Measurable[m.1] Y :=
    (stronglyMeasurable_condExp.sub stronglyMeasurable_const).measurable
  set W : Ω → ℂ := fun ω => ((‖Y ω‖ : ℝ) : ℂ) * (Y ω)⁻¹ with hWdef
  have hφ : Measurable fun z : ℂ => ((‖z‖ : ℝ) : ℂ) * z⁻¹ :=
    (Complex.measurable_ofReal.comp measurable_norm).mul measurable_inv
  have hWm : Measurable[m.1] W := hφ.comp hYm
  have hW : StronglyMeasurable[m.1] W := hWm.stronglyMeasurable
  have hWbdd : ∀ ω, ‖W ω‖ ≤ 1 := by
    intro ω
    simp only [hWdef]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    by_cases h : Y ω = 0
    · simp [h]
    · exact le_of_eq (mul_inv_cancel₀ (norm_ne_zero_iff.2 h))
  have hWY : ∀ ω, W ω * Y ω = ((‖Y ω‖ : ℝ) : ℂ) := by
    intro ω
    simp only [hWdef]
    by_cases h : Y ω = 0
    · simp [h]
    · rw [mul_assoc, inv_mul_cancel₀ h, mul_one]
  refine ⟨W, hW, hWbdd, ?_⟩
  have hWΩ : StronglyMeasurable W := hW.mono m.2
  have hWint : Integrable W P :=
    Integrable.of_bound hWΩ.aestronglyMeasurable 1 (Eventually.of_forall hWbdd)
  have hWf : Integrable (fun ω => W ω * f ω) P :=
    hf.bdd_mul hWΩ.aestronglyMeasurable (Eventually.of_forall hWbdd)
  have hWc : Integrable (fun ω => W ω * (P[f | m.1]) ω) P :=
    integrable_condExp.bdd_mul hWΩ.aestronglyMeasurable (Eventually.of_forall hWbdd)
  have hpull : P[fun ω => W ω * f ω | m.1] =ᵐ[P] fun ω => W ω * (P[f | m.1]) ω :=
    condExp_bilin_of_stronglyMeasurable_left (.mul ℝ ℂ) hW hWf hf
  have h1 : (∫ ω, W ω * f ω ∂P) = ∫ ω, W ω * (P[f | m.1]) ω ∂P := by
    calc (∫ ω, W ω * f ω ∂P) = ∫ ω, (P[fun ω => W ω * f ω | m.1]) ω ∂P :=
          (integral_condExp m.2).symm
      _ = ∫ ω, W ω * (P[f | m.1]) ω ∂P := integral_congr_ae hpull
  have h2 : (∫ ω, W ω * (P[f | m.1]) ω ∂P) - c * ∫ ω, W ω ∂P
      = ∫ ω, W ω * Y ω ∂P := by
    rw [← integral_const_mul, ← integral_sub hWc (hWint.const_mul c)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hYdef]
    ring
  rw [h1, h2]
  simp only [hWY]
  exact (integral_ofReal (𝕜 := ℂ)).symm

/-! ## Bounded convergence for the bracket exponential -/

/-- If `X k → a` in probability with `X k ≥ 0` and `a ≥ 0`, then
`E |e^{-u² X_k/2} - e^{-u² a/2}| → 0`. -/
theorem tendsto_integral_abs_exp_neg_sub [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hXm : ∀ k, Measurable (X k)) (hX0 : ∀ k, ∀ᵐ ω ∂P, 0 ≤ X k ω)
    {a : ℝ} (ha : 0 ≤ a) (hX : TendstoInMeasure P X atTop (fun _ => a)) (u : ℝ) :
    Tendsto (fun k => ∫ ω, |Real.exp (-(u ^ 2 * X k ω / 2)) - Real.exp (-(u ^ 2 * a / 2))| ∂P)
      atTop (𝓝 0) := by
  have hbound : ∀ (k : ℕ) (ρ : ℝ), 0 < ρ →
      (∫ ω, |Real.exp (-(u ^ 2 * X k ω / 2)) - Real.exp (-(u ^ 2 * a / 2))| ∂P)
        ≤ 2 * P.real {ω | ρ ≤ ‖X k ω - a‖} + u ^ 2 / 2 * ρ := by
    intro k ρ hρ
    have hS : MeasurableSet {ω | ρ ≤ ‖X k ω - a‖} :=
      measurableSet_le measurable_const ((hXm k).sub measurable_const).norm
    have hint : Integrable (fun ω => {ω | ρ ≤ ‖X k ω - a‖}.indicator (fun _ => (2 : ℝ)) ω
        + u ^ 2 / 2 * ρ) P :=
      ((integrable_const (2 : ℝ)).indicator hS).add (integrable_const _)
    have hpt : ∀ᵐ ω ∂P, |Real.exp (-(u ^ 2 * X k ω / 2)) - Real.exp (-(u ^ 2 * a / 2))|
        ≤ {ω | ρ ≤ ‖X k ω - a‖}.indicator (fun _ => (2 : ℝ)) ω + u ^ 2 / 2 * ρ := by
      filter_upwards [hX0 k] with ω hω
      have hx0 : 0 ≤ u ^ 2 * X k ω / 2 := div_nonneg (mul_nonneg (sq_nonneg u) hω) (by norm_num)
      have ha0 : 0 ≤ u ^ 2 * a / 2 := div_nonneg (mul_nonneg (sq_nonneg u) ha) (by norm_num)
      have hρ' : 0 ≤ u ^ 2 / 2 * ρ := by positivity
      by_cases hmem : ω ∈ {ω | ρ ≤ ‖X k ω - a‖}
      · rw [Set.indicator_of_mem hmem]
        have h1 : |Real.exp (-(u ^ 2 * X k ω / 2)) - Real.exp (-(u ^ 2 * a / 2))| ≤ 2 := by
          refine (abs_sub _ _).trans ?_
          rw [Real.abs_exp, Real.abs_exp]
          have e1 : Real.exp (-(u ^ 2 * X k ω / 2)) ≤ 1 :=
            Real.exp_le_one_iff.2 (neg_nonpos.2 hx0)
          have e2 : Real.exp (-(u ^ 2 * a / 2)) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 ha0)
          linarith
        linarith
      · rw [Set.indicator_of_notMem hmem, zero_add]
        have hlt : ‖X k ω - a‖ < ρ := not_le.1 hmem
        have hlip := abs_exp_neg_sub_exp_neg_le hx0 ha0
        refine hlip.trans ?_
        rw [show u ^ 2 * X k ω / 2 - u ^ 2 * a / 2 = u ^ 2 / 2 * (X k ω - a) by ring, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 2 / 2)]
        rw [Real.norm_eq_abs] at hlt
        exact mul_le_mul_of_nonneg_left hlt.le (by positivity)
    calc (∫ ω, |Real.exp (-(u ^ 2 * X k ω / 2)) - Real.exp (-(u ^ 2 * a / 2))| ∂P)
        ≤ ∫ ω, ({ω | ρ ≤ ‖X k ω - a‖}.indicator (fun _ => (2 : ℝ)) ω + u ^ 2 / 2 * ρ) ∂P :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _) hint hpt
      _ = 2 * P.real {ω | ρ ≤ ‖X k ω - a‖} + u ^ 2 / 2 * ρ := by
          rw [integral_add ((integrable_const (2 : ℝ)).indicator hS) (integrable_const _),
            integral_indicator_const _ hS, integral_const]
          simp [smul_eq_mul, mul_comm]
  rw [tendsto_order]
  refine ⟨fun c hc => Eventually.of_forall fun k =>
    lt_of_lt_of_le hc (integral_nonneg fun ω => abs_nonneg _), fun c hc => ?_⟩
  have hρ : 0 < c / (u ^ 2 + 4) := by positivity
  have hmeas := (tendstoInMeasure_iff_measureReal_norm.mp hX) (c / (u ^ 2 + 4)) hρ
  filter_upwards [hmeas.eventually (gt_mem_nhds hρ)] with k hk
  have hk' : P.real {ω | c / (u ^ 2 + 4) ≤ ‖X k ω - a‖} < c / (u ^ 2 + 4) := hk
  have hfinal : 2 * (c / (u ^ 2 + 4)) + u ^ 2 / 2 * (c / (u ^ 2 + 4)) ≤ c := by
    have hpos : (0 : ℝ) < u ^ 2 + 4 := by positivity
    have : (2 + u ^ 2 / 2) * (c / (u ^ 2 + 4)) ≤ c := by
      rw [mul_div_assoc', div_le_iff₀ hpos]
      nlinarith [sq_nonneg u]
    linarith
  calc (∫ ω, |Real.exp (-(u ^ 2 * X k ω / 2)) - Real.exp (-(u ^ 2 * a / 2))| ∂P)
      ≤ 2 * P.real {ω | c / (u ^ 2 + 4) ≤ ‖X k ω - a‖} + u ^ 2 / 2 * (c / (u ^ 2 + 4)) :=
        hbound k _ hρ
    _ < 2 * (c / (u ^ 2 + 4)) + u ^ 2 / 2 * (c / (u ^ 2 + 4)) := by linarith
    _ ≤ c := hfinal

/-! ## The localized array and the main theorem -/

/-- **A localized martingale array with an approximate bracket.**  For every `k`, `N k` is a
square-integrable martingale for `𝔽 k` whose bracket `A k` is adapted, monotone on `[s, t]`,
bounded by `K` over `[s, t]`, and satisfies the bracket identity; the quadratic oscillation of
`A k` along the uniform partitions vanishes; the Lindeberg sums vanish in the double limit
(`k → ∞`, then `n → ∞`); and `A k t - A k s → C (t - s)` in probability. -/
structure LocalizedBracketArray (P : Measure Ω) (𝔽 : ℕ → Filtration ℝ≥0 mΩ)
    (N A : ℕ → ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (C K : ℝ) : Prop where
  martingale : ∀ k, Martingale (N k) (𝔽 k) P
  memLp : ∀ k (v : ℝ≥0), MemLp (N k v) 2 P
  adapted : ∀ k (v : ℝ≥0), Measurable[𝔽 k v] (A k v)
  monotone : ∀ k, ∀ᵐ ω ∂P, MonotoneOn (fun v : ℝ≥0 => A k v ω) (Set.Icc s t)
  bounded : ∀ k, ∀ᵐ ω ∂P, A k t ω - A k s ω ≤ K
  bracket : ∀ k (a b : ℝ≥0), s ≤ a → a ≤ b → b ≤ t →
    P[fun ω => (N k b ω - N k a ω) ^ 2 | 𝔽 k a] =ᵐ[P] P[fun ω => A k b ω - A k a ω | 𝔽 k a]
  oscillation : ∀ k, Tendsto (fun n => bracketOscillation P (A k) s t n) atTop (𝓝 0)
  lindeberg : ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ k in atTop, ∀ᶠ n in atTop, lindebergSum P (N k) δ s t n ≤ ε
  limit : TendstoInMeasure P (fun k ω => A k t ω - A k s ω) atTop
    (fun _ => C * ((t : ℝ) - (s : ℝ)))

/-- **Producer from compensated-square martingales.**  The bracket identity, adaptedness of
the bracket and the vanishing oscillation all follow from `N k² - A k` being a martingale and
`A k` having continuous paths on `[s, t]`. -/
theorem LocalizedBracketArray.of_square_martingale [IsProbabilityMeasure P]
    {𝔽 : ℕ → Filtration ℝ≥0 mΩ} {N A : ℕ → ℝ≥0 → Ω → ℝ} {s t : ℝ≥0} (hst : s ≤ t) {C K : ℝ}
    (hN : ∀ k, Martingale (N k) (𝔽 k) P)
    (hNA : ∀ k, Martingale (fun v ω => N k v ω ^ 2 - A k v ω) (𝔽 k) P)
    (h2 : ∀ k (v : ℝ≥0), MemLp (N k v) 2 P)
    (hcont : ∀ k, ∀ᵐ ω ∂P, ContinuousOn (fun v : ℝ≥0 => A k v ω) (Set.Icc s t))
    (hmono : ∀ k, ∀ᵐ ω ∂P, MonotoneOn (fun v : ℝ≥0 => A k v ω) (Set.Icc s t))
    (hbdd : ∀ k, ∀ᵐ ω ∂P, A k t ω - A k s ω ≤ K)
    (hlind : ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, ∀ᶠ n in atTop, lindebergSum P (N k) δ s t n ≤ ε)
    (hlimit : TendstoInMeasure P (fun k ω => A k t ω - A k s ω) atTop
      (fun _ => C * ((t : ℝ) - (s : ℝ)))) :
    LocalizedBracketArray P 𝔽 N A s t C K := by
  have hadapt : ∀ k (v : ℝ≥0), Measurable[𝔽 k v] (A k v) := by
    intro k v
    have h1 : StronglyMeasurable[𝔽 k v] (fun ω => N k v ω ^ 2 - A k v ω) :=
      (hNA k).stronglyMeasurable v
    have h2' : StronglyMeasurable[𝔽 k v] (fun ω => N k v ω ^ 2) :=
      ((hN k).stronglyMeasurable v).pow 2
    have heq : A k v = fun ω => N k v ω ^ 2 - (N k v ω ^ 2 - A k v ω) := by
      funext ω
      ring
    rw [heq]
    exact (h2'.sub h1).measurable
  exact
    { martingale := hN
      memLp := h2
      adapted := hadapt
      monotone := hmono
      bounded := hbdd
      bracket := fun k a b _ hab _ =>
        condExp_increment_sq_eq_condExp_bracket (hN k) (hNA k) (h2 k) hab
      oscillation := fun k => tendsto_bracketOscillation
        (fun v => (hadapt k v).mono ((𝔽 k).le v) le_rfl) hst (hcont k) (hmono k) (hbdd k)
      lindeberg := hlind
      limit := hlimit }

/-- **The compensated tested integrals converge to `E[W_k]`**, uniformly over bounded
`𝔽 k s`-measurable test functions: first `n → ∞` (the oscillation), then `k → ∞` (the
Lindeberg sums), with `δ` and `η` chosen from `ε` beforehand. -/
theorem tendsto_norm_integral_test_mul_cexp_mul_exp_sub [IsProbabilityMeasure P]
    {𝔽 : ℕ → Filtration ℝ≥0 mΩ} {N A : ℕ → ℝ≥0 → Ω → ℝ} {s t : ℝ≥0} (hst : s ≤ t)
    {C K : ℝ} (hK : 0 ≤ K) (h : LocalizedBracketArray P 𝔽 N A s t C K) (u : ℝ)
    {W : ℕ → Ω → ℂ} (hWmeas : ∀ k, StronglyMeasurable[𝔽 k s] (W k))
    (hWbdd : ∀ k ω, ‖W k ω‖ ≤ 1) :
    Tendsto (fun k => ‖(∫ ω, W k ω * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
          * ((Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2) : ℝ) : ℂ) ∂P) - ∫ ω, W k ω ∂P‖)
      atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun c hc => Eventually.of_forall fun k => lt_of_lt_of_le hc (norm_nonneg _),
    fun ε hε => ?_⟩
  -- the coefficients
  obtain ⟨a₃, ha₃, ha₃0⟩ : ∃ a₃ : ℝ,
      a₃ = Real.exp (u ^ 2 * K / 2) * (2 / 9 * |u| ^ 3 * K) ∧ 0 ≤ a₃ :=
    ⟨_, rfl, by positivity⟩
  obtain ⟨a₂, ha₂, ha₂0⟩ : ∃ a₂ : ℝ,
      a₂ = Real.exp (u ^ 2 * K / 2) * (u ^ 2 / 2 * (u ^ 2 / 2 * K)) ∧ 0 ≤ a₂ :=
    ⟨_, rfl, by positivity⟩
  obtain ⟨a₄, ha₄, ha₄0⟩ : ∃ a₄ : ℝ, a₄ = Real.exp (u ^ 2 * K / 2) * (4 * u ^ 2) ∧ 0 ≤ a₄ :=
    ⟨_, rfl, by positivity⟩
  -- the truncation level
  obtain ⟨δ, hδpos, huδ, hδterm⟩ : ∃ δ : ℝ, 0 < δ ∧ |u| * δ ≤ 1 ∧ a₃ * δ ≤ ε / 5 := by
    refine ⟨min (1 / (|u| + 1)) (ε / (5 * (a₃ + 1))),
      lt_min (by positivity) (div_pos hε (by linarith)), ?_, ?_⟩
    · have h1 : min (1 / (|u| + 1)) (ε / (5 * (a₃ + 1))) ≤ 1 / (|u| + 1) := min_le_left _ _
      calc |u| * min (1 / (|u| + 1)) (ε / (5 * (a₃ + 1)))
          ≤ |u| * (1 / (|u| + 1)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg u)
        _ ≤ 1 := by
            rw [mul_one_div, div_le_one (by positivity)]
            linarith
    · have h1 : min (1 / (|u| + 1)) (ε / (5 * (a₃ + 1))) ≤ ε / (5 * (a₃ + 1)) :=
        min_le_right _ _
      calc a₃ * min (1 / (|u| + 1)) (ε / (5 * (a₃ + 1)))
          ≤ a₃ * (ε / (5 * (a₃ + 1))) := mul_le_mul_of_nonneg_left h1 ha₃0
        _ ≤ ε / 5 := by
            rw [mul_div_assoc', div_le_iff₀ (by linarith)]
            nlinarith
  -- the free parameter
  obtain ⟨η, hηpos, hηterm⟩ : ∃ η : ℝ, 0 < η ∧ a₂ * η ≤ ε / 5 := by
    refine ⟨ε / (5 * (a₂ + 1)), div_pos hε (by linarith), ?_⟩
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  obtain ⟨a₁, ha₁, ha₁0⟩ : ∃ a₁ : ℝ, a₁ = Real.exp (u ^ 2 * K / 2)
      * (Real.exp (u ^ 2 * K / 2) * (u ^ 4 / 4) + u ^ 2 / 2 * (η⁻¹ / 2)) ∧ 0 ≤ a₁ :=
    ⟨_, rfl, by positivity⟩
  -- the Lindeberg eventuality in `k`
  have hlindk := h.lindeberg δ hδpos (ε / (5 * (a₄ + 1))) (div_pos hε (by linarith))
  filter_upwards [hlindk] with k hk
  -- the oscillation eventuality in `n`
  have hoscn : ∀ᶠ n in atTop, a₁ * bracketOscillation P (A k) s t n ≤ ε / 5 := by
    have h1 := (h.oscillation k).eventually
      (gt_mem_nhds (show (0 : ℝ) < ε / (5 * (a₁ + 1)) from div_pos hε (by linarith)))
    filter_upwards [h1] with n hn
    calc a₁ * bracketOscillation P (A k) s t n
        ≤ a₁ * (ε / (5 * (a₁ + 1))) := mul_le_mul_of_nonneg_left hn.le ha₁0
      _ ≤ ε / 5 := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]
          nlinarith
  obtain ⟨n, hn0, hnosc, hnlind⟩ : ∃ n : ℕ, n ≠ 0
      ∧ a₁ * bracketOscillation P (A k) s t n ≤ ε / 5
      ∧ lindebergSum P (N k) δ s t n ≤ ε / (5 * (a₄ + 1)) := by
    obtain ⟨n, h1, h2, h3⟩ := ((eventually_ne_atTop 0).and (hoscn.and hk)).exists
    exact ⟨n, h1, h2, h3⟩
  have hlindterm : a₄ * lindebergSum P (N k) δ s t n ≤ ε / 5 := by
    calc a₄ * lindebergSum P (N k) δ s t n
        ≤ a₄ * (ε / (5 * (a₄ + 1))) := mul_le_mul_of_nonneg_left hnlind ha₄0
      _ ≤ ε / 5 := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]
          nlinarith
  have hB := norm_integral_test_mul_cexp_increment_mul_exp_sub_le (h.martingale k) (h.memLp k)
    (h.adapted k) hst (h.monotone k) (h.bounded k) (h.bracket k) (hWmeas k) (hWbdd k)
    hδpos.le huδ hηpos hn0
  have hexpand : Real.exp (u ^ 2 * K / 2) * (Real.exp (u ^ 2 * K / 2) * (u ^ 4 / 4)
        * bracketOscillation P (A k) s t n
      + u ^ 2 / 2 * (η / 2 * u ^ 2 * K + η⁻¹ / 2 * bracketOscillation P (A k) s t n)
      + 2 / 9 * |u| ^ 3 * δ * K + 4 * u ^ 2 * lindebergSum P (N k) δ s t n)
      = a₁ * bracketOscillation P (A k) s t n + a₂ * η + a₃ * δ
        + a₄ * lindebergSum P (N k) δ s t n := by
    rw [ha₁, ha₂, ha₃, ha₄]
    ring
  calc _ ≤ _ := hB
    _ = a₁ * bracketOscillation P (A k) s t n + a₂ * η + a₃ * δ
        + a₄ * lindebergSum P (N k) δ s t n := hexpand
    _ ≤ ε / 5 + ε / 5 + ε / 5 + ε / 5 := by linarith [hnosc, hηterm, hδterm, hlindterm]
    _ < ε := by linarith

/-- **The approximate-bracket martingale CLT, one increment, conditional, in `L¹`.**
For a `LocalizedBracketArray` with `C, K ≥ 0` and `s ≤ t`,

  `∫ ‖ P[e^{iu(N_k t - N_k s)} | 𝔽_k s] - e^{-u² C (t-s)/2} ‖ dP ⟶ 0`.

No Gaussianity of the limit, no independence and no exact bracket is assumed: the bracket is
random and only converges in probability. -/
theorem tendsto_integral_norm_condExp_cexp_sub_of_localized [IsProbabilityMeasure P]
    {𝔽 : ℕ → Filtration ℝ≥0 mΩ} {N A : ℕ → ℝ≥0 → Ω → ℝ} {s t : ℝ≥0} (hst : s ≤ t)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (h : LocalizedBracketArray P 𝔽 N A s t C K) (u : ℝ) :
    Tendsto (fun k => ∫ ω, ‖(P[fun ω => Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
        | 𝔽 k s]) ω - ((Real.exp (-(u ^ 2 * (C * ((t : ℝ) - (s : ℝ))) / 2)) : ℝ) : ℂ)‖ ∂P)
      atTop (𝓝 0) := by
  classical
  have hts : (0 : ℝ) ≤ (t : ℝ) - (s : ℝ) := sub_nonneg.2 (NNReal.coe_le_coe.2 hst)
  have hCts : 0 ≤ C * ((t : ℝ) - (s : ℝ)) := mul_nonneg hC hts
  set c₀ : ℝ := Real.exp (-(u ^ 2 * (C * ((t : ℝ) - (s : ℝ))) / 2)) with hc₀
  have hc₀0 : 0 ≤ c₀ := (Real.exp_pos _).le
  have hc₀1 : c₀ ≤ 1 := by
    refine Real.exp_le_one_iff.2 ?_
    have : 0 ≤ u ^ 2 * (C * ((t : ℝ) - (s : ℝ))) := mul_nonneg (sq_nonneg u) hCts
    linarith
  have hccnorm : ‖((c₀ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc₀0]
    exact hc₀1
  have hNm : ∀ k (v : ℝ≥0), Measurable (N k v) := fun k v =>
    ((h.martingale k).stronglyMeasurable v).measurable.mono ((𝔽 k).le v) le_rfl
  have hAm : ∀ k (v : ℝ≥0), Measurable (A k v) := fun k v =>
    (h.adapted k v).mono ((𝔽 k).le v) le_rfl
  have hA0 : ∀ k, ∀ᵐ ω ∂P, 0 ≤ A k t ω - A k s ω := by
    intro k
    filter_upwards [h.monotone k] with ω hω
    exact sub_nonneg.2 (hω ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst)
  -- the test functions realising the `L¹` norms
  have hdual : ∀ k, ∃ W : Ω → ℂ, StronglyMeasurable[𝔽 k s] W ∧ (∀ ω, ‖W ω‖ ≤ 1) ∧
      ((∫ ω, ‖(P[fun ω => Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I) | 𝔽 k s]) ω
          - ((c₀ : ℝ) : ℂ)‖ ∂P : ℝ) : ℂ)
        = (∫ ω, W ω * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I) ∂P)
          - ((c₀ : ℝ) : ℂ) * ∫ ω, W ω ∂P := by
    intro k
    exact exists_test_integral_norm_condExp_sub ⟨𝔽 k s, (𝔽 k).le s⟩
      (integrable_cexp_ofReal_mul_I (((hNm k t).sub (hNm k s)).const_mul u)) _
  choose W hWmeas hWbdd hWeq using hdual
  -- the two vanishing pieces
  have hpiece1 : Tendsto (fun k => Real.exp (u ^ 2 * K / 2)
      * ∫ ω, |Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) - c₀| ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_abs_exp_neg_sub (X := fun k ω => A k t ω - A k s ω)
      (fun k => (hAm k t).sub (hAm k s)) hA0 hCts h.limit u
    simpa using this.const_mul (Real.exp (u ^ 2 * K / 2))
  have hpiece2 := tendsto_norm_integral_test_mul_cexp_mul_exp_sub hst hK h u hWmeas hWbdd
  -- the bound
  have hbound : ∀ k,
      (∫ ω, ‖(P[fun ω => Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I) | 𝔽 k s]) ω
          - ((c₀ : ℝ) : ℂ)‖ ∂P)
      ≤ Real.exp (u ^ 2 * K / 2)
          * (∫ ω, |Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) - c₀| ∂P)
        + ‖(∫ ω, W k ω * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
            * ((Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2) : ℝ) : ℂ) ∂P) - ∫ ω, W k ω ∂P‖ := by
    intro k
    have hfm : Measurable fun ω => Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I) :=
      Complex.measurable_exp.comp
        ((Complex.measurable_ofReal.comp (((hNm k t).sub (hNm k s)).const_mul u)).mul_const _)
    have hfnorm : ∀ ω, ‖Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)‖ = 1 :=
      fun ω => Complex.norm_exp_ofReal_mul_I _
    have hxm : Measurable fun ω => u ^ 2 * (A k t ω - A k s ω) / 2 :=
      (((hAm k t).sub (hAm k s)).const_mul _).div_const _
    have hWΩ : StronglyMeasurable (W k) := (hWmeas k).mono ((𝔽 k).le s)
    have hxK : ∀ᵐ ω ∂P, u ^ 2 * (A k t ω - A k s ω) / 2 ≤ u ^ 2 * K / 2 := by
      filter_upwards [h.bounded k] with ω hω
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hω (sq_nonneg u)) (by norm_num)
    have hx0 : ∀ᵐ ω ∂P, 0 ≤ u ^ 2 * (A k t ω - A k s ω) / 2 := by
      filter_upwards [hA0 k] with ω hω
      exact div_nonneg (mul_nonneg (sq_nonneg u) hω) (by norm_num)
    -- the pointwise identity `W f = W f e^x (e^{-x} - c) + c (W f e^x)`
    have hid : ∀ ω, W k ω * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
        = W k ω * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
            * ((Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2) : ℝ) : ℂ)
            * (((Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) : ℝ) : ℂ) - ((c₀ : ℝ) : ℂ))
          + ((c₀ : ℝ) : ℂ) * (W k ω * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
            * ((Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2) : ℝ) : ℂ)) := by
      intro ω
      have hee : ((Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2) : ℝ) : ℂ)
          * ((Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
          Complex.ofReal_one]
      linear_combination
        (-(W k ω * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I))) * hee
    -- integrability
    have hWfx : Integrable (fun ω => W k ω
        * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
        * ((Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2) : ℝ) : ℂ)) P := by
      refine Integrable.of_bound ?_ (Real.exp (u ^ 2 * K / 2)) ?_
      · have hsm : StronglyMeasurable fun ω => W k ω
            * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
            * ((Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2) : ℝ) : ℂ) :=
          (hWΩ.mul hfm.stronglyMeasurable).mul
            (Complex.continuous_ofReal.comp_stronglyMeasurable
              (Real.continuous_exp.comp_stronglyMeasurable hxm.stronglyMeasurable))
        exact hsm.aestronglyMeasurable
      · filter_upwards [hxK] with ω hω
        rw [norm_mul, norm_mul, hfnorm, mul_one, Complex.norm_real, Real.norm_eq_abs,
          Real.abs_exp]
        calc ‖W k ω‖ * Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2)
            ≤ 1 * Real.exp (u ^ 2 * K / 2) :=
              mul_le_mul (hWbdd k ω) (Real.exp_le_exp.2 hω) (Real.exp_pos _).le zero_le_one
          _ = Real.exp (u ^ 2 * K / 2) := one_mul _
    have habsm : Measurable fun ω =>
        |Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) - c₀| := by
      have h1 : Measurable fun ω => -(u ^ 2 * (A k t ω - A k s ω) / 2) := hxm.neg
      have h2 : Measurable fun ω => Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) - c₀ :=
        (Real.measurable_exp.comp h1).sub measurable_const
      exact continuous_abs.measurable.comp h2
    have habsbdd : ∀ᵐ ω ∂P, |Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) - c₀| ≤ 2 := by
      filter_upwards [hx0] with ω hω
      refine (abs_sub _ _).trans ?_
      rw [Real.abs_exp, abs_of_nonneg hc₀0]
      have : Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 hω)
      linarith
    have habsint : Integrable (fun ω =>
        |Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) - c₀|) P :=
      Integrable.of_bound habsm.aestronglyMeasurable 2
        (habsbdd.mono fun ω hω => by rw [Real.norm_eq_abs, abs_abs]; exact hω)
    have hWfxc : Integrable (fun ω => W k ω
        * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
        * ((Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2) : ℝ) : ℂ)
        * (((Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) : ℝ) : ℂ) - ((c₀ : ℝ) : ℂ))) P := by
      refine hWfx.mul_bdd (c := 2) ?_ ?_
      · exact ((Complex.continuous_ofReal.comp_stronglyMeasurable
          (Real.continuous_exp.comp_stronglyMeasurable hxm.neg.stronglyMeasurable)).sub
          stronglyMeasurable_const).aestronglyMeasurable
      · filter_upwards [habsbdd] with ω hω
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact hω
    -- the split
    have hsplit : (∫ ω, W k ω * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I) ∂P)
        - ((c₀ : ℝ) : ℂ) * ∫ ω, W k ω ∂P
        = (∫ ω, W k ω * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
            * ((Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2) : ℝ) : ℂ)
            * (((Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) : ℝ) : ℂ)
              - ((c₀ : ℝ) : ℂ)) ∂P)
          + ((c₀ : ℝ) : ℂ) * ((∫ ω, W k ω
              * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
              * ((Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2) : ℝ) : ℂ) ∂P)
            - ∫ ω, W k ω ∂P) := by
      have e1 : (∫ ω, W k ω * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I) ∂P)
          = (∫ ω, W k ω * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
              * ((Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2) : ℝ) : ℂ)
              * (((Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) : ℝ) : ℂ)
                - ((c₀ : ℝ) : ℂ)) ∂P)
            + ((c₀ : ℝ) : ℂ) * ∫ ω, W k ω
                * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
                * ((Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2) : ℝ) : ℂ) ∂P := by
        rw [← integral_const_mul, ← integral_add hWfxc (hWfx.const_mul _)]
        exact integral_congr_ae (Eventually.of_forall hid)
      rw [e1]
      ring
    have hfirst : ‖∫ ω, W k ω * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
            * ((Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2) : ℝ) : ℂ)
            * (((Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) : ℝ) : ℂ)
              - ((c₀ : ℝ) : ℂ)) ∂P‖
        ≤ Real.exp (u ^ 2 * K / 2)
            * ∫ ω, |Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) - c₀| ∂P := by
      calc _ ≤ ∫ ω, ‖W k ω * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
            * ((Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2) : ℝ) : ℂ)
            * (((Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) : ℝ) : ℂ)
              - ((c₀ : ℝ) : ℂ))‖ ∂P := norm_integral_le_integral_norm _
        _ ≤ ∫ ω, Real.exp (u ^ 2 * K / 2)
              * |Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) - c₀| ∂P := by
            refine integral_mono_ae hWfxc.norm (habsint.const_mul _) ?_
            filter_upwards [hxK] with ω hω
            rw [norm_mul, norm_mul, norm_mul, hfnorm, mul_one, Complex.norm_real,
              Real.norm_eq_abs, Real.abs_exp, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_eq_abs]
            have h1 : ‖W k ω‖ * Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2)
                ≤ Real.exp (u ^ 2 * K / 2) := by
              calc ‖W k ω‖ * Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2)
                  ≤ 1 * Real.exp (u ^ 2 * K / 2) :=
                    mul_le_mul (hWbdd k ω) (Real.exp_le_exp.2 hω) (Real.exp_pos _).le
                      zero_le_one
                _ = Real.exp (u ^ 2 * K / 2) := one_mul _
            exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = Real.exp (u ^ 2 * K / 2)
              * ∫ ω, |Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) - c₀| ∂P :=
            integral_const_mul _ _
    have hnorm : (∫ ω, ‖(P[fun ω => Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
          | 𝔽 k s]) ω - ((c₀ : ℝ) : ℂ)‖ ∂P)
        = ‖(∫ ω, W k ω * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I) ∂P)
            - ((c₀ : ℝ) : ℂ) * ∫ ω, W k ω ∂P‖ := by
      rw [← hWeq k, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
    rw [hnorm, hsplit]
    calc ‖_ + ((c₀ : ℝ) : ℂ) * _‖ ≤ ‖_‖ + ‖((c₀ : ℝ) : ℂ) * _‖ := norm_add_le _ _
      _ ≤ Real.exp (u ^ 2 * K / 2)
            * (∫ ω, |Real.exp (-(u ^ 2 * (A k t ω - A k s ω) / 2)) - c₀| ∂P)
          + 1 * ‖(∫ ω, W k ω * Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
              * ((Real.exp (u ^ 2 * (A k t ω - A k s ω) / 2) : ℝ) : ℂ) ∂P)
            - ∫ ω, W k ω ∂P‖ := by
          refine add_le_add hfirst ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right hccnorm (norm_nonneg _)
      _ = _ := by rw [one_mul]
  refine squeeze_zero (fun k => integral_nonneg fun ω => norm_nonneg _) hbound ?_
  simpa using hpiece1.add hpiece2

/-! ## Unlocalisation -/

/-- The `L¹` distance between the conditional characteristic functions of two real random
variables is at most twice the probability that they differ. -/
theorem integral_norm_condExp_cexp_sub_condExp_cexp_le [IsProbabilityMeasure P]
    (m : {q : MeasurableSpace Ω // q ≤ mΩ}) {X X' : Ω → ℝ} (hX : Measurable X)
    (hX' : Measurable X') (u : ℝ) :
    (∫ ω, ‖(P[fun ω => Complex.exp ((u * X ω : ℝ) * Complex.I) | m.1]) ω
        - (P[fun ω => Complex.exp ((u * X' ω : ℝ) * Complex.I) | m.1]) ω‖ ∂P)
      ≤ 2 * P.real {ω | X ω ≠ X' ω} := by
  classical
  set f : Ω → ℂ := fun ω => Complex.exp ((u * X ω : ℝ) * Complex.I) with hf
  set g : Ω → ℂ := fun ω => Complex.exp ((u * X' ω : ℝ) * Complex.I) with hg
  have hfint : Integrable f P := integrable_cexp_ofReal_mul_I (hX.const_mul u)
  have hgint : Integrable g P := integrable_cexp_ofReal_mul_I (hX'.const_mul u)
  have hS : MeasurableSet {ω | X ω ≠ X' ω} := by
    have hset : {ω | X ω ≠ X' ω} = (fun ω => X ω - X' ω) ⁻¹' ({0}ᶜ) := by
      ext ω
      simp [sub_eq_zero]
    rw [hset]
    exact (hX.sub hX') (measurableSet_singleton 0).compl
  have hsub : P[f | m.1] - P[g | m.1] =ᵐ[P] P[f - g | m.1] := (condExp_sub hfint hgint m.1).symm
  have hjensen := norm_condExp_le (μ := P) (m := m.1) (f - g)
  have hpt : ∀ ω, ‖(f - g) ω‖ ≤ {ω | X ω ≠ X' ω}.indicator (fun _ => (2 : ℝ)) ω := by
    intro ω
    by_cases hω : X ω = X' ω
    · have h0 : (f - g) ω = 0 := by simp [hf, hg, hω]
      rw [h0, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => by norm_num) ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | X ω ≠ X' ω} from hω)]
      calc ‖(f - g) ω‖ = ‖f ω - g ω‖ := rfl
        _ ≤ ‖f ω‖ + ‖g ω‖ := norm_sub_le _ _
        _ = 2 := by
            simp only [hf, hg, Complex.norm_exp_ofReal_mul_I]
            norm_num
  calc (∫ ω, ‖(P[f | m.1]) ω - (P[g | m.1]) ω‖ ∂P)
      = ∫ ω, ‖(P[f - g | m.1]) ω‖ ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hsub] with ω hω
        rw [← hω, Pi.sub_apply]
    _ ≤ ∫ ω, (P[fun ω => ‖(f - g) ω‖ | m.1]) ω ∂P :=
        integral_mono_ae integrable_condExp.norm integrable_condExp hjensen
    _ = ∫ ω, ‖(f - g) ω‖ ∂P := integral_condExp m.2
    _ ≤ ∫ ω, {ω | X ω ≠ X' ω}.indicator (fun _ => (2 : ℝ)) ω ∂P :=
        integral_mono (hfint.sub hgint).norm ((integrable_const _).indicator hS) hpt
    _ = 2 * P.real {ω | X ω ≠ X' ω} := by
        rw [integral_indicator_const _ hS, smul_eq_mul, mul_comm]

/-- **Unlocalised form.**  If for some `K` there is a `LocalizedBracketArray` `(N', A')`
whose martingales agree with `N` at the times `s` and `t` outside events of vanishing
probability, then the conditional characteristic functions of the increments of `N` have the
Gaussian `L¹` limit.  In the application `N'` is `N` stopped at the first time its bracket
reaches `K`; the exit probability vanishes because the bracket increment converges in
probability to `C (t - s) < K`. -/
theorem tendsto_integral_norm_condExp_cexp_sub_of_exists_localized [IsProbabilityMeasure P]
    {𝔽 : ℕ → Filtration ℝ≥0 mΩ} {N : ℕ → ℝ≥0 → Ω → ℝ} (hNm : ∀ k (v : ℝ≥0), Measurable (N k v))
    {s t : ℝ≥0} (hst : s ≤ t) {C : ℝ} (hC : 0 ≤ C)
    (hloc : ∃ (N' A' : ℕ → ℝ≥0 → Ω → ℝ) (K : ℝ), 0 ≤ K
      ∧ LocalizedBracketArray P 𝔽 N' A' s t C K
      ∧ Tendsto (fun k => P.real {ω | ¬ (N' k t ω = N k t ω ∧ N' k s ω = N k s ω)}) atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun k => ∫ ω, ‖(P[fun ω => Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
        | 𝔽 k s]) ω - ((Real.exp (-(u ^ 2 * (C * ((t : ℝ) - (s : ℝ))) / 2)) : ℝ) : ℂ)‖ ∂P)
      atTop (𝓝 0) := by
  obtain ⟨N', A', K, hK, h, hexit⟩ := hloc
  have hmain := tendsto_integral_norm_condExp_cexp_sub_of_localized hst hC hK h u
  have hN'm : ∀ k (v : ℝ≥0), Measurable (N' k v) := fun k v =>
    ((h.martingale k).stronglyMeasurable v).measurable.mono ((𝔽 k).le v) le_rfl
  have hbound : ∀ k,
      (∫ ω, ‖(P[fun ω => Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I) | 𝔽 k s]) ω
          - ((Real.exp (-(u ^ 2 * (C * ((t : ℝ) - (s : ℝ))) / 2)) : ℝ) : ℂ)‖ ∂P)
      ≤ 2 * P.real {ω | ¬ (N' k t ω = N k t ω ∧ N' k s ω = N k s ω)}
        + ∫ ω, ‖(P[fun ω => Complex.exp ((u * (N' k t ω - N' k s ω) : ℝ) * Complex.I)
            | 𝔽 k s]) ω
          - ((Real.exp (-(u ^ 2 * (C * ((t : ℝ) - (s : ℝ))) / 2)) : ℝ) : ℂ)‖ ∂P := by
    intro k
    have htri : ∀ ω,
        ‖(P[fun ω => Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I) | 𝔽 k s]) ω
            - ((Real.exp (-(u ^ 2 * (C * ((t : ℝ) - (s : ℝ))) / 2)) : ℝ) : ℂ)‖
        ≤ ‖(P[fun ω => Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I) | 𝔽 k s]) ω
            - (P[fun ω => Complex.exp ((u * (N' k t ω - N' k s ω) : ℝ) * Complex.I)
              | 𝔽 k s]) ω‖
          + ‖(P[fun ω => Complex.exp ((u * (N' k t ω - N' k s ω) : ℝ) * Complex.I)
              | 𝔽 k s]) ω
            - ((Real.exp (-(u ^ 2 * (C * ((t : ℝ) - (s : ℝ))) / 2)) : ℝ) : ℂ)‖ := by
      intro ω
      rw [← sub_add_sub_cancel _ (P[fun ω => Complex.exp
        ((u * (N' k t ω - N' k s ω) : ℝ) * Complex.I) | 𝔽 k s] ω)]
      exact norm_add_le _ _
    have hsubset : {ω | N k t ω - N k s ω ≠ N' k t ω - N' k s ω}
        ⊆ {ω | ¬ (N' k t ω = N k t ω ∧ N' k s ω = N k s ω)} := by
      intro ω hω hand
      apply hω
      rw [hand.1, hand.2]
    calc (∫ ω, ‖(P[fun ω => Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
            | 𝔽 k s]) ω
          - ((Real.exp (-(u ^ 2 * (C * ((t : ℝ) - (s : ℝ))) / 2)) : ℝ) : ℂ)‖ ∂P)
        ≤ ∫ ω, (‖(P[fun ω => Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
              | 𝔽 k s]) ω
            - (P[fun ω => Complex.exp ((u * (N' k t ω - N' k s ω) : ℝ) * Complex.I)
              | 𝔽 k s]) ω‖
          + ‖(P[fun ω => Complex.exp ((u * (N' k t ω - N' k s ω) : ℝ) * Complex.I)
              | 𝔽 k s]) ω
            - ((Real.exp (-(u ^ 2 * (C * ((t : ℝ) - (s : ℝ))) / 2)) : ℝ) : ℂ)‖) ∂P :=
          integral_mono (integrable_condExp.sub (integrable_const _)).norm
            ((integrable_condExp.sub integrable_condExp).norm.add
              (integrable_condExp.sub (integrable_const _)).norm) htri
      _ = (∫ ω, ‖(P[fun ω => Complex.exp ((u * (N k t ω - N k s ω) : ℝ) * Complex.I)
              | 𝔽 k s]) ω
            - (P[fun ω => Complex.exp ((u * (N' k t ω - N' k s ω) : ℝ) * Complex.I)
              | 𝔽 k s]) ω‖ ∂P)
          + ∫ ω, ‖(P[fun ω => Complex.exp ((u * (N' k t ω - N' k s ω) : ℝ) * Complex.I)
              | 𝔽 k s]) ω
            - ((Real.exp (-(u ^ 2 * (C * ((t : ℝ) - (s : ℝ))) / 2)) : ℝ) : ℂ)‖ ∂P :=
          integral_add (integrable_condExp.sub integrable_condExp).norm
            (integrable_condExp.sub (integrable_const _)).norm
      _ ≤ 2 * P.real {ω | N k t ω - N k s ω ≠ N' k t ω - N' k s ω}
          + ∫ ω, ‖(P[fun ω => Complex.exp ((u * (N' k t ω - N' k s ω) : ℝ) * Complex.I)
              | 𝔽 k s]) ω
            - ((Real.exp (-(u ^ 2 * (C * ((t : ℝ) - (s : ℝ))) / 2)) : ℝ) : ℂ)‖ ∂P :=
          add_le_add (integral_norm_condExp_cexp_sub_condExp_cexp_le ⟨𝔽 k s, (𝔽 k).le s⟩
            ((hNm k t).sub (hNm k s)) ((hN'm k t).sub (hN'm k s)) u) le_rfl
      _ ≤ 2 * P.real {ω | ¬ (N' k t ω = N k t ω ∧ N' k s ω = N k s ω)}
          + ∫ ω, ‖(P[fun ω => Complex.exp ((u * (N' k t ω - N' k s ω) : ℝ) * Complex.I)
              | 𝔽 k s]) ω
            - ((Real.exp (-(u ^ 2 * (C * ((t : ℝ) - (s : ℝ))) / 2)) : ℝ) : ℂ)‖ ∂P :=
          add_le_add (mul_le_mul_of_nonneg_left (measureReal_mono hsubset) (by norm_num)) le_rfl
  refine squeeze_zero (fun k => integral_nonneg fun ω => norm_nonneg _) hbound ?_
  simpa using (hexit.const_mul 2).add hmain

/-! ## Satisfiability: the exact deterministic bracket -/

end ReflectedGMS.ApproximateBracketCLT
