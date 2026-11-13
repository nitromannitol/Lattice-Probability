/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Field.SupBounds at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Field.OscBlock
import LatticeProb.Bonanno.LQGDimension.Gaussian.Concentration

/-!
# Suprema of band fields on boxes (packet P-OSC, targets T3 and T4)

Source: `source/higher-dimensional-lfpp-limit.pdf`, App. A.1 (last paragraph: the band
`H_{ε,1} - H_{2^{-N},1}` has supremum `O_P(√N)` on `U`); planning audit HA5, Details D4
(Lemma S, Lemma 3.4′, the band bound used in D11) and packet row X3.

**Expected supremum (target T3).**  Let `H` be a continuous version of `H_{a,b}`
(`0 < a ≤ b`), `V ≥ log(b/a)`, and `B = x₀ + [-R, R]^d`.  Cover `B` by the grid of mesh `a`
(`N ≤ (2R/a + 1)^d` points `g`, each point of `B` within `√d a` of its grid point).  For a
finite family `F ⊆ B`, in the Gram representation `H(z) = ⟪u_z, x⟫` (`x` standard Gaussian),

`max_{z ∈ F} ⟪u_z, x⟫ ≤ max_g ⟪u_g, x⟫ + max_g (M_g(x) - E M_g) + max_g E M_g`,

where `M_g = max_{z ∈ F, z ↦ g} ⟪u_z - u_g, x⟫`.  The first term has mean
`≤ √(2V(1 + log N))` (Gaussian maximal inequality), the third is `≤ Osc.blockConst` (chaining
on a block, `LQGDimension.ChainBox.chainingBox_bound`), and the second has mean
`≤ π σ √((1 + log N)/2)` with `σ² = d L` by the exponential concentration of finite maxima
(`LQGDimension.MaxConc.integral_exp_max_le`) and a soft maximum
(`SupB.integral_iSup_le_of_exp_le`).  This bound (`SupB.supMean`) holds for every finite
family, so `LQGMetric.SupTail.integrable_iSup_of_continuous` gives it for `E sup_B H` and
`E sup_B (-H)`, and Borell–TIS (`LQGMetric.SupTail.tail_iSup_abs_le`, variance `≤ V`) gives

`P(sup_B |H| ≥ supMean + u) ≤ 2 exp(-u² / (2V))`   (`SupB.bandSup_bounds`, `SupB.bandSup_tail`),

and `E sup_B |H| ≤ 2 supMean + √V` (`SupB.integral_iSup_abs_le`).  With constants depending only
on `κ` and `d`: `exists_bandSup_bounds`.  Here
`supMean d L V ℓ = √(2V(1+ℓ)) + blockConst d L √d + π √(dL) √((1+ℓ)/2)`, `ℓ = d log(2R/a + 1)`,
so `E sup_B H = O(√(V · d log(2R/a + 1)) + √(d log(2R/a + 1)) + 1)`: with `V = m log 2` and
`R/a ≍ 2^n` this gives HA5's Lemma S and Lemma 3.4′ (via the Borell–TIS tail).

**Band difference (target T4, App. A.1, HA5 D11).**  For `2^{-N-1} ≤ ε ≤ 2^{-N}` the difference
`H_{ε,1} - H_{2^{-N},1}` of continuous versions is a continuous version of the band
`H_{ε,2^{-N}}` (band additivity `IsWhiteNoise.bandVec_add_ae`), with variance `≤ log 2`; with
`R = 2`, `log N_grid ≤ 4 d (N + 1) log 2`, so

`P(∃ z ∈ closure U, C √(N+1) + u < |H_{ε,1}(z) - H_{2^{-N},1}(z)|) ≤ 2 exp(-u² / (2 log 2))`

with `C` depending only on `κ` and `d` (`exists_cutoff_diff_sup_tail`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Real
open scoped RealInnerProductSpace

namespace HigherDimLFPP

namespace SupB

/-! ### Finite maxima -/

/-- A finite supremum of integrable functions is integrable. -/
theorem integrable_iSup_of_finite {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Finite ι]
    [Nonempty ι] {f : ι → α → ℝ} (hf : ∀ i, Integrable (f i) μ) :
    Integrable (fun x => ⨆ i, f i x) μ := by
  have := Fintype.ofFinite ι
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun i _ => (hf i).abs)
    (AEMeasurable.iSup fun i => (hf i).aemeasurable).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i => f i x)
  rw [← hj, Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun i => |f i x|) (fun i _ => abs_nonneg _)
    (Finset.mem_univ j)

/-- **Soft maximum**: if `E e^{l Y_g} ≤ e^{l² c}` for the `N` functions `Y_g`, then
`E max_g Y_g ≤ (log N + l² c)/l`. -/
theorem integral_iSup_le_of_exp_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] (G : Finset ι) (hG : G.Nonempty) (Y : ι → α → ℝ)
    (hYi : ∀ g ∈ G, Integrable (Y g) μ) {l c : ℝ} (hl : 0 < l)
    (hEi : ∀ g ∈ G, Integrable (fun x => Real.exp (l * Y g x)) μ)
    (hexp : ∀ g ∈ G, ∫ x, Real.exp (l * Y g x) ∂μ ≤ Real.exp (l ^ 2 * c)) :
    ∫ x, (⨆ g : G, Y g x) ∂μ ≤ (Real.log G.card + l ^ 2 * c) / l := by
  set N : ℝ := (G.card : ℝ) with hNdef
  set A : ℝ := Real.log N + l ^ 2 * c with hA
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast hG.card_pos
  have : Nonempty G := hG.to_subtype
  have hpt : ∀ x, l * (⨆ g : G, Y g x) ≤
      (A - 1) + Real.exp (-A) * ∑ g ∈ G, Real.exp (l * Y g x) := by
    intro x
    obtain ⟨g₀, hg₀⟩ := exists_eq_ciSup_of_finite (f := fun g : G => Y g x)
    rw [← hg₀]
    have h1 : Real.exp (l * Y g₀ x) ≤ ∑ g ∈ G, Real.exp (l * Y g x) :=
      Finset.single_le_sum (f := fun g => Real.exp (l * Y g x)) (fun g _ => (Real.exp_pos _).le)
        g₀.2
    have h2 := Real.add_one_le_exp (l * Y g₀ x - A)
    have h3 : Real.exp (l * Y g₀ x - A) = Real.exp (-A) * Real.exp (l * Y g₀ x) := by
      rw [← Real.exp_add]
      ring_nf
    rw [h3] at h2
    nlinarith [Real.exp_pos (-A)]
  have hsupi : Integrable (fun x => ⨆ g : G, Y g x) μ :=
    integrable_iSup_of_finite fun g => hYi g g.2
  have hsumi : Integrable (fun x => ∑ g ∈ G, Real.exp (l * Y g x)) μ :=
    integrable_finsetSum G fun g hg => hEi g hg
  have hRint : Integrable (fun x => (A - 1) + Real.exp (-A) * ∑ g ∈ G, Real.exp (l * Y g x)) μ :=
    (integrable_const _).add (hsumi.const_mul _)
  have hmono := integral_mono (hsupi.const_mul l) hRint hpt
  rw [integral_const_mul, integral_add (integrable_const _) (hsumi.const_mul _), integral_const,
    integral_const_mul, integral_finsetSum G fun g hg => hEi g hg] at hmono
  simp only [probReal_univ, one_smul] at hmono
  have hsum : ∑ g ∈ G, ∫ x, Real.exp (l * Y g x) ∂μ ≤ N * Real.exp (l ^ 2 * c) := by
    calc ∑ g ∈ G, ∫ x, Real.exp (l * Y g x) ∂μ ≤ ∑ _g ∈ G, Real.exp (l ^ 2 * c) :=
          Finset.sum_le_sum hexp
      _ = N * Real.exp (l ^ 2 * c) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hexpA : Real.exp (-A) * (N * Real.exp (l ^ 2 * c)) = 1 := by
    rw [hA, Real.exp_neg, Real.exp_add, Real.exp_log hN]
    field_simp
  rw [le_div_iff₀ hl]
  have hea := Real.exp_pos (-A)
  nlinarith [mul_le_mul_of_nonneg_left hsum hea.le]

/-! ### The expected maximum over a finite family, in the Gram representation -/

variable {d : ℕ}

/-- **Grid decomposition of a finite Gaussian maximum.**  Let `F` be a finite family of points,
`G ⊆ F` a nonempty grid, `gr` an assignment of grid points with `‖z - gr z‖ ≤ r a` on `F`, and
`u` vectors with `‖u_g‖² ≤ V` on `G` and `‖u_z - u_w‖² ≤ L ‖z - w‖²/a²` on `F`.  Then for all
`l₁, l₂ > 0`,
`E max_{z ∈ F} ⟪u_z, x⟫ ≤ (log N + l₁² V/2)/l₁ + blockConst d L r + (log N + l₂² π² r² L/8)/l₂`
with `N = |G|`. -/
theorem vecExpectedMax_le_grid {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {F G : Finset (Rd d)} (hGF : G ⊆ F) (hG : G.Nonempty) (gr : Rd d → Rd d)
    {a r L V : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hL : 0 ≤ L)
    (hgr : ∀ z ∈ F, gr z ∈ G ∧ ‖z - gr z‖ ≤ r * a) (u : Rd d → E)
    (hu : ∀ g ∈ G, ‖u g‖ ^ 2 ≤ V)
    (hinc : ∀ z ∈ F, ∀ w ∈ F, ‖u z - u w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2)
    {l₁ l₂ : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) :
    LQGDimension.vecExpectedMax F u 0 ≤
      (Real.log G.card + l₁ ^ 2 * (V / 2)) / l₁ + Osc.blockConst d L r +
        (Real.log G.card + l₂ ^ 2 * (π ^ 2 * (r ^ 2 * L) / 8)) / l₂ := by
  classical
  obtain ⟨g₀, hg₀⟩ := hG
  have hV0 : 0 ≤ V := (sq_nonneg _).trans (hu g₀ hg₀)
  set σ : ℝ := r * √L with hσ
  have hσ2 : σ ^ 2 = r ^ 2 * L := by rw [hσ, mul_pow, Real.sq_sqrt hL]
  -- the blocks
  set Fg : Rd d → Finset (Rd d) := fun g => insert g (F.filter fun z => gr z = g) with hFg
  have hFg_sub : ∀ g ∈ G, Fg g ⊆ F := fun g hg z hz => by
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hGF hg
    · exact (Finset.mem_filter.1 hz).1
  have hFg_mem : ∀ g, g ∈ Fg g := fun g => Finset.mem_insert_self _ _
  have hFg_norm : ∀ g, ∀ z ∈ Fg g, ‖z - g‖ ≤ r * a := fun g z hz => by
    rcases Finset.mem_insert.1 hz with rfl | hz
    · rw [sub_self, norm_zero]
      positivity
    · obtain ⟨hzF, hzg⟩ := Finset.mem_filter.1 hz
      have := (hgr z hzF).2
      rwa [hzg] at this
  have hdiam : ∀ g, ∀ z ∈ Fg g, ∀ w ∈ Fg g, ‖z - w‖ ≤ 2 * r * a := fun g z hz w hw => by
    calc ‖z - w‖ = ‖(z - g) - (w - g)‖ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖z - g‖ + ‖w - g‖ := norm_sub_le _ _
      _ ≤ 2 * r * a := by linarith [hFg_norm g z hz, hFg_norm g w hw]
  -- chaining on each block
  set m : Rd d → ℝ := fun g => LQGDimension.vecExpectedMax (Fg g) (fun i => u i - u g) 0
    with hm
  have hmle : ∀ g ∈ G, m g ≤ Osc.blockConst d L r := by
    intro g hg
    have h := LQGDimension.ChainBox.chainingBox_bound (Fg g) (fun z => WithLp.ofLp z) u
      (L := √(2 * r * L * √(d : ℝ) / a)) (a := 2 * r * a) (Real.sqrt_nonneg _)
      (fun i hi j hj => (Osc.norm_ofLp_sub_le i j).trans (hdiam g i hi j hj))
      (fun i hi j hj => (hinc i (hFg_sub g hg hi) j (hFg_sub g hg hj)).trans
        (Osc.incr_le_chain hL hr ha (hdiam g i hi j hj))) (hFg_mem g)
    rwa [Osc.chain_identity hL hr ha] at h
  -- concentration on each block
  have hvσ : ∀ g ∈ G, ∀ i ∈ Fg g, ‖u i - u g‖ ≤ σ := by
    intro g hg i hi
    have h1 := hinc i (hFg_sub g hg hi) g (hGF hg)
    have h2 : L * ‖i - g‖ ^ 2 / a ^ 2 ≤ σ ^ 2 := by
      rw [hσ2]
      have h3 : ‖i - g‖ ^ 2 ≤ (r * a) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hFg_norm g i hi) 2
      calc L * ‖i - g‖ ^ 2 / a ^ 2 ≤ L * (r * a) ^ 2 / a ^ 2 := by gcongr
        _ = r ^ 2 * L := by field_simp
    have hσ0 : 0 ≤ σ := by positivity
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hσ0 two_ne_zero).1 (h1.trans h2)
  set Y : Rd d → E → ℝ := fun g x =>
    (⨆ i : Fg g, ⟪u i - u g, x⟫ + (0 : Rd d → ℝ) i) - m g with hY
  have hYi : ∀ g ∈ G, Integrable (Y g) (stdGaussian E) := fun g _ =>
    (LQGDimension.integrable_iSup_inner_add (Fg g) (fun i => u i - u g) 0).sub
      (integrable_const _)
  have hEi : ∀ g ∈ G, Integrable (fun x => Real.exp (l₂ * Y g x)) (stdGaussian E) := fun g hg =>
    LQGDimension.MaxConc.integrable_exp_max (Fg g) (fun i => u i - u g) 0 (hvσ g hg) l₂
  have hexp : ∀ g ∈ G, ∫ x, Real.exp (l₂ * Y g x) ∂stdGaussian E ≤
      Real.exp (l₂ ^ 2 * (π ^ 2 * (r ^ 2 * L) / 8)) := by
    intro g hg
    refine (LQGDimension.MaxConc.integral_exp_max_le (Fg g) (fun i => u i - u g) 0 (hvσ g hg)
      l₂).trans (le_of_eq ?_)
    rw [hσ2]
    ring_nf
  have hYmax := integral_iSup_le_of_exp_le G ⟨g₀, hg₀⟩ Y hYi hl₂ hEi hexp
  -- the grid maximum
  have hGmax := LQGDimension.GaussianMax.integral_iSup_inner_le G ⟨g₀, hg₀⟩ u (σ := √V) hl₁
    (fun g hg => by
      rw [← Real.sqrt_sq (norm_nonneg (u g))]
      exact Real.sqrt_le_sqrt (hu g hg))
    (LQGDimension.ChainBox.integrable_iSup_inner G u)
  rw [Real.sq_sqrt hV0] at hGmax
  -- pointwise decomposition
  have : Nonempty G := ⟨⟨g₀, hg₀⟩⟩
  have : Nonempty F := ⟨⟨g₀, hGF hg₀⟩⟩
  have hpt : ∀ x, (⨆ z : F, ⟪u z, x⟫ + (0 : Rd d → ℝ) z) ≤
      (⨆ g : G, ⟪u g, x⟫) + ((⨆ g : G, Y g x) + Osc.blockConst d L r) := by
    intro x
    refine ciSup_le fun z => ?_
    obtain ⟨hgz, -⟩ := hgr z z.2
    set g := gr z with hgdef
    have hzFg : (z : Rd d) ∈ Fg g :=
      Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨z.2, hgdef.symm⟩)
    have h1 : ⟪u z, x⟫ + (0 : Rd d → ℝ) z = ⟪u g, x⟫ + (⟪u z - u g, x⟫ + (0 : Rd d → ℝ) z) := by
      rw [inner_sub_left]
      ring
    have h2 : ⟪u z - u g, x⟫ + (0 : Rd d → ℝ) z ≤
        ⨆ i : Fg g, ⟪u i - u g, x⟫ + (0 : Rd d → ℝ) i :=
      le_ciSup (f := fun i : Fg g => ⟪u i - u g, x⟫ + (0 : Rd d → ℝ) i)
        (Finite.bddAbove_range _) ⟨z, hzFg⟩
    have h3 : Y g x ≤ ⨆ g' : G, Y g' x :=
      le_ciSup (f := fun g' : G => Y g' x) (Finite.bddAbove_range _) ⟨g, hgz⟩
    have h4 : ⟪u g, x⟫ ≤ ⨆ g' : G, ⟪u g', x⟫ :=
      le_ciSup (f := fun g' : G => ⟪u g', x⟫) (Finite.bddAbove_range _) ⟨g, hgz⟩
    have h5 := hmle g hgz
    have h6 : (⨆ i : Fg g, ⟪u i - u g, x⟫ + (0 : Rd d → ℝ) i) = Y g x + m g := by
      rw [hY]
      ring
    rw [h1]
    linarith
  have hint1 := LQGDimension.ChainBox.integrable_iSup_inner G u
  have hint2 : Integrable (fun x => ⨆ g : G, Y g x) (stdGaussian E) :=
    integrable_iSup_of_finite fun g => hYi g g.2
  have hint3 : Integrable (fun x => (⨆ g : G, Y g x) + Osc.blockConst d L r) (stdGaussian E) :=
    hint2.add (integrable_const _)
  calc LQGDimension.vecExpectedMax F u 0
      = ∫ x, (⨆ z : F, ⟪u z, x⟫ + (0 : Rd d → ℝ) z) ∂stdGaussian E := rfl
    _ ≤ ∫ x, ((⨆ g : G, ⟪u g, x⟫) + ((⨆ g : G, Y g x) + Osc.blockConst d L r)) ∂stdGaussian E :=
        integral_mono (LQGDimension.integrable_iSup_inner_add F u 0) (hint1.add hint3) hpt
    _ = (∫ x, (⨆ g : G, ⟪u g, x⟫) ∂stdGaussian E) + ((∫ x, (⨆ g : G, Y g x) ∂stdGaussian E) +
          Osc.blockConst d L r) := by
        rw [integral_add hint1 hint3, integral_add hint2 (integrable_const _), integral_const,
          probReal_univ, one_smul]
    _ ≤ (Real.log G.card + l₁ ^ 2 * (V / 2)) / l₁ + Osc.blockConst d L r +
          (Real.log G.card + l₂ ^ 2 * (π ^ 2 * (r ^ 2 * L) / 8)) / l₂ := by
        have e : (Real.log G.card + l₁ ^ 2 * V / 2) / l₁ =
            (Real.log G.card + l₁ ^ 2 * (V / 2)) / l₁ := by ring
        rw [e] at hGmax
        linarith

/-- Choice of the soft-maximum parameter: `(N' + (λ/√c)² c)/(λ/√c) ≤ 2 λ √c` when `N' ≤ λ²`. -/
theorem softmax_opt {c lam N' : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hN : N' ≤ lam ^ 2) :
    (N' + (lam / √c) ^ 2 * c) / (lam / √c) ≤ 2 * lam * √c := by
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  have e1 : (lam / √c) ^ 2 * c = lam ^ 2 := by
    rw [div_pow, Real.sq_sqrt hc.le]
    field_simp
  rw [e1, div_le_iff₀ (by positivity)]
  have e2 : 2 * lam * √c * (lam / √c) = 2 * lam ^ 2 := by
    field_simp
  rw [e2]
  linarith

/-- The bound on `E sup_B H` for a box `B` and grid of mesh `a` with `log N_grid ≤ ℓ`:
`supMean d L V ℓ = 2 √(1+ℓ) √(V/2) + blockConst d L √d + 2 √(1+ℓ) √(π² d L / 8)`, i.e.
`√(2V(1+ℓ)) + blockConst d L √d + π √(dL) √((1+ℓ)/2)`. -/
def supMean (d : ℕ) (L V ℓ : ℝ) : ℝ :=
  2 * √(1 + ℓ) * √(V / 2) + Osc.blockConst d L √(d : ℝ) +
    2 * √(1 + ℓ) * √(π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8)

/-- `supMean` is monotone in `V` and `ℓ`. -/
theorem supMean_mono (d : ℕ) {L V V' ℓ ℓ' : ℝ} (hV : V ≤ V') (hℓ : ℓ ≤ ℓ') :
    supMean d L V ℓ ≤ supMean d L V' ℓ' := by
  unfold supMean
  have h1 : √(1 + ℓ) ≤ √(1 + ℓ') := Real.sqrt_le_sqrt (by linarith)
  have h2 : √(V / 2) ≤ √(V' / 2) := Real.sqrt_le_sqrt (by linarith)
  have h3 : 0 ≤ √(π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8) := Real.sqrt_nonneg _
  have h4 : 0 ≤ √(1 + ℓ) := Real.sqrt_nonneg _
  have h5 : 0 ≤ √(V / 2) := Real.sqrt_nonneg _
  gcongr

/-- `log N_grid ≤ d log(2R/a + 1)`. -/
theorem log_card_grid_le (x₀ : Rd d) {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a) :
    Real.log (Osc.grid x₀ R a).card ≤ d * Real.log (2 * R / a + 1) := by
  have h1 : (0 : ℝ) < (Osc.grid x₀ R a).card := by
    exact_mod_cast Osc.one_le_card_grid x₀ R a
  calc Real.log (Osc.grid x₀ R a).card ≤ Real.log ((2 * R / a + 1) ^ d) :=
        Real.log_le_log h1 (Osc.card_grid_le x₀ hR ha)
    _ = d * Real.log (2 * R / a + 1) := Real.log_pow _ _

section Field

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {κ : Rd d → ℝ}

/-- **Expected maxima over finite families of a band field**, for both signs `s = ±1`: if the
finite family `F` lies in the box `x₀ + [-R,R]^d` and contains its grid of mesh `a`, then
`E max_{z ∈ F} s H(z) ≤ supMean d L V ℓ`. -/
theorem integral_iSup_finset_le [NeZero d] (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H)
    {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ z w : Rd d, ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2)
    {V : ℝ} (hV : 0 < V) (hbV : Real.log (b / a) ≤ V) (x₀ : Rd d) {R : ℝ} (hR : 0 ≤ R)
    {ℓ : ℝ} (hℓ : d * Real.log (2 * R / a + 1) ≤ ℓ) {s : ℝ} (hs : s * s = 1)
    (F : Finset (Rd d)) (hF : ∀ z ∈ F, z ∈ Osc.box x₀ R) (hGF : Osc.grid x₀ R a ⊆ F) :
    ∫ ω, (⨆ z : F, s * H z ω) ∂P ≤ supMean d L V ℓ := by
  classical
  set k : Rd d → WN d := fun z => bandVec κ a b z with hk
  -- transfer to the Gaussian expected maximum
  have hval : ∫ ω, (⨆ z : F, s * H z ω) ∂P =
      LQGDimension.gaussianExpectedMax F (fun z w => ⟪k z, k w⟫) 0 := by
    have h := hW.integral_iSup_eq_gaussianExpectedMax F (fun z => s • k z) 0
    have hae : ∀ᵐ ω ∂P, ∀ z : F, s * H z ω = W (s • k z) ω + (0 : Rd d → ℝ) z := by
      refine ae_all_iff.2 fun z => ?_
      filter_upwards [hW.smul_ae s (k z), hH.ae_eq (z : Rd d)] with ω h1 h2
      rw [h1, h2, Pi.zero_apply, add_zero]
    have hC : (fun z w : Rd d => ⟪s • k z, s • k w⟫) = fun z w => ⟪k z, k w⟫ := by
      funext z w
      rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, hs, one_mul]
    rw [hC] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    simp only [hω]
  obtain ⟨u, hu, hEq⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F
    (fun z w => ⟪k z, k w⟫) (LQGDimension.posSemidef_gramOn F k)
  rw [hval, hEq]
  set G := Osc.grid x₀ R a with hGdef
  have hG : G.Nonempty := Finset.card_pos.1 (Osc.one_le_card_grid x₀ R a)
  have hgr : ∀ z ∈ F, Osc.gridOf x₀ R a z ∈ G ∧ ‖z - Osc.gridOf x₀ R a z‖ ≤ √(d : ℝ) * a :=
    fun z hz => ⟨Osc.gridOf_mem_grid x₀ ha (hF z hz), Osc.norm_sub_gridOf_le x₀ ha (hF z hz)⟩
  have hu' : ∀ g ∈ G, ‖u g‖ ^ 2 ≤ V := by
    intro g hg
    rw [← real_inner_self_eq_norm_sq, hu g (hGF hg) g (hGF hg), real_inner_self_eq_norm_sq,
      norm_bandVec_sq hκ ha hab]
    exact hbV
  have hinc : ∀ z ∈ F, ∀ w ∈ F, ‖u z - u w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2 := by
    intro z hz w hw
    have e : ‖u z - u w‖ ^ 2 = ‖k z - k w‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq (k z),
        ← real_inner_self_eq_norm_sq (k w), hu z hz z hz, hu z hz w hw, hu w hw w hw]
    rw [e]
    exact hL z w
  have hlogN : Real.log G.card ≤ ℓ := (log_card_grid_le x₀ hR ha).trans hℓ
  have hlog0 : 0 ≤ Real.log G.card := Real.log_nonneg (by exact_mod_cast hG.card_pos)
  set lam := √(1 + ℓ) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.2 (by linarith)
  have hlam2 : lam ^ 2 = 1 + ℓ := Real.sq_sqrt (by linarith)
  have hN : Real.log G.card ≤ lam ^ 2 := by rw [hlam2]; linarith
  set c₁ : ℝ := V / 2 with hc₁
  set c₂ : ℝ := π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8 with hc₂
  have hc₁0 : 0 < c₁ := by positivity
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hc₂0 : 0 < c₂ := by positivity
  have hmain := vecExpectedMax_le_grid hGF hG (Osc.gridOf x₀ R a) ha (Real.sqrt_nonneg _)
    hL0.le hgr u hu' hinc (l₁ := lam / √c₁) (l₂ := lam / √c₂) (by positivity) (by positivity)
  have h1 := softmax_opt hc₁0 hlam0 hN
  have h2 := softmax_opt hc₂0 hlam0 hN
  refine hmain.trans ?_
  unfold supMean
  rw [← hlam, ← hc₁, ← hc₂]
  linarith

/-- `sup |f| = max (sup f) (sup (-f))` for a continuous function on a nonempty compact space. -/
theorem iSup_abs_eq_max {T : Type*} [TopologicalSpace T] [CompactSpace T] [Nonempty T]
    {f : T → ℝ} (hf : Continuous f) :
    ⨆ t, |f t| = max (⨆ t, f t) (⨆ t, -f t) := by
  have hb : BddAbove (range f) := (isCompact_range hf).bddAbove
  have hb' : BddAbove (range fun t => -f t) := (isCompact_range hf.neg).bddAbove
  have hb'' : BddAbove (range fun t => |f t|) := (isCompact_range hf.abs).bddAbove
  refine le_antisymm (ciSup_le fun t => ?_) (max_le (ciSup_le fun t => ?_) (ciSup_le fun t => ?_))
  · rw [abs_eq_max_neg]
    exact max_le_max (le_ciSup hb t) (le_ciSup hb' t)
  · exact (le_abs_self (f t)).trans (le_ciSup hb'' t)
  · exact (neg_le_abs (f t)).trans (le_ciSup hb'' t)

/-- **Expected suprema and Gaussian tail of a band field on a box** (target T3, explicit
constants).  Let `H` be a continuous version of `H_{a,b}` (`0 < a ≤ b`), with the increment bound
`‖k_z - k_w‖² ≤ L ‖z - w‖²/a²` (`L > 0`), `V ≥ log(b/a)`, `V > 0`, `B = x₀ + [-R, R]^d`
(`R ≥ 0`) and `ℓ ≥ d log(2R/a + 1)`.  With `M = supMean d L V ℓ`:
`E sup_B H ≤ M`, `E sup_B (-H) ≤ M`, `sup_B |H| ∈ L¹`, and for `u ≥ 0`
`P(sup_B |H| ≥ M + u) ≤ 2 exp(-u²/(2V))` (Borell–TIS). -/
theorem bandSup_bounds [NeZero d] (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H)
    {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ z w : Rd d, ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2)
    {V : ℝ} (hV : 0 < V) (hbV : Real.log (b / a) ≤ V) (x₀ : Rd d) {R : ℝ} (hR : 0 ≤ R)
    {ℓ : ℝ} (hℓ : d * Real.log (2 * R / a + 1) ≤ ℓ) :
    (Integrable (fun ω => ⨆ z : Osc.box x₀ R, H z ω) P ∧
        ∫ ω, (⨆ z : Osc.box x₀ R, H z ω) ∂P ≤ supMean d L V ℓ) ∧
      (Integrable (fun ω => ⨆ z : Osc.box x₀ R, -H z ω) P ∧
        ∫ ω, (⨆ z : Osc.box x₀ R, -H z ω) ∂P ≤ supMean d L V ℓ) ∧
      Integrable (fun ω => ⨆ z : Osc.box x₀ R, |H z ω|) P ∧
      ∀ {u : ℝ}, 0 ≤ u → P {ω | supMean d L V ℓ + u ≤ ⨆ z : Osc.box x₀ R, |H z ω|} ≤
        ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * V))) := by
  classical
  have := hW.isProbabilityMeasure
  set B : Set (Rd d) := Osc.box x₀ R with hB
  have : CompactSpace B := isCompact_iff_compactSpace.1 (Osc.isCompact_box x₀ R)
  have hx₀ : x₀ ∈ B := fun i => by simpa only [sub_self, abs_zero] using hR
  have : Nonempty B := ⟨⟨x₀, hx₀⟩⟩
  set M := supMean d L V ℓ with hM
  -- the finite-family bound, for both signs
  have hfin : ∀ s : ℝ, s * s = 1 → ∀ (n : ℕ) (t : Fin (n + 1) → B),
      ∫ ω, (⨆ i, s * H (t i) ω) ∂P ≤ M := by
    intro s hs n t
    set F : Finset (Rd d) := (Finset.univ.image fun i => (t i : Rd d)) ∪ Osc.grid x₀ R a with hF
    have hFB : ∀ z ∈ F, z ∈ B := by
      intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact (t i).2
      · exact Osc.grid_subset_box x₀ hR ha hz
    have hGF : Osc.grid x₀ R a ⊆ F := Finset.subset_union_right
    have : Nonempty F := ⟨⟨t 0, Finset.mem_union_left _ (Finset.mem_image_of_mem _
      (Finset.mem_univ 0))⟩⟩
    have hint1 : Integrable (fun ω => ⨆ i, s * H (t i) ω) P :=
      integrable_iSup_of_finite fun i => (Osc.integrable_of_isBandVersion hH hW _).const_mul s
    have hint2 : Integrable (fun ω => ⨆ z : F, s * H z ω) P :=
      integrable_iSup_of_finite fun z => (Osc.integrable_of_isBandVersion hH hW _).const_mul s
    have hpt : ∀ ω, (⨆ i, s * H (t i) ω) ≤ ⨆ z : F, s * H z ω := fun ω =>
      ciSup_le fun i => le_ciSup (f := fun z : F => s * H z ω) (Finite.bddAbove_range _)
        ⟨t i, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
    exact (integral_mono hint1 hint2 hpt).trans
      (integral_iSup_finset_le hκ hW ha hab hH hL0 hL hV hbV x₀ hR hℓ hs F hFB hGF)
  set X : B → Ω → ℝ := fun z ω => H z ω with hX
  have hXg : IsGaussianProcess X P := (hH.isGaussianProcess hW).comp_right Subtype.val
  have hX0 : ∀ z, ∫ ω, X z ω ∂P = 0 := fun z => hH.integral_eq_zero hW z
  have hXc : ∀ ω, Continuous fun z => X z ω := fun ω =>
    (hH.continuous ω).comp continuous_subtype_val
  obtain ⟨hint, hMle⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous hXg hXc (C := M)
    fun n t => by simpa only [one_mul] using hfin 1 (one_mul 1) n t
  obtain ⟨hint', hMle'⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous
    (LQGMetric.SupTail.isGaussianProcess_neg hXg) (fun ω => (hXc ω).neg) (C := M)
    fun n t => by simpa only [neg_one_mul] using hfin (-1) (by norm_num) n t
  have habs : (fun ω => ⨆ z : B, |H z ω|) = fun ω => max (⨆ z : B, H z ω) (⨆ z : B, -H z ω) :=
    funext fun ω => iSup_abs_eq_max (f := fun z : B => H z ω) (hXc ω)
  refine ⟨⟨hint, hMle⟩, ⟨hint', hMle'⟩, ?_, fun {u} hu => ?_⟩
  · rw [habs]
    exact hint.sup hint'
  · have hvar : ∀ z : B, Var[X z; P] ≤ √V ^ 2 := fun z => by
      rw [Real.sq_sqrt hV.le, show X z = H z from rfl, (hH.hasLaw_log hW hκ ha hab z).variance_eq,
        variance_id_gaussianReal, Real.coe_toNNReal _ (Real.log_nonneg ?_)]
      · exact hbV
      · rw [le_div_iff₀ ha, one_mul]
        exact hab
    have htail := LQGMetric.SupTail.tail_iSup_abs_le hXg hX0 hXc hint hint' hMle hMle' hvar hu
    rw [Real.sq_sqrt hV.le] at htail
    calc P {ω | M + u ≤ ⨆ z : B, |H z ω|}
        = ENNReal.ofReal (P.real {ω | M + u ≤ ⨆ z : B, |H z ω|}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * V))) := ENNReal.ofReal_le_ofReal htail

/-- `E |H z| ≤ √V` for a continuous version `H` of `H_{a,b}` with `log(b/a) ≤ V`. -/
theorem integral_abs_le_sqrt (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H) {V : ℝ}
    (hbV : Real.log (b / a) ≤ V) (z : Rd d) : ∫ ω, |H z ω| ∂P ≤ √V := by
  have := hW.isProbabilityMeasure
  have hm : MemLp (fun ω => |H z ω|) 2 P := (Osc.memLp_two_of_isBandVersion hH hW z).norm
  have hvar := variance_nonneg (fun ω => |H z ω|) P
  rw [variance_eq_sub hm] at hvar
  have hsq : ∫ ω, (fun ω => |H z ω|) ω ^ 2 ∂P = Real.log (b / a) := by
    simp only [sq_abs]
    rw [← variance_of_integral_eq_zero (hH.hasLaw_log hW hκ ha hab z).aemeasurable
      (hH.integral_eq_zero hW z), (hH.hasLaw_log hW hκ ha hab z).variance_eq,
      variance_id_gaussianReal, Real.coe_toNNReal _ (Real.log_nonneg ?_)]
    rw [le_div_iff₀ ha, one_mul]
    exact hab
  have h1 : (∫ ω, |H z ω| ∂P) ^ 2 ≤ V := by
    have : (∫ ω, |H z ω| ∂P) ^ 2 ≤ ∫ ω, (fun ω => |H z ω|) ω ^ 2 ∂P := by
      simpa only [Pi.pow_apply, sub_nonneg] using hvar
    linarith
  exact (le_abs_self _).trans (Real.abs_le_sqrt h1)

/-- `E sup_B |H| ≤ 2 supMean + √V` (from `E sup_B (±H) ≤ supMean` and
`sup |H| ≤ sup H + sup (-H) + |H x₀|`). -/
theorem integral_iSup_abs_le [NeZero d] (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H)
    {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ z w : Rd d, ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2)
    {V : ℝ} (hV : 0 < V) (hbV : Real.log (b / a) ≤ V) (x₀ : Rd d) {R : ℝ} (hR : 0 ≤ R)
    {ℓ : ℝ} (hℓ : d * Real.log (2 * R / a + 1) ≤ ℓ) :
    ∫ ω, (⨆ z : Osc.box x₀ R, |H z ω|) ∂P ≤ 2 * supMean d L V ℓ + √V := by
  have : CompactSpace (Osc.box x₀ R) := isCompact_iff_compactSpace.1 (Osc.isCompact_box x₀ R)
  have hx₀ : x₀ ∈ Osc.box x₀ R := fun i => by simpa only [sub_self, abs_zero] using hR
  have : Nonempty (Osc.box x₀ R) := ⟨⟨x₀, hx₀⟩⟩
  obtain ⟨⟨hint, hM⟩, ⟨hint', hM'⟩, hint'', -⟩ :=
    bandSup_bounds hκ hW ha hab hH hL0 hL hV hbV x₀ hR hℓ
  have hc : ∀ ω, Continuous fun z : Osc.box x₀ R => H z ω := fun ω =>
    (hH.continuous ω).comp continuous_subtype_val
  have habs := (Osc.integrable_of_isBandVersion hH hW x₀).abs
  have hpt : ∀ ω, (⨆ z : Osc.box x₀ R, |H z ω|) ≤
      ((⨆ z : Osc.box x₀ R, H z ω) + ⨆ z : Osc.box x₀ R, -H z ω) + |H x₀ ω| := by
    intro ω
    rw [iSup_abs_eq_max (hc ω)]
    have h1 : H x₀ ω ≤ ⨆ z : Osc.box x₀ R, H z ω :=
      le_ciSup (f := fun z : Osc.box x₀ R => H z ω) (isCompact_range (hc ω)).bddAbove ⟨x₀, hx₀⟩
    have h2 : -H x₀ ω ≤ ⨆ z : Osc.box x₀ R, -H z ω :=
      le_ciSup (f := fun z : Osc.box x₀ R => -H z ω) (isCompact_range (hc ω).neg).bddAbove
        ⟨x₀, hx₀⟩
    have h3 := le_abs_self (H x₀ ω)
    have h4 := neg_abs_le (H x₀ ω)
    exact max_le (by linarith) (by linarith)
  have hsum : Integrable
      (fun ω => (⨆ z : Osc.box x₀ R, H z ω) + ⨆ z : Osc.box x₀ R, -H z ω) P := hint.add hint'
  have habs' : Integrable (fun ω => |H x₀ ω|) P := habs
  calc ∫ ω, (⨆ z : Osc.box x₀ R, |H z ω|) ∂P
      ≤ ∫ ω, (((⨆ z : Osc.box x₀ R, H z ω) + ⨆ z : Osc.box x₀ R, -H z ω) + |H x₀ ω|) ∂P :=
        integral_mono hint'' (hsum.add habs') hpt
    _ = (∫ ω, (⨆ z : Osc.box x₀ R, H z ω) ∂P) + (∫ ω, (⨆ z : Osc.box x₀ R, -H z ω) ∂P) +
          ∫ ω, |H x₀ ω| ∂P := by
        rw [integral_add hsum habs', integral_add hint hint']
    _ ≤ 2 * supMean d L V ℓ + √V := by
        have := integral_abs_le_sqrt hκ hW ha hab hH hbV x₀
        linarith

/-- Event form of the tail of `bandSup_bounds`: `P*(∃ z ∈ B, M + u < |H z|) ≤ 2 exp(-u²/(2V))`. -/
theorem bandSup_tail [NeZero d] (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H)
    {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ z w : Rd d, ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2)
    {V : ℝ} (hV : 0 < V) (hbV : Real.log (b / a) ≤ V) (x₀ : Rd d) {R : ℝ} (hR : 0 ≤ R)
    {ℓ : ℝ} (hℓ : d * Real.log (2 * R / a + 1) ≤ ℓ) {u : ℝ} (hu : 0 ≤ u) :
    P {ω | ∃ z ∈ Osc.box x₀ R, supMean d L V ℓ + u < |H z ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * V))) := by
  have : CompactSpace (Osc.box x₀ R) := isCompact_iff_compactSpace.1 (Osc.isCompact_box x₀ R)
  obtain ⟨-, -, -, htail⟩ := bandSup_bounds hκ hW ha hab hH hL0 hL hV hbV x₀ hR hℓ
  refine (measure_mono fun ω hω => ?_).trans (htail hu)
  obtain ⟨z, hz, hlt⟩ := hω
  have hb : BddAbove (range fun z : Osc.box x₀ R => |H z ω|) :=
    (isCompact_range ((hH.continuous ω).comp continuous_subtype_val).abs).bddAbove
  exact hlt.le.trans (le_ciSup (f := fun z : Osc.box x₀ R => |H z ω|) hb ⟨z, hz⟩)

/-- The difference of continuous versions of `H_{ε,1}` and `H_{c,1}` (`0 < ε ≤ c ≤ 1`) is a
continuous version of the band `H_{ε,c}` (band additivity, HA2 (F3)). -/
theorem sub_isBandVersion (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {ε c : ℝ} (hε : 0 < ε)
    (hεc : ε ≤ c) (hc1 : c ≤ 1) {H₁ H₂ : Rd d → Ω → ℝ} (h₁ : IsBandVersion P W κ ε 1 H₁)
    (h₂ : IsBandVersion P W κ c 1 H₂) :
    IsBandVersion P W κ ε c (fun z ω => H₁ z ω - H₂ z ω) where
  continuous ω := (h₁.continuous ω).sub (h₂.continuous ω)
  measurable z := (h₁.measurable z).sub (h₂.measurable z)
  ae_eq z := by
    filter_upwards [h₁.ae_eq z, h₂.ae_eq z, hW.bandVec_add_ae hκ hε hεc hc1 z] with ω e1 e2 e3
    rw [e1, e2, e3]
    ring

end Field

/-- The constant of the band-difference bound:
`2 √(1 + 4d log 2) (√(log 2 / 2) + √(π² d L / 8)) + blockConst d L √d`. -/
def diffConst (d : ℕ) (L : ℝ) : ℝ :=
  2 * √(1 + 4 * d * Real.log 2) * (√(Real.log 2 / 2) + √(π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8)) +
    Osc.blockConst d L √(d : ℝ)

/-- `diffConst d L ≥ 0`. -/
theorem diffConst_nonneg (d : ℕ) (L : ℝ) : 0 ≤ diffConst d L := by
  unfold diffConst
  have := Osc.blockConst_nonneg d (L := L) (Real.sqrt_nonneg (d : ℝ))
  positivity

/-- For the band `(ε, 2^{-N})` on `[-2,2]^d`:
`supMean d L (log 2) (4d(N+1) log 2) ≤ diffConst d L · √(N+1)`. -/
theorem supMean_le_diffConst (d : ℕ) (L : ℝ) (N : ℕ) :
    supMean d L (Real.log 2) (4 * d * ((N : ℝ) + 1) * Real.log 2) ≤
      diffConst d L * √((N : ℝ) + 1) := by
  unfold supMean diffConst
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hν : 1 ≤ √((N : ℝ) + 1) :=
    calc (1 : ℝ) = √1 := Real.sqrt_one.symm
      _ ≤ √((N : ℝ) + 1) := Real.sqrt_le_sqrt hN1
  have hlam : √(1 + 4 * d * ((N : ℝ) + 1) * Real.log 2) ≤
      √(1 + 4 * d * Real.log 2) * √((N : ℝ) + 1) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hlog.le)
      (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hB := Osc.blockConst_nonneg d (L := L) (Real.sqrt_nonneg (d : ℝ))
  have hs1 := Real.sqrt_nonneg (Real.log 2 / 2)
  have hs2 := Real.sqrt_nonneg (π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8)
  have hBν : Osc.blockConst d L √(d : ℝ) ≤ Osc.blockConst d L √(d : ℝ) * √((N : ℝ) + 1) :=
    le_mul_of_one_le_right hB hν
  have key : 2 * √(1 + 4 * d * ((N : ℝ) + 1) * Real.log 2) *
      (√(Real.log 2 / 2) + √(π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8)) ≤
      2 * (√(1 + 4 * d * Real.log 2) * √((N : ℝ) + 1)) *
      (√(Real.log 2 / 2) + √(π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8)) := by
    gcongr
  nlinarith [key, hBν]

section Field

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {κ : Rd d → ℝ}

/-- **The App. A.1 band estimate** (HA5 D11, band bound; explicit constants).  For
`2^{-N-1} ≤ ε ≤ 2^{-N}` and continuous versions `H₁` of `H_{ε,1}` and `H₂` of `H_{2^{-N},1}`,
`P*(∃ z ∈ closure U, diffConst d L · √(N+1) + u < |H₁ z - H₂ z|) ≤ 2 exp(-u²/(2 log 2))`. -/
theorem cutoff_diff_sup_tail [NeZero d] (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ a : ℝ, 0 < a → ∀ (b : ℝ) (z w : Rd d),
      ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2)
    (N : ℕ) {ε : ℝ} (hε1 : ((2 : ℝ) ^ (N + 1))⁻¹ ≤ ε) (hε2 : ε ≤ ((2 : ℝ) ^ N)⁻¹)
    {H₁ H₂ : Rd d → Ω → ℝ} (h₁ : IsBandVersion P W κ ε 1 H₁)
    (h₂ : IsBandVersion P W κ ((2 : ℝ) ^ N)⁻¹ 1 H₂) {u : ℝ} (hu : 0 ≤ u) :
    P {ω | ∃ z ∈ closure (cube d), diffConst d L * √((N : ℝ) + 1) + u < |H₁ z ω - H₂ z ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * Real.log 2))) := by
  set c : ℝ := ((2 : ℝ) ^ N)⁻¹ with hc
  have hpow : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ hpow
  have hε0 : 0 < ε := lt_of_lt_of_le (by positivity) hε1
  have hD := sub_isBandVersion hκ hW hε0 hε2 hc1 h₁ h₂
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc2ε : c ≤ 2 * ε := by
    have e : c = 2 * ((2 : ℝ) ^ (N + 1))⁻¹ := by
      rw [hc, pow_succ]
      ring
    rw [e]
    linarith
  have hbV : Real.log (c / ε) ≤ Real.log 2 :=
    Real.log_le_log (div_pos hc0 hε0) ((div_le_iff₀ hε0).2 (by linarith))
  have hℓ : (d : ℝ) * Real.log (2 * 2 / ε + 1) ≤ 4 * d * ((N : ℝ) + 1) * Real.log 2 := by
    have hinv : ε⁻¹ ≤ 2 ^ (N + 1) := by
      rw [inv_le_comm₀ hε0 (by positivity)]
      exact hε1
    have h1 : 2 * 2 / ε + 1 ≤ (2 : ℝ) ^ (N + 4) := by
      have e : (2 : ℝ) ^ (N + 4) = 8 * 2 ^ (N + 1) := by ring
      rw [e, div_eq_mul_inv]
      have : (1 : ℝ) ≤ 2 ^ (N + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have h2 : Real.log (2 * 2 / ε + 1) ≤ (N + 4 : ℕ) * Real.log 2 := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) h1
    have h3 : ((N + 4 : ℕ) : ℝ) * Real.log 2 ≤ 4 * ((N : ℝ) + 1) * Real.log 2 := by
      push_cast
      nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc (d : ℝ) * Real.log (2 * 2 / ε + 1) ≤ d * (4 * ((N : ℝ) + 1) * Real.log 2) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) hd0
      _ = 4 * d * ((N : ℝ) + 1) * Real.log 2 := by ring
  have htail := bandSup_tail hκ hW hε0 hε2 hD hL0 (hL ε hε0 c) hlog2 hbV 0 (R := 2) (by norm_num)
    hℓ hu
  refine (measure_mono fun ω hω => ?_).trans htail
  obtain ⟨z, hz, hlt⟩ := hω
  exact ⟨z, Osc.closure_cube_subset_box hz,
    lt_of_le_of_lt (by linarith [supMean_le_diffConst d L N]) hlt⟩

end Field

end SupB

open SupB

variable {d : ℕ}

/-- **Target T3** (HA5 D4: crude sup bounds, Lemma S, Lemma 3.4′, band bound), with constants
depending only on `κ` and `d`: there is `L > 0` such that for every white noise, every
`0 < a ≤ b`, every continuous version `H` of `H_{a,b}`, every `V > 0` with `log(b/a) ≤ V`, and
every box `B = x₀ + [-R, R]^d`, with `M = supMean d L V (d log(2R/a + 1))`
(`= √(2V(1+ℓ)) + blockConst d L √d + π √(dL) √((1+ℓ)/2)`, `ℓ = d log(2R/a + 1)`):
`E sup_B H ≤ M`, `E sup_B (-H) ≤ M`, `sup_B |H| ∈ L¹` with `E sup_B |H| ≤ 2M + √V`, and
`P*(∃ z ∈ B, M + u < |H z|) ≤ 2 exp(-u²/(2V))` for `u ≥ 0` (Borell–TIS).  For `a < b` one may
take `V = log(b/a)`. -/
theorem exists_bandSup_bounds [NeZero d] {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ L : ℝ, 0 < L ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ {H : Rd d → Ω → ℝ},
        IsBandVersion P W κ a b H → ∀ {V : ℝ}, 0 < V → Real.log (b / a) ≤ V →
        ∀ (x₀ : Rd d) {R : ℝ}, 0 ≤ R →
          (Integrable (fun ω => ⨆ z : Osc.box x₀ R, H z ω) P ∧
              ∫ ω, (⨆ z : Osc.box x₀ R, H z ω) ∂P ≤
                supMean d L V (d * Real.log (2 * R / a + 1))) ∧
            (Integrable (fun ω => ⨆ z : Osc.box x₀ R, -H z ω) P ∧
              ∫ ω, (⨆ z : Osc.box x₀ R, -H z ω) ∂P ≤
                supMean d L V (d * Real.log (2 * R / a + 1))) ∧
            (Integrable (fun ω => ⨆ z : Osc.box x₀ R, |H z ω|) P ∧
              ∫ ω, (⨆ z : Osc.box x₀ R, |H z ω|) ∂P ≤
                2 * supMean d L V (d * Real.log (2 * R / a + 1)) + √V) ∧
            ∀ {u : ℝ}, 0 ≤ u →
              P {ω | ∃ z ∈ Osc.box x₀ R,
                  supMean d L V (d * Real.log (2 * R / a + 1)) + u < |H z ω|} ≤
                ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * V))) := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_bandVec_sub_sq_le hκ
  have hL1 : 0 < L + 1 := by linarith
  refine ⟨L + 1, hL1, ?_⟩
  intro Ω _ P W hW a b ha hab H hH V hV hbV x₀ R hR
  have hL' : ∀ z w : Rd d, ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤
      (L + 1) * ‖z - w‖ ^ 2 / a ^ 2 := fun z w => (hL a ha b z w).trans (by gcongr; linarith)
  obtain ⟨h1, h2, h3, -⟩ := bandSup_bounds hκ hW ha hab hH hL1 hL' hV hbV x₀ hR le_rfl
  exact ⟨h1, h2, ⟨h3, integral_iSup_abs_le hκ hW ha hab hH hL1 hL' hV hbV x₀ hR le_rfl⟩,
    fun hu => bandSup_tail hκ hW ha hab hH hL1 hL' hV hbV x₀ hR le_rfl hu⟩

/-- **Target T4** (App. A.1, last paragraph; HA5 D11 band bound): there is `C ≥ 0`, depending
only on `κ` and `d`, such that for `2^{-N-1} ≤ ε ≤ 2^{-N}` the difference of continuous versions
of `H_{ε,1}` and `H_{2^{-N},1}` is `O_P(√N)` on `closure U`, uniformly in that range of `ε`:
`P*(∃ z ∈ closure U, C √(N+1) + u < |H_{ε,1}(z) - H_{2^{-N},1}(z)|) ≤ 2 exp(-u²/(2 log 2))`.
The second conjunct is the same statement for a family `H ε` of versions of `H_{ε,1}`,
`ε ∈ (0,1)` (as in the frozen `theorem11`), for `N ≥ 1`. -/
theorem exists_cutoff_diff_sup_tail [NeZero d] {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W →
      (∀ (N : ℕ) {ε : ℝ}, ((2 : ℝ) ^ (N + 1))⁻¹ ≤ ε → ε ≤ ((2 : ℝ) ^ N)⁻¹ →
        ∀ {H₁ H₂ : Rd d → Ω → ℝ}, IsBandVersion P W κ ε 1 H₁ →
          IsBandVersion P W κ ((2 : ℝ) ^ N)⁻¹ 1 H₂ → ∀ {u : ℝ}, 0 ≤ u →
            P {ω | ∃ z ∈ closure (cube d), C * √((N : ℝ) + 1) + u < |H₁ z ω - H₂ z ω|} ≤
              ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * Real.log 2)))) ∧
      ∀ {H : ℝ → Rd d → Ω → ℝ}, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
        ∀ (N : ℕ), 1 ≤ N → ∀ {ε : ℝ}, ((2 : ℝ) ^ (N + 1))⁻¹ ≤ ε → ε ≤ ((2 : ℝ) ^ N)⁻¹ →
          ∀ {u : ℝ}, 0 ≤ u →
            P {ω | ∃ z ∈ closure (cube d),
                C * √((N : ℝ) + 1) + u < |H ε z ω - H ((2 : ℝ) ^ N)⁻¹ z ω|} ≤
              ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * Real.log 2))) := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_bandVec_sub_sq_le hκ
  have hL1 : 0 < L + 1 := by linarith
  have hL' : ∀ a : ℝ, 0 < a → ∀ (b : ℝ) (z w : Rd d),
      ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ (L + 1) * ‖z - w‖ ^ 2 / a ^ 2 :=
    fun a ha b z w => (hL a ha b z w).trans (by gcongr; linarith)
  refine ⟨diffConst d (L + 1), diffConst_nonneg d _, ?_⟩
  intro Ω _ P W hW
  have hgen : ∀ (N : ℕ) {ε : ℝ}, ((2 : ℝ) ^ (N + 1))⁻¹ ≤ ε → ε ≤ ((2 : ℝ) ^ N)⁻¹ →
      ∀ {H₁ H₂ : Rd d → Ω → ℝ}, IsBandVersion P W κ ε 1 H₁ →
        IsBandVersion P W κ ((2 : ℝ) ^ N)⁻¹ 1 H₂ → ∀ {u : ℝ}, 0 ≤ u →
          P {ω | ∃ z ∈ closure (cube d),
              diffConst d (L + 1) * √((N : ℝ) + 1) + u < |H₁ z ω - H₂ z ω|} ≤
            ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * Real.log 2))) :=
    fun N ε hε1 hε2 H₁ H₂ h₁ h₂ u hu =>
      cutoff_diff_sup_tail hκ hW hL1 hL' N hε1 hε2 h₁ h₂ hu
  refine ⟨hgen, fun {H} hH N hN ε hε1 hε2 u hu => ?_⟩
  have hpow : (2 : ℝ) ≤ 2 ^ N := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hcN : ((2 : ℝ) ^ N)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hε0 : 0 < ε := lt_of_lt_of_le (by positivity) hε1
  exact hgen N hε1 hε2 (hH ε ⟨hε0, lt_of_le_of_lt hε2 hcN⟩)
    (hH _ ⟨by positivity, hcN⟩) hu

end HigherDimLFPP
