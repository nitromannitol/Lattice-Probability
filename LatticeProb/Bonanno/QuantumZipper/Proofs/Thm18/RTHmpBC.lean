/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.RTHmpBC at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.SWCoreN2Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-HMP (2): Gaussian families with logarithmic variance grow at most linearly in the scale

For each scale `k` let `Z k θ` (`θ` in a bounded countable `D k ⊂ ℝ^d`, sup norm) be a centred
Gaussian process with `Var (Z k θ) ≤ V (k + 1)` and the scale-relative modulus
`Var (Z k θ − Z k θ') ≤ L² (‖θ − θ'‖ / r_k)^β` for `‖θ − θ'‖ ≤ r_k²`. Then a.s., eventually in
`k`, `|Z k θ| ≤ a (k + 1)` for all `θ ∈ D k`, with `a = 3 (V/2 + log 4^d + 1)`
(`hmp_ae_eventually_le`).

This is the union bound over a grid plus the modulus that proves the logarithmic growth of the
circle average process: Hu–Miller–Peres, *Thick points of the Gaussian free field*, Ann. Probab. 38
(2010), Prop. 2.1 (modulus) and the proof of Lemma 3.1 (grid + union bound + Borel–Cantelli).
The per-box estimate (Dudley chaining + Borell–TIS) and the grid bookkeeping are those of
`SWCore.swcn2_box_bound` / `SWCore.swcn2_fixed` (Sheffield–Wang, arXiv:1605.06171, Lemma 3.5);
only the point term changes (Gaussian tail with variance `V (k + 1)` at level `a (k + 1)/3`).
Own adaptation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Real

namespace QuantumZipper
namespace R18
namespace RTHmp

open RegUnif SWCore

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **One grid box**, point variance `≤ V₁`. -/
theorem hmp_box_bound {d : ℕ} {Z : (Fin d → ℝ) → Ω → ℝ} {D : Set (Fin d → ℝ)}
    (hD : D.Countable) (hG : IsGaussianProcess Z P) (hc : ∀ θ, ∫ ω, Z θ ω ∂P = 0)
    (hZm : ∀ θ, Measurable (Z θ)) {V₁ L β r η : ℝ} (hβ : 0 < β)
    (hβ1 : β ≤ 1) (hL : 0 ≤ L) (hr : 0 < r) (hr1 : r ≤ 1)
    (hvar : ∀ θ ∈ D, Var[Z θ; P] ≤ V₁)
    (hmod : ∀ θ ∈ D, ∀ θ' ∈ D, ‖θ - θ'‖ ≤ r ^ 2 →
      Var[fun ω => Z θ ω - Z θ' ω; P] ≤ L ^ 2 * (‖θ - θ'‖ / r) ^ β)
    (g : Fin d → ℤ) (i₀ : Fin d → ℝ) (hi₀ : i₀ ∈ swcn2Box D (r ^ 2) g) :
    P (({ω | ∃ θ ∈ swcn2Box D (r ^ 2) g, η / 3 ≤ Z θ ω - Z i₀ ω} ∪
        {ω | ∃ θ ∈ swcn2Box D (r ^ 2) g, η / 3 ≤ -Z θ ω - -Z i₀ ω}) ∪
        ({ω | η / 3 ≤ Z i₀ ω} ∪ {ω | η / 3 ≤ -Z i₀ ω})) ≤
      ENNReal.ofReal (2 * Real.exp (fgmChainConst d β * L + π ^ 2 / 8 * L ^ 2 -
          η / 3 * (r ^ (β / 2))⁻¹) + 2 * Real.exp (V₁ / 2 - η / 3)) := by
  haveI : Countable D := hD.to_subtype
  set A := swcn2Box D (r ^ 2) g with hA
  set u := r ^ (β / 2) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hr _
  obtain ⟨hs_u, hr_u⟩ := swcn2_rpow_facts hr β
  rw [← hu] at hs_u hr_u
  have hs0 : 0 ≤ r ^ 2 := by positivity
  have hGn : IsGaussianProcess (fun θ ω => -Z θ ω) P := by
    simpa using hG.smul (fun _ => (-1 : ℝ))
  have hcn : ∀ θ, ∫ ω, -Z θ ω ∂P = 0 := fun θ => by rw [integral_neg, hc, neg_zero]
  have hZmn : ∀ θ, Measurable fun ω => -Z θ ω := fun θ => (hZm θ).neg
  have hboxW : ∀ W : (Fin d → ℝ) → Ω → ℝ, IsGaussianProcess W P → (∀ θ, ∫ ω, W θ ω ∂P = 0) →
      (∀ θ, Measurable (W θ)) →
      (∀ θ θ', Var[fun ω => W θ ω - W θ' ω; P] = Var[fun ω => Z θ ω - Z θ' ω; P]) →
      P {ω | ∃ θ ∈ A, η / 3 ≤ W θ ω - W i₀ ω} ≤
        ENNReal.ofReal (Real.exp (fgmChainConst d β * L + π ^ 2 / 8 * L ^ 2 -
          η / 3 * u⁻¹)) := by
    intro W hW hWc hWm hWv
    have hWD : IsGaussianProcess (fun i : D => W i) P := hW.restrict D
    set A' : Set D := {i | (i : Fin d → ℝ) ∈ A} with hA'
    have hdiam : ∀ i ∈ A', ∀ j ∈ A', ‖(i : Fin d → ℝ) - j‖ ≤ r ^ 2 := fun i hi j hj =>
      swcn2_box_diam hs0 hi hj
    have hkey := swcn2_box_tail hWD (fun i => hWc i) (fun i => hWm i) (Subtype.val : D → _)
      (L := L / u) (a := r ^ 2) (σ := L * u) (t := u⁻¹) (η := η / 3) hβ hβ1
      (div_nonneg hL hu0.le) (mul_nonneg hL hu0.le) (inv_nonneg.2 hu0.le) ⟨i₀, hi₀.1⟩ A'
      hdiam (fun i hi j hj => by
        rw [hWv]
        refine (hmod i i.2 j j.2 (hdiam i hi j hj)).trans (le_of_eq ?_)
        rw [Real.div_rpow (norm_nonneg _) hr.le, hr_u]
        field_simp)
      (fun i hi => by
        rw [hWv]
        have hd := hdiam i hi ⟨i₀, hi₀.1⟩ hi₀
        refine (hmod i i.2 i₀ hi₀.1 hd).trans ?_
        have h1 : (‖(i : Fin d → ℝ) - i₀‖ / r) ^ β ≤ (r ^ 2 / r) ^ β :=
          Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hd hr.le) hβ.le
        have h2 : r ^ 2 / r = r := by field_simp
        rw [h2, hr_u] at h1
        calc L ^ 2 * (‖(i : Fin d → ℝ) - i₀‖ / r) ^ β ≤ L ^ 2 * u ^ 2 :=
              mul_le_mul_of_nonneg_left h1 (sq_nonneg L)
          _ = (L * u) ^ 2 := by ring)
    refine (measure_mono fun ω hω => ?_).trans (hkey.trans (le_of_eq ?_))
    · obtain ⟨θ, hθ, hle⟩ := hω
      exact ⟨⟨θ, hθ.1⟩, hθ, hle⟩
    · congr 2
      rw [hs_u]
      field_simp
  have hU := hboxW Z hG hc hZm fun _ _ => rfl
  have hU' := hboxW (fun θ ω => -Z θ ω) hGn hcn hZmn fun θ θ' => swcn2_var_neg_sub
  have hpt : ∀ U : Ω → ℝ, HasGaussianLaw U P → ∫ ω, U ω ∂P = 0 → Measurable U →
      Var[U; P] ≤ V₁ →
      P {ω | η / 3 ≤ U ω} ≤ ENNReal.ofReal (Real.exp (V₁ / 2 - η / 3)) := by
    intro U hUg hUc hUm hUv
    refine (swcn2_point_tail hUg hUc hUm (t := 1) (η := η / 3) zero_le_one).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    linarith
  have hW1 := hpt (Z i₀) (hG.hasGaussianLaw_eval i₀) (hc i₀) (hZm i₀) (hvar i₀ hi₀.1)
  have hW2 := hpt (fun ω => -Z i₀ ω) (hGn.hasGaussianLaw_eval i₀) (hcn i₀) (hZmn i₀)
    (by rw [variance_fun_neg]; exact hvar i₀ hi₀.1)
  calc _ ≤ (P {ω | ∃ θ ∈ A, η / 3 ≤ Z θ ω - Z i₀ ω} +
          P {ω | ∃ θ ∈ A, η / 3 ≤ -Z θ ω - -Z i₀ ω}) +
        (P {ω | η / 3 ≤ Z i₀ ω} + P {ω | η / 3 ≤ -Z i₀ ω}) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) (measure_union_le _ _))
    _ ≤ (ENNReal.ofReal (Real.exp (fgmChainConst d β * L + π ^ 2 / 8 * L ^ 2 - η / 3 * u⁻¹)) +
          ENNReal.ofReal (Real.exp (fgmChainConst d β * L + π ^ 2 / 8 * L ^ 2 - η / 3 * u⁻¹))) +
        (ENNReal.ofReal (Real.exp (V₁ / 2 - η / 3)) +
          ENNReal.ofReal (Real.exp (V₁ / 2 - η / 3))) :=
        add_le_add (add_le_add hU hU') (add_le_add hW1 hW2)
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- The growth constant. -/
def hmpA (d : ℕ) (V : ℝ) : ℝ := 3 * (V / 2 + Real.log ((4 : ℝ) ^ d) + 1)

theorem hmp_log4_nonneg (d : ℕ) : 0 ≤ Real.log ((4 : ℝ) ^ d) :=
  Real.log_nonneg (one_le_pow₀ (by norm_num))

/-- **Linear growth in the scale** (grid boxes of side `r_k²`, per-box tails, Borel–Cantelli). -/
theorem hmp_ae_eventually_le {d : ℕ} (Z : ℕ → (Fin d → ℝ) → Ω → ℝ) {D : ℕ → Set (Fin d → ℝ)}
    (hD : ∀ k, (D k).Countable) {R : ℝ} (hR : 0 ≤ R) (hDR : ∀ k, ∀ θ ∈ D k, ‖θ‖ ≤ R)
    (hG : ∀ k, IsGaussianProcess (Z k) P) (hc : ∀ k θ, ∫ ω, Z k θ ω ∂P = 0)
    (hZm : ∀ k θ, Measurable (Z k θ)) {V L β : ℝ} (hβ : 0 < β)
    (hβ1 : β ≤ 1) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hvar : ∀ k, ∀ θ ∈ D k, Var[Z k θ; P] ≤ V * (k + 1))
    (hmod : ∀ k, ∀ θ ∈ D k, ∀ θ' ∈ D k, ‖θ - θ'‖ ≤ radius k ^ 2 →
      Var[fun ω => Z k θ ω - Z k θ' ω; P] ≤ L ^ 2 * (‖θ - θ'‖ / radius k) ^ β) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ θ ∈ D k, |Z k θ ω| ≤ hmpA d V * (k + 1) := by
  classical
  set a := hmpA d V with ha
  set c0 : ℝ := Real.log ((4 : ℝ) ^ d) + 1 with hc0
  have hc0p : 0 < c0 := by have := hmp_log4_nonneg d; linarith
  have ha3 : a / 3 = V / 2 + c0 := by simp only [ha, hmpA, hc0]; ring
  have ha0 : 0 < a / 3 := by rw [ha3]; linarith
  set η : ℕ → ℝ := fun k => a * (k + 1) with hη
  set r : ℕ → ℝ := fun k => radius k with hrdef
  have hr : ∀ k, 0 < r k := fun k => by simp only [hrdef]; unfold radius; positivity
  set N : ℕ → ℕ := fun k => ⌈R / r k ^ 2⌉₊ + 1 with hN
  set G : ℕ → Finset (Fin d → ℤ) := fun k =>
    Fintype.piFinset fun _ : Fin d => Finset.Icc (-((N k : ℕ) : ℤ)) ((N k : ℕ) : ℤ) with hGdef
  set A : ℕ → (Fin d → ℤ) → Set (Fin d → ℝ) := fun k g => swcn2Box (D k) (r k ^ 2) g with hA
  set i₀ : ℕ → (Fin d → ℤ) → (Fin d → ℝ) := fun k g =>
    if h : (A k g).Nonempty then h.some else 0 with hi₀
  set bad : ℕ → (Fin d → ℤ) → Set Ω := fun k g => if (A k g).Nonempty then
    (({ω | ∃ θ ∈ A k g, η k / 3 ≤ Z k θ ω - Z k (i₀ k g) ω} ∪
      {ω | ∃ θ ∈ A k g, η k / 3 ≤ -Z k θ ω - -Z k (i₀ k g) ω}) ∪
      ({ω | η k / 3 ≤ Z k (i₀ k g) ω} ∪ {ω | η k / 3 ≤ -Z k (i₀ k g) ω})) else ∅ with hbad
  set E : ℕ → Set Ω := fun k => ⋃ g ∈ G k, bad k g with hE
  set B1 : ℝ := (2 : ℝ) ^ (β / 2) with hB1
  have hB1g : 1 < B1 := Real.one_lt_rpow (by norm_num) (by positivity)
  set C1 : ℝ := fgmChainConst d β * L + π ^ 2 / 8 * L ^ 2 with hC1
  set b : ℕ → ℝ := fun k => (2 * Real.exp (C1 - η k / 3 * B1 ^ k) +
    2 * Real.exp (V * (k + 1) / 2 - η k / 3)) with hb
  have hbad_le : ∀ k g, P (bad k g) ≤ ENNReal.ofReal (b k) := by
    intro k g
    by_cases hne : (A k g).Nonempty
    · have hmem : i₀ k g ∈ A k g := by simp only [hi₀, dif_pos hne]; exact hne.some_mem
      simp only [hbad, if_pos hne]
      have h := hmp_box_bound (hD k) (hG k) (hc k) (hZm k) hβ hβ1 hL (hr k)
        (swcn2_radius_le_one k) (hvar k) (hmod k) g (i₀ k g) hmem (P := P) (η := η k)
      refine h.trans (le_of_eq ?_)
      rw [swcn2_rad_rpow_inv]
    · simp only [hbad, if_neg hne, measure_empty]; exact bot_le
  have hcard : ∀ k, ((G k).card : ℝ) ≤ (2 * R + 5) ^ d * ((4 : ℝ) ^ d) ^ k := by
    intro k
    have hr2 : r k ^ 2 = ((4 : ℝ) ^ k)⁻¹ := by
      simp only [hrdef]; unfold radius
      rw [← pow_mul, inv_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
    have hNk : (N k : ℝ) ≤ R * 4 ^ k + 2 := by
      have hc1 := Nat.ceil_lt_add_one (show 0 ≤ R / r k ^ 2 by positivity)
      rw [hr2, div_inv_eq_mul] at hc1
      have e : (N k : ℝ) = ((⌈R * 4 ^ k⌉₊ : ℕ) : ℝ) + 1 := by
        simp only [hN, hr2, div_inv_eq_mul]; push_cast; ring
      rw [e]; linarith
    rw [hGdef, Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
    push_cast
    have h4 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    have hbase : ((((N k : ℤ) + 1 - -(N k : ℤ)).toNat : ℕ) : ℝ) ≤ (2 * R + 5) * 4 ^ k := by
      have e : ((N k : ℤ) + 1 - -(N k : ℤ)).toNat = 2 * N k + 1 := by omega
      rw [e]; push_cast; nlinarith
    calc ((((N k : ℤ) + 1 - -(N k : ℤ)).toNat : ℕ) : ℝ) ^ d ≤ ((2 * R + 5) * 4 ^ k) ^ d :=
          pow_le_pow_left₀ (by positivity) hbase d
      _ = (2 * R + 5) ^ d * ((4 : ℝ) ^ d) ^ k := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm d]
  have hEk : ∀ k, P (E k) ≤ ENNReal.ofReal ((2 * R + 5) ^ d * ((4 : ℝ) ^ d) ^ k * b k) := by
    intro k
    have hb0 : 0 ≤ b k := by simp only [hb]; positivity
    calc P (E k) ≤ ∑ g ∈ G k, P (bad k g) := measure_biUnion_finset_le _ _
      _ ≤ ∑ g ∈ G k, ENNReal.ofReal (b k) := Finset.sum_le_sum fun g _ => hbad_le k g
      _ = ENNReal.ofReal ((G k).card * b k) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hcard k) hb0)
  -- summability
  have h4d : (0 : ℝ) < (4 : ℝ) ^ d := by positivity
  have hq : (4 : ℝ) ^ d * Real.exp (-c0) = Real.exp (-1) := by
    rw [hc0, neg_add, Real.exp_add, Real.exp_neg, Real.exp_log h4d]
    field_simp
  have hq1 : Real.exp (-1) < 1 := (Real.exp_lt_exp.2 (by norm_num : (-1 : ℝ) < 0)).trans_eq Real.exp_zero
  have hsum : Summable fun k => (2 * R + 5) ^ d * ((4 : ℝ) ^ d) ^ k * b k := by
    have h1 := (swcn2_summable (A := (4 : ℝ) ^ d) (by positivity) ha0 hB1g).mul_left
      ((2 * R + 5) ^ d * (2 * Real.exp C1))
    have h2 := (summable_geometric_of_lt_one (Real.exp_pos _).le hq1).mul_left
      ((2 * R + 5) ^ d * (2 * Real.exp (-c0)))
    refine Summable.of_nonneg_of_le (fun k => by simp only [hb]; positivity) (fun k => ?_)
      (h1.add h2)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hB1k : 0 ≤ B1 ^ k := by positivity
    have e1 : Real.exp (C1 - η k / 3 * B1 ^ k) ≤ Real.exp C1 * Real.exp (-(a / 3 * B1 ^ k)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : a / 3 * B1 ^ k ≤ η k / 3 * B1 ^ k := by
        refine mul_le_mul_of_nonneg_right ?_ hB1k
        simp only [hη]; nlinarith
      linarith
    have e2 : ((4 : ℝ) ^ d) ^ k * Real.exp (V * (k + 1) / 2 - η k / 3) =
        Real.exp (-c0) * Real.exp (-1) ^ k := by
      have e3 : V * (k + 1) / 2 - η k / 3 = -c0 + k * (-c0) := by
        simp only [hη]
        have : a * (k + 1) / 3 = (a / 3) * (k + 1) := by ring
        rw [this, ha3]; ring
      rw [e3, Real.exp_add, Real.exp_nat_mul, ← hq, mul_pow]
      ring
    have hR5 : 0 ≤ (2 * R + 5) ^ d := by positivity
    simp only [hb]
    calc (2 * R + 5) ^ d * ((4 : ℝ) ^ d) ^ k * (2 * Real.exp (C1 - η k / 3 * B1 ^ k) +
          2 * Real.exp (V * (k + 1) / 2 - η k / 3))
        = (2 * R + 5) ^ d * (2 * (((4 : ℝ) ^ d) ^ k * Real.exp (C1 - η k / 3 * B1 ^ k))) +
          (2 * R + 5) ^ d * (2 * (((4 : ℝ) ^ d) ^ k *
            Real.exp (V * (k + 1) / 2 - η k / 3))) := by ring
      _ ≤ (2 * R + 5) ^ d * (2 * (((4 : ℝ) ^ d) ^ k * (Real.exp C1 *
            Real.exp (-(a / 3 * B1 ^ k))))) +
          (2 * R + 5) ^ d * (2 * (Real.exp (-c0) * Real.exp (-1) ^ k)) := by
          rw [e2]; gcongr
      _ = _ := by ring
  have htsum : (∑' k, P (E k)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEk)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by simp only [hb]; positivity) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem htsum] with ω hω
  filter_upwards [hω] with k hk θ hθ
  set g : Fin d → ℤ := fun i => round (θ i / r k ^ 2) with hg
  have hs : 0 < r k ^ 2 := pow_pos (hr k) 2
  have hθA : θ ∈ A k g := swcn2_mem_box hs hθ
  have hgG : g ∈ G k := swcn2_round_mem hs hR (hDR k θ hθ)
  have hne : (A k g).Nonempty := ⟨θ, hθA⟩
  have hnb : ω ∉ bad k g := fun h => hk (mem_biUnion hgG h)
  simp only [hbad, if_pos hne, mem_union, mem_ofPred_eq, not_or, not_exists, not_and,
    not_le] at hnb
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hnb
  have a1 := h1 θ hθA
  have a2 := h2 θ hθA
  have hηk : 0 ≤ η k := by simp only [hη]; exact mul_nonneg (by linarith) (by positivity)
  rw [abs_le]
  constructor <;> linarith

end RTHmp
end R18
end QuantumZipper
