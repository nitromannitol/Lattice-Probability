/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.ProducersGrid at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces

/-!
# Elementary finite-grid producer for the scaled-grid estimate

This module proves the center/radius lattice count in the waypoint construction, lines 578–582. It uses the same integer triples and
admissibility conditions as the interface, with a finite coordinate box containing every admissible triple.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellFamily

private theorem producer_mesh_eq_inv_pow (k : ℕ) : mesh k = ((2 : ℝ) ^ k)⁻¹ := by
  simp [mesh, zpow_neg, zpow_natCast]

private theorem producer_mesh_pos (k : ℕ) : 0 < mesh k := by
  rw [producer_mesh_eq_inv_pow]
  positivity

private theorem producer_mesh_le_one (k : ℕ) : mesh k ≤ 1 := by
  rw [producer_mesh_eq_inv_pow]
  apply (inv_le_one₀ (by positivity)).2
  exact one_le_pow₀ (by norm_num : 1 ≤ (2 : ℝ))

private def gridBox (N : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ
    (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ))

private def gridAdmissible (χ β ρ : ℝ) (k : ℕ) (t : ℤ × ℤ × ℤ) : Prop :=
  gridCenter (mesh k) χ t ∈ ball (0 : ℂ) ρ ∧
  mesh k ^ β ≤ gridRadius (mesh k) χ t ∧ gridRadius (mesh k) χ t ≤ ρ ∧
  ball (gridCenter (mesh k) χ t) (2 * gridRadius (mesh k) χ t) ⊆ ball (0 : ℂ) ρ

private noncomputable def gridSet (χ β ρ : ℝ) (k : ℕ) : Finset (ℤ × ℤ × ℤ) := by
  classical
  let a := mesh k ^ χ
  let N := ⌈(abs ρ + 1) / a⌉₊ + 1
  exact (gridBox N).filter (gridAdmissible χ β ρ k)

private lemma gridCenterCoordBound {χ β ρ : ℝ} {k : ℕ} {m n ℓ : ℤ}
    (_hχ : 0 < χ) (_hβ : 0 < β)
    (hvalid : gridAdmissible χ β ρ k (m, n, ℓ)) :
    |(m : ℝ)| ≤ (abs ρ + 1) / mesh k ^ χ ∧
    |(n : ℝ)| ≤ (abs ρ + 1) / mesh k ^ χ ∧
    |(ℓ : ℝ)| ≤ (abs ρ + 1) / mesh k ^ χ := by
  have ha : 0 < mesh k ^ χ := Real.rpow_pos_of_pos (producer_mesh_pos k) χ
  have hn : ‖gridCenter (mesh k) χ (m, n, ℓ)‖ < ρ := by
    have hmem := hvalid.1
    rw [Metric.mem_ball, dist_eq_norm] at hmem
    simpa [gridCenter] using hmem
  have hmNorm : |(mesh k ^ χ * (m : ℝ))| ≤ ‖gridCenter (mesh k) χ (m, n, ℓ)‖ := by
    have := Complex.abs_re_le_norm (gridCenter (mesh k) χ (m, n, ℓ))
    simpa [gridCenter, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_im, Complex.ofReal_im] using this
  have hnNorm : |(mesh k ^ χ * (n : ℝ))| ≤ ‖gridCenter (mesh k) χ (m, n, ℓ)‖ := by
    have := Complex.abs_im_le_norm (gridCenter (mesh k) χ (m, n, ℓ))
    simpa [gridCenter, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_im, Complex.ofReal_im] using this
  have hradpos : 0 < gridRadius (mesh k) χ (m, n, ℓ) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (producer_mesh_pos k) β) hvalid.2.1
  have hρ : 0 ≤ ρ := le_of_lt (lt_of_lt_of_le
    (Real.rpow_pos_of_pos (producer_mesh_pos k) β) (le_trans hvalid.2.1 hvalid.2.2.1))
  have hradle : gridRadius (mesh k) χ (m, n, ℓ) ≤ ρ := hvalid.2.2.1
  have hlbound : |(ℓ : ℝ)| ≤ (abs ρ + 1) / mesh k ^ χ := by
    have hℓpos : 0 < (ℓ : ℝ) := by
      have : 0 < mesh k ^ χ * (ℓ : ℝ) := by simpa [gridRadius] using hradpos
      exact (mul_pos_iff_of_pos_left ha).mp this
    have hmul : mesh k ^ χ * (ℓ : ℝ) ≤ ρ := by simpa [gridRadius] using hradle
    rw [abs_of_pos hℓpos]
    apply (le_div_iff₀ ha).2
    nlinarith [le_abs_self ρ]
  have hmBound : |(m : ℝ)| ≤ (abs ρ + 1) / mesh k ^ χ := by
    apply (le_div_iff₀ ha).2
    have hmul : mesh k ^ χ * |(m : ℝ)| ≤ ‖gridCenter (mesh k) χ (m, n, ℓ)‖ := by
      simpa [abs_mul, abs_of_pos ha, mul_comm] using hmNorm
    nlinarith [le_abs_self ρ]
  have hnBound : |(n : ℝ)| ≤ (abs ρ + 1) / mesh k ^ χ := by
    apply (le_div_iff₀ ha).2
    have hmul : mesh k ^ χ * |(n : ℝ)| ≤ ‖gridCenter (mesh k) χ (m, n, ℓ)‖ := by
      simpa [abs_mul, abs_of_pos ha, mul_comm] using hnNorm
    nlinarith [le_abs_self ρ]
  exact ⟨hmBound, hnBound, hlbound⟩

private lemma integer_in_gridBox {χ β ρ : ℝ} {k : ℕ} {m n ℓ : ℤ}
    (hχ : 0 < χ) (hβ : 0 < β)
    (hvalid : gridAdmissible χ β ρ k (m, n, ℓ)) :
    (m, n, ℓ) ∈ gridBox (⌈(abs ρ + 1) / mesh k ^ χ⌉₊ + 1) := by
  rcases gridCenterCoordBound hχ hβ hvalid with ⟨hm, hn, hℓ⟩
  let N : ℕ := ⌈(abs ρ + 1) / mesh k ^ χ⌉₊ + 1
  have hRnonneg : 0 ≤ (abs ρ + 1) / mesh k ^ χ :=
    div_nonneg (by positivity) (le_of_lt (Real.rpow_pos_of_pos (producer_mesh_pos k) χ))
  have hNlt : (N : ℝ) > (abs ρ + 1) / mesh k ^ χ := by
    dsimp [N]
    push_cast
    have hceil : (abs ρ + 1) / mesh k ^ χ ≤
        (⌈(abs ρ + 1) / mesh k ^ χ⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have bound_int (j : ℤ) (hj : |(j : ℝ)| ≤ (abs ρ + 1) / mesh k ^ χ) :
      -(N : ℤ) ≤ j ∧ j ≤ (N : ℤ) := by
    have hj' : |(j : ℝ)| < (N : ℝ) := lt_of_le_of_lt hj hNlt
    have habs := abs_le.mp (le_of_lt hj')
    have hjlo : -(N : ℝ) ≤ (j : ℝ) := by linarith [habs.1]
    have hjhi : (j : ℝ) ≤ (N : ℝ) := by linarith [habs.2]
    constructor
    · exact_mod_cast hjlo
    · exact_mod_cast hjhi
  simp only [gridBox, Finset.mem_product, Finset.mem_Icc]
  exact ⟨bound_int m hm, bound_int n hn, bound_int ℓ hℓ⟩

private lemma card_gridBox (N : ℕ) :
    ((gridBox N).card : ℝ) = (2 * (N : ℝ) + 1) ^ 3 := by
  simp only [gridBox, Finset.card_product]
  have hcard : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) = 2 * (N : ℝ) + 1 := by
    rw [Int.card_Icc]
    have hnat : ((N : ℤ) + 1 - (-(N : ℤ))).toNat = 2 * N + 1 := by
      apply Nat.cast_injective (R := ℤ)
      rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ (N : ℤ) + 1 - (-(N : ℤ)))]
      push_cast
      ring
    norm_cast
  push_cast
  rw [hcard]
  ring

/-- The finite-grid lattice count in the exact `FiniteGridCount` interface shape. -/
theorem finiteGridCount_holds (ρ : ℝ) : FiniteGridCount ρ := by
  classical
  intro χ β hχ hβ hβχ
  let Cgrid : ℝ := (2 * abs ρ + 10) ^ 3
  refine ⟨Cgrid, ?_, ?_⟩
  · dsimp [Cgrid]
    positivity
  · refine ⟨gridSet χ β ρ, ?_, ?_⟩
    · intro k m n ℓ
      classical
      simp only [gridSet, Finset.mem_filter]
      constructor
      · rintro ⟨_, hvalid⟩
        simpa [gridAdmissible, gridCenter, gridRadius] using hvalid
      · intro hvalid
        refine ⟨integer_in_gridBox hχ hβ ?_, ?_⟩
        · simpa [gridAdmissible, gridCenter, gridRadius] using hvalid
        · simpa [gridAdmissible, gridCenter, gridRadius] using hvalid
    · intro k
      let a := mesh k ^ χ
      let N := ⌈(abs ρ + 1) / a⌉₊ + 1
      have haPos : 0 < a := Real.rpow_pos_of_pos (producer_mesh_pos k) χ
      have haLe : a ≤ 1 := Real.rpow_le_one (le_of_lt (producer_mesh_pos k))
        (producer_mesh_le_one k) (le_of_lt hχ)
      have hN : (N : ℝ) < (abs ρ + 1) / a + 2 := by
        dsimp [N]
        push_cast
        have hR : (⌈(abs ρ + 1) / a⌉₊ : ℝ) < (abs ρ + 1) / a + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        linarith
      have hbox : ((gridBox N).card : ℝ) ≤ ((2 * abs ρ + 10) / a) ^ 3 := by
        rw [card_gridBox]
        have hside : 2 * (N : ℝ) + 1 ≤ (2 * abs ρ + 10) / a := by
          have hrough : 2 * (N : ℝ) + 1 < 2 * ((abs ρ + 1) / a) + 5 := by linarith
          have hfive : (5 : ℝ) ≤ 5 / a := by
            exact (le_div_iff₀ haPos).2 (by nlinarith [haLe])
          have hmain : 2 * ((abs ρ + 1) / a) + 5 / a = (2 * abs ρ + 7) / a := by
            field_simp
            ring
          have hbase : (2 * abs ρ + 7) / a ≤ (2 * abs ρ + 10) / a := by
            exact div_le_div_of_nonneg_right (by nlinarith [abs_nonneg ρ]) haPos.le
          linarith
        exact pow_le_pow_left₀ (by positivity) hside 3
      have hcard : ((gridSet χ β ρ k).card : ℝ) ≤ ((2 * abs ρ + 10) / a) ^ 3 := by
        calc
          ((gridSet χ β ρ k).card : ℝ) ≤ (gridBox N).card := by
            exact_mod_cast Finset.card_filter_le _ _
          _ ≤ ((2 * abs ρ + 10) / a) ^ 3 := hbox
      have hpow3 : mesh k ^ (3 * χ) = a ^ 3 := by
        dsimp [a]
        rw [show 3 * χ = χ * 3 by ring, Real.rpow_mul (le_of_lt (producer_mesh_pos k)) χ 3]
        exact Real.rpow_natCast _ 3
      have hfinal : ((2 * abs ρ + 10) / a) ^ 3 ≤ Cgrid * mesh k ^ (-3 * χ) := by
        rw [div_pow]
        dsimp [Cgrid]
        rw [div_eq_mul_inv, show -3 * χ = -(3 * χ) by ring,
          Real.rpow_neg (le_of_lt (producer_mesh_pos k)), hpow3]
      have hcardNat : (gridSet χ β ρ k).card ≤ (gridBox N).card := by
        exact Finset.card_filter_le _ _
      exact hcard.trans hfinal

end MatedCRTHarmonic.CellFamily
