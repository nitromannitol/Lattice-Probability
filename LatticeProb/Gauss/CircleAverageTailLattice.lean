import LatticeProb.Gauss.CircleAverageTailUniform

/-!
# Lattice union bound for circle averages of the whole-plane Gaussian free field

For a whole-plane Gaussian free field `h`, `0 < ε < 1`, `r̄ > 0`, `R ≥ 0`, `ν > 0` and `q > 0`, let
`Λ` be the lattice `(ε^{1+ν} r̄ / 4)(ℤ + iℤ)`.  We bound the probability that some circle average
`h_r(w)` with `w ∈ Λ`, `‖w‖ ≤ R r̄` and `r ∈ [ε^{1+ν} r̄, ε r̄]` differs from `h_{r̄}(0)` by at least
`q log (1/ε)`: it is at most
`(8R+1)² (2 + 2 (1+R)^{(q/(1+√ν))²}) ε^{q²/(2(1+√ν)²) - (2+2ν)}`,
a constant depending only on `q, ν, R` (not on `r̄` or `ε`) times a power of `ε`.  This follows from
the one-point bound with `s = q√ν/(1+√ν)` (for which `s²/(2ν) = (q-s)²/2 = q²/(2(1+√ν)²)`) and a
union bound over the at most `(8R+1)² ε^{-(2+2ν)}` lattice points in the disc `‖w‖ ≤ R r̄`.

* `LatticeProb.Gauss.latticePoint`: the lattice point `δ (m + n i)`;
* `LatticeProb.Gauss.IsWholePlaneGFF.measure_exists_lattice_circle_sub_start_ge_le`: the bound.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.Gauss

/-- The lattice point `δ (m + n i)` of the lattice `δ (ℤ + iℤ)`. -/
def latticePoint (δ : ℝ) (m n : ℤ) : ℂ := (δ : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)

/-- A lattice point of norm at most `R'` has both integer coordinates of modulus at most `R'/δ`. -/
theorem abs_le_div_of_norm_latticePoint_le {δ R' : ℝ} (hδ : 0 < δ) {m n : ℤ}
    (h : ‖latticePoint δ m n‖ ≤ R') : (|(m : ℝ)| ≤ R' / δ) ∧ (|(n : ℝ)| ≤ R' / δ) := by
  have hre : (latticePoint δ m n).re = δ * m := by simp [latticePoint]
  have him : (latticePoint δ m n).im = δ * n := by simp [latticePoint]
  have h1 := Complex.abs_re_le_norm (latticePoint δ m n)
  have h2 := Complex.abs_im_le_norm (latticePoint δ m n)
  rw [hre, abs_mul, abs_of_pos hδ] at h1
  rw [him, abs_mul, abs_of_pos hδ] at h2
  exact ⟨(le_div_iff₀ hδ).2 (by linarith), (le_div_iff₀ hδ).2 (by linarith)⟩

/-- The square box `[-N, N]²` of integers, `N = ⌊X⌋`, has at most `(2X+1)²` points. -/
theorem card_box_le {X : ℝ} (hX : 0 ≤ X) :
    (((Finset.Icc (-⌊X⌋) ⌊X⌋) ×ˢ (Finset.Icc (-⌊X⌋) ⌊X⌋)).card : ℝ) ≤ (2 * X + 1) ^ 2 := by
  have hN : 0 ≤ ⌊X⌋ := Int.floor_nonneg.2 hX
  have hNX : (⌊X⌋ : ℝ) ≤ X := Int.floor_le X
  rw [Finset.card_product, Int.card_Icc]
  have h1 : (((⌊X⌋ + 1 - -⌊X⌋).toNat : ℕ) : ℤ) = 2 * ⌊X⌋ + 1 := by
    rw [Int.toNat_of_nonneg (by omega)]; ring
  have h2 : ((⌊X⌋ + 1 - -⌊X⌋).toNat : ℝ) = 2 * (⌊X⌋ : ℝ) + 1 := by
    exact_mod_cast h1
  push_cast
  rw [h2, ← sq]
  have h3 : (0 : ℝ) ≤ 2 * (⌊X⌋ : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (⌊X⌋ : ℝ) := by exact_mod_cast hN
    linarith
  exact pow_le_pow_left₀ h3 (by linarith) 2

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Lattice union bound.** Let `0 < ε < 1`, `r̄ > 0`, `R ≥ 0`, `ν > 0`, `q > 0` and
`δ = ε^{1+ν} r̄ / 4`.  Then
`P {∃ w ∈ δ(ℤ+iℤ), ‖w‖ ≤ R r̄, ∃ r ∈ [ε^{1+ν} r̄, ε r̄], q log (1/ε) ≤ |h_r(w) - h_{r̄}(0)|}`
is at most `(8R+1)² (2 + 2 (1+R)^{(q/(1+√ν))²}) ε^{q²/(2(1+√ν)²) - (2+2ν)}`. -/
theorem measure_exists_lattice_circle_sub_start_ge_le (hh : IsWholePlaneGFF P hC hcirc)
    {ε R rbar ν q : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hr : 0 < rbar) (hR : 0 ≤ R) (hν : 0 < ν)
    (hq : 0 < q) :
    P {ω | ∃ m n : ℤ, ‖latticePoint (ε ^ (1 + ν) * rbar / 4) m n‖ ≤ R * rbar ∧
        ∃ r ∈ Icc (ε ^ (1 + ν) * rbar) (ε * rbar),
          q * -Real.log ε ≤
            |hcirc ω r (latticePoint (ε ^ (1 + ν) * rbar / 4) m n) - hcirc ω rbar 0|} ≤
      ENNReal.ofReal ((8 * R + 1) ^ 2 *
        (2 + 2 * Real.exp ((q / (1 + Real.sqrt ν)) ^ 2 * Real.log (1 + R))) *
        ε ^ (q ^ 2 / (2 * (1 + Real.sqrt ν) ^ 2) - (2 + 2 * ν))) := by
  obtain ⟨t, ht0, htν⟩ : ∃ t : ℝ, 0 < t ∧ Real.sqrt ν = t := ⟨_, Real.sqrt_pos.2 hν, rfl⟩
  have ht2 : t ^ 2 = ν := by rw [← htν]; exact Real.sq_sqrt hν.le
  rw [htν]
  subst ht2
  set κ : ℝ := ε ^ (1 + t ^ 2) with hκ
  have hκ0 : 0 < κ := Real.rpow_pos_of_pos hε0 _
  have hκ1 : κ ≤ 1 := Real.rpow_le_one hε0.le hε1.le (by positivity)
  set δ : ℝ := κ * rbar / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  set e : ℝ := q ^ 2 / (2 * (1 + t) ^ 2) with he
  set s : ℝ := q * t / (1 + t) with hs
  have hs0 : 0 < s := by positivity
  have hqs : q - s = q / (1 + t) := by rw [hs]; field_simp; ring
  have hsq : s < q := by
    have : 0 < q - s := by rw [hqs]; positivity
    linarith
  have hexp1 : s ^ 2 / (2 * t ^ 2) = e := by rw [hs, he]; field_simp
  have hexp2 : (q - s) ^ 2 / 2 = e := by rw [hqs, he]; field_simp
  set K : ℝ := 2 + 2 * Real.exp ((q / (1 + t)) ^ 2 * Real.log (1 + R)) with hK
  have hK0 : 0 ≤ K := by positivity
  -- one-point bound at a lattice point in the disc
  have hone : ∀ w : ℂ, ‖w‖ ≤ R * rbar →
      P {ω | ∃ r ∈ Icc (κ * rbar) (ε * rbar), q * -Real.log ε ≤ |hcirc ω r w - hcirc ω rbar 0|} ≤
        ENNReal.ofReal (K * ε ^ e) := by
    intro w hw
    have h := hh.measure_exists_circle_sub_start_ge_le hε0 hε1 hr hR hν hs0 hsq hw
    rw [hexp1, hexp2, hqs] at h
    refine h.trans (le_of_eq (congrArg ENNReal.ofReal ?_))
    rw [hK]; ring
  -- the index set
  set X : ℝ := 4 * R / κ with hX
  have hX0 : 0 ≤ X := by positivity
  set S : Finset (ℤ × ℤ) := (Finset.Icc (-⌊X⌋) ⌊X⌋) ×ˢ (Finset.Icc (-⌊X⌋) ⌊X⌋) with hS
  set S' : Finset (ℤ × ℤ) :=
    S.filter (fun p => ‖latticePoint δ p.1 p.2‖ ≤ R * rbar) with hS'
  have hcover : {ω | ∃ m n : ℤ, ‖latticePoint δ m n‖ ≤ R * rbar ∧
        ∃ r ∈ Icc (κ * rbar) (ε * rbar),
          q * -Real.log ε ≤ |hcirc ω r (latticePoint δ m n) - hcirc ω rbar 0|} ⊆
      ⋃ p ∈ S', {ω | ∃ r ∈ Icc (κ * rbar) (ε * rbar),
          q * -Real.log ε ≤ |hcirc ω r (latticePoint δ p.1 p.2) - hcirc ω rbar 0|} := by
    rintro ω ⟨m, n, hmn, hω⟩
    have hdiv : R * rbar / δ = X := by
      rw [hX, hδ]; field_simp
    obtain ⟨hm, hn⟩ := abs_le_div_of_norm_latticePoint_le hδ0 hmn
    rw [hdiv] at hm hn
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    refine ⟨(m, n), ?_, hω⟩
    rw [hS', Finset.mem_filter, hS, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hmn⟩
    · have : (-(m : ℝ)) ≤ X := (neg_le_abs _).trans hm
      have : -m ≤ ⌊X⌋ := Int.le_floor.2 (by exact_mod_cast this)
      omega
    · exact Int.le_floor.2 (by exact_mod_cast (le_abs_self _).trans hm)
    · have : (-(n : ℝ)) ≤ X := (neg_le_abs _).trans hn
      have : -n ≤ ⌊X⌋ := Int.le_floor.2 (by exact_mod_cast this)
      omega
    · exact Int.le_floor.2 (by exact_mod_cast (le_abs_self _).trans hn)
  have hunion : P (⋃ p ∈ S', {ω | ∃ r ∈ Icc (κ * rbar) (ε * rbar),
          q * -Real.log ε ≤ |hcirc ω r (latticePoint δ p.1 p.2) - hcirc ω rbar 0|}) ≤
      S'.card • ENNReal.ofReal (K * ε ^ e) := by
    refine (measure_biUnion_finset_le S' _).trans (Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_)
    exact hone _ (Finset.mem_filter.1 hp).2
  have hcard : (S'.card : ℝ) ≤ (8 * R + 1) ^ 2 / κ ^ 2 := by
    have h1 : (S'.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _
    have h2 := card_box_le hX0
    have h3 : 2 * X + 1 ≤ (8 * R + 1) / κ := by
      rw [hX]
      have : 1 ≤ 1 / κ := by rw [le_div_iff₀ hκ0]; linarith
      calc 2 * (4 * R / κ) + 1 ≤ 2 * (4 * R / κ) + 1 / κ := by linarith
        _ = (8 * R + 1) / κ := by field_simp; ring
    have h4 : (2 * X + 1) ^ 2 ≤ ((8 * R + 1) / κ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h3 2
    rw [div_pow] at h4
    exact h1.trans (h2.trans h4)
  have h2e : ε ^ (2 + 2 * t ^ 2) = κ ^ 2 := by
    rw [hκ, ← Real.rpow_natCast (ε ^ (1 + t ^ 2)) 2, ← Real.rpow_mul hε0.le]
    congr 1
    push_cast; ring
  have hpow : ε ^ (e - (2 + 2 * t ^ 2)) = ε ^ e / κ ^ 2 := by
    rw [Real.rpow_sub hε0, h2e]
  refine (measure_mono hcover).trans (hunion.trans ?_)
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (S'.card : ℝ) * (K * ε ^ e) ≤ ((8 * R + 1) ^ 2 / κ ^ 2) * (K * ε ^ e) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (8 * R + 1) ^ 2 * K * ε ^ (e - (2 + 2 * t ^ 2)) := by rw [hpow]; ring

end IsWholePlaneGFF

end LatticeProb.Gauss
