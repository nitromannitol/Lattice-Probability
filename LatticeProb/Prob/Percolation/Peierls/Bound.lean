import LatticeProb.Prob.Percolation.Peierls.Basic
import LatticeProb.Prob.Percolation.Peierls.Boundary
import LatticeProb.Prob.Percolation.Peierls.ClosedAnimals
import LatticeProb.Prob.Percolation.Peierls.CenterBox

/-!
# Peierls estimate for planar site percolation

The exterior boundary of a finite open cluster is a nearby closed star-connected set.
The closed-animal event and its union estimate are adapted from Exploding-Sandpiles,
`Exploding/Support/ExtMHPeierls.lean` (Apache-2.0).
-/

namespace LatticeProb.Percolation.Peierls

open LatticeProb MeasureTheory
open scoped ENNReal

/-- A finite open cluster containing the origin has a closed star-connected exterior boundary
whose sites lie in the box of radius its cardinality. -/
theorem finite_origin_cluster_closed_boundary {S : Set (Site 2)} (h0 : 0 ∈ S)
    (hfinite : (componentIn S 0).Finite) :
    ∃ D : Set (Site 2), D.Finite ∧ D.Nonempty ∧ D ⊆ Sᶜ ∧ xmh_SConn D ∧
      ∀ z ∈ D, ∀ i : Fin 2, |z i| ≤ (D.ncard : ℤ) := by
  obtain ⟨p, _, hfin, hne, hclosed, hconn, hspan⟩ :=
    Boundary.finite_cluster_exterior_boundary h0 hfinite
  let A := componentIn S 0
  let B := componentIn Aᶜ p
  let D : Set (Site 2) := {z | z ∈ B ∧ ∃ c ∈ A, (lattice 2).Adj c z}
  have h0A : (0 : Site 2) ∈ A := ⟨h0, h0, SimpleGraph.Reachable.refl _⟩
  refine ⟨D, hfin, hne, hclosed, hconn, ?_⟩
  intro z hz i
  obtain ⟨_, a, ha, hadj⟩ := hz
  have hpos := hspan i 0 h0A a ha
  have hneg := hspan i a ha 0 h0A
  have hnear := abs_le.mp (Boundary.xmh3_near_of_adj hadj i)
  simp only [Pi.zero_apply, sub_zero, zero_sub] at hpos hneg
  change a i + 3 ≤ (D.ncard : ℤ) at hpos
  change -a i + 3 ≤ (D.ncard : ℤ) at hneg
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- A closed star-connected animal close to the origin. -/
def originBad (ω : Site 2 → Bool) : Prop :=
  ∃ j : ℕ, ∃ z ∈ xmh4_centFinset 2 (j + 1), ∃ F : Finset (Site 2),
    z ∈ F ∧ F.card = j + 1 ∧ xmh_SConn (F : Set (Site 2)) ∧
      ∀ x ∈ F, ω x = false

/-- If the origin is open and its cluster is finite, a nearby closed animal exists. -/
theorem originBad_of_finite {ω : Site 2 → Bool} (h0 : ω 0 = true)
    (hfinite : (componentIn {z | ω z = true} 0).Finite) : originBad ω := by
  classical
  obtain ⟨D, hfin, hne, hclosed, hconn, hnear⟩ :=
    finite_origin_cluster_closed_boundary h0 hfinite
  obtain ⟨z, hz⟩ := hne
  have hpos : 0 < D.ncard := (Set.ncard_pos hfin).2 ⟨z, hz⟩
  have hcard : D.ncard - 1 + 1 = D.ncard := by omega
  refine ⟨D.ncard - 1, z, ?_, hfin.toFinset, ?_, ?_, ?_, ?_⟩
  · rw [xmh4_mem_centFinset]
    simpa [xmh4_cent, hcard] using hnear z hz
  · exact hfin.mem_toFinset.mpr hz
  · simpa [hcard] using (Set.ncard_eq_toFinset_card D hfin).symm
  · simpa only [hfin.coe_toFinset] using hconn
  · intro x hx
    have hnot := hclosed (hfin.mem_toFinset.mp hx)
    cases h : ω x <;> simp_all

/-- The closed-animal event is bounded by the sum of the finite-family estimates. -/
theorem originBad_prob {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    sitePercolation 2 q {ω | originBad ω} ≤
      ∑' j : ℕ, ((xmh4_centFinset 2 (j + 1)).card : ENNReal) *
        ((xmh6_K 2 : ENNReal) ^ (j + 1) * ENNReal.ofReal (1 - q) ^ (j + 1)) := by
  have hset : {ω : Site 2 → Bool | originBad ω} = ⋃ j : ℕ, {ω : Site 2 → Bool |
      ∃ z ∈ xmh4_centFinset 2 (j + 1), ∃ F : Finset (Site 2),
        z ∈ F ∧ F.card = j + 1 ∧ xmh_SConn (F : Set (Site 2)) ∧
          ∀ x ∈ F, ω x = false} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, originBad]
  rw [hset]
  refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => ?_)
  exact xmh5_finset_closed_prob (xmh6_K 2) (xmh6_K_spec 2) h0 h1 _ _

private theorem two_mul_add_one_le (m : ℕ) : 2 * m + 1 ≤ 3 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [pow_succ]; omega

private theorem center_card_le (m : ℕ) :
    ((xmh4_centFinset 2 m).card : ENNReal) ≤ (9 : ENNReal) ^ m := by
  have h : (2 * m + 1) ^ 2 ≤ 9 ^ m := by
    calc
      (2 * m + 1) ^ 2 ≤ (3 ^ m) ^ 2 := Nat.pow_le_pow_left (two_mul_add_one_le m) _
      _ = 9 ^ m := by rw [← pow_mul, Nat.mul_comm m 2, pow_mul]; norm_num
  rw [xmh4_centFinset_card]
  exact_mod_cast h

/-- A uniform bound on the closed-animal event at high density. -/
theorem originBad_prob_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hsmall : 9 * (xmh6_K 2 : ENNReal) * ENNReal.ofReal (1 - q) ≤ 1 / 40) :
    sitePercolation 2 q {ω | originBad ω} ≤ 1 / 20 := by
  let r : ENNReal := 9 * (xmh6_K 2 : ENNReal) * ENNReal.ofReal (1 - q)
  have hr : r ≤ 1 / 40 := hsmall
  have hrhalf : r ≤ 1 / 2 := hr.trans (by norm_num)
  refine (originBad_prob h0 h1).trans ?_
  calc
    (∑' j : ℕ, ((xmh4_centFinset 2 (j + 1)).card : ENNReal) *
        ((xmh6_K 2 : ENNReal) ^ (j + 1) * ENNReal.ofReal (1 - q) ^ (j + 1)))
        ≤ ∑' j : ℕ, r * (1 / 2 : ENNReal) ^ j := by
          apply ENNReal.tsum_le_tsum
          intro j
          calc
            ((xmh4_centFinset 2 (j + 1)).card : ENNReal) *
                ((xmh6_K 2 : ENNReal) ^ (j + 1) * ENNReal.ofReal (1 - q) ^ (j + 1))
                ≤ (9 : ENNReal) ^ (j + 1) *
                    ((xmh6_K 2 : ENNReal) ^ (j + 1) * ENNReal.ofReal (1 - q) ^ (j + 1)) := by
                  gcongr
                  exact center_card_le _
            _ = r ^ (j + 1) := by simp only [r, mul_pow]; ring
            _ = r * r ^ j := by rw [pow_succ']
            _ ≤ r * (1 / 2 : ENNReal) ^ j := by gcongr
    _ = r * 2 := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]; norm_num
    _ ≤ 1 / 20 := by calc
      r * 2 ≤ (1 / 40 : ENNReal) * 2 := by gcongr
      _ = 1 / 20 := by
        have h : ENNReal.ofReal ((1 / 40 : ℝ) * 2) = ENNReal.ofReal (1 / 20 : ℝ) := by
          congr 1
          norm_num
        simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 40),
          ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 40),
          ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 20),
          ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using h

end LatticeProb.Percolation.Peierls

namespace LatticeProb.Percolation

open LatticeProb MeasureTheory Peierls
open scoped ENNReal

private theorem origin_open_prob (p : NNReal) (hp : p ≤ 1) :
    sitePercolationLaw p hp {ω | ω 0 = true} = ENNReal.ofReal p := by
  have hpre : (fun f : Site 2 → Bool => f 0) ⁻¹' ({true} : Set Bool) =
      {ω : Site 2 → Bool | ω 0 = true} := by ext ω; simp
  rw [← hpre, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton true)]
  simp only [sitePercolationLaw]
  rw [Measure.infinitePi_map_eval, ← bitLaw_eq_bernoulli]
  exact bitLaw_true p

/-- For all sufficiently large densities, the open component of the origin is infinite
with positive probability. -/
theorem peierls_origin_infinite_pos :
    ∃ p₀ : NNReal, p₀ < 1 ∧ ∀ p : NNReal, p₀ ≤ p → ∀ hp : p ≤ 1,
      0 < sitePercolationLaw p hp {ω | (componentIn {z | ω z = true} 0).Infinite} := by
  let k : ℝ := xmh6_K 2
  let δ : ℝ := 1 / (360 * (k + 1))
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hden : 0 < 360 * (k + 1) := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ 1 / 360 := by
    dsimp [δ]
    rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 360)]
    nlinarith
  have hp0nn : 0 ≤ 1 - δ := by linarith
  let p₀ : NNReal := ⟨1 - δ, hp0nn⟩
  refine ⟨p₀, ?_, fun p hp0 hp => ?_⟩
  · apply NNReal.coe_lt_coe.mp
    change 1 - δ < 1
    linarith
  have hp0' : 1 - δ ≤ (p : ℝ) := by exact_mod_cast hp0
  have hp1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hpnonneg : 0 ≤ (p : ℝ) := p.coe_nonneg
  have hreal : 9 * k * (1 - (p : ℝ)) ≤ 1 / 40 := by
    calc
      9 * k * (1 - (p : ℝ)) ≤ 9 * k * δ := by
        gcongr
        linarith
      _ ≤ 1 / 40 := by
        dsimp [δ]
        rw [mul_one_div, div_le_iff₀ hden]
        nlinarith
  have hsmall : 9 * (xmh6_K 2 : ENNReal) * ENNReal.ofReal (1 - (p : ℝ)) ≤ 1 / 40 := by
    have h := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast,
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 40),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at h
    simpa only [k] using h
  have hbad : sitePercolationLaw p hp {ω | originBad ω} ≤ 1 / 20 := by
    rw [← sitePercolation_eq_sitePercolationLaw p hp]
    exact originBad_prob_le hpnonneg hp1 hsmall
  have hpgt : (1 / 20 : ENNReal) < ENNReal.ofReal (p : ℝ) := by
    have h : (1 / 20 : ℝ) < (p : ℝ) := by linarith
    have h' := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 20)).2 h
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 20),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using h'
  have hsub : {ω : Site 2 → Bool | ω 0 = true} ⊆
      {ω | (componentIn {z | ω z = true} 0).Infinite} ∪ {ω | originBad ω} := by
    intro ω hω
    by_cases hf : (componentIn {z | ω z = true} 0).Finite
    · exact Or.inr (originBad_of_finite hω hf)
    · exact Or.inl hf
  have hbound : sitePercolationLaw p hp {ω | ω 0 = true} ≤
      sitePercolationLaw p hp {ω | (componentIn {z | ω z = true} 0).Infinite} +
        sitePercolationLaw p hp {ω | originBad ω} :=
    (measure_mono hsub).trans (measure_union_le _ _)
  rw [origin_open_prob p hp] at hbound
  by_contra hnot
  have hzero : sitePercolationLaw p hp
      {ω | (componentIn {z | ω z = true} 0).Infinite} = 0 :=
    le_antisymm (le_of_not_gt hnot) bot_le
  rw [hzero, zero_add] at hbound
  exact (not_le_of_gt hpgt) (hbound.trans hbad)

end LatticeProb.Percolation
