/-
The resistance packing bound on `ℤ^d`: for `d ≥ 2`, and any injective enumeration
`x 0, …, x (M-1)` of `M` sites, the effective resistances from each `x i` to the complement
of `{x 0, …, x i}` sum to at most `C M`, with `C` depending only on `d`.

`pref x k` is the set of the first `k` sites of the enumeration.  `packing_count` bounds the
number of steps whose escape radius `esc` from the next prefix is at least `r`: the boxes
`qbox` of side about `r / (2d)` around those sites are disjoint and lie in the image of `x`.
`resistance_packing` combines this with the flow bound `Reff ≤ 2 esc` of
`LatticeProb.Walk.Energy` (`reff_le_nrm1`), writes the sum of escape radii as a sum of level
counts, and sums the resulting bound `M (2d)^d / (r+1)^2` on the `r`-th level against the
telescoping series `∑ 1/((r+1)(r+2)) ≤ 1`.  The series converges because `d ≥ 2`.

Moved from the ORRW formalization (`nitromannitol/ORRW-Lower-Bound`,
`ORRW/Support/InsertionSum.lean` and `ORRW/Support/Thomson.lean`), where it proves the
resistance packing lemma `lem:packing` of Bou-Rabee and Peres on once-reinforced random walk.
-/
import Mathlib
import LatticeProb.Walk.Energy

open Finset

namespace LatticeProb

variable {d : ℕ}

/-! ## Prefixes of an insertion order -/

/-- The prefix of length `k` of an insertion order `x : Fin M → Site d`: the set of the sites
`x j` with `j < k`.  It is all of the image of `x` once `k ≥ M`. -/
def pref {M : ℕ} (x : Fin M → Site d) (k : ℕ) : Finset (Site d) :=
  (Finset.univ.filter (fun j : Fin M => (j : ℕ) < k)).image x

/-- The empty prefix: no site is inserted before step `0`. -/
lemma pref_zero {M : ℕ} (x : Fin M → Site d) : pref x 0 = ∅ := by
  simp [pref]

/-- The sites inserted strictly before step `i` form the prefix of length `i`. -/
lemma pref_Iio {M : ℕ} (x : Fin M → Site d) (i : Fin M) :
    (Finset.Iio i).image x = pref x (i : ℕ) := by
  congr 1
  ext j
  simp only [Finset.mem_Iio, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Fin.lt_def

/-- Inserting the site of step `i` into the prefix of length `i` gives the prefix of length
`i + 1`. -/
lemma pref_succ {M : ℕ} (x : Fin M → Site d) (i : Fin M) :
    insert (x i) (pref x (i : ℕ)) = pref x ((i : ℕ) + 1) := by
  ext y
  simp only [pref, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨j, by omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    rcases Nat.lt_or_ge (j : ℕ) (i : ℕ) with hji | hji
    · exact Or.inr ⟨j, hji, rfl⟩
    · left
      congr 1
      exact Fin.ext (by omega)

/-- The prefixes of an insertion order increase with their length. -/
lemma pref_mono {M : ℕ} (x : Fin M → Site d) {k l : ℕ} (h : k ≤ l) :
    pref x k ⊆ pref x l := by
  intro y hy
  simp only [pref, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  obtain ⟨j, hj, rfl⟩ := hy
  exact ⟨j, by omega, rfl⟩

/-- For an injective insertion order, the site of step `i` is not among the sites inserted
before it. -/
lemma pref_notMem {M : ℕ} (x : Fin M → Site d) (hinj : Function.Injective x) (i : Fin M) :
    x i ∉ pref x (i : ℕ) := by
  simp only [pref, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨j, hj, hxj⟩
  have : j = i := hinj hxj
  omega

/-- For an injective insertion order of length `M`, the full prefix has `M` sites. -/
lemma pref_card {M : ℕ} (x : Fin M → Site d) (hinj : Function.Injective x) :
    (pref x M).card = M := by
  have huniv : (Finset.univ.filter (fun j : Fin M => (j : ℕ) < M)) = Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact j.2
  rw [pref, huniv, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-! ## The packing count -/

/-- The packing count.  If the escape radius of `x i` from the prefix of length `i + 1` is at
least `r ≥ 1`, then the box `qbox (x i) q` with `q = (r - 1) / (2d)` lies in the image of
`x`, and these boxes are pairwise disjoint.  Hence the number of such steps `i`, times the
volume `(q + 1)^d` of one box, is at most `M`. -/
lemma packing_count {M : ℕ} (x : Fin M → Site d) (hinj : Function.Injective x)
    (r : ℕ) (hr : 1 ≤ r) :
    (Finset.univ.filter (fun i : Fin M => r ≤ esc (pref x ((i:ℕ)+1)) (x i))).card
      * (((r-1)/(2*d)) + 1)^d ≤ M := by
  classical
  set q : ℕ := (r-1)/(2*d) with hq
  set S : Finset (Fin M) :=
    Finset.univ.filter (fun i : Fin M => r ≤ esc (pref x ((i:ℕ)+1)) (x i)) with hS
  have hqd : q * (2*d) = d * q + d * q := by ring
  have hdq : d * q + d * q ≤ r - 1 := by
    rw [← hqd, hq]
    exact Nat.div_mul_le_self _ _
  have hdqr : d * q < r := by omega
  have hsep : ∀ i ∈ S, ∀ j : Fin M, (i:ℕ) < (j:ℕ) → r ≤ nrm1 (x j - x i) := by
    intro i hi j hij
    have hnot : x j ∉ pref x ((i:ℕ)+1) := by
      simp only [pref, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨l, hl, hxl⟩
      have hlj : l = j := hinj hxl
      rw [hlj] at hl
      omega
    have h1 := esc_le (x := x i) hnot
    have h2 := (Finset.mem_filter.mp hi).2
    omega
  have hsubs : ∀ i ∈ S, qbox (x i) q ⊆ pref x M := by
    intro i hi z hz
    have hle : nrm1 (z - x i) ≤ d * q := nrm1_le_of_mem_qbox hz
    have h2 := (Finset.mem_filter.mp hi).2
    have hmem : z ∈ pref x ((i:ℕ)+1) := mem_of_lt_esc (x := x i) (by omega)
    exact pref_mono x (by omega) hmem
  have hdisj : (S : Set (Fin M)).PairwiseDisjoint (fun i => qbox (x i) q) := by
    have hkey : ∀ i ∈ S, ∀ j : Fin M, (i:ℕ) < (j:ℕ) →
        Disjoint (qbox (x i) q) (qbox (x j) q) := by
      intro i hi j hij
      rw [Finset.disjoint_left]
      intro w hwi hwj
      have h1 : nrm1 (w - x i) ≤ d * q := nrm1_le_of_mem_qbox hwi
      have h2 : nrm1 (x j - w) ≤ d * q := by
        rw [nrm1_sub_comm]
        exact nrm1_le_of_mem_qbox hwj
      have h3 : nrm1 (x j - x i) ≤ nrm1 (x j - w) + nrm1 (w - x i) := by
        have hsplit : x j - x i = (x j - w) + (w - x i) := by abel
        rw [hsplit]
        exact nrm1_add_le _ _
      have h4 := hsep i hi j hij
      omega
    intro i hi j hj hne
    have hne' : (i:ℕ) ≠ (j:ℕ) := fun hc => hne (Fin.ext hc)
    rcases Nat.lt_or_ge (i:ℕ) (j:ℕ) with h | h
    · exact hkey i (Finset.mem_coe.mp hi) j h
    · exact (hkey j (Finset.mem_coe.mp hj) i (by omega)).symm
  have hcardU : (S.biUnion (fun i => qbox (x i) q)).card = S.card * (q+1)^d := by
    rw [Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl (fun i _ => card_qbox (x i) q), Finset.sum_const, smul_eq_mul]
  have hsubU : S.biUnion (fun i => qbox (x i) q) ⊆ pref x M := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp hz
    exact hsubs i hi hzi
  have := Finset.card_le_card hsubU
  rw [hcardU, pref_card x hinj] at this
  exact this

/-! ## The resistance packing bound -/

/-- The resistance packing bound.  For `d ≥ 2` there is a constant `C > 0`, depending only on
`d`, such that for every injective enumeration `x : Fin M → Site d` of `M ≥ 1` sites, the sum
over `i` of the effective resistance from `x i` to the complement of the set
`{x 0, …, x i}` is at most `C M`.  In the notation of `LatticeProb.Reff`, whose first
argument is the set of strictly earlier sites, this is
`∑ i, Reff ((Iio i).image x) (x i) ≤ C * M`. -/
theorem resistance_packing (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → ∀ x : Fin M → Site d, Function.Injective x →
      ∑ i : Fin M, Reff ((Finset.Iio i).image x) (x i) ≤ C * (M : ℝ) := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  refine ⟨2 * (1 + ((2*(d:ℝ))^d)), by positivity, ?_⟩
  intro M hM x hinj
  set ρ : Fin M → ℕ := fun i => esc (pref x ((i:ℕ)+1)) (x i) with hρ
  -- the flow bound `Reff ≤ 2 ‖p - x‖₁` at a nearest point `p` outside the next prefix
  have hReff : ∀ i : Fin M,
      Reff ((Finset.Iio i).image x) (x i) ≤ 2 * (ρ i : ℝ) := by
    intro i
    rw [pref_Iio]
    obtain ⟨p, hp, hpe⟩ := esc_spec hd0 (pref x ((i:ℕ)+1)) (x i)
    have hp' : p ∉ insert (x i) (pref x (i:ℕ)) := by rw [pref_succ x i]; exact hp
    have hb := reff_le_nrm1 hd0 (pref x (i:ℕ)) (x i) p hp'
    rw [hpe] at hb
    exact hb
  -- ρ i ≤ M
  have hρle : ∀ i : Fin M, ρ i ≤ M := by
    intro i
    have h1 : esc (pref x ((i:ℕ)+1)) (x i) ≤ (pref x ((i:ℕ)+1)).card :=
      esc_le_card hd0 _ _
    have h2 : (pref x ((i:ℕ)+1)).card ≤ (pref x M).card :=
      Finset.card_le_card (pref_mono x (by omega))
    rw [pref_card x hinj] at h2
    exact le_trans h1 h2
  set Nn : ℕ → ℕ :=
    fun r => (Finset.univ.filter (fun i : Fin M => r < ρ i)).card with hNdef
  -- layer cake
  have hlayer : ∑ i : Fin M, ρ i = ∑ r ∈ Finset.range M, Nn r := by
    have hrow : ∀ i : Fin M, ρ i = ∑ r ∈ Finset.range M, (if r < ρ i then 1 else 0) := by
      intro i
      rw [← Finset.sum_filter]
      have hf : (Finset.range M).filter (fun r => r < ρ i) = Finset.range (ρ i) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_range]
        have := hρle i
        omega
      rw [hf, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hNdef]
    simp only
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  -- the packing estimate
  have hNbound : ∀ r : ℕ, Nn r * (r+1)^2 ≤ M * (2*d)^d := by
    intro r
    have hpc := packing_count x hinj (r+1) (by omega)
    have hfe : (Finset.univ.filter (fun i : Fin M => r + 1 ≤ esc (pref x ((i:ℕ)+1)) (x i)))
        = (Finset.univ.filter (fun i : Fin M => r < ρ i)) := by
      apply Finset.filter_congr
      intro i _
      simp only [hρ]
      constructor <;> intro h <;> omega
    rw [hfe] at hpc
    have hq : r < (r / (2*d) + 1) * (2*d) := by
      have h1 : (2*d) * (r / (2*d)) + r % (2*d) = r := Nat.div_add_mod r (2*d)
      have h2 : r % (2*d) < 2*d := Nat.mod_lt _ (by omega)
      have h3 : (r / (2*d) + 1) * (2*d) = (2*d) * (r / (2*d)) + (2*d) := by ring
      omega
    have hpow : (r+1)^d ≤ (r / (2*d) + 1)^d * (2*d)^d := by
      rw [← Nat.mul_pow]
      exact Nat.pow_le_pow_left (by omega) d
    have hsq : (r+1)^2 ≤ (r+1)^d := Nat.pow_le_pow_right (by omega) hd
    calc Nn r * (r+1)^2 ≤ Nn r * ((r / (2*d) + 1)^d * (2*d)^d) := by
          exact Nat.mul_le_mul_left _ (le_trans hsq hpow)
      _ = (Nn r * ((r+1-1) / (2*d) + 1)^d) * (2*d)^d := by
          simp only [Nat.add_sub_cancel]
          ring
      _ ≤ M * (2*d)^d := Nat.mul_le_mul_right _ hpc
  -- sum the layers in ℝ
  have hsum : (∑ r ∈ Finset.range M, (Nn r : ℝ)) ≤ (1 + (2*(d:ℝ))^d) * M := by
    obtain ⟨M', rfl⟩ : ∃ M' : ℕ, M = M' + 1 := ⟨M - 1, by omega⟩
    rw [Finset.sum_range_succ' (fun r => (Nn r : ℝ)) M']
    have hN0 : (Nn 0 : ℝ) ≤ ((M' + 1 : ℕ) : ℝ) := by
      have : Nn 0 ≤ M' + 1 := by
        rw [hNdef]
        simpa using Finset.card_filter_le (Finset.univ : Finset (Fin (M'+1))) _
      exact_mod_cast this
    have hstep : ∀ r ∈ Finset.range M', (Nn (r+1) : ℝ)
        ≤ (((M':ℝ)+1) * (2*(d:ℝ))^d) * (1/((r:ℝ)+1) - 1/((r:ℝ)+2)) := by
      intro r _
      have hb := hNbound (r+1)
      have hbR : (Nn (r+1) : ℝ) * ((r:ℝ)+2)^2 ≤ ((M':ℝ)+1) * (2*(d:ℝ))^d := by
        have : ((Nn (r+1) * (r+1+1)^2 : ℕ) : ℝ) ≤ (((M'+1) * (2*d)^d : ℕ) : ℝ) := by
          exact_mod_cast hb
        push_cast at this
        nlinarith [this]
      have hid : (1/((r:ℝ)+1) - 1/((r:ℝ)+2)) = 1/(((r:ℝ)+1)*((r:ℝ)+2)) := by
        field_simp
        ring
      have hle : ((r:ℝ)+1)*((r:ℝ)+2) ≤ ((r:ℝ)+2)^2 := by nlinarith [sq_nonneg ((r:ℝ)+1)]
      have hNnn : (0:ℝ) ≤ (Nn (r+1) : ℝ) := Nat.cast_nonneg _
      rw [hid, mul_one_div, le_div_iff₀ (by positivity)]
      nlinarith [hbR, hle, hNnn]
    have htele : ∑ r ∈ Finset.range M', (1/((r:ℝ)+1) - 1/((r:ℝ)+2)) ≤ 1 := by
      have := Finset.sum_range_sub' (fun r : ℕ => 1/((r:ℝ)+1)) M'
      have hpos : (0:ℝ) < 1/((M':ℝ)+1) := by positivity
      have heq : ∑ r ∈ Finset.range M', (1/((r:ℝ)+1) - 1/(((r:ℝ)+1)+1))
          = 1/((0:ℝ)+1) - 1/((M':ℝ)+1) := by
        exact_mod_cast this
      have hcast : ∑ r ∈ Finset.range M', (1/((r:ℝ)+1) - 1/((r:ℝ)+2))
          = ∑ r ∈ Finset.range M', (1/((r:ℝ)+1) - 1/(((r:ℝ)+1)+1)) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        norm_num
        ring
      rw [hcast, heq]
      norm_num
      positivity
    have hstepsum : ∑ r ∈ Finset.range M', (Nn (r+1) : ℝ)
        ≤ (((M':ℝ)+1) * (2*(d:ℝ))^d) * ∑ r ∈ Finset.range M', (1/((r:ℝ)+1) - 1/((r:ℝ)+2)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hstep
    have hfac : (0:ℝ) ≤ ((M':ℝ)+1) * (2*(d:ℝ))^d := by positivity
    have : (((M':ℝ)+1) * (2*(d:ℝ))^d)
        * ∑ r ∈ Finset.range M', (1/((r:ℝ)+1) - 1/((r:ℝ)+2))
        ≤ ((M':ℝ)+1) * (2*(d:ℝ))^d := by
      nlinarith [htele, hfac]
    push_cast at hN0 ⊢
    linarith [hstepsum, this, hN0]
  -- assemble
  calc ∑ i : Fin M, Reff ((Finset.Iio i).image x) (x i)
      ≤ ∑ i : Fin M, 2 * (ρ i : ℝ) := Finset.sum_le_sum fun i _ => hReff i
    _ = 2 * ((∑ i : Fin M, ρ i : ℕ) : ℝ) := by
        rw [← Finset.mul_sum]
        norm_cast
    _ = 2 * ((∑ r ∈ Finset.range M, Nn r : ℕ) : ℝ) := by rw [hlayer]
    _ = 2 * ∑ r ∈ Finset.range M, (Nn r : ℝ) := by push_cast; ring
    _ ≤ 2 * ((1 + (2*(d:ℝ))^d) * M) := by linarith [hsum]
    _ = 2 * (1 + (2*(d:ℝ))^d) * (M:ℝ) := by ring

end LatticeProb
