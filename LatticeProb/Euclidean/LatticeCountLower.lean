import LatticeProb.Euclidean.Lattice

/-!
# Lower counts in physical lattices

Bounded sets have finitely many integer indices whose physical image belongs to the set.
A nonempty open set contains a coordinate box, giving a positive lower bound for the count
multiplied by the physical cell volume. Coordinate boxes serve only topology and counting.
-/

namespace LatticeProb.Euclidean.Lattice

noncomputable section

/-- Physical coordinate differences bounded by `R` place indices in a translated integer box. -/
lemma physical_lattice_subset_box {d : ℕ} {ε R : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (q₀ : Site d)
    (hR : ∀ q ∈ {q : Site d | physical ε q ∈ U}, ∀ i, |ε * ((q i : ℝ) - q₀ i)| ≤ R) :
    {q : Site d | physical ε q ∈ U} ⊆ (Fintype.piFinset (fun i =>
      Finset.Icc (q₀ i - ⌈R / ε⌉) (q₀ i + ⌈R / ε⌉)) : Set (Site d)) := by
  intro q hq
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  have hi := hR q hq i
  rw [abs_mul, abs_of_pos hε] at hi
  have hb : |(q i : ℝ) - q₀ i| ≤ (⌈R / ε⌉ : ℝ) :=
    ((le_div_iff₀ hε).mpr (by simpa only [mul_comm] using hi)).trans (Int.le_ceil _)
  have hb' : |q i - q₀ i| ≤ ⌈R / ε⌉ := by
    exact_mod_cast hb
  rw [Finset.mem_Icc]
  have := abs_le.mp hb'
  omega

/-- A bounded set has finitely many indices at every strictly positive lattice spacing. -/
theorem physical_lattice_finite {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) :
    {q : Site d | physical ε q ∈ U}.Finite := by
  obtain ⟨R, hR⟩ := hU.exists_norm_le
  apply (Finset.finite_toSet (Fintype.piFinset (fun _ : Fin d =>
    Finset.Icc (-⌈R / ε⌉) ⌈R / ε⌉))).subset
  have hcoords : ∀ q ∈ {q : Site d | physical ε q ∈ U}, ∀ i : Fin d,
      |ε * ((q i : ℝ) - (0 : Site d) i)| ≤ R := by
    intro q hq i
    have hi := norm_le_pi_norm (physical ε q) i
    have hr := hR (physical ε q) hq
    simpa only [Pi.zero_apply, Int.cast_zero, sub_zero, physical, Real.norm_eq_abs]
      using hi.trans hr
  simpa only [Pi.zero_apply, zero_sub, zero_add] using
    physical_lattice_subset_box hε (0 : Site d) hcoords

/-- A nonempty bounded open set contains at least a fixed multiple of `ε⁻ᵈ` lattice sites. -/
theorem exists_physical_lattice_count_lower {d : ℕ} {U : Set (Fin d → ℝ)}
    (hUo : IsOpen U) (hUne : U.Nonempty) (hU : Bornology.IsBounded U) :
    ∃ c > (0 : ℝ), ∃ ε₀ > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      c ≤ ε ^ d * (({q : Site d | physical ε q ∈ U}).ncard : ℝ) := by
  classical
  obtain ⟨x, hx⟩ := hUne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUo x hx
  refine ⟨(r / 2) ^ d, pow_pos (half_pos hr) _, r / 2, half_pos hr, ?_⟩
  intro ε hε hsmall
  let lower : Fin d → ℤ := fun i => ⌈(x i - r / 2) / ε⌉
  let upper : Fin d → ℤ := fun i => ⌊(x i + r / 2) / ε⌋
  let s := Fintype.piFinset (fun i => Finset.Icc (lower i) (upper i))
  have hsub : (s : Set (Site d)) ⊆ {q : Site d | physical ε q ∈ U} := by
    intro q hq
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hr]
    intro i
    have hi := Fintype.mem_piFinset.mp hq i
    have hl : x i - r / 2 ≤ ε * (q i : ℝ) := by
      have hh : (x i - r / 2) / ε ≤ (q i : ℝ) :=
        (Int.le_ceil _).trans (by exact_mod_cast (Finset.mem_Icc.mp hi).1)
      exact (div_le_iff₀ hε).mp hh |>.trans_eq (mul_comm _ _)
    have hu : ε * (q i : ℝ) ≤ x i + r / 2 := by
      have hqi : (q i : ℝ) ≤ (upper i : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hi).2
      have hh : (q i : ℝ) ≤ (x i + r / 2) / ε := hqi.trans (Int.floor_le _)
      exact (le_div_iff₀ hε).mp hh |>.trans_eq' (mul_comm _ _)
    rw [Real.dist_eq, physical, abs_lt]
    constructor <;> linarith
  have hcard (i : Fin d) : r / (2 * ε) ≤
      ((Finset.Icc (lower i) (upper i)).card : ℝ) := by
    have hlo := Int.ceil_lt_add_one ((x i - r / 2) / ε)
    have hup := Int.lt_floor_add_one ((x i + r / 2) / ε)
    change (lower i : ℝ) < (x i - r / 2) / ε + 1 at hlo
    change (x i + r / 2) / ε < (upper i : ℝ) + 1 at hup
    have hlength : r / ε - 1 < (upper i : ℝ) + 1 - lower i := by
      calc
        r / ε - 1 = ((x i + r / 2) / ε) - ((x i - r / 2) / ε + 1) := by ring
        _ < (upper i : ℝ) + 1 - lower i := by linarith
    have hratio : 2 < r / ε := (lt_div_iff₀ hε).mpr (by linarith)
    have hnonneg : 0 ≤ upper i + 1 - lower i := by
      have h : (0 : ℝ) ≤ (upper i : ℝ) + 1 - lower i := by linarith
      exact_mod_cast h
    rw [Int.card_Icc]
    have hcast : ((upper i + 1 - lower i).toNat : ℝ) =
        (upper i : ℝ) + 1 - lower i := by
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    rw [hcast]
    have hhalf : r / (2 * ε) = (r / ε) / 2 := by ring
    rw [hhalf]
    linarith
  have hcount : (r / (2 * ε)) ^ d ≤ (({q : Site d | physical ε q ∈ U}).ncard : ℝ) := by
    calc
      _ = ∏ _i : Fin d, r / (2 * ε) := by simp only [Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ i : Fin d, ((Finset.Icc (lower i) (upper i)).card : ℝ) :=
        Finset.prod_le_prod (fun _ _ => by positivity) (fun i _ => hcard i)
      _ = (s.card : ℝ) := by
        simp only [s, Fintype.card_piFinset, Nat.cast_prod]
      _ ≤ _ := by
        exact_mod_cast Set.ncard_le_ncard hsub (physical_lattice_finite hε hU)
  have hm := mul_le_mul_of_nonneg_left hcount (pow_nonneg hε.le d)
  have heq : ε ^ d * (r / (2 * ε)) ^ d = (r / 2) ^ d := by
    rw [← mul_pow]
    congr 1
    field_simp
  rwa [heq] at hm


end

end LatticeProb.Euclidean.Lattice
