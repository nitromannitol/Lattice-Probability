import LatticeProb.Sandpile.Parallel
import LatticeProb.Walk.SRWPos

/-!
# Bounds for sandpile odometers on boxes

A nonnegative function with bounded Laplacian is bounded near a zero.
A box of sites that have all toppled contains at least one grain per internal edge.
-/

namespace LatticeProb.Sandpile.FLP
open LatticeProb

private theorem neighbor_bound {d : ℕ} (A : ℤ) (w : Site d → ℤ)
    (hw : ∀ x, 0 ≤ w x) (hl : ∀ x, lap w x ≤ A) (x : Site d) (a : Dir d) :
    w (x + dirVec a) ≤ 2 * (d : ℤ) * w x + max A 0 := by
  have hs : ∀ i : Fin d, 0 ≤ w (x + unit i) + w (x - unit i) :=
    fun i => add_nonneg (hw _) (hw _)
  have h := Finset.single_le_sum (f := fun i : Fin d => w (x + unit i) + w (x - unit i))
    (fun i _ => hs i) (Finset.mem_univ a.1)
  have hc : w (x + dirVec a) ≤ w (x + unit a.1) + w (x - unit a.1) := by
    rcases a with ⟨i, b⟩
    cases b <;> simp only [dirVec_eq_unit, dirVec_eq_neg_unit, ← sub_eq_add_neg] <;>
      linarith [hw (x + unit i), hw (x - unit i)]
  have hA : A ≤ max A 0 := le_max_left _ _
  have hlx := hl x
  unfold lap nbrSumZ at hlx
  linarith

private def bound (d : ℕ) (A : ℤ) (n : ℕ) : ℤ :=
  (2 * (d : ℤ) + 1) ^ n * (max A 0 + 1)

private theorem bound_ge (d : ℕ) (A : ℤ) (n : ℕ) : max A 0 + 1 ≤ bound d A n := by
  unfold bound
  have hp : (1 : ℤ) ≤ (2 * (d : ℤ) + 1) ^ n := one_le_pow₀ (by nlinarith [Int.natCast_nonneg d])
  have hA : 0 ≤ max A 0 + 1 := by have := le_max_right A 0; omega
  nlinarith

private theorem bound_step (d : ℕ) (A : ℤ) (n : ℕ) :
    2 * (d : ℤ) * bound d A n + max A 0 ≤ bound d A (n + 1) := by
  have h := bound_ge d A n
  unfold bound at *
  rw [pow_succ]
  nlinarith

/-- A nonnegative function with bounded Laplacian is bounded near any zero. -/
theorem le_of_lap_le_of_eq_zero (d : ℕ) (A : ℤ) (L : ℕ) : ∃ C : ℤ, ∀ w : Site d → ℤ, (∀ x, 0 ≤ w x) →
    (∀ x, lap w x ≤ A) → ∀ y z : Site d, ∑ i, |y i - z i| ≤ (L : ℤ) → w z = 0 → w y ≤ C := by
  refine ⟨bound d A L, ?_⟩
  intro w hw hl y z hy hz
  have hdist : graphNorm (y - z) ≤ L := by
    have hcast : (graphNorm (y - z) : ℤ) = ∑ i, |y i - z i| := by
      simp [graphNorm, Pi.sub_apply]
    exact_mod_cast hcast ▸ hy
  have hmain : ∀ n : ℕ, ∀ v : Site d, graphNorm (v - z) ≤ n → w v ≤ bound d A n := by
    intro n
    induction n with
    | zero =>
      intro v hv
      have hvz : v = z := by
        have : v - z = 0 := graphNorm_eq_zero_iff.mp (by omega)
        exact sub_eq_zero.mp this
      subst v
      rw [hz]
      have := bound_ge d A 0
      have := le_max_right A 0
      omega
    | succ n ih =>
      intro v hv
      by_cases hvz : v = z
      · subst v
        rw [hz]
        have := bound_ge d A (n + 1)
        have := le_max_right A 0
        omega
      · have hne : v - z ≠ 0 := sub_ne_zero.mpr hvz
        obtain ⟨a, ha⟩ := exists_dirVec_graphNorm_eq_sub_one hne
        let u := v + dirVec a
        have hu : graphNorm (u - z) ≤ n := by
          have heq : u - z = (v - z) + dirVec a := by dsimp [u]; abel
          rw [heq, ha]
          have hpos : 0 < graphNorm (v - z) := Nat.pos_of_ne_zero (fun h => hne (graphNorm_eq_zero_iff.mp h))
          omega
        have hback : w v ≤ 2 * (d : ℤ) * w u + max A 0 := by
          have h := neighbor_bound A w hw hl u (a.1, !a.2)
          have heq : u + dirVec (a.1, !a.2) = v := by
            rcases a with ⟨i, b⟩
            cases b <;> simp [u, dirVec_eq_unit, dirVec_eq_neg_unit]
          simpa only [heq] using h
        have hcoeff : 0 ≤ 2 * (d : ℤ) := by positivity
        have := ih u hu
        have hb := bound_step d A n
        nlinarith
  exact hmain L y hdist
private theorem pconf_ge_received {d : ℕ} (s : Site d → ℤ) (T t : ℕ) (x : Site d)
    (hfire : 2 * (d : ℤ) ≤ pconf s t x)
    (hlast : podo s T x = podo s (t + 1) x) :
    (∑ i : Fin d, ((podo s T (x + unit i) - podo s t (x + unit i)) +
      (podo s T (x - unit i) - podo s t (x - unit i)))) ≤ pconf s T x := by
  have hinc : podo s T x = podo s t x + 1 := by
    rw [hlast, podo_succ, ite_eq_left hfire]
  have hsum : (∑ i : Fin d, ((podo s T (x + unit i) - podo s t (x + unit i)) +
      (podo s T (x - unit i) - podo s t (x - unit i)))) =
      nbrSumZ (podo s T) x - nbrSumZ (podo s t) x := by
    simp only [nbrSumZ, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  unfold pconf lap at *
  rw [hinc]
  linarith


private theorem exists_last_topple {d : ℕ} (s : Site d → ℤ) (T : ℕ) (x : Site d)
    (hpos : 0 < podo s T x) :
    ∃ t < T, 2 * (d : ℤ) ≤ pconf s t x ∧ podo s T x = podo s (t + 1) x := by
  classical
  let P : ℕ → Prop := fun t => podo s t x = podo s T x
  have hex : ∃ t, P t := ⟨T, rfl⟩
  have hle : Nat.find hex ≤ T := Nat.find_min' hex rfl
  have hpos' : 0 < Nat.find hex := by
    by_contra h
    have hz : Nat.find hex = 0 := by omega
    have hfound := Nat.find_spec hex
    dsimp [P] at hfound
    rw [hz] at hfound
    simp only [podo_zero] at hfound
    omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos')
  refine ⟨t, by omega, ?_⟩
  have heq : podo s (t + 1) x = podo s T x := by
    have h := Nat.find_spec hex
    dsimp [P] at h
    simpa [ht] using h
  have hne : podo s t x ≠ podo s T x := by
    apply Nat.find_min hex
    omega
  have hs := podo_succ s t x
  constructor
  · by_contra hn
    rw [ite_eq_right hn] at hs
    simp only [add_zero] at hs
    exact hne (hs.symm.trans heq)
  · exact heq.symm

private theorem one_le_received {d : ℕ} (s : Site d → ℤ) (T t t' : ℕ) (y : Site d)
    (htt : t ≤ t') (hfire : 2 * (d : ℤ) ≤ pconf s t' y)
    (hlast : podo s T y = podo s (t' + 1) y) :
    1 ≤ podo s T y - podo s t y := by
  have hmono := podo_mono s htt y
  rw [hlast, podo_succ, ite_eq_left hfire]
  omega


private theorem box_edge_card (d k : ℕ) (x : Site d) (i : Fin d) :
    ({y ∈ Fintype.piFinset (fun j => Finset.Icc (x j - k) (x j + k)) |
      y i < x i + k}).card = 2 * k * (2 * k + 1) ^ (d - 1) := by
  classical
  let S : Fin d → Finset ℤ := fun j => Finset.Icc (x j - k) (x j + k)
  let U := Finset.Ico (x i - (k : ℤ)) (x i + k)
  have hsub : U ⊆ S i := by
    intro z hz
    simp only [U, S, Finset.mem_Ico, Finset.mem_Icc] at *
    omega
  have heq : {y ∈ Fintype.piFinset S | y i < x i + k} =
      Fintype.piFinset (Function.update S i U) := by
    rw [Fintype.piFinset_update_eq_filter_piFinset_mem S i hsub]
    apply Finset.filter_congr
    intro y hy
    simp only [Fintype.mem_piFinset] at hy
    simp only [U, Finset.mem_Ico]
    exact ⟨fun h => ⟨(Finset.mem_Icc.mp (hy i)).1, h⟩, fun h => h.2⟩
  change {y ∈ Fintype.piFinset S | y i < x i + k}.card = _
  rw [heq, Fintype.card_piFinset]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have hU : U.card = 2 * k := by
    simp only [U, Int.card_Ico]
    omega
  have hS : ∀ j, (S j).card = 2 * k + 1 := by
    intro j
    simp only [S, Int.card_Icc]
    omega
  simp only [Function.update_self, hU]
  have hprod : (∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
      (Function.update S i U j).card) = (2 * k + 1) ^ (d - 1) := by
    calc
      _ = ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i, (2 * k + 1) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), hS]
      _ = _ := by simp
  rw [hprod]
  exact Nat.mul_comm _ _


private theorem edges_le_sum {d : ℕ} (B E : Finset (Site d)) (i : Fin d)
    (r : Site d → Site d → ℤ) (hsub : E ⊆ B)
    (hsubplus : E.image (fun y => y + unit i) ⊆ B)
    (hr : ∀ y ∈ B, ∀ z, 0 ≤ r y z)
    (hedge : ∀ y ∈ E, 1 ≤ r y (y + unit i) + r (y + unit i) y) :
    (E.card : ℤ) ≤ ∑ y ∈ B, (r y (y + unit i) + r y (y - unit i)) := by
  classical
  have hinj : Function.Injective (fun y : Site d => y + unit i) := fun a b h => add_right_cancel h
  have hfirst : (∑ y ∈ E, r y (y + unit i)) ≤ ∑ y ∈ B, r y (y + unit i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y hy _ => hr y hy _)
  have hsecond : (∑ y ∈ E, r (y + unit i) y) ≤ ∑ y ∈ B, r y (y - unit i) := by
    have hsum : (∑ y ∈ E, r (y + unit i) y) =
        ∑ y ∈ E.image (fun y => y + unit i), r y (y - unit i) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro y hy
        simp
      · intro a ha b hb hab
        exact hinj hab
    rw [hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubplus (fun y hy _ => hr y hy _)
  have he := Finset.sum_le_sum (fun y hy => hedge y hy)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.sum_add_distrib] at he ⊢
  omega


end LatticeProb.Sandpile.FLP

namespace LatticeProb.Sandpile.FLP
open LatticeProb

/-- A box whose sites have toppled contains at least one grain per internal edge. -/
theorem box_sum_ge (d : ℕ) (h : ℤ) (n T k : ℕ) (x : Site d)
    (hpos : ∀ y : Site d, (∀ i, |y i - x i| ≤ (k : ℤ)) →
      0 < podo (fun y : Site d => h + (n : ℤ) * dirac 0 y) T y) :
    (d : ℤ) * (2 * k) * (2 * k + 1) ^ (d - 1) ≤
      ∑ y ∈ Fintype.piFinset (fun i => Finset.Icc (x i - k) (x i + k)),
        (h + (n : ℤ) * dirac 0 y + lap (podo (fun y : Site d => h + (n : ℤ) * dirac 0 y) T) y) := by
  classical
  let s : Site d → ℤ := fun y => h + (n : ℤ) * dirac 0 y
  let B : Finset (Site d) := Fintype.piFinset (fun i => Finset.Icc (x i - k) (x i + k))
  have hB : ∀ y ∈ B, 0 < podo s T y := by
    intro y hy
    apply hpos y
    intro i
    have hi := Fintype.mem_piFinset.mp hy i
    simp only [Finset.mem_Icc] at hi
    rw [abs_le]
    omega
  let t : Site d → ℕ := fun y => if hp : 0 < podo s T y then (exists_last_topple s T y hp).choose else 0
  have hlast : ∀ y ∈ B, t y < T ∧ 2 * (d : ℤ) ≤ pconf s (t y) y ∧
      podo s T y = podo s (t y + 1) y := by
    intro y hy
    dsimp only [t]
    rw [dite_eq_left (hB y hy)]
    exact (exists_last_topple s T y (hB y hy)).choose_spec
  let r : Site d → Site d → ℤ := fun y z => podo s T z - podo s (t y) z
  have hr : ∀ y ∈ B, ∀ z, 0 ≤ r y z := by
    intro y hy z
    dsimp [r]
    have hm := podo_mono s (Nat.le_of_lt (hlast y hy).1) z
    omega
  let E : Fin d → Finset (Site d) := fun i => B.filter (fun y => y i < x i + k)
  have hsub : ∀ i, E i ⊆ B := fun i => Finset.filter_subset _ _
  have hplus : ∀ i, (E i).image (fun y => y + unit i) ⊆ B := by
    intro i z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    have hyB : y ∈ B := (Finset.mem_filter.mp hy).1
    have hyi := (Finset.mem_filter.mp hy).2
    apply Fintype.mem_piFinset.mpr
    intro j
    have hj := Fintype.mem_piFinset.mp hyB j
    simp only [Finset.mem_Icc] at hj ⊢
    by_cases hji : j = i
    · subst j
      simp only [Pi.add_apply, unit, Pi.single_eq_same]
      omega
    · have hu : unit i j = 0 := by simp [unit, hji]
      simp only [Pi.add_apply, hu, add_zero]
      exact hj
  have hedge : ∀ i y, y ∈ E i → 1 ≤ r y (y + unit i) + r (y + unit i) y := by
    intro i y hy
    have hyB := hsub i hy
    have hyplus : y + unit i ∈ B := hplus i (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    rcases le_total (t y) (t (y + unit i)) with hle | hle
    · have hrecv := one_le_received s T (t y) (t (y + unit i)) (y + unit i) hle
        (hlast _ hyplus).2.1 (hlast _ hyplus).2.2
      have hnn := hr (y + unit i) hyplus y
      dsimp [r] at *
      omega
    · have hrecv := one_le_received s T (t (y + unit i)) (t y) y hle
        (hlast _ hyB).2.1 (hlast _ hyB).2.2
      have hnn := hr y hyB (y + unit i)
      dsimp [r] at *
      omega
  have heach : ∀ i, ((E i).card : ℤ) ≤
      ∑ y ∈ B, (r y (y + unit i) + r y (y - unit i)) :=
    fun i => edges_le_sum B (E i) i r (hsub i) (hplus i) hr (hedge i)
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => heach i)
  have hcard : ∀ i, ((E i).card : ℤ) = (2 * (k : ℤ)) * (2 * (k : ℤ) + 1) ^ (d - 1) := by
    intro i
    have := box_edge_card d k x i
    exact_mod_cast this
  simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htotal
  rw [Finset.sum_comm] at htotal
  have hfinal : (∑ y ∈ B, ∑ i : Fin d, (r y (y + unit i) + r y (y - unit i))) ≤
      ∑ y ∈ B, pconf s T y := by
    apply Finset.sum_le_sum
    intro y hy
    exact pconf_ge_received s T (t y) y (hlast y hy).2.1 (hlast y hy).2.2
  simpa only [B, s, pconf, mul_assoc] using htotal.trans hfinal

end LatticeProb.Sandpile.FLP
