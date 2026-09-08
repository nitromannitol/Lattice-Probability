/-
The same-parity total-variation gradient of the simple random walk, in every
dimension.

`ssec:green-estimates` asks for `∑_y |p_n(x,y) - p_n(w,y)| ≤ C |x-w| n^{-1/2}`
when `x` and `w` have the same parity.  `LatticeProb/Walk/ShiftGrad.lean` reduces
that to the shift by a SUM OF TWO signed unit vectors, and this file proves the
bound for such a shift.

Three ingredients meet here.  The rotated schedule decomposition
`LatticeProb.srwHeat_eq_schedRot` writes the kernel as an average over the
schedules of a product in which a chosen pair `i ≠ j` of coordinates is replaced
by the two rotated coordinates `x_i + x_j` and `x_i - x_j`, both one-dimensional
kernels run for the number of steps `K(c)` the schedule gives to the pair.  A
shift supported on the pair translates those two rotated coordinates by
`g_i + g_j` and `g_i - g_j`, each of which is `0` or `±2` when `g` is a sum of two
signed unit vectors; the shift never changes the parity of a rotated coordinate,
which is exactly what the same-parity hypothesis buys.  So the conditional
total-variation distance is at most twice the one-dimensional two-step gradient
at `K(c)`, which is `O(K(c)^{-1/2})`.  Averaging that over the schedules is
`LatticeProb.avg_inv_sqrt_succ_blockCnt_le`, and gives `O(n^{-1/2})`.

The bookkeeping that makes the middle step short is the rotation
`LatticeProb.rotSite`, an injection of the lattice into itself that replaces the
pair of coordinates by their sum and difference.  After it the summand is a
PRODUCT over the coordinates, one factor per coordinate, and a finite sum of such
a product is at most the product of the coordinate sums
(`LatticeProb.sum_prod_le_prod_sum`), which is the only place the dimension
enters.  Without the rotation the pair contributes a function of `x_i + x_j` and
`x_i - x_j` jointly and no product bound applies.

In dimension one there is no pair, and the statement is the one-dimensional
gradient `LatticeProb.exists_tsum_abs_S1_shift_le` read through the identification
of `ℤ` with the sites.
-/
import Mathlib
import LatticeProb.Walk.SchedRot
import LatticeProb.Walk.SchedBinom
import LatticeProb.Walk.OneDimGrad
import LatticeProb.Walk.ShiftGrad

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

theorem sum_prod_le_prod_sum (g : Fin d → ℤ → ℝ) (hg : ∀ l c, 0 ≤ g l c)
    (F : Finset (Site d)) :
    ∑ w ∈ F, ∏ l : Fin d, g l (w l)
      ≤ ∏ l : Fin d, ∑ c ∈ F.image (fun w : Site d => w l), g l c := by
  classical
  have hsub : F ⊆ Fintype.piFinset (fun l => F.image (fun w : Site d => w l)) := by
    intro w hw
    rw [Fintype.mem_piFinset]
    exact fun l => Finset.mem_image_of_mem _ hw
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun w _ _ => Finset.prod_nonneg fun l _ => hg l (w l))).trans ?_
  rw [Finset.prod_univ_sum]


theorem prod_split_pair {i j : Fin d} (hij : i ≠ j) (G : Fin d → ℝ) :
    ∏ m : Fin d, G m = G i * G j * ∏ m ∈ (Finset.univ.erase i).erase j, G m := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ G (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) G
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
  ring

/-- A finite sum of a product of a function of the `i`-th coordinate, a function
of the `j`-th coordinate and the one-dimensional kernels at the remaining
coordinates is at most the product of the two total sums. -/
theorem sum_block_le {i j : Fin d} (hij : i ≠ j) (n : Fin d → ℕ) (f h : ℤ → ℝ)
    (hf : ∀ s, 0 ≤ f s) (hh : ∀ t, 0 ≤ h t) (hfs : Summable f) (hhs : Summable h)
    (F : Finset (Site d)) :
    ∑ w ∈ F, f (w i) * h (w j) * ∏ l ∈ (Finset.univ.erase i).erase j, S1 (n l) (w l)
      ≤ (∑' s : ℤ, f s) * (∑' t : ℤ, h t) := by
  classical
  set E : Finset (Fin d) := (Finset.univ.erase i).erase j with hE
  set g : Fin d → ℤ → ℝ := fun l => if l = i then f else if l = j then h else S1 (n l) with hgdef
  have hgnn : ∀ l c, 0 ≤ g l c := by
    intro l c
    rw [hgdef]
    dsimp only
    split
    · exact hf c
    · split
      · exact hh c
      · exact S1_nonneg _ _
  have hgi : g i = f := by rw [hgdef]; simp
  have hgj : g j = h := by rw [hgdef]; simp [Ne.symm hij]
  have hgE : ∀ l ∈ E, g l = S1 (n l) := by
    intro l hl
    have h1 : l ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
    have h2 : l ≠ j := Finset.ne_of_mem_erase hl
    rw [hgdef]; simp [h1, h2]
  have hrw : ∀ w : Site d,
      f (w i) * h (w j) * ∏ l ∈ E, S1 (n l) (w l) = ∏ l : Fin d, g l (w l) := by
    intro w
    rw [prod_split_pair hij (fun l => g l (w l)), hgi, hgj]
    congr 1
    exact (Finset.prod_congr rfl fun l hl => by rw [hgE l hl]).symm
  rw [Finset.sum_congr rfl fun w _ => hrw w]
  refine (sum_prod_le_prod_sum g hgnn F).trans ?_
  rw [prod_split_pair hij (fun l => ∑ c ∈ F.image (fun w : Site d => w l), g l c), hgi, hgj]
  have hbound : ∀ l ∈ E, (∑ c ∈ F.image (fun w : Site d => w l), g l c) ≤ 1 := by
    intro l hl
    rw [hgE l hl]
    exact sum_finset_S1_le _ _
  have hnn : ∀ l ∈ E, (0 : ℝ) ≤ ∑ c ∈ F.image (fun w : Site d => w l), g l c :=
    fun l _ => Finset.sum_nonneg fun c _ => hgnn l c
  have hprodle : (∏ l ∈ E, ∑ c ∈ F.image (fun w : Site d => w l), g l c) ≤ 1 :=
    Finset.prod_le_one hnn hbound
  have hfle : (∑ c ∈ F.image (fun w : Site d => w i), f c) ≤ ∑' s : ℤ, f s :=
    Summable.sum_le_tsum _ (fun c _ => hf c) hfs
  have hhle : (∑ c ∈ F.image (fun w : Site d => w j), h c) ≤ ∑' t : ℤ, h t :=
    Summable.sum_le_tsum _ (fun c _ => hh c) hhs
  have hfnn : (0 : ℝ) ≤ ∑ c ∈ F.image (fun w : Site d => w i), f c :=
    Finset.sum_nonneg fun c _ => hf c
  have hhnn : (0 : ℝ) ≤ ∑ c ∈ F.image (fun w : Site d => w j), h c :=
    Finset.sum_nonneg fun c _ => hh c
  have hprodnn : (0 : ℝ) ≤ ∏ l ∈ E, ∑ c ∈ F.image (fun w : Site d => w l), g l c :=
    Finset.prod_nonneg hnn
  calc (∑ c ∈ F.image (fun w : Site d => w i), f c)
        * (∑ c ∈ F.image (fun w : Site d => w j), h c)
        * ∏ l ∈ E, ∑ c ∈ F.image (fun w : Site d => w l), g l c
      ≤ (∑ c ∈ F.image (fun w : Site d => w i), f c)
        * (∑ c ∈ F.image (fun w : Site d => w j), h c) * 1 := by
        exact mul_le_mul_of_nonneg_left hprodle (by positivity)
    _ = (∑ c ∈ F.image (fun w : Site d => w i), f c)
        * (∑ c ∈ F.image (fun w : Site d => w j), h c) := by ring
    _ ≤ (∑' s : ℤ, f s) * (∑' t : ℤ, h t) := by
        exact mul_le_mul hfle hhle hhnn (le_trans hfnn hfle)


/-! ### The rotation of a pair of coordinates -/

/-- Replace the coordinates `i` and `j` of a site by their sum and difference. -/
def rotSite (i j : Fin d) (w : Site d) : Site d :=
  Function.update (Function.update w i (w i + w j)) j (w i - w j)

theorem rotSite_apply_i {i j : Fin d} (hij : i ≠ j) (w : Site d) :
    rotSite i j w i = w i + w j := by
  rw [rotSite, Function.update_of_ne hij, Function.update_self]

theorem rotSite_apply_j (i j : Fin d) (w : Site d) : rotSite i j w j = w i - w j := by
  rw [rotSite, Function.update_self]

theorem rotSite_apply_other (i j : Fin d) (w : Site d) {l : Fin d} (hli : l ≠ i) (hlj : l ≠ j) :
    rotSite i j w l = w l := by
  rw [rotSite, Function.update_of_ne hlj, Function.update_of_ne hli]

theorem rotSite_injective {i j : Fin d} (hij : i ≠ j) :
    Function.Injective (rotSite i j : Site d → Site d) := by
  intro w v hwv
  have hi := congrFun hwv i
  have hj := congrFun hwv j
  rw [rotSite_apply_i hij, rotSite_apply_i hij] at hi
  rw [rotSite_apply_j, rotSite_apply_j] at hj
  funext l
  by_cases hli : l = i
  · subst hli; omega
  · by_cases hlj : l = j
    · subst hlj; omega
    · have := congrFun hwv l
      rwa [rotSite_apply_other i j w hli hlj, rotSite_apply_other i j v hli hlj] at this

/-! ### The one-dimensional gradient at a general shift -/

/-- The total-variation distance between the one-dimensional kernel and its
translate by `α`. -/
noncomputable def S1Grad (m : ℕ) (α : ℤ) : ℝ := ∑' s : ℤ, |S1 m s - S1 m (s + α)|

theorem S1Grad_nonneg (m : ℕ) (α : ℤ) : 0 ≤ S1Grad m α :=
  tsum_nonneg fun _ => abs_nonneg _

theorem S1Grad_zero (m : ℕ) : S1Grad m 0 = 0 := by
  simp [S1Grad]

theorem S1Grad_neg (m : ℕ) (α : ℤ) : S1Grad m (-α) = S1Grad m α := by
  have h := (Equiv.addRight α).tsum_eq (fun s : ℤ => |S1 m s - S1 m (s + -α)|)
  rw [S1Grad, ← h]
  refine tsum_congr fun u => ?_
  simp only [Equiv.coe_addRight]
  rw [show u + α + -α = u from by ring, abs_sub_comm]


/-! ### The gradient of the rotated kernel -/

/-- **The gradient of one rotated product kernel.**  A shift supported on the
pair `{i, j}` translates the two rotated coordinates by `g i + g j` and
`g i - g j` and leaves the other coordinates alone, so the total-variation
distance is at most the sum of the two one-dimensional gradients at the number of
steps the schedule gives to the pair. -/
theorem sum_abs_KR_shift_le {i j : Fin d} (hij : i ≠ j) (n : Fin d → ℕ) (g : Site d)
    (hg : ∀ l, l ≠ i → l ≠ j → g l = 0) (F : Finset (Site d)) :
    ∑ w ∈ F, |KR i j n w - KR i j n (w + g)|
      ≤ S1Grad (n i + n j) (g i + g j) + S1Grad (n i + n j) (g i - g j) := by
  classical
  have hterm : ∀ w : Site d, |KR i j n w - KR i j n (w + g)|
      ≤ (|S1 (n i + n j) (rotSite i j w i)
            - S1 (n i + n j) (rotSite i j w i + (g i + g j))|
          * S1 (n i + n j) (rotSite i j w j)
          * ∏ l ∈ (Finset.univ.erase i).erase j, S1 (n l) (rotSite i j w l))
        + (S1 (n i + n j) (rotSite i j w i + (g i + g j))
          * |S1 (n i + n j) (rotSite i j w j)
              - S1 (n i + n j) (rotSite i j w j + (g i - g j))|
          * ∏ l ∈ (Finset.univ.erase i).erase j, S1 (n l) (rotSite i j w l)) := by
    intro w
    have hP : ∏ l ∈ (Finset.univ.erase i).erase j, S1 (n l) (rotSite i j w l)
        = ∏ l ∈ (Finset.univ.erase i).erase j, S1 (n l) (w l) := by
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [rotSite_apply_other i j w (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl))
        (Finset.ne_of_mem_erase hl)]
    have hPg : ∏ l ∈ (Finset.univ.erase i).erase j, S1 (n l) ((w + g) l)
        = ∏ l ∈ (Finset.univ.erase i).erase j, S1 (n l) (w l) := by
      refine Finset.prod_congr rfl fun l hl => ?_
      have h1 : l ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
      have h2 : l ≠ j := Finset.ne_of_mem_erase hl
      show S1 (n l) (w l + g l) = S1 (n l) (w l)
      rw [hg l h1 h2, add_zero]
    have hsum : (w + g) i + (w + g) j = (w i + w j) + (g i + g j) := by
      show w i + g i + (w j + g j) = _
      ring
    have hdiff : (w + g) i - (w + g) j = (w i - w j) + (g i - g j) := by
      show w i + g i - (w j + g j) = _
      ring
    rw [KR, KR, hsum, hdiff, hPg, rotSite_apply_i hij, rotSite_apply_j, hP]
    have hnnP : (0 : ℝ) ≤ ∏ l ∈ (Finset.univ.erase i).erase j, S1 (n l) (w l) :=
      Finset.prod_nonneg fun _ _ => S1_nonneg _ _
    set A := S1 (n i + n j) (w i + w j)
    set A' := S1 (n i + n j) (w i + w j + (g i + g j))
    set B := S1 (n i + n j) (w i - w j)
    set B' := S1 (n i + n j) (w i - w j + (g i - g j))
    set P := ∏ l ∈ (Finset.univ.erase i).erase j, S1 (n l) (w l)
    have hkey : |A * B * P - A' * B' * P| ≤ |A - A'| * B * P + A' * |B - B'| * P := by
      have hB : (0 : ℝ) ≤ B := S1_nonneg _ _
      have hA' : (0 : ℝ) ≤ A' := S1_nonneg _ _
      have he : A * B * P - A' * B' * P = ((A - A') * B + A' * (B - B')) * P := by ring
      rw [he, abs_mul, abs_of_nonneg hnnP]
      have h1 : |(A - A') * B + A' * (B - B')| ≤ |A - A'| * B + A' * |B - B'| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hB, abs_of_nonneg hA']
      nlinarith [h1, hnnP, abs_nonneg ((A - A') * B + A' * (B - B'))]
    calc |A * B * P - A' * B' * P| ≤ |A - A'| * B * P + A' * |B - B'| * P := hkey
      _ = |A - A'| * B * P + A' * |B - B'| * P := rfl
  refine (Finset.sum_le_sum fun w _ => hterm w).trans ?_
  rw [Finset.sum_add_distrib]
  have hrot : ∀ (Q : Site d → ℝ), ∑ w ∈ F, Q (rotSite i j w) = ∑ v ∈ F.image (rotSite i j), Q v :=
    fun Q => (Finset.sum_image fun a _ b _ hab => rotSite_injective hij hab).symm
  have h1 : ∑ w ∈ F, (|S1 (n i + n j) (rotSite i j w i)
            - S1 (n i + n j) (rotSite i j w i + (g i + g j))|
          * S1 (n i + n j) (rotSite i j w j)
          * ∏ l ∈ (Finset.univ.erase i).erase j, S1 (n l) (rotSite i j w l))
      ≤ S1Grad (n i + n j) (g i + g j) * 1 := by
    rw [hrot (fun v => |S1 (n i + n j) (v i) - S1 (n i + n j) (v i + (g i + g j))|
      * S1 (n i + n j) (v j) * ∏ l ∈ (Finset.univ.erase i).erase j, S1 (n l) (v l))]
    have := sum_block_le hij n
      (fun s => |S1 (n i + n j) s - S1 (n i + n j) (s + (g i + g j))|)
      (fun t => S1 (n i + n j) t) (fun s => abs_nonneg _) (fun t => S1_nonneg _ _)
      (summable_abs_S1_shift_any _ _) (summable_S1 _) (F.image (rotSite i j))
    rw [tsum_S1] at this
    exact this
  have h2 : ∑ w ∈ F, (S1 (n i + n j) (rotSite i j w i + (g i + g j))
          * |S1 (n i + n j) (rotSite i j w j)
              - S1 (n i + n j) (rotSite i j w j + (g i - g j))|
          * ∏ l ∈ (Finset.univ.erase i).erase j, S1 (n l) (rotSite i j w l))
      ≤ 1 * S1Grad (n i + n j) (g i - g j) := by
    rw [hrot (fun v => S1 (n i + n j) (v i + (g i + g j))
      * |S1 (n i + n j) (v j) - S1 (n i + n j) (v j + (g i - g j))|
      * ∏ l ∈ (Finset.univ.erase i).erase j, S1 (n l) (v l))]
    have := sum_block_le hij n
      (fun s => S1 (n i + n j) (s + (g i + g j)))
      (fun t => |S1 (n i + n j) t - S1 (n i + n j) (t + (g i - g j))|)
      (fun s => S1_nonneg _ _) (fun t => abs_nonneg _)
      (((Equiv.addRight (g i + g j)).summable_iff (f := fun s : ℤ => S1 (n i + n j) s)).mpr
        (summable_S1 _))
      (summable_abs_S1_shift_any _ _) (F.image (rotSite i j))
    rw [tsum_S1_shift] at this
    exact this
  linarith [h1, h2]


theorem S1Grad_le_two (m : ℕ) (α : ℤ) : S1Grad m α ≤ 2 := by
  have hs1 : Summable fun s : ℤ => S1 m s := summable_S1 m
  have hs2 : Summable fun s : ℤ => S1 m (s + α) :=
    ((Equiv.addRight α).summable_iff (f := fun s : ℤ => S1 m s)).mpr hs1
  have hle : ∀ s : ℤ, |S1 m s - S1 m (s + α)| ≤ S1 m s + S1 m (s + α) := by
    intro s
    have h1 : (0 : ℝ) ≤ S1 m s := S1_nonneg _ _
    have h2 : (0 : ℝ) ≤ S1 m (s + α) := S1_nonneg _ _
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  calc S1Grad m α ≤ ∑' s : ℤ, (S1 m s + S1 m (s + α)) :=
        Summable.tsum_le_tsum hle (summable_abs_S1_shift_any m α) (hs1.add hs2)
    _ = 1 + 1 := by rw [Summable.tsum_add hs1 hs2, tsum_S1, tsum_S1_shift]
    _ = 2 := by norm_num

/-- The one-dimensional gradient at a shift of size at most two decays like
`(m+1)^{-1/2}`, with a constant that also covers the trivial bound at `m = 0`. -/
theorem exists_S1Grad_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (α : ℤ), (α = 0 ∨ α = 2 ∨ α = -2) →
      S1Grad m α ≤ C / Real.sqrt ((m : ℝ) + 1) := by
  obtain ⟨C₁, hC₁, hgrad⟩ := exists_tsum_abs_S1_shift_le
  refine ⟨max 2 (C₁ * Real.sqrt 2), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  have hkey : ∀ m : ℕ, S1Grad m 2 ≤ max 2 (C₁ * Real.sqrt 2) / Real.sqrt ((m : ℝ) + 1) := by
    intro m
    have hsq : (0 : ℝ) < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have : S1Grad 0 2 ≤ 2 := S1Grad_le_two 0 2
      have h2 : (2 : ℝ) ≤ max 2 (C₁ * Real.sqrt 2) := le_max_left _ _
      simp only [Nat.cast_zero, zero_add, Real.sqrt_one, div_one]
      linarith
    · have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by linarith)
      have h1 : S1Grad m 2 ≤ C₁ / Real.sqrt (m : ℝ) := hgrad m hm
      have hle : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt (m : ℝ) := by
        rw [← Real.sqrt_mul (by norm_num)]
        exact Real.sqrt_le_sqrt (by linarith)
      have h2 : C₁ / Real.sqrt (m : ℝ) ≤ (C₁ * Real.sqrt 2) / Real.sqrt ((m : ℝ) + 1) := by
        rw [div_le_div_iff₀ hsm hsq]
        nlinarith [hle, hC₁.le, Real.sqrt_nonneg (m : ℝ)]
      have h3 : (C₁ * Real.sqrt 2) / Real.sqrt ((m : ℝ) + 1)
          ≤ max 2 (C₁ * Real.sqrt 2) / Real.sqrt ((m : ℝ) + 1) :=
        (div_le_div_iff_of_pos_right hsq).mpr (le_max_right _ _)
      linarith
  intro m α hα
  rcases hα with rfl | rfl | rfl
  · rw [S1Grad_zero]
    positivity
  · exact hkey m
  · rw [show (-2 : ℤ) = -(2 : ℤ) from by norm_num, S1Grad_neg]
    exact hkey m


/-! ### The gradient of the kernel along a generator -/

theorem blockCnt_pair {i j : Fin d} (hij : i ≠ j) {r : ℕ} (c : Fin r → Fin d) :
    blockCnt ({i, j} : Finset (Fin d)) c = cnt c i + cnt c j := by
  classical
  rw [blockCnt, cnt, cnt, ← Finset.card_filter, ← Finset.card_filter]
  have hsplit : (Finset.univ.filter fun t => c t ∈ ({i, j} : Finset (Fin d)))
      = (Finset.univ.filter fun t => c t = i) ∪ (Finset.univ.filter fun t => c t = j) := by
    rw [← Finset.filter_or]
    refine Finset.filter_congr fun t _ => ?_
    simp
  have hdisj : Disjoint (Finset.univ.filter fun t => c t = i)
      (Finset.univ.filter fun t => c t = j) := by
    rw [Finset.disjoint_filter]
    intro t _ h1 h2
    exact hij (h1 ▸ h2 ▸ rfl)
  rw [hsplit, Finset.card_union_of_disjoint hdisj]

theorem tsum_abs_srwHeat_pair_shift_le (hd : 0 < d) {i j : Fin d} (hij : i ≠ j)
    (r : ℕ) (g : Site d) (hg : ∀ l, l ≠ i → l ≠ j → g l = 0) :
    ∑' w : Site d, |srwHeat d r w - srwHeat d r (w + g)|
      ≤ (∑ c : Fin r → Fin d,
          (S1Grad (cnt c i + cnt c j) (g i + g j)
            + S1Grad (cnt c i + cnt c j) (g i - g j))) / (d : ℝ) ^ r := by
  classical
  have hdr : (0 : ℝ) < (d : ℝ) ^ r := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  refine Real.tsum_le_of_sum_le (fun w => abs_nonneg _) fun F => ?_
  have hterm : ∀ w : Site d, |srwHeat d r w - srwHeat d r (w + g)|
      ≤ (∑ c : Fin r → Fin d, |KR i j (cnt c) w - KR i j (cnt c) (w + g)|) / (d : ℝ) ^ r := by
    intro w
    rw [srwHeat_eq_schedRot hd hij r w, srwHeat_eq_schedRot hd hij r (w + g),
      div_sub_div_same, abs_div, abs_of_pos hdr]
    refine (div_le_div_iff_of_pos_right hdr).mpr ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  refine (Finset.sum_le_sum fun w _ => hterm w).trans ?_
  rw [← Finset.sum_div]
  refine (div_le_div_iff_of_pos_right hdr).mpr ?_
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun c _ => sum_abs_KR_shift_le hij (cnt c) g hg F


/-- **The gradient along a shift supported on a pair of coordinates.**  Averaging
the one-dimensional gradient over the schedules with the block average of
`LatticeProb.avg_inv_sqrt_succ_blockCnt_le` gives the rate `n^{-1/2}`. -/
theorem tsum_abs_srwHeat_pair_shift_bound (hd : 0 < d) {i j : Fin d} (hij : i ≠ j)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hS : ∀ (m : ℕ) (α : ℤ), (α = 0 ∨ α = 2 ∨ α = -2) →
      S1Grad m α ≤ C₀ / Real.sqrt ((m : ℝ) + 1))
    (n : ℕ) (hn : 1 ≤ n) (g : Site d) (hg : ∀ l, l ≠ i → l ≠ j → g l = 0)
    (hα : g i + g j = 0 ∨ g i + g j = 2 ∨ g i + g j = -2)
    (hβ : g i - g j = 0 ∨ g i - g j = 2 ∨ g i - g j = -2) :
    ∑' w : Site d, |srwHeat d n w - srwHeat d n (w + g)|
      ≤ 2 * C₀ * Real.sqrt d / Real.sqrt n := by
  classical
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdr : (0 : ℝ) < (d : ℝ) ^ n := by positivity
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcard : ({i, j} : Finset (Fin d)).card = 2 := Finset.card_pair hij
  have hstep : ∀ c : Fin n → Fin d,
      S1Grad (cnt c i + cnt c j) (g i + g j) + S1Grad (cnt c i + cnt c j) (g i - g j)
        ≤ 2 * C₀ * (1 / Real.sqrt ((blockCnt ({i, j} : Finset (Fin d)) c : ℝ) + 1)) := by
    intro c
    have h1 := hS (cnt c i + cnt c j) _ hα
    have h2 := hS (cnt c i + cnt c j) _ hβ
    rw [blockCnt_pair hij c]
    have hsq : (0 : ℝ) < Real.sqrt (((cnt c i + cnt c j : ℕ) : ℝ) + 1) :=
      Real.sqrt_pos.mpr (by positivity)
    rw [mul_one_div]
    have hdd : 2 * C₀ / Real.sqrt (((cnt c i + cnt c j : ℕ) : ℝ) + 1)
        = C₀ / Real.sqrt (((cnt c i + cnt c j : ℕ) : ℝ) + 1)
          + C₀ / Real.sqrt (((cnt c i + cnt c j : ℕ) : ℝ) + 1) := by ring
    rw [hdd]
    linarith
  have hbase := tsum_abs_srwHeat_pair_shift_le hd hij n g hg
  have hsum : (∑ c : Fin n → Fin d,
      (S1Grad (cnt c i + cnt c j) (g i + g j) + S1Grad (cnt c i + cnt c j) (g i - g j)))
        / (d : ℝ) ^ n
      ≤ 2 * C₀ * ((∑ c : Fin n → Fin d,
          1 / Real.sqrt ((blockCnt ({i, j} : Finset (Fin d)) c : ℝ) + 1)) / (d : ℝ) ^ n) := by
    rw [mul_div_assoc'] 
    refine (div_le_div_iff_of_pos_right hdr).mpr ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun c _ => hstep c
  have havg := avg_inv_sqrt_succ_blockCnt_le hd ({i, j} : Finset (Fin d))
    (by rw [hcard]; norm_num) n
  rw [hcard] at havg
  have hfin : Real.sqrt ((d : ℝ) / (2 * ((n : ℝ) + 1))) ≤ Real.sqrt d / Real.sqrt n := by
    rw [← Real.sqrt_div (le_of_lt hdR)]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_div_iff₀ (by positivity) hnR]
    nlinarith [hdR.le, hnR.le]
  have hC2 : (0 : ℝ) ≤ 2 * C₀ := by positivity
  calc ∑' w : Site d, |srwHeat d n w - srwHeat d n (w + g)|
      ≤ (∑ c : Fin n → Fin d,
          (S1Grad (cnt c i + cnt c j) (g i + g j)
            + S1Grad (cnt c i + cnt c j) (g i - g j))) / (d : ℝ) ^ n := hbase
    _ ≤ 2 * C₀ * ((∑ c : Fin n → Fin d,
          1 / Real.sqrt ((blockCnt ({i, j} : Finset (Fin d)) c : ℝ) + 1)) / (d : ℝ) ^ n) := hsum
    _ ≤ 2 * C₀ * Real.sqrt ((d : ℝ) / (2 * ((n : ℝ) + 1))) := by
        have := mul_le_mul_of_nonneg_left havg hC2
        simpa [Nat.cast_ofNat] using this
    _ ≤ 2 * C₀ * (Real.sqrt d / Real.sqrt n) := mul_le_mul_of_nonneg_left hfin hC2
    _ = 2 * C₀ * Real.sqrt d / Real.sqrt n := by ring


/-- **The same-parity gradient along a generator, in every dimension `d ≥ 2`.**
The shift is a sum of two signed unit vectors, so it is supported on at most two
coordinates; taking those two as the pair of the rotated decomposition, the two
rotated coordinates are shifted by `0` or `±2`, and the bound is the average of
the one-dimensional gradient over the number of steps in the pair. -/
theorem exists_tsum_abs_srwHeat_gen_le (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ g₁ g₂ : Site d,
      graphNorm g₁ = 1 → graphNorm g₂ = 1 →
      ∑' w : Site d, |srwHeat d n w - srwHeat d n (w + (g₁ + g₂))| ≤ C / Real.sqrt n := by
  classical
  obtain ⟨C₀, hC₀, hS⟩ := exists_S1Grad_le
  have hd0 : 0 < d := by omega
  refine ⟨2 * C₀ * Real.sqrt d, by positivity, fun n hn g₁ g₂ h₁ h₂ => ?_⟩
  obtain ⟨i₁, s₁, hs₁, rfl⟩ := eq_single_of_graphNorm_eq_one h₁
  obtain ⟨i₂, s₂, hs₂, rfl⟩ := eq_single_of_graphNorm_eq_one h₂
  have hs₁' : s₁ = 1 ∨ s₁ = -1 := by omega
  have hs₂' : s₂ = 1 ∨ s₂ = -1 := by omega
  by_cases hne : i₁ = i₂
  · subst hne
    haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
    obtain ⟨j, hj⟩ : ∃ j : Fin d, j ≠ i₁ := exists_ne i₁
    have hgi : (Pi.single i₁ s₁ + Pi.single i₁ s₂ : Site d) i₁ = s₁ + s₂ := by
      simp
    have hgj : (Pi.single i₁ s₁ + Pi.single i₁ s₂ : Site d) j = 0 := by
      simp [hj]
    refine tsum_abs_srwHeat_pair_shift_bound hd0 (Ne.symm hj) hC₀ hS n hn _ ?_ ?_ ?_
    · intro l hl1 _
      simp [hl1]
    · rw [hgi, hgj]; omega
    · rw [hgi, hgj]; omega
  · have hgi : (Pi.single i₁ s₁ + Pi.single i₂ s₂ : Site d) i₁ = s₁ := by
      simp [hne]
    have hgj : (Pi.single i₁ s₁ + Pi.single i₂ s₂ : Site d) i₂ = s₂ := by
      simp [Ne.symm hne]
    refine tsum_abs_srwHeat_pair_shift_bound hd0 hne hC₀ hS n hn _ ?_ ?_ ?_
    · intro l hl1 hl2
      simp [hl1, hl2]
    · rw [hgi, hgj]; omega
    · rw [hgi, hgj]; omega


/-! ### Dimension one -/

theorem exists_tsum_abs_srwHeat_gen_le_one :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ g₁ g₂ : Site 1,
      graphNorm g₁ = 1 → graphNorm g₂ = 1 →
      ∑' w : Site 1, |srwHeat 1 n w - srwHeat 1 n (w + (g₁ + g₂))| ≤ C / Real.sqrt n := by
  classical
  obtain ⟨C₀, hC₀, hS⟩ := exists_S1Grad_le
  refine ⟨C₀, hC₀, fun n hn g₁ g₂ h₁ h₂ => ?_⟩
  obtain ⟨i₁, s₁, hs₁, rfl⟩ := eq_single_of_graphNorm_eq_one h₁
  obtain ⟨i₂, s₂, hs₂, rfl⟩ := eq_single_of_graphNorm_eq_one h₂
  have hi₁ : i₁ = 0 := Subsingleton.elim _ _
  have hi₂ : i₂ = 0 := Subsingleton.elim _ _
  subst hi₁; subst hi₂
  have hv : ∀ k : ℤ, (![k] : Site 1) = fun _ => k := by
    intro k; funext t; fin_cases t; rfl
  have hpt : ∀ k : ℤ, srwHeat 1 n (fun _ => k) = S1 n k := by
    intro k
    rw [S1, hv]
  have he := ((Equiv.funUnique (Fin 1) ℤ).symm).tsum_eq
    (fun w : Site 1 => |srwHeat 1 n w
      - srwHeat 1 n (w + (Pi.single (0 : Fin 1) s₁ + Pi.single (0 : Fin 1) s₂))|)
  rw [← he]
  have hcongr : ∀ k : ℤ,
      |srwHeat 1 n ((Equiv.funUnique (Fin 1) ℤ).symm k)
        - srwHeat 1 n ((Equiv.funUnique (Fin 1) ℤ).symm k
            + (Pi.single (0 : Fin 1) s₁ + Pi.single (0 : Fin 1) s₂))|
      = |S1 n k - S1 n (k + (s₁ + s₂))| := by
    intro k
    have h2 : (((fun _ => k) : Site 1)
        + (Pi.single (0 : Fin 1) s₁ + Pi.single (0 : Fin 1) s₂)) = fun _ => k + (s₁ + s₂) := by
      funext t
      have ht : t = 0 := Subsingleton.elim _ _
      subst ht
      simp
    rw [show ((Equiv.funUnique (Fin 1) ℤ).symm k : Site 1) = fun _ => k from rfl, h2, hpt, hpt]
  rw [tsum_congr hcongr]
  have hbound : S1Grad n (s₁ + s₂) ≤ C₀ / Real.sqrt ((n : ℝ) + 1) := by
    refine hS n _ ?_
    omega
  have hmono : C₀ / Real.sqrt ((n : ℝ) + 1) ≤ C₀ / Real.sqrt n := by
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
    have h2 : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    exact div_le_div_of_nonneg_left hC₀.le h1 h2
  exact le_trans hbound hmono


/-! ### The same-parity gradient -/

theorem exists_tsum_abs_srwHeat_gen_le_of_one_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ g₁ g₂ : Site d,
      graphNorm g₁ = 1 → graphNorm g₂ = 1 →
      ∑' w : Site d, |srwHeat d n w - srwHeat d n (w + (g₁ + g₂))| ≤ C / Real.sqrt n := by
  rcases Nat.lt_or_ge d 2 with h | h
  · obtain rfl : d = 1 := by omega
    exact exists_tsum_abs_srwHeat_gen_le_one
  · exact exists_tsum_abs_srwHeat_gen_le h

/-- **The same-parity total-variation gradient of the simple random walk in
every dimension.**  For a shift `u` of even `ℓ¹` norm,

    ∑_w |p_n(w) - p_n(w + u)| ≤ C |u|_1 n^{-1/2} .

This is the second display of `ssec:green-estimates` up to the comparison of the
`ℓ¹` and Euclidean norms of `u`.  The linear factor is the number of generators
in `LatticeProb.tsum_abs_srwHeat_shift_le_of_even`, and the rate is the block
average of the one-dimensional gradient. -/
theorem exists_tsum_abs_srwHeat_even_shift_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ u : Site d, Even (graphNorm u) →
      ∑' w : Site d, |srwHeat d n w - srwHeat d n (w + u)|
        ≤ C * (graphNorm u : ℝ) / Real.sqrt n := by
  obtain ⟨C, hC, hgen⟩ := exists_tsum_abs_srwHeat_gen_le_of_one_le hd
  refine ⟨C / 2, by positivity, fun n hn u hu => ?_⟩
  have h := tsum_abs_srwHeat_shift_le_of_even
    (K := C / Real.sqrt (n : ℝ)) (fun g₁ g₂ h1 h2 => hgen n hn g₁ g₂ h1 h2) u hu
  have he : (graphNorm u : ℝ) / 2 * (C / Real.sqrt (n : ℝ))
      = C / 2 * (graphNorm u : ℝ) / Real.sqrt (n : ℝ) := by ring
  linarith [h, he.le, he.ge]

end LatticeProb
