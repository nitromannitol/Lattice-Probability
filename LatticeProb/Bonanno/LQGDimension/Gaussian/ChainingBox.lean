/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Gaussian.ChainingBox at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import LatticeProb.Bonanno.LQGDimension.Gaussian.MaxInequality
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic

/-!
# A minimal Dudley bound: chaining on a box (node `G4`, `Blueprint.Draft.ChainingBox`)

Let `F` be a finite family with parameters `p i ∈ ℝ^d` (sup norm) of diameter at most `a`, and
vectors `v i` with `‖v i - v j‖² ≤ L² ‖p i - p j‖`.  Then for every `i₀ ∈ F`,
`E max_{i ∈ F} ⟪v i - v i₀, x⟫ ≤ 20 √5 · L √((d + 1) a)`.

Proof (chaining with nets inside `F`).
* Level-`k` cells: `cell a k q = (⌊q_j 4^k / a⌋)_j`.  Two points in the same cell are at
  sup-distance `< a 4^{-k}` (`norm_sub_lt_of_cell_eq`); the level-`k` cells of `F` lie in a box of
  `≤ (4^{k+1})^d` cells (`cell_mem_box`, `card_box_le`).
* `proj k i ∈ F` is a fixed representative of the level-`k` cell of `i` (`proj 0 i = i₀`), so
  `‖p (proj k i) - p i‖ ≤ a 4^{-k}` and the increments `w k i = v (proj (k+1) i) - v (proj k i)` have
  norm `≤ σ_k = L √(5a) 2^{-(k+1)}`; they only depend on the pair of cells of `i` at levels
  `k, k + 1`, so there are at most `4^{(2k+3)d}` of them.
* Since `F` is finite, at a deep enough level `K` the cells separate the distinct parameters, so
  `v (proj K i) = v i` and `v i - v i₀ = ∑_{k<K} w k i` (telescoping).
* Pointwise `max ≤ ∑_k max_i ⟪w k i, x⟫`; each level is bounded by the Gaussian maximal inequality
  (`GaussianMax.integral_iSup_inner_le`, with `λ = √(d+1)/σ_k`) by `10 √(d+1) σ_k (k+1)`, and
  `∑_k (k+1) 2^{-(k+1)} ≤ 2`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped RealInnerProductSpace

namespace LQGDimension

namespace ChainBox

/-! ### Gaussian maxima over families with few distinct vectors -/

section Gaussian

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem integrable_iSup_inner (F : Finset ι) (w : ι → E) :
    Integrable (fun x => ⨆ i : F, ⟪w i, x⟫) (stdGaussian E) := by
  simpa using integrable_iSup_inner_add F w 0

/-- Maximal inequality for a family whose vectors only depend on a label `f i`: the cardinality
entering the bound is the number of labels. -/
theorem integral_iSup_inner_le_of_fiber {κ : Type*} [DecidableEq κ] (F : Finset ι)
    (hF : F.Nonempty) (f : ι → κ) (w : ι → E)
    (hw : ∀ i ∈ F, ∀ j ∈ F, f i = f j → w i = w j) {σ l : ℝ} (hl : 0 < l)
    (hσ : ∀ i ∈ F, ‖w i‖ ≤ σ) :
    ∫ x, (⨆ i : F, ⟪w i, x⟫) ∂stdGaussian E ≤
      (Real.log (F.image f).card + l ^ 2 * σ ^ 2 / 2) / l := by
  classical
  let sec : κ → ι := fun c => if h : ∃ i ∈ F, f i = c then h.choose else hF.choose
  have hsec : ∀ i ∈ F, sec (f i) ∈ F ∧ f (sec (f i)) = f i := by
    intro i hi
    have h : ∃ j ∈ F, f j = f i := ⟨i, hi, rfl⟩
    simp only [sec, dite_eq_left h]
    exact h.choose_spec
  set T : Finset ι := (F.image f).image sec with hTdef
  have hTF : T ⊆ F := by
    intro t ht
    rw [hTdef, Finset.mem_image] at ht
    obtain ⟨c, hc, rfl⟩ := ht
    rw [Finset.mem_image] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    exact (hsec i hi).1
  have hmemT : ∀ i ∈ F, sec (f i) ∈ T := fun i hi =>
    Finset.mem_image_of_mem sec (Finset.mem_image_of_mem f hi)
  have hTne : T.Nonempty := ⟨_, hmemT _ hF.choose_spec⟩
  have : Nonempty F := hF.to_subtype
  have hpt : ∀ x, (⨆ i : F, ⟪w i, x⟫) ≤ ⨆ t : T, ⟪w t, x⟫ := by
    intro x
    refine ciSup_le fun i => ?_
    have heq : w (sec (f i)) = w i := hw _ (hsec i i.2).1 i i.2 (hsec i i.2).2
    rw [← heq]
    exact le_ciSup (f := fun t : T => ⟪w t, x⟫) (Set.finite_range _).bddAbove
      ⟨sec (f i), hmemT i i.2⟩
  have hmono := integral_mono (integrable_iSup_inner F w) (integrable_iSup_inner T w) hpt
  have hmax := GaussianMax.integral_iSup_inner_le T hTne w hl (fun t ht => hσ t (hTF ht))
    (integrable_iSup_inner T w)
  have hcard : Real.log T.card ≤ Real.log (F.image f).card := by
    apply Real.log_le_log
    · exact_mod_cast hTne.card_pos
    · exact_mod_cast Finset.card_image_le
  refine hmono.trans (hmax.trans ?_)
  exact div_le_div_of_nonneg_right (by linarith) hl.le

omit [BorelSpace E] in
/-- If all the vectors agree with `v i₀` on `F`, the expected maximum of the increments is `0`. -/
theorem vecExpectedMax_sub_eq_zero (F : Finset ι) (v : ι → E) (i₀ : ι)
    (h : ∀ i ∈ F, v i = v i₀) : vecExpectedMax F (fun i => v i - v i₀) 0 = 0 := by
  unfold vecExpectedMax
  have hx : ∀ x : E, (⨆ i : F, ⟪v i - v i₀, x⟫ + (0 : ι → ℝ) i) = 0 := by
    intro x
    have h' : ∀ i : F, ⟪v i - v i₀, x⟫ + (0 : ι → ℝ) i = 0 := fun i => by
      rw [h i i.2, sub_self, inner_zero_left, Pi.zero_apply, add_zero]
    simp only [h', Real.iSup_const_zero]
  simp only [hx, integral_zero]

end Gaussian

/-! ### Cells -/

section Cells

variable {d : ℕ}

/-- The level-`k` cell of `q`: the integer parts of `q_j 4^k / a`. -/
def cell (a : ℝ) (k : ℕ) (q : Fin d → ℝ) : Fin d → ℤ := fun j => ⌊q j * 4 ^ k / a⌋

theorem norm_sub_lt_of_cell_eq {a : ℝ} (ha : 0 < a) (k : ℕ) {q q' : Fin d → ℝ}
    (h : cell a k q = cell a k q') : ‖q - q'‖ < a / 4 ^ k := by
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  rw [pi_norm_lt_iff (by positivity)]
  intro j
  have hj := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun h j)
  have heq : q j * 4 ^ k / a - q' j * 4 ^ k / a = (q j - q' j) * (4 ^ k / a) := by ring
  rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ k / a)] at hj
  rw [Pi.sub_apply, Real.norm_eq_abs, lt_div_iff₀ h4]
  have hmul : |q j - q' j| * 4 ^ k = |q j - q' j| * (4 ^ k / a) * a := by field_simp
  rw [hmul]
  calc |q j - q' j| * (4 ^ k / a) * a < 1 * a := mul_lt_mul_of_pos_right hj ha
    _ = a := one_mul a

/-- The box of level-`k` cells around the cell of `q₀`. -/
def box (a : ℝ) (k : ℕ) (q₀ : Fin d → ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun j => Finset.Icc (cell a k q₀ j - 4 ^ k) (cell a k q₀ j + 4 ^ k)

theorem cell_mem_box {a : ℝ} (ha : 0 < a) (k : ℕ) {q q₀ : Fin d → ℝ} (h : ‖q - q₀‖ ≤ a) :
    cell a k q ∈ box a k q₀ := by
  rw [box, Fintype.mem_piFinset]
  intro j
  have hj : |q j - q₀ j| ≤ a := by
    have := norm_le_pi_norm (q - q₀) j
    rw [Pi.sub_apply, Real.norm_eq_abs] at this
    linarith
  rw [abs_le] at hj
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  have hc : (((4 : ℤ) ^ k : ℤ) : ℝ) = (4 : ℝ) ^ k := by push_cast; ring
  have heq : q j * 4 ^ k / a - q₀ j * 4 ^ k / a = (q j - q₀ j) * 4 ^ k / a := by ring
  have h2 : (q j - q₀ j) * 4 ^ k / a ≤ 4 ^ k := by
    rw [div_le_iff₀ ha]; nlinarith
  have h3 : -4 ^ k ≤ (q j - q₀ j) * 4 ^ k / a := by
    rw [le_div_iff₀ ha]; nlinarith
  have hup : q j * 4 ^ k / a ≤ q₀ j * 4 ^ k / a + (((4 : ℤ) ^ k : ℤ) : ℝ) := by
    rw [hc]; linarith
  have hlo : q₀ j * 4 ^ k / a - (((4 : ℤ) ^ k : ℤ) : ℝ) ≤ q j * 4 ^ k / a := by
    rw [hc]; linarith
  rw [Finset.mem_Icc]
  constructor
  · have := Int.floor_mono hlo
    rw [Int.floor_sub_intCast] at this
    exact this
  · have := Int.floor_mono hup
    rw [Int.floor_add_intCast] at this
    exact this

theorem card_box_le (a : ℝ) (k : ℕ) (q₀ : Fin d → ℝ) :
    (box a k q₀).card ≤ (4 ^ (k + 1)) ^ d := by
  rw [box, Fintype.card_piFinset]
  have h := Finset.prod_le_pow_card (Finset.univ : Finset (Fin d))
    (fun j => (Finset.Icc (cell a k q₀ j - 4 ^ k) (cell a k q₀ j + 4 ^ k)).card) (4 ^ (k + 1))
    (fun j _ => by
      rw [Int.card_Icc, Int.toNat_le]
      push_cast
      rw [pow_succ]
      have : (1 : ℤ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
      linarith)
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- `∑_{k < n} (k + 1) / 2^{k+1} = 2 - (n + 2) / 2^n`. -/
theorem sum_range_succ_div_two_pow (n : ℕ) :
    ∑ k ∈ Finset.range n, ((k : ℝ) + 1) / 2 ^ (k + 1) = 2 - ((n : ℝ) + 2) / 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    field_simp
    ring

end Cells

/-! ### Representatives and the chaining projections -/

section Proj

variable {ι : Type*} {d : ℕ}

open scoped Classical in
/-- A fixed element of `F` in the level-`k` cell `c` (or `i₀` if there is none). -/
def rep (F : Finset ι) (p : ι → Fin d → ℝ) (a : ℝ) (i₀ : ι) (k : ℕ) (c : Fin d → ℤ) : ι :=
  if h : ∃ i ∈ F, cell a k (p i) = c then h.choose else i₀

/-- The level-`k` chaining projection: `i₀` at level `0`, and the representative of the
level-`k` cell of `i` at level `k ≥ 1`. -/
def proj (F : Finset ι) (p : ι → Fin d → ℝ) (a : ℝ) (i₀ : ι) (k : ℕ) (i : ι) : ι :=
  if k = 0 then i₀ else rep F p a i₀ k (cell a k (p i))

variable {F : Finset ι} {p : ι → Fin d → ℝ} {a : ℝ} {i₀ : ι}

theorem rep_spec (k : ℕ) {i : ι} (hi : i ∈ F) :
    rep F p a i₀ k (cell a k (p i)) ∈ F ∧
      cell a k (p (rep F p a i₀ k (cell a k (p i)))) = cell a k (p i) := by
  have h : ∃ j ∈ F, cell a k (p j) = cell a k (p i) := ⟨i, hi, rfl⟩
  rw [rep, dite_eq_left h]
  exact h.choose_spec

theorem proj_zero (i : ι) : proj F p a i₀ 0 i = i₀ := by simp [proj]

theorem proj_of_ne_zero {k : ℕ} (hk : k ≠ 0) (i : ι) :
    proj F p a i₀ k i = rep F p a i₀ k (cell a k (p i)) := by simp [proj, hk]

theorem proj_mem (hi₀ : i₀ ∈ F) {i : ι} (hi : i ∈ F) (k : ℕ) : proj F p a i₀ k i ∈ F := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [proj_zero]; exact hi₀
  · rw [proj_of_ne_zero hk.ne']; exact (rep_spec k hi).1

theorem proj_congr {k : ℕ} {i j : ι} (h : cell a k (p i) = cell a k (p j)) :
    proj F p a i₀ k i = proj F p a i₀ k j := by
  unfold proj; rw [h]

theorem norm_proj_sub_lt (ha : 0 < a) {k : ℕ} (hk : k ≠ 0) {i : ι} (hi : i ∈ F) :
    ‖p (proj F p a i₀ k i) - p i‖ < a / 4 ^ k := by
  rw [proj_of_ne_zero hk]
  exact norm_sub_lt_of_cell_eq ha k (rep_spec k hi).2

theorem norm_proj_sub_le (ha : 0 < a) (hp : ∀ i ∈ F, ∀ j ∈ F, ‖p i - p j‖ ≤ a) (hi₀ : i₀ ∈ F)
    {i : ι} (hi : i ∈ F) (k : ℕ) : ‖p (proj F p a i₀ k i) - p i‖ ≤ a / 4 ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [proj_zero, pow_zero, div_one]; exact hp i₀ hi₀ i hi
  · exact (norm_proj_sub_lt ha hk.ne' hi).le

/-- Separation at a deep level: at some level `K ≥ 1`, points of `F` closer than the cell size
have the same parameter. -/
theorem exists_level_sep (F : Finset ι) (p : ι → Fin d → ℝ) {a : ℝ} :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ i ∈ F, ∀ j ∈ F, ‖p i - p j‖ < a / 4 ^ K → p i = p j := by
  have htend : Tendsto (fun K : ℕ => a / 4 ^ K) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hev : ∀ᶠ K : ℕ in atTop, 1 ≤ K ∧
      ∀ q ∈ F ×ˢ F, p q.1 ≠ p q.2 → a / 4 ^ K < ‖p q.1 - p q.2‖ := by
    refine (eventually_ge_atTop 1).and ((eventually_all_finset _).2 fun q _ => ?_)
    by_cases hq : p q.1 = p q.2
    · exact Eventually.of_forall fun K h => absurd hq h
    · have hpos : 0 < ‖p q.1 - p q.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hq)
      exact (htend.eventually_lt_const hpos).mono fun K hK _ => hK
  obtain ⟨K, hK1, hK⟩ := hev.exists
  refine ⟨K, hK1, fun i hi j hj hlt => ?_⟩
  by_contra hne
  have := hK (i, j) (Finset.mem_product.2 ⟨hi, hj⟩) hne
  linarith

end Proj

/-! ### The chaining bound -/

section Main

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The chaining bound in the nondegenerate case `L > 0`, `a > 0`. -/
theorem chainingBox_bound_pos {d : ℕ} (F : Finset ι) (p : ι → Fin d → ℝ) (v : ι → E) {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) (hp : ∀ i ∈ F, ∀ j ∈ F, ‖p i - p j‖ ≤ a)
    (hv : ∀ i ∈ F, ∀ j ∈ F, ‖v i - v j‖ ^ 2 ≤ L ^ 2 * ‖p i - p j‖) {i₀ : ι} (hi₀ : i₀ ∈ F) :
    vecExpectedMax F (fun i => v i - v i₀) 0 ≤ 20 * √5 * L * √((d + 1) * a) := by
  classical
  have hFne : F.Nonempty := ⟨i₀, hi₀⟩
  set w : ℕ → ι → E := fun k i => v (proj F p a i₀ (k + 1) i) - v (proj F p a i₀ k i) with hw
  set σ : ℕ → ℝ := fun k => L * √(5 * a) / 2 ^ (k + 1) with hσdef
  set s : ℝ := √((d : ℝ) + 1) with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = (d : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hσpos : ∀ k, 0 < σ k := fun k => by simp only [hσdef]; positivity
  -- termination of the chain
  obtain ⟨K, hK1, hKsep⟩ := exists_level_sep F p (a := a)
  have hterm : ∀ i ∈ F, v (proj F p a i₀ K i) = v i := by
    intro i hi
    have hmem : proj F p a i₀ K i ∈ F := proj_mem hi₀ hi K
    have hpeq : p (proj F p a i₀ K i) = p i :=
      hKsep _ hmem i hi (norm_proj_sub_lt ha (by omega) hi)
    have h := hv _ hmem i hi
    rw [hpeq, sub_self, norm_zero, mul_zero] at h
    have h0 : ‖v (proj F p a i₀ K i) - v i‖ = 0 := by
      nlinarith [norm_nonneg (v (proj F p a i₀ K i) - v i)]
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  -- size of the increments
  have hwσ : ∀ k, ∀ i ∈ F, ‖w k i‖ ≤ σ k := by
    intro k i hi
    have hd1 := norm_proj_sub_le ha hp hi₀ hi (k + 1)
    have hd0 := norm_proj_sub_le ha hp hi₀ hi k
    have hdist : ‖p (proj F p a i₀ (k + 1) i) - p (proj F p a i₀ k i)‖ ≤
        5 * a / 4 ^ (k + 1) := by
      calc ‖p (proj F p a i₀ (k + 1) i) - p (proj F p a i₀ k i)‖
          = ‖(p (proj F p a i₀ (k + 1) i) - p i) - (p (proj F p a i₀ k i) - p i)‖ := by
            congr 1; abel
        _ ≤ ‖p (proj F p a i₀ (k + 1) i) - p i‖ + ‖p (proj F p a i₀ k i) - p i‖ :=
            norm_sub_le _ _
        _ ≤ a / 4 ^ (k + 1) + a / 4 ^ k := add_le_add hd1 hd0
        _ = 5 * a / 4 ^ (k + 1) := by rw [pow_succ]; field_simp; ring
    have h2 : ((2 : ℝ) ^ (k + 1)) ^ 2 = 4 ^ (k + 1) := by rw [← pow_mul, pow_mul']; norm_num
    have hsq : ‖w k i‖ ^ 2 ≤ σ k ^ 2 := by
      calc ‖w k i‖ ^ 2 ≤ L ^ 2 * ‖p (proj F p a i₀ (k + 1) i) - p (proj F p a i₀ k i)‖ :=
            hv _ (proj_mem hi₀ hi (k + 1)) _ (proj_mem hi₀ hi k)
        _ ≤ L ^ 2 * (5 * a / 4 ^ (k + 1)) := mul_le_mul_of_nonneg_left hdist (sq_nonneg L)
        _ = σ k ^ 2 := by
          simp only [hσdef]
          rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), h2]
          ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (hσpos k).le two_ne_zero).1 hsq
  -- the increments only depend on the cells at levels `k` and `k + 1`
  set fk : ℕ → ι → (Fin d → ℤ) × (Fin d → ℤ) :=
    fun k i => (cell a k (p i), cell a (k + 1) (p i)) with hfk
  have hfib : ∀ k, ∀ i ∈ F, ∀ j ∈ F, fk k i = fk k j → w k i = w k j := by
    intro k i _ j _ h
    simp only [hfk, Prod.mk.injEq] at h
    simp only [hw]
    rw [proj_congr h.1, proj_congr h.2]
  -- counting the increments
  have hlog : ∀ k : ℕ, Real.log (F.image (fk k)).card ≤ 9 * ((d : ℝ) + 1) * ((k : ℝ) + 1) := by
    intro k
    have hsub : F.image (fk k) ⊆ box a k (p i₀) ×ˢ box a (k + 1) (p i₀) := by
      intro c hc
      rw [Finset.mem_image] at hc
      obtain ⟨i, hi, rfl⟩ := hc
      exact Finset.mem_product.2 ⟨cell_mem_box ha k (hp i hi i₀ hi₀),
        cell_mem_box ha (k + 1) (hp i hi i₀ hi₀)⟩
    have hcard : (F.image (fk k)).card ≤ 4 ^ ((2 * k + 3) * d) := by
      calc (F.image (fk k)).card ≤ (box a k (p i₀) ×ˢ box a (k + 1) (p i₀)).card :=
            Finset.card_le_card hsub
        _ = (box a k (p i₀)).card * (box a (k + 1) (p i₀)).card := Finset.card_product _ _
        _ ≤ (4 ^ (k + 1)) ^ d * (4 ^ (k + 1 + 1)) ^ d :=
            Nat.mul_le_mul (card_box_le a k _) (card_box_le a (k + 1) _)
        _ = 4 ^ ((2 * k + 3) * d) := by
            rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
    have hpos : (0 : ℝ) < (F.image (fk k)).card := by
      exact_mod_cast (hFne.image _).card_pos
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
    calc Real.log (F.image (fk k)).card ≤ Real.log ((4 : ℝ) ^ ((2 * k + 3) * d)) :=
          Real.log_le_log hpos (by exact_mod_cast hcard)
      _ = (((2 * k + 3) * d : ℕ) : ℝ) * Real.log 4 := Real.log_pow _ _
      _ ≤ 9 * ((d : ℝ) + 1) * ((k : ℝ) + 1) := by
          push_cast
          have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          nlinarith [mul_le_mul_of_nonneg_left hlog4 (by positivity : (0 : ℝ) ≤ (2 * k + 3) * d)]
  -- bound at each level
  have hlev : ∀ k ∈ Finset.range K,
      ∫ x, (⨆ i : F, ⟪w k i, x⟫) ∂stdGaussian E ≤ 10 * s * σ k * ((k : ℝ) + 1) := by
    intro k _
    have hl : 0 < s / σ k := div_pos hs (hσpos k)
    have h := integral_iSup_inner_le_of_fiber F hFne (fk k) (w k) (hfib k) hl (hwσ k)
    refine h.trans ?_
    rw [div_le_iff₀ hl]
    have hσne : σ k ≠ 0 := (hσpos k).ne'
    have e1 : (s / σ k) ^ 2 * σ k ^ 2 = s ^ 2 := by field_simp
    have e2 : 10 * s * σ k * ((k : ℝ) + 1) * (s / σ k) = 10 * s ^ 2 * ((k : ℝ) + 1) := by
      rw [mul_div_assoc', div_eq_iff hσne]; ring
    rw [e1, e2, hs2]
    have := hlog k
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [mul_nonneg hd hk]
  -- pointwise chaining
  have hpt : ∀ x : E, (⨆ i : F, ⟪v i - v i₀, x⟫ + (0 : ι → ℝ) i) ≤
      ∑ k ∈ Finset.range K, ⨆ i : F, ⟪w k i, x⟫ := by
    intro x
    have : Nonempty F := hFne.to_subtype
    refine ciSup_le fun i => ?_
    have htel : ∑ k ∈ Finset.range K, w k i =
        v (proj F p a i₀ K i) - v (proj F p a i₀ 0 i) :=
      Finset.sum_range_sub (fun k => v (proj F p a i₀ k i)) K
    rw [hterm i i.2, proj_zero] at htel
    rw [Pi.zero_apply, add_zero, ← htel, sum_inner]
    exact Finset.sum_le_sum fun k _ =>
      le_ciSup (f := fun j : F => ⟪w k j, x⟫) (Set.finite_range _).bddAbove i
  have hint : ∀ k, Integrable (fun x => ⨆ i : F, ⟪w k i, x⟫) (stdGaussian E) :=
    fun k => integrable_iSup_inner F (w k)
  have hint0 : Integrable (fun x => ⨆ i : F, ⟪v i - v i₀, x⟫ + (0 : ι → ℝ) i)
      (stdGaussian E) := integrable_iSup_inner_add F (fun i => v i - v i₀) 0
  have h1 : vecExpectedMax F (fun i => v i - v i₀) 0 ≤
      ∫ x, (∑ k ∈ Finset.range K, ⨆ i : F, ⟪w k i, x⟫) ∂stdGaussian E :=
    integral_mono hint0 (integrable_finsetSum _ fun k _ => hint k) hpt
  rw [integral_finsetSum _ fun k _ => hint k] at h1
  have hsum2 : ∑ k ∈ Finset.range K, ((k : ℝ) + 1) / 2 ^ (k + 1) ≤ 2 := by
    rw [sum_range_succ_div_two_pow]
    have : 0 ≤ ((K : ℝ) + 2) / 2 ^ K := by positivity
    linarith
  have hc : 0 ≤ 10 * s * (L * √(5 * a)) := by positivity
  calc vecExpectedMax F (fun i => v i - v i₀) 0
      ≤ ∑ k ∈ Finset.range K, ∫ x, (⨆ i : F, ⟪w k i, x⟫) ∂stdGaussian E := h1
    _ ≤ ∑ k ∈ Finset.range K, 10 * s * σ k * ((k : ℝ) + 1) := Finset.sum_le_sum hlev
    _ = 10 * s * (L * √(5 * a)) * ∑ k ∈ Finset.range K, ((k : ℝ) + 1) / 2 ^ (k + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hσdef]
        ring
    _ ≤ 10 * s * (L * √(5 * a)) * 2 := mul_le_mul_of_nonneg_left hsum2 hc
    _ = 20 * √5 * L * √((d + 1) * a) := by
        rw [hsdef, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5) a,
          Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (d : ℝ) + 1) a]
        ring

/-- **Chaining on a box.**  If the parameters `p i ∈ ℝ^d` (sup norm) have diameter at most `a`
on `F` and `‖v i - v j‖² ≤ L² ‖p i - p j‖` on `F`, then for `i₀ ∈ F`,
`E max_{i ∈ F} ⟪v i - v i₀, x⟫ ≤ 20 √5 · L √((d + 1) a)`. -/
theorem chainingBox_bound {d : ℕ} (F : Finset ι) (p : ι → Fin d → ℝ) (v : ι → E) {L a : ℝ}
    (hL : 0 ≤ L) (hp : ∀ i ∈ F, ∀ j ∈ F, ‖p i - p j‖ ≤ a)
    (hv : ∀ i ∈ F, ∀ j ∈ F, ‖v i - v j‖ ^ 2 ≤ L ^ 2 * ‖p i - p j‖) {i₀ : ι} (hi₀ : i₀ ∈ F) :
    vecExpectedMax F (fun i => v i - v i₀) 0 ≤ 20 * √5 * L * √((d + 1) * a) := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (hp i₀ hi₀ i₀ hi₀)
  have hRHS : 0 ≤ 20 * √5 * L * √((d + 1) * a) := by positivity
  have hdeg : (∀ i ∈ F, L ^ 2 * ‖p i - p i₀‖ = 0) →
      vecExpectedMax F (fun i => v i - v i₀) 0 ≤ 20 * √5 * L * √((d + 1) * a) := by
    intro h0
    have hv0 : ∀ i ∈ F, v i = v i₀ := by
      intro i hi
      have h := hv i hi i₀ hi₀
      rw [h0 i hi] at h
      have hn : ‖v i - v i₀‖ = 0 := by nlinarith [norm_nonneg (v i - v i₀)]
      exact sub_eq_zero.1 (norm_eq_zero.1 hn)
    rw [vecExpectedMax_sub_eq_zero F v i₀ hv0]
    exact hRHS
  rcases hL.eq_or_lt with hL0 | hLpos
  · exact hdeg fun i _ => by rw [← hL0]; ring
  rcases ha0.eq_or_lt with ha0' | hapos
  · refine hdeg fun i hi => ?_
    have : ‖p i - p i₀‖ = 0 :=
      le_antisymm ((hp i hi i₀ hi₀).trans ha0'.symm.le) (norm_nonneg _)
    rw [this, mul_zero]
  exact chainingBox_bound_pos F p v hLpos hapos hp hv hi₀

end Main

end ChainBox

/-- **Node `G4`** (`Blueprint.Draft.ChainingBox`), with `C = 20 √5`. -/
theorem chainingBox : Blueprint.Draft.ChainingBox := by
  refine ⟨20 * √5, ?_⟩
  intro ι E _ _ _ _ _ d F p v L a hL hp hv i₀ hi₀
  exact ChainBox.chainingBox_bound F p v hL hp hv hi₀

end LQGDimension
