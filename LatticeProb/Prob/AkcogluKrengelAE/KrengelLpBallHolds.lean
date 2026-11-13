import LatticeProb.Prob.AkcogluKrengelAE.KrengelLpBallReduction
import LatticeProb.Prob.AkcogluKrengelAE.AnchoredBoxMaximalHolds
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodicAllFlip

/-!
# Krengel's multiparameter `Lᵖ` maximal bound for `ℓ¹`-ball averages

For `p > 1` there is a constant `C`, independent of the probability space, the action and the
function, with `∫⁻ (⨆_{1 ≤ R} avg (B¹_R(0)) (f ∘ T_·))ᵖ ≤ C ∫⁻ fᵖ` for every measure-preserving
additive action `T` of `ℤ^d` and every measurable `f : Ω → ℝ≥0∞`: this is `KrengelLpBall d`.

The `ℓ¹`-ball average is at most `(2d)^d` times the largest of the `2^d` orthant-box averages
(`l1BallMax_le_orthantBoxMax`). The orthant box with sign pattern `s` is the image of the box
`∏ᵢ [0, mᵢ)` under the reflection of the negative coordinates followed by the shift `-1` in those
coordinates, so its average along `T` at `ω` is the box average along the reflected action at the
shifted point. The `Lᵖ` box maximal inequality, with the constant `((p / (p - 1))ᵖ)ᵈ` of Wiener's
maximal theorem applied once per coordinate, bounds each of the `2^d` terms. Truncating `f` at
the levels `M ∈ ℕ` and monotone convergence pass from bounded real functions to `ℝ≥0∞`-valued
ones.

## Main results

* `lintegral_iSup_boxAvg_rpow_le_uniform`: the `Lᵖ` box maximal inequality with the explicit
  constant `((p / (p - 1))ᵖ)^{|s|}`;
* `avg_orthantBox_eq`: the orthant-box average as a box average after reflection and shift;
* `lintegral_l1BallMax_rpow_le_of_real`: the bound for bounded real functions;
* `krengelLpBall_holds`: `KrengelLpBall d` for every `d`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace LatticeProb

variable {d : ℕ}

/-- **The `Lᵖ` box maximal inequality with a uniform constant.**  For `p > 1`, a
measure-preserving additive action `σ` and a measurable `f ≥ 0`, the maximal function of the box
averages over `∏_{i ∈ s} [0, mᵢ)` satisfies
`∫⁻ (sup_m boxAvg σ f s m)ᵖ ≤ ((p / (p - 1))ᵖ)^{|s|} ∫⁻ fᵖ`. -/
theorem lintegral_iSup_boxAvg_rpow_le_uniform {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : Site d → Ω → Ω} (hσ : ∀ z, MeasurePreserving (σ z) μ μ)
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) {p : ℝ} (hp : 1 < p) (s : Finset (Fin d))
    {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) :
    ∫⁻ ω, (⨆ m : Fin d → ℕ, ENNReal.ofReal (boxAvg σ f s m ω)) ^ p ∂μ ≤
      ENNReal.ofReal (((p / (p - 1)) ^ p) ^ s.card) * ∫⁻ ω, ENNReal.ofReal (f ω) ^ p ∂μ := by
  have hC₁ : 0 ≤ (p / (p - 1)) ^ p :=
    Real.rpow_nonneg (div_nonneg (by linarith) (by linarith)) _
  have hB : ∀ T : Ω → Ω, MeasurePreserving T μ μ → ∀ g : Ω → ℝ≥0∞, Measurable g →
      ∫⁻ x, (⨆ N : ℕ, (N : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range N, g (T^[k] x)) ^ p ∂μ ≤
        ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ x, g x ^ p ∂μ := fun T hT g hg =>
    marcinkiewicz_abstract μ (birkhoffMax T g) g p hp
      (measurable_birkhoffMax hT.measurable hg) hg (birkhoffMax_weakType μ hT hg)
  induction s using Finset.induction_on with
  | empty =>
    simp only [boxAvg_empty, ciSup_const, Finset.card_empty, pow_zero, ENNReal.ofReal_one,
      one_mul]
    have hm : Measurable fun ω => ENNReal.ofReal (f ω) ^ p := hf.ennreal_ofReal.pow_const p
    exact ((hσ (natToSite 0)).lintegral_comp hm).le
  | @insert i s hi ih =>
    let G : Ω → ℝ≥0∞ := fun ω => ⨆ m : Fin d → ℕ, ENNReal.ofReal (boxAvg σ f s m ω)
    have hGm : Measurable G :=
      Measurable.iSup fun m => (measurable_boxAvg hσ hf s m).ennreal_ofReal
    have hle : ∀ ω, (⨆ m : Fin d → ℕ, ENNReal.ofReal (boxAvg σ f (insert i s) m ω)) ≤
        ⨆ n : ℕ, (n : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range n, G ((σ (unit i))^[k] ω) := by
      intro ω
      refine iSup_le fun m => ?_
      rw [boxAvg_insert_eq_bAvg_boxAvg hσadd f s i hi m ω]
      refine (ofReal_bAvg_le (boxAvg_nonneg hf0 s m) G
        (fun ω' => le_iSup (fun m' : Fin d → ℕ => ENNReal.ofReal (boxAvg σ f s m' ω')) m)
        (m i) ω).trans ?_
      exact le_iSup (fun n : ℕ => (n : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range n,
        G ((σ (unit i))^[k] ω)) (m i)
    calc ∫⁻ ω, (⨆ m : Fin d → ℕ, ENNReal.ofReal (boxAvg σ f (insert i s) m ω)) ^ p ∂μ
        ≤ ∫⁻ ω, (⨆ n : ℕ, (n : ℝ≥0∞)⁻¹ *
            ∑ k ∈ Finset.range n, G ((σ (unit i))^[k] ω)) ^ p ∂μ :=
          lintegral_mono fun ω => ENNReal.rpow_le_rpow (hle ω) (by linarith)
      _ ≤ ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ ω, G ω ^ p ∂μ := hB (σ (unit i)) (hσ _) G hGm
      _ ≤ ENNReal.ofReal ((p / (p - 1)) ^ p) * (ENNReal.ofReal (((p / (p - 1)) ^ p) ^ s.card) *
            ∫⁻ ω, ENNReal.ofReal (f ω) ^ p ∂μ) := mul_le_mul_right ih _
      _ = ENNReal.ofReal (((p / (p - 1)) ^ p) ^ (insert i s).card) *
            ∫⁻ ω, ENNReal.ofReal (f ω) ^ p ∂μ := by
          rw [Finset.card_insert_of_notMem hi, pow_succ', ENNReal.ofReal_mul hC₁, mul_assoc]

/-! ### Orthant boxes as reflected boxes -/

/-- The coordinates in which the orthant `s` is negative. -/
def orthantNegSet (s : Fin d → Bool) : Finset (Fin d) :=
  Finset.univ.filter fun i => s i = false

/-- The shift `-1` in the negative coordinates of the orthant `s`. -/
def orthantShift (s : Fin d → Bool) : Site d :=
  fun i => if s i then 0 else -1

/-- The side lengths of the orthant box `orthantBox s R`: `R + 1` in the positive coordinates
and `R` in the negative ones. -/
def orthantSide (s : Fin d → Bool) (R : ℕ) : Fin d → ℕ :=
  fun i => if s i then R + 1 else R

theorem mem_intBox_univ {m : Fin d → ℕ} {y : Site d} :
    y ∈ intBox Finset.univ m ↔ ∀ i, 0 ≤ y i ∧ y i < (m i : ℤ) := by
  simp [intBox, Fintype.mem_piFinset, Finset.mem_Ico]

theorem flipSubset_add_orthantShift_mem {s : Fin d → Bool} {R : ℕ} {y : Site d}
    (hy : y ∈ intBox Finset.univ (orthantSide s R)) :
    flipSubset (orthantNegSet s) y + orthantShift s ∈ orthantBox s R := by
  rw [mem_intBox_univ] at hy
  rw [mem_orthantBox]
  intro i
  have h := hy i
  cases hs : s i <;>
    simp [hs, orthantSide, orthantNegSet, orthantShift, flipSubset] at h ⊢ <;> omega

theorem flipSubset_sub_orthantShift_mem {s : Fin d → Bool} {R : ℕ} {x : Site d}
    (hx : x ∈ orthantBox s R) :
    flipSubset (orthantNegSet s) (x - orthantShift s) ∈ intBox Finset.univ (orthantSide s R) := by
  rw [mem_orthantBox] at hx
  rw [mem_intBox_univ]
  intro i
  have h := hx i
  cases hs : s i <;>
    simp [hs, orthantSide, orthantNegSet, orthantShift, flipSubset] at h ⊢ <;> omega

/-- **The orthant box is a reflected and shifted box**, at the level of sums. -/
theorem sum_orthantBox_eq_sum_intBox {M : Type*} [AddCommMonoid M] (s : Fin d → Bool) (R : ℕ)
    (F : Site d → M) :
    ∑ x ∈ orthantBox s R, F x =
      ∑ y ∈ intBox Finset.univ (orthantSide s R),
        F (flipSubset (orthantNegSet s) y + orthantShift s) := by
  symm
  refine Finset.sum_nbij' (fun y => flipSubset (orthantNegSet s) y + orthantShift s)
    (fun x => flipSubset (orthantNegSet s) (x - orthantShift s))
    (fun y hy => flipSubset_add_orthantShift_mem hy)
    (fun x hx => flipSubset_sub_orthantShift_mem hx) ?_ ?_ fun _ _ => rfl
  · intro y _
    simp only [add_sub_cancel_right, flipSubset_involutive]
  · intro x _
    simp only [flipSubset_involutive, sub_add_cancel]

/-- **The orthant-box average is a box average after reflection and shift.** -/
theorem avg_orthantBox_eq (s : Fin d → Bool) (R : ℕ) (F : Site d → ℝ≥0∞) :
    avg (orthantBox s R) F =
      avg (intBox Finset.univ (orthantSide s R))
        (fun y => F (flipSubset (orthantNegSet s) y + orthantShift s)) := by
  have hcard : (orthantBox s R).card = (intBox Finset.univ (orthantSide s R)).card := by
    simpa using sum_orthantBox_eq_sum_intBox s R (fun _ => (1 : ℕ))
  unfold avg
  rw [hcard, sum_orthantBox_eq_sum_intBox]

/-- The `ℝ≥0∞` average over the box `∏ᵢ [0, mᵢ)` of a nonnegative function is at most its real
box average. -/
theorem avg_intBox_ofReal_le {Ω : Type*} [MeasurableSpace Ω] (σ : Site d → Ω → Ω) {g : Ω → ℝ}
    (hg0 : ∀ ω, 0 ≤ g ω) (m : Fin d → ℕ) (ω : Ω) :
    avg (intBox Finset.univ m) (fun y => ENNReal.ofReal (g (σ y ω))) ≤
      ENNReal.ofReal (boxAvg σ g Finset.univ m ω) := by
  have hcard : (intBox Finset.univ m).card = ∏ i, m i := by
    simp [intBox, Fintype.card_piFinset, Int.card_Ico]
  have hsum : ∑ y ∈ intBox Finset.univ m, ENNReal.ofReal (g (σ y ω)) =
      ENNReal.ofReal (∑ w ∈ boxGridSet Finset.univ m, g (σ (natToSite w) ω)) := by
    rw [sum_boxGridSet_eq_sum_intBox Finset.univ m (fun x => g (σ x ω)),
      ENNReal.ofReal_sum_of_nonneg fun _ _ => hg0 _]
  rcases Nat.eq_zero_or_pos (∏ i, m i) with h0 | hpos
  · have hempty : intBox Finset.univ m = ∅ := Finset.card_eq_zero.1 (hcard.trans h0)
    simp [avg, hempty]
  · have hP : (0 : ℝ) < ∏ i, (m i : ℝ) := by exact_mod_cast hpos
    unfold avg
    rw [hsum, hcard, boxAvg, ENNReal.ofReal_div_of_pos hP, div_eq_mul_inv, mul_comm,
      ← ENNReal.ofReal_natCast, Nat.cast_prod]

/-- **Orthant-box maximal against the reflected box maximal**, pointwise. -/
theorem iSup_avg_orthantBox_le {Ω : Type*} [MeasurableSpace Ω] {T : Site d → Ω → Ω}
    (hadd : ∀ x y, T (x + y) = T x ∘ T y) {g : Ω → ℝ} (hg0 : ∀ ω, 0 ≤ g ω)
    (s : Fin d → Bool) (ω : Ω) :
    ⨆ R : ℕ, avg (orthantBox s R) (fun y => ENNReal.ofReal (g (T y ω))) ≤
      ⨆ m : Fin d → ℕ, ENNReal.ofReal
        (boxAvg (reflectActionS T (orthantNegSet s)) g Finset.univ m (T (orthantShift s) ω)) := by
  refine iSup_le fun R => ?_
  rw [avg_orthantBox_eq]
  have hT : ∀ y, T (flipSubset (orthantNegSet s) y + orthantShift s) ω =
      reflectActionS T (orthantNegSet s) y (T (orthantShift s) ω) := fun y => by
    rw [hadd]; rfl
  simp_rw [hT]
  exact (avg_intBox_ofReal_le _ hg0 _ _).trans (le_iSup (fun m : Fin d → ℕ => ENNReal.ofReal
    (boxAvg (reflectActionS T (orthantNegSet s)) g Finset.univ m (T (orthantShift s) ω)))
      (orthantSide s R))

/-- The `p`-th power of a finite supremum is at most the sum of the `p`-th powers. -/
theorem univ_sup_rpow_le_sum {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ≥0∞) {p : ℝ} :
    (Finset.univ.sup a) ^ p ≤ ∑ i, a i ^ p := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty a
  rw [hi]
  exact Finset.single_le_sum (f := fun i => a i ^ p) (fun _ _ => zero_le) (Finset.mem_univ i)

/-! ### The `ℓ¹`-ball maximal bound -/

/-- **The `ℓ¹`-ball `Lᵖ` maximal bound for nonnegative real functions**, with the constant
`((2d)^d)ᵖ · 2^d · ((p / (p - 1))ᵖ)^d`. -/
theorem lintegral_l1BallMax_rpow_le_of_real (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Site d → Ω → Ω}
    (hT : ∀ x, MeasurePreserving (T x) μ μ) (hadd : ∀ x y, T (x + y) = T x ∘ T y)
    {p : ℝ} (hp : 1 < p) {g : Ω → ℝ} (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω) :
    ∫⁻ ω, l1BallMax T (fun x => ENNReal.ofReal (g x)) ω ^ p ∂μ ≤
      ENNReal.ofReal (((2 * d : ℝ) ^ d) ^ p * (2 ^ d * ((p / (p - 1)) ^ p) ^ d)) *
        ∫⁻ ω, ENNReal.ofReal (g ω) ^ p ∂μ := by
  have hp0 : (0 : ℝ) ≤ p := by linarith
  set C₁ : ℝ := (p / (p - 1)) ^ p with hC₁def
  have hC₁ : 0 ≤ C₁ := Real.rpow_nonneg (div_nonneg (by linarith) (by linarith)) _
  set K : ℝ := (2 * d : ℝ) ^ d with hKdef
  have hK : 0 ≤ K := by positivity
  let σ : (Fin d → Bool) → Site d → Ω → Ω := fun s => reflectActionS T (orthantNegSet s)
  have hσ : ∀ s z, MeasurePreserving (σ s z) μ μ := fun s z => hT _
  have hσadd : ∀ s z w ω, σ s (z + w) ω = σ s z (σ s w ω) := fun s z w ω => by
    show T (flipSubset _ (z + w)) ω = T (flipSubset _ z) (T (flipSubset _ w) ω)
    rw [flipSubset_add, hadd]; rfl
  let G : (Fin d → Bool) → Ω → ℝ≥0∞ := fun s ω' =>
    ⨆ m : Fin d → ℕ, ENNReal.ofReal (boxAvg (σ s) g Finset.univ m ω')
  have hGm : ∀ s, Measurable (G s) := fun s =>
    Measurable.iSup fun m => (measurable_boxAvg (hσ s) hg Finset.univ m).ennreal_ofReal
  let H : (Fin d → Bool) → Ω → ℝ≥0∞ := fun s ω => G s (T (orthantShift s) ω)
  have hHm : ∀ s, Measurable fun ω => H s ω ^ p := fun s =>
    ((hGm s).comp (hT (orthantShift s)).measurable).pow_const p
  have hpt : ∀ ω, l1BallMax T (fun x => ENNReal.ofReal (g x)) ω ^ p ≤
      ENNReal.ofReal K ^ p * ∑ s, H s ω ^ p := by
    intro ω
    have h1 := l1BallMax_le_orthantBoxMax hd T (fun x => ENNReal.ofReal (g x)) ω
    have h2 : (Finset.univ.sup fun s : Fin d → Bool =>
          ⨆ R : ℕ, avg (orthantBox s R) (fun y => ENNReal.ofReal (g (T y ω)))) ≤
        Finset.univ.sup fun s => H s ω :=
      Finset.sup_mono_fun fun s _ => iSup_avg_orthantBox_le hadd hg0 s ω
    have hKe : (((2 * d) ^ d : ℕ) : ℝ≥0∞) = ENNReal.ofReal K := by
      rw [hKdef, ← ENNReal.ofReal_natCast]; push_cast; rfl
    calc l1BallMax T (fun x => ENNReal.ofReal (g x)) ω ^ p
        ≤ (ENNReal.ofReal K * Finset.univ.sup fun s => H s ω) ^ p := by
          rw [← hKe]
          exact ENNReal.rpow_le_rpow (h1.trans (mul_le_mul_right h2 _)) hp0
      _ = ENNReal.ofReal K ^ p * (Finset.univ.sup fun s => H s ω) ^ p :=
          ENNReal.mul_rpow_of_nonneg _ _ hp0
      _ ≤ ENNReal.ofReal K ^ p * ∑ s, H s ω ^ p :=
          mul_le_mul_right (univ_sup_rpow_le_sum (fun s => H s ω)) _
  have hHint : ∀ s, ∫⁻ ω, H s ω ^ p ∂μ ≤
      ENNReal.ofReal (C₁ ^ d) * ∫⁻ ω, ENNReal.ofReal (g ω) ^ p ∂μ := by
    intro s
    have hcomp : ∫⁻ ω, H s ω ^ p ∂μ = ∫⁻ ω, G s ω ^ p ∂μ :=
      (hT (orthantShift s)).lintegral_comp ((hGm s).pow_const p)
    rw [hcomp]
    have := lintegral_iSup_boxAvg_rpow_le_uniform (hσ s) (hσadd s) hp Finset.univ hg hg0
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hKp : ENNReal.ofReal K ^ p = ENNReal.ofReal (K ^ p) :=
    ENNReal.ofReal_rpow_of_nonneg hK hp0
  calc ∫⁻ ω, l1BallMax T (fun x => ENNReal.ofReal (g x)) ω ^ p ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal K ^ p * ∑ s, H s ω ^ p ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal K ^ p * ∑ s, ∫⁻ ω, H s ω ^ p ∂μ := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun s _ => hHm s),
          lintegral_finsetSum _ fun s _ => hHm s]
    _ ≤ ENNReal.ofReal K ^ p *
          ∑ _s : Fin d → Bool, ENNReal.ofReal (C₁ ^ d) * ∫⁻ ω, ENNReal.ofReal (g ω) ^ p ∂μ :=
        mul_le_mul_right (Finset.sum_le_sum fun s _ => hHint s) _
    _ = ENNReal.ofReal (K ^ p * (2 ^ d * C₁ ^ d)) * ∫⁻ ω, ENNReal.ofReal (g ω) ^ p ∂μ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, hKp, ENNReal.ofReal_mul (Real.rpow_nonneg hK _),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_ofNat]
        push_cast
        ring

/-- Monotonicity of the `ℓ¹`-ball maximal function in the function. -/
theorem l1BallMax_mono {Ω : Type*} [MeasurableSpace Ω] (T : Site d → Ω → Ω)
    {f f' : Ω → ℝ≥0∞} (h : f ≤ f') : l1BallMax T f ≤ l1BallMax T f' := fun ω =>
  iSup_mono fun _ => iSup_mono fun _ => avg_mono fun y => h (T y ω)

/-- An average of a constant is at most the constant. -/
theorem avg_const_le (B : Finset (Site d)) (a : ℝ≥0∞) : avg B (fun _ => a) ≤ a := by
  unfold avg
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
  rcases eq_or_ne B.card 0 with h | h
  · simp [h]
  · rw [ENNReal.inv_mul_cancel (by exact_mod_cast h) (ENNReal.natCast_ne_top _), one_mul]

/-- **Krengel's multiparameter `Lᵖ` maximal bound for `ℓ¹`-ball averages** holds in every
dimension. -/
theorem krengelLpBall_holds (d : ℕ) : KrengelLpBall d := by
  intro p hp
  have hp0 : (0 : ℝ) ≤ p := by linarith
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, zero_le_one, ?_⟩
    intro Ω _ μ _ T hT _ f hf
    have hpt : ∀ ω, (⨆ (R : ℕ) (_ : 1 ≤ R),
        avg (l1Ball (0 : Site 0) R) (fun y => f (T y ω))) ≤ f (T 0 ω) := by
      intro ω
      refine iSup_le fun _ => iSup_le fun _ => ?_
      have hc : (fun y : Site 0 => f (T y ω)) = fun _ => f (T 0 ω) := by
        funext y; rw [Subsingleton.elim y 0]
      rw [hc]
      exact avg_const_le _ _
    calc ∫⁻ ω, (⨆ (R : ℕ) (_ : 1 ≤ R),
          avg (l1Ball (0 : Site 0) R) (fun y => f (T y ω))) ^ p ∂μ
        ≤ ∫⁻ ω, f (T 0 ω) ^ p ∂μ := lintegral_mono fun ω => ENNReal.rpow_le_rpow (hpt ω) hp0
      _ = ∫⁻ ω, f ω ^ p ∂μ := (hT 0).lintegral_comp (hf.pow_const p)
      _ = ENNReal.ofReal 1 * ∫⁻ ω, f ω ^ p ∂μ := by rw [ENNReal.ofReal_one, one_mul]
  · refine ⟨((2 * d : ℝ) ^ d) ^ p * (2 ^ d * ((p / (p - 1)) ^ p) ^ d), ?_, ?_⟩
    · have : 0 ≤ (p / (p - 1)) ^ p :=
        Real.rpow_nonneg (div_nonneg (by linarith) (by linarith)) _
      positivity
    intro Ω _ μ _ T hT hadd f hf
    set C : ℝ := ((2 * d : ℝ) ^ d) ^ p * (2 ^ d * ((p / (p - 1)) ^ p) ^ d)
    let fM : ℕ → Ω → ℝ≥0∞ := fun M x => min (f x) (M : ℝ≥0∞)
    have hfM : ∀ M x, ENNReal.ofReal ((fM M x).toReal) = fM M x := fun M x =>
      ENNReal.ofReal_toReal (lt_of_le_of_lt (min_le_right _ _) (ENNReal.natCast_lt_top M)).ne
    have hLm : ∀ M, Measurable (l1BallMax T (fM M)) := fun M =>
      measurable_l1BallMax (fun x => (hT x).measurable) (hf.min measurable_const)
    have hmono : Monotone fun M => l1BallMax T (fM M) := fun M N hMN =>
      l1BallMax_mono T fun x => min_le_min le_rfl (by exact_mod_cast hMN)
    have hbound : ∀ M, ∫⁻ ω, l1BallMax T (fM M) ω ^ p ∂μ ≤
        ENNReal.ofReal C * ∫⁻ ω, f ω ^ p ∂μ := by
      intro M
      have h := lintegral_l1BallMax_rpow_le_of_real hd hT hadd hp
        (g := fun x => (fM M x).toReal) (hf.min measurable_const).ennreal_toReal
        (fun _ => ENNReal.toReal_nonneg)
      simp only [hfM] at h
      refine h.trans (mul_le_mul_right (lintegral_mono fun ω => ?_) _)
      exact ENNReal.rpow_le_rpow (min_le_left _ _) hp0
    show ∫⁻ ω, l1BallMax T f ω ^ p ∂μ ≤ ENNReal.ofReal C * ∫⁻ ω, f ω ^ p ∂μ
    have hiSup : ∀ ω, l1BallMax T f ω ^ p = ⨆ M : ℕ, l1BallMax T (fM M) ω ^ p := by
      intro ω
      rw [congr_fun (l1BallMax_eq_iSup_min T f) ω]
      exact (ENNReal.orderIsoRpow p (by linarith)).map_iSup _
    simp_rw [hiSup]
    rw [lintegral_iSup (fun M => (hLm M).pow_const p)
      (fun M N hMN ω => ENNReal.rpow_le_rpow (hmono hMN ω) hp0)]
    exact iSup_le hbound

end LatticeProb
