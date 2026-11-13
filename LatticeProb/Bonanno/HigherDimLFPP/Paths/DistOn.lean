/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Paths.DistOn at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Paths.Basic

/-!
# Internal LFPP distances on subdomains of `ℝ^d`

Packet P-X1, target T1 (audit HA5, §1 conventions and Details D1; DGZ §2, `D_h(x, y; S)`).

For a field `φ`, a set `V ⊆ ℝ^d` and points `x, y`,
`lfppDistOn ζ φ V x y = inf ∫₀¹ e^{ζ φ(γ)} |γ'|` over piecewise `C¹` paths `γ : [0,1] → V` from
`x` to `y` (real-valued; the infimum of the empty family is the junk value `0`, so the joinability
predicate `PcwJoined V x y` appears as a hypothesis where it matters).

* `lfppDistance_eq_lfppDistOn`: the frozen `lfppDistance d ζ φ` is
  `lfppDistOn ζ φ (cube d) 0 (e₁ d)`.
* `PcwJoined.of_convex`: points of a convex set are joined by the segment.
* `lfppDistOn_mono` (monotone in `V`), `lfppDistOn_triangle` (concatenation),
  `lfppDistOn_comm`, `lfppDistOn_self`, segment and chain bounds (`lfppDistOn_le_sum`).
* Lower bounds: `IsPcwC1Path.exp_mul_norm_sub_le_lfppLength` (cost ≥ `|y - x| e^{min ζφ}` along the
  path) and the exit-time bound `IsPcwC1Path.exp_mul_le_lfppLength` (cost ≥ `r e^{m}` if
  `ζ φ ≥ m` on `B̄(x, r)`, `r ≤ |y - x|`), hence `lfppDistOn_pos` for continuous `φ` and `x ≠ y`.

2D source: `LQGMetric/LFPP/DistOn.lean` (`lfppDOn`, `ℝ≥0∞`-valued, ℂ).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLFPP

variable {d : ℕ}

/-- `x` and `y` are joined inside `V` by a piecewise `C¹` path. -/
def PcwJoined (V : Set (Rd d)) (x y : Rd d) : Prop :=
  ∃ γ : ℝ → Rd d, IsPcwC1Path γ x y ∧ MapsTo γ (Icc 0 1) V

/-- The internal LFPP distance `D^ζ_V(x, y)(φ) = inf ∫₀¹ e^{ζ φ(γ t)} |γ'(t)| dt` over piecewise
`C¹` paths `γ : [0,1] → V` from `x` to `y` (junk value `0` if there is no such path). -/
def lfppDistOn (ζ : ℝ) (φ : Rd d → ℝ) (V : Set (Rd d)) (x y : Rd d) : ℝ :=
  ⨅ γ : {γ : ℝ → Rd d // IsPcwC1Path γ x y ∧ MapsTo γ (Icc 0 1) V}, lfppLength ζ φ γ.1

section Joined

variable {V W : Set (Rd d)} {x y z : Rd d}

theorem PcwJoined.nonempty (h : PcwJoined V x y) :
    Nonempty {γ : ℝ → Rd d // IsPcwC1Path γ x y ∧ MapsTo γ (Icc 0 1) V} :=
  let ⟨γ, hγ⟩ := h; ⟨⟨γ, hγ⟩⟩
theorem PcwJoined.mem_left (h : PcwJoined V x y) : x ∈ V :=
  let ⟨_, hγ, hV⟩ := h; (hγ.mem_of_mapsTo hV).1

theorem PcwJoined.mono (h : PcwJoined V x y) (hVW : V ⊆ W) : PcwJoined W x y :=
  let ⟨γ, hγ, hV⟩ := h; ⟨γ, hγ, hV.mono_right hVW⟩

theorem PcwJoined.symm (h : PcwJoined V x y) : PcwJoined V y x :=
  let ⟨γ, hγ, hV⟩ := h; ⟨revPath γ, hγ.revPath, mapsTo_revPath hV⟩

theorem PcwJoined.trans (h₁ : PcwJoined V x y) (h₂ : PcwJoined V y z) : PcwJoined V x z :=
  let ⟨γ₁, hγ₁, hV₁⟩ := h₁
  let ⟨γ₂, hγ₂, hV₂⟩ := h₂
  ⟨concatPath γ₁ γ₂, hγ₁.concat hγ₂, mapsTo_concatPath hV₁ hV₂⟩

/-- Two points of a convex set are joined by the segment. -/
theorem PcwJoined.of_convex (hV : Convex ℝ V) (hx : x ∈ V) (hy : y ∈ V) : PcwJoined V x y :=
  ⟨segPath x y, isPcwC1Path_segPath x y, mapsTo_segPath hV hx hy⟩

theorem PcwJoined.refl (hx : x ∈ V) : PcwJoined V x x :=
  ⟨segPath x x, isPcwC1Path_segPath x x, fun u _ => by simp [segPath, hx]⟩

end Joined

section Basic

variable {ζ : ℝ} {φ : Rd d → ℝ} {V W : Set (Rd d)} {x y z : Rd d}

theorem bddBelow_range_lfppLength (ζ : ℝ) (φ : Rd d → ℝ) {ι : Sort*} (f : ι → ℝ → Rd d) :
    BddBelow (range fun i => lfppLength ζ φ (f i)) :=
  ⟨0, by rintro _ ⟨i, rfl⟩; exact lfppLength_nonneg ζ φ (f i)⟩

theorem lfppDistOn_nonneg (ζ : ℝ) (φ : Rd d → ℝ) (V : Set (Rd d)) (x y : Rd d) :
    0 ≤ lfppDistOn ζ φ V x y :=
  Real.iInf_nonneg fun γ => lfppLength_nonneg ζ φ γ.1

/-- The internal distance is at most the length of any admissible path. -/
theorem lfppDistOn_le_lfppLength {γ : ℝ → Rd d} (hγ : IsPcwC1Path γ x y)
    (hV : MapsTo γ (Icc 0 1) V) : lfppDistOn ζ φ V x y ≤ lfppLength ζ φ γ :=
  ciInf_le (bddBelow_range_lfppLength ζ φ fun γ :
    {γ : ℝ → Rd d // IsPcwC1Path γ x y ∧ MapsTo γ (Icc 0 1) V} => γ.1) ⟨γ, hγ, hV⟩

/-- A lower bound valid for every admissible path is a lower bound for the internal distance. -/
theorem le_lfppDistOn (hj : PcwJoined V x y) {c : ℝ}
    (h : ∀ γ : ℝ → Rd d, IsPcwC1Path γ x y → MapsTo γ (Icc 0 1) V → c ≤ lfppLength ζ φ γ) :
    c ≤ lfppDistOn ζ φ V x y := by
  have := hj.nonempty
  exact le_ciInf fun γ => h γ.1 γ.2.1 γ.2.2

theorem lfppDistOn_of_not_pcwJoined (h : ¬ PcwJoined V x y) : lfppDistOn ζ φ V x y = 0 := by
  have : IsEmpty {γ : ℝ → Rd d // IsPcwC1Path γ x y ∧ MapsTo γ (Icc 0 1) V} :=
    ⟨fun γ => h ⟨γ.1, γ.2⟩⟩
  exact Real.iInf_of_isEmpty _

/-- Near-optimal paths exist. -/
theorem exists_lfppLength_lt (hj : PcwJoined V x y) {c : ℝ} (hlt : lfppDistOn ζ φ V x y < c) :
    ∃ γ : ℝ → Rd d, IsPcwC1Path γ x y ∧ MapsTo γ (Icc 0 1) V ∧ lfppLength ζ φ γ < c := by
  have := hj.nonempty
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨γ.1, γ.2.1, γ.2.2, hγ⟩

/-- **Consistency with the frozen definition**: `D^ζ_{ε,d} = D^ζ_U(0, e₁)`. -/
theorem lfppDistance_eq_lfppDistOn (d : ℕ) (ζ : ℝ) (φ : Rd d → ℝ) :
    lfppDistance d ζ φ = lfppDistOn ζ φ (cube d) 0 (e₁ d) :=
  Equiv.iInf_congr (Equiv.subtypeEquivRight fun _ => isAdmissiblePath_iff) fun _ => rfl

/-- **Monotonicity in the domain.** -/
theorem lfppDistOn_mono (hVW : V ⊆ W) (hj : PcwJoined V x y) :
    lfppDistOn ζ φ W x y ≤ lfppDistOn ζ φ V x y :=
  le_lfppDistOn hj fun _ hγ hV => lfppDistOn_le_lfppLength hγ (hV.mono_right hVW)

/-- **Triangle inequality** (continuous field). -/
theorem lfppDistOn_triangle (hφ : Continuous φ) (hxy : PcwJoined V x y)
    (hyz : PcwJoined V y z) :
    lfppDistOn ζ φ V x z ≤ lfppDistOn ζ φ V x y + lfppDistOn ζ φ V y z := by
  have key : ∀ γ₁ : ℝ → Rd d, IsPcwC1Path γ₁ x y → MapsTo γ₁ (Icc 0 1) V →
      ∀ γ₂ : ℝ → Rd d, IsPcwC1Path γ₂ y z → MapsTo γ₂ (Icc 0 1) V →
      lfppDistOn ζ φ V x z ≤ lfppLength ζ φ γ₁ + lfppLength ζ φ γ₂ := by
    intro γ₁ h₁ hV₁ γ₂ h₂ hV₂
    rw [← lfppLength_concatPath hφ h₁ h₂]
    exact lfppDistOn_le_lfppLength (h₁.concat h₂) (mapsTo_concatPath hV₁ hV₂)
  have h2 : ∀ γ₂ : ℝ → Rd d, IsPcwC1Path γ₂ y z → MapsTo γ₂ (Icc 0 1) V →
      lfppDistOn ζ φ V x z - lfppLength ζ φ γ₂ ≤ lfppDistOn ζ φ V x y := by
    intro γ₂ h₂ hV₂
    refine le_lfppDistOn hxy fun γ₁ h₁ hV₁ => ?_
    linarith [key γ₁ h₁ hV₁ γ₂ h₂ hV₂]
  have h3 : lfppDistOn ζ φ V x z - lfppDistOn ζ φ V x y ≤ lfppDistOn ζ φ V y z :=
    le_lfppDistOn hyz fun γ₂ h₂ hV₂ => by linarith [h2 γ₂ h₂ hV₂]
  linarith

/-- `D_V(x, x) = 0` for `x ∈ V` (constant path). -/
theorem lfppDistOn_self (ζ : ℝ) (φ : Rd d → ℝ) (V : Set (Rd d)) (x : Rd d) :
    lfppDistOn ζ φ V x x = 0 := by
  by_cases hx : x ∈ V
  · exact le_antisymm ((lfppDistOn_le_lfppLength (isPcwC1Path_segPath x x)
      (fun u _ => by simp [segPath, hx])).trans_eq (lfppLength_segPath_self ζ φ x))
      (lfppDistOn_nonneg ζ φ V x x)
  · exact lfppDistOn_of_not_pcwJoined fun h => hx h.mem_left

/-- **Segment bound**: if the segment `[x, y]` lies in `V` and `e^{ζ φ} ≤ B` along it, then
`D_V(x, y) ≤ B |y - x|`. -/
theorem lfppDistOn_le_of_segment (hφ : Continuous φ) (hseg : MapsTo (segPath x y) (Icc 0 1) V)
    {B : ℝ} (hB : ∀ u ∈ Icc (0 : ℝ) 1, Real.exp (ζ * φ (segPath x y u)) ≤ B) :
    lfppDistOn ζ φ V x y ≤ B * ‖y - x‖ :=
  (lfppDistOn_le_lfppLength (isPcwC1Path_segPath x y) hseg).trans
    (lfppLength_segPath_le hφ x y hB)

/-- **Chain bound**: `D_V(v₀, v_N) ≤ Σ_{i<N} D_{W_i}(v_i, v_{i+1})` when `W_i ⊆ V` and each pair is
joined in `W_i`. -/
theorem lfppDistOn_le_sum (hφ : Continuous φ) (v : ℕ → Rd d) (Wi : ℕ → Set (Rd d))
    (hW : ∀ i, Wi i ⊆ V) (N : ℕ) (hj : ∀ i < N, PcwJoined (Wi i) (v i) (v (i + 1))) :
    lfppDistOn ζ φ V (v 0) (v N) ≤
      ∑ i ∈ Finset.range N, lfppDistOn ζ φ (Wi i) (v i) (v (i + 1)) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [lfppDistOn_self]
  have hv0 : v 0 ∈ V := hW 0 (hj 0 hN).mem_left
  have hJ : ∀ n ≤ N, PcwJoined V (v 0) (v n) := by
    intro n hn
    induction n with
    | zero => exact PcwJoined.refl hv0
    | succ n ih =>
      exact (ih (Nat.le_of_succ_le hn)).trans ((hj n (Nat.lt_of_succ_le hn)).mono (hW n))
  have key : ∀ n ≤ N, lfppDistOn ζ φ V (v 0) (v n) ≤
      ∑ i ∈ Finset.range n, lfppDistOn ζ φ (Wi i) (v i) (v (i + 1)) := by
    intro n hn
    induction n with
    | zero => simp [lfppDistOn_self]
    | succ n ih =>
      have hn' : n < N := Nat.lt_of_succ_le hn
      rw [Finset.sum_range_succ]
      calc lfppDistOn ζ φ V (v 0) (v (n + 1))
          ≤ lfppDistOn ζ φ V (v 0) (v n) + lfppDistOn ζ φ V (v n) (v (n + 1)) :=
            lfppDistOn_triangle hφ (hJ n hn'.le) ((hj n hn').mono (hW n))
        _ ≤ _ := add_le_add (ih hn'.le) (lfppDistOn_mono (hW n) (hj n hn'))
  exact key N le_rfl

end Basic

/-! ## Lower bounds and positivity -/

section Lower

variable {ζ : ℝ} {φ : Rd d → ℝ} {V : Set (Rd d)} {x y : Rd d} {γ : ℝ → Rd d}

/-- If `ζ φ ≥ m` along `γ|_{[a,b]}`, then `∫_a^b e^{ζφ(γ)}|γ'| ≥ e^m |γ(b) - γ(a)|`. -/
theorem IsPcwC1Path.exp_mul_norm_sub_le_integral (hφ : Continuous φ) (hγ : IsPcwC1Path γ x y)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {m : ℝ}
    (hm : ∀ t ∈ Icc a b, m ≤ ζ * φ (γ t)) :
    Real.exp m * ‖γ b - γ a‖ ≤ ∫ t in a..b, lfppIntegrand ζ φ γ t := by
  have hI := intervalIntegrable_of_sub (hγ.intervalIntegrable_lfppIntegrand hφ ζ) ha hab hb
  have hD := intervalIntegrable_of_sub hγ.intervalIntegrable_deriv ha hab hb
  calc Real.exp m * ‖γ b - γ a‖ ≤ Real.exp m * ∫ t in a..b, ‖deriv γ t‖ :=
        mul_le_mul_of_nonneg_left (hγ.norm_sub_le_integral ha hab hb) (Real.exp_pos m).le
    _ = ∫ t in a..b, Real.exp m * ‖deriv γ t‖ := (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ ∫ t in a..b, lfppIntegrand ζ φ γ t := by
        refine intervalIntegral.integral_mono_on hab (hD.norm.const_mul _) hI fun t ht => ?_
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hm t ht)) (norm_nonneg _)
/-- **Cost ≥ chord × minimal weight**: if `ζ φ ≥ m` along `γ`, then
`lfppLength ζ φ γ ≥ e^m |y - x|`. -/
theorem IsPcwC1Path.exp_mul_norm_sub_le_lfppLength (hφ : Continuous φ)
    (hγ : IsPcwC1Path γ x y) {m : ℝ} (hm : ∀ t ∈ Icc (0 : ℝ) 1, m ≤ ζ * φ (γ t)) :
    Real.exp m * ‖y - x‖ ≤ lfppLength ζ φ γ := by
  have := hγ.exp_mul_norm_sub_le_integral hφ le_rfl zero_le_one le_rfl hm
  rwa [hγ.source, hγ.target] at this

/-- **Exit-time lower bound.** If `r ≤ |y - x|` and `ζ φ ≥ m` on the closed ball `B̄(x, r)`,
every piecewise `C¹` path from `x` to `y` has LFPP length at least `e^m r`. -/
theorem IsPcwC1Path.exp_mul_le_lfppLength (hφ : Continuous φ) (hγ : IsPcwC1Path γ x y)
    {r m : ℝ} (hr : r ≤ ‖y - x‖) (hm : ∀ z ∈ Metric.closedBall x r, m ≤ ζ * φ z) :
    Real.exp m * r ≤ lfppLength ζ φ γ := by
  rcases le_or_gt r 0 with hr0 | hr0
  · exact (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos m).le hr0).trans
      (lfppLength_nonneg ζ φ γ)
  -- the first time `τ` at which `|γ - x| ≥ r`
  set S : Set ℝ := Icc (0 : ℝ) 1 ∩ {t | r ≤ ‖γ t - x‖} with hS
  have hSc : IsClosed S := by
    have hcont : ContinuousOn (fun t => ‖γ t - x‖) (Icc (0 : ℝ) 1) :=
      (hγ.continuousOn.sub continuousOn_const).norm
    exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have h1S : (1 : ℝ) ∈ S := ⟨⟨zero_le_one, le_rfl⟩, by
    show r ≤ ‖γ 1 - x‖; rw [hγ.target]; exact hr⟩
  have hSb : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set τ := sInf S with hτ
  have hτS : τ ∈ S := hSc.csInf_mem ⟨1, h1S⟩ hSb
  have hτ0 : 0 ≤ τ := hτS.1.1
  have hτ1 : τ ≤ 1 := hτS.1.2
  have hlt : ∀ t ∈ Ico (0 : ℝ) τ, ‖γ t - x‖ < r := by
    intro t ht
    by_contra hcon
    have htS : t ∈ S := ⟨⟨ht.1, ht.2.le.trans hτ1⟩, not_lt.1 hcon⟩
    exact absurd (csInf_le hSb htS) (not_le.2 ht.2)
  have hτpos : 0 < τ := by
    rcases hτ0.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 := hτS.2
      rw [← h] at h0
      simp only [mem_ofPred_eq] at h0
      rw [hγ.source, sub_self, norm_zero] at h0
      linarith
  -- on `[0, τ]` the path stays in the closed ball
  have hball : ∀ t ∈ Icc (0 : ℝ) τ, γ t ∈ Metric.closedBall x r := by
    intro t ht
    rcases ht.2.lt_or_eq with h | h
    · rw [Metric.mem_closedBall, dist_eq_norm]
      exact (hlt t ⟨ht.1, h⟩).le
    · have hcw : ContinuousWithinAt γ (Ico 0 τ) τ :=
        (hγ.continuousOn τ ⟨hτ0, hτ1⟩).mono
          (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hτ1))
      have hmem := hcw.mem_closure_image (by
        rw [closure_Ico hτpos.ne]; exact right_mem_Icc.2 hτ0)
      have hsub : γ '' Ico 0 τ ⊆ Metric.closedBall x r := by
        rintro _ ⟨s, hs, rfl⟩
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact (hlt s hs).le
      rw [h]
      exact (Metric.isClosed_closedBall.closure_subset_iff.2 hsub) hmem
  have hI := hγ.intervalIntegrable_lfppIntegrand hφ ζ
  calc Real.exp m * r ≤ Real.exp m * ‖γ τ - γ 0‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos m).le
        rw [hγ.source]; exact hτS.2
    _ ≤ ∫ t in (0 : ℝ)..τ, lfppIntegrand ζ φ γ t :=
        hγ.exp_mul_norm_sub_le_integral hφ le_rfl hτ0 hτ1 fun t ht => hm _ (hball t ht)
    _ ≤ (∫ t in (0 : ℝ)..τ, lfppIntegrand ζ φ γ t) + ∫ t in τ..1, lfppIntegrand ζ φ γ t :=
        le_add_of_nonneg_right (integral_lfppIntegrand_nonneg ζ φ γ hτ1)
    _ = lfppLength ζ φ γ := by
        rw [intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_of_sub hI le_rfl hτ0 hτ1)
          (intervalIntegrable_of_sub hI hτ0 hτ1 le_rfl), lfppLength_eq_integral]

/-- Lower bound for the internal distance from the exit-time bound. -/
theorem exp_mul_le_lfppDistOn (hφ : Continuous φ) (hj : PcwJoined V x y) {r m : ℝ}
    (hr : r ≤ ‖y - x‖) (hm : ∀ z ∈ Metric.closedBall x r, m ≤ ζ * φ z) :
    Real.exp m * r ≤ lfppDistOn ζ φ V x y :=
  le_lfppDistOn hj fun _ hγ _ => hγ.exp_mul_le_lfppLength hφ hr hm

/-- **Positivity** of internal distances between distinct joined points, for continuous `φ`. -/
theorem lfppDistOn_pos (hφ : Continuous φ) (hxy : x ≠ y) (hj : PcwJoined V x y) :
    0 < lfppDistOn ζ φ V x y := by
  have hK : IsCompact (Metric.closedBall x ‖y - x‖) := isCompact_closedBall x _
  obtain ⟨z₀, -, hz₀⟩ := hK.exists_isMinOn
    ⟨x, Metric.mem_closedBall_self (norm_nonneg _)⟩ (continuous_const.mul hφ).continuousOn
  have hr : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy.symm)
  exact (mul_pos (Real.exp_pos _) hr).trans_le
    (exp_mul_le_lfppDistOn hφ hj le_rfl fun z hz => hz₀ hz)

end Lower

/-! ## The cube and the frozen LFPP distance -/

section Cube

theorem convex_cube (d : ℕ) : Convex ℝ (cube d) := by
  intro z hz w hw a b ha hb hab i
  show |(a • z + b • w).ofLp i| < 2
  have e : (a • z + b • w).ofLp i = a * z.ofLp i + b * w.ofLp i := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [e]
  have hm : max |z.ofLp i| |w.ofLp i| < 2 := max_lt (hz i) (hw i)
  calc |a * z.ofLp i + b * w.ofLp i| ≤ |a * z.ofLp i| + |b * w.ofLp i| := abs_add_le _ _
    _ = a * |z.ofLp i| + b * |w.ofLp i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * max |z.ofLp i| |w.ofLp i| + b * max |z.ofLp i| |w.ofLp i| :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
    _ = max |z.ofLp i| |w.ofLp i| := by rw [← add_mul, hab, one_mul]
    _ < 2 := hm

theorem isOpen_cube (d : ℕ) : IsOpen (cube d) := by
  have : cube d = ⋂ i : Fin d, {z : Rd d | |z.ofLp i| < 2} := by
    ext z; simp only [cube, mem_iInter, mem_ofPred_eq]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_abs.comp (PiLp.continuous_apply 2 _ i)) continuous_const

theorem zero_mem_cube (d : ℕ) : (0 : Rd d) ∈ cube d := fun i => by
  show |(0 : Rd d).ofLp i| < 2
  simp

theorem e₁_ofLp (d : ℕ) (i : Fin d) : (e₁ d).ofLp i = if (i : ℕ) = 0 then 1 else 0 := rfl

theorem e₁_mem_cube (d : ℕ) : e₁ d ∈ cube d := fun i => by
  show |(e₁ d).ofLp i| < 2
  rw [e₁_ofLp]
  split_ifs <;> norm_num

theorem e₁_ne_zero {d : ℕ} (hd : 0 < d) : e₁ d ≠ 0 := by
  intro h
  have h1 : (e₁ d).ofLp ⟨0, hd⟩ = 1 := by rw [e₁_ofLp]; simp
  rw [h] at h1
  simp at h1

theorem norm_e₁ {d : ℕ} (hd : 0 < d) : ‖e₁ d‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have : ∑ i : Fin d, ‖(e₁ d).ofLp i‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single ⟨0, hd⟩]
    · rw [e₁_ofLp]; simp
    · intro i _ hi
      rw [e₁_ofLp, ite_eq_right (fun h => hi (Fin.ext h))]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [this, Real.sqrt_one]

/-- `0` and `e₁` are joined inside the cube (by the segment). -/
theorem pcwJoined_cube (d : ℕ) : PcwJoined (cube d) 0 (e₁ d) :=
  PcwJoined.of_convex (convex_cube d) (zero_mem_cube d) (e₁_mem_cube d)

/-- Near-optimal admissible paths for the frozen distance. -/
theorem exists_isAdmissiblePath_lfppLength_lt {d : ℕ} {ζ : ℝ} {φ : Rd d → ℝ} {c : ℝ}
    (hlt : lfppDistance d ζ φ < c) :
    ∃ γ : ℝ → Rd d, IsAdmissiblePath d γ ∧ lfppLength ζ φ γ < c := by
  rw [lfppDistance_eq_lfppDistOn] at hlt
  obtain ⟨γ, hγ, hV, hL⟩ := exists_lfppLength_lt (pcwJoined_cube d) hlt
  exact ⟨γ, isAdmissiblePath_iff.2 ⟨hγ, hV⟩, hL⟩

/-- **Positivity of the frozen LFPP distance** for every continuous field (`d ≥ 1`). -/
theorem lfppDistance_pos {d : ℕ} (hd : 0 < d) {ζ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ) :
    0 < lfppDistance d ζ φ := by
  rw [lfppDistance_eq_lfppDistOn]
  exact lfppDistOn_pos hφ (e₁_ne_zero hd).symm (pcwJoined_cube d)

/-- **Crude lower bound** (HA5 D1(c)): if `|φ| ≤ M` on `U`, then `e^{-|ζ| M} ≤ D^ζ(φ)`. -/
theorem exp_neg_le_lfppDistance {d : ℕ} (hd : 0 < d) {ζ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ)
    {M : ℝ} (hM : ∀ z ∈ cube d, |φ z| ≤ M) : Real.exp (-(|ζ| * M)) ≤ lfppDistance d ζ φ := by
  rw [lfppDistance_eq_lfppDistOn]
  refine le_lfppDistOn (pcwJoined_cube d) fun γ hγ hV => ?_
  have := hγ.exp_mul_norm_sub_le_lfppLength (ζ := ζ) (m := -(|ζ| * M)) hφ fun t ht => by
    have h1 : |ζ * φ (γ t)| ≤ |ζ| * M := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM _ (hV ht)) (abs_nonneg ζ)
    linarith [neg_abs_le (ζ * φ (γ t))]
  rwa [sub_zero, norm_e₁ hd, mul_one] at this

/-- **Crude upper bound** (HA5 D1(c)): if `|φ| ≤ M` on `U`, then `D^ζ(φ) ≤ e^{|ζ| M}`. -/
theorem lfppDistance_le_exp {d : ℕ} (hd : 0 < d) {ζ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ)
    {M : ℝ} (hM : ∀ z ∈ cube d, |φ z| ≤ M) : lfppDistance d ζ φ ≤ Real.exp (|ζ| * M) := by
  rw [lfppDistance_eq_lfppDistOn]
  have hseg := mapsTo_segPath (convex_cube d) (zero_mem_cube d) (e₁_mem_cube d)
  have := lfppDistOn_le_of_segment (ζ := ζ) hφ hseg (B := Real.exp (|ζ| * M)) fun u hu => by
    rw [Real.exp_le_exp]
    have h1 : |ζ * φ (segPath 0 (e₁ d) u)| ≤ |ζ| * M := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM _ (hseg hu)) (abs_nonneg ζ)
    linarith [le_abs_self (ζ * φ (segPath 0 (e₁ d) u))]
  rwa [sub_zero, norm_e₁ hd, mul_one] at this

/-- **Crude bound, logarithmic form** (HA5 D1(c), D2(1)): if `|φ| ≤ M` on `U`, then
`|log D^ζ(φ)| ≤ |ζ| M`. -/
theorem abs_log_lfppDistance_le {d : ℕ} (hd : 0 < d) {ζ : ℝ} {φ : Rd d → ℝ}
    (hφ : Continuous φ) {M : ℝ} (hM : ∀ z ∈ cube d, |φ z| ≤ M) :
    |Real.log (lfppDistance d ζ φ)| ≤ |ζ| * M := by
  have h1 := exp_neg_le_lfppDistance (ζ := ζ) hd hφ hM
  have h2 := lfppDistance_le_exp (ζ := ζ) hd hφ hM
  have hpos : 0 < lfppDistance d ζ φ := (Real.exp_pos _).trans_le h1
  rw [abs_le]
  constructor
  · have := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at this
    linarith
  · have := Real.log_le_log hpos h2
    rwa [Real.log_exp] at this

end Cube

end HigherDimLFPP
