/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.DegOutMeasurable at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.DegMeasurable

/-!
# Measurability of `deg^ε_out` on the curve space

The outer degree of [18] §4.2 counts crossings `c((a, b)) ⊂ int B̄`
between `∂B̄` and the local segment `W = c([t₀ − ε, t₀ + ε])`. Its defining condition `c((a, b)) ⊂ int B̄` is neither
open nor closed in `(c, a, b)`, so we re-encode the crossings by their *window times*:

* a crossing whose window end is `b` ("type `true`") is `(L(b), b)` with `L(b)` the last *far time* (distance `≥ 4 diam W`
  from `c(t₀)`) before `b`; a crossing whose window end is `a` ("type `false`") is `(a, F(a))` with `F(a)` the first far
  time after `a`;
* two crossings are disjoint iff a far time lies between their window times (or, for crossings of different types,
  the window times are in the right order).

`exists_degOutFamily_iff` proves that an outer-degree family of size `N ≥ 1` exists iff `diam W > 0` and such
`CrossingData` exists; every condition in `CrossingData` is closed in `(c, t)` except the existence of far times on one
side, which is `F_σ`. Hence `{deg^ε_out ≥ k}` is Borel (`measurable_locDegOut`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

/-! ## Window times and far times -/

/-- A *far time*: `c(s)` is at distance at least `4 diam(c([t₀ − ε, t₀ + ε]))` from `c(t₀)`. -/
def IsFarTime (ε : ℝ) (c : ℝ → ℂ) (t₀ s : ℝ) : Prop :=
  4 * diam (locWindow ε c t₀) ≤ dist (c s) (c t₀)

/-- A far time lies between `s` and `t`. -/
def FarBetween (ε : ℝ) (c : ℝ → ℂ) (t₀ s t : ℝ) : Prop :=
  ∃ u, min s t ≤ u ∧ u ≤ max s t ∧ IsFarTime ε c t₀ u

/-- A far time exists on the appropriate side of the window time `t` of a crossing of type `τ`. -/
def FarSide (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) (τ : Bool) (t : ℝ) : Prop :=
  (τ = true → ∃ s, s ≤ t ∧ IsFarTime ε c t₀ s) ∧ (τ = false → ∃ s, t ≤ s ∧ IsFarTime ε c t₀ s)

/-- Disjointness of two crossings, in terms of their window times. -/
def CrossPairOK (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) (τ τ' : Bool) (t t' : ℝ) : Prop :=
  (τ = τ' → FarBetween ε c t₀ t t') ∧ (τ = true → τ' = false → t ≤ t' ∨ FarBetween ε c t₀ t t') ∧
    (τ = false → τ' = true → t' ≤ t ∨ FarBetween ε c t₀ t t')

/-- Window-time data of `N` pairwise disjoint crossings. -/
def CrossingData (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) {N : ℕ} (τ : Fin N → Bool) (t : Fin N → ℝ) : Prop :=
  (∀ i, c (t i) ∈ locWindow ε c t₀) ∧ (∀ i, FarSide ε c t₀ (τ i) (t i)) ∧
    ∀ i j, i ≠ j → CrossPairOK ε c t₀ (τ i) (τ j) (t i) (t j)

theorem frontier_locBall {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} (hD : 0 < diam (locWindow ε c t₀)) :
    frontier (locBall ε c t₀) = sphere (c t₀) (4 * diam (locWindow ε c t₀)) :=
  frontier_closedBall _ (by positivity)

theorem interior_locBall {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} (hD : 0 < diam (locWindow ε c t₀)) :
    interior (locBall ε c t₀) = ball (c t₀) (4 * diam (locWindow ε c t₀)) :=
  interior_closedBall _ (by positivity)

/-- Window times are not far. -/
theorem not_isFarTime_of_mem_window {ε : ℝ} {c : ℝ → ℂ} (hc : Continuous c) {t₀ s : ℝ} (hε : 0 ≤ ε)
    (hD : 0 < diam (locWindow ε c t₀)) (hs : c s ∈ locWindow ε c t₀) : ¬ IsFarTime ε c t₀ s := by
  intro hfar
  have hb : Bornology.IsBounded (locWindow ε c t₀) := (isCompact_Icc.image hc).isBounded
  have h0 : c t₀ ∈ locWindow ε c t₀ :=
    mem_image_of_mem c (show t₀ ∈ Icc (t₀ - ε) (t₀ + ε) from ⟨by linarith, by linarith⟩)
  have := dist_le_diam_of_mem hb hs h0
  unfold IsFarTime at hfar
  linarith

/-! ## From families to window-time data -/

theorem exists_crossingData_of_family {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} {N : ℕ} {a b : Fin N → ℝ}
    (h : IsDegOutFamily ε c t₀ a b) : ∃ (τ : Fin N → Bool) (t : Fin N → ℝ), CrossingData ε c t₀ τ t := by
  classical
  -- type `true`: `c (a i)` on the sphere and `c (b i)` in the window
  set R : Fin N → Prop := fun i => c (a i) ∈ frontier (locBall ε c t₀) ∧ c (b i) ∈ locWindow ε c t₀
  have hfarR : ∀ i, R i → IsFarTime ε c t₀ (a i) := by
    intro i hi
    have hD := h.diam_pos i
    have := hi.1
    rw [frontier_locBall hD, mem_sphere] at this
    unfold IsFarTime; rw [this]
  have hnotR : ∀ i, ¬ R i → c (b i) ∈ frontier (locBall ε c t₀) ∧ c (a i) ∈ locWindow ε c t₀ := by
    intro i hi
    rcases (h.2.2 i).2 with h1 | h1
    · exact absurd h1 hi
    · exact h1
  have hfarL : ∀ i, ¬ R i → IsFarTime ε c t₀ (b i) := by
    intro i hi
    have hD := h.diam_pos i
    have := (hnotR i hi).1
    rw [frontier_locBall hD, mem_sphere] at this
    unfold IsFarTime; rw [this]
  refine ⟨fun i => decide (R i), fun i => if R i then b i else a i, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : R i
    · simp only [hi, ite_true]; exact hi.2
    · simp only [hi, ite_false]; exact (hnotR i hi).2
  · intro i
    by_cases hi : R i
    · refine ⟨fun _ => ?_, fun hf => ?_⟩
      · simp only [hi, ite_true]; exact ⟨a i, (h.1 i).le, hfarR i hi⟩
      · simp [hi] at hf
    · refine ⟨fun hf => ?_, fun _ => ?_⟩
      · simp [hi] at hf
      · simp only [hi, ite_false]; exact ⟨b i, (h.1 i).le, hfarL i hi⟩
  · intro i j hij
    have hord := h.ordered hij
    have hai := h.1 i
    have haj := h.1 j
    by_cases hi : R i <;> by_cases hj : R j
    · -- both `true`: window times `b i`, `b j`
      simp only [hi, hj, decide_true, ite_true]
      refine ⟨fun _ => ?_, fun _ h2 => by simp at h2, fun h1 => by simp at h1⟩
      rcases hord with hle | hle
      · exact ⟨a j, by simp only [min_le_iff]; left; exact hle, by
          simp only [le_max_iff]; right; exact haj.le, hfarR j hj⟩
      · exact ⟨a i, by simp only [min_le_iff]; right; exact hle, by
          simp only [le_max_iff]; left; exact hai.le, hfarR i hi⟩
    · -- `i` true, `j` false: window times `b i`, `a j`
      simp only [hi, hj, decide_true, decide_false, ite_true, ite_false]
      refine ⟨fun h0 => by simp at h0, fun _ _ => ?_, fun h1 => by simp at h1⟩
      rcases hord with hle | hle
      · exact Or.inl hle
      · refine Or.inr ⟨b j, ?_, ?_, hfarL j hj⟩
        · simp only [min_le_iff]; right; exact haj.le
        · simp only [le_max_iff]; left; linarith
    · -- `i` false, `j` true: window times `a i`, `b j`
      simp only [hi, hj, decide_true, decide_false, ite_true, ite_false]
      refine ⟨fun h0 => by simp at h0, fun h1 => by simp at h1, fun _ _ => ?_⟩
      rcases hord with hle | hle
      · refine Or.inr ⟨b i, ?_, ?_, hfarL i hi⟩
        · simp only [min_le_iff]; left; exact hai.le
        · simp only [le_max_iff]; right; linarith
      · exact Or.inl hle
    · -- both `false`: window times `a i`, `a j`
      simp only [hi, hj, decide_false, ite_false]
      refine ⟨fun _ => ?_, fun h1 => by simp at h1, fun _ h2 => by simp at h2⟩
      rcases hord with hle | hle
      · exact ⟨b i, by simp only [min_le_iff]; left; exact hai.le, by
          simp only [le_max_iff]; right; exact hle, hfarL i hi⟩
      · exact ⟨b j, by simp only [min_le_iff]; right; exact haj.le, by
          simp only [le_max_iff]; left; exact hle, hfarL j hj⟩

/-! ## From window-time data to families -/

theorem isClosed_isFarTime {ε : ℝ} {c : ℝ → ℂ} (hc : Continuous c) (t₀ : ℝ) :
    IsClosed {s | IsFarTime ε c t₀ s} :=
  isClosed_le continuous_const (hc.dist continuous_const)

theorem exists_family_of_crossingData {ε : ℝ} {c : ℝ → ℂ} (hc : Continuous c) {t₀ : ℝ} (hε : 0 ≤ ε)
    (hD : 0 < diam (locWindow ε c t₀)) {N : ℕ} {τ : Fin N → Bool} {t : Fin N → ℝ}
    (h : CrossingData ε c t₀ τ t) : ∃ a b : Fin N → ℝ, IsDegOutFamily ε c t₀ a b := by
  classical
  have hZ := isClosed_isFarTime (ε := ε) hc t₀
  have hnot : ∀ i, ¬ IsFarTime ε c t₀ (t i) := fun i => not_isFarTime_of_mem_window hc hε hD (h.1 i)
  -- last far time before / first far time after
  set Lt : Fin N → ℝ := fun i => sSup {s | s ≤ t i ∧ IsFarTime ε c t₀ s}
  set Ft : Fin N → ℝ := fun i => sInf {s | t i ≤ s ∧ IsFarTime ε c t₀ s}
  have hLmem : ∀ i, τ i = true → Lt i ≤ t i ∧ IsFarTime ε c t₀ (Lt i) := by
    intro i hi
    obtain ⟨s, hs, hsf⟩ := (h.2.1 i).1 hi
    have hcl : IsClosed {s | s ≤ t i ∧ IsFarTime ε c t₀ s} := isClosed_Iic.inter hZ
    exact hcl.csSup_mem ⟨s, hs, hsf⟩ ⟨t i, fun _ hx => hx.1⟩
  have hLge : ∀ i, τ i = true → ∀ u, u ≤ t i → IsFarTime ε c t₀ u → u ≤ Lt i := by
    intro i _ u hu hfu
    exact le_csSup ⟨t i, fun _ hx => hx.1⟩ ⟨hu, hfu⟩
  have hFmem : ∀ i, τ i = false → t i ≤ Ft i ∧ IsFarTime ε c t₀ (Ft i) := by
    intro i hi
    obtain ⟨s, hs, hsf⟩ := (h.2.1 i).2 hi
    have hcl : IsClosed {s | t i ≤ s ∧ IsFarTime ε c t₀ s} := isClosed_Ici.inter hZ
    exact hcl.csInf_mem ⟨s, hs, hsf⟩ ⟨t i, fun _ hx => hx.1⟩
  have hFle : ∀ i, τ i = false → ∀ u, t i ≤ u → IsFarTime ε c t₀ u → Ft i ≤ u := by
    intro i _ u hu hfu
    exact csInf_le ⟨t i, fun _ hx => hx.1⟩ ⟨hu, hfu⟩
  set a : Fin N → ℝ := fun i => if τ i = true then Lt i else t i
  set b : Fin N → ℝ := fun i => if τ i = true then t i else Ft i
  have hab : ∀ i, a i < b i := by
    intro i
    by_cases hi : τ i = true
    · simp only [a, b, ite_eq_left hi]
      obtain ⟨h1, h2⟩ := hLmem i hi
      exact lt_of_le_of_ne h1 fun he => hnot i (he ▸ h2)
    · have hi' : τ i = false := by simpa using hi
      simp only [a, b, ite_eq_right hi]
      obtain ⟨h1, h2⟩ := hFmem i hi'
      exact lt_of_le_of_ne h1 fun he => hnot i (he ▸ h2)
  -- interior times are not far
  have hint : ∀ i, ∀ s ∈ Ioo (a i) (b i), ¬ IsFarTime ε c t₀ s := by
    intro i s hs hfs
    by_cases hi : τ i = true
    · simp only [a, b, ite_eq_left hi] at hs
      have := hLge i hi s hs.2.le hfs
      linarith [hs.1]
    · have hi' : τ i = false := by simpa using hi
      simp only [a, b, ite_eq_right hi] at hs
      have := hFle i hi' s hs.1.le hfs
      linarith [hs.2]
  set r : ℝ := 4 * diam (locWindow ε c t₀)
  have hcloseIcc : ∀ i, ∀ s ∈ Icc (a i) (b i), dist (c s) (c t₀) ≤ r := by
    intro i
    have hsub : Ioo (a i) (b i) ⊆ {s | dist (c s) (c t₀) ≤ r} := fun s hs => by
      have := hint i s hs
      unfold IsFarTime at this
      exact (not_le.mp this).le
    have hcl : IsClosed {s | dist (c s) (c t₀) ≤ r} := isClosed_le (hc.dist continuous_const) continuous_const
    intro s hs
    rw [← closure_Ioo (hab i).ne] at hs
    exact hcl.closure_subset_iff.mpr hsub hs
  have hsphere : ∀ i s, s ∈ Icc (a i) (b i) → IsFarTime ε c t₀ s → c s ∈ frontier (locBall ε c t₀) := by
    intro i s hs hfs
    rw [frontier_locBall hD, mem_sphere]
    exact le_antisymm (hcloseIcc i s hs) hfs
  refine ⟨a, b, hab, fun i j hij => ?_, fun i => ⟨?_, ?_⟩⟩
  · -- disjointness
    rw [Ioo_disjoint_Ioo]
    have hp := h.2.2 i j hij
    have key : b i ≤ a j ∨ b j ≤ a i := by
      cases hti : τ i <;> cases htj : τ j
      · -- both false
        obtain ⟨u, hu1, hu2, hfu⟩ := hp.1 (by rw [hti, htj])
        simp only [a, b, hti, htj, Bool.false_eq_true, ite_false]
        rcases le_total (t i) (t j) with hle | hle
        · rw [min_eq_left hle] at hu1; rw [max_eq_right hle] at hu2
          exact Or.inl ((hFle i hti u hu1 hfu).trans hu2)
        · rw [min_eq_right hle] at hu1; rw [max_eq_left hle] at hu2
          exact Or.inr ((hFle j htj u hu1 hfu).trans hu2)
      · -- `i` false, `j` true
        simp only [a, b, hti, htj, Bool.false_eq_true, ite_false, ite_true]
        rcases hp.2.2 hti htj with hle | ⟨u, hu1, hu2, hfu⟩
        · exact Or.inr hle
        · rcases le_total (t i) (t j) with hle | hle
          · rw [min_eq_left hle] at hu1; rw [max_eq_right hle] at hu2
            exact Or.inl ((hFle i hti u hu1 hfu).trans (hLge j htj u hu2 hfu))
          · rw [max_eq_left hle] at hu2
            exact Or.inr hle
      · -- `i` true, `j` false
        simp only [a, b, hti, htj, Bool.false_eq_true, ite_false, ite_true]
        rcases hp.2.1 hti htj with hle | ⟨u, hu1, hu2, hfu⟩
        · exact Or.inl hle
        · rcases le_total (t i) (t j) with hle | hle
          · exact Or.inl hle
          · rw [min_eq_right hle] at hu1; rw [max_eq_left hle] at hu2
            exact Or.inr ((hFle j htj u hu1 hfu).trans (hLge i hti u hu2 hfu))
      · -- both true
        obtain ⟨u, hu1, hu2, hfu⟩ := hp.1 (by rw [hti, htj])
        simp only [a, b, hti, htj, ite_true]
        rcases le_total (t i) (t j) with hle | hle
        · rw [min_eq_left hle] at hu1; rw [max_eq_right hle] at hu2
          exact Or.inl (hu1.trans (hLge j htj u hu2 hfu))
        · rw [min_eq_right hle] at hu1; rw [max_eq_left hle] at hu2
          exact Or.inr (hu1.trans (hLge i hti u hu2 hfu))
    rcases key with hk | hk
    · exact (min_le_left _ _).trans (hk.trans (le_max_right _ _))
    · exact (min_le_right _ _).trans (hk.trans (le_max_left _ _))
  · -- the open crossing lies in the open ball
    rintro _ ⟨s, hs, rfl⟩
    rw [interior_locBall hD, mem_ball]
    have := hint i s hs
    unfold IsFarTime at this
    exact not_le.mp this
  · -- endpoints
    by_cases hi : τ i = true
    · left
      have hai : a i = Lt i := by simp only [a, ite_eq_left hi]
      have hbi : b i = t i := by simp only [b, ite_eq_left hi]
      refine ⟨hsphere i (a i) ⟨le_rfl, (hab i).le⟩ (hai ▸ (hLmem i hi).2), hbi ▸ h.1 i⟩
    · right
      have hi' : τ i = false := by simpa using hi
      have hai : a i = t i := by simp only [a, ite_eq_right hi]
      have hbi : b i = Ft i := by simp only [b, ite_eq_right hi]
      refine ⟨hsphere i (b i) ⟨(hab i).le, le_rfl⟩ (hbi ▸ (hFmem i hi').2), hai ▸ h.1 i⟩

/-- **Window-time characterization of outer-degree families** (`N ≥ 1`). -/
theorem exists_degOutFamily_iff {ε : ℝ} {c : ℝ → ℂ} (hc : Continuous c) {t₀ : ℝ} (hε : 0 ≤ ε)
    {N : ℕ} (hN : 0 < N) :
    (∃ a b : Fin N → ℝ, IsDegOutFamily ε c t₀ a b) ↔
      0 < diam (locWindow ε c t₀) ∧ ∃ (τ : Fin N → Bool) (t : Fin N → ℝ), CrossingData ε c t₀ τ t := by
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨h.diam_pos ⟨0, hN⟩, exists_crossingData_of_family h⟩
  · rintro ⟨hD, τ, t, h⟩
    exact exists_family_of_crossingData hc hε hD h

/-! ## Restriction and superlevel sets -/

theorem IsDegOutFamily.castLE {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} {M N : ℕ} {a b : Fin N → ℝ}
    (h : IsDegOutFamily ε c t₀ a b) (hMN : M ≤ N) :
    IsDegOutFamily ε c t₀ (a ∘ Fin.castLE hMN) (b ∘ Fin.castLE hMN) :=
  ⟨fun _ => h.1 _, fun _ _ hij => h.2.1 _ _ fun he => hij (Fin.castLE_injective hMN he), fun _ => h.2.2 _⟩

theorem le_locDegOut_iff {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} (k : ℕ) :
    (k : ℕ∞) ≤ locDegOut ε c t₀ ↔ ∃ a b : Fin k → ℝ, IsDegOutFamily ε c t₀ a b := by
  constructor
  · intro hk
    by_contra hno
    push Not at hno
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      exact hno Fin.elim0 Fin.elim0 ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    have hle : locDegOut ε c t₀ ≤ ((k - 1 : ℕ) : ℕ∞) := by
      refine locDegOut_le fun N a b hab => ?_
      by_contra hlt
      push Not at hlt
      have hkN : k ≤ N := by
        have : (k - 1 : ℕ) < N := Nat.cast_lt.mp hlt
        omega
      exact hno _ _ (hab.castLE hkN)
    have := hk.trans hle
    have : k ≤ k - 1 := Nat.cast_le.mp this
    omega
  · rintro ⟨a, b, hab⟩
    exact le_locDegOut hab

/-! ## Closedness and measurability -/

/-- `FarSide` with the far time within distance `n` of the window time. -/
def FarSideN (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) (n : ℕ) (τ : Bool) (t : ℝ) : Prop :=
  (τ = true → ∃ σ ∈ Icc (0 : ℝ) n, IsFarTime ε c t₀ (t - σ)) ∧
    (τ = false → ∃ σ ∈ Icc (0 : ℝ) n, IsFarTime ε c t₀ (t + σ))

/-- `CrossingData` with far times within distance `n`. -/
def CrossingDataN (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) (n : ℕ) {N : ℕ} (τ : Fin N → Bool) (t : Fin N → ℝ) : Prop :=
  (∀ i, c (t i) ∈ locWindow ε c t₀) ∧ (∀ i, FarSideN ε c t₀ n (τ i) (t i)) ∧
    ∀ i j, i ≠ j → CrossPairOK ε c t₀ (τ i) (τ j) (t i) (t j)
theorem FarSideN.mono {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} {m n : ℕ} (hmn : m ≤ n) {τ : Bool} {t : ℝ}
    (h : FarSideN ε c t₀ m τ t) : FarSideN ε c t₀ n τ t := by
  have hmn' : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  refine ⟨fun hτ => ?_, fun hτ => ?_⟩
  · obtain ⟨σ, hσ, hf⟩ := h.1 hτ; exact ⟨σ, ⟨hσ.1, hσ.2.trans hmn'⟩, hf⟩
  · obtain ⟨σ, hσ, hf⟩ := h.2 hτ; exact ⟨σ, ⟨hσ.1, hσ.2.trans hmn'⟩, hf⟩

theorem FarSide.exists_farSideN {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} {τ : Bool} {t : ℝ}
    (h : FarSide ε c t₀ τ t) : ∃ n : ℕ, FarSideN ε c t₀ n τ t := by
  cases τ
  · obtain ⟨s, hs, hf⟩ := h.2 rfl
    obtain ⟨n, hn⟩ := exists_nat_ge (s - t)
    refine ⟨n, fun h1 => by simp at h1, fun _ => ⟨s - t, ⟨by linarith, hn⟩, ?_⟩⟩
    rwa [add_sub_cancel]
  · obtain ⟨s, hs, hf⟩ := h.1 rfl
    obtain ⟨n, hn⟩ := exists_nat_ge (t - s)
    refine ⟨n, fun _ => ⟨t - s, ⟨by linarith, hn⟩, ?_⟩, fun h1 => by simp at h1⟩
    rwa [sub_sub_cancel]

theorem FarSideN.farSide {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} {n : ℕ} {τ : Bool} {t : ℝ}
    (h : FarSideN ε c t₀ n τ t) : FarSide ε c t₀ τ t := by
  refine ⟨fun hτ => ?_, fun hτ => ?_⟩
  · obtain ⟨σ, hσ, hf⟩ := h.1 hτ; exact ⟨t - σ, by linarith [hσ.1], hf⟩
  · obtain ⟨σ, hσ, hf⟩ := h.2 hτ; exact ⟨t + σ, by linarith [hσ.1], hf⟩

theorem crossingData_iff_exists {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} {N : ℕ} (τ : Fin N → Bool) (t : Fin N → ℝ) :
    CrossingData ε c t₀ τ t ↔ ∃ n : ℕ, CrossingDataN ε c t₀ n τ t := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    choose m hm using fun i => (h2 i).exists_farSideN
    refine ⟨Finset.univ.sup m, h1, fun i => (hm i).mono (Finset.le_sup (Finset.mem_univ i)), h3⟩
  · rintro ⟨n, h1, h2, h3⟩
    exact ⟨h1, fun i => (h2 i).farSide, h3⟩

theorem farBetween_iff {ε : ℝ} {c : ℝ → ℂ} {t₀ s t : ℝ} :
    FarBetween ε c t₀ s t ↔
      ∃ σ ∈ Icc (0 : ℝ) 1, IsFarTime ε c t₀ (min s t + σ * (max s t - min s t)) := by
  have hmm : min s t ≤ max s t := min_le_max
  constructor
  · rintro ⟨u, hu1, hu2, hf⟩
    rcases hmm.eq_or_lt with heq | hlt
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      have : u = min s t := le_antisymm (heq ▸ hu2) hu1
      rwa [zero_mul, add_zero, ← this]
    · have hpos : 0 < max s t - min s t := sub_pos.mpr hlt
      refine ⟨(u - min s t) / (max s t - min s t), ⟨div_nonneg (by linarith) hpos.le, ?_⟩, ?_⟩
      · rw [div_le_one hpos]; linarith
      · rwa [div_mul_cancel₀ _ hpos.ne', add_sub_cancel]
  · rintro ⟨σ, hσ, hf⟩
    refine ⟨_, ?_, ?_, hf⟩
    · nlinarith [hσ.1]
    · nlinarith [hσ.2]

section Closed

variable {Y : Type*} [TopologicalSpace Y] {ε t₀ : ℝ} {g : Y → C(ℝ, ℂ)} (hg : Continuous g)
include hg

theorem isClosed_isFarTime_comp {f : Y → ℝ} (hf : Continuous f) :
    IsClosed {y | IsFarTime ε (g y) t₀ (f y)} :=
  isClosed_le (continuous_const.mul ((continuous_diam_window ε t₀).comp hg))
    ((continuous_eval.comp (hg.prodMk hf)).dist (continuous_eval.comp (hg.prodMk continuous_const)))

theorem isClosed_farBetween_comp {f₁ f₂ : Y → ℝ} (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) :
    IsClosed {y | FarBetween ε (g y) t₀ (f₁ y) (f₂ y)} := by
  simp only [farBetween_iff]
  exact isClosed_exists_mem_of_isCompact isCompact_Icc <| isClosed_isFarTime_comp (hg.comp continuous_fst)
    (((hf₁.comp continuous_fst).min (hf₂.comp continuous_fst)).add (continuous_snd.mul
      (((hf₁.comp continuous_fst).max (hf₂.comp continuous_fst)).sub
        ((hf₁.comp continuous_fst).min (hf₂.comp continuous_fst)))))

theorem isClosed_farSideN_comp (n : ℕ) (τ : Bool) {f : Y → ℝ} (hf : Continuous f) :
    IsClosed {y | FarSideN ε (g y) t₀ n τ (f y)} := by
  cases τ
  · have : {y | FarSideN ε (g y) t₀ n false (f y)} =
        {y | ∃ σ ∈ Icc (0 : ℝ) n, IsFarTime ε (g y) t₀ (f y + σ)} := by
      ext y; simp [FarSideN]
    rw [this]
    exact isClosed_exists_mem_of_isCompact isCompact_Icc
      (isClosed_isFarTime_comp (hg.comp continuous_fst) ((hf.comp continuous_fst).add continuous_snd))
  · have : {y | FarSideN ε (g y) t₀ n true (f y)} =
        {y | ∃ σ ∈ Icc (0 : ℝ) n, IsFarTime ε (g y) t₀ (f y - σ)} := by
      ext y; simp [FarSideN]
    rw [this]
    exact isClosed_exists_mem_of_isCompact isCompact_Icc
      (isClosed_isFarTime_comp (hg.comp continuous_fst) ((hf.comp continuous_fst).sub continuous_snd))

theorem isClosed_crossPairOK_comp (τ τ' : Bool) {f₁ f₂ : Y → ℝ} (hf₁ : Continuous f₁)
    (hf₂ : Continuous f₂) :
    IsClosed {y | CrossPairOK ε (g y) t₀ τ τ' (f₁ y) (f₂ y)} := by
  have hFB := isClosed_farBetween_comp (ε := ε) (t₀ := t₀) hg hf₁ hf₂
  cases τ <;> cases τ'
  · have : {y | CrossPairOK ε (g y) t₀ false false (f₁ y) (f₂ y)} =
        {y | FarBetween ε (g y) t₀ (f₁ y) (f₂ y)} := by ext y; simp [CrossPairOK]
    rw [this]; exact hFB
  · have : {y | CrossPairOK ε (g y) t₀ false true (f₁ y) (f₂ y)} =
        {y | f₂ y ≤ f₁ y} ∪ {y | FarBetween ε (g y) t₀ (f₁ y) (f₂ y)} := by
      ext y; simp [CrossPairOK]
    rw [this]; exact (isClosed_le hf₂ hf₁).union hFB
  · have : {y | CrossPairOK ε (g y) t₀ true false (f₁ y) (f₂ y)} =
        {y | f₁ y ≤ f₂ y} ∪ {y | FarBetween ε (g y) t₀ (f₁ y) (f₂ y)} := by
      ext y; simp [CrossPairOK]
    rw [this]; exact (isClosed_le hf₁ hf₂).union hFB
  · have : {y | CrossPairOK ε (g y) t₀ true true (f₁ y) (f₂ y)} =
        {y | FarBetween ε (g y) t₀ (f₁ y) (f₂ y)} := by ext y; simp [CrossPairOK]
    rw [this]; exact hFB

theorem isClosed_mem_window_comp {f : Y → ℝ} (hf : Continuous f) :
    IsClosed {y | g y (f y) ∈ locWindow ε (g y) t₀} := by
  have : {y | g y (f y) ∈ locWindow ε (g y) t₀} =
      {y | ∃ u ∈ Icc (t₀ - ε) (t₀ + ε), (y, u) ∈ {q : Y × ℝ | g q.1 (f q.1) = g q.1 q.2}} := by
    ext y
    simp only [locWindow, mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, h⟩; exact ⟨u, hu, h.symm⟩
    · rintro ⟨u, hu, h⟩; exact ⟨u, hu, h.symm⟩
  rw [this]
  exact isClosed_exists_mem_of_isCompact isCompact_Icc
    (isClosed_eq (continuous_eval.comp ((hg.comp continuous_fst).prodMk (hf.comp continuous_fst)))
      (continuous_eval.comp ((hg.comp continuous_fst).prodMk continuous_snd)))

end Closed

theorem isClosed_crossingDataN (ε t₀ : ℝ) (n : ℕ) {N : ℕ} (τ : Fin N → Bool) :
    IsClosed {p : C(ℝ, ℂ) × (Fin N → ℝ) | CrossingDataN ε p.1 t₀ n τ p.2} := by
  have heq : {p : C(ℝ, ℂ) × (Fin N → ℝ) | CrossingDataN ε p.1 t₀ n τ p.2} =
      (⋂ i, {p : C(ℝ, ℂ) × (Fin N → ℝ) | p.1 (p.2 i) ∈ locWindow ε p.1 t₀}) ∩
      ((⋂ i, {p : C(ℝ, ℂ) × (Fin N → ℝ) | FarSideN ε p.1 t₀ n (τ i) (p.2 i)}) ∩
      (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), {p : C(ℝ, ℂ) × (Fin N → ℝ) |
        CrossPairOK ε p.1 t₀ (τ i) (τ j) (p.2 i) (p.2 j)})) := by
    ext p; simp only [mem_ofPred_eq, CrossingDataN, mem_inter_iff, mem_iInter]
  rw [heq]
  refine IsClosed.inter (isClosed_iInter fun i => ?_) (IsClosed.inter (isClosed_iInter fun i => ?_)
    (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_))
  · exact isClosed_mem_window_comp continuous_fst ((continuous_apply i).comp continuous_snd)
  · exact isClosed_farSideN_comp continuous_fst n (τ i) ((continuous_apply i).comp continuous_snd)
  · exact isClosed_crossPairOK_comp continuous_fst (τ i) (τ j)
      ((continuous_apply i).comp continuous_snd) ((continuous_apply j).comp continuous_snd)

/-- **`deg^ε_out` is Borel** on `C(ℝ, ℂ)` (`ε ≥ 0`). -/
theorem measurable_locDegOut {ε : ℝ} (hε : 0 ≤ ε) (t₀ : ℝ) :
    Measurable fun c : C(ℝ, ℂ) => locDegOut ε c t₀ := by
  refine measurable_of_le_enat fun k => ?_
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero, zero_le, ofPred_true, MeasurableSet.univ]
  have heq : {c : C(ℝ, ℂ) | (k : ℕ∞) ≤ locDegOut ε c t₀} =
      {c : C(ℝ, ℂ) | 0 < diam (locWindow ε c t₀)} ∩
        ⋃ τ : Fin k → Bool, ⋃ n : ℕ,
          {c | ∃ t : Fin k → ℝ, (c, t) ∈ {p : C(ℝ, ℂ) × (Fin k → ℝ) | CrossingDataN ε p.1 t₀ n τ p.2}} := by
    ext c
    simp only [mem_ofPred_eq, le_locDegOut_iff, exists_degOutFamily_iff c.continuous hε hpos,
      mem_inter_iff, mem_iUnion, crossingData_iff_exists]
    constructor
    · rintro ⟨hD, τ, t, n, h⟩; exact ⟨hD, τ, n, t, h⟩
    · rintro ⟨hD, τ, n, t, h⟩; exact ⟨hD, τ, t, n, h⟩
  rw [heq]
  refine (isOpen_lt continuous_const (continuous_diam_window ε t₀)).measurableSet.inter ?_
  exact MeasurableSet.iUnion fun τ => MeasurableSet.iUnion fun n =>
    measurableSet_exists_of_isClosed (isClosed_crossingDataN ε t₀ n τ)

/-- **`u^ε_*` is Borel** on `C(ℝ, ℂ)` (`ε ≥ 0`). -/
theorem measurable_locUStar {ε : ℝ} (hε : 0 ≤ ε) (t₀ : ℝ) :
    Measurable fun c : C(ℝ, ℂ) => locUStar ε c t₀ := by
  have h1 := measurable_locDA ε t₀
  have h2 := measurable_locDegIn ε t₀
  have h3 := measurable_locDegOut hε t₀
  have h4 : Measurable fun c : C(ℝ, ℂ) => locDegIn ε c t₀ + locDegOut ε c t₀ :=
    (measurable_of_countable (fun p : ℕ∞ × ℕ∞ => p.1 + p.2)).comp (h2.prodMk h3)
  exact h1.mul ((measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp h4)

end MatedCRTHarmonic.GMS4b
