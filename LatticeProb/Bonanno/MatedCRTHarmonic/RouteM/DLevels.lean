/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.DLevels at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.DGeometry

/-!
# Route M, the explicit drawing `D` (Proposition M2): chord levels and ports

The drawing construction and Details (d2). For a non-consecutive pair
`x < y` and a continuous coordinate `X` (`X = L` or `X = R`):

* the level window `(dWinLo, dWinHi) = (max(inf_{I_x} X, inf_{I_y} X), inf_{[εx, ε(y−1)]} X)`; condition (1.1) of
  [18] is `dWinLo ≤ dWinHi` (`sideCond_iff_dWin`), and G0 (`SideStrict`) makes it strict;
* `dLevel ε X x y`, a level in the window when it is non-empty (`dLevel_mem`), of the form `q + n√2` with `q ∈ ℚ` and
  `n` the code of the pair `(x, y)`; hence **distinct pairs have distinct levels** (`dLevel_injective`, Details (d2):
  "all L-levels are chosen pairwise distinct");
* the ports `dPort₁ = ℓ⁻(εx, λ) ∈ int I_x` and `dPort₂ = ℓ⁺(ε(y−1), λ) ∈ int I_y`, between which `X` makes a direct
  excursion above `λ` (`lowArcData_dPorts`: the data `LowArcData` of `RouteM/DGeometry.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Function

namespace MatedCRTHarmonic.RouteM

section Windows

variable (ε : ℝ)

/-- Lower end of the level window of the pair `x < y` for the coordinate `X`: `max(inf_{I_x} X, inf_{I_y} X)`. -/
def dWinLo (X : ℝ → ℝ) (x y : ℤ) : ℝ :=
  max (MatedCRT.intervalInf X (ε * ((x : ℝ) - 1)) (ε * x))
    (MatedCRT.intervalInf X (ε * ((y : ℝ) - 1)) (ε * y))

/-- Upper end of the level window of the pair `x < y` for the coordinate `X`: `inf_{[εx, ε(y−1)]} X`. -/
def dWinHi (X : ℝ → ℝ) (x y : ℤ) : ℝ := MatedCRT.intervalInf X (ε * x) (ε * ((y : ℝ) - 1))

/-- A rational number in `(a, b)` when `a < b` (junk `0` otherwise). -/
def DAux.ratBetween (a b : ℝ) : ℚ := if h : a < b then Classical.choose (exists_rat_btwn h) else 0

theorem DAux.ratBetween_spec {a b : ℝ} (h : a < b) :
    a < DAux.ratBetween a b ∧ (DAux.ratBetween a b : ℝ) < b := by
  have hq : DAux.ratBetween a b = Classical.choose (exists_rat_btwn h) := by
    simp only [DAux.ratBetween, h, dite_true]
  rw [hq]
  exact Classical.choose_spec (exists_rat_btwn h)

/-- The code of a pair of integers, a natural number (`Encodable.encode`), seen in `ℝ`. -/
def dCode (x y : ℤ) : ℝ := (Encodable.encode (x, y) : ℕ)

/-- The chord level of the pair `(x, y)` for the coordinate `X` (TF3 §5.2): `q + dCode x y · √2` with `q` rational,
chosen so that the level lies in the window whenever the window is non-empty. -/
def dLevel (X : ℝ → ℝ) (x y : ℤ) : ℝ :=
  (DAux.ratBetween (dWinLo ε X x y - dCode x y * √2) (dWinHi ε X x y - dCode x y * √2) : ℝ) +
    dCode x y * √2

variable {ε}

theorem dLevel_mem {X : ℝ → ℝ} {x y : ℤ} (h : dWinLo ε X x y < dWinHi ε X x y) :
    dWinLo ε X x y < dLevel ε X x y ∧ dLevel ε X x y < dWinHi ε X x y := by
  have := DAux.ratBetween_spec (sub_lt_sub_right h (dCode x y * √2))
  unfold dLevel
  constructor <;> linarith [this.1, this.2]

/-- **Distinct levels** (TF3 Details (d2)): the levels of distinct pairs differ (for any coordinates). -/
theorem dLevel_injective {X X' : ℝ → ℝ} {x y x' y' : ℤ} (h : dLevel ε X x y = dLevel ε X' x' y') :
    x = x' ∧ y = y' := by
  have hcode : Encodable.encode (x, y) = Encodable.encode (x', y') := by
    by_contra hne
    have hz : ((Encodable.encode (x, y) : ℕ) : ℤ) - (Encodable.encode (x', y') : ℕ) ≠ 0 := by
      intro h0
      exact hne (by exact_mod_cast sub_eq_zero.mp h0)
    have hirr := irrational_sqrt_two.intCast_mul hz
    apply hirr.ne_rat (DAux.ratBetween (dWinLo ε X' x' y' - dCode x' y' * √2)
        (dWinHi ε X' x' y' - dCode x' y' * √2) -
      DAux.ratBetween (dWinLo ε X x y - dCode x y * √2) (dWinHi ε X x y - dCode x y * √2))
    unfold dLevel at h
    unfold dCode at h ⊢
    push_cast
    linear_combination h
  have := Encodable.encode_injective hcode
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

end Windows

/-! ### Last and first contacts, ports -/

section Ports

variable (ε : ℝ)

/-- The last time `≤ t` at which `X ≤ λ` (TF3 §5.1's `ℓ⁻(t, λ)` for the coordinate `X`). -/
def dLast (X : ℝ → ℝ) (t lev : ℝ) : ℝ := sSup {s | s ≤ t ∧ X s ≤ lev}

/-- The first time `≥ t` at which `X ≤ λ` (TF3 §5.1's `ℓ⁺(t, λ)` for the coordinate `X`). -/
def dFirst (X : ℝ → ℝ) (t lev : ℝ) : ℝ := sInf {s | t ≤ s ∧ X s ≤ lev}

/-- The port of the pair `(x, y)` in the cell of `x` (TF3 §5.2: `t₁ = ℓ⁻(εx, λ_{xy})`). -/
def dPort₁ (X : ℝ → ℝ) (x y : ℤ) : ℝ := dLast X (ε * x) (dLevel ε X x y)

/-- The port of the pair `(x, y)` in the cell of `y` (TF3 §5.2: `t₂ = ℓ⁺(ε(y − 1), λ_{xy})`). -/
def dPort₂ (X : ℝ → ℝ) (x y : ℤ) : ℝ := dFirst X (ε * ((y : ℝ) - 1)) (dLevel ε X x y)

variable {ε}

/-- The infimum of a continuous function over a non-empty compact interval is attained and is a lower bound. -/
theorem DAux.intervalInf_spec {X : ℝ → ℝ} (hX : Continuous X) {a b : ℝ} (hab : a ≤ b) :
    (∃ s ∈ Icc a b, X s = MatedCRT.intervalInf X a b) ∧ ∀ s ∈ Icc a b, MatedCRT.intervalInf X a b ≤ X s := by
  have hK : IsCompact (X '' Icc a b) := isCompact_Icc.image hX
  have hne : (X '' Icc a b).Nonempty := (nonempty_Icc.mpr hab).image X
  refine ⟨?_, fun s hs => csInf_le hK.bddBelow ⟨s, hs, rfl⟩⟩
  obtain ⟨s, hs, hXs⟩ := hK.sInf_mem hne
  exact ⟨s, hs, hXs⟩

/-- **The ports of a chord** (TF3 §5.2): for a level `λ` strictly inside the window of a non-consecutive pair
`x < y`, the last contact `t₁ = ℓ⁻(εx, λ)` lies in `int I_x`, the first contact `t₂ = ℓ⁺(ε(y−1), λ)` lies in
`int I_y`, `X(t₁) = λ`, and `X` makes a direct excursion above `λ` from `t₁` to `t₂`. -/
theorem lowArcData_contacts {X : ℝ → ℝ} (hX : Continuous X) (hε : 0 < ε) {x y : ℤ} (hxy : x + 1 < y)
    {lev : ℝ} (hlo : dWinLo ε X x y < lev) (hhi : lev < dWinHi ε X x y) :
    LowArcData ε X x y (dLast X (ε * x) lev) (dFirst X (ε * ((y : ℝ) - 1)) lev) ∧
      X (dLast X (ε * x) lev) = lev := by
  set a : ℝ := ε * ((x : ℝ) - 1)
  set b : ℝ := ε * x
  set c : ℝ := ε * ((y : ℝ) - 1)
  set d : ℝ := ε * y
  have hab : a < b := by simp only [a, b]; nlinarith
  have hbc : b < c := by
    have : (x : ℝ) + 1 < y := by exact_mod_cast hxy
    simp only [b, c]; nlinarith
  have hcd : c < d := by simp only [c, d]; nlinarith
  -- the three infima
  obtain ⟨⟨s₀, hs₀, hXs₀⟩, -⟩ := DAux.intervalInf_spec hX hab.le
  obtain ⟨-, hmid⟩ := DAux.intervalInf_spec hX hbc.le
  obtain ⟨⟨s₁, hs₁, hXs₁⟩, -⟩ := DAux.intervalInf_spec hX hcd.le
  have hlo₁ : MatedCRT.intervalInf X a b < lev := lt_of_le_of_lt (le_max_left _ _) hlo
  have hlo₂ : MatedCRT.intervalInf X c d < lev := lt_of_le_of_lt (le_max_right _ _) hlo
  have hXb : lev < X b := lt_of_lt_of_le hhi (hmid b ⟨le_rfl, hbc.le⟩)
  have hXc : lev < X c := lt_of_lt_of_le hhi (hmid c ⟨hbc.le, le_rfl⟩)
  have hhi' : lev < MatedCRT.intervalInf X b c := hhi
  -- the last contact before `b`
  set A₁ : Set ℝ := {s | s ≤ b ∧ X s ≤ lev}
  have hA₁c : IsClosed A₁ := isClosed_Iic.inter (isClosed_Iic.preimage hX)
  have hs₀A : s₀ ∈ A₁ := ⟨hs₀.2, by rw [hXs₀]; exact hlo₁.le⟩
  have hA₁b : BddAbove A₁ := ⟨b, fun s hs => hs.1⟩
  set p₁ : ℝ := dLast X b lev
  have hp₁A : p₁ ∈ A₁ := hA₁c.csSup_mem ⟨s₀, hs₀A⟩ hA₁b
  have hs₀p₁ : s₀ ≤ p₁ := le_csSup hA₁b hs₀A
  have hXp₁ : X p₁ = lev := by
    obtain ⟨s, hs, hXs⟩ := intermediate_value_Icc hp₁A.1 hX.continuousOn ⟨hp₁A.2, hXb.le⟩
    have hsA : s ∈ A₁ := ⟨hs.2, hXs.le⟩
    have : s ≤ p₁ := le_csSup hA₁b hsA
    rw [← le_antisymm this hs.1]
    exact hXs
  -- the first contact after `c`
  set A₂ : Set ℝ := {s | c ≤ s ∧ X s ≤ lev}
  have hA₂c : IsClosed A₂ := isClosed_Ici.inter (isClosed_Iic.preimage hX)
  have hs₁A : s₁ ∈ A₂ := ⟨hs₁.1, by rw [hXs₁]; exact hlo₂.le⟩
  have hA₂b : BddBelow A₂ := ⟨c, fun s hs => hs.1⟩
  set p₂ : ℝ := dFirst X c lev
  have hp₂A : p₂ ∈ A₂ := hA₂c.csInf_mem ⟨s₁, hs₁A⟩ hA₂b
  have hp₂s₁ : p₂ ≤ s₁ := csInf_le hA₂b hs₁A
  have hXp₂ : X p₂ = lev := by
    obtain ⟨s, hs, hXs⟩ := intermediate_value_Icc' hp₂A.1 hX.continuousOn ⟨hp₂A.2, hXc.le⟩
    have hsA : s ∈ A₂ := ⟨hs.1, hXs.le⟩
    have : p₂ ≤ s := csInf_le hA₂b hsA
    rw [← le_antisymm hs.2 this]
    exact hXs
  -- positions of the ports
  have hp₁a : a < p₁ := by
    refine lt_of_le_of_lt hs₀.1 (lt_of_le_of_ne hs₀p₁ ?_)
    intro h
    rw [h, hXp₁] at hXs₀
    linarith
  have hp₁b : p₁ < b := lt_of_le_of_ne hp₁A.1 (fun h => by rw [h] at hXp₁; linarith)
  have hp₂c : c < p₂ := lt_of_le_of_ne hp₂A.1 (fun h => by rw [← h] at hXp₂; linarith)
  have hp₂d : p₂ < d := by
    refine lt_of_lt_of_le (lt_of_le_of_ne hp₂s₁ ?_) hs₁.2
    intro h
    rw [← h, hXp₂] at hXs₁
    linarith
  refine ⟨⟨by omega, ⟨hp₁a, hp₁b⟩, ⟨hp₂c, hp₂d⟩, ⟨by linarith, by rw [hXp₁, hXp₂], ?_⟩⟩, hXp₁⟩
  intro u hu
  rw [hXp₁]
  by_contra hle
  push Not at hle
  rcases le_or_gt u b with hub | hbu
  · have : u ≤ p₁ := le_csSup hA₁b ⟨hub, hle⟩
    linarith [hu.1]
  rcases le_or_gt u c with huc | hcu
  · linarith [hmid u ⟨hbu.le, huc⟩, hhi']
  · have : p₂ ≤ u := csInf_le hA₂b ⟨hcu.le, hle⟩
    linarith [hu.2]

/-- The ports of a pair whose window is non-empty form the data of a lower arc, at the level `dLevel`. -/
theorem lowArcData_dPorts {X : ℝ → ℝ} (hX : Continuous X) (hε : 0 < ε) {x y : ℤ} (hxy : x + 1 < y)
    (hwin : dWinLo ε X x y < dWinHi ε X x y) :
    LowArcData ε X x y (dPort₁ ε X x y) (dPort₂ ε X x y) ∧ X (dPort₁ ε X x y) = dLevel ε X x y :=
  lowArcData_contacts hX hε hxy (dLevel_mem hwin).1 (dLevel_mem hwin).2

end Ports

end MatedCRTHarmonic.RouteM
