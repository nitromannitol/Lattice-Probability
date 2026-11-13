/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Paths.Measurable at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Paths.Compare
import LatticeProb.Bonanno.HigherDimLFPP.Paths.Polygon
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.CompactOpen

/-!
# Rational polygons, measurability of internal LFPP distances, the frozen distance

Packet P-X1, targets T3 and T4 (audit HA5, Details D1(a)–(b), §4.3 row X4, risk R5; source App. A.1,
"rational polygonal approximation also gives measurability").

* `ratPoly x y q`: the polygonal path from `x` to `y` through the rational points (`ℚ^d ⊆ ℝ^d`)
  listed by the index `q : RatPolyIdx d = Σ M, Fin M → ℚ^d`, a countable type.
* `lfppDistOn_eq_iInf_ratPoly`: **for open `V` and continuous `φ`, the infimum over the countable,
  field-independent family of rational polygons inside `V` equals `lfppDistOn ζ φ V x y`** (from
  the polygonal approximation `exists_polygonPath_le` with the dense set `ℚ^d`).
* `measurable_lfppLength`, `measurable_lfppDistOn`: for a random field `H` with continuous paths
  and measurable values, `ω ↦ lfppDistOn ζ (H · ω) V x y` is measurable (`V` open).
* `measurable_lfppDistOn_continuousMap`: `φ ↦ lfppDistOn ζ φ V x y` is Borel on `C(ℝ^d, ℝ)`
  (compact-open topology, any `OpensMeasurableSpace` structure).
* T4: `lfppDistance_pos` (in `Paths/DistOn.lean`) and `measurable_lfppDistance`,
  `IsBandVersion.measurable_lfppDistance`: for continuous measurable fields the frozen
  `D^ζ_{ε,d}` is a measurable random variable, so `IsLFPPExponent` involves no outer measure.

2D source: `LQGMetric/Papers/DDDF/LenCountable.lean` (`measurable_lfppLen`,
`measurable_crossLenIn`; there the countable family comes from the separability of `C(ℂ, ℝ)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLFPP

variable {d : ℕ}

/-! ## Rational points and rational polygons -/

/-- The point of `ℝ^d` with rational coordinates `q`. -/
def ratPt (q : Fin d → ℚ) : Rd d := WithLp.toLp 2 (fun i => (q i : ℝ))

theorem denseRange_ratPt : DenseRange (ratPt (d := d)) := by
  have h1 : DenseRange (Pi.map fun _ : Fin d => ((↑) : ℚ → ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  have h2 : DenseRange (WithLp.toLp 2 : (Fin d → ℝ) → Rd d) :=
    (WithLp.toLp_surjective 2).denseRange
  exact h2.comp h1 (PiLp.continuous_toLp 2 _)

theorem dense_range_ratPt : Dense (range (ratPt (d := d))) := denseRange_ratPt

/-- Index of the rational polygons: the number `M` of interior vertices and the vertices. -/
abbrev RatPolyIdx (d : ℕ) : Type := (M : ℕ) × (Fin M → Fin d → ℚ)

/-- Vertices of the rational polygon `q` from `x` to `y`: `x`, the `M` rational points, `y`. -/
def ratVert (x y : Rd d) (q : RatPolyIdx d) (i : ℕ) : Rd d :=
  if i = 0 then x else if h : i - 1 < q.1 then ratPt (q.2 ⟨i - 1, h⟩) else y

/-- The rational polygon `q` from `x` to `y` (`M + 1` edges). -/
def ratPoly (x y : Rd d) (q : RatPolyIdx d) : ℝ → Rd d := polygonPath (ratVert x y q) (q.1 + 1)

theorem ratVert_zero (x y : Rd d) (q : RatPolyIdx d) : ratVert x y q 0 = x := by
  simp [ratVert]

theorem ratVert_last (x y : Rd d) (q : RatPolyIdx d) : ratVert x y q (q.1 + 1) = y := by
  simp [ratVert]

theorem isPcwC1Path_ratPoly (x y : Rd d) (q : RatPolyIdx d) : IsPcwC1Path (ratPoly x y q) x y := by
  have := isPcwC1Path_polygonPath (ratVert x y q) (q.1 + 1)
  rwa [ratVert_zero, ratVert_last] at this

/-- **Rational polygonal approximation**: inside an open set, every piecewise `C¹` path is
approximated in LFPP length by rational polygons with the same endpoints. -/
theorem exists_ratPoly_le {V : Set (Rd d)} (hV : IsOpen V) {ζ : ℝ} {φ : Rd d → ℝ}
    (hφ : Continuous φ) {γ : ℝ → Rd d} {x y : Rd d} (hγ : IsPcwC1Path γ x y)
    (hγV : MapsTo γ (Icc 0 1) V) {η : ℝ} (hη : 0 < η) :
    ∃ q : RatPolyIdx d, MapsTo (ratPoly x y q) (Icc 0 1) V ∧
      lfppLength ζ φ (ratPoly x y q) ≤ lfppLength ζ φ γ + η := by
  classical
  obtain ⟨N, p, hN, hp0, hpN, hpS, hpV, hpL⟩ :=
    exists_polygonPath_le (dense_range_ratPt (d := d)) hV hφ hγ hγV (ζ := ζ) hη
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hex : ∀ j : Fin M, ∃ r : Fin d → ℚ, ratPt r = p (j + 1) := fun j =>
    hpS (j + 1) (Nat.succ_pos _) (by omega)
  choose qv hqv using hex
  have hcongr : ratPoly x y ⟨M, qv⟩ = polygonPath p (M + 1) := by
    refine polygonPath_congr (N := M + 1) fun i (hi : i ≤ M + 1) => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [ratVert_zero, hp0]
    rcases hi.lt_or_eq with hiM | rfl
    · have h1 : i - 1 < M := by omega
      have hne : i ≠ 0 := by omega
      show (if i = 0 then x else if h : i - 1 < M then ratPt (qv ⟨i - 1, h⟩) else y) = p i
      rw [ite_eq_right hne, dite_eq_left h1, hqv]
      show p (i - 1 + 1) = p i
      congr 1
      omega
    · rw [ratVert_last, hpN]
  exact ⟨⟨M, qv⟩, hcongr ▸ hpV, hcongr ▸ hpL⟩

/-- **The countable family** (HA5 D1, App. A.1): for open `V` and continuous `φ`, the internal
LFPP distance is the infimum over the rational polygons from `x` to `y` inside `V`. -/
theorem lfppDistOn_eq_iInf_ratPoly {V : Set (Rd d)} (hV : IsOpen V) {ζ : ℝ} {φ : Rd d → ℝ}
    (hφ : Continuous φ) (x y : Rd d) :
    lfppDistOn ζ φ V x y =
      ⨅ q : {q : RatPolyIdx d // MapsTo (ratPoly x y q) (Icc 0 1) V},
        lfppLength ζ φ (ratPoly x y q.1) := by
  by_cases hj : PcwJoined V x y
  · obtain ⟨γ₀, hγ₀, hγ₀V⟩ := hj
    have hne : Nonempty {q : RatPolyIdx d // MapsTo (ratPoly x y q) (Icc 0 1) V} := by
      obtain ⟨q, hq, -⟩ := exists_ratPoly_le hV hφ hγ₀ hγ₀V (ζ := ζ) one_pos
      exact ⟨⟨q, hq⟩⟩
    refine le_antisymm (le_ciInf fun q => lfppDistOn_le_lfppLength (isPcwC1Path_ratPoly x y q.1)
      q.2) (le_lfppDistOn ⟨γ₀, hγ₀, hγ₀V⟩ fun γ hγ hγV => ?_)
    refine le_of_forall_pos_le_add fun η hη => ?_
    obtain ⟨q, hq, hqL⟩ := exists_ratPoly_le hV hφ hγ hγV (ζ := ζ) hη
    exact (ciInf_le (bddBelow_range_lfppLength ζ φ fun q :
      {q : RatPolyIdx d // MapsTo (ratPoly x y q) (Icc 0 1) V} => ratPoly x y q.1)
      ⟨q, hq⟩).trans hqL
  · rw [lfppDistOn_of_not_pcwJoined hj]
    have : IsEmpty {q : RatPolyIdx d // MapsTo (ratPoly x y q) (Icc 0 1) V} :=
      ⟨fun q => hj ⟨_, isPcwC1Path_ratPoly x y q.1, q.2⟩⟩
    exact (Real.iInf_of_isEmpty _).symm

/-! ## Measurability -/

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- For a random field with continuous paths and measurable values, the LFPP length of a fixed
path continuous on `[0,1]` is measurable in `ω`. -/
theorem measurable_lfppLength {H : Rd d → Ω → ℝ} (hc : ∀ ω, Continuous fun z => H z ω)
    (hm : ∀ z, Measurable (H z)) {γ : ℝ → Rd d} (hγ : ContinuousOn γ (Icc 0 1)) (ζ : ℝ) :
    Measurable fun ω => lfppLength ζ (fun z => H z ω) γ := by
  set γ' : ℝ → Rd d := fun t => γ (projIcc (0 : ℝ) 1 zero_le_one t) with hγ'def
  have hγ' : Continuous γ' :=
    hγ.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun t =>
      (projIcc _ _ _ t).2
  have heq : ∀ ω, lfppLength ζ (fun z => H z ω) γ =
      ∫ t in Ioc (0 : ℝ) 1, Real.exp (ζ * H (γ' t) ω) * ‖deriv γ t‖ := by
    intro ω
    rw [lfppLength, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    simp only [hγ'def, projIcc_of_mem zero_le_one (Ioc_subset_Icc_self ht)]
  simp_rw [heq]
  have hH : Measurable (Function.uncurry H) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  have hF : StronglyMeasurable
      (fun p : Ω × ℝ => Real.exp (ζ * H (γ' p.2) p.1) * ‖deriv γ p.2‖) := by
    refine Measurable.stronglyMeasurable ?_
    exact (((hH.comp ((hγ'.measurable.comp measurable_snd).prodMk measurable_fst)).const_mul
      ζ).exp).mul ((measurable_deriv γ).comp measurable_snd).norm
  exact (hF.integral_prod_right' (ν := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))).measurable

/-- **Measurability of internal LFPP distances** (HA5 D1(b), X4): for open `V` and a random field
`H` with continuous paths and measurable values, `ω ↦ D_V(x,y)(H(·, ω))` is measurable. -/
theorem measurable_lfppDistOn {H : Rd d → Ω → ℝ} (hc : ∀ ω, Continuous fun z => H z ω)
    (hm : ∀ z, Measurable (H z)) {V : Set (Rd d)} (hV : IsOpen V) (ζ : ℝ) (x y : Rd d) :
    Measurable fun ω => lfppDistOn ζ (fun z => H z ω) V x y := by
  have heq : (fun ω => lfppDistOn ζ (fun z => H z ω) V x y) = fun ω =>
      ⨅ q : {q : RatPolyIdx d // MapsTo (ratPoly x y q) (Icc 0 1) V},
        lfppLength ζ (fun z => H z ω) (ratPoly x y q.1) :=
    funext fun ω => lfppDistOn_eq_iInf_ratPoly hV (hc ω) x y
  rw [heq]
  exact Measurable.iInf fun q =>
    measurable_lfppLength hc hm (isPcwC1Path_ratPoly x y q.1).continuousOn ζ

/-- **Borel measurability on continuous fields**: `φ ↦ D_V(x,y)(φ)` is measurable on `C(ℝ^d, ℝ)`
for every measurable structure containing the open sets of the compact-open topology. -/
theorem measurable_lfppDistOn_continuousMap [MeasurableSpace C(Rd d, ℝ)]
    [OpensMeasurableSpace C(Rd d, ℝ)] {V : Set (Rd d)} (hV : IsOpen V) (ζ : ℝ) (x y : Rd d) :
    Measurable fun φ : C(Rd d, ℝ) => lfppDistOn ζ φ V x y :=
  measurable_lfppDistOn (H := fun z (φ : C(Rd d, ℝ)) => φ z) (fun φ => φ.continuous)
    (fun z => (continuous_eval_const z).measurable) hV ζ x y

/-- **Measurability of the frozen LFPP distance** (T4): for a random field with continuous paths and
measurable values, `ω ↦ D^ζ(H(·, ω))` is measurable. -/
theorem measurable_lfppDistance {H : Rd d → Ω → ℝ} (hc : ∀ ω, Continuous fun z => H z ω)
    (hm : ∀ z, Measurable (H z)) (ζ : ℝ) :
    Measurable fun ω => lfppDistance d ζ (fun z => H z ω) := by
  simp_rw [lfppDistance_eq_lfppDistOn]
  exact measurable_lfppDistOn hc hm (isOpen_cube d) ζ 0 (e₁ d)

/-- The frozen distance of a continuous version of a band field is measurable. -/
theorem IsBandVersion.measurable_lfppDistance {P : Measure Ω} {W : WN d → Ω → ℝ}
    {κ : Rd d → ℝ} {a b : ℝ} {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H) (ζ : ℝ) :
    Measurable fun ω => lfppDistance d ζ (fun z => H z ω) :=
  HigherDimLFPP.measurable_lfppDistance hH.continuous hH.measurable ζ

end Measurability

end HigherDimLFPP
