/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsBRateCellFamily at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBRateAnnulus38

/-!
# The itinerary, annulus-disconnection estimate, and [18] Lemma 3.11 with explicit rates

Continuation of `EpsBRateAnnulus38`: the landed producers
`CellFamily.itineraryEstimateBad_of_lemma38Bad_fixed2` (rate `min a₂₇ a₈`), `CellFamily.cellFamily_compl_of_interfaces_bad`
(rate `min a₂₇ aᵢ / 4`, grid exponent `χ = min a₂₇ aᵢ / 6`) and `T15A.lemma311Bad_of_cellFamily` (rate unchanged)
are copied with their statements changed only by fixing the rates (bodies verbatim; private mesh helpers replaced by
`EpsB.mesh_pos`, `EpsB.mesh_le_one`, `EpsB.mesh_antitone`, `epsB_eventually_rpow_lt`).

* `ItinRate F ρ a` — `CellFamily.ItineraryEstimateBad F ρ` with rate `a`; `itinRate_of_l38Rate`;
* `sgcRate_of_itinRate` — the annulus-disconnection estimate (`ScaledGridControl`) at rate `min a27 ai / 4`;
* `lemma311Rate_of_sgc` — [18] Lemma 3.11 at the same rate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.EpsB

open MatedCRTHarmonic
open MatedCRTHarmonic.CellFamily (mesh RandomCellFamily DiameterGood PolarItineraryGood Lemma38EnvironmentGood
  GraphConnected GraphLoopless TemplateSeparation FiniteGridCount WaypointStrongMarkovInputFixed2 gridCenter
  gridRadius GridEnvironmentGood measure_finset_iInter_compl_le_card_mul scaledGridControl_of_good_environment)

theorem epsB_eventually_rpow_lt (a : ℝ) (ha : 0 < a) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, mesh k ^ a < c :=
  Lemma38Source.eventually_meshPow_lt ha hc

/-- `CellFamily.ItineraryEstimateBad F ρ` with the rate exponent `a` fixed. -/
def ItinRate (F : RandomCellFamily) (ρ a : ℝ) : Prop :=
  ∃ s₀ βᵢ Cᵢ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 10 ∧ 0 < βᵢ ∧
    ∀ k (z : ℂ) (r : ℝ), mesh k ^ βᵢ ≤ r → r ≤ ρ → ball z (2 * r) ⊆ ball (0 : ℂ) ρ →
      F.P (PolarItineraryGood F k z r s₀)ᶜ ≤ ENNReal.ofReal (Cᵢ * mesh k ^ a)

/-- **The itinerary estimate with its rate `min a27 a8` exposed** (body of
`CellFamily.itineraryEstimateBad_of_lemma38Bad_fixed2`). -/
theorem itinRate_of_l38Rate (F : RandomCellFamily) (q ρ : ℝ) {a27 C27 a8 : ℝ} (ha27 : 0 < a27)
    (h27 : ∀ k, F.P (DiameterGood F k q ρ)ᶜ ≤ ENNReal.ofReal (C27 * mesh k ^ a27)) (ha8 : 0 < a8)
    (h38 : L38Rate F ρ a8)
    (hConnected : GraphConnected F) (hLoopless : GraphLoopless F)
    (hq : 0 < q) (hway : WaypointStrongMarkovInputFixed2 F q ρ) : ItinRate F ρ (min a27 a8) := by
  classical
  have h27bad := h27
  rcases h38 with ⟨b8, hb8, A8, C8, h38bad⟩
  rcases hway hConnected hLoopless b8 A8 hb8 hq with
    ⟨s₀, βᵢ, hs₀, hs₀le, hβᵢ, hβᵢ8, hβᵢq, _hA, hproducer⟩
  let aᵢ : ℝ := min a27 a8
  let C₀ : ℝ := max 0 (max C27 C8)
  let N : ℕ := ⌈4 * 10 ^ 5 / s₀ ^ 2⌉₊
  let Cᵢ : ℝ := ((N + 1 : ℕ) : ℝ) * C₀
  have haᵢ : 0 < aᵢ := lt_min ha27 ha8
  have hC₀ : 0 ≤ C₀ := le_max_left _ _
  have hC27 : C27 ≤ C₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC8 : C8 ≤ C₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hCᵢ : 0 ≤ Cᵢ := mul_nonneg (Nat.cast_nonneg _) hC₀
  have hpow27 (k : ℕ) : mesh k ^ a27 ≤ mesh k ^ aᵢ :=
    Real.rpow_le_rpow_of_exponent_ge (EpsB.mesh_pos k) (EpsB.mesh_le_one k)
      (min_le_left _ _)
  have hpow8 (k : ℕ) : mesh k ^ a8 ≤ mesh k ^ aᵢ :=
    Real.rpow_le_rpow_of_exponent_ge (EpsB.mesh_pos k) (EpsB.mesh_le_one k)
      (min_le_right _ _)
  have hlarge : ∀ᶠ k : ℕ in atTop,
      mesh k ^ (b8 - βᵢ) < 1 / 100 ∧ mesh k ^ b8 < s₀ ∧ mesh k ^ (q - βᵢ) < s₀ / 100 := by
    filter_upwards [epsB_eventually_rpow_lt (b8 - βᵢ) (by linarith)
        (by norm_num : (0 : ℝ) < 1 / 100),
      epsB_eventually_rpow_lt b8 hb8 hs₀,
      epsB_eventually_rpow_lt (q - βᵢ) (by linarith) (by positivity : (0 : ℝ) < s₀ / 100)]
      with k h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hlarge
  let C : ℝ := Cᵢ + (mesh K ^ aᵢ)⁻¹ + 1
  have hKpos : 0 < mesh K ^ aᵢ := Real.rpow_pos_of_pos (EpsB.mesh_pos K) aᵢ
  have hC : Cᵢ ≤ C := by
    have : 0 ≤ (mesh K ^ aᵢ)⁻¹ := inv_nonneg.mpr hKpos.le
    dsimp [C]
    linarith
  refine ⟨s₀, βᵢ, C, hs₀, hs₀le, hβᵢ, ?_⟩
  intro k z r hr hρ hball
  by_cases hk : K ≤ k
  · obtain ⟨hk8, hks, hkq⟩ := hK k hk
    have hβpos : 0 < mesh k ^ βᵢ := Real.rpow_pos_of_pos (EpsB.mesh_pos k) βᵢ
    have hrWaypoint : mesh k ^ b8 ≤ r / 100 := by
      have hsplit : mesh k ^ b8 = mesh k ^ βᵢ * mesh k ^ (b8 - βᵢ) := by
        rw [← Real.rpow_add (EpsB.mesh_pos k) βᵢ (b8 - βᵢ)]
        congr 1
        ring
      rw [hsplit]
      calc
        mesh k ^ βᵢ * mesh k ^ (b8 - βᵢ) ≤ mesh k ^ βᵢ * (1 / 100) :=
          mul_le_mul_of_nonneg_left hk8.le hβpos.le
        _ ≤ r / 100 := by linarith
    have hr100 : r / 100 ≤ ρ := by
      have hrnonneg : 0 ≤ r := hβpos.le.trans hr
      linarith
    have hqConf : mesh k ^ q ≤ s₀ * r / 100 := by
      have hsplitQ : mesh k ^ q = mesh k ^ βᵢ * mesh k ^ (q - βᵢ) := by
        rw [← Real.rpow_add (EpsB.mesh_pos k) βᵢ (q - βᵢ)]
        congr 1
        ring
      rw [hsplitQ]
      calc
        mesh k ^ βᵢ * mesh k ^ (q - βᵢ) ≤ mesh k ^ βᵢ * (s₀ / 100) :=
          mul_le_mul_of_nonneg_left hkq.le hβpos.le
        _ ≤ r * (s₀ / 100) := mul_le_mul_of_nonneg_right hr (by positivity)
        _ = s₀ * r / 100 := by ring
    obtain ⟨W, hWcard, -, -, hWball, hWproducer⟩ :=
      hproducer k z r hrWaypoint hks.le hqConf hr100 hball
    let idx : Finset (Option ℂ) := insert none (W.image some)
    let Ev : Option ℂ → Set F.Ω := fun i => match i with
      | none => DiameterGood F k q ρ
      | some w => Lemma38EnvironmentGood F k w (r / 100) b8 A8
    have hnone : none ∉ W.image some := by simp
    have hcardImage : (W.image some).card = W.card :=
      Finset.card_image_iff.mpr (fun x _ y _ hxy => Option.some.inj hxy)
    have hidxCard : idx.card ≤ N + 1 := by
      dsimp [idx]
      rw [Finset.card_insert_of_notMem hnone, hcardImage]
      exact Nat.add_le_add_right hWcard 1
    let δ : ℝ≥0∞ := ENNReal.ofReal (C₀ * mesh k ^ aᵢ)
    have hbad : ∀ i ∈ idx, F.P (Ev i)ᶜ ≤ δ := by
      intro i hi
      rcases i with _ | w
      · refine (h27bad k).trans (ENNReal.ofReal_le_ofReal ?_)
        calc
          C27 * mesh k ^ a27 ≤ C₀ * mesh k ^ a27 :=
            mul_le_mul_of_nonneg_right hC27 (Real.rpow_nonneg (EpsB.mesh_pos k).le _)
          _ ≤ C₀ * mesh k ^ aᵢ := mul_le_mul_of_nonneg_left (hpow27 k) hC₀
      · have hw : w ∈ W := by
          have : some w ∈ W.image some := (Finset.mem_insert.mp hi).resolve_left (by simp)
          rcases Finset.mem_image.mp this with ⟨a, ha, haw⟩
          simpa [Option.some.inj haw] using ha
        refine (h38bad k w (r / 100) hrWaypoint hr100 (hWball w hw)).trans
          (ENNReal.ofReal_le_ofReal ?_)
        calc
          C8 * mesh k ^ a8 ≤ C₀ * mesh k ^ a8 :=
            mul_le_mul_of_nonneg_right hC8 (Real.rpow_nonneg (EpsB.mesh_pos k).le _)
          _ ≤ C₀ * mesh k ^ aᵢ := mul_le_mul_of_nonneg_left (hpow8 k) hC₀
    have hQbad := measure_finset_iInter_compl_le_card_mul F.P idx Ev hbad
    have hmult : ((idx.card : ℝ≥0∞) * δ) ≤ ENNReal.ofReal (C * mesh k ^ aᵢ) := by
      have hcast : (idx.card : ℝ≥0∞) = ENNReal.ofReal (idx.card : ℝ) := by norm_num
      rw [hcast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have hrealCard : (idx.card : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast hidxCard
      have hnn : 0 ≤ C₀ * mesh k ^ aᵢ :=
        mul_nonneg hC₀ (Real.rpow_nonneg (EpsB.mesh_pos k).le _)
      calc
        (idx.card : ℝ) * (C₀ * mesh k ^ aᵢ) ≤ ((N + 1 : ℕ) : ℝ) * (C₀ * mesh k ^ aᵢ) :=
          mul_le_mul_of_nonneg_right hrealCard hnn
        _ = Cᵢ * mesh k ^ aᵢ := by dsimp [Cᵢ]; ring
        _ ≤ C * mesh k ^ aᵢ :=
          mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (EpsB.mesh_pos k).le _)
    have hsubset : (PolarItineraryGood F k z r s₀)ᶜ ≤ᵐ[F.P] (⋂ i ∈ idx, Ev i)ᶜ := by
      filter_upwards [hConnected k, hLoopless k] with ω hconn hloop
      intro hnot hgood
      apply hnot
      have hωall : ∀ i ∈ idx, ω ∈ Ev i := by simpa using hgood
      exact hWproducer ω hconn hloop (hωall none (by simp [idx]))
        (fun w hw => hωall (some w) (by simp [idx, hw]))
    calc
      F.P (PolarItineraryGood F k z r s₀)ᶜ ≤ F.P (⋂ i ∈ idx, Ev i)ᶜ := measure_mono_ae hsubset
      _ ≤ (idx.card : ℝ≥0∞) * δ := hQbad
      _ ≤ ENNReal.ofReal (C * mesh k ^ aᵢ) := hmult
  · have hk' : k ≤ K := Nat.le_of_not_ge hk
    have hpow : mesh K ^ aᵢ ≤ mesh k ^ aᵢ :=
      Real.rpow_le_rpow (EpsB.mesh_pos K).le (EpsB.mesh_antitone hk') haᵢ.le
    have hCinv : (mesh K ^ aᵢ)⁻¹ ≤ C := by
      dsimp [C]
      linarith
    have hone : (1 : ℝ) ≤ C * mesh k ^ aᵢ := by
      calc
        (1 : ℝ) = (mesh K ^ aᵢ)⁻¹ * mesh K ^ aᵢ := (inv_mul_cancel₀ hKpos.ne').symm
        _ ≤ C * mesh K ^ aᵢ := mul_le_mul_of_nonneg_right hCinv hKpos.le
        _ ≤ C * mesh k ^ aᵢ := mul_le_mul_of_nonneg_left hpow
            (le_trans (inv_nonneg.mpr hKpos.le) hCinv)
    calc
      F.P (PolarItineraryGood F k z r s₀)ᶜ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (C * mesh k ^ aᵢ) := ENNReal.ofReal_le_ofReal hone

/-- **The grid annulus-disconnection estimate with its rate `min a27 ai / 4` exposed** (body of
`CellFamily.cellFamily_compl_of_interfaces_bad`). -/
theorem sgcRate_of_itinRate (F : RandomCellFamily) (γ ρ q : ℝ)
    (_hγ : γ ∈ Set.Ioo 0 2) (_hρ : ρ ∈ Set.Ioo 0 1)
    (hq : 0 < q ∧ q < 2 / (2 + γ) ^ 2) {a27 C27 ai : ℝ} (ha27 : 0 < a27)
    (h27 : ∀ k, F.P (DiameterGood F k q ρ)ᶜ ≤ ENNReal.ofReal (C27 * mesh k ^ a27)) (hai : 0 < ai)
    (hItinerary : ItinRate F ρ ai)
    (hGridCount : FiniteGridCount ρ)
    (hConnected : GraphConnected F) (hSeparation : TemplateSeparation F) :
    ∃ χ β p C : ℝ, 0 < χ ∧ 0 < β ∧ β < min χ q ∧ 0 < p ∧
      ∀ k, F.P {ω | (F.H k ω).ScaledGridControl 1 (mesh k) χ β q ρ p}ᶜ ≤
        ENNReal.ofReal (C * mesh k ^ (min a27 ai / 4)) := by
  classical
  have h27bad := h27
  rcases hItinerary with ⟨s₀, bi, Ci, hs₀, hs₀le, hbi, hIbad⟩
  let a₀ : ℝ := min a27 ai
  let χ : ℝ := a₀ / 6
  let β : ℝ := min χ (min q bi) / 2
  let α : ℝ := a₀ / 4
  let p : ℝ := (2 : ℝ) ^ (-(⌈11600 / s₀⌉ : ℤ))
  have ha₀ : 0 < a₀ := by
    dsimp [a₀]
    exact lt_min ha27 hai
  have hχ : 0 < χ := by dsimp [χ]; positivity
  have hmin : 0 < min χ (min q bi) := lt_min hχ (lt_min hq.1 hbi)
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβχ : β < χ := by
    dsimp [β]
    have hle : min χ (min q bi) ≤ χ := min_le_left _ _
    linarith
  have hβq : β < q := by
    dsimp [β]
    have hle₁ : min χ (min q bi) ≤ min q bi := min_le_right _ _
    have hle₂ : min q bi ≤ q := min_le_left _ _
    linarith
  have hβi : β < bi := by
    dsimp [β]
    have hle₁ : min χ (min q bi) ≤ min q bi := min_le_right _ _
    have hle₂ : min q bi ≤ bi := min_le_right _ _
    linarith
  have hα : 0 < α := by dsimp [α]; positivity
  have hp : 0 < p := by dsimp [p]; positivity
  obtain ⟨Cgrid, hCgrid, hGridCard⟩ := hGridCount χ β hχ hβ hβχ
  obtain ⟨S, hS, hScard⟩ := hGridCard
  let C₀ : ℝ := max 0 (max C27 Ci)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC27 : C27 ≤ C₀ := by
    dsimp [C₀]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hCi : Ci ≤ C₀ := by
    dsimp [C₀]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hpowD : ∀ k, mesh k ^ a27 ≤ mesh k ^ a₀ := by
    intro k
    apply Real.rpow_le_rpow_of_exponent_ge (EpsB.mesh_pos k) (EpsB.mesh_le_one k)
    dsimp [a₀]
    exact min_le_left _ _
  have hpowI : ∀ k, mesh k ^ ai ≤ mesh k ^ a₀ := by
    intro k
    apply Real.rpow_le_rpow_of_exponent_ge (EpsB.mesh_pos k) (EpsB.mesh_le_one k)
    dsimp [a₀]
    exact min_le_right _ _
  have hDbad (k : ℕ) : F.P (DiameterGood F k q ρ)ᶜ ≤
      ENNReal.ofReal (C₀ * mesh k ^ a₀) := by
    have hbase : C27 * mesh k ^ a27 ≤ C₀ * mesh k ^ a₀ := by
      calc
        C27 * mesh k ^ a27 ≤ C₀ * mesh k ^ a27 :=
          mul_le_mul_of_nonneg_right hC27 (Real.rpow_nonneg (le_of_lt (EpsB.mesh_pos k)) _)
        _ ≤ C₀ * mesh k ^ a₀ := mul_le_mul_of_nonneg_left (hpowD k) hC₀
    have hb := ENNReal.ofReal_le_ofReal hbase
    have hbad := h27bad k
    simpa [DiameterGood] using hbad.trans hb
  have hIbad' (k : ℕ) (z : ℂ) (r : ℝ)
      (hr : mesh k ^ bi ≤ r) (hrρ : r ≤ ρ) (hball : ball z (2 * r) ⊆ ball (0 : ℂ) ρ) :
      F.P (PolarItineraryGood F k z r s₀)ᶜ ≤
        ENNReal.ofReal (C₀ * mesh k ^ a₀) := by
    have hbase : Ci * mesh k ^ ai ≤ C₀ * mesh k ^ a₀ := by
      calc
        Ci * mesh k ^ ai ≤ C₀ * mesh k ^ ai :=
          mul_le_mul_of_nonneg_right hCi (Real.rpow_nonneg (le_of_lt (EpsB.mesh_pos k)) _)
        _ ≤ C₀ * mesh k ^ a₀ := mul_le_mul_of_nonneg_left (hpowI k) hC₀
    have hb := ENNReal.ofReal_le_ofReal hbase
    exact (hIbad k z r hr hrρ hball).trans hb
  let δ (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal (C₀ * mesh k ^ a₀)
  let idx (k : ℕ) : Finset (Option (ℤ × ℤ × ℤ)) := insert none ((S k).image some)
  let Ev (k : ℕ) (i : Option (ℤ × ℤ × ℤ)) : Set F.Ω :=
    match i with
    | none => DiameterGood F k q ρ
    | some t => PolarItineraryGood F k (gridCenter (mesh k) χ t) (gridRadius (mesh k) χ t) s₀
  let Q (k : ℕ) : Set F.Ω := ⋂ i ∈ idx k, Ev k i
  have hδeach (k : ℕ) (i : Option (ℤ × ℤ × ℤ)) (hi : i ∈ idx k) :
      F.P (Ev k i)ᶜ ≤ δ k := by
    rcases Finset.mem_insert.mp hi with hnone | hi
    · subst i
      simpa [Ev, DiameterGood, δ] using hDbad k
    · rcases Finset.mem_image.mp hi with ⟨t, ht, rfl⟩
      obtain ⟨m, n, ℓ⟩ := t
      have hspec := hS k m n ℓ
      have hconstraints := hspec.1 ht
      have hrad : mesh k ^ bi ≤ gridRadius (mesh k) χ (m, n, ℓ) := by
        calc
          mesh k ^ bi ≤ mesh k ^ β :=
            Real.rpow_le_rpow_of_exponent_ge (EpsB.mesh_pos k) (EpsB.mesh_le_one k) (le_of_lt hβi)
          _ ≤ gridRadius (mesh k) χ (m, n, ℓ) := by simpa [gridRadius] using hconstraints.2.1
      have hbad := hIbad' k (gridCenter (mesh k) χ (m, n, ℓ))
        (gridRadius (mesh k) χ (m, n, ℓ)) hrad hconstraints.2.2.1 hconstraints.2.2.2
      simpa [Ev, δ] using hbad
  have hidxcard (k : ℕ) : (idx k).card = (S k).card + 1 := by
    have himage : ((S k).image some).card = (S k).card :=
      Finset.card_image_iff.mpr (by
        intro a ha b hb hab
        exact Option.some.inj hab)
    have hnone : none ∉ (S k).image some := by simp
    change (insert none ((S k).image some)).card = (S k).card + 1
    rw [Finset.card_insert_of_notMem hnone, himage]
  let Cbig : ℝ := (Cgrid + 1) * C₀
  have hCbig : 0 ≤ Cbig := by dsimp [Cbig]; positivity
  have hpowNeg (k : ℕ) : 1 ≤ mesh k ^ (-3 * χ) := by
    rw [← Real.rpow_zero (mesh k)]
    exact Real.rpow_le_rpow_of_exponent_ge (EpsB.mesh_pos k) (EpsB.mesh_le_one k) (by linarith [hχ])
  have hrealidxbound (k : ℕ) : ((idx k).card : ℝ) ≤ (Cgrid + 1) * mesh k ^ (-3 * χ) := by
    have hcard : (S k).card ≤ Cgrid * mesh k ^ (-3 * χ) := hScard k
    have hcast : ((idx k).card : ℝ) = (S k).card + 1 := by rw [hidxcard]; norm_num
    rw [hcast]
    nlinarith [hpowNeg k, hCgrid]
  have halpha_small : α ≤ a₀ - 3 * χ := by dsimp [α, χ]; dsimp [a₀]; linarith
  have hprodreal (k : ℕ) : ((idx k).card : ℝ) * (C₀ * mesh k ^ a₀) ≤
      Cbig * mesh k ^ α := by
    have heps : 0 < mesh k := EpsB.mesh_pos k
    have hpows : mesh k ^ (-3 * χ) * mesh k ^ a₀ = mesh k ^ (a₀ - 3 * χ) := by
      rw [← Real.rpow_add heps (-3 * χ) a₀]
      congr 1
      dsimp [χ, a₀]
      ring
    calc
      _ ≤ ((Cgrid + 1) * mesh k ^ (-3 * χ)) * (C₀ * mesh k ^ a₀) :=
        mul_le_mul_of_nonneg_right (hrealidxbound k) (mul_nonneg hC₀ (Real.rpow_nonneg heps.le _))
      _ = Cbig * mesh k ^ (a₀ - 3 * χ) := by
        rw [show ((Cgrid + 1) * mesh k ^ (-3 * χ)) * (C₀ * mesh k ^ a₀) =
          ((Cgrid + 1) * C₀) * (mesh k ^ (-3 * χ) * mesh k ^ a₀) by ring, hpows]
      _ ≤ Cbig * mesh k ^ α := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge heps (EpsB.mesh_le_one k) halpha_small) hCbig
  have hδprod (k : ℕ) : ((idx k).card : ℝ≥0∞) * δ k ≤
      ENNReal.ofReal (Cbig * mesh k ^ α) := by
    have hcast : ((idx k).card : ℝ≥0∞) = ENNReal.ofReal ((idx k).card : ℝ) := by norm_num
    rw [hcast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hprodreal k)
  have hQbad (k : ℕ) : F.P (Q k)ᶜ ≤ ENNReal.ofReal (Cbig * mesh k ^ α) := by
    have h := measure_finset_iInter_compl_le_card_mul F.P (idx k) (Ev k) (hδeach k)
    calc
      F.P (Q k)ᶜ ≤ ((idx k).card : ℝ≥0∞) * δ k := by simpa [Q] using h
      _ ≤ ENNReal.ofReal (Cbig * mesh k ^ α) := hδprod k
  have hsmallEvent := epsB_eventually_rpow_lt (q - β) (by linarith [hβq]) (by norm_num : (0:ℝ) < 1 / 1000)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hsmallEvent
  let C : ℝ := Cbig + (mesh K ^ α)⁻¹ + 1
  have hC : Cbig ≤ C := by dsimp [C]; linarith [hCbig, inv_nonneg.mpr (Real.rpow_nonneg (le_of_lt (EpsB.mesh_pos K)) α)]
  refine ⟨χ, β, p, C, hχ, hβ, ?_, hp, ?_⟩
  · exact lt_min hβχ hβq
  · intro k
    by_cases hk : K ≤ k
    · have hsmallPow : mesh k ^ (q - β) < 1 / 1000 := hK k hk
      let Env : Set F.Ω := {ω | (F.G k ω).adj.Connected ∧
        ∀ z r, 0 < r →
          (∀ x, ((F.H k ω).cell x ∩ closedBall z (2 * r)).Nonempty →
            diam ((F.H k ω).cell x) ≤ r / 1000) → (F.H k ω).TemplateSeparation z r}
      have haeEnv : ∀ᵐ ω ∂F.P, ω ∈ Env := by
        filter_upwards [hConnected k, hSeparation k] with ω hconn hTS
        exact ⟨hconn, hTS⟩
      have hEnvNull : F.P Envᶜ = 0 := ae_iff.mp haeEnv
      have hsubset : Q k ∩ Env ⊆ {ω | (F.H k ω).ScaledGridControl 1 (mesh k) χ β q ρ p} := by
        intro ω hω
        obtain ⟨hQ, hEnv⟩ := hω
        obtain ⟨hconn, hTS⟩ := hEnv
        have hQ' : ∀ i, i ∈ idx k → ω ∈ Ev k i := by simpa [Q] using hQ
        have hdiam : ω ∈ DiameterGood F k q ρ := by
          have := hQ' none (by simp [idx])
          simpa [Ev] using this
        have hgridgood : ω ∈ GridEnvironmentGood F k q χ ρ s₀ S := by
          change ω ∈ DiameterGood F k q ρ ∧
            ∀ t ∈ S k, ω ∈ PolarItineraryGood F k
              (gridCenter (mesh k) χ t) (gridRadius (mesh k) χ t) s₀
          refine ⟨hdiam, ?_⟩
          intro t ht
          have hsome : some t ∈ idx k := by simp [idx, ht]
          have := hQ' (some t) hsome
          simpa [Ev] using this
        exact scaledGridControl_of_good_environment F k q χ β ρ s₀ S hS
          hsmallPow ω hconn hTS hgridgood
      let Target : Set F.Ω := {ω | (F.H k ω).ScaledGridControl 1 (mesh k) χ β q ρ p}
      have hTargetBad : F.P Targetᶜ ≤ ENNReal.ofReal (Cbig * mesh k ^ α) := by
        have hbadSubset : Targetᶜ ⊆ (Q k ∩ Env)ᶜ := by
          intro ω hω hgood
          exact hω (hsubset hgood)
        have hcompl : (Q k ∩ Env)ᶜ = (Q k)ᶜ ∪ Envᶜ := by
          ext ω
          change ¬ (ω ∈ Q k ∧ ω ∈ Env) ↔ (ω ∉ Q k ∨ ω ∉ Env)
          tauto
        calc
          F.P Targetᶜ ≤ F.P (Q k ∩ Env)ᶜ := measure_mono hbadSubset
          _ = F.P ((Q k)ᶜ ∪ Envᶜ) := by rw [hcompl]
          _ ≤ F.P (Q k)ᶜ + F.P Envᶜ := measure_union_le _ _
          _ = F.P (Q k)ᶜ := by rw [hEnvNull]; simp
          _ ≤ ENNReal.ofReal (Cbig * mesh k ^ α) := hQbad k
      have hCbound : ENNReal.ofReal (Cbig * mesh k ^ α) ≤
          ENNReal.ofReal (C * mesh k ^ α) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (le_of_lt (EpsB.mesh_pos k)) α)
      exact hTargetBad.trans hCbound
    · have hk' : k ≤ K := Nat.le_of_not_ge hk
      have hmesh : mesh K ≤ mesh k := EpsB.mesh_antitone hk'
      have hpow : mesh K ^ α ≤ mesh k ^ α :=
        Real.rpow_le_rpow (le_of_lt (EpsB.mesh_pos K)) hmesh (le_of_lt hα)
      have hsmall : 1 ≤ C * mesh k ^ α := by
        have hNpos : 0 < mesh K ^ α := Real.rpow_pos_of_pos (EpsB.mesh_pos K) α
        have hbase : 1 ≤ (mesh K ^ α)⁻¹ * mesh K ^ α := by rw [inv_mul_cancel₀ hNpos.ne']
        have hmon := mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hNpos.le)
        have hCinv : (mesh K ^ α)⁻¹ ≤ C := by dsimp [C]; linarith [hCbig]
        have hmon' := mul_le_mul_of_nonneg_right hCinv (Real.rpow_nonneg (le_of_lt (EpsB.mesh_pos k)) α)
        nlinarith [hbase, hmon, hmon']
      calc
        F.P {ω | (F.H k ω).ScaledGridControl 1 (mesh k) χ β q ρ p}ᶜ ≤ 1 := prob_le_one
        _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ ENNReal.ofReal (C * mesh k ^ α) := ENNReal.ofReal_le_ofReal hsmall

/-- **[18] Lemma 3.11 from the annulus-disconnection estimate with the rate unchanged** (body of T15A's `T15A.lemma311Bad_of_cellFamily`). -/
theorem lemma311Rate_of_sgc (F : CellFamily.RandomCellFamily) (hconn : CellFamily.GraphConnected F)
    {χ β α p C q ρ₂ ρ : ℝ} (hβ : 0 < β) (hβχ : β < χ) (hβq : β < q) (hα : 0 < α) (_hp : 0 < p)
    (hρ : ρ < ρ₂)
    (h26 : ∀ k, F.P {ω | (F.H k ω).ScaledGridControl 1 (CellFamily.mesh k) χ β q ρ₂ p}ᶜ ≤
      ENNReal.ofReal (C * CellFamily.mesh k ^ α)) :
    ∃ C' : ℝ, ∀ k, F.P (T15A.Lemma311Good F k ρ β p)ᶜ ≤ ENNReal.ofReal (C' * CellFamily.mesh k ^ α) := by
  have hgap : 0 < ρ₂ - ρ := by linarith
  have hev : ∀ᶠ k : ℕ in atTop,
      CellFamily.mesh k ^ (q - β) < 1 / 18 ∧ CellFamily.mesh k ^ (χ - β) < 1 / 18 ∧
        CellFamily.mesh k ^ q < (ρ₂ - ρ) / 7 ∧ CellFamily.mesh k ^ χ < (ρ₂ - ρ) / 7 :=
    (Lemma38Source.eventually_meshPow_lt (by linarith) (by norm_num)).and
      ((Lemma38Source.eventually_meshPow_lt (by linarith) (by norm_num)).and
        ((Lemma38Source.eventually_meshPow_lt (by linarith) (by linarith)).and
          (Lemma38Source.eventually_meshPow_lt (by linarith) (by linarith))))
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  refine ⟨max C 0 + (CellFamily.mesh K ^ α)⁻¹, fun k => ?_⟩
  have hm0 := EpsB.mesh_pos k
  have hpowα : 0 ≤ CellFamily.mesh k ^ α := Real.rpow_nonneg hm0.le _
  rcases lt_or_ge k K with hkK | hkK
  · -- coarse meshes: the bound is `≥ 1`
    have hKk : CellFamily.mesh K ^ α ≤ CellFamily.mesh k ^ α :=
      Real.rpow_le_rpow (EpsB.mesh_pos K).le (EpsB.mesh_antitone hkK.le) hα.le
    have hKpos : 0 < CellFamily.mesh K ^ α := Real.rpow_pos_of_pos (EpsB.mesh_pos K) _
    have hone : 1 ≤ (max C 0 + (CellFamily.mesh K ^ α)⁻¹) * CellFamily.mesh k ^ α := by
      have h1 : 1 ≤ (CellFamily.mesh K ^ α)⁻¹ * CellFamily.mesh k ^ α := by
        rw [inv_mul_eq_div, le_div_iff₀ hKpos, one_mul]
        exact hKk
      have h2 : 0 ≤ max C 0 * CellFamily.mesh k ^ α := mul_nonneg (le_max_right _ _) hpowα
      nlinarith
    calc F.P (T15A.Lemma311Good F k ρ β p)ᶜ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hone
  · -- fine meshes: (3.35) holds on the grid annulus-disconnection event of a connected graph
    obtain ⟨h1, h2, h3, h4⟩ := hK k hkK
    have hs : 0 < CellFamily.mesh k ^ χ := Real.rpow_pos_of_pos hm0 _
    have hd : 0 ≤ CellFamily.mesh k ^ q := Real.rpow_nonneg hm0.le _
    have hβpow : 0 < CellFamily.mesh k ^ β := Real.rpow_pos_of_pos hm0 _
    have hsmall : 5 * CellFamily.mesh k ^ q + 13 * CellFamily.mesh k ^ χ ≤ CellFamily.mesh k ^ β := by
      have hq' : CellFamily.mesh k ^ q = CellFamily.mesh k ^ β * CellFamily.mesh k ^ (q - β) := by
        rw [← Real.rpow_add hm0]
        ring_nf
      have hχ' : CellFamily.mesh k ^ χ = CellFamily.mesh k ^ β * CellFamily.mesh k ^ (χ - β) := by
        rw [← Real.rpow_add hm0]
        ring_nf
      rw [hq', hχ']
      nlinarith
    have hroom : 2 * CellFamily.mesh k ^ q + 5 * CellFamily.mesh k ^ χ < ρ₂ - ρ := by linarith
    have hsub : (T15A.Lemma311Good F k ρ β p)ᶜ ⊆
        {ω | (F.H k ω).ScaledGridControl 1 (CellFamily.mesh k) χ β q ρ₂ p}ᶜ ∪
          {ω | ¬ (F.G k ω).adj.Connected} := by
      intro ω hω
      by_contra hnot
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_not] at hnot
      exact hω (T15A.lemma311Holds_of_scaledGridControl (F.H k ω) hnot.2 hnot.1 hs hd hsmall hroom)
    have hnull : F.P {ω | ¬ (F.G k ω).adj.Connected} = 0 := ae_iff.mp (hconn k)
    calc F.P (T15A.Lemma311Good F k ρ β p)ᶜ
        ≤ F.P ({ω | (F.H k ω).ScaledGridControl 1 (CellFamily.mesh k) χ β q ρ₂ p}ᶜ ∪
            {ω | ¬ (F.G k ω).adj.Connected}) := measure_mono hsub
      _ ≤ F.P {ω | (F.H k ω).ScaledGridControl 1 (CellFamily.mesh k) χ β q ρ₂ p}ᶜ +
            F.P {ω | ¬ (F.G k ω).adj.Connected} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (C * CellFamily.mesh k ^ α) := by rw [hnull, add_zero]; exact h26 k
      _ ≤ ENNReal.ofReal ((max C 0 + (CellFamily.mesh K ^ α)⁻¹) * CellFamily.mesh k ^ α) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_right _ hpowα
          have := inv_nonneg.mpr (Real.rpow_nonneg (EpsB.mesh_pos K).le α)
          linarith [le_max_left C 0]

end MatedCRTHarmonic.GMSMain.EpsB
