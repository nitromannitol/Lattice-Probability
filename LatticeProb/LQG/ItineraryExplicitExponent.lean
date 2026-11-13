/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsBRateCellFamily at commit fdb5cad. The proof is copied; in the
   statement the exponent `βᵢ` of the itinerary estimate is a parameter instead of an existential witness. -/
import LatticeProb.LQG.Lemma38ExplicitScale
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBRateCellFamily

/-!
# The itinerary estimate of Lemma 3.11 with an explicit exponent

`EpsBRateCellFamily.itinRate_of_l38Rate` produces the itinerary estimate with an existential exponent `βᵢ`.
In its proof, `βᵢ` is only used to compare the lower scale endpoint `mesh k ^ βᵢ` with the scale `mesh k ^ β₈`
of Lemma 3.8 and with `mesh k ^ q`; the waypoint producer does not depend on it. Here `βᵢ` is a parameter with
`0 < βᵢ < min β₈ q`, so that a caller can fix it before the ambient radius `ρ`.

* `ItinRateAt F ρ a βᵢ` — the itinerary estimate with rate exponent `a` and lower scale `mesh k ^ βᵢ`;
* `itinRateAt_of_l38RateAt` — from the diameter estimate and the Lemma 3.8 estimate at the scale `β₈`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LatticeProb.LQG.ExplicitScale

open MatedCRTHarmonic MatedCRTHarmonic.GMSMain MatedCRTHarmonic.GMSMain.EpsB
open MatedCRTHarmonic.CellFamily (mesh RandomCellFamily DiameterGood PolarItineraryGood
  Lemma38EnvironmentGood GraphConnected GraphLoopless WaypointStrongMarkovInputFixed2
  measure_finset_iInter_compl_le_card_mul)

/-- `CellFamily.ItineraryEstimateBad F ρ` with the rate exponent `a` and the lower scale `mesh k ^ βᵢ` fixed. -/
def ItinRateAt (F : RandomCellFamily) (ρ a βᵢ : ℝ) : Prop :=
  ∃ s₀ Cᵢ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 10 ∧
    ∀ k (z : ℂ) (r : ℝ), mesh k ^ βᵢ ≤ r → r ≤ ρ → ball z (2 * r) ⊆ ball (0 : ℂ) ρ →
      F.P (PolarItineraryGood F k z r s₀)ᶜ ≤ ENNReal.ofReal (Cᵢ * mesh k ^ a)

/-- **The itinerary estimate with its rate `min a27 a8` exposed and the exponent `βᵢ` given** (body of
`CellFamily.itineraryEstimateBad_of_lemma38Bad_fixed2`). The waypoint producer constrains the scale `s₀` only;
its exponent witness does not enter the conclusion, so any `0 < βᵢ < min β₈ q` may be used. -/
theorem itinRateAt_of_l38RateAt (F : RandomCellFamily) (q ρ : ℝ) {a27 C27 a8 b8 βᵢ : ℝ}
    (ha27 : 0 < a27)
    (h27 : ∀ k, F.P (DiameterGood F k q ρ)ᶜ ≤ ENNReal.ofReal (C27 * mesh k ^ a27)) (ha8 : 0 < a8)
    (h38 : L38RateAt F ρ a8 b8) (hβᵢ : 0 < βᵢ) (hβᵢ8 : βᵢ < b8) (hβᵢq : βᵢ < q)
    (hConnected : GraphConnected F) (hLoopless : GraphLoopless F)
    (hway : WaypointStrongMarkovInputFixed2 F q ρ) : ItinRateAt F ρ (min a27 a8) βᵢ := by
  classical
  have h27bad := h27
  have hb8 : 0 < b8 := hβᵢ.trans hβᵢ8
  have hq : 0 < q := hβᵢ.trans hβᵢq
  rcases h38 with ⟨A8, C8, h38bad⟩
  rcases hway hConnected hLoopless b8 A8 hb8 hq with
    ⟨s₀, -, hs₀, hs₀le, -, -, -, _hA, hproducer⟩
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
  refine ⟨s₀, C, hs₀, hs₀le, ?_⟩
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

end LatticeProb.LQG.ExplicitScale
