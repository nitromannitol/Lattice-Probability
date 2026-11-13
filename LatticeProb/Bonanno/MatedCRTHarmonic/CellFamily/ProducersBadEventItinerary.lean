/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.ProducersBadEventItinerary at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Core
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.BadEventInterfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.WaypointStrongMarkovFixed

/-!
# Conditional itinerary estimate from [18] Lemmas 2.7 and 3.8

This file applies the uniform Lemma 3.8 environment bound at the finitely many waypoints, intersects those events with
the Lemma 2.7 diameter event, and proves the polynomial environment estimate by a finite union bound. The
pathwise/strong-Markov waypoint conclusion remains an explicit intermediate input.

: the corrected producer is `itineraryEstimateBad_of_lemma38Bad_fixed2`, conditional on
the corrected waypoint input `WaypointStrongMarkovInputFixed2` (environment net of `⌈4·10⁵/s₀²⌉` points, positive
`β₈, q`), almost-sure connectivity and looplessness; its union bound is an outer-measure bound, so it needs no event
measurability.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellFamily

private theorem itinerary_mesh_eq_inv_pow (k : ℕ) : mesh k = ((2 : ℝ) ^ k)⁻¹ := by
  simp [mesh, zpow_neg, zpow_natCast]

private theorem itinerary_mesh_pos (k : ℕ) : 0 < mesh k := by
  rw [itinerary_mesh_eq_inv_pow]
  positivity

private theorem itinerary_mesh_le_one (k : ℕ) : mesh k ≤ 1 := by
  rw [itinerary_mesh_eq_inv_pow]
  apply (inv_le_one₀ (by positivity)).2
  exact one_le_pow₀ (by norm_num : 1 ≤ (2 : ℝ))

private theorem itinerary_mesh_antitone : Antitone mesh := by
  intro a b hab
  rw [itinerary_mesh_eq_inv_pow, itinerary_mesh_eq_inv_pow]
  apply inv_anti₀ (by positivity)
  gcongr
  norm_num

private theorem itinerary_mesh_rpow_tendsto_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun k : ℕ => mesh k ^ a) atTop (𝓝 0) := by
  have hp : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hi : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hp
  have hm : Tendsto mesh atTop (𝓝 0) := by
    convert hi using 1
    ext k
    exact itinerary_mesh_eq_inv_pow k
  have hc : ContinuousAt (fun x : ℝ => x ^ a) 0 :=
    Real.continuousAt_rpow_const 0 a (Or.inr ha.le)
  simpa [Function.comp_def, Real.zero_rpow ha.ne'] using hc.tendsto.comp hm

private theorem itinerary_eventually_rpow_lt (a : ℝ) (ha : 0 < a) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, mesh k ^ a < c :=
  (itinerary_mesh_rpow_tendsto_zero a ha).eventually (Iio_mem_nhds hc)

/-- **Corrected itinerary producer** : the
bad-event itinerary estimate from the bad-event [18] Lemmas 2.7 and 3.8, almost-sure connectivity and looplessness of
the mesh graphs, `0 < q`, and the corrected waypoint input `WaypointStrongMarkovInputFixed2`. For large `k` the
waypoint input applies at the Lemma 3.8 exponent `β₈`; on the connectivity/looplessness event the itinerary event
contains the intersection of the diameter event and the `⌈4·10⁵/s₀²⌉` Lemma 3.8 environment events at the net points,
and the union bound for that intersection is an outer-measure bound. Small `k` are absorbed into the constant. No
event measurability is used. -/
theorem itineraryEstimateBad_of_lemma38Bad_fixed2
    (F : RandomCellFamily) (q ρ : ℝ)
    (h27 : Lemma27CellDiamBad F q ρ) (h38 : Lemma38AnnulusHitBad F ρ)
    (hConnected : GraphConnected F) (hLoopless : GraphLoopless F)
    (hq : 0 < q) (hway : WaypointStrongMarkovInputFixed2 F q ρ) : ItineraryEstimateBad F ρ := by
  classical
  rcases h27 with ⟨a27, ha27, C27, h27bad⟩
  rcases h38 with ⟨a8, ha8, b8, hb8, A8, C8, h38bad⟩
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
    Real.rpow_le_rpow_of_exponent_ge (itinerary_mesh_pos k) (itinerary_mesh_le_one k)
      (min_le_left _ _)
  have hpow8 (k : ℕ) : mesh k ^ a8 ≤ mesh k ^ aᵢ :=
    Real.rpow_le_rpow_of_exponent_ge (itinerary_mesh_pos k) (itinerary_mesh_le_one k)
      (min_le_right _ _)
  have hlarge : ∀ᶠ k : ℕ in atTop,
      mesh k ^ (b8 - βᵢ) < 1 / 100 ∧ mesh k ^ b8 < s₀ ∧ mesh k ^ (q - βᵢ) < s₀ / 100 := by
    filter_upwards [itinerary_eventually_rpow_lt (b8 - βᵢ) (by linarith)
        (by norm_num : (0 : ℝ) < 1 / 100),
      itinerary_eventually_rpow_lt b8 hb8 hs₀,
      itinerary_eventually_rpow_lt (q - βᵢ) (by linarith) (by positivity : (0 : ℝ) < s₀ / 100)]
      with k h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hlarge
  let C : ℝ := Cᵢ + (mesh K ^ aᵢ)⁻¹ + 1
  have hKpos : 0 < mesh K ^ aᵢ := Real.rpow_pos_of_pos (itinerary_mesh_pos K) aᵢ
  have hC : Cᵢ ≤ C := by
    have : 0 ≤ (mesh K ^ aᵢ)⁻¹ := inv_nonneg.mpr hKpos.le
    dsimp [C]
    linarith
  refine ⟨s₀, aᵢ, βᵢ, C, hs₀, hs₀le, haᵢ, hβᵢ, ?_⟩
  intro k z r hr hρ hball
  by_cases hk : K ≤ k
  · obtain ⟨hk8, hks, hkq⟩ := hK k hk
    have hβpos : 0 < mesh k ^ βᵢ := Real.rpow_pos_of_pos (itinerary_mesh_pos k) βᵢ
    have hrWaypoint : mesh k ^ b8 ≤ r / 100 := by
      have hsplit : mesh k ^ b8 = mesh k ^ βᵢ * mesh k ^ (b8 - βᵢ) := by
        rw [← Real.rpow_add (itinerary_mesh_pos k) βᵢ (b8 - βᵢ)]
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
        rw [← Real.rpow_add (itinerary_mesh_pos k) βᵢ (q - βᵢ)]
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
            mul_le_mul_of_nonneg_right hC27 (Real.rpow_nonneg (itinerary_mesh_pos k).le _)
          _ ≤ C₀ * mesh k ^ aᵢ := mul_le_mul_of_nonneg_left (hpow27 k) hC₀
      · have hw : w ∈ W := by
          have : some w ∈ W.image some := (Finset.mem_insert.mp hi).resolve_left (by simp)
          rcases Finset.mem_image.mp this with ⟨a, ha, haw⟩
          simpa [Option.some.inj haw] using ha
        refine (h38bad k w (r / 100) hrWaypoint hr100 (hWball w hw)).trans
          (ENNReal.ofReal_le_ofReal ?_)
        calc
          C8 * mesh k ^ a8 ≤ C₀ * mesh k ^ a8 :=
            mul_le_mul_of_nonneg_right hC8 (Real.rpow_nonneg (itinerary_mesh_pos k).le _)
          _ ≤ C₀ * mesh k ^ aᵢ := mul_le_mul_of_nonneg_left (hpow8 k) hC₀
    have hQbad := measure_finset_iInter_compl_le_card_mul F.P idx Ev hbad
    have hmult : ((idx.card : ℝ≥0∞) * δ) ≤ ENNReal.ofReal (C * mesh k ^ aᵢ) := by
      have hcast : (idx.card : ℝ≥0∞) = ENNReal.ofReal (idx.card : ℝ) := by norm_num
      rw [hcast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have hrealCard : (idx.card : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast hidxCard
      have hnn : 0 ≤ C₀ * mesh k ^ aᵢ :=
        mul_nonneg hC₀ (Real.rpow_nonneg (itinerary_mesh_pos k).le _)
      calc
        (idx.card : ℝ) * (C₀ * mesh k ^ aᵢ) ≤ ((N + 1 : ℕ) : ℝ) * (C₀ * mesh k ^ aᵢ) :=
          mul_le_mul_of_nonneg_right hrealCard hnn
        _ = Cᵢ * mesh k ^ aᵢ := by dsimp [Cᵢ]; ring
        _ ≤ C * mesh k ^ aᵢ :=
          mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (itinerary_mesh_pos k).le _)
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
      Real.rpow_le_rpow (itinerary_mesh_pos K).le (itinerary_mesh_antitone hk') haᵢ.le
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

end MatedCRTHarmonic.CellFamily
