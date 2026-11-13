/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.BadEventProposition at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Proposition
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.BadEventInterfaces

/-! The corrected scaled-grid estimate proof with outer-measure bad-event hypotheses. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellFamily

open MatedCRTHarmonic

private theorem bad_mesh_pos (k : ℕ) : 0 < mesh k := by
  rw [show mesh k = ((2 : ℝ) ^ k)⁻¹ by simp [mesh, zpow_neg, zpow_natCast]]
  positivity

private theorem bad_mesh_le_one (k : ℕ) : mesh k ≤ 1 := by
  rw [show mesh k = ((2 : ℝ) ^ k)⁻¹ by simp [mesh, zpow_neg, zpow_natCast]]
  apply (inv_le_one₀ (by positivity)).2
  exact one_le_pow₀ (by norm_num : 1 ≤ (2 : ℝ))

private theorem bad_mesh_antitone : Antitone mesh := by
  intro a b hab
  rw [show mesh a = ((2 : ℝ) ^ a)⁻¹ by simp [mesh, zpow_neg, zpow_natCast],
    show mesh b = ((2 : ℝ) ^ b)⁻¹ by simp [mesh, zpow_neg, zpow_natCast]]
  apply inv_anti₀ (by positivity)
  gcongr
  norm_num

private theorem bad_mesh_rpow_tendsto_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun k : ℕ => mesh k ^ a) atTop (𝓝 0) := by
  have hp : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hi : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hp
  have hm : Tendsto mesh atTop (𝓝 0) := by
    convert hi using 1
    ext k
    simp [mesh, zpow_neg, zpow_natCast]
  have hc : ContinuousAt (fun x : ℝ => x ^ a) 0 :=
    Real.continuousAt_rpow_const 0 a (Or.inr ha.le)
  simpa [Function.comp_def, Real.zero_rpow ha.ne'] using hc.tendsto.comp hm

private theorem bad_eventually_mesh_rpow_lt (a : ℝ) (ha : 0 < a) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, mesh k ^ a < c :=
  (bad_mesh_rpow_tendsto_zero a ha).eventually (Iio_mem_nhds hc)

/-- **Corrected scaled-grid estimate, bad-event form** : from outer-measure bounds on the
bad diameter and itinerary events, plus the finite-grid, graph-connectivity, and template-separation interfaces, the
**failure** event of the exact frozen v2 `ScaledGridControl` statement (with explicit annular-event probability
`2^{−⌈11600/s₀⌉}`) has outer measure at most `C ε_k^α`. No measurability premise is needed for any event; in
particular downstream Borel–Cantelli arguments need no measurability of `{ScaledGridControl}` (the former
`hGridMeas`). The proof is the finite union bound `hTargetBad` for large `k` and `prob_le_one` for the finitely many
small `k`, where `1 ≤ C ε_k^α`. -/
theorem cellFamily_compl_of_interfaces_bad
    (F : RandomCellFamily) (γ ρ q : ℝ)
    (_hγ : γ ∈ Set.Ioo 0 2) (_hρ : ρ ∈ Set.Ioo 0 1)
    (hq : 0 < q ∧ q < 2 / (2 + γ) ^ 2)
    (h27 : Lemma27CellDiamBad F q ρ)
    (hItinerary : ItineraryEstimateBad F ρ)
    (hGridCount : FiniteGridCount ρ)
    (hConnected : GraphConnected F) (hSeparation : TemplateSeparation F) :
    ∃ χ β α p C : ℝ, 0 < χ ∧ 0 < β ∧ β < min χ q ∧ 0 < α ∧ 0 < p ∧
      ∀ k, F.P {ω | (F.H k ω).ScaledGridControl 1 (mesh k) χ β q ρ p}ᶜ ≤
        ENNReal.ofReal (C * mesh k ^ α) := by
  classical
  rcases h27 with ⟨a27, ha27, C27, h27bad⟩
  rcases hItinerary with ⟨s₀, ai, bi, Ci, hs₀, hs₀le, hai, hbi, hIbad⟩
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
    apply Real.rpow_le_rpow_of_exponent_ge (bad_mesh_pos k) (bad_mesh_le_one k)
    dsimp [a₀]
    exact min_le_left _ _
  have hpowI : ∀ k, mesh k ^ ai ≤ mesh k ^ a₀ := by
    intro k
    apply Real.rpow_le_rpow_of_exponent_ge (bad_mesh_pos k) (bad_mesh_le_one k)
    dsimp [a₀]
    exact min_le_right _ _
  have hDbad (k : ℕ) : F.P (DiameterGood F k q ρ)ᶜ ≤
      ENNReal.ofReal (C₀ * mesh k ^ a₀) := by
    have hbase : C27 * mesh k ^ a27 ≤ C₀ * mesh k ^ a₀ := by
      calc
        C27 * mesh k ^ a27 ≤ C₀ * mesh k ^ a27 :=
          mul_le_mul_of_nonneg_right hC27 (Real.rpow_nonneg (le_of_lt (bad_mesh_pos k)) _)
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
          mul_le_mul_of_nonneg_right hCi (Real.rpow_nonneg (le_of_lt (bad_mesh_pos k)) _)
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
            Real.rpow_le_rpow_of_exponent_ge (bad_mesh_pos k) (bad_mesh_le_one k) (le_of_lt hβi)
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
    exact Real.rpow_le_rpow_of_exponent_ge (bad_mesh_pos k) (bad_mesh_le_one k) (by linarith [hχ])
  have hrealidxbound (k : ℕ) : ((idx k).card : ℝ) ≤ (Cgrid + 1) * mesh k ^ (-3 * χ) := by
    have hcard : (S k).card ≤ Cgrid * mesh k ^ (-3 * χ) := hScard k
    have hcast : ((idx k).card : ℝ) = (S k).card + 1 := by rw [hidxcard]; norm_num
    rw [hcast]
    nlinarith [hpowNeg k, hCgrid]
  have halpha_small : α ≤ a₀ - 3 * χ := by dsimp [α, χ]; dsimp [a₀]; linarith
  have hprodreal (k : ℕ) : ((idx k).card : ℝ) * (C₀ * mesh k ^ a₀) ≤
      Cbig * mesh k ^ α := by
    have heps : 0 < mesh k := bad_mesh_pos k
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
        (Real.rpow_le_rpow_of_exponent_ge heps (bad_mesh_le_one k) halpha_small) hCbig
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
  have hsmallEvent := bad_eventually_mesh_rpow_lt (q - β) (by linarith [hβq]) (by norm_num : (0:ℝ) < 1 / 1000)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hsmallEvent
  let C : ℝ := Cbig + (mesh K ^ α)⁻¹ + 1
  have hC : Cbig ≤ C := by dsimp [C]; linarith [hCbig, inv_nonneg.mpr (Real.rpow_nonneg (le_of_lt (bad_mesh_pos K)) α)]
  refine ⟨χ, β, α, p, C, hχ, hβ, ?_, ?_, hp, ?_⟩
  · exact lt_min hβχ hβq
  · exact hα
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
        exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (le_of_lt (bad_mesh_pos k)) α)
      exact hTargetBad.trans hCbound
    · have hk' : k ≤ K := Nat.le_of_not_ge hk
      have hmesh : mesh K ≤ mesh k := bad_mesh_antitone hk'
      have hpow : mesh K ^ α ≤ mesh k ^ α :=
        Real.rpow_le_rpow (le_of_lt (bad_mesh_pos K)) hmesh (le_of_lt hα)
      have hsmall : 1 ≤ C * mesh k ^ α := by
        have hNpos : 0 < mesh K ^ α := Real.rpow_pos_of_pos (bad_mesh_pos K) α
        have hbase : 1 ≤ (mesh K ^ α)⁻¹ * mesh K ^ α := by rw [inv_mul_cancel₀ hNpos.ne']
        have hmon := mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hNpos.le)
        have hCinv : (mesh K ^ α)⁻¹ ≤ C := by dsimp [C]; linarith [hCbig]
        have hmon' := mul_le_mul_of_nonneg_right hCinv (Real.rpow_nonneg (le_of_lt (bad_mesh_pos k)) α)
        nlinarith [hbase, hmon, hmon']
      calc
        F.P {ω | (F.H k ω).ScaledGridControl 1 (mesh k) χ β q ρ p}ᶜ ≤ 1 := prob_le_one
        _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ ENNReal.ofReal (C * mesh k ^ α) := ENNReal.ofReal_le_ofReal hsmall

end MatedCRTHarmonic.CellFamily
