import Mathlib

/-!
# Vague limits of sequences of measures

Two deterministic facts used to construct a random measure as an almost sure vague limit.

* `exists_regular_tendsto_integral`, `exists_isLocallyFiniteMeasure_tendsto_integral`: on a locally compact
  Hausdorff space, if `m k` are measures finite on compacts and `∫ f d(m k)` converges for every continuous
  compactly supported `f`, then there is a regular (hence locally finite) measure `μ` with
  `∫ f d(m k) → ∫ f dμ` for all such `f`. The limit functional is positive and linear, and the measure is given
  by the Riesz-Markov-Kakutani representation theorem.
* `exists_countable_determining`: on a proper metric space there is a countable family `D` of continuous compactly
  supported functions such that convergence of `∫ g d(m k)` for all `g ∈ D` implies convergence of `∫ f d(m k)`
  for every continuous compactly supported `f`, for every sequence of measures finite on compacts. The family
  consists of a countable dense set of the continuous functions vanishing off each closed ball of integer radius
  (compact-open topology) and of one cutoff function per radius.

Together: a sequence of measures finite on compacts whose integrals converge on the countable family `D` has a
locally finite vague limit (`exists_isLocallyFiniteMeasure_tendsto_integral_of_countable`). This is how the
Liouville measure is obtained from almost sure convergence of countably many integrals (Duplantier and Sheffield,
*Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), proof of Proposition 1.1).
-/

open MeasureTheory Filter Topology Metric Set
open scoped CompactlySupported

namespace LatticeProb.VagueLimit

section RieszMarkovKakutani

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A sequence of measures finite on compacts whose integrals against every compactly supported continuous function
converge has a regular vague limit. -/
theorem exists_regular_tendsto_integral (m : ℕ → Measure X) (hm : ∀ k, IsFiniteMeasureOnCompacts (m k))
    (h : ∀ f : C_c(X, ℝ), ∃ ℓ : ℝ, Tendsto (fun k => ∫ x, f x ∂(m k)) atTop (𝓝 ℓ)) :
    ∃ μ : Measure X, μ.Regular ∧
      ∀ f : C_c(X, ℝ), Tendsto (fun k => ∫ x, f x ∂(m k)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  choose ℓ hℓ using h
  have hint : ∀ (k : ℕ) (f : C_c(X, ℝ)), Integrable (fun x => f x) (m k) := fun k f => by
    have := hm k
    exact f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hadd : ∀ f g : C_c(X, ℝ), ℓ (f + g) = ℓ f + ℓ g := by
    intro f g
    refine tendsto_nhds_unique (hℓ (f + g)) (((hℓ f).add (hℓ g)).congr fun k => ?_)
    rw [← integral_add (hint k f) (hint k g)]
    rfl
  have hsmul : ∀ (c : ℝ) (f : C_c(X, ℝ)), ℓ (c • f) = c • ℓ f := by
    intro c f
    refine tendsto_nhds_unique (hℓ (c • f)) (((hℓ f).const_smul c).congr fun k => ?_)
    rw [← integral_smul]
    rfl
  have hnonneg : ∀ f : C_c(X, ℝ), 0 ≤ f → 0 ≤ ℓ f := by
    intro f hf
    exact ge_of_tendsto' (hℓ f) fun k => integral_nonneg fun x => by simpa using hf x
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ ⟨⟨ℓ, hadd⟩, hsmul⟩ hnonneg
  refine ⟨RealRMK.rieszMeasure Λ, inferInstance, fun f => ?_⟩
  rw [RealRMK.integral_rieszMeasure Λ f]
  exact hℓ f

/-- A sequence of measures finite on compacts whose integrals against every compactly supported continuous function
converge has a locally finite vague limit. -/
theorem exists_isLocallyFiniteMeasure_tendsto_integral (m : ℕ → Measure X)
    (hm : ∀ k, IsFiniteMeasureOnCompacts (m k))
    (h : ∀ f : X → ℝ, Continuous f → HasCompactSupport f →
      ∃ ℓ : ℝ, Tendsto (fun k => ∫ x, f x ∂(m k)) atTop (𝓝 ℓ)) :
    ∃ μ : Measure X, IsLocallyFiniteMeasure μ ∧ ∀ f : X → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k => ∫ x, f x ∂(m k)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨μ, hμ, hlim⟩ := exists_regular_tendsto_integral m hm fun f =>
    h f f.continuous f.hasCompactSupport
  have := hμ
  exact ⟨μ, inferInstance, fun f hf hfc => hlim ⟨⟨f, hf⟩, hfc⟩⟩

end RieszMarkovKakutani

section Countable

variable {X : Type*} [MetricSpace X]

/-- A continuous cutoff equal to `1` on the closed ball of radius `n` and vanishing off the closed ball of radius
`n + 1`. -/
noncomputable def ballCutoff (x₀ : X) (n : ℕ) (x : X) : ℝ :=
  max 0 (min 1 ((n : ℝ) + 1 - dist x x₀))

theorem continuous_ballCutoff (x₀ : X) (n : ℕ) : Continuous (ballCutoff x₀ n) :=
  continuous_const.max (continuous_const.min (continuous_const.sub (continuous_id.dist continuous_const)))

theorem ballCutoff_nonneg (x₀ : X) (n : ℕ) (x : X) : 0 ≤ ballCutoff x₀ n x :=
  le_max_left _ _

theorem ballCutoff_eq_one {x₀ : X} {n : ℕ} {x : X} (h : dist x x₀ ≤ n) : ballCutoff x₀ n x = 1 := by
  unfold ballCutoff
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem ballCutoff_eq_zero {x₀ : X} {n : ℕ} {x : X} (h : (n : ℝ) + 1 < dist x x₀) : ballCutoff x₀ n x = 0 := by
  unfold ballCutoff
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]

variable [ProperSpace X]

theorem hasCompactSupport_ballCutoff (x₀ : X) (n : ℕ) : HasCompactSupport (ballCutoff x₀ n) :=
  HasCompactSupport.intro (isCompact_closedBall x₀ ((n : ℝ) + 1)) fun x hx =>
    ballCutoff_eq_zero (by simpa [mem_closedBall, not_le] using hx)

variable [MeasurableSpace X] [BorelSpace X]

/-- **A countable convergence-determining family.** On a proper metric space there is a countable family of
continuous compactly supported functions such that, for every sequence of measures finite on compacts, convergence of
the integrals of the members of the family implies convergence of the integrals of every continuous compactly
supported function. -/
theorem exists_countable_determining [Nonempty X] :
    ∃ D : Set (X → ℝ), D.Countable ∧ (∀ g ∈ D, Continuous g ∧ HasCompactSupport g) ∧
      ∀ m : ℕ → Measure X, (∀ k, IsFiniteMeasureOnCompacts (m k)) →
        (∀ g ∈ D, ∃ ℓ : ℝ, Tendsto (fun k => ∫ x, g x ∂(m k)) atTop (𝓝 ℓ)) →
        ∀ f : X → ℝ, Continuous f → HasCompactSupport f →
          ∃ ℓ : ℝ, Tendsto (fun k => ∫ x, f x ∂(m k)) atTop (𝓝 ℓ) := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  -- the continuous functions vanishing off the closed ball of radius `n`
  let S : ℕ → Set C(X, ℝ) := fun n => {F | ∀ x, x ∉ closedBall x₀ (n : ℝ) → F x = 0}
  have hE : ∀ n, ∃ E : Set (S n), E.Countable ∧ Dense E := fun n =>
    TopologicalSpace.exists_countable_dense (S n)
  choose E hEc hEd using hE
  let D : Set (X → ℝ) :=
    (⋃ n, (fun G : S n => ((G : C(X, ℝ)) : X → ℝ)) '' E n) ∪ Set.range (ballCutoff x₀)
  have hS_cc : ∀ n (G : S n),
      Continuous ((G : C(X, ℝ)) : X → ℝ) ∧ HasCompactSupport ((G : C(X, ℝ)) : X → ℝ) :=
    fun n G => ⟨(G : C(X, ℝ)).continuous, HasCompactSupport.intro (isCompact_closedBall x₀ n) G.2⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · exact (Set.countable_iUnion fun n => (hEc n).image _).union (Set.countable_range _)
  · rintro g (hg | ⟨n, rfl⟩)
    · obtain ⟨n, G, -, rfl⟩ := Set.mem_iUnion.mp hg
      exact hS_cc n G
    · exact ⟨continuous_ballCutoff x₀ n, hasCompactSupport_ballCutoff x₀ n⟩
  · intro m hm hD f hf hfc
    obtain ⟨n, hn⟩ : ∃ n : ℕ, tsupport f ⊆ closedBall x₀ (n : ℝ) := by
      obtain ⟨r, hr⟩ := hfc.isCompact.isBounded.subset_closedBall x₀
      exact ⟨⌈r⌉₊, hr.trans (closedBall_subset_closedBall (Nat.le_ceil r))⟩
    have hfS : (⟨f, hf⟩ : C(X, ℝ)) ∈ S n := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hn h)
    have hχD : ballCutoff x₀ n ∈ D := Or.inr ⟨n, rfl⟩
    obtain ⟨ℓχ, hℓχ⟩ := hD _ hχD
    obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ k, ∫ x, ballCutoff x₀ n x ∂(m k) ≤ B := by
      obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hℓχ).exists_norm_le
      exact ⟨C, fun k => (le_abs_self _).trans (hC _ ⟨k, rfl⟩)⟩
    have hB0 : 0 ≤ B := (integral_nonneg fun x => ballCutoff_nonneg x₀ n x).trans (hB 0)
    have hintf : ∀ k, Integrable f (m k) := fun k => by
      have := hm k
      exact hf.integrable_of_hasCompactSupport hfc
    have hintχ : ∀ k, Integrable (ballCutoff x₀ n) (m k) := fun k => by
      have := hm k
      exact (continuous_ballCutoff x₀ n).integrable_of_hasCompactSupport (hasCompactSupport_ballCutoff x₀ n)
    -- uniform approximation of `f` on the ball by a member of the dense family
    have happrox : ∀ η : ℝ, 0 < η →
        ∃ G ∈ E n, ∀ x, |f x - (G : C(X, ℝ)) x| ≤ η * ballCutoff x₀ n x := by
      intro η hη
      have : CompactSpace (closedBall x₀ (n : ℝ)) :=
        isCompact_iff_compactSpace.mp (isCompact_closedBall x₀ n)
      let r : S n → C(closedBall x₀ (n : ℝ), ℝ) := fun G => (G : C(X, ℝ)).restrict (closedBall x₀ n)
      have hr : Continuous r := (ContinuousMap.continuous_restrict _).comp continuous_subtype_val
      let F : S n := ⟨⟨f, hf⟩, hfS⟩
      have hopen : IsOpen (r ⁻¹' Metric.ball (r F) η) := Metric.isOpen_ball.preimage hr
      obtain ⟨G, hGU, hGE⟩ := (hEd n).inter_open_nonempty _ hopen ⟨F, Metric.mem_ball_self hη⟩
      refine ⟨G, hGE, fun x => ?_⟩
      by_cases hx : x ∈ closedBall x₀ (n : ℝ)
      · have h1 : dist ((r G) ⟨x, hx⟩) ((r F) ⟨x, hx⟩) ≤ dist (r G) (r F) :=
          ContinuousMap.dist_apply_le_dist _
        have h2 : dist (r G) (r F) < η := hGU
        have h3 : ballCutoff x₀ n x = 1 := ballCutoff_eq_one (mem_closedBall.mp hx)
        rw [h3, mul_one, abs_sub_comm]
        exact h1.trans h2.le
      · have h1 : (G : C(X, ℝ)) x = 0 := G.2 x hx
        have h2 : f x = 0 := hfS x hx
        rw [h1, h2, sub_zero, abs_zero]
        exact mul_nonneg hη.le (ballCutoff_nonneg x₀ n x)
    have hcauchy : CauchySeq fun k => ∫ x, f x ∂(m k) := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨G, hGE, hG⟩ := happrox (ε / (4 * (B + 1))) (by positivity)
      have hGD : ((G : C(X, ℝ)) : X → ℝ) ∈ D := Or.inl (Set.mem_iUnion.mpr ⟨n, G, hGE, rfl⟩)
      obtain ⟨ℓG, hℓG⟩ := hD _ hGD
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hℓG.cauchySeq (ε / 2) (by positivity)
      have hclose : ∀ k, |∫ x, f x ∂(m k) - ∫ x, (G : C(X, ℝ)) x ∂(m k)| ≤ ε / 4 := by
        intro k
        have := hm k
        have hintG : Integrable (fun x => (G : C(X, ℝ)) x) (m k) :=
          (hS_cc n G).1.integrable_of_hasCompactSupport (hS_cc n G).2
        rw [← integral_sub (hintf k) hintG]
        calc |∫ x, (f x - (G : C(X, ℝ)) x) ∂(m k)|
            = ‖∫ x, (f x - (G : C(X, ℝ)) x) ∂(m k)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ∫ x, ε / (4 * (B + 1)) * ballCutoff x₀ n x ∂(m k) :=
              norm_integral_le_of_norm_le ((hintχ k).const_mul _)
                (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hG x)
          _ = ε / (4 * (B + 1)) * ∫ x, ballCutoff x₀ n x ∂(m k) := integral_const_mul _ _
          _ ≤ ε / (4 * (B + 1)) * B := mul_le_mul_of_nonneg_left (hB k) (by positivity)
          _ ≤ ε / 4 := by
              rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith
      refine ⟨N, fun k hk => ?_⟩
      have h1 := hclose k
      have h2 := hclose N
      have h3 := hN k hk
      rw [Real.dist_eq] at h3 ⊢
      rw [abs_lt] at h3 ⊢
      rw [abs_le] at h1 h2
      constructor <;> linarith
    exact cauchySeq_tendsto_of_complete hcauchy

/-- A sequence of measures finite on compacts, on a proper metric space, has a locally finite vague limit as soon as
its integrals converge on the countable family of `exists_countable_determining`. -/
theorem exists_countable_determining_vague_limit [Nonempty X] :
    ∃ D : Set (X → ℝ), D.Countable ∧ (∀ g ∈ D, Continuous g ∧ HasCompactSupport g) ∧
      ∀ m : ℕ → Measure X, (∀ k, IsFiniteMeasureOnCompacts (m k)) →
        (∀ g ∈ D, ∃ ℓ : ℝ, Tendsto (fun k => ∫ x, g x ∂(m k)) atTop (𝓝 ℓ)) →
        ∃ μ : Measure X, IsLocallyFiniteMeasure μ ∧ ∀ f : X → ℝ, Continuous f → HasCompactSupport f →
          Tendsto (fun k => ∫ x, f x ∂(m k)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨D, hDc, hDcc, hD⟩ := exists_countable_determining (X := X)
  exact ⟨D, hDc, hDcc, fun m hm hconv =>
    exists_isLocallyFiniteMeasure_tendsto_integral m hm (hD m hm hconv)⟩

end Countable

end LatticeProb.VagueLimit
