import LatticeProb.Vendor.FormalMathPercolation.Literature.SharpnessDCTProofs
import LatticeProb.Vendor.FormalMathPercolation.Literature.BernoulliPercolationProofs

/-!
# Finite-size critical threshold

The finite-size threshold agrees with the critical probability of Bernoulli
bond percolation on the integer lattice.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open Percolation.Literature.LatticeModels Filter
open scoped ProbabilityTheory Topology

noncomputable section

namespace FiniteSizeCriticalThreshold

/-- The supremum of parameters admitting a finite set with boundary sum below one. -/
def finiteSizeCriticalProb (d : ℕ) : ℝ :=
  sSup {p : ℝ | ∃ hp : p ∈ unitInterval,
    ∃ S : Finset (Site d), (0 : Site d) ∈ S ∧ DCT16.phi ⟨p, hp⟩ S < 1}

private theorem admissible_nonempty (d : ℕ) :
    ({p : ℝ | ∃ hp : p ∈ unitInterval,
      ∃ S : Finset (Site d), (0 : Site d) ∈ S ∧ DCT16.phi ⟨p, hp⟩ S < 1}).Nonempty := by
  refine ⟨0, ⟨⟨le_rfl, zero_le_one⟩, {0}, by simp, ?_⟩⟩
  change DCT16.phi (0 : unitInterval) {0} < 1
  simp

private theorem admissible_bddAbove (d : ℕ) :
    BddAbove {p : ℝ | ∃ hp : p ∈ unitInterval,
      ∃ S : Finset (Site d), (0 : Site d) ∈ S ∧ DCT16.phi ⟨p, hp⟩ S < 1} := by
  refine ⟨1, ?_⟩
  rintro p ⟨hp, _⟩
  exact hp.2

private theorem theta_eq_zero_of_phi_lt_one {d : ℕ} (p : unitInterval)
    (hp : (p : ℝ) < 1) (S : Finset (Site d)) (hS : (0 : Site d) ∈ S)
    (hphi : DCT16.phi p S < 1) : theta (zdGraph d) 0 p = 0 := by
  obtain ⟨c, hc, hdec⟩ := DCT16.DCT16_expDecay_of_phi_lt_one_holds p S hS hphi hp
  have ht : Tendsto (fun n : ℕ => Real.exp (-c * n)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos hc)
  apply le_antisymm
  · apply ge_of_tendsto ht
    exact Filter.Eventually.of_forall fun n =>
      (DCT16.theta_le_real_siteToBoundary p n).trans (hdec n)
  · exact measureReal_nonneg

/-- The finite-size threshold is the usual critical probability. -/
theorem finiteSizeCriticalProb_eq_criticalProb (d : ℕ) :
    finiteSizeCriticalProb d = criticalProb (zdGraph d) 0 := by
  let A : Set ℝ := {p : ℝ | ∃ hp : p ∈ unitInterval,
    ∃ S : Finset (Site d), (0 : Site d) ∈ S ∧ DCT16.phi ⟨p, hp⟩ S < 1}
  have hA : A.Nonempty := admissible_nonempty d
  have hAb : BddAbove A := admissible_bddAbove d
  have hAc : finiteSizeCriticalProb d = sSup A := rfl
  have hA0 : 0 ≤ finiteSizeCriticalProb d := by
    rw [hAc]
    apply le_csSup hAb
    exact ⟨⟨le_rfl, zero_le_one⟩, {0}, by simp, by change DCT16.phi (0 : unitInterval) {0} < 1; simp⟩
  have hA1 : finiteSizeCriticalProb d ≤ 1 := by
    rw [hAc]
    exact csSup_le hA (fun _ h => h.1.2)
  obtain ⟨hpc0, hpc1⟩ := criticalProb_mem_Icc (zdGraph d) (0 : Site d)
  apply le_antisymm
  · rw [hAc]
    apply csSup_le hA
    rintro p ⟨hp, S, hS, hphi⟩
    by_contra h
    have hpcp : criticalProb (zdGraph d) 0 < p := lt_of_not_ge h
    let q : ℝ := (criticalProb (zdGraph d) 0 + p) / 2
    have hcq : criticalProb (zdGraph d) 0 < q := by dsimp [q]; linarith
    have hqp : q < p := by dsimp [q]; linarith
    have hq : q ∈ unitInterval := ⟨by linarith, by linarith [hp.2]⟩
    let q' : unitInterval := ⟨q, hq⟩
    have hphi' : DCT16.phi q' S < 1 :=
      (DCT16.DCT16_phi_mono_holds S (show q' ≤ ⟨p, hp⟩ from hqp.le)).trans_lt hphi
    have hz := theta_eq_zero_of_phi_lt_one q' (by change q < 1; linarith [hp.2]) S hS hphi'
    have hpos := theta_pos_of_criticalProb_lt_holds (zdGraph d) 0 q' hcq
    linarith
  · by_contra h
    have hac : finiteSizeCriticalProb d < criticalProb (zdGraph d) 0 := lt_of_not_ge h
    let p : ℝ := (finiteSizeCriticalProb d + criticalProb (zdGraph d) 0) / 2
    let r : ℝ := (p + criticalProb (zdGraph d) 0) / 2
    have hap : finiteSizeCriticalProb d < p := by dsimp [p]; linarith
    have hpr : p < r := by dsimp [r, p]; linarith
    have hrc : r < criticalProb (zdGraph d) 0 := by dsimp [r, p]; linarith
    have hp : p ∈ unitInterval := ⟨by linarith, by linarith⟩
    have hr : r ∈ unitInterval := ⟨by linarith, by linarith⟩
    let p' : unitInterval := ⟨p, hp⟩
    let r' : unitInterval := ⟨r, hr⟩
    have hphi : ∀ q : unitInterval, p' ≤ q → ∀ S : Finset (Site d),
        (0 : Site d) ∈ S → 1 ≤ DCT16.phi q S := by
      intro q hpq S hS
      have hbase : 1 ≤ DCT16.phi p' S := by
        by_contra hh
        have hmem : p ∈ A := ⟨hp, S, hS, lt_of_not_ge hh⟩
        have hle : p ≤ finiteSizeCriticalProb d := hAc.symm ▸ le_csSup hAb hmem
        linarith
      exact hbase.trans (DCT16.DCT16_phi_mono_holds S hpq)
    have hθ := DCT16.DCT16_meanField_of_phi_ge_one_holds p' hphi r' hpr (by change r < 1; linarith)
    have hz := theta_eq_zero_of_lt_criticalProb_holds (zdGraph d) 0 r' hrc
    have hpos : 0 < (r - p) / (r * (1 - p)) :=
      div_pos (by linarith) (mul_pos (by linarith) (by linarith))
    change (r - p) / (r * (1 - p)) ≤ theta (zdGraph d) 0 r' at hθ
    linarith

/-- Below the critical probability the one-arm probability decays exponentially. -/
theorem siteToBoundary_exp_decay_of_lt_criticalProb (d : ℕ) (p : unitInterval)
    (hp : (p : ℝ) < criticalProb (zdGraph d) 0) :
    ∃ c > 0, ∀ n : ℕ, 1 ≤ n →
      (bondPercolation (zdGraph d) p).real (siteToBoundary d n) ≤ Real.exp (-c * n) := by
  let A : Set ℝ := {q : ℝ | ∃ hq : q ∈ unitInterval,
    ∃ S : Finset (Site d), (0 : Site d) ∈ S ∧ DCT16.phi ⟨q, hq⟩ S < 1}
  have hpA : (p : ℝ) < sSup A := by
    change (p : ℝ) < finiteSizeCriticalProb d
    rw [finiteSizeCriticalProb_eq_criticalProb]
    exact hp
  obtain ⟨q, ⟨hq, S, hS, hphi⟩, hpq⟩ :=
    exists_lt_of_lt_csSup (admissible_nonempty d) hpA
  have hphi' : DCT16.phi p S < 1 :=
    (DCT16.DCT16_phi_mono_holds S (show p ≤ ⟨q, hq⟩ from hpq.le)).trans_lt hphi
  have hp1 : (p : ℝ) < 1 := hp.trans_le (criticalProb_mem_Icc (zdGraph d) 0).2
  obtain ⟨c, hc, hdec⟩ := DCT16.DCT16_expDecay_of_phi_lt_one_holds p S hS hphi' hp1
  exact ⟨c, hc, fun n _ => hdec n⟩

end FiniteSizeCriticalThreshold
