/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.GeometricToAnalytic.Loewner.ChainPotential
import NoWanderingDomains.Analysis.Helpers.WeightedLengthLSC
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The chain-potential boundary-value limit

The compactness heart of the planar Loewner reciprocity: the chain potentials of the
Moreau–Yosida approximants attain boundary values tending to `1` on the far side. This is
Claim 2 of Eriksson-Bique–Poggi-Corradini, *On the sharp lower bound for duality of
modulus*, Proc. AMS 150 (2022), Theorem 3.5, transplanted to the plane.

Setup: `Ω` a compact preconnected set, `E, F ⊆ Ω` closed, `ρ` a density admissible against
every absolutely continuous curve in `Ω` from `E` to `F`, and `Φ ≥ ρ` a lower
semicontinuous majorant with uniform cushion `Φ ≥ ε > 0`. Feed the `i`-th Moreau–Yosida
envelope `g_i = moreauEnvelope Φ i` to the chain potential at mesh `1/(i+1)` on the domain
`D_i = closure (thickening (1/(i+1)) Ω)`.

**Claim: for every `δ > 0`, eventually in `i`, the potential is `≥ 1 − δ` everywhere on
`F`.** Contradiction argument: otherwise there are indices `i → ∞` and chains from `E`
into `F` through `D_i` of `g_i`-cost `≤ 1 − δ`.

* The cushion survives to the envelopes (`le_moreauEnvelope_of_forall_le`), so the chain
  cost dominates `ε ·` (chain length): chain lengths are bounded by `(1−δ)/ε`.
* `exists_lipschitz_interpolation` (`Analysis/Helpers/WeightedLengthLSC.lean`) interpolates each
  chain by a single `L`-Lipschitz curve through the chain segments (so within
  `2/(i+1)` of `Ω`), with weighted length against each fixed envelope `g_{i₀}` bounded by
  the chain cost plus `i₀ · (1/(i+1)) · L → 0` (envelopes are monotone:
  `g_{i₀} ≤ g_i` at the chain points).
* `exists_subseq_tendstoUniformlyOn_of_lipschitzWith` extracts a uniform limit curve `γ₀`:
  Lipschitz, from `E` to `F` (closedness), with trace in `⋂ᵢ (2/(i+1))`-neighborhoods
  `= Ω`.
* Lower semicontinuity of the weighted length against the fixed continuous envelope
  (`arcLengthLineIntegral_le_liminf_of_tendstoUniformlyOn`) gives
  `∫_{γ₀} g_{i₀} ds ≤ 1 − δ` for every `i₀`; monotone convergence
  (`lintegral_iSup'` + `iSup_ofReal_moreauEnvelope`) upgrades to
  `∫_{γ₀} Φ ds ≤ 1 − δ`, hence `∫_{γ₀} ρ ds ≤ 1 − δ < 1`.
* But `γ₀` is a continuous absolutely continuous curve in `Ω` from `E` to `F` (Lipschitz ⇒
  AC via `lipschitzOnWith_uIcc_absolutelyContinuousOnInterval`), so admissibility forces
  `∫_{γ₀} ρ ds ≥ 1` — contradiction.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- **The chain-potential boundary-value limit (Eriksson-Bique–Poggi-Corradini Claim 2).**
Under the setup of the file docstring, for every `δ > 0` there is `i₀` such that for all
`i ≥ i₀` and every `w ∈ F`,

  `1 − δ ≤ chainPotential (closure (thickening (1/(i+1)) Ω)) E (moreauEnvelope Φ i)
      (1/(i+1)) w`. -/
theorem chainPotential_limit_one
    {Ω E F : Set ℂ} (hΩc : IsCompact Ω) (hΩconn : IsPreconnected Ω)
    (hE : IsClosed E) (hF : IsClosed F) (hEΩ : E ⊆ Ω) (hFΩ : F ⊆ Ω) (hEne : E.Nonempty)
    {ρ : ℂ → ℝ≥0∞}
    (hadm : ∀ γ : ℝ → ℂ, Continuous γ → AbsolutelyContinuousOnInterval γ 0 1 →
      γ 0 ∈ E → γ 1 ∈ F → (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Ω) →
      1 ≤ arcLengthLineIntegral ρ γ)
    {Φ : ℂ → ℝ≥0∞} (hΦlsc : LowerSemicontinuous Φ) (hΦρ : ∀ z, ρ z ≤ Φ z)
    {ε : ℝ} (hε : 0 < ε) (hΦε : ∀ z, ENNReal.ofReal ε ≤ Φ z)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → ∀ w ∈ F,
      1 - δ ≤ chainPotential (closure (Metric.thickening (1 / (i + 1 : ℝ)) Ω)) E
          (moreauEnvelope Φ i) (1 / (i + 1 : ℝ)) w := by
  -- Trivial case: `1 ≤ δ` — the potential is nonnegative, and `1 - δ ≤ 0`.
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · refine ⟨0, fun i _ w' _ => ?_⟩
    have h0 := chainPotential_nonneg (D := closure (Metric.thickening (1 / (i + 1 : ℝ)) Ω))
      (A := E) (moreauEnvelope_nonneg Φ i) (1 / (i + 1 : ℝ)) w'
    linarith
  -- Main case: `δ < 1`. Argue by contradiction.
  by_contra hcon
  push Not at hcon
  -- Basic geometric facts.
  obtain ⟨x₀, hx₀E⟩ := hEne
  have hΩne : Ω.Nonempty := ⟨x₀, hEΩ hx₀E⟩
  have hrpos : ∀ i : ℕ, (0 : ℝ) < 1 / (i + 1 : ℝ) := fun i => by positivity
  have hΩD : ∀ i : ℕ, Ω ⊆ closure (Metric.thickening (1 / (i + 1 : ℝ)) Ω) := fun i =>
    (Metric.self_subset_thickening (hrpos i) Ω).trans subset_closure
  -- A cushion index: `ε ≤ N₀`.
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge ε
  -- Extract a sequence of bad indices `n k ≥ N₀ + k` with witnesses `w k ∈ F`.
  choose n hn w hwF hwP using fun k : ℕ => hcon (N₀ + k)
  -- The cushion survives to the envelopes at the extracted indices.
  have hεn : ∀ k : ℕ, ∀ x : ℂ, ε ≤ moreauEnvelope Φ (n k) x := by
    intro k x
    refine le_moreauEnvelope_of_forall_le hε.le hΦε ?_ x
    calc ε ≤ (N₀ : ℝ) := hN₀
      _ ≤ ((n k : ℕ) : ℝ) := by
          exact_mod_cast (Nat.le_add_right N₀ k).trans (hn k)
  -- Extract chains of cost `< 1 - δ`, padded so that they have at least one step.
  have hchain : ∀ k : ℕ, ∃ (m : ℕ) (z : Fin (m + 1) → ℂ), 1 ≤ m ∧
      (∀ i, z i ∈ closure (Metric.thickening (1 / (n k + 1 : ℝ)) Ω)) ∧
      (∀ i : Fin m, dist (z i.castSucc) (z i.succ) ≤ 1 / (n k + 1 : ℝ)) ∧
      z 0 ∈ E ∧ z (Fin.last m) = w k ∧
      ∑ i : Fin m, moreauEnvelope Φ (n k) (z i.castSucc) * dist (z i.castSucc) (z i.succ)
        < 1 - δ := by
    intro k
    have hwD : w k ∈ closure (Metric.thickening (1 / (n k + 1 : ℝ)) Ω) :=
      hΩD (n k) (hFΩ (hwF k))
    have hED : (E ∩ closure (Metric.thickening (1 / (n k + 1 : ℝ)) Ω)).Nonempty :=
      ⟨x₀, hx₀E, hΩD (n k) (hEΩ hx₀E)⟩
    have hne : (chainCosts (closure (Metric.thickening (1 / (n k + 1 : ℝ)) Ω)) E
        (moreauEnvelope Φ (n k)) (1 / (n k + 1 : ℝ)) (w k)).Nonempty :=
      chainCosts_nonempty (isPreconnected_closure_thickening hΩconn (hrpos (n k)))
        (hrpos (n k)) hED hwD
    have hsinf : sInf (chainCosts (closure (Metric.thickening (1 / (n k + 1 : ℝ)) Ω)) E
        (moreauEnvelope Φ (n k)) (1 / (n k + 1 : ℝ)) (w k)) < 1 - δ := by
      have h1 := hwP k
      simp only [chainPotential] at h1
      rcases min_lt_iff.mp h1 with h | h
      · linarith
      · exact h
    obtain ⟨c, hcmem, hclt⟩ := exists_lt_of_csInf_lt hne hsinf
    simp only [chainCosts, Set.mem_ofPred_eq] at hcmem
    obtain ⟨m, z, hzD, hzstep, hz0, hzlast, rfl⟩ := hcmem
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- A zero-step chain forces `w k ∈ E`; pad with the constant one-step chain at `w k`.
      have hwE : w k ∈ E := by
        have h00 : z (Fin.last 0) = z 0 := congrArg z (Fin.fin_one_eq_zero _)
        rw [← hzlast, h00]; exact hz0
      refine ⟨1, fun _ => w k, le_rfl, fun _ => hwD, ?_, hwE, rfl, ?_⟩
      · intro i
        simp only [dist_self]
        positivity
      · simp only [dist_self, mul_zero, Finset.sum_const_zero]
        linarith
    · exact ⟨m, z, hm, hzD, hzstep, hz0, hzlast, hclt⟩
  choose m z hm hzD hzstep hz0 hzlast hcost using hchain
  -- The cushion bounds the chain lengths by `L₀ := (1 - δ) / ε`.
  set L₀ : ℝ := (1 - δ) / ε with hL₀def
  have hlen : ∀ k, ∑ i : Fin (m k), dist (z k i.castSucc) (z k i.succ) ≤ L₀ := by
    intro k
    have h1 : ε * ∑ i : Fin (m k), dist (z k i.castSucc) (z k i.succ)
        ≤ ∑ i : Fin (m k),
            moreauEnvelope Φ (n k) (z k i.castSucc) * dist (z k i.castSucc) (z k i.succ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hεn k _) dist_nonneg
    rw [hL₀def, le_div_iff₀ hε]
    have h2 := mul_comm ε (∑ i : Fin (m k), dist (z k i.castSucc) (z k i.succ))
    linarith [hcost k]
  -- Interpolate every chain by a single `L₀`-Lipschitz curve.
  choose γ hγ0 hγ1 hγlip hγtrace hγweight using fun k =>
    exists_lipschitz_interpolation (hm k) (z k) (hrpos (n k)) (hzstep k) (hlen k)
  -- Every interpolant stays within `2/(n k + 1)` of `Ω`.
  have htrΩ : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Metric.infDist (γ k t) Ω ≤ 2 * (1 / (n k + 1 : ℝ)) := by
    intro k t ht
    obtain ⟨i, hseg⟩ := hγtrace k t ht
    have hp : Metric.infDist (z k i.castSucc) Ω ≤ 1 / (n k + 1 : ℝ) := by
      have h1 : Metric.infEDist (z k i.castSucc) Ω ≤ ENNReal.ofReal (1 / (n k + 1 : ℝ)) :=
        Metric.mem_cthickening_iff.mp
          (Metric.closure_thickening_subset_cthickening _ _ (hzD k i.castSucc))
      have h2 : Metric.infDist (z k i.castSucc) Ω
          ≤ (ENNReal.ofReal (1 / (n k + 1 : ℝ))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal (hrpos (n k)).le] at h2
    have hq : dist (γ k t) (z k i.castSucc) ≤ dist (z k i.castSucc) (z k i.succ) := by
      have hsub : segment ℝ (z k i.castSucc) (z k i.succ) ⊆
          Metric.closedBall (z k i.castSucc) (dist (z k i.castSucc) (z k i.succ)) := by
        refine (convex_closedBall _ _).segment_subset
          (Metric.mem_closedBall_self dist_nonneg) ?_
        exact Metric.mem_closedBall.mpr (dist_comm (z k i.succ) (z k i.castSucc)).le
      exact Metric.mem_closedBall.mp (hsub hseg)
    calc Metric.infDist (γ k t) Ω
        ≤ Metric.infDist (z k i.castSucc) Ω + dist (γ k t) (z k i.castSucc) :=
          Metric.infDist_le_infDist_add_dist
      _ ≤ 1 / (n k + 1 : ℝ) + 1 / (n k + 1 : ℝ) := add_le_add hp (hq.trans (hzstep k i))
      _ = 2 * (1 / (n k + 1 : ℝ)) := by ring
  -- The interpolants are uniformly bounded (Arzelà–Ascoli input).
  obtain ⟨R₀, hR₀⟩ := hΩc.isBounded.subset_closedBall (0 : ℂ)
  have hbd : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ k t ∈ Metric.closedBall (0 : ℂ) (R₀ + 2) := by
    intro k t ht
    obtain ⟨ω, hωΩ, hωd⟩ := hΩc.exists_infDist_eq_dist hΩne (γ k t)
    have h1 : Metric.infDist (γ k t) Ω ≤ 2 * (1 / (n k + 1 : ℝ)) := htrΩ k t ht
    have h2 : 2 * (1 / (n k + 1 : ℝ)) ≤ 2 := by
      have h3 : (1 : ℝ) / (n k + 1 : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have h4 : (0 : ℝ) ≤ (n k : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
    have h5 : dist (γ k t) ω ≤ 2 := by rw [← hωd]; linarith
    have h6 : dist ω 0 ≤ R₀ := Metric.mem_closedBall.mp (hR₀ hωΩ)
    have h7 := dist_triangle (γ k t) ω (0 : ℂ)
    exact Metric.mem_closedBall.mpr (by linarith)
  -- Arzelà–Ascoli: extract a uniformly convergent subsequence.
  obtain ⟨φ, γ₀, hφ, hγ₀lip, hconv⟩ :=
    exists_subseq_tendstoUniformlyOn_of_lipschitzWith hγlip hbd
  -- The extracted indices still escape to infinity.
  have hnφ : ∀ j : ℕ, j ≤ n (φ j) := fun j =>
    (hφ.le_apply).trans ((Nat.le_add_left (φ j) N₀).trans (hn (φ j)))
  have hmesh : Tendsto (fun j : ℕ => 1 / (n (φ j) + 1 : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun j => by positivity) (fun j => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h1 : ((j : ℕ) : ℝ) ≤ ((n (φ j) : ℕ) : ℝ) := by exact_mod_cast hnφ j
    linarith
  -- The limit curve runs from `E` to `F`.
  have hγ₀0E : γ₀ 0 ∈ E := by
    refine hE.mem_of_tendsto (hconv.tendsto_at (Set.left_mem_Icc.mpr zero_le_one))
      (Eventually.of_forall fun j => ?_)
    rw [hγ0 (φ j)]; exact hz0 (φ j)
  have hγ₀1F : γ₀ 1 ∈ F := by
    refine hF.mem_of_tendsto (hconv.tendsto_at (Set.right_mem_Icc.mpr zero_le_one))
      (Eventually.of_forall fun j => ?_)
    rw [hγ1 (φ j), hzlast (φ j)]; exact hwF (φ j)
  -- The limit curve has its trace in `Ω`.
  have hγ₀Ω : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₀ t ∈ Ω := by
    intro t ht
    have hptw : Tendsto (fun j => γ (φ j) t) atTop (𝓝 (γ₀ t)) := hconv.tendsto_at ht
    have hinf : Tendsto (fun j => Metric.infDist (γ (φ j) t) Ω) atTop
        (𝓝 (Metric.infDist (γ₀ t) Ω)) :=
      ((Metric.continuous_infDist_pt Ω).tendsto (γ₀ t)).comp hptw
    have h2 : Tendsto (fun j : ℕ => 2 * (1 / (n (φ j) + 1 : ℝ))) atTop (𝓝 0) := by
      simpa using hmesh.const_mul (2 : ℝ)
    have hle : Metric.infDist (γ₀ t) Ω ≤ 0 :=
      le_of_tendsto_of_tendsto' hinf h2 fun j => htrΩ (φ j) t ht
    exact (hΩc.isClosed.mem_iff_infDist_zero hΩne).mpr
      (le_antisymm hle Metric.infDist_nonneg)
  -- Cost transfer: against every fixed envelope, the limit curve has weighted length
  -- at most `1 - δ`.
  have hkey : ∀ i₀ : ℕ,
      arcLengthLineIntegral (fun zz => ENNReal.ofReal (moreauEnvelope Φ i₀ zz)) γ₀
        ≤ ENNReal.ofReal (1 - δ) := by
    intro i₀
    have hlsc := arcLengthLineIntegral_le_liminf_of_tendstoUniformlyOn
      (g := moreauEnvelope Φ i₀) ((moreauEnvelope_lipschitz Φ i₀).continuous)
      (moreauEnvelope_nonneg Φ i₀) (fun j => hγlip (φ j)) hγ₀lip hconv
    refine hlsc.trans ?_
    have hbound : ∀ᶠ j in atTop,
        arcLengthLineIntegral (fun zz => ENNReal.ofReal (moreauEnvelope Φ i₀ zz)) (γ (φ j))
          ≤ ENNReal.ofReal (1 - δ + (i₀ : ℝ) * (1 / (n (φ j) + 1 : ℝ)) * L₀) := by
      filter_upwards [eventually_ge_atTop i₀] with j hj
      have hi₀n : i₀ ≤ n (φ j) := hj.trans (hnφ j)
      have hw := hγweight (φ j) (moreauEnvelope Φ i₀) (i₀ : ℝ≥0)
        (moreauEnvelope_lipschitz Φ i₀) (moreauEnvelope_nonneg Φ i₀)
      refine hw.trans (ENNReal.ofReal_le_ofReal ?_)
      have hsum : ∑ i : Fin (m (φ j)),
            moreauEnvelope Φ i₀ (z (φ j) i.castSucc)
              * dist (z (φ j) i.castSucc) (z (φ j) i.succ)
          ≤ ∑ i : Fin (m (φ j)),
              moreauEnvelope Φ (n (φ j)) (z (φ j) i.castSucc)
                * dist (z (φ j) i.castSucc) (z (φ j) i.succ) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (moreauEnvelope_mono Φ hi₀n _) dist_nonneg
      rw [NNReal.coe_natCast]
      linarith [hcost (φ j)]
    have hblim : Tendsto
        (fun j => ENNReal.ofReal (1 - δ + (i₀ : ℝ) * (1 / (n (φ j) + 1 : ℝ)) * L₀)) atTop
        (𝓝 (ENNReal.ofReal (1 - δ))) := by
      refine ENNReal.tendsto_ofReal ?_
      have h0 : Tendsto (fun j : ℕ => (i₀ : ℝ) * (1 / (n (φ j) + 1 : ℝ)) * L₀) atTop
          (𝓝 0) := by
        simpa using (hmesh.const_mul (i₀ : ℝ)).mul_const L₀
      simpa using tendsto_const_nhds.add h0
    calc liminf (fun j =>
          arcLengthLineIntegral (fun zz => ENNReal.ofReal (moreauEnvelope Φ i₀ zz)) (γ (φ j)))
            atTop
        ≤ liminf (fun j =>
            ENNReal.ofReal (1 - δ + (i₀ : ℝ) * (1 / (n (φ j) + 1 : ℝ)) * L₀)) atTop :=
          Filter.liminf_le_liminf hbound
      _ = ENNReal.ofReal (1 - δ) := hblim.liminf_eq
  -- Monotone convergence upgrades the bound to the majorant `Φ`.
  have hΦint : arcLengthLineIntegral Φ γ₀ ≤ ENNReal.ofReal (1 - δ) := by
    have hmeasd : Measurable fun t : ℝ => (‖deriv γ₀ t‖₊ : ℝ≥0∞) :=
      (measurable_deriv γ₀).nnnorm.coe_nnreal_ennreal
    have hmeasf : ∀ i : ℕ, Measurable fun t : ℝ =>
        ENNReal.ofReal (moreauEnvelope Φ i (γ₀ t)) * (‖deriv γ₀ t‖₊ : ℝ≥0∞) := fun i =>
      ((ENNReal.continuous_ofReal.comp
        ((moreauEnvelope_lipschitz Φ i).continuous.comp hγ₀lip.continuous)).measurable).mul
        hmeasd
    have hmono : Monotone fun (i : ℕ) (t : ℝ) =>
        ENNReal.ofReal (moreauEnvelope Φ i (γ₀ t)) * (‖deriv γ₀ t‖₊ : ℝ≥0∞) :=
      fun i j hij t =>
        mul_le_mul_left (ENNReal.ofReal_le_ofReal (moreauEnvelope_mono Φ hij _)) _
    calc arcLengthLineIntegral Φ γ₀
        = ∫⁻ t in Set.Icc (0 : ℝ) 1,
            ⨆ i : ℕ, ENNReal.ofReal (moreauEnvelope Φ i (γ₀ t)) * (‖deriv γ₀ t‖₊ : ℝ≥0∞) := by
          simp only [arcLengthLineIntegral]
          refine lintegral_congr fun t => ?_
          rw [← iSup_ofReal_moreauEnvelope hΦlsc (γ₀ t), ENNReal.iSup_mul]
      _ = ⨆ i : ℕ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
            ENNReal.ofReal (moreauEnvelope Φ i (γ₀ t)) * (‖deriv γ₀ t‖₊ : ℝ≥0∞) :=
          lintegral_iSup hmeasf hmono
      _ ≤ ENNReal.ofReal (1 - δ) := by
          refine iSup_le fun i => ?_
          simpa only [arcLengthLineIntegral] using hkey i
  -- Downgrade to `ρ ≤ Φ` and contradict admissibility.
  have hρint : arcLengthLineIntegral ρ γ₀ ≤ ENNReal.ofReal (1 - δ) := by
    refine le_trans ?_ hΦint
    simp only [arcLengthLineIntegral]
    exact lintegral_mono fun t => mul_le_mul_left (hΦρ (γ₀ t)) _
  have h1le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 - δ) :=
    (hadm γ₀ hγ₀lip.continuous
      (lipschitzOnWith_uIcc_absolutelyContinuousOnInterval hγ₀lip.lipschitzOnWith)
      hγ₀0E hγ₀1F hγ₀Ω).trans hρint
  exact absurd h1le (not_le.mpr (ENNReal.ofReal_lt_one.mpr (by linarith)))

end NoWanderingDomains
