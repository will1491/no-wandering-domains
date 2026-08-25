/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.WeakLimits.JacobianWeakContinuity.WeakContinuity
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Weak `L²_loc` limits: extraction, calculus, and the variational inequality lemma

Connective tissue between the abstract Hilbert-space weak compactness of
`Analysis/WeakLimits/WeakCompactness.lean` and the concrete `L²_loc` pairing form
(`TendstoWeaklyL2Loc`, `Analysis/WeakLimits/JacobianWeakContinuity/NullLagrangian.lean`) that the
null-Lagrangian cluster consumes.

* `exists_subseq_tendstoWeaklyL2Loc` — **local weak `L²` sequential compactness**: a
  sequence with uniform `L²` bounds on every ball has a subsequence converging weakly
  against every compactly supported `L²` test, to a limit that is itself `L²_loc`.
  The proof runs a *single* Hilbert-space extraction in the weighted space
  `L²(w·volume)`, where the weight `w` is built from the given ball bounds so that the
  whole sequence is uniformly `w`-square-integrable; pairing against compactly
  supported tests divides the weight back out. This avoids any ball-by-ball diagonal
  argument.
* `TendstoWeaklyL2Loc.smul_add_smul` — weak limits pass through fixed real linear
  combinations (the directional-derivative combinations of a gradient pair).
* `memW12loc_of_continuous_weakGradient` — packaging: a continuous function with an
  `L²_loc` weak gradient is `W^{1,2}_loc`.
* `ae_nonpos_of_forall_integral_smooth_mul_nonpos` — the inequality form of the
  fundamental lemma of the calculus of variations: a locally integrable function whose
  pairings against all nonnegative smooth compactly supported tests are nonpositive is
  itself nonpositive almost everywhere.
* `integral_normSq_le_of_lintegral_enormSq_le` — Bochner/lower-integral bookkeeping for
  squared norms.
-/

open MeasureTheory Complex Filter
open scoped ContDiff ENNReal NNReal Topology

namespace NoWanderingDomains

/-- **Weak local limits of real linear combinations.** If `hₙ ⇀ u` and `h'ₙ ⇀ u'`
weakly against compactly supported `L²` tests, and all the functions involved are
`L²_loc`, then for fixed real scalars `a`, `b` the combinations
`a•hₙ + b•h'ₙ` converge weakly to `a•u + b•u'`. The local square-integrability
hypotheses make each pairing integral split into the two pieces. -/
theorem TendstoWeaklyL2Loc.smul_add_smul {hₙ h'ₙ : ℕ → ℂ → ℂ} {u u' : ℂ → ℂ}
    (hw : TendstoWeaklyL2Loc hₙ u) (hw' : TendstoWeaklyL2Loc h'ₙ u')
    (hloc : ∀ n, MemLpLocOn (hₙ n) 2 Set.univ) (hloc' : ∀ n, MemLpLocOn (h'ₙ n) 2 Set.univ)
    (huloc : MemLpLocOn u 2 Set.univ) (hu'loc : MemLpLocOn u' 2 Set.univ)
    (a b : ℝ) :
    TendstoWeaklyL2Loc (fun n z => a • hₙ n z + b • h'ₙ n z)
      (fun z => a • u z + b • u' z) := by
  intro ψ hψ hψcs
  -- Any `L²_loc` function pairs integrably against the compactly supported `L²` test.
  have hInt : ∀ f : ℂ → ℂ, MemLpLocOn f 2 Set.univ →
      Integrable (fun z => f z * ψ z) volume := by
    intro f hf
    have hS : IsCompact (tsupport ψ) := hψcs
    have hfS : MemLp f 2 (volume.restrict (tsupport ψ)) :=
      hf (tsupport ψ) (Set.subset_univ _) hS
    have hprodS : Integrable (fun z => f z * ψ z) (volume.restrict (tsupport ψ)) :=
      hfS.integrable_mul (hψ.restrict (tsupport ψ))
    rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport ψ)]
    · exact hprodS
    · intro z hz
      by_contra hzS
      have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hzS
      exact hz (by simp [hψz])
  -- The pairing integral splits through the fixed real linear combination.
  have key : ∀ f g : ℂ → ℂ, MemLpLocOn f 2 Set.univ → MemLpLocOn g 2 Set.univ →
      (∫ z, (a • f z + b • g z) * ψ z)
        = a • (∫ z, f z * ψ z) + b • (∫ z, g z * ψ z) := by
    intro f g hf hg
    have h1 : Integrable (fun z => a • (f z * ψ z)) volume := (hInt f hf).smul a
    have h2 : Integrable (fun z => b • (g z * ψ z)) volume := (hInt g hg).smul b
    calc (∫ z, (a • f z + b • g z) * ψ z)
        = ∫ z, (a • (f z * ψ z) + b • (g z * ψ z)) := by
          simp only [add_mul, smul_mul_assoc]
      _ = (∫ z, a • (f z * ψ z)) + ∫ z, b • (g z * ψ z) := integral_add h1 h2
      _ = a • (∫ z, f z * ψ z) + b • (∫ z, g z * ψ z) := by
          congr 1
          · exact integral_smul a fun z => f z * ψ z
          · exact integral_smul b fun z => g z * ψ z
  -- Combine the two weak limits and rewrite both sides via the splitting identity.
  change Tendsto (fun n => ∫ z, (a • hₙ n z + b • h'ₙ n z) * ψ z) atTop
    (𝓝 (∫ z, (a • u z + b • u' z) * ψ z))
  rw [key u u' huloc hu'loc]
  exact Tendsto.congr (fun n => (key (hₙ n) (h'ₙ n) (hloc n) (hloc' n)).symm)
    (((hw ψ hψ hψcs).const_smul a).add ((hw' ψ hψ hψcs).const_smul b))

/-- **Local weak `L²` sequential compactness.** A sequence of measurable functions with
uniform `L²` bounds on every centred ball admits a subsequence converging weakly
against every compactly supported `L²` test function, to a limit which is `L²_loc`.

The proof performs a single Hilbert-space weak extraction
(`exists_weak_subseq_of_bounded`) in the weighted space `L²(w·volume)`: the weight
`w`, constant on the annuli `m ≤ ‖z‖ < m+1`, is chosen small enough (relative to the
given ball bounds `C`) that every member of the sequence has `w`-weighted energy at
most `2`. A compactly supported `L²` test divides by the weight (bounded below on the
support) to produce a legitimate weighted-space test vector, so weighted weak
convergence yields the unweighted local pairing convergence. -/
theorem exists_subseq_tendstoWeaklyL2Loc {hₙ : ℕ → ℂ → ℂ}
    (hmeas : ∀ n, AEStronglyMeasurable (hₙ n) volume)
    {C : ℕ → ℝ≥0∞} (hC : ∀ m, C m < ⊤)
    (hbound : ∀ (m : ℕ) (n : ℕ), (∫⁻ z in Metric.closedBall 0 (m : ℝ), ‖hₙ n z‖ₑ ^ 2) ≤ C m) :
    ∃ (φ : ℕ → ℕ) (u : ℂ → ℂ), StrictMono φ ∧ AEStronglyMeasurable u volume ∧
      MemLpLocOn u 2 Set.univ ∧ TendstoWeaklyL2Loc (fun k => hₙ (φ k)) u := by
  classical
  -- § 1. The weight sequence `d` and the weight `w`, constant on the annuli `m ≤ ‖z‖ < m+1`.
  set d : ℕ → ℝ≥0 := fun m => ((2 : ℝ≥0) ^ m)⁻¹ * (1 + (C (m + 1)).toNNReal)⁻¹ with hd_def
  have hd_pos : ∀ m, 0 < d m := by
    intro m
    simp only [hd_def]
    positivity
  have hd_key : ∀ m, (d m : ℝ≥0∞) * C (m + 1) ≤ (2 : ℝ≥0∞)⁻¹ ^ m := by
    intro m
    have hc : C (m + 1) ≠ ⊤ := (hC (m + 1)).ne
    have h2 : ((2 : ℝ≥0) ^ m : ℝ≥0) ≠ 0 := by positivity
    have h1 : (1 + (C (m + 1)).toNNReal : ℝ≥0) ≠ 0 := by positivity
    simp only [hd_def]
    rw [ENNReal.coe_mul, ENNReal.coe_inv h2, ENNReal.coe_inv h1]
    have hcoe : ((1 + (C (m + 1)).toNNReal : ℝ≥0) : ℝ≥0∞) = 1 + C (m + 1) := by
      rw [ENNReal.coe_add, ENNReal.coe_toNNReal hc, ENNReal.coe_one]
    rw [hcoe, mul_assoc]
    calc (((2 : ℝ≥0) ^ m : ℝ≥0) : ℝ≥0∞)⁻¹ * ((1 + C (m + 1))⁻¹ * C (m + 1))
        ≤ (((2 : ℝ≥0) ^ m : ℝ≥0) : ℝ≥0∞)⁻¹ * 1 := by
          gcongr
          calc (1 + C (m + 1))⁻¹ * C (m + 1)
              ≤ (1 + C (m + 1))⁻¹ * (1 + C (m + 1)) := by gcongr; exact le_add_self
            _ ≤ 1 := ENNReal.inv_mul_le_one _
      _ = (2 : ℝ≥0∞)⁻¹ ^ m := by
          rw [mul_one, ENNReal.coe_pow, ← ENNReal.inv_pow]
          norm_num
  set w : ℂ → ℝ≥0 := fun z => d ⌊‖z‖⌋₊ with hw_def
  have hfloor : Measurable fun z : ℂ => ⌊‖z‖⌋₊ := by
    apply measurable_to_countable'
    intro m
    have hpre : (fun z : ℂ => ⌊‖z‖⌋₊) ⁻¹' {m} = (fun z : ℂ => ‖z‖) ⁻¹' Set.Ico (m : ℝ) (m + 1) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ico]
      exact Nat.floor_eq_iff (norm_nonneg z)
    rw [hpre]
    exact measurable_norm measurableSet_Ico
  have hw_meas : Measurable w := by
    rw [hw_def]
    exact (Measurable.of_discrete (f := d)).comp hfloor
  have hw_pos : ∀ z, 0 < w z := fun z => hd_pos _
  have hwe_meas : Measurable fun z => (w z : ℝ≥0∞) := hw_meas.coe_nnreal_ennreal
  -- § 2. The weighted measure and the Hilbert space `L²(w · volume)`.
  set μw : Measure ℂ := volume.withDensity (fun z => (w z : ℝ≥0∞)) with hμw_def
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have : SFinite μw := by rw [hμw_def]; infer_instance
  have : MeasureTheory.IsSeparable μw := inferInstance
  have : SecondCountableTopology (Lp ℂ 2 μw) := inferInstance
  have : TopologicalSpace.SeparableSpace (Lp ℂ 2 μw) := inferInstance
  -- Lower bound for the weight on centred balls of natural radius.
  have hwlow : ∀ M : ℕ, ∃ dm : ℝ≥0, 0 < dm ∧ ∀ z : ℂ, ‖z‖ ≤ (M : ℝ) → dm ≤ w z := by
    intro M
    refine ⟨(Finset.range (M + 1)).inf' ⟨0, Finset.mem_range.mpr M.succ_pos⟩ d, ?_, ?_⟩
    · exact (Finset.lt_inf'_iff _).2 fun i _ => hd_pos i
    · intro z hz
      have hfl : ⌊‖z‖⌋₊ ≤ M := by
        calc ⌊‖z‖⌋₊ ≤ ⌊(M : ℝ)⌋₊ := Nat.floor_mono hz
          _ = M := Nat.floor_natCast M
      have hwz : w z = d ⌊‖z‖⌋₊ := by simp only [hw_def]
      rw [hwz]
      exact Finset.inf'_le d (Finset.mem_range.mpr (Nat.lt_succ_of_le hfl))
  -- The rpow/pow bookkeeping for the exponent `2`.
  have hrpow2 : ∀ x : ℝ≥0∞, x ^ ((2 : ℝ≥0∞).toReal) = x ^ (2 : ℕ) := fun x => by
    rw [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  -- § 3. Uniform weighted energy: every `hₙ n` has `w`-weighted energy at most `2`.
  have henergy : ∀ n, (∫⁻ z, ‖hₙ n z‖ₑ ^ 2 ∂μw) ≤ 2 := by
    intro n
    have hg : AEMeasurable (fun z => ‖hₙ n z‖ₑ ^ 2) volume := (hmeas n).enorm.pow_const 2
    rw [hμw_def, lintegral_withDensity_eq_lintegral_mul₀ hwe_meas.aemeasurable hg]
    -- annuli
    set A : ℕ → Set ℂ := fun m => (fun z : ℂ => ⌊‖z‖⌋₊) ⁻¹' {m} with hA_def
    have hA_meas : ∀ m, MeasurableSet (A m) := fun m =>
      hfloor (measurableSet_singleton m)
    have hA_disj : Pairwise (Function.onFun Disjoint A) := by
      intro i j hij
      rw [Function.onFun, Set.disjoint_left]
      intro z hzi hzj
      simp only [hA_def, Set.mem_preimage, Set.mem_singleton_iff] at hzi hzj
      exact hij (hzi ▸ hzj)
    have hA_union : (⋃ m, A m) = Set.univ := by
      ext z
      simp only [hA_def, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_univ, iff_true]
      exact ⟨⌊‖z‖⌋₊, rfl⟩
    have hA_ball : ∀ m, A m ⊆ Metric.closedBall 0 ((m + 1 : ℕ) : ℝ) := by
      intro m z hz
      simp only [hA_def, Set.mem_preimage, Set.mem_singleton_iff] at hz
      rw [Metric.mem_closedBall, dist_zero_right]
      have hlt := Nat.lt_floor_add_one ‖z‖
      rw [hz] at hlt
      push_cast
      linarith
    have hw_on : ∀ m, ∀ z ∈ A m, (w z : ℝ≥0∞) * ‖hₙ n z‖ₑ ^ 2
        = (d m : ℝ≥0∞) * ‖hₙ n z‖ₑ ^ 2 := by
      intro m z hz
      simp only [hA_def, Set.mem_preimage, Set.mem_singleton_iff] at hz
      have hwz : w z = d m := by simp only [hw_def]; rw [hz]
      rw [hwz]
    calc ∫⁻ z, ((fun z => (w z : ℝ≥0∞)) * fun z => ‖hₙ n z‖ₑ ^ 2) z ∂volume
        = ∫⁻ z, (w z : ℝ≥0∞) * ‖hₙ n z‖ₑ ^ 2 ∂volume := by simp only [Pi.mul_apply]
      _ = ∫⁻ z in ⋃ m, A m, (w z : ℝ≥0∞) * ‖hₙ n z‖ₑ ^ 2 ∂volume := by
          rw [hA_union, setLIntegral_univ]
      _ = ∑' m, ∫⁻ z in A m, (w z : ℝ≥0∞) * ‖hₙ n z‖ₑ ^ 2 ∂volume :=
          lintegral_iUnion hA_meas hA_disj _
      _ ≤ ∑' m, (2 : ℝ≥0∞)⁻¹ ^ m := by
          apply ENNReal.tsum_le_tsum
          intro m
          calc ∫⁻ z in A m, (w z : ℝ≥0∞) * ‖hₙ n z‖ₑ ^ 2 ∂volume
              = ∫⁻ z in A m, (d m : ℝ≥0∞) * ‖hₙ n z‖ₑ ^ 2 ∂volume :=
                setLIntegral_congr_fun (hA_meas m) (hw_on m)
            _ = (d m : ℝ≥0∞) * ∫⁻ z in A m, ‖hₙ n z‖ₑ ^ 2 ∂volume :=
                lintegral_const_mul' _ _ ENNReal.coe_ne_top
            _ ≤ (d m : ℝ≥0∞) * C (m + 1) := by
                gcongr
                exact le_trans (lintegral_mono_set (hA_ball m)) (hbound (m + 1) n)
            _ ≤ (2 : ℝ≥0∞)⁻¹ ^ m := hd_key m
      _ = 2 := by
          rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]
          simp
  -- § 4. Membership in the weighted `L²` space and the weak extraction.
  have hmemw : ∀ n, MemLp (hₙ n) 2 μw := by
    intro n
    refine ⟨(hmeas n).mono_ac (withDensity_absolutelyContinuous volume _), ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    have hle : (∫⁻ z, ‖hₙ n z‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂μw) ≤ 2 := by
      simp_rw [hrpow2]
      exact henergy n
    exact hle.trans_lt (by norm_num)
  have hbnd : ∀ n, ‖(hmemw n).toLp (hₙ n)‖ ≤ 2 := by
    intro n
    rw [Lp.norm_toLp]
    have h1 : eLpNorm (hₙ n) 2 μw ≤ 2 := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      calc (∫⁻ z, ‖hₙ n z‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂μw) ^ (1 / (2 : ℝ≥0∞).toReal)
          ≤ (2 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞).toReal) := by
            gcongr
            simp_rw [hrpow2]
            exact henergy n
        _ ≤ (2 : ℝ≥0∞) ^ (1 : ℝ) := by
            apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two
            rw [ENNReal.toReal_ofNat]
            norm_num
        _ = 2 := by simp
    calc (eLpNorm (hₙ n) 2 μw).toReal
        ≤ (2 : ℝ≥0∞).toReal :=
          (ENNReal.toReal_le_toReal (h1.trans_lt (by norm_num)).ne (by norm_num)).mpr h1
      _ = 2 := by simp
  obtain ⟨φ, xLim, hφ, hweak⟩ :=
    exists_weak_subseq_of_bounded (𝕜 := ℂ) (x := fun n => (hmemw n).toLp (hₙ n)) hbnd
  -- § 5. The limit function, its measurability, and local square-integrability.
  set u : ℂ → ℂ := ⇑xLim with hu_def
  have hac : volume ≪ μw := by
    rw [hμw_def]
    refine withDensity_absolutelyContinuous' hwe_meas.aemeasurable ?_
    exact Filter.Eventually.of_forall fun z => ENNReal.coe_ne_zero.mpr (hw_pos z).ne'
  have hu_meas : AEStronglyMeasurable u volume :=
    (Lp.aestronglyMeasurable xLim).mono_ac hac
  have hu_lint : (∫⁻ z, ‖u z‖ₑ ^ (2 : ℕ) ∂μw) < ⊤ := by
    have h := (Lp.memLp xLim).2
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at h
    simp_rw [hrpow2] at h
    exact h
  have hu_aem : AEMeasurable (fun z => ‖u z‖ₑ ^ (2 : ℕ)) volume := hu_meas.enorm.pow_const 2
  have hu_conv : (∫⁻ z, ‖u z‖ₑ ^ (2 : ℕ) ∂μw) = ∫⁻ z, (w z : ℝ≥0∞) * ‖u z‖ₑ ^ 2 ∂volume := by
    rw [hμw_def, lintegral_withDensity_eq_lintegral_mul₀ hwe_meas.aemeasurable hu_aem]
    simp only [Pi.mul_apply]
  have hu_loc : MemLpLocOn u 2 Set.univ := by
    intro K _ hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨M, hM⟩ := exists_nat_ge r
    obtain ⟨dm, hdm_pos, hdm_le⟩ := hwlow M
    refine ⟨hu_meas.restrict, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    simp_rw [hrpow2]
    have hKw : ∀ z ∈ K, dm ≤ w z := by
      intro z hz
      have hzr := hr hz
      rw [Metric.mem_closedBall, dist_zero_right] at hzr
      exact hdm_le z (hzr.trans hM)
    have hdm_ne0 : (dm : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hdm_pos.ne'
    calc ∫⁻ z, ‖u z‖ₑ ^ (2 : ℕ) ∂(volume.restrict K)
        ≤ ∫⁻ z in K, (dm : ℝ≥0∞)⁻¹ * ((w z : ℝ≥0∞) * ‖u z‖ₑ ^ 2) ∂volume := by
          apply lintegral_mono_ae
          rw [ae_restrict_iff' hK.measurableSet]
          apply Filter.Eventually.of_forall
          intro z hz
          calc ‖u z‖ₑ ^ (2 : ℕ)
              = (dm : ℝ≥0∞)⁻¹ * ((dm : ℝ≥0∞) * ‖u z‖ₑ ^ 2) := by
                rw [← mul_assoc, ENNReal.inv_mul_cancel hdm_ne0 ENNReal.coe_ne_top, one_mul]
            _ ≤ (dm : ℝ≥0∞)⁻¹ * ((w z : ℝ≥0∞) * ‖u z‖ₑ ^ 2) := by
                gcongr
                exact hKw z hz
      _ = (dm : ℝ≥0∞)⁻¹ * ∫⁻ z in K, (w z : ℝ≥0∞) * ‖u z‖ₑ ^ 2 ∂volume :=
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hdm_ne0)
      _ ≤ (dm : ℝ≥0∞)⁻¹ * ∫⁻ z, (w z : ℝ≥0∞) * ‖u z‖ₑ ^ 2 ∂volume := by
          gcongr
          exact Measure.restrict_le_self
      _ < ⊤ := by
          apply ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr hdm_pos))
          rw [← hu_conv]
          exact hu_lint
  refine ⟨φ, u, hφ, hu_meas, hu_loc, ?_⟩
  -- § 6. The pairing against a compactly supported `L²` test.
  intro ψ hψ hψc
  obtain ⟨r, hr⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨M, hM⟩ := exists_nat_ge r
  have hsupp : tsupport ψ ⊆ Metric.closedBall 0 (M : ℝ) :=
    hr.trans (Metric.closedBall_subset_closedBall hM)
  obtain ⟨dm, hdm_pos, hdm_le⟩ := hwlow M
  have hdm_ne0 : (dm : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hdm_pos.ne'
  -- The weighted test vector: `ψ` conjugated and divided by the weight.
  set y : ℂ → ℂ := fun z => (starRingEnd ℂ) (ψ z) * (((w z : ℝ) : ℂ))⁻¹ with hy_def
  have hy_meas : AEStronglyMeasurable y volume := by
    apply AEStronglyMeasurable.mul
    · exact Complex.continuous_conj.comp_aestronglyMeasurable hψ.1
    · exact ((Complex.measurable_ofReal.comp hw_meas.coe_nnreal_real).inv).aestronglyMeasurable
  have hy_mem : MemLp y 2 μw := by
    refine ⟨hy_meas.mono_ac (withDensity_absolutelyContinuous volume _), ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    simp_rw [hrpow2]
    have hy_aem : AEMeasurable (fun z => ‖y z‖ₑ ^ (2 : ℕ)) volume := hy_meas.enorm.pow_const 2
    have hconv : (∫⁻ z, ‖y z‖ₑ ^ (2 : ℕ) ∂μw) = ∫⁻ z, (w z : ℝ≥0∞) * ‖y z‖ₑ ^ 2 ∂volume := by
      rw [hμw_def, lintegral_withDensity_eq_lintegral_mul₀ hwe_meas.aemeasurable hy_aem]
      simp only [Pi.mul_apply]
    rw [hconv]
    have hpt : ∀ z, (w z : ℝ≥0∞) * ‖y z‖ₑ ^ 2 ≤ (dm : ℝ≥0∞)⁻¹ * ‖ψ z‖ₑ ^ 2 := by
      intro z
      by_cases hz : ψ z = 0
      · simp [hy_def, hz]
      · have hzsupp : z ∈ tsupport ψ :=
          subset_closure (by simpa [Function.mem_support] using hz)
        have hzM : ‖z‖ ≤ (M : ℝ) := by
          have hmem := hsupp hzsupp
          rwa [Metric.mem_closedBall, dist_zero_right] at hmem
        have hwz : dm ≤ w z := hdm_le z hzM
        have hwz0 : w z ≠ 0 := (lt_of_lt_of_le hdm_pos hwz).ne'
        have hwre : ‖((w z : ℝ) : ℂ)‖ₑ = (w z : ℝ≥0∞) := by
          rw [enorm_eq_nnnorm, Complex.nnnorm_real, NNReal.nnnorm_eq]
        have hy_enorm : ‖y z‖ₑ = ‖ψ z‖ₑ * ((w z : ℝ≥0∞))⁻¹ := by
          simp only [hy_def]
          rw [enorm_mul, RCLike.enorm_conj,
            enorm_inv (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr hwz0)), hwre]
        rw [hy_enorm]
        calc (w z : ℝ≥0∞) * (‖ψ z‖ₑ * ((w z : ℝ≥0∞))⁻¹) ^ 2
            = ‖ψ z‖ₑ ^ 2 * (((w z : ℝ≥0∞)) * (((w z : ℝ≥0∞))⁻¹) ^ 2) := by ring
          _ = ‖ψ z‖ₑ ^ 2 * ((w z : ℝ≥0∞))⁻¹ := by
              congr 1
              rw [sq, ← mul_assoc,
                ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr hwz0) ENNReal.coe_ne_top,
                one_mul]
          _ ≤ ‖ψ z‖ₑ ^ 2 * ((dm : ℝ≥0∞))⁻¹ := by gcongr
          _ = (dm : ℝ≥0∞)⁻¹ * ‖ψ z‖ₑ ^ 2 := mul_comm _ _
    calc ∫⁻ z, (w z : ℝ≥0∞) * ‖y z‖ₑ ^ 2 ∂volume
        ≤ ∫⁻ z, (dm : ℝ≥0∞)⁻¹ * ‖ψ z‖ₑ ^ 2 ∂volume := lintegral_mono hpt
      _ = (dm : ℝ≥0∞)⁻¹ * ∫⁻ z, ‖ψ z‖ₑ ^ 2 ∂volume :=
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hdm_ne0)
      _ < ⊤ := by
          apply ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr hdm_pos))
          have h := hψ.2
          rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at h
          simp_rw [hrpow2] at h
          exact h
  -- The pairing identity: against the weighted test, the weighted inner product computes
  -- the conjugate of the unweighted pairing with `ψ`.
  have hpair : ∀ (F : Lp ℂ 2 μw) (f : ℂ → ℂ), (⇑F =ᵐ[μw] f) →
      inner ℂ F (hy_mem.toLp y) = (starRingEnd ℂ) (∫ z, f z * ψ z) := by
    intro F f hFf
    have step3 : ∀ z, w z • (y z * (starRingEnd ℂ) (f z)) = (starRingEnd ℂ) (f z * ψ z) := by
      intro z
      have hwz0 : ((w z : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (hw_pos z).ne')
      have hsmul : ∀ v : ℂ, w z • v = ((w z : ℝ) : ℂ) * v := fun v => by norm_cast
      rw [hsmul, map_mul]
      simp only [hy_def]
      calc ((w z : ℝ) : ℂ) * ((starRingEnd ℂ) (ψ z) * (((w z : ℝ) : ℂ))⁻¹ * (starRingEnd ℂ) (f z))
          = (((w z : ℝ) : ℂ) * (((w z : ℝ) : ℂ))⁻¹)
              * ((starRingEnd ℂ) (f z) * (starRingEnd ℂ) (ψ z)) := by ring
        _ = (starRingEnd ℂ) (f z) * (starRingEnd ℂ) (ψ z) := by
            rw [mul_inv_cancel₀ hwz0, one_mul]
    calc inner ℂ F (hy_mem.toLp y)
        = ∫ z, inner ℂ (F z) ((hy_mem.toLp y) z) ∂μw := L2.inner_def F (hy_mem.toLp y)
      _ = ∫ z, y z * (starRingEnd ℂ) (f z) ∂μw := by
          apply integral_congr_ae
          filter_upwards [hFf, hy_mem.coeFn_toLp] with z hz1 hz2
          rw [RCLike.inner_apply, hz1, hz2]
      _ = ∫ z, w z • (y z * (starRingEnd ℂ) (f z)) := by
          rw [hμw_def]
          exact integral_withDensity_eq_integral_smul hw_meas _
      _ = ∫ z, (starRingEnd ℂ) (f z * ψ z) := by simp_rw [step3]
      _ = (starRingEnd ℂ) (∫ z, f z * ψ z) := integral_conj
  have h1 : ∀ k, inner ℂ ((hmemw (φ k)).toLp (hₙ (φ k))) (hy_mem.toLp y)
      = (starRingEnd ℂ) (∫ z, hₙ (φ k) z * ψ z) :=
    fun k => hpair _ _ ((hmemw (φ k)).coeFn_toLp)
  have h2 : inner ℂ xLim (hy_mem.toLp y) = (starRingEnd ℂ) (∫ z, u z * ψ z) :=
    hpair xLim u Filter.EventuallyEq.rfl
  have hfin := hweak (hy_mem.toLp y)
  rw [h2] at hfin
  have hfin2 : Filter.Tendsto (fun k => (starRingEnd ℂ) (∫ z, hₙ (φ k) z * ψ z)) Filter.atTop
      (nhds ((starRingEnd ℂ) (∫ z, u z * ψ z))) :=
    Filter.Tendsto.congr (fun k => h1 k) hfin
  have hfin3 := (Complex.continuous_conj.tendsto _).comp hfin2
  simp only [Function.comp_def, Complex.conj_conj] at hfin3
  exact hfin3

/-- **The fundamental lemma of the calculus of variations, inequality form.** A locally
integrable real function whose integral against every nonnegative smooth compactly
supported test is nonpositive is itself nonpositive almost everywhere. Smooth bump
approximations of ball indicators give `∫_B F ≤ 0` on every closed ball, and the
Besicovitch differentiation theorem recovers the pointwise sign at almost every
point. -/
theorem ae_nonpos_of_forall_integral_smooth_mul_nonpos {F : ℂ → ℝ}
    (hF : LocallyIntegrable F)
    (h : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ z, 0 ≤ φ z) →
      (∫ z, F z * φ z) ≤ 0) :
    ∀ᵐ z, F z ≤ 0 := by
  -- **Step 1**: the integral of `F` over every closed ball is nonpositive, by testing
  -- against smooth bumps squeezing down onto the ball indicator.
  have step1 : ∀ (x : ℂ) (r : ℝ), 0 < r → (∫ z in Metric.closedBall x r, F z) ≤ 0 := by
    intro x r hr
    -- a sequence of bumps: `1` on `closedBall x r`, supported in `ball x (r + (j+1)⁻¹)`
    obtain ⟨b, hbIn, hbOut⟩ :
        ∃ b : ℕ → ContDiffBump x,
          (∀ j, (b j).rIn = r) ∧ ∀ j, (b j).rOut = r + ((j : ℝ) + 1)⁻¹ :=
      ⟨fun j => ⟨r, r + ((j : ℝ) + 1)⁻¹, hr, lt_add_of_pos_right r (by positivity)⟩,
        fun _ => rfl, fun _ => rfl⟩
    have hkey : ∀ j : ℕ, (∫ z, F z * b j z) ≤ 0 := fun j =>
      h (b j) (b j).contDiff (b j).hasCompactSupport fun _ => (b j).nonneg
    have hzero : ∀ (j : ℕ) {z : ℂ}, z ∉ Metric.ball x (b j).rOut → b j z = 0 := fun j z hz =>
      Function.notMem_support.1 (by rw [(b j).support_eq]; exact hz)
    -- pointwise convergence of `F · bump j` to `F · 1_{closedBall x r}`
    have hlim : ∀ z : ℂ, Tendsto (fun j : ℕ => F z * b j z) atTop
        (𝓝 ((Metric.closedBall x r).indicator F z)) := by
      intro z
      by_cases hz : z ∈ Metric.closedBall x r
      · rw [Set.indicator_of_mem hz]
        have heq : ∀ j : ℕ, F z * b j z = F z := fun j => by
          rw [(b j).one_of_mem_closedBall (by rw [hbIn j]; exact hz), mul_one]
        exact tendsto_const_nhds.congr fun j => (heq j).symm
      · rw [Set.indicator_of_notMem hz]
        rw [Metric.mem_closedBall, not_le] at hz
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 hz)
        rw [one_div] at hN
        have hev : (fun j : ℕ => F z * b j z) =ᶠ[atTop] fun _ => (0 : ℝ) := by
          filter_upwards [eventually_ge_atTop N] with j hj
          have h1 : ((j : ℝ) + 1)⁻¹ ≤ ((N : ℝ) + 1)⁻¹ := by
            have hcast : ((N : ℝ) + 1) ≤ ((j : ℝ) + 1) := by
              exact_mod_cast Nat.succ_le_succ hj
            have h2 := one_div_le_one_div_of_le (by positivity) hcast
            rwa [one_div, one_div] at h2
          have hout : z ∉ Metric.ball x (b j).rOut := by
            rw [hbOut j, Metric.mem_ball, not_lt]
            linarith
          rw [hzero j hout, mul_zero]
        exact tendsto_const_nhds.congr' hev.symm
    -- measurability and an integrable dominating function
    have hmeas : ∀ j : ℕ, AEStronglyMeasurable (fun z => F z * b j z) volume := fun j =>
      hF.aestronglyMeasurable.mul (b j).continuous.aestronglyMeasurable
    have hboundInt :
        Integrable ((Metric.closedBall x (r + 1)).indicator fun z => ‖F z‖) volume :=
      MeasureTheory.IntegrableOn.integrable_indicator
        ((hF.integrableOn_isCompact (isCompact_closedBall x (r + 1))).norm)
        measurableSet_closedBall
    have hdom : ∀ j : ℕ, ∀ᵐ z, ‖F z * b j z‖ ≤
        ((Metric.closedBall x (r + 1)).indicator fun z => ‖F z‖) z := by
      intro j
      refine Eventually.of_forall fun z => ?_
      by_cases hz : z ∈ Metric.closedBall x (r + 1)
      · rw [Set.indicator_of_mem hz, norm_mul]
        have h1 : ‖b j z‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (b j).nonneg]
          exact (b j).le_one
        calc ‖F z‖ * ‖b j z‖ ≤ ‖F z‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = ‖F z‖ := mul_one _
      · rw [Set.indicator_of_notMem hz]
        have hout : z ∉ Metric.ball x (b j).rOut := by
          rw [Metric.mem_closedBall, not_le] at hz
          rw [hbOut j, Metric.mem_ball, not_lt]
          have h1 : ((j : ℝ) + 1)⁻¹ ≤ 1 :=
            inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg j))
          linarith
        rw [hzero j hout, mul_zero, norm_zero]
    -- dominated convergence and passage to the limit in the inequality
    have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
      ((Metric.closedBall x (r + 1)).indicator fun z => ‖F z‖) hmeas hboundInt hdom
      (Eventually.of_forall hlim)
    rw [MeasureTheory.integral_indicator measurableSet_closedBall] at hDCT
    exact le_of_tendsto hDCT (Eventually.of_forall hkey)
  -- **Step 2**: Lebesgue differentiation (doubling-measure density theorem) turns the
  -- ball-average sign into the pointwise sign almost everywhere.
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average (μ := (volume : Measure ℂ)) hF 1]
    with x hx
  have havg : Tendsto (fun ρ : ℝ => ⨍ y in Metric.closedBall x ρ, F y) (𝓝[>] 0)
      (𝓝 (F x)) := by
    have hmem : ∀ᶠ ρ : ℝ in 𝓝[>] 0, x ∈ Metric.closedBall x (1 * id ρ) := by
      filter_upwards [self_mem_nhdsWithin] with ρ hρ
      have hρ' : (0 : ℝ) < ρ := hρ
      exact Metric.mem_closedBall_self (by simpa using hρ'.le)
    exact hx (fun _ => x) id tendsto_id hmem
  have hev : ∀ᶠ ρ : ℝ in 𝓝[>] 0, (⨍ y in Metric.closedBall x ρ, F y) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    rw [MeasureTheory.setAverage_eq]
    exact smul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 MeasureTheory.measureReal_nonneg)
      (step1 x ρ hρ)
  exact le_of_tendsto havg hev

/-- **`W^{1,2}_loc` packaging.** A continuous function with an `L²_loc` weak gradient is
`W^{1,2}_loc`: continuity supplies the local square-integrability of the function
itself on compacta. -/
theorem memW12loc_of_continuous_weakGradient {g u v : ℂ → ℂ}
    (hg : Continuous g) (hW : HasWeakGradient u v g Set.univ)
    (hu : MemLpLocOn u 2 Set.univ) (hv : MemLpLocOn v 2 Set.univ) :
    MemW12loc g := by
  have hgL2 : MemLpLocOn g (2 : ℝ≥0∞) Set.univ := by
    intro K _ hK
    have : IsFiniteMeasure (volume.restrict K) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
    have hbound : ∀ᵐ x ∂(volume.restrict K), ‖g x‖ ≤ C := by
      rw [ae_restrict_iff' hK.measurableSet]
      exact Filter.Eventually.of_forall hC
    exact (memLp_top_of_bound hg.aestronglyMeasurable C hbound).mono_exponent le_top
  exact ⟨hgL2, u, v, hW, hu, hv⟩

/-- **Squared-norm Bochner integral from a lower-integral bound.** If the lower integral
of `‖f‖ₑ²` over `s` is at most `C < ∞` and `f` is a.e. strongly measurable on `s`, the
Bochner integral of `‖f‖²` over `s` is at most `C.toReal`. -/
theorem integral_normSq_le_of_lintegral_enormSq_le {f : ℂ → ℂ} {s : Set ℂ} {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hm : AEStronglyMeasurable f (volume.restrict s))
    (h : (∫⁻ z in s, ‖f z‖ₑ ^ 2) ≤ C) :
    (∫ z in s, ‖f z‖ ^ 2) ≤ C.toReal := by
  have hnn : 0 ≤ᵐ[volume.restrict s] fun z => ‖f z‖ ^ 2 :=
    Filter.Eventually.of_forall fun z => sq_nonneg _
  have hmeas : AEStronglyMeasurable (fun z => ‖f z‖ ^ 2) (volume.restrict s) := by
    simpa [sq] using! hm.norm.mul hm.norm
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
  have hkey : (∫⁻ z in s, ENNReal.ofReal (‖f z‖ ^ 2)) = ∫⁻ z in s, ‖f z‖ₑ ^ 2 :=
    lintegral_congr fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [hkey]
  exact ENNReal.toReal_mono hC h

end NoWanderingDomains
