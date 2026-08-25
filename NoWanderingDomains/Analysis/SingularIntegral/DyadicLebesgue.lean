/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.SingularIntegral.DyadicCubes
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Dyadic Lebesgue differentiation on `ℂ`

The dyadic averages of a locally integrable function converge almost everywhere to the
function: for almost every `z`, the average of `f` over the generation-`m` dyadic square
containing `z` tends to `f z` as `m → -∞` (the squares shrink to `z`).

This is the analytic engine behind the Calderón–Zygmund dyadic stopping decomposition
`exists_dyadic_CZ_stopping`: it is what guarantees that almost every point of a super-level
set `{f > lam}` is captured by some dyadic square on which the average of `f` exceeds `lam`.

The proof routes through Mathlib's Vitali-family Lebesgue differentiation theorem
(`VitaliFamily.ae_tendsto_average`) for the uniformly-locally-doubling Lebesgue measure on
`ℂ`: the dyadic squares containing `z` shrink to `z` with bounded eccentricity, so they are
eventually in the Vitali family's `filterAt z`, and the dyadic averages inherit the a.e.
convergence of the family averages.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- **Dyadic Lebesgue differentiation.**  For a locally integrable `f : ℂ → ℝ`, almost every
`z` is a point at which the dyadic averages converge: the average of `f` over the
generation-`m` dyadic square containing `z` tends to `f z` as the squares shrink
(`m → -∞`, i.e. along `atBot`). -/
theorem dyadic_ae_tendsto_average {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ z ∂volume,
      Tendsto (fun m : ℤ => ⨍ y in dyadicSquare m (dyadicIndexAt m z), f y ∂volume)
        atBot (𝓝 (f z)) := by
  -- STEP 1: a.e. point is a Lebesgue point for closed balls (Mathlib's doubling-measure
  -- ball Lebesgue differentiation, with non-fixed centers, along an arbitrary filter).
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
      (μ := (volume : Measure ℂ)) hf 1] with z hz
  -- The radii `δ m = 2^m * √2`, the centers all equal to `z`, `K = 1`.
  set s : ℤ → ℝ := fun m => (2 : ℝ) ^ m with hs
  set δ : ℤ → ℝ := fun m => s m * Real.sqrt 2 with hδ
  have hspos : ∀ m : ℤ, 0 < s m := fun m => zpow_pos (by norm_num) m
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hδpos : ∀ m : ℤ, 0 < δ m := fun m => mul_pos (hspos m) hsqrt2_pos
  -- The radius tends to `0⁺`.
  have hsto : Tendsto s atBot (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall (fun m => hspos m)⟩
    -- `2^m = exp (log 2 * m)`, and `log 2 * (m:ℝ) → atBot`, `exp → 0`.
    have hrw : s = fun m : ℤ => Real.exp (Real.log 2 * (m : ℝ)) := by
      funext m
      change (2 : ℝ) ^ m = Real.exp (Real.log 2 * (m : ℝ))
      rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [hrw]
    apply Real.tendsto_exp_atBot.comp
    apply Filter.Tendsto.const_mul_atBot (Real.log_pos (by norm_num))
    exact tendsto_intCast_atBot_iff.2 tendsto_id
  have hδto : Tendsto δ atBot (𝓝[>] (0 : ℝ)) := by
    rw [hδ]
    have : (0 : ℝ) = 0 * Real.sqrt 2 := by ring
    rw [tendsto_nhdsWithin_iff] at hsto ⊢
    refine ⟨?_, ?_⟩
    · have := hsto.1.mul_const (Real.sqrt 2)
      simpa using this
    · exact Eventually.of_forall (fun m => mul_pos (hspos m) hsqrt2_pos)
  -- The Lebesgue-point convergence for these closed balls.
  have hball : Tendsto
      (fun m : ℤ => ⨍ y in Metric.closedBall z (δ m), ‖f y - f z‖ ∂volume) atBot (𝓝 0) := by
    refine hz (fun _ => z) δ hδto ?_
    refine Eventually.of_forall (fun m => ?_)
    have : z ∈ Metric.closedBall z (1 * δ m) := by
      rw [one_mul]; exact Metric.mem_closedBall_self (hδpos m).le
    exact this
  -- STEP 2: the bounded-eccentricity sandwich.
  set S : ℤ → Set ℂ := fun m => dyadicSquare m (dyadicIndexAt m z) with hS
  -- `z ∈ S m`.
  have hzS : ∀ m, z ∈ S m := fun m => mem_dyadicSquare_dyadicIndexAt m z
  -- `S m ⊆ closedBall z (δ m)`.
  have hsub : ∀ m, S m ⊆ Metric.closedBall z (δ m) := by
    intro m y hy
    rw [Metric.mem_closedBall, Complex.dist_eq_re_im]
    -- both `y` and `z` lie in `S m`, so their re/im differ by at most `s m`.
    have hyz := (mem_dyadicSquare).1 hy
    have hzz := (mem_dyadicSquare).1 (hzS m)
    have hre : |y.re - z.re| ≤ s m := by
      rw [abs_sub_le_iff]
      constructor
      · nlinarith [hyz.1, hyz.2.1, hzz.1, hzz.2.1]
      · nlinarith [hyz.1, hyz.2.1, hzz.1, hzz.2.1]
    have him : |y.im - z.im| ≤ s m := by
      rw [abs_sub_le_iff]
      constructor
      · nlinarith [hyz.2.2.1, hyz.2.2.2, hzz.2.2.1, hzz.2.2.2]
      · nlinarith [hyz.2.2.1, hyz.2.2.2, hzz.2.2.1, hzz.2.2.2]
    have hre2 : (y.re - z.re) ^ 2 ≤ (s m) ^ 2 := by
      have := sq_abs (y.re - z.re)
      nlinarith [hre, abs_nonneg (y.re - z.re), this]
    have him2 : (y.im - z.im) ^ 2 ≤ (s m) ^ 2 := by
      have := sq_abs (y.im - z.im)
      nlinarith [him, abs_nonneg (y.im - z.im), this]
    have hsum : (y.re - z.re) ^ 2 + (y.im - z.im) ^ 2 ≤ (δ m) ^ 2 := by
      have : (δ m) ^ 2 = (s m) ^ 2 * 2 := by
        rw [hδ]
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      rw [this]; nlinarith [hre2, him2]
    calc Real.sqrt ((y.re - z.re) ^ 2 + (y.im - z.im) ^ 2)
        ≤ Real.sqrt ((δ m) ^ 2) := Real.sqrt_le_sqrt hsum
      _ = δ m := Real.sqrt_sq (hδpos m).le
  -- Abbreviations for the closed balls.
  set B : ℤ → Set ℂ := fun m => Metric.closedBall z (δ m) with hB
  -- Measurability and integrability data.
  have hmeasS : ∀ m, MeasurableSet (S m) := fun m => measurableSet_dyadicSquare m _
  have hcptB : ∀ m, IsCompact (B m) := fun m => isCompact_closedBall z (δ m)
  have hintB : ∀ m, IntegrableOn f (B m) volume := fun m => hf.integrableOn_isCompact (hcptB m)
  have hintS : ∀ m, IntegrableOn f (S m) volume :=
    fun m => (hintB m).mono_set (hsub m)
  -- Volumes (as reals).
  have hvolS : ∀ m, (volume (S m)).toReal = (s m) ^ 2 := by
    intro m
    rw [hS]; rw [volume_dyadicSquare]
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hvolSpos : ∀ m, (0 : ℝ) < (volume (S m)).toReal := by
    intro m; rw [hvolS]; positivity
  have hvolB : ∀ m, (volume (B m)).toReal = (s m) ^ 2 * (2 * Real.pi) := by
    intro m
    rw [hB, Complex.volume_closedBall]
    rw [ENNReal.toReal_mul, ← ENNReal.ofReal_pow (hδpos m).le,
      ENNReal.toReal_ofReal (by positivity)]
    rw [ENNReal.coe_toReal, NNReal.coe_real_pi]
    have hδsq : (δ m) ^ 2 = (s m) ^ 2 * 2 := by
      rw [hδ, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [hδsq]; ring
  -- The key per-`m` sandwich bound.
  have key : ∀ m, ‖(⨍ y in S m, f y ∂volume) - f z‖
      ≤ (2 * Real.pi) * (⨍ y in B m, ‖f y - f z‖ ∂volume) := by
    intro m
    -- Rewrite the LHS difference as the average of `f y - f z` over `S m`.
    have hSne : (volume (S m)) ≠ 0 := by
      rw [hS, volume_dyadicSquare]
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    have hStop : (volume (S m)) ≠ ⊤ := by
      rw [hS, volume_dyadicSquare]; exact ENNReal.ofReal_ne_top
    have hdiff : (⨍ y in S m, f y ∂volume) - f z = ⨍ y in S m, (f y - f z) ∂volume := by
      rw [setAverage_eq, setAverage_eq]
      rw [integral_sub (hintS m) (integrableOn_const (C := f z) hStop)]
      rw [setIntegral_const]
      rw [smul_sub]
      congr 1
      rw [measureReal_def, smul_smul, inv_mul_cancel₀ (hvolSpos m).ne', one_smul]
    rw [hdiff]
    -- `‖⨍ (f-fz)‖ ≤ ⨍ ‖f-fz‖` over `S m`, then bound by the ball average.
    have hnorm_avg : ‖⨍ y in S m, (f y - f z) ∂volume‖
        ≤ ⨍ y in S m, ‖f y - f z‖ ∂volume := by
      rw [setAverage_eq, setAverage_eq, norm_smul, measureReal_def,
        norm_inv, Real.norm_of_nonneg (hvolSpos m).le]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact norm_integral_le_integral_norm _
    refine hnorm_avg.trans ?_
    -- Now bound the `S`-average of `‖f-fz‖` by the `B`-average times `2π`.
    have hmono : ∫ y in S m, ‖f y - f z‖ ∂volume ≤ ∫ y in B m, ‖f y - f z‖ ∂volume := by
      apply setIntegral_mono_set
      · have hBtop : (volume (B m)) ≠ ⊤ := by
          rw [hB]; exact (measure_closedBall_lt_top).ne
        exact ((hintB m).sub (integrableOn_const (C := f z) hBtop)).norm
      · exact Eventually.of_forall (fun y => norm_nonneg _)
      · exact Eventually.of_forall (hsub m)
    rw [setAverage_eq, measureReal_def, setAverage_eq, measureReal_def, smul_eq_mul, smul_eq_mul]
    rw [hvolB]
    -- `(volS)⁻¹ • ∫_S ≤ (volS)⁻¹ • ∫_B`, and rearrange to `2π • (volB)⁻¹ • ∫_B`.
    have hBvolpos : (0 : ℝ) < (volume (B m)).toReal := by rw [hvolB]; positivity
    rw [hvolS] at *
    -- Goal now: (s^2)⁻¹ * ∫_S ≤ 2π * ((s^2 * 2π)⁻¹ * ∫_B)
    have hsm2 : (0 : ℝ) < (s m) ^ 2 := by positivity
    have hrhs : (2 * Real.pi) * (((s m) ^ 2 * (2 * Real.pi))⁻¹ * (∫ y in B m, ‖f y - f z‖ ∂volume))
        = ((s m) ^ 2)⁻¹ * (∫ y in B m, ‖f y - f z‖ ∂volume) := by
      rw [mul_inv]
      field_simp
    rw [hrhs]
    apply mul_le_mul_of_nonneg_left hmono (by positivity)
  -- STEP 3: squeeze.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  -- The upper bound `2π • (ball average)` tends to `0`.
  have hupper : Tendsto (fun m : ℤ => (2 * Real.pi) * (⨍ y in B m, ‖f y - f z‖ ∂volume))
      atBot (𝓝 0) := by
    have := hball.const_mul (2 * Real.pi)
    simpa [hB] using this
  refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) hupper
  have := key m
  simpa [hS] using this

/-- **Calderón–Zygmund dyadic stopping-time decomposition.**  Fix an ambient dyadic square
`Q = dyadicSquare N J` and a nonnegative locally integrable `f`.  For any height
`lam` strictly above the ambient average `⨍_Q f`, the super-level set `{f > lam}` inside `Q`
is, up to a null set, covered by a countable family of pairwise-disjoint *maximal* dyadic
subsquares `Q i = dyadicSquare (n i) (k i) ⊆ Q`, each satisfying the two-sided stopping bound
`lam < ⨍_{Q i} f ≤ 4 * lam` (the factor `4 = 2^2` is the planar parent/child area ratio).
The almost-everywhere cover is supplied by `dyadic_ae_tendsto_average`: a.e. point of the
super-level set has dyadic averages tending to its value `> lam`, hence is captured by some
dyadic square on which the average exceeds `lam`, and the maximal such square is a stopping
square.  This is the irreducible covering core of the dyadic Gehring argument. -/
theorem exists_dyadic_CZ_stopping {f : ℂ → ℝ≥0∞} (hf : AEMeasurable f volume)
    (N : ℤ) (J : ℤ × ℤ) {lam : ℝ≥0∞}
    (hlam : (⨍⁻ z in dyadicSquare N J, f z ∂volume) < lam)
    (hlamfin : lam ≠ ⊤) :
    ∃ (ι : Type) (B : Set ι) (n : ι → ℤ) (k : ι → ℤ × ℤ),
      B.Countable ∧
      (∀ i ∈ B, dyadicSquare (n i) (k i) ⊆ dyadicSquare N J) ∧
      (Pairwise (fun i j => Disjoint (dyadicSquare (n i) (k i)) (dyadicSquare (n j) (k j)))) ∧
      (volume ({z ∈ dyadicSquare N J | lam < f z} \
        ⋃ i ∈ B, dyadicSquare (n i) (k i)) = 0) ∧
      (∀ i ∈ B, lam < ⨍⁻ z in dyadicSquare (n i) (k i), f z ∂volume ∧
        (⨍⁻ z in dyadicSquare (n i) (k i), f z ∂volume) ≤ 4 * lam) := by
  classical
  set Q : Set ℂ := dyadicSquare N J with hQdef
  -- Volume facts for the ambient square `Q`.
  have hvQtop : volume Q ≠ ⊤ := by
    rw [hQdef, volume_dyadicSquare]; exact ENNReal.ofReal_ne_top
  have hvQ0 : volume Q ≠ 0 := by
    rw [hQdef, volume_dyadicSquare]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  -- The ambient integral is finite (else the average would be `⊤ ≥ lam`).
  have hQint : ∫⁻ z in Q, f z ∂volume ≠ ⊤ := by
    rw [setLAverage_eq] at hlam
    intro htop
    rw [htop, ENNReal.top_div_of_ne_top hvQtop] at hlam
    exact absurd hlam (by simp)
  -- Generic per-square volume facts.
  have hvol_netop : ∀ (m : ℤ) (j : ℤ × ℤ), volume (dyadicSquare m j) ≠ ⊤ := by
    intro m j; rw [volume_dyadicSquare]; exact ENNReal.ofReal_ne_top
  -- Index uniqueness: the index of a square containing `z` equals `dyadicIndexAt`.
  have hidx_uniq : ∀ (m : ℤ) (j : ℤ × ℤ) (z : ℂ), z ∈ dyadicSquare m j → j = dyadicIndexAt m z := by
    intro m j z hz
    by_contra hne
    have hd := dyadicSquare_pairwise_disjoint m hne
    simp only [Function.onFun] at hd
    exact absurd (mem_dyadicSquare_dyadicIndexAt m z) (Set.disjoint_left.mp hd hz)
  -- A generation-`m` square (`m < N`) containing a point of `Q` is automatically `⊆ Q`.
  have hfine_sub : ∀ (m : ℤ) (z : ℂ), z ∈ Q → m < N →
      dyadicSquare m (dyadicIndexAt m z) ⊆ Q := by
    intro m z hzQ hmN
    rcases dyadicSquare_subset_or_disjoint m (dyadicIndexAt m z) N J with h | h | h
    · exact h
    · exfalso
      have hvol : volume Q ≤ volume (dyadicSquare m (dyadicIndexAt m z)) := measure_mono h
      rw [hQdef, volume_dyadicSquare, volume_dyadicSquare] at hvol
      rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hvol
      have h2 : (2:ℝ)^m < (2:ℝ)^N := zpow_lt_zpow_right₀ (by norm_num) hmN
      nlinarith [zpow_pos (by norm_num : (0:ℝ)<2) m, zpow_pos (by norm_num : (0:ℝ)<2) N, h2]
    · exact absurd hzQ (Set.disjoint_left.mp h (mem_dyadicSquare_dyadicIndexAt m z))
  -- ============ Capture predicate and the greatest capturing generation ============
  set cap : ℤ → ℂ → Prop :=
    fun m z => m < N ∧ lam < ⨍⁻ y in dyadicSquare m (dyadicIndexAt m z), f y ∂volume with hcapdef
  set captured : ℂ → Prop := fun z => z ∈ Q ∧ ∃ m, cap m z with hcaptdef
  have hMexists : ∀ z, captured z → ∃ ub, cap ub z ∧ ∀ m, cap m z → m ≤ ub := by
    intro z hz
    apply Int.exists_greatest_of_bdd
    · exact ⟨N - 1, fun m hm => by have := hm.1; omega⟩
    · exact hz.2
  set M : ℂ → ℤ := fun z => if h : captured z then (hMexists z h).choose else 0 with hMdef
  have hMcap : ∀ z, captured z → cap (M z) z := by
    intro z h; rw [hMdef]; simp only [h, dif_pos]; exact (hMexists z h).choose_spec.1
  have hMgreatest : ∀ z, captured z → ∀ m, cap m z → m ≤ M z := by
    intro z h m hm; rw [hMdef]; simp only [h, dif_pos]; exact (hMexists z h).choose_spec.2 m hm
  -- ============ The index set ============
  set IsStop : ℤ × ℤ × ℤ → Prop :=
    fun mj => ∃ z, captured z ∧ mj = (M z, dyadicIndexAt (M z) z) with hStopdef
  refine ⟨{mj : ℤ × ℤ × ℤ // IsStop mj}, Set.univ, fun i => i.val.1, fun i => i.val.2,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- COUNTABLE
    exact Set.countable_univ
  · -- ⊆ Q : every stopping square lies in `Q` (its generation is `< N` and it shares
    -- the point `z ∈ Q`).
    rintro i -
    obtain ⟨z, hzc, hzeq⟩ := i.2
    have hcap := hMcap z hzc
    rw [hcapdef] at hcap
    have hsub : dyadicSquare (M z) (dyadicIndexAt (M z) z) ⊆ Q :=
      hfine_sub (M z) z hzc.1 hcap.1
    have heq : dyadicSquare i.val.1 i.val.2 = dyadicSquare (M z) (dyadicIndexAt (M z) z) := by
      rw [hzeq]
    rw [heq]; exact hsub
  · -- DISJOINT : distinct stopping squares are disjoint.
    -- Core: if `stop a ⊆ stop b` then the two encodings coincide.
    have core : ∀ a b : ℂ, captured a → captured b →
        dyadicSquare (M a) (dyadicIndexAt (M a) a) ⊆ dyadicSquare (M b) (dyadicIndexAt (M b) b) →
        (M a, dyadicIndexAt (M a) a) = (M b, dyadicIndexAt (M b) b) := by
      intro a b ha hb hsub
      have hzR : a ∈ dyadicSquare (M a) (dyadicIndexAt (M a) a) :=
        mem_dyadicSquare_dyadicIndexAt _ _
      have hzR' : a ∈ dyadicSquare (M b) (dyadicIndexAt (M b) b) := hsub hzR
      have hidxeq : dyadicIndexAt (M b) b = dyadicIndexAt (M b) a :=
        hidx_uniq (M b) (dyadicIndexAt (M b) b) a hzR'
      have hcapMb : cap (M b) a := by
        rw [hcapdef]
        have hMbcap := hMcap b hb; rw [hcapdef] at hMbcap
        exact ⟨hMbcap.1, by rw [← hidxeq]; exact hMbcap.2⟩
      have hle : M b ≤ M a := hMgreatest a ha (M b) hcapMb
      have hMale : M a ≤ M b := by
        by_contra hgt
        simp only [not_le] at hgt
        have hvol : volume (dyadicSquare (M a) (dyadicIndexAt (M a) a))
            ≤ volume (dyadicSquare (M b) (dyadicIndexAt (M b) b)) := measure_mono hsub
        rw [volume_dyadicSquare, volume_dyadicSquare] at hvol
        rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hvol
        have h2 : (2:ℝ)^(M b) < (2:ℝ)^(M a) := zpow_lt_zpow_right₀ (by norm_num) hgt
        nlinarith [zpow_pos (by norm_num : (0:ℝ)<2) (M b),
          zpow_pos (by norm_num : (0:ℝ)<2) (M a), h2]
      have hMeq : M a = M b := le_antisymm hMale hle
      have hidx : dyadicIndexAt (M a) a = dyadicIndexAt (M b) b := by rw [hMeq, hidxeq]
      exact Prod.ext hMeq hidx
    intro i j hij
    obtain ⟨z, hzc, hzeq⟩ := i.2
    obtain ⟨z', hz'c, hz'eq⟩ := j.2
    have heqi : dyadicSquare i.val.1 i.val.2 = dyadicSquare (M z) (dyadicIndexAt (M z) z) := by
      rw [hzeq]
    have heqj : dyadicSquare j.val.1 j.val.2 = dyadicSquare (M z') (dyadicIndexAt (M z') z') := by
      rw [hz'eq]
    rw [heqi, heqj]
    -- distinct encodings.
    have hne : (M z, dyadicIndexAt (M z) z) ≠ (M z', dyadicIndexAt (M z') z') := by
      intro hc
      apply hij
      apply Subtype.ext
      rw [hzeq, hz'eq, hc]
    rcases dyadicSquare_subset_or_disjoint (M z) (dyadicIndexAt (M z) z)
        (M z') (dyadicIndexAt (M z') z') with hsub | hsub | hdisj
    · exact absurd (core z z' hzc hz'c hsub) hne
    · exact absurd (core z' z hz'c hzc hsub).symm hne
    · exact hdisj
  · -- A.E. COVER : the uncovered part of the super-level set is null.
    -- It is contained in `{z ∈ Q | lam < f z ∧ ¬ captured z}`, which we show to be null.
    -- First: the "non-captured" null set, via dyadic Lebesgue differentiation of `g`.
    set g : ℂ → ℝ := fun z => (Q.indicator f z).toReal with hgdef
    have hms : MeasurableSet Q := by rw [hQdef]; exact measurableSet_dyadicSquare N J
    have haem : AEMeasurable (fun z => Q.indicator f z) volume := hf.indicator hms
    have hlint : ∫⁻ z, Q.indicator f z ∂volume ≠ ⊤ := by
      rw [lintegral_indicator hms]; exact hQint
    have hgloc : LocallyIntegrable g volume :=
      (integrable_toReal_of_lintegral_ne_top haem hlint).locallyIntegrable
    have hae := dyadic_ae_tendsto_average hgloc
    have hftop : volume {x | Q.indicator f x = ⊤} = 0 :=
      measure_eq_top_of_lintegral_ne_top haem hlint
    have hcomb : ∀ᵐ z ∂volume,
        Tendsto (fun m : ℤ => ⨍ y in dyadicSquare m (dyadicIndexAt m z), g y ∂volume)
          atBot (𝓝 (g z)) ∧ Q.indicator f z ≠ ⊤ := by
      refine hae.and ?_
      rw [ae_iff]; simp only [ne_eq, not_not]; exact hftop
    have hnull : volume {z | z ∈ Q ∧ lam < f z ∧ ¬ captured z} = 0 := by
      apply measure_mono_null _ (ae_iff.mp hcomb)
      intro z hz
      simp only [mem_ofPred_eq] at hz ⊢
      obtain ⟨hzQ, hflt, hncap⟩ := hz
      rintro ⟨htends, hfne⟩
      apply hncap
      have hgz : g z = (f z).toReal := by
        rw [hgdef]; simp only [Set.indicator_apply, if_pos hzQ]
      have hfzne : f z ≠ ⊤ := by
        have hQif : Q.indicator f z = f z := by simp only [Set.indicator_apply, if_pos hzQ]
        rwa [hQif] at hfne
      have hltreal : lam.toReal < g z := by
        rw [hgz]; exact (ENNReal.toReal_lt_toReal hlamfin hfzne).mpr hflt
      have hev1 : ∀ᶠ m in (atBot : Filter ℤ),
          lam.toReal < ⨍ y in dyadicSquare m (dyadicIndexAt m z), g y ∂volume :=
        htends.eventually_const_lt hltreal
      have hev2 : ∀ᶠ m in (atBot : Filter ℤ), m < N :=
        eventually_atBot.2 ⟨N - 1, fun m hm => by omega⟩
      obtain ⟨m, havg, hmN⟩ := (hev1.and hev2).exists
      refine ⟨hzQ, m, ?_⟩
      rw [hcapdef]
      refine ⟨hmN, ?_⟩
      set S : Set ℂ := dyadicSquare m (dyadicIndexAt m z) with hSdef
      have hSQ : S ⊆ Q := hfine_sub m z hzQ hmN
      have hSms : MeasurableSet S := by rw [hSdef]; exact measurableSet_dyadicSquare m _
      have hSint : ∫⁻ y in S, f y ∂volume ≠ ⊤ :=
        ne_top_of_le_ne_top hQint (lintegral_mono_set hSQ)
      have hgeqf : ∀ y ∈ S, g y = (f y).toReal := by
        intro y hy
        rw [hgdef]; simp only [Set.indicator_apply, if_pos (hSQ hy)]
      have hbridge : ⨍ y in S, g y ∂volume = (⨍⁻ y in S, f y ∂volume).toReal := by
        rw [show (⨍ y in S, g y ∂volume) = ⨍ y in S, (f y).toReal ∂volume by
          rw [setAverage_eq, setAverage_eq]; congr 1; exact setIntegral_congr_fun hSms hgeqf]
        rw [setLAverage_eq, setAverage_eq, measureReal_def, ENNReal.toReal_div, smul_eq_mul]
        rw [integral_toReal hf.restrict (ae_lt_top' hf.restrict hSint), div_eq_inv_mul]
      rw [hbridge] at havg
      by_cases hStop : (⨍⁻ y in S, f y ∂volume) = ⊤
      · rw [hStop]; exact lt_of_le_of_ne le_top hlamfin
      · exact (ENNReal.toReal_lt_toReal hlamfin hStop).mp havg
    -- Now: the uncovered super-level set ⊆ the non-captured null set.
    refine measure_mono_null ?_ hnull
    intro z hz
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq] at hz
    obtain ⟨⟨hzQ, hflt⟩, hncov⟩ := hz
    refine ⟨hzQ, hflt, ?_⟩
    intro hcapt
    -- captured z ⟹ z is in its stopping square ∈ the union, contradicting hncov.
    apply hncov
    rw [Set.mem_iUnion₂]
    have hzstop : z ∈ dyadicSquare (M z) (dyadicIndexAt (M z) z) :=
      mem_dyadicSquare_dyadicIndexAt _ _
    have hIsStop : IsStop (M z, dyadicIndexAt (M z) z) := ⟨z, hcapt, rfl⟩
    exact ⟨⟨(M z, dyadicIndexAt (M z) z), hIsStop⟩, Set.mem_univ _, hzstop⟩
  · -- TWO-SIDED BOUND
    rintro i -
    obtain ⟨z, hzc, hzeq⟩ := i.2
    have hMz := hMcap z hzc
    rw [hcapdef] at hMz
    obtain ⟨hMzN, hMzlam⟩ := hMz
    -- Identify the square with the stopping square of `z`.
    have hSeq : dyadicSquare i.val.1 i.val.2 = dyadicSquare (M z) (dyadicIndexAt (M z) z) := by
      rw [hzeq]
    rw [hSeq]
    refine ⟨hMzlam, ?_⟩
    -- Upper bound: via the parent.
    set S : Set ℂ := dyadicSquare (M z) (dyadicIndexAt (M z) z) with hSdef
    set jP : ℤ × ℤ := dyadicParent (dyadicIndexAt (M z) z) with hjP
    set P : Set ℂ := dyadicSquare (M z + 1) jP with hPdef
    have hSP : S ⊆ P := dyadicSquare_subset_parent (M z) (dyadicIndexAt (M z) z)
    have hzS : z ∈ S := mem_dyadicSquare_dyadicIndexAt (M z) z
    have hzP : z ∈ P := hSP hzS
    have hjPidx : jP = dyadicIndexAt (M z + 1) z := hidx_uniq (M z + 1) jP z hzP
    -- The parent average is `≤ lam` (since gen `M z + 1` does not capture, or it is `Q`).
    have hParentLe : (⨍⁻ z' in P, f z' ∂volume) ≤ lam := by
      rcases lt_or_eq_of_le (show M z + 1 ≤ N by omega) with hlt | heq
      · -- `M z + 1 < N`: not captured at `M z + 1`.
        have hnotcap : ¬ cap (M z + 1) z := by
          intro hc; have := hMgreatest z hzc (M z + 1) hc; omega
        rw [hcapdef] at hnotcap
        simp only [not_and, not_lt] at hnotcap
        have hle := hnotcap hlt
        rw [hPdef, hjPidx]; exact hle
      · -- `M z + 1 = N`: the parent is `Q`.
        have hPQ : P = Q := by
          have hjPJ : jP = J := by
            rw [hjPidx, heq]
            exact (hidx_uniq N J z (by rw [← hQdef]; exact hzc.1)).symm
          rw [hPdef, hjPJ, heq, hQdef]
        rw [hPQ]; exact le_of_lt hlam
    -- `vol P = 4 * vol S`.
    have hvolPS : volume P = 4 * volume S := by
      rw [hPdef, hSdef, hjP, volume_dyadicSquare, volume_dyadicSquare]
      rw [show (4:ℝ≥0∞) = ENNReal.ofReal 4 by rw [ENNReal.ofReal_ofNat]]
      rw [← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      have : (2:ℝ)^(M z + 1) = 2 * 2^(M z) := by rw [zpow_add_one₀ (by norm_num)]; ring
      rw [this]; ring
    -- `⨍⁻_S ≤ 4 * ⨍⁻_P ≤ 4 * lam`.
    have hSavg : (⨍⁻ z' in S, f z' ∂volume) ≤ 4 * (⨍⁻ z' in P, f z' ∂volume) := by
      rw [setLAverage_eq, setLAverage_eq, hvolPS]
      have hint_mono : ∫⁻ z' in S, f z' ∂volume ≤ ∫⁻ z' in P, f z' ∂volume :=
        lintegral_mono_set hSP
      calc (∫⁻ z' in S, f z' ∂volume) / volume S
          ≤ (∫⁻ z' in P, f z' ∂volume) / volume S := ENNReal.div_le_div_right hint_mono _
        _ = 4 * ((∫⁻ z' in P, f z' ∂volume) / (4 * volume S)) := by
            rw [ENNReal.div_eq_inv_mul (a := ∫⁻ z' in P, f z' ∂volume) (b := 4 * volume S)]
            rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
            rw [← mul_assoc, ← mul_assoc, mul_comm (4:ℝ≥0∞) (4:ℝ≥0∞)⁻¹]
            rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
            rw [ENNReal.div_eq_inv_mul]
    calc (⨍⁻ z' in S, f z' ∂volume) ≤ 4 * (⨍⁻ z' in P, f z' ∂volume) := hSavg
      _ ≤ 4 * lam := mul_le_mul' (le_refl 4) hParentLe

end NoWanderingDomains
