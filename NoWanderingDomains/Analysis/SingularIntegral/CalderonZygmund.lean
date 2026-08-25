/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Carleson.ToMathlib.RealInterpolation.Main

/-!
# Calderón–Zygmund `Lᵖ` bounds

The predicate `IsCalderonZygmundBound T p C` records that a singular-integral
operator `T : (ℂ → ℂ) → (ℂ → ℂ)` is bounded `Lᵖ(ℂ) → Lᵖ(ℂ)` with constant `C`:

`‖T f‖_p ≤ C · ‖f‖_p`   for every `f`.

The file's substantive content is the **Marcinkiewicz interpolation bridge**
`isCalderonZygmundBound_of_hasWeakType`: a subadditive operator that is weak-(1,1)
and weak-(2,2) is bounded on `Lᵖ` for every `1 < p < 2`. It is the abstract,
kernel-free node through which the Beurling transform's `Lᵖ` bound factors — the
Beurling-specific input (the kernel satisfies the Calderón–Zygmund hypotheses,
giving weak-(1,1) via the Carleson project's `czOperator_weak_1_1`, together with
the `L²` isometry) feeds this bridge in `Analysis/SingularIntegral/Beurling/Kernel.lean`.
The proof routes through the Carleson real-interpolation theorem
`MeasureTheory.exists_hasStrongType_real_interpolation`.

This is the qualitative form the measurable Riemann mapping theorem consumes for
the Beurling transform: a constant `C_p` for every `1 < p < ∞`, continuous in
`p`, with `C_2 = 1`, so that the Neumann series `∑ (μ T)ⁿ μ` converges in `Lᵖ`
for `‖μ‖∞ < 1` and `p` near `2`.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- A singular-integral operator `T` on `ℂ` satisfies a **Calderón–Zygmund `Lᵖ`
bound** with constant `C` if `‖T f‖_p ≤ C ‖f‖_p` for every `Lᵖ` function `f`
(the bound is asserted on `MemLp f p volume`, the class the Neumann series
consumes; an unrestricted `∀ f` would overreach to non-measurable functions). -/
def IsCalderonZygmundBound (T : (ℂ → ℂ) → ℂ → ℂ) (p : ℝ≥0∞) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ f : ℂ → ℂ, MemLp f p volume →
    eLpNorm (T f) p volume ≤ ENNReal.ofReal C * eLpNorm f p volume

/-- **Marcinkiewicz interpolation bridge.** A subadditive operator on `ℂ` that is
weak-(1,1) and weak-(2,2) is bounded on `Lᵖ(ℂ)` for every `1 < p < 2` — the
abstract Calderón–Zygmund `Lᵖ` step, obtained from the two endpoint weak-type
bounds by real interpolation (`MeasureTheory.exists_hasStrongType_real_interpolation`).
The Beurling transform feeds its kernel-derived weak-(1,1) bound and `L²` isometry
into this node; the range `p > 2` then follows by duality. -/
theorem isCalderonZygmundBound_of_hasWeakType
    {T : (ℂ → ℂ) → ℂ → ℂ} {p : ℝ≥0∞} (hp₁ : 1 < p) (hp₂ : p < 2)
    {A C₁ C₂ : ℝ≥0} (hA : 1 ≤ A) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hmeas : ∀ f : ℂ → ℂ, MemLp f p volume → AEStronglyMeasurable (T f) volume)
    (hsub : AESubadditiveOn T (fun f : ℂ → ℂ => MemLp f 1 volume ∨ MemLp f 2 volume) A volume)
    (hweak₁ : HasWeakType T 1 1 volume volume C₁)
    (hweak₂ : HasWeakType T 2 2 volume volume C₂) :
    ∃ C : ℝ, IsCalderonZygmundBound T p C := by
  -- interpolation parameter
  set t : ℝ≥0∞ := 2 * (1 - p⁻¹) with ht_def
  -- basic facts about p
  have hp0 : p ≠ 0 := by rintro rfl; exact absurd hp₁ (by simp)
  have hpinv_lt1 : p⁻¹ < 1 := by rw [ENNReal.inv_lt_one]; exact hp₁
  have hhalf_lt : (2:ℝ≥0∞)⁻¹ < p⁻¹ := by rw [ENNReal.inv_lt_inv]; exact hp₂
  have hpinv_ne_top : p⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hp0
  have h2mulinv : (2:ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  -- 1 - p⁻¹ < 2⁻¹, proved by adding p⁻¹ to both sides
  have h2 : (1:ℝ≥0∞) - p⁻¹ < 2⁻¹ := by
    have htwo_inv_ne : (2:ℝ≥0∞)⁻¹ ≠ ∞ := by simp
    have hadd : (1:ℝ≥0∞) - p⁻¹ + p⁻¹ < 2⁻¹ + p⁻¹ := by
      rw [tsub_add_cancel_of_le hpinv_lt1.le]
      calc (1:ℝ≥0∞) = 2⁻¹ + 2⁻¹ := (ENNReal.inv_two_add_inv_two).symm
        _ < 2⁻¹ + p⁻¹ := by
          rw [ENNReal.add_lt_add_iff_left htwo_inv_ne]; exact hhalf_lt
    exact lt_of_add_lt_add_right hadd
  -- ht : t ∈ Ioo 0 1
  have ht : t ∈ Ioo (0:ℝ≥0∞) 1 := by
    constructor
    · have : 0 < 1 - p⁻¹ := tsub_pos_of_lt hpinv_lt1
      rw [ht_def]; positivity
    · rw [ht_def]
      calc 2 * (1 - p⁻¹) < 2 * 2⁻¹ := by gcongr; simp
        _ = 1 := h2mulinv
  -- hp : p⁻¹ = (1 - t)/1 + t/2
  have h2pinv : (1:ℝ≥0∞) ≤ 2 * p⁻¹ := by
    calc (1:ℝ≥0∞) = 2 * 2⁻¹ := h2mulinv.symm
      _ ≤ 2 * p⁻¹ := by gcongr
  have hp : p⁻¹ = (1 - t) / 1 + t / 2 := by
    rw [ht_def, div_one]
    -- goal: p⁻¹ = (1 - 2*(1 - p⁻¹)) + (2*(1 - p⁻¹)) / 2
    have htle1 : 2 * (1 - p⁻¹) ≤ 1 := ht.2.le
    lift p⁻¹ to ℝ≥0 using hpinv_ne_top with y
    have hy1 : y ≤ 1 := by exact_mod_cast hpinv_lt1.le
    have hone_sub : (1:ℝ≥0∞) - (y : ℝ≥0∞) = ((1 - y : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_one, ← ENNReal.coe_sub]
    rw [hone_sub, show (2:ℝ≥0∞) = ((2:ℝ≥0):ℝ≥0∞) by simp, ← ENNReal.coe_mul] at htle1 ⊢
    have htle1' : 2 * (1 - y) ≤ 1 := by exact_mod_cast htle1
    rw [show (1:ℝ≥0∞) = ((1:ℝ≥0):ℝ≥0∞) by simp, ← ENNReal.coe_sub,
      ← ENNReal.coe_div (by simp), ← ENNReal.coe_add, ENNReal.coe_inj]
    rw [NNReal.eq_iff]
    push_cast [NNReal.coe_sub, NNReal.coe_div, htle1', hy1]
    ring
  -- side conditions for the interpolation endpoints
  have hp0' : (1:ℝ≥0∞) ∈ Ioc 0 1 := by constructor <;> simp
  have hp1' : (2:ℝ≥0∞) ∈ Ioc 0 2 := by constructor <;> simp
  have hq0q1 : (1:ℝ≥0∞) ≠ 2 := by norm_num
  -- apply the Carleson real-interpolation theorem
  have hST : HasStrongType T p p volume volume
      (C_realInterpolation 1 2 1 2 p C₁ C₂ A t) :=
    exists_hasStrongType_real_interpolation hp0' hp1' hq0q1 hA ht hC₁ hC₂ hp hp
      hmeas hsub hweak₁ hweak₂
  set c : ℝ≥0 := C_realInterpolation 1 2 1 2 p C₁ C₂ A t with hc_def
  refine ⟨(c : ℝ), NNReal.coe_nonneg c, fun f hf => ?_⟩
  have hbound := (hST f hf).2
  -- hbound : eLpNorm (T f) p volume ≤ ↑c * eLpNorm f p volume
  rw [show ENNReal.ofReal (c : ℝ) = (c : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal]
  exact hbound

/-! ## Abstract analysis input for the `Lᵖ` theory

A general measure-theory fact that Mathlib/Carleson do not package, used to push
the Carleson Calderón–Zygmund weak-type bounds (stated for `BoundedFiniteSupport`
test functions) up to all of `Lᵖ`. The companion `Lᵖ`–`Lᵖ'` duality lemma used
for the `p > 2` range lives in `Analysis/SingularIntegral/LpDuality.lean`. -/

/-- **Lower semicontinuity of the weak `Lᵖ` quasinorm under a.e. convergence**
(weak-type Fatou). If `wnorm (f n) p μ ≤ C` eventually and `f n → g` a.e., then
`wnorm g p μ ≤ C`. The distribution function `t ↦ μ {‖·‖ₑ > t}` is lower
semicontinuous along a.e. limits (set-Fatou), and `⨆ₜ liminfₙ ≤ liminfₙ ⨆ₜ`. -/
theorem wnorm_le_of_ae_tendsto {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {ι : Type*} {u : Filter ι} [u.NeBot] [u.IsCountablyGenerated]
    {f : ι → α → E} {g : α → E} {p : ℝ≥0∞} {C : ℝ≥0∞}
    (bound : ∀ᶠ n in u, wnorm (f n) p μ ≤ C)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (h_tendsto : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => f n x) u (𝓝 (g x))) :
    wnorm g p μ ≤ C := by
  -- The limit `g` is a.e. strongly measurable as an a.e. limit of such functions.
  have hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae u hf h_tendsto
  by_cases hptop : p = ⊤
  · -- `p = ⊤`: `wnorm · ⊤ μ = eLpNormEssSup · μ = eLpNorm · ⊤ μ`, so the strong
    -- `eLpNorm` Fatou lemma `Lp.eLpNorm_le_of_ae_tendsto` applies directly.
    subst hptop
    rw [wnorm_top, ← eLpNorm_exponent_top]
    refine MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (u := u) ?_ hf h_tendsto
    filter_upwards [bound] with n hn
    rwa [eLpNorm_exponent_top, ← wnorm_top]
  -- `p ≠ ⊤`: work with `q := p.toReal` and `wnorm' = ⨆ₜ t · (distribution)^(1/q)`.
  rw [wnorm_ne_top hptop]
  set q : ℝ := p.toReal with hq_def
  by_cases hq0 : q = 0
  · -- `q = 0` (i.e. `p = 0`): `wnorm' g 0 μ = ∞`, and `bound` forces `C = ∞`.
    rw [hq0, wnorm'_zero]
    obtain ⟨n, hn⟩ := bound.exists
    rw [wnorm_ne_top hptop, ← hq_def, hq0, wnorm'_zero] at hn
    exact hn
  have hq : 0 < q := lt_of_le_of_ne (by positivity) (Ne.symm hq0)
  -- Reduce to a sequence: pick `v : ℕ → ι` with `Tendsto v atTop u`, set `F := f ∘ v`.
  obtain ⟨v, hv⟩ := exists_seq_tendsto u
  set F : ℕ → α → E := fun k => f (v k) with hF_def
  have hFmeas : ∀ k, AEStronglyMeasurable (F k) μ := fun k => hf (v k)
  have hbound' : ∀ᶠ k in atTop, wnorm' (F k) q μ ≤ C := by
    have hcomp := hv.eventually bound
    filter_upwards [hcomp] with k hk
    rwa [wnorm_ne_top hptop] at hk
  have h_tendsto' : ∀ᵐ x ∂μ, Filter.Tendsto (fun k => F k x) atTop (𝓝 (g x)) := by
    filter_upwards [h_tendsto] with x hx
    exact hx.comp hv
  -- Lower semicontinuity of the distribution function along the sequence (set-Fatou).
  have lsc : ∀ t : ℝ≥0, distribution g (t : ℝ≥0∞) μ
      ≤ liminf (fun k => distribution (F k) (t : ℝ≥0∞) μ) atTop := by
    intro t
    -- Strongly measurable representatives, so that the level sets are genuinely measurable.
    set F' : ℕ → α → E := fun k => (hFmeas k).mk (F k) with hF'def
    set g' : α → E := hg.mk g with hg'def
    have hF'eq : ∀ k, F k =ᵐ[μ] F' k := fun k => (hFmeas k).ae_eq_mk
    have hg'eq : g =ᵐ[μ] g' := hg.ae_eq_mk
    have hF'meas : ∀ k, Measurable (fun x => ‖F' k x‖ₑ) := fun k =>
      ((hFmeas k).stronglyMeasurable_mk).enorm
    have hg'meas : Measurable (fun x => ‖g' x‖ₑ) := hg.stronglyMeasurable_mk.enorm
    -- The distribution function only sees `f` up to a.e. equality.
    have hdc : ∀ (f₁ f₂ : α → E), f₁ =ᵐ[μ] f₂ →
        distribution f₁ (t : ℝ≥0∞) μ = distribution f₂ (t : ℝ≥0∞) μ := by
      intro f₁ f₂ heq
      refine measure_congr ?_
      filter_upwards [heq] with x hx
      change ((t : ℝ≥0∞) < ‖f₁ x‖ₑ) = ((t : ℝ≥0∞) < ‖f₂ x‖ₑ)
      rw [hx]
    have hdist_eq : ∀ k, distribution (F k) (t : ℝ≥0∞) μ = distribution (F' k) (t : ℝ≥0∞) μ :=
      fun k => hdc (F k) (F' k) (hF'eq k)
    have hdist_g : distribution g (t : ℝ≥0∞) μ = distribution g' (t : ℝ≥0∞) μ := hdc g g' hg'eq
    set A : ℕ → Set α := fun k => {x | (t : ℝ≥0∞) < ‖F' k x‖ₑ} with hAdef
    have hAmeas : ∀ k, MeasurableSet (A k) := fun k =>
      measurableSet_lt measurable_const (hF'meas k)
    have hAdist : ∀ k, μ (A k) = distribution (F' k) (t : ℝ≥0∞) μ := fun k => rfl
    set Bg : Set α := {x | (t : ℝ≥0∞) < ‖g' x‖ₑ} with hBgdef
    have hBgmeas : MeasurableSet Bg := measurableSet_lt measurable_const hg'meas
    have hBgdist : distribution g' (t : ℝ≥0∞) μ = μ Bg := rfl
    -- `‖F' k x‖ₑ → ‖g' x‖ₑ` a.e.
    have h_tendsto'' : ∀ᵐ x ∂μ, Filter.Tendsto (fun k => ‖F' k x‖ₑ) atTop (𝓝 ‖g' x‖ₑ) := by
      have hall : ∀ᵐ x ∂μ, ∀ k, F k x = F' k x := by rw [ae_all_iff]; exact fun k => hF'eq k
      filter_upwards [h_tendsto', hall, hg'eq] with x hx hxall hxg
      have heq : (fun k => F k x) = (fun k => F' k x) := funext hxall
      rw [heq] at hx; rw [hxg] at hx
      exact hx.enorm
    -- Pointwise a.e. domination of indicators: membership in `Bg` ⟹ eventual membership in `A k`.
    have hpt : ∀ᵐ x ∂μ, Bg.indicator (1 : α → ℝ≥0∞) x
        ≤ liminf (fun k => (A k).indicator (1 : α → ℝ≥0∞) x) atTop := by
      filter_upwards [h_tendsto''] with x hx
      by_cases hxg : x ∈ Bg
      · rw [Set.indicator_of_mem hxg]
        refine le_liminf_of_le (by isBoundedDefault) ?_
        have hev : ∀ᶠ k in atTop, (t : ℝ≥0∞) < ‖F' k x‖ₑ :=
          Tendsto.eventually_const_lt hxg hx
        filter_upwards [hev] with k hk
        rw [Set.indicator_of_mem (show x ∈ A k from hk)]
      · rw [Set.indicator_of_notMem hxg]; exact zero_le
    calc distribution g (t : ℝ≥0∞) μ
        = μ Bg := by rw [hdist_g, hBgdist]
      _ = ∫⁻ x, Bg.indicator (1 : α → ℝ≥0∞) x ∂μ := by rw [lintegral_indicator_one hBgmeas]
      _ ≤ ∫⁻ x, liminf (fun k => (A k).indicator (1 : α → ℝ≥0∞) x) atTop ∂μ :=
          lintegral_mono_ae hpt
      _ ≤ liminf (fun k => ∫⁻ x, (A k).indicator (1 : α → ℝ≥0∞) x ∂μ) atTop :=
          lintegral_liminf_le (fun k => (measurable_const.indicator (hAmeas k)))
      _ = liminf (fun k => distribution (F' k) (t : ℝ≥0∞) μ) atTop := by
          congr 1; ext k; rw [lintegral_indicator_one (hAmeas k), hAdist k]
      _ = liminf (fun k => distribution (F k) (t : ℝ≥0∞) μ) atTop := by
          congr 1; ext k; exact (hdist_eq k).symm
  -- Push the distribution bound through `t · (·)^(1/q)` and take the supremum over `t`.
  have hmain : wnorm' g q μ ≤ liminf (fun k => wnorm' (F k) q μ) atTop := by
    set a : ℝ := q⁻¹ with ha_def
    have ha : 0 ≤ a := by positivity
    have hterm : ∀ t : ℝ≥0, (t : ℝ≥0∞) * (distribution g (t : ℝ≥0∞) μ) ^ a
        ≤ liminf (fun k => wnorm' (F k) q μ) atTop := by
      intro t
      -- `φ := t · (·)^a` is monotone and continuous on `ℝ≥0∞`, so it commutes with `liminf`.
      set φ : ℝ≥0∞ → ℝ≥0∞ := fun x => (t : ℝ≥0∞) * x ^ a with hφ_def
      have hmono : Monotone φ := fun x y hxy =>
        mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hxy ha) (zero_le)
      set D : ℕ → ℝ≥0∞ := fun k => distribution (F k) (t : ℝ≥0∞) μ with hD_def
      have hcont : ContinuousAt φ (liminf D atTop) := by
        have h2 : ContinuousAt (fun x : ℝ≥0∞ => x ^ a) (liminf D atTop) :=
          (ENNReal.continuous_rpow_const).continuousAt
        have h1 : ContinuousAt (fun y : ℝ≥0∞ => (t : ℝ≥0∞) * y) ((liminf D atTop) ^ a) :=
          ENNReal.continuousAt_const_mul (Or.inl ENNReal.coe_ne_top)
        exact ContinuousAt.comp h1 h2
      have hmap : φ (liminf D atTop) = liminf (fun k => φ (D k)) atTop :=
        hmono.map_liminf_of_continuousAt _ hcont
      have h1 : (t : ℝ≥0∞) * (distribution g (t : ℝ≥0∞) μ) ^ a ≤ φ (liminf D atTop) :=
        hmono (lsc t)
      rw [hmap] at h1
      refine h1.trans ?_
      refine liminf_le_liminf ?_
      filter_upwards with k
      change (t : ℝ≥0∞) * (distribution (F k) (t : ℝ≥0∞) μ) ^ a ≤ wnorm' (F k) q μ
      unfold wnorm'
      exact le_iSup (fun s : ℝ≥0 => (s : ℝ≥0∞) * distribution (F k) (s : ℝ≥0∞) μ ^ (q : ℝ)⁻¹) t
    unfold wnorm'
    exact iSup_le hterm
  -- Finally `liminf (wnorm' (F k) q μ) ≤ C`, from the eventual bound.
  refine hmain.trans ?_
  refine liminf_le_of_le (by isBoundedDefault) ?_
  intro b hb
  obtain ⟨k, hk⟩ := (hb.and hbound').exists
  exact hk.1.trans hk.2

end NoWanderingDomains
