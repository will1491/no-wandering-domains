/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Regularity.RingModulus
import NoWanderingDomains.QC.Regularity.RingModulusTransport
import NoWanderingDomains.QC.LengthArea.CurveConcat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# The metric-extraction engine

This file converts an *inscribed round annulus with a transported modulus bound* into an explicit
metric separation estimate, isolating the entire analytic content of the forward equicontinuity of
uniformly quasiconformal families into a single hypothesis package (`hInsc`).

The mechanism is the closed form `ringModulus z₀ r R = 2π / log (R / r)`
(`ringModulus_roundAnnulus`): an upper bound `ringModulus c rᵢ rₒ ≤ M` on the connecting modulus of
a round annulus is equivalent to `log (rₒ / rᵢ) ≥ 2π / M`, i.e. `rᵢ ≤ rₒ · exp (-2π / M)`. Once a
future modulus-transport step supplies such an inscription, the metric bound follows by pure
`log`/`exp` bookkeeping, with no further analysis.

## Main statements

* `metric_bound_of_inscribed_annulus` — from a round annulus `RoundAnnulus c rᵢ rₒ` with `ε ≤ rᵢ`
  and `ringModulus c rᵢ rₒ ≤ M`, conclude the explicit bound `ε ≤ rₒ · exp (-2π / M.toReal)`;
* `dist_image_le_of_inscribed` — the modulus-of-continuity form: an image point separated from a
  base point by an inscribed annulus of transported modulus `M` satisfies
  `dist (f z) (f w) ≤ rₒ · exp (-2π / M.toReal)`;
* `equicontinuousOn_of_uniform_isQCGeometric_of_inscription` — the forward equicontinuity of a
  family on `S` from the inscription+transport package `hInsc : InscriptionModulusData f S` alone.
-/

open MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Real

namespace NoWanderingDomains

/-- **The metric-extraction engine.** Suppose `0 < rᵢ < rₒ`, the target separation `ε` satisfies
`ε ≤ rᵢ`, and the connecting modulus of the round annulus `RoundAnnulus c rᵢ rₒ` is bounded above by
`M`, i.e. `ringModulus c rᵢ rₒ ≤ M`. Then the explicit metric bound `ε ≤ rₒ · exp (-2π / M.toReal)`
holds.

Since `ringModulus c rᵢ rₒ = 2π / log (rₒ / rᵢ)`, the hypothesis reads `2π / log (rₒ / rᵢ) ≤ M`,
hence `log (rₒ / rᵢ) ≥ 2π / M`, i.e. `rᵢ ≤ rₒ · exp (-2π / M)`; combined with `ε ≤ rᵢ` this is the
claim. When `M = ⊤` the bound degenerates to `ε ≤ rₒ` (`M.toReal = 0`, `exp 0 = 1`), which holds
because `ε ≤ rᵢ < rₒ`; the modulus bound `M = 0` is impossible since `2π / log (rₒ / rᵢ) > 0`. -/
theorem metric_bound_of_inscribed_annulus {c : ℂ} {rᵢ rₒ ε : ℝ} {M : ℝ≥0∞}
    (hri : 0 < rᵢ) (hriro : rᵢ < rₒ) (hε : ε ≤ rᵢ)
    (hmod : ringModulus c rᵢ rₒ ≤ M) :
    ε ≤ rₒ * Real.exp (-(2 * Real.pi) / M.toReal) := by
  have hro : 0 < rₒ := lt_trans hri hriro
  set L := Real.log (rₒ / rᵢ) with hL
  have hRr1 : 1 < rₒ / rᵢ := (one_lt_div hri).mpr hriro
  have hLpos : 0 < L := Real.log_pos hRr1
  have hpi : 0 < Real.pi := Real.pi_pos
  -- The connecting modulus in closed form: `2π / L`, a positive real.
  have hmodval : ringModulus c rᵢ rₒ = ENNReal.ofReal (2 * Real.pi / L) :=
    ringModulus_roundAnnulus hri hriro
  have hqpos : 0 < 2 * Real.pi / L := by positivity
  rw [hmodval] at hmod
  -- From `ofReal (2π/L) ≤ M` and positivity, `M ≠ 0`.
  have hMpos : 0 < M := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hqpos) hmod
  -- The bound reduces to `rᵢ ≤ rₒ · exp (-2π / M.toReal)`; then `ε ≤ rᵢ` closes it.
  refine le_trans hε ?_
  by_cases hMtop : M = ⊤
  · -- `M = ⊤ ⇒ M.toReal = 0 ⇒ exp 0 = 1`, and `rᵢ < rₒ`.
    rw [hMtop, ENNReal.toReal_top]
    simp only [div_zero, Real.exp_zero, mul_one]
    exact hriro.le
  · -- `M ≠ ⊤`: transfer the ENNReal inequality to the reals.
    have hMr : 0 < M.toReal := ENNReal.toReal_pos hMpos.ne' hMtop
    have hle : 2 * Real.pi / L ≤ M.toReal := by
      have := (ENNReal.ofReal_le_iff_le_toReal hMtop).mp hmod
      exact this
    -- `2π/L ≤ M.toReal ⇒ 2π/M.toReal ≤ L`.
    have hkey : 2 * Real.pi / M.toReal ≤ L := by
      rw [div_le_iff₀ hLpos] at hle
      rw [div_le_iff₀ hMr]
      nlinarith [hle, hLpos.le, hMr.le]
    -- Exponentiate: `exp (2π/M.toReal) ≤ rₒ/rᵢ`.
    have hexp : Real.exp (2 * Real.pi / M.toReal) ≤ rₒ / rᵢ := by
      calc Real.exp (2 * Real.pi / M.toReal) ≤ Real.exp L := Real.exp_le_exp.mpr hkey
        _ = rₒ / rᵢ := by rw [hL, Real.exp_log (by positivity)]
    -- Invert: `rᵢ ≤ rₒ · exp (-2π/M.toReal)`.
    rw [neg_div, Real.exp_neg]
    rw [le_mul_inv_iff₀ (Real.exp_pos _)]
    calc rᵢ * Real.exp (2 * Real.pi / M.toReal) ≤ rᵢ * (rₒ / rᵢ) :=
          mul_le_mul_of_nonneg_left hexp hri.le
      _ = rₒ := by field_simp

/-- **Modulus-of-continuity form of the extraction engine.** If the images `f z`, `f w` are
separated by a round annulus centred at `f z` — the separation is at most the inner radius,
`dist (f z) (f w) ≤ rᵢ`, and the transported connecting modulus is bounded, `ringModulus (f z) rᵢ rₒ
≤ M` — then `dist (f z) (f w) ≤ rₒ · exp (-2π / M.toReal)`.

This is the metric bound in the form the equicontinuity argument consumes: the outer radius `rₒ` is
pinned to the family's scale by the two-point normalization, while a small domain separation forces
the domain fatness (hence `M`) toward `0`, driving the right-hand side to `0`. It is a direct
instance of `metric_bound_of_inscribed_annulus` with `ε := dist (f z) (f w)` and centre `f z`. -/
theorem dist_image_le_of_inscribed {f : ℂ → ℂ} {z w : ℂ} {rᵢ rₒ : ℝ} {M : ℝ≥0∞}
    (hri : 0 < rᵢ) (hriro : rᵢ < rₒ) (hsep : dist (f z) (f w) ≤ rᵢ)
    (hmod : ringModulus (f z) rᵢ rₒ ≤ M) :
    dist (f z) (f w) ≤ rₒ * Real.exp (-(2 * Real.pi) / M.toReal) :=
  metric_bound_of_inscribed_annulus hri hriro hsep hmod

/-- The **inscription + modulus-transport package** for a family `f : ι → ℂ → ℂ` on a set `S`: the
single geometric hypothesis into which the entire analytic content of forward equicontinuity is
isolated (the `hstar` pattern).

It asserts a continuity-modulus function `ω : ℝ → ℝ` with `ω t → 0` as `t → 0⁺` and `ω ≥ 0`, such
that for every index `i`, every base point `x₀ ∈ S`, and every nearby `x ∈ S` (with `x ≠ x₀`), the
images `f i x₀`, `f i x` are separated by a round annulus centred at `f i x₀`: there are radii
`0 < rᵢ < rₒ` and a transported connecting-modulus bound `M` with
`dist (f i x₀) (f i x) ≤ rᵢ`, `ringModulus (f i x₀) rᵢ rₒ ≤ M`, and the extracted metric bound
`rₒ · exp (-2π / M.toReal) ≤ ω (dist x₀ x)`.

This is exactly the data a modulus-transport step (`IsQCGeometric`, the two-point normalization
pinning `rₒ` to the family scale, and the domain-fatness blow-up as `dist x₀ x → 0`) will supply.
Everything downstream is pure metric extraction (`dist_image_le_of_inscribed`). -/
def InscriptionModulusData {ι : Type*} (f : ι → ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∃ ω : ℝ → ℝ, Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0) ∧ (∀ t, 0 ≤ ω t) ∧
    ∀ (i : ι), ∀ x₀ ∈ S, ∀ x ∈ S, x ≠ x₀ →
      ∃ (rᵢ rₒ : ℝ) (M : ℝ≥0∞), 0 < rᵢ ∧ rᵢ < rₒ ∧
        dist (f i x₀) (f i x) ≤ rᵢ ∧ ringModulus (f i x₀) rᵢ rₒ ≤ M ∧
        rₒ * Real.exp (-(2 * Real.pi) / M.toReal) ≤ ω (dist x₀ x)

/-- **Pointwise metric bound from the inscription package.** Under `InscriptionModulusData f S`,
with its modulus function `ω`, every pair `x₀ ∈ S`, `x ∈ S` (with `x ≠ x₀`) satisfies
`dist (f i x₀) (f i x) ≤ ω (dist x₀ x)`. Immediate from `dist_image_le_of_inscribed`: the inscribed
annulus and modulus bound yield `dist (f i x₀) (f i x) ≤ rₒ · exp (-2π / M.toReal) ≤ ω (dist x₀ x)`.
-/
theorem dist_image_le_omega_of_inscription {ι : Type*} {f : ι → ℂ → ℂ} {S : Set ℂ}
    {ω : ℝ → ℝ} (hω : ∀ (i : ι), ∀ x₀ ∈ S, ∀ x ∈ S, x ≠ x₀ →
        ∃ (rᵢ rₒ : ℝ) (M : ℝ≥0∞), 0 < rᵢ ∧ rᵢ < rₒ ∧
          dist (f i x₀) (f i x) ≤ rᵢ ∧ ringModulus (f i x₀) rᵢ rₒ ≤ M ∧
          rₒ * Real.exp (-(2 * Real.pi) / M.toReal) ≤ ω (dist x₀ x))
    (i : ι) {x₀ x : ℂ} (hx₀ : x₀ ∈ S) (hx : x ∈ S) (hne : x ≠ x₀) :
    dist (f i x₀) (f i x) ≤ ω (dist x₀ x) := by
  obtain ⟨rᵢ, rₒ, M, hri, hriro, hsep, hmod, hbound⟩ := hω i x₀ hx₀ x hx hne
  exact le_trans (dist_image_le_of_inscribed hri hriro hsep hmod) hbound

/-- **Forward equicontinuity from the inscription package.** A family `f : ι → ℂ → ℂ`
carrying the inscription+transport package `hInsc : InscriptionModulusData f S` is equicontinuous
on `S`. This is the metric-extraction half of `equicontinuousOn_of_uniform_isQCGeometric`: the
entire analytic content (quasiconformal modulus transport + the two-point normalization pinning
the outer radius to the family scale) is isolated in `hInsc` — the `hstar` pattern — and nothing
else is assumed of `f` or `S`.

Given `hInsc`'s modulus function `ω` (with `ω t → 0` as `t → 0⁺`), the pointwise bound
`dist (f i x₀) (f i x) ≤ ω (dist x₀ x)` (`dist_image_le_omega_of_inscription`) is a *uniform*
continuity modulus: for each `ε > 0` choose `δ` with `ω t < ε` on `(0, δ)`; then on the ball
`dist x x₀ < δ` within `S` the images stay within `ε`, uniformly in `i`. -/
theorem equicontinuousOn_of_uniform_isQCGeometric_of_inscription {ι : Type*} {f : ι → ℂ → ℂ}
    {S : Set ℂ} (hInsc : InscriptionModulusData f S) :
    EquicontinuousOn f S := by
  obtain ⟨ω, hωlim, hωnn, hωdata⟩ := hInsc
  -- Reduce to the metric ε-δ form at each base point.
  intro x₀ hx₀ U hU
  rw [Metric.mem_uniformity_dist] at hU
  obtain ⟨ε, hε, hεU⟩ := hU
  -- `ω t → 0` as `t → 0⁺` gives a radius `δ₀` with `ω t < ε` on `(0, δ₀)`.
  have hωε : ∀ᶠ t in 𝓝[>] (0 : ℝ), ω t < ε :=
    hωlim (Iio_mem_nhds hε)
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := ((nhdsGT_basis (0 : ℝ)).eventually_iff).mp hωε
  -- On the punctured `S`-ball of radius `δ₀`, the images stay `ε`-close, uniformly in `i`.
  refine Filter.eventually_iff_exists_mem.mpr ⟨S ∩ Metric.ball x₀ δ₀, ?_, ?_⟩
  · exact inter_mem_nhdsWithin S (Metric.ball_mem_nhds x₀ hδ₀pos)
  · rintro x ⟨hxS, hxball⟩ i
    apply hεU
    by_cases hxeq : x = x₀
    · subst hxeq; simpa using hε
    · -- `dist x₀ x ∈ (0, δ₀)`, so `ω (dist x₀ x) < ε`.
      have hdpos : 0 < dist x₀ x := dist_pos.mpr (fun h => hxeq h.symm)
      have hdlt : dist x₀ x < δ₀ := by rw [dist_comm]; exact hxball
      have hωlt : ω (dist x₀ x) < ε := hδ₀ ⟨hdpos, hdlt⟩
      calc dist (f i x₀) (f i x) ≤ ω (dist x₀ x) :=
            dist_image_le_omega_of_inscription hωdata i hx₀ hxS hxeq
        _ < ε := hωlt

/-- **Free topological inscription.** For a homeomorphism `f : ℂ → ℂ` of the plane, a base point
`x₀`, an inner point `w ∈ closedBall x₀ a`, and radii `a`, `b` (no positivity or ordering of the
radii is needed), set

* `a' := sSup {r | ∃ ζ ∈ f '' closedBall x₀ a, r = dist ζ (f x₀)}` — the largest distance from
  `f x₀` attained on the image of the closed inner disk (a maximum: the image is compact, nonempty);
* `b' := infDist (f x₀) (f '' {z | b ≤ dist z x₀})` — the distance from `f x₀` to the image of the
  closed outer region.

Then:

* (i) `dist (f x₀) (f w) ≤ a'` — the image of an inner point is within `a'` of `f x₀`;
* (ii) if `a' < b'`, the round shell `RoundAnnulus (f x₀) a' b'` is inscribed in `f '' A`, where
  `A := RoundAnnulus x₀ a b`.

No Jordan curve theorem is used: the three source regions
`closedBall x₀ a`, `RoundAnnulus x₀ a b`, `{b ≤ dist · x₀}` cover the plane, `f` is a bijection, and
any `ζ` with `a' < dist ζ (f x₀) < b'` lies outside the image of the first (its distance exceeds
the maximum `a'`) and outside the image of the third (its distance is below the infimum `b'`), hence
in the image of the middle annulus. -/
theorem exists_inscribed_shell_of_homeomorph {f : ℂ → ℂ} (hf : IsHomeomorph f) {x₀ w : ℂ}
    {a b : ℝ} (hw : w ∈ Metric.closedBall x₀ a) :
    (dist (f x₀) (f w)
      ≤ sSup {r : ℝ | ∃ ζ ∈ f '' Metric.closedBall x₀ a, r = dist ζ (f x₀)}) ∧
    (sSup {r : ℝ | ∃ ζ ∈ f '' Metric.closedBall x₀ a, r = dist ζ (f x₀)}
        < Metric.infDist (f x₀) (f '' {z | b ≤ dist z x₀}) →
      RoundAnnulus (f x₀)
          (sSup {r : ℝ | ∃ ζ ∈ f '' Metric.closedBall x₀ a, r = dist ζ (f x₀)})
          (Metric.infDist (f x₀) (f '' {z | b ≤ dist z x₀}))
        ⊆ f '' RoundAnnulus x₀ a b) := by
  classical
  set S : Set ℝ := {r : ℝ | ∃ ζ ∈ f '' Metric.closedBall x₀ a, r = dist ζ (f x₀)} with hS
  set a' : ℝ := sSup S with ha'
  set b' : ℝ := Metric.infDist (f x₀) (f '' {z | b ≤ dist z x₀}) with hb'
  -- `S` is the continuous image of the compact set `f '' closedBall x₀ a`, hence bounded above.
  have hSimg : S = (fun ζ => dist ζ (f x₀)) '' (f '' Metric.closedBall x₀ a) := by
    ext r
    simp only [hS, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨ζ, hζ, rfl⟩; exact ⟨ζ, hζ, rfl⟩
    · rintro ⟨ζ, hζ, rfl⟩; exact ⟨ζ, hζ, rfl⟩
  have hKcpt : IsCompact (f '' Metric.closedBall x₀ a) :=
    (isCompact_closedBall x₀ a).image hf.continuous
  have hbdd : BddAbove S := by
    rw [hSimg]
    exact hKcpt.bddAbove_image (continuous_id.dist continuous_const).continuousOn
  -- (i) `f w` lies in the image of the closed inner disk, so its distance is `≤ a' = sSup S`.
  have hi : dist (f x₀) (f w) ≤ a' := by
    have hmem : dist (f w) (f x₀) ∈ S := ⟨f w, ⟨w, hw, rfl⟩, rfl⟩
    rw [dist_comm]
    exact le_csSup hbdd hmem
  refine ⟨hi, fun hab' ζ hζ => ?_⟩
  -- (ii) unpack `ζ ∈ RoundAnnulus (f x₀) a' b'`: `a' < dist ζ (f x₀) < b'`.
  simp only [RoundAnnulus, Set.mem_ofPred_eq] at hζ
  obtain ⟨hζlo, hζhi⟩ := hζ
  -- `f` is surjective: write `ζ = f y`.
  obtain ⟨y, rfl⟩ := hf.surjective ζ
  -- `y` cannot lie in the closed inner disk: else `dist (f y) (f x₀) ≤ a'`.
  have hy_not_inner : y ∉ Metric.closedBall x₀ a := by
    intro hyin
    have : dist (f y) (f x₀) ∈ S := ⟨f y, ⟨y, hyin, rfl⟩, rfl⟩
    exact absurd (le_csSup hbdd this) (not_le.mpr hζlo)
  -- `y` cannot lie in the closed outer region: else `b' ≤ dist (f x₀) (f y)`.
  have hy_not_outer : y ∉ {z | b ≤ dist z x₀} := by
    intro hyout
    have hle : b' ≤ dist (f x₀) (f y) :=
      Metric.infDist_le_dist_of_mem ⟨y, hyout, rfl⟩
    rw [dist_comm] at hle
    exact absurd hle (not_le.mpr hζhi)
  -- Hence `y ∈ RoundAnnulus x₀ a b`, so `f y ∈ f '' A`.
  have hyann : y ∈ RoundAnnulus x₀ a b := by
    simp only [Metric.mem_closedBall, not_le] at hy_not_inner
    simp only [Set.mem_ofPred_eq, not_le] at hy_not_outer
    exact ⟨hy_not_inner, hy_not_outer⟩
  exact ⟨y, hyann, rfl⟩

/-- **A far outer image point forces the shell to be nonempty.** With the notation of
`exists_inscribed_shell_of_homeomorph` — `a' := sSup {r | ∃ ζ ∈ f '' closedBall x₀ a,
r = dist ζ (f x₀)}` (a supremum of distances, hence `0 ≤ a'`) and
`b' := infDist (f x₀) (f '' {z | b ≤ dist z x₀})` — the inscribed shell `RoundAnnulus (f x₀) a' b'`
is nonempty as soon as `a' < b'`: the point at distance `(a' + b') / 2 ∈ (a', b')` from `f x₀` lies
in the shell. -/
theorem inscribed_shell_nonempty_of_far {c : ℂ} {a' b' : ℝ} (ha' : 0 ≤ a') (hab' : a' < b') :
    (RoundAnnulus c a' b').Nonempty := by
  -- The point at distance `(a' + b') / 2 > a'` (and `< b'`) from `c` lies in the shell.
  set t : ℝ := (a' + b') / 2 with ht
  have hlo : a' < t := by rw [ht]; linarith
  have hhi : t < b' := by rw [ht]; linarith
  have ht0 : 0 ≤ t := le_trans ha' hlo.le
  refine ⟨c + (t : ℂ), ?_⟩
  simp only [RoundAnnulus, Set.mem_ofPred_eq]
  have hdist : dist (c + (t : ℂ)) c = t := by
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  rw [hdist]
  exact ⟨hlo, hhi⟩

/-- **Frontier trapping / first hit (JCT-free).** Let `K` be a set whose topological frontier is
contained in a closed set `F` (`frontier K ⊆ F`). Consider a continuous path `γ : ℝ → ℂ` whose start
`γ 0` lies in the interior of `K` and whose end `γ 1` lies outside `K`. Then there is a first hit
time `t* ∈ (0, 1]` of `F`, i.e. `γ t* ∈ F` and, for every `t ∈ [0, t*)`, `γ t ∈ K` and `γ t ∉ F`.

The set `T := {t ∈ [0,1] | γ t ∈ F}` is a nonempty (the path must cross the frontier to leave `K`)
closed subset of `[0,1]`, so its infimum `t*` is attained and is a hit. Before `t*` the path avoids
`F`; and since the start is in the interior of `K` and never crosses `frontier K ⊆ F` before `t*`,
connectedness of `[0, t*)` keeps the path inside `K` there. -/
theorem exists_first_hit_frontier {K F : Set ℂ} (hFclosed : IsClosed F)
    (hfront : frontier K ⊆ F) {γ : ℝ → ℂ} (hγ : Continuous γ)
    (h0 : γ 0 ∈ interior K) (hstart : γ 0 ∉ F) (h1 : γ 1 ∉ K) :
    ∃ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 ∧ γ t ∈ F ∧
      (∀ u ∈ Set.Ico (0 : ℝ) t, γ u ∈ K ∧ γ u ∉ F) := by
  classical
  -- The hit set `T` of times in `[0,1]` landing in `F`.
  set T : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ γ ⁻¹' F with hT
  have hTclosed : IsClosed T := isClosed_Icc.inter (hFclosed.preimage hγ)
  -- `T` is nonempty: else `γ` maps `[0,1]` into the two disjoint opens
  -- `interior K` and `(closure K)ᶜ`, contradicting connectedness (start inside, end outside).
  have hTne : T.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hnoF : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∉ F := by
      intro t ht hmem
      rw [Set.eq_empty_iff_forall_notMem] at hempty
      exact hempty t ⟨ht, hmem⟩
    -- Every value avoids `frontier K`, hence lands in `interior K ∪ (closure K)ᶜ`.
    have hsplit : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ interior K ∨ γ t ∈ (closure K)ᶜ := by
      intro t ht
      by_cases hcl : γ t ∈ closure K
      · left
        by_contra hni
        have hfr : γ t ∈ frontier K := by rw [frontier, Set.mem_sdiff]; exact ⟨hcl, hni⟩
        exact hnoF t ht (hfront hfr)
      · right; exact hcl
    -- The two opens `interior K` and `(closure K)ᶜ` disconnect `γ '' [0,1]`.
    have hUopen : IsOpen (interior K) := isOpen_interior
    have hVopen : IsOpen ((closure K)ᶜ) := isClosed_closure.isOpen_compl
    have hpre0 : (0 : ℝ) ∈ γ ⁻¹' interior K := h0
    have hpre1 : (1 : ℝ) ∈ γ ⁻¹' (closure K)ᶜ := by
      simp only [Set.mem_preimage, Set.mem_compl_iff]
      intro hcl1
      -- if `γ 1 ∈ closure K` then, avoiding `F ⊇ frontier K`, it is in `interior K ⊆ K`.
      rcases hsplit 1 (by norm_num) with hi | hv
      · exact h1 (interior_subset hi)
      · exact hv hcl1
    -- Preimages are open, cover `[0,1]`, disjoint, both nonempty: contradiction.
    have hcover : Set.Icc (0 : ℝ) 1 ⊆ γ ⁻¹' interior K ∪ γ ⁻¹' (closure K)ᶜ := by
      intro t ht
      rcases hsplit t ht with hi | hv
      · exact Or.inl hi
      · exact Or.inr hv
    have hdisj : Disjoint (γ ⁻¹' interior K) (γ ⁻¹' (closure K)ᶜ) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      exact ht2 (subset_closure (interior_subset ht1))
    have hconn := (isPreconnected_Icc (a := (0 : ℝ)) (b := 1))
    have := hconn.subset_or_subset (hUopen.preimage hγ) (hVopen.preimage hγ) hdisj hcover
    rcases this with hsub | hsub
    · exact hpre1 (Set.mem_preimage.mp (by
        have : (1 : ℝ) ∈ γ ⁻¹' interior K := hsub (by norm_num)
        exact absurd (interior_subset this) h1))
    · exact (hsub (by norm_num : (0:ℝ) ∈ Set.Icc (0:ℝ) 1)).elim
        (by simpa using subset_closure (interior_subset (a := γ 0) h0))
  -- First-hit time `t* := sInf T`, attained since `T` is closed, nonempty, bounded below.
  have hTbdd : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  set tstar : ℝ := sInf T with htstar
  have htstarMem : tstar ∈ T := hTclosed.csInf_mem hTne hTbdd
  have htstarIcc : tstar ∈ Set.Icc (0 : ℝ) 1 := htstarMem.1
  have htstarF : γ tstar ∈ F := htstarMem.2
  -- `tstar > 0`: else `γ 0 ∈ F`, contradicting `hstart`.
  have htstarpos : 0 < tstar := by
    rcases lt_or_eq_of_le htstarIcc.1 with h | h
    · exact h
    · exact absurd (by rw [← h] at htstarF; exact htstarF) hstart
  -- Before `tstar` no `F`-hit (definition of infimum) and the path stays in `K`.
  have hbefore : ∀ u ∈ Set.Ico (0 : ℝ) tstar, γ u ∈ K ∧ γ u ∉ F := by
    intro u hu
    have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1, le_trans hu.2.le htstarIcc.2⟩
    -- `γ u ∉ F`: else `u ∈ T`, so `tstar ≤ u`, contradicting `u < tstar`.
    have hnotF : γ u ∉ F := by
      intro hmem
      exact absurd (csInf_le hTbdd ⟨huIcc, hmem⟩) (not_le.mpr hu.2)
    refine ⟨?_, hnotF⟩
    -- `γ u ∈ K`: else `γ u ∈ (closure K)ᶜ`; but `[0, u]` is connected, starts in `interior K`
    -- and never hits `frontier K ⊆ F`, so stays in `interior K ⊆ K`.
    by_contra hnotK
    have hcl : γ u ∉ interior K := fun hi => hnotK (interior_subset hi)
    -- split `[0, u]` by the two opens; start is in interior K, `u` is not.
    have hsplit2 : ∀ s ∈ Set.Icc (0 : ℝ) u, γ s ∈ interior K ∨ γ s ∈ (closure K)ᶜ := by
      intro s hs
      have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, le_trans hs.2 huIcc.2⟩
      have hsBefore : s < tstar := lt_of_le_of_lt hs.2 hu.2
      have hsnotF : γ s ∉ F := fun hmem =>
        absurd (csInf_le hTbdd ⟨hsIcc, hmem⟩) (not_le.mpr hsBefore)
      by_cases hscl : γ s ∈ closure K
      · left; by_contra hni
        exact hsnotF (hfront (by rw [frontier, Set.mem_sdiff]; exact ⟨hscl, hni⟩))
      · right; exact hscl
    have hUopen : IsOpen (interior K) := isOpen_interior
    have hVopen : IsOpen ((closure K)ᶜ) := isClosed_closure.isOpen_compl
    have hcover2 : Set.Icc (0 : ℝ) u ⊆ γ ⁻¹' interior K ∪ γ ⁻¹' (closure K)ᶜ := by
      intro s hs; rcases hsplit2 s hs with hi | hv
      · exact Or.inl hi
      · exact Or.inr hv
    have hdisj2 : Disjoint (γ ⁻¹' interior K) (γ ⁻¹' (closure K)ᶜ) := by
      rw [Set.disjoint_left]; intro s hs1 hs2
      exact hs2 (subset_closure (interior_subset hs1))
    have hconn2 := (isPreconnected_Icc (a := (0 : ℝ)) (b := u))
    have hzero : (0:ℝ) ∈ Set.Icc (0:ℝ) u := ⟨le_refl _, hu.1⟩
    have huu : u ∈ Set.Icc (0:ℝ) u := ⟨hu.1, le_refl _⟩
    rcases hconn2.subset_or_subset (hUopen.preimage hγ) (hVopen.preimage hγ) hdisj2 hcover2
      with hsub | hsub
    · -- `u ∈ γ⁻¹(interior K)`, contradicting `hcl`.
      exact hcl (hsub huu)
    · -- `0 ∈ γ⁻¹((closure K)ᶜ)`, contradicting `γ 0 ∈ interior K ⊆ closure K`.
      exact (hsub hzero) (subset_closure (interior_subset h0))
  exact ⟨tstar, ⟨htstarpos, htstarIcc.2⟩, htstarF, hbefore⟩

/-- **Interior trapping (JCT-free).** If `frontier K ⊆ F`, a continuous path `γ` starts in the
interior of `K`, and `γ` avoids `F` on all of `[0, T]`, then `γ` stays in the interior of `K` on
`[0, T]`. The path maps the connected interval `[0, T]` into the disjoint opens `interior K` and
`(closure K)ᶜ` (it never lands on `frontier K ⊆ F`), and the start is in `interior K`. -/
theorem stays_in_interior {K F : Set ℂ} (hfront : frontier K ⊆ F) {γ : ℝ → ℂ} (hγ : Continuous γ)
    (h0 : γ 0 ∈ interior K) {T : ℝ} (hT : 0 ≤ T) (hno : ∀ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ F) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, γ t ∈ interior K := by
  intro t ht
  by_contra hcl
  have hsplit : ∀ u ∈ Set.Icc (0 : ℝ) T, γ u ∈ interior K ∨ γ u ∈ (closure K)ᶜ := by
    intro u hu
    by_cases hucl : γ u ∈ closure K
    · left; by_contra hni
      exact hno u hu (hfront (by rw [frontier, Set.mem_sdiff]; exact ⟨hucl, hni⟩))
    · right; exact hucl
  have hUopen : IsOpen (interior K) := isOpen_interior
  have hVopen : IsOpen ((closure K)ᶜ) := isClosed_closure.isOpen_compl
  have hcover : Set.Icc (0 : ℝ) T ⊆ γ ⁻¹' interior K ∪ γ ⁻¹' (closure K)ᶜ := by
    intro u hu; rcases hsplit u hu with hi | hv
    · exact Or.inl hi
    · exact Or.inr hv
  have hdisj : Disjoint (γ ⁻¹' interior K) (γ ⁻¹' (closure K)ᶜ) := by
    rw [Set.disjoint_left]; intro u hu1 hu2
    exact hu2 (subset_closure (interior_subset hu1))
  have hconn := (isPreconnected_Icc (a := (0 : ℝ)) (b := T))
  rcases hconn.subset_or_subset (hUopen.preimage hγ) (hVopen.preimage hγ) hdisj hcover
    with hsub | hsub
  · exact hcl (hsub ht)
  · exact (hsub ⟨le_refl _, hT⟩) (subset_closure (interior_subset h0))

/-- **Extended-real arithmetic–geometric mean inequality** `2·A·B ≤ A² + B²`. -/
theorem two_mul_mul_le_add_sq_enn (A B : ℝ≥0∞) : 2 * (A * B) ≤ A ^ 2 + B ^ 2 := by
  rcases eq_or_ne A ⊤ with hAt | hAt
  · rw [hAt]; rcases eq_or_ne B 0 with hB0 | hB0
    · rw [hB0]; simp
    · rw [ENNReal.top_mul hB0, ENNReal.mul_top (by simp), ENNReal.top_pow (by norm_num)]; simp
  rcases eq_or_ne B ⊤ with hBt | hBt
  · rw [hBt]; rcases eq_or_ne A 0 with hA0 | hA0
    · rw [hA0]; simp
    · rw [ENNReal.mul_top hA0, ENNReal.mul_top (by simp), ENNReal.top_pow (by norm_num)]; simp
  lift A to NNReal using hAt
  lift B to NNReal using hBt
  rw [← ENNReal.coe_mul, ← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_add,
    show (2:ℝ≥0∞) = ((2:NNReal):ℝ≥0∞) from rfl, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe]
  push_cast; nlinarith [sq_nonneg ((A:ℝ) - B)]

/-- **A connected set meeting an inner ball and an outer point crosses every intermediate sphere.**
If `F ⊆ ℂ` is connected, contains a point `w₁` with `dist w₁ c ≤ r₁` and a point `w₂` with
`r₂ ≤ dist w₂ c`, then for every `ρ ∈ [r₁, r₂]` there is a point of `F` at distance exactly `ρ` from
`c`. This is the intermediate value theorem applied to the continuous function `dist · c` on the
connected set `F`. -/
theorem exists_mem_dist_eq_of_isConnected {F : Set ℂ} (hF : IsConnected F) {c w₁ w₂ : ℂ}
    (hw₁ : w₁ ∈ F) (hw₂ : w₂ ∈ F) {r₁ r₂ ρ : ℝ}
    (h₁ : dist w₁ c ≤ r₁) (h₂ : r₂ ≤ dist w₂ c) (hρ₁ : r₁ ≤ ρ) (hρ₂ : ρ ≤ r₂) :
    ∃ w ∈ F, dist w c = ρ := by
  have hcont : ContinuousOn (fun w => dist w c) F :=
    (continuous_id.dist continuous_const).continuousOn
  have hmem : ρ ∈ Set.Icc (dist w₁ c) (dist w₂ c) :=
    ⟨le_trans h₁ hρ₁, le_trans hρ₂ h₂⟩
  have himg : Set.Icc ((fun w => dist w c) w₁) ((fun w => dist w c) w₂)
      ⊆ (fun w => dist w c) '' F :=
    hF.isPreconnected.intermediate_value hw₁ hw₂ hcont
  obtain ⟨w, hwF, hwρ⟩ := himg hmem
  exact ⟨w, hwF, hwρ⟩

/-- **Arc-length of a vertical segment as a `y`-integral.** For the vertical curve
`t ↦ x + i (p + t d)` (`d > 0`), the `ρ`-arc-length line integral equals
`∫_{(p, p+d)} ρ(x + i y) dy` via the affine change of variables `y = p + t d` (Jacobian `d`). -/
private theorem arcLength_vertical_seg (ρ : ℂ → ℝ≥0∞) (x p d : ℝ) (hd : 0 < d) :
    arcLengthLineIntegral ρ (fun t => (x : ℂ) + ((p + t * d : ℝ) : ℂ) * Complex.I)
      = ∫⁻ y in Set.Ioo p (p + d), ρ ((x : ℂ) + (y : ℝ) * Complex.I) := by
  set V : ℝ → ℂ := fun t => (x : ℂ) + ((p + t * d : ℝ) : ℂ) * Complex.I with hV
  have hVderiv : ∀ t, HasDerivAt V (((d : ℝ) : ℂ) * Complex.I) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => ((p + t * d : ℝ) : ℂ) * Complex.I)
        (((d : ℝ) : ℂ) * Complex.I) t := by
      have := (((hasDerivAt_id t).mul_const d).const_add p).ofReal_comp.mul_const Complex.I
      simpa using this
    simpa [hV] using h1.const_add (x : ℂ)
  have hVnorm : ∀ t, ‖deriv V t‖ = d := by
    intro t; rw [(hVderiv t).deriv, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hd]
  set L : ℝ → ℝ := fun t => p + t * d with hLdef
  have hLimg : L '' Set.Ioo (0 : ℝ) 1 = Set.Ioo p (p + d) := by
    ext y; simp only [Set.mem_image, Set.mem_Ioo, hLdef]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨by nlinarith [ht.1, ht.2, hd], by nlinarith [ht.2, hd]⟩
    · rintro ⟨hy1, hy2⟩
      exact ⟨(y - p) / d, ⟨by rw [lt_div_iff₀ hd]; linarith,
        by rw [div_lt_one hd]; linarith⟩, by field_simp; ring⟩
  have hLderiv : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivWithinAt L d (Set.Ioo (0:ℝ) 1) t := by
    intro t _
    have : HasDerivAt L d t := by
      rw [hLdef]; simpa using (((hasDerivAt_id t).mul_const d).const_add p)
    exact this.hasDerivWithinAt
  have hLinj : Set.InjOn L (Set.Ioo (0:ℝ) 1) := by
    intro u _ v _ huv; simp only [hLdef] at huv; exact mul_right_cancel₀ hd.ne' (by linarith [huv])
  have hcov : ∫⁻ y in Set.Ioo p (p + d), ρ ((x : ℂ) + (y : ℝ) * Complex.I)
      = ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal d * ρ ((x : ℂ) + ((L t : ℝ) : ℂ) * Complex.I) := by
    rw [← hLimg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (f := L) (f' := fun _ => d) hLderiv hLinj]
    apply lintegral_congr; intro t; rw [abs_of_pos hd]
  rw [hcov]; unfold arcLengthLineIntegral
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm]
  apply lintegral_congr; intro t
  rw [show (‖deriv V t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv V t‖ from by
    rw [ofReal_norm, enorm_eq_nnnorm], hVnorm, mul_comm]

/-- **Arc-length of a circular arc as a `θ`-integral.** For the arc `t ↦ r · exp(i (φ + t Δ))`
(`0 ≤ r`, `Δ ≠ 0`) the `ρ`-arc-length line integral equals
`∫ ofReal r · ρ(r exp(iθ)) dθ` over the swept angular interval `(min φ (φ+Δ), max φ (φ+Δ))`, the
arc length element being `r dθ`. -/
private theorem arcLength_arc_seg (ρ : ℂ → ℝ≥0∞) (r φ Δ : ℝ) (hr : 0 ≤ r) (hΔ : Δ ≠ 0) :
    arcLengthLineIntegral ρ (fun t => (r : ℂ) * Complex.exp (((φ + t * Δ : ℝ)) * Complex.I))
      = ∫⁻ θ in Set.Ioo (min φ (φ + Δ)) (max φ (φ + Δ)),
          ENNReal.ofReal r * ρ ((r : ℂ) * Complex.exp (((θ : ℝ)) * Complex.I)) := by
  set A : ℝ → ℂ := fun t => (r : ℂ) * Complex.exp (((φ + t * Δ : ℝ)) * Complex.I) with hA
  have hAderiv : ∀ t, HasDerivAt A
      ((r : ℂ) * (Complex.exp (((φ + t * Δ : ℝ)) * Complex.I) * ((Δ : ℂ) * Complex.I))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => ((φ + t * Δ : ℝ) : ℂ) * Complex.I)
        ((Δ : ℂ) * Complex.I) t := by
      have := (((hasDerivAt_id t).mul_const Δ).const_add φ).ofReal_comp.mul_const Complex.I
      simpa using this
    exact ((Complex.hasDerivAt_exp _).comp t h1).const_mul (r : ℂ)
  have hAnorm : ∀ t, ‖deriv A t‖ = r * |Δ| := by
    intro t
    rw [(hAderiv t).deriv, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_exp,
      Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_nonneg hr,
      Real.norm_eq_abs]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      mul_zero, mul_one, sub_zero, Real.exp_zero, one_mul]
  set L : ℝ → ℝ := fun t => φ + t * Δ with hLdef
  have hLimg : L '' Set.Ioo (0 : ℝ) 1 = Set.Ioo (min φ (φ + Δ)) (max φ (φ + Δ)) := by
    ext y; simp only [Set.mem_image, Set.mem_Ioo, hLdef]
    rcases lt_or_gt_of_ne hΔ with hneg | hpos
    · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ⟨by nlinarith [ht.2, hneg], by nlinarith [ht.1, hneg]⟩
      · rintro ⟨hy1, hy2⟩
        exact ⟨(y - φ) / Δ, ⟨by rw [lt_div_iff_of_neg hneg]; linarith,
          by rw [div_lt_one_of_neg hneg]; linarith⟩, by field_simp; ring⟩
    · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ⟨by nlinarith [ht.1, hpos], by nlinarith [ht.2, hpos]⟩
      · rintro ⟨hy1, hy2⟩
        exact ⟨(y - φ) / Δ, ⟨by rw [lt_div_iff₀ hpos]; linarith,
          by rw [div_lt_one hpos]; linarith⟩, by field_simp; ring⟩
  have hLderiv : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivWithinAt L Δ (Set.Ioo (0:ℝ) 1) t := by
    intro t _
    have : HasDerivAt L Δ t := by
      rw [hLdef]; simpa using (((hasDerivAt_id t).mul_const Δ).const_add φ)
    exact this.hasDerivWithinAt
  have hLinj : Set.InjOn L (Set.Ioo (0:ℝ) 1) := by
    intro u _ v _ huv; simp only [hLdef] at huv; exact mul_right_cancel₀ hΔ (by linarith [huv])
  have hcov : ∫⁻ θ in Set.Ioo (min φ (φ + Δ)) (max φ (φ + Δ)),
        ENNReal.ofReal r * ρ ((r : ℂ) * Complex.exp (((θ : ℝ)) * Complex.I))
      = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |Δ| *
          (ENNReal.ofReal r * ρ ((r : ℂ) * Complex.exp (((L t : ℝ)) * Complex.I))) := by
    rw [← hLimg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (f := L) (f' := fun _ => Δ) hLderiv hLinj]
  rw [hcov]; unfold arcLengthLineIntegral
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm]
  apply lintegral_congr; intro t
  rw [show (‖deriv A t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv A t‖ from by
    rw [ofReal_norm, enorm_eq_nnnorm], hAnorm, ENNReal.ofReal_mul hr]
  change ρ ((r : ℂ) * Complex.exp (((φ + t * Δ : ℝ)) * Complex.I))
        * (ENNReal.ofReal r * ENNReal.ofReal |Δ|)
    = ENNReal.ofReal |Δ| * (ENNReal.ofReal r * ρ ((r : ℂ) * Complex.exp (((L t : ℝ)) * Complex.I)))
  rw [hLdef]; ring

/-- **Energy bound for a two-piece L-curve.** Concatenate a vertical piece `Vγ` (from `Ê` to a
common point in `U`) with an arc piece `arcT` (from that point to `F'`), both absolutely continuous
on `[0, 1]` with interiors in `U`. The concatenation joins `Ê` to `F'` inside `U`, so any density
admissible for `connectingCurveFamily Ê F' U` gives arc-length at least `1`; by additivity this
splits over the two pieces. Combined with the vertical piece's length `= IV`, the arc piece's
length `= ∫_{(a,b)} c · g` over the swept angular window `(a, b) ⊆ (lo, hi)`, and finiteness of the
scale `c`, the sub-arc energy is bounded by `c · ∫_{(lo,hi)} g`, giving
`1 ≤ IV + c · ∫_{(lo,hi)} g`. -/
private theorem lCurve_case_two_final {ρ : ℂ → ℝ≥0∞} {Ê F' U : Set ℂ} {Vγ arcT : ℝ → ℂ}
    {IV c : ℝ≥0∞} {g : ℝ → ℝ≥0∞} {a b lo hi : ℝ}
    (hρadm : ∀ γ ∈ connectingCurveFamily Ê F' U, 1 ≤ arcLengthLineIntegral ρ γ)
    (hVcont : Continuous Vγ) (hVac : AbsolutelyContinuousOnInterval Vγ 0 1)
    (hAcont : Continuous arcT) (hAac : AbsolutelyContinuousOnInterval arcT 0 1)
    (hjoin : Vγ 1 = arcT 0) (hV0 : Vγ 0 ∈ Ê) (hA1 : arcT 1 ∈ F')
    (hVint : ∀ t ∈ Set.Ioo (0 : ℝ) 1, Vγ t ∈ U) (hseam : Vγ 1 ∈ U)
    (hAint : ∀ t ∈ Set.Ioo (0 : ℝ) 1, arcT t ∈ U)
    (hVlen : arcLengthLineIntegral ρ Vγ = IV)
    (harcTlen : arcLengthLineIntegral ρ arcT = ∫⁻ θ in Set.Ioo a b, c * g θ)
    (hc : c ≠ ⊤) (hsub : Set.Ioo a b ⊆ Set.Ioo lo hi) :
    1 ≤ IV + c * ∫⁻ θ in Set.Ioo lo hi, g θ := by
  obtain ⟨cγ, hcγcont, hcγac, hcγ0, hcγ1, _, hcγopen, hcγadd⟩ :=
    exists_concat_curve hVcont hVac hAcont hAac hjoin
  have hcγmem : cγ ∈ connectingCurveFamily Ê F' U := by
    refine ⟨hcγcont, hcγac, ?_, ?_, ?_⟩
    · rw [hcγ0]; exact hV0
    · rw [hcγ1]; exact hA1
    · intro t ht
      rcases hcγopen t ht with (hV | hs) | hA
      · obtain ⟨u, hu, heq⟩ := hV; rw [← heq]; exact hVint u hu
      · rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hseam
      · obtain ⟨u, hu, heq⟩ := hA; rw [← heq]; exact hAint u hu
  have hadm : 1 ≤ arcLengthLineIntegral ρ cγ := hρadm cγ hcγmem
  rw [hcγadd ρ, hVlen, harcTlen] at hadm
  refine hadm.trans (add_le_add (le_refl IV) ?_)
  rw [lintegral_const_mul' _ _ hc]
  exact mul_le_mul' (le_refl _) (lintegral_mono_set hsub)

set_option maxHeartbeats 400000 in -- foliation argument: per-point L-curve, several changes of
-- variables and Cauchy–Schwarz estimates, elaboration exceeds the default heartbeat budget.
open Set in
/-- **The L-curve lower bound (normalized).** Let `f : ℂ → ℂ` be a homeomorphism of the plane,
`x₀` a base point, and `0 < a < b`. Write

* `Ê := f '' closedBall x₀ a` (compact, connected, contains `f x₀`),
* `F' := f '' sphere x₀ b` (compact, connected),
* `U := f '' (ball x₀ b \ closedBall x₀ a)` (open).

Assume the configuration is normalized so that `f x₀ = 0`, the image inner disk lies in
`closedBall 0 s` with the extremal distance `s` attained at the real point `(s : ℂ) ∈ Ê`, and the
image sphere has `infDist 0 F' = 1`, under the gate `s² < 1/2`. Then the connecting modulus of the
family joining `Ê` to `F'` inside `U` is bounded below:
`ENNReal.ofReal (s² / 60) ≤ curveModulus (connectingCurveFamily Ê F' U)`.

The lower bound is produced by an explicit L-curve family foliating the base segment `(0, s)`: over
each `x` a vertical segment climbs from the top slice point of `Ê` toward the unit circle, and — in
the case where `F'` reaches past radius `2` — is completed by a circular arc that must cross `F'`
(the connectedness of `F'` and the intermediate-value crossing of every intermediate sphere). The
first-hit trapping keeps each L-curve inside `U` until it lands on `F'`, so every L-curve is an
admissible connecting curve, and one-dimensional Cauchy–Schwarz plus a polar change of variables
turns the length-`≥ 1` admissibility into the energy bound. -/
theorem ofReal_le_curveModulus_lCurve {f : ℂ → ℂ} (hf : IsHomeomorph f) {x₀ : ℂ} {a b s : ℝ}
    (ha : 0 < a) (hab : a < b) (hcenter : f x₀ = 0) (hspos : 0 < s) (hs2 : s ^ 2 < 1 / 2)
    (hEsub : f '' Metric.closedBall x₀ a ⊆ Metric.closedBall (0 : ℂ) s)
    (hsE : (s : ℂ) ∈ f '' Metric.closedBall x₀ a)
    (hb : Metric.infDist (0 : ℂ) (f '' Metric.sphere x₀ b) = 1) :
    ENNReal.ofReal (s ^ 2 / 60)
      ≤ curveModulus (connectingCurveFamily (f '' Metric.closedBall x₀ a)
          (f '' Metric.sphere x₀ b) (f '' (Metric.ball x₀ b \ Metric.closedBall x₀ a))) := by
  classical
  have hbpos : 0 < b := lt_trans ha hab
  have hinj : Function.Injective f := hf.injective
  set Ê : Set ℂ := f '' Metric.closedBall x₀ a with hÊdef
  set F' : Set ℂ := f '' Metric.sphere x₀ b with hF'def
  set U : Set ℂ := f '' (Metric.ball x₀ b \ Metric.closedBall x₀ a) with hUdef
  set K : Set ℂ := f '' Metric.closedBall x₀ b with hKdef
  -- Topological skeleton.
  have hKcpt : IsCompact K := (isCompact_closedBall x₀ b).image hf.continuous
  have hballopen : IsOpen (f '' Metric.ball x₀ b) := hf.isOpenMap _ isOpen_ball
  have hballsubK : f '' Metric.ball x₀ b ⊆ K :=
    image_mono Metric.ball_subset_closedBall
  -- `f '' ball ⊆ interior K` since it is an open subset of `K`.
  have hballint : f '' Metric.ball x₀ b ⊆ interior K :=
    interior_maximal hballsubK hballopen
  -- `Ê ⊆ interior K` (closedBall a ⊆ ball b).
  have hÊint : Ê ⊆ interior K := by
    rw [hÊdef]
    exact subset_trans (image_mono (Metric.closedBall_subset_ball hab)) hballint
  -- `F' ⊆ K`.
  have hF'subK : F' ⊆ K := by
    rw [hF'def]; exact image_mono Metric.sphere_subset_closedBall
  have hF'closed : IsClosed F' := by
    rw [hF'def]; exact ((isCompact_sphere x₀ b).image hf.continuous).isClosed
  -- `frontier K ⊆ F'`: a frontier point is in `K` but not in `f '' ball`, so its preimage is on
  -- the sphere.
  have hfrontier : frontier K ⊆ F' := by
    intro w hw
    rw [frontier, Set.mem_sdiff, hKcpt.isClosed.closure_eq] at hw
    obtain ⟨hwK, hwnotint⟩ := hw
    -- `w = f y` with `y ∈ closedBall x₀ b`.
    obtain ⟨y, hyK, rfl⟩ := hwK
    -- `y ∉ ball x₀ b`: else `f y ∈ f '' ball ⊆ interior K`.
    have hynotball : y ∉ Metric.ball x₀ b := fun hyb =>
      hwnotint (hballint ⟨y, hyb, rfl⟩)
    -- So `y ∈ sphere x₀ b`.
    have hyle : dist y x₀ ≤ b := Metric.mem_closedBall.mp hyK
    have hyge : b ≤ dist y x₀ := by
      rw [Metric.mem_ball, not_lt] at hynotball; exact hynotball
    have hysphere : y ∈ Metric.sphere x₀ b := by
      rw [Metric.mem_sphere]; exact le_antisymm hyle hyge
    exact ⟨y, hysphere, rfl⟩
  -- `Ê ∩ F' = ∅` (injectivity: `closedBall a ∩ sphere b = ∅` since `a < b`).
  have hÊF'disj : Disjoint Ê F' := by
    rw [Set.disjoint_left]
    rintro w ⟨y, hyE, rfl⟩ ⟨z, hzS, hzeq⟩
    have : y = z := hinj hzeq.symm
    subst this
    rw [Metric.mem_closedBall] at hyE
    rw [Metric.mem_sphere] at hzS
    linarith [hyE, hzS.symm ▸ hab]
  -- `0 ∈ Ê` and `Ê` is compact connected.
  have h0E : (0 : ℂ) ∈ Ê := by
    rw [hÊdef, ← hcenter]; exact ⟨x₀, Metric.mem_closedBall_self ha.le, rfl⟩
  have hÊcpt : IsCompact Ê := (isCompact_closedBall x₀ a).image hf.continuous
  have hÊconn : IsConnected Ê :=
    (isConnected_closedBall (x := x₀) (r := a) ha.le).image f hf.continuous.continuousOn
  have hrankℂ : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have hF'conn : IsConnected F' :=
    (isConnected_sphere hrankℂ x₀ hbpos.le).image f hf.continuous.continuousOn
  -- `U`-membership from `K`-membership off `Ê ∪ F'` (injectivity: the three source regions
  -- partition `closedBall x₀ b`).
  have hUchar : ∀ w ∈ K, w ∉ Ê → w ∉ F' → w ∈ U := by
    rintro w ⟨y, hyK, rfl⟩ hnotE hnotF
    have hynotinner : y ∉ Metric.closedBall x₀ a := fun hyin => hnotE ⟨y, hyin, rfl⟩
    have hynotsphere : y ∉ Metric.sphere x₀ b := fun hyS => hnotF ⟨y, hyS, rfl⟩
    have hyle : dist y x₀ ≤ b := Metric.mem_closedBall.mp hyK
    have hylt : dist y x₀ < b := lt_of_le_of_ne hyle (fun heq => hynotsphere (by
      rw [Metric.mem_sphere]; exact heq))
    have hygt : a < dist y x₀ := by
      rw [Metric.mem_closedBall, not_le] at hynotinner; exact hynotinner
    exact ⟨y, ⟨Metric.mem_ball.mpr hylt, Metric.mem_closedBall.not.mpr (by
      rw [not_le]; exact hygt)⟩, rfl⟩
  -- ==== Analytic core: foliate the base segment and bound `∫ ρ²`. ====
  have hs1 : s < 1 := by nlinarith [hs2, hspos]
  unfold curveModulus
  refine le_iInf₂ ?_
  rintro ρ ⟨hρmeas, hρadm⟩
  -- Height of the unit circle over `x`.
  set c : ℝ → ℝ := fun x => Real.sqrt (1 - x ^ 2) with hc
  have hcpos : ∀ x ∈ Set.Ioo (0 : ℝ) s, 0 < c x := by
    intro x hx
    have hx2 : x ^ 2 < 1 := by nlinarith [hx.1, hx.2, hs1]
    exact Real.sqrt_pos.mpr (by linarith)
  have hcle1 : ∀ x, c x ≤ 1 := by
    intro x
    have h : (1 : ℝ) - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    calc c x = Real.sqrt (1 - x ^ 2) := rfl
      _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h
      _ = 1 := Real.sqrt_one
  have hslt : ∀ x ∈ Set.Ioo (0 : ℝ) s, s < c x := by
    intro x hx
    have hx2 : x ^ 2 < s ^ 2 := by nlinarith [hx.1, hx.2]
    have hs_sq : s ^ 2 < 1 - x ^ 2 := by nlinarith [hs2, hx2]
    have : Real.sqrt (s ^ 2) < c x := Real.sqrt_lt_sqrt (sq_nonneg s) hs_sq
    rwa [Real.sqrt_sq hspos.le] at this
  -- The embedding `x ↦ y ↦ x + i y` and the vertical slice `S x = emb x ⁻¹' Ê`.
  set emb : ℝ → ℝ → ℂ := fun x y => (x : ℂ) + (y : ℝ) * Complex.I with hemb
  have hembcont : ∀ x, Continuous (emb x) :=
    fun x => continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hembnorm : ∀ x y : ℝ, ‖emb x y‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
    intro x y; rw [hemb, Complex.norm_add_mul_I]
  set S : ℝ → Set ℝ := fun x => (emb x) ⁻¹' Ê with hS
  have hÊclosed : IsClosed Ê := hÊcpt.isClosed
  have hSsub : ∀ x, S x ⊆ Set.Icc (-s) s := by
    intro x y hy
    have hball : emb x y ∈ Metric.closedBall (0 : ℂ) s := hEsub hy
    rw [Metric.mem_closedBall, dist_zero_right, hembnorm] at hball
    have hxy : x ^ 2 + y ^ 2 ≤ s ^ 2 := by
      have h1 : Real.sqrt (x ^ 2 + y ^ 2) ^ 2 ≤ s ^ 2 := by
        apply sq_le_sq'
        · linarith [Real.sqrt_nonneg (x ^ 2 + y ^ 2), hball]
        · exact hball
      rwa [Real.sq_sqrt (by positivity : (0:ℝ) ≤ x ^ 2 + y ^ 2)] at h1
    have hy2 : y ^ 2 ≤ s ^ 2 := by nlinarith [sq_nonneg x]
    rw [Set.mem_Icc]
    constructor
    · nlinarith [hy2, hspos]
    · nlinarith [hy2, hspos]
  have hScompact : ∀ x, IsCompact (S x) := by
    intro x
    exact IsCompact.of_isClosed_subset isCompact_Icc (hÊclosed.preimage (hembcont x)) (hSsub x)
  -- `Complex.re '' Ê` covers `[0, s]`, so each slice is nonempty for `x ∈ (0, s)`.
  have hproj : Set.Icc (0 : ℝ) s ⊆ Complex.re '' Ê := by
    have hconn : IsConnected (Complex.re '' Ê) := hÊconn.image _ Complex.continuous_re.continuousOn
    refine hconn.Icc_subset ?_ ?_
    · exact ⟨0, h0E, by simp⟩
    · exact ⟨(s : ℂ), hsE, by simp⟩
  have hSne : ∀ x ∈ Set.Ioo (0 : ℝ) s, (S x).Nonempty := by
    intro x hx
    obtain ⟨w, hwE, hwre⟩ := hproj ⟨hx.1.le, hx.2.le⟩
    refine ⟨w.im, ?_⟩
    have hpt : emb x w.im = w := by rw [hemb, ← hwre]; exact Complex.re_add_im w
    rw [hS]; simp only [Set.mem_preimage, hpt]; exact hwE
  set yTop : ℝ → ℝ := fun x => sSup (S x) with hyTop
  have hyTopMem : ∀ x ∈ Set.Ioo (0 : ℝ) s, yTop x ∈ S x :=
    fun x hx => (hScompact x).sSup_mem (hSne x hx)
  have hyTople : ∀ x ∈ Set.Ioo (0 : ℝ) s, yTop x ≤ s := fun x hx =>
    (Set.mem_Icc.mp (hSsub x (hyTopMem x hx))).2
  have hyTopge : ∀ x ∈ Set.Ioo (0 : ℝ) s, -s ≤ yTop x := fun x hx =>
    (Set.mem_Icc.mp (hSsub x (hyTopMem x hx))).1
  have hSbddA : ∀ x ∈ Set.Ioo (0 : ℝ) s, BddAbove (S x) := fun x hx => (hScompact x).bddAbove
  have hnotTop : ∀ x ∈ Set.Ioo (0 : ℝ) s, ∀ y, yTop x < y → emb x y ∉ Ê := by
    intro x hx y hy hmem
    exact absurd (le_csSup (hSbddA x hx) hmem) (not_le.mpr hy)
  -- `emb x y ∈ interior K` when `emb x y ∈ Ê`; and the top slice point is off `F'`.
  have hpxint : ∀ x ∈ Set.Ioo (0 : ℝ) s, emb x (yTop x) ∈ interior K :=
    fun x hx => hÊint (hyTopMem x hx)
  have hpxnotF : ∀ x ∈ Set.Ioo (0 : ℝ) s, emb x (yTop x) ∉ F' := by
    intro x hx
    exact Set.disjoint_left.mp hÊF'disj (hyTopMem x hx)
  -- `emb x y ∉ Ê` for radius `> s` (since `Ê ⊆ closedBall 0 s`).
  have hbignotÊ : ∀ x y : ℝ, s < ‖emb x y‖ → emb x y ∉ Ê := by
    intro x y hxy hmem
    have := hEsub hmem
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  -- `emb`-image of a vertical window integral, in the arc-length form.
  -- Reusable CS window bound (mirrors the landed foliation `seg_bound`): a segment from the
  -- top slice point `emb x p` (`p := yTop x`, in `Ê`) up to `emb x q ∈ F'`, of length
  -- `q - p ≤ Lwin`, interior in `U`, forces `1 ≤ ∫_{(p,q)} ρ(emb x ·)` and hence
  -- `1 / (q - p) ≤ ∫_{(p,q)} ρ(emb x ·)²`.
  have vseg_bound : ∀ (x p q : ℝ), p < q →
      emb x p ∈ Ê → emb x q ∈ F' →
      (∀ y ∈ Set.Ioo p q, emb x y ∈ U) →
      1 ≤ ∫⁻ y in Set.Ioo p q, ρ (emb x y) := by
    intro x p q hpq hpE hqF hint
    set L : ℝ → ℝ := fun t => p + t * (q - p) with hL
    set γ : ℝ → ℂ := fun t => emb x (L t) with hγ
    have hqp : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hpq))
    have hqppos : 0 < q - p := sub_pos.mpr hpq
    have hderiv : ∀ t, HasDerivAt γ (((q - p : ℝ) : ℂ) * Complex.I) t := by
      intro t
      have h1 : HasDerivAt L (q - p) t := by
        rw [hL]; simpa using (((hasDerivAt_id t).mul_const (q - p)).const_add p)
      have h2 : HasDerivAt (fun t => ((L t : ℝ) : ℂ)) (((q - p : ℝ) : ℂ)) t := h1.ofReal_comp
      have h3 : HasDerivAt (fun t => ((L t : ℝ) : ℂ) * Complex.I)
          (((q - p : ℝ) : ℂ) * Complex.I) t := h2.mul_const Complex.I
      simpa [hγ, hemb, hL] using h3.const_add (x : ℂ)
    have hderiveq : ∀ t, deriv γ t = ((q - p : ℝ) : ℂ) * Complex.I := fun t => (hderiv t).deriv
    have hnormderiv : ∀ t, ‖deriv γ t‖ = q - p := by
      intro t; rw [hderiveq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos hqppos]
    have hlipγ : LipschitzWith (NNReal.mk (q - p) hqppos.le) γ := by
      apply LipschitzWith.of_dist_le_mul
      intro u v
      rw [dist_eq_norm, dist_eq_norm, hγ, hemb, hL]
      rw [show ((x : ℂ) + ((p + u * (q - p) : ℝ) : ℂ) * Complex.I)
          - ((x : ℂ) + ((p + v * (q - p) : ℝ) : ℂ) * Complex.I)
          = (((u - v) * (q - p) : ℝ)) * Complex.I from by push_cast; ring]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos hqppos, NNReal.coe_mk, Real.norm_eq_abs, mul_comm]
    have hcontγ : Continuous γ := hlipγ.continuous
    have hacγ : AbsolutelyContinuousOnInterval γ 0 1 :=
      (hlipγ.lipschitzOnWith (s := Set.uIcc 0 1)).absolutelyContinuousOnInterval
    have hLmem : ∀ t ∈ Set.Ioo (0 : ℝ) 1, L t ∈ Set.Ioo p q := by
      intro t ht; rw [hL]
      exact ⟨by nlinarith [ht.1, ht.2, hqppos], by nlinarith [ht.1, ht.2, hqppos]⟩
    have hmemf : γ ∈ connectingCurveFamily Ê F' U := by
      refine ⟨hcontγ, hacγ, ?_, ?_, ?_⟩
      · show γ 0 ∈ Ê
        have : γ 0 = emb x p := by rw [hγ, hL]; simp
        rw [this]; exact hpE
      · show γ 1 ∈ F'
        have : γ 1 = emb x q := by rw [hγ, hL]; simp
        rw [this]; exact hqF
      · intro t ht; exact hint (L t) (hLmem t ht)
    have hadm : 1 ≤ arcLengthLineIntegral ρ γ := hρadm γ hmemf
    have hLimg : L '' Set.Ioo (0 : ℝ) 1 = Set.Ioo p q := by
      ext y; simp only [Set.mem_image, Set.mem_Ioo]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact hLmem t ht
      · rintro ⟨hy1, hy2⟩
        exact ⟨(y - p) / (q - p), ⟨by rw [lt_div_iff₀ hqppos]; linarith,
          by rw [div_lt_one hqppos]; linarith⟩, by rw [hL]; field_simp; ring⟩
    have hLderiv : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivWithinAt L (q - p) (Set.Ioo (0:ℝ) 1) t := by
      intro t _
      have : HasDerivAt L (q - p) t := by
        rw [hL]; simpa using (((hasDerivAt_id t).mul_const (q - p)).const_add p)
      exact this.hasDerivWithinAt
    have hLinj : Set.InjOn L (Set.Ioo (0:ℝ) 1) := by
      intro u _ v _ huv
      simp only [hL] at huv; exact mul_right_cancel₀ hqp (by linarith [huv])
    have hcov : ∫⁻ y in Set.Ioo p q, ρ (emb x y)
        = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (q - p) * ρ (emb x (L t)) := by
      rw [← hLimg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
        (f := L) (f' := fun _ => q - p) hLderiv hLinj]
      apply lintegral_congr; intro t; rw [abs_of_pos hqppos]
    have harc : arcLengthLineIntegral ρ γ = ∫⁻ y in Set.Ioo p q, ρ (emb x y) := by
      rw [hcov]; unfold arcLengthLineIntegral
      rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm]
      apply lintegral_congr; intro t
      rw [show (‖deriv γ t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv γ t‖ from by
        rw [ofReal_norm, enorm_eq_nnnorm], hnormderiv, mul_comm]
    rw [← harc]; exact hadm
  -- Squared Cauchy–Schwarz on a window `(α, β)` for an `emb`-slice: `(∫ρ)² ≤ (β-α)·∫ρ²`.
  have cs_sq : ∀ (x α β : ℝ), α ≤ β →
      (∫⁻ y in Set.Ioo α β, ρ (emb x y)) ^ 2
        ≤ ENNReal.ofReal (β - α) * ∫⁻ y in Set.Ioo α β, (ρ (emb x y)) ^ 2 := by
    intro x α β hαβ
    set μ := volume.restrict (Set.Ioo α β) with hμ
    set fm : ℝ → ℝ≥0∞ := fun y => ρ (emb x y) with hfm
    set g : ℝ → ℝ≥0∞ := fun _ => 1 with hg
    have hmeasf : AEMeasurable fm μ := (hρmeas.comp (hembcont x).measurable).aemeasurable
    have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
      (Real.HolderConjugate.two_two) hmeasf (aemeasurable_const (b := (1:ℝ≥0∞)))
    have hfg : ∫⁻ y, (fm * g) y ∂μ = ∫⁻ y in Set.Ioo α β, ρ (emb x y) := by
      rw [hμ]; apply lintegral_congr; intro y; simp [hfm, hg]
    have hgsq : ∫⁻ y, g y ^ (2 : ℝ) ∂μ = ENNReal.ofReal (β - α) := by
      have : ∫⁻ y, g y ^ (2 : ℝ) ∂μ = ∫⁻ _y in Set.Ioo α β, (1 : ℝ≥0∞) := by
        rw [hμ]; apply lintegral_congr; intro y; simp [hg]
      rw [this, setLIntegral_const, Real.volume_Ioo]; simp [ENNReal.ofReal]
    have hfsq : ∫⁻ y, fm y ^ (2 : ℝ) ∂μ = ∫⁻ y in Set.Ioo α β, (ρ (emb x y)) ^ 2 := by
      rw [hμ]; apply lintegral_congr; intro y; rw [hfm, ENNReal.rpow_two, sq]
    rw [hfg, hfsq, hgsq, show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num] at hholder
    -- `∫ρ ≤ (∫ρ²)^{1/2}·(β-α)^{1/2}`, square both sides.
    have h := ENNReal.rpow_le_rpow hholder (show (0 : ℝ) ≤ 2 by norm_num)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      show (2 : ℝ)⁻¹ * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one,
      ENNReal.rpow_two] at h
    -- `h : (∫ρ)² ≤ (∫ρ²)·(β-α)`.  Reorder to match the goal.
    rw [mul_comm (ENNReal.ofReal (β - α))]
    exact h
  -- One-dimensional Cauchy–Schwarz on a bounded window `(α, β)`: `1 ≤ ∫ ρ` implies
  -- `ofReal (1/(β-α)) ≤ ∫ ρ²`.
  have cs_window : ∀ (x α β : ℝ), α < β →
      1 ≤ (∫⁻ y in Set.Ioo α β, ρ (emb x y)) →
      ENNReal.ofReal ((β - α)⁻¹) ≤ ∫⁻ y in Set.Ioo α β, (ρ (emb x y)) ^ 2 := by
    intro x α β hαβ hlow
    have hβα : 0 < β - α := sub_pos.mpr hαβ
    set μ := volume.restrict (Set.Ioo α β) with hμ
    set fm : ℝ → ℝ≥0∞ := fun y => ρ (emb x y) with hfm
    set g : ℝ → ℝ≥0∞ := fun _ => 1 with hg
    have hmeasf : AEMeasurable fm μ := (hρmeas.comp (hembcont x).measurable).aemeasurable
    have hmeasg : AEMeasurable g μ := aemeasurable_const
    have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
      (Real.HolderConjugate.two_two) hmeasf hmeasg
    have hone : 1 ≤ ∫⁻ y, (fm * g) y ∂μ := by
      have : ∫⁻ y, (fm * g) y ∂μ = ∫⁻ y in Set.Ioo α β, ρ (emb x y) := by
        rw [hμ]; apply lintegral_congr; intro y; simp [hfm, hg]
      rw [this]; exact hlow
    have hgsq : ∫⁻ y, g y ^ (2 : ℝ) ∂μ = ENNReal.ofReal (β - α) := by
      have : ∫⁻ y, g y ^ (2 : ℝ) ∂μ = ∫⁻ _y in Set.Ioo α β, (1 : ℝ≥0∞) := by
        rw [hμ]; apply lintegral_congr; intro y; simp [hg]
      rw [this, setLIntegral_const, Real.volume_Ioo]; simp [ENNReal.ofReal]
    have hfsq : ∫⁻ y, fm y ^ (2 : ℝ) ∂μ = ∫⁻ y in Set.Ioo α β, (ρ (emb x y)) ^ 2 := by
      rw [hμ]; apply lintegral_congr; intro y; rw [hfm, ENNReal.rpow_two, sq]
    rw [hfsq, hgsq, show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num] at hholder
    set A : ℝ≥0∞ := ∫⁻ y in Set.Ioo α β, (ρ (emb x y)) ^ 2 with hA
    have hle : (1 : ℝ≥0∞) ≤ A ^ (2 : ℝ)⁻¹ * (ENNReal.ofReal (β - α)) ^ (2 : ℝ)⁻¹ :=
      le_trans hone hholder
    have hAcx : (1 : ℝ≥0∞) ≤ A * ENNReal.ofReal (β - α) := by
      have h := ENNReal.rpow_le_rpow hle (show (0 : ℝ) ≤ 2 by norm_num)
      rw [ENNReal.one_rpow, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)] at h
      rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        show (2 : ℝ)⁻¹ * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one] at h
    -- From `1 ≤ A · (β-α)` deduce `ofReal ((β-α)⁻¹) ≤ A`.
    rcases eq_or_ne A ⊤ with hAtop | hAtop
    · rw [hAtop]; exact le_top
    rw [ENNReal.ofReal_inv_of_pos hβα, ENNReal.inv_le_iff_inv_le]
    -- Goal: `A⁻¹ ≤ ofReal (β - α)`.
    calc A⁻¹ ≤ (A * ENNReal.ofReal (β - α)) * A⁻¹ := by
          conv_lhs => rw [← one_mul A⁻¹]
          gcongr
      _ = ENNReal.ofReal (β - α) * (A * A⁻¹) := by ring
      _ = ENNReal.ofReal (β - α) := by
          rcases eq_or_ne A 0 with hA0 | hA0
          · rw [hA0] at hAcx; simp at hAcx
          · rw [ENNReal.mul_inv_cancel hA0 hAtop, mul_one]
  -- `K` is bounded; fix a radius `R` with `K ⊆ closedBall 0 R` and `R ≥ 3`.
  obtain ⟨R₀, hR₀⟩ := hKcpt.isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ 3 with hR
  have hKR : K ⊆ Metric.closedBall (0 : ℂ) R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hR3 : (3 : ℝ) ≤ R := le_max_right _ _
  -- Upward vertical first hit of `F'` from the top slice point.
  have up_hit : ∀ x ∈ Set.Ioo (0 : ℝ) s, ∃ H : ℝ, yTop x < H ∧ emb x H ∈ F' ∧
      (∀ y ∈ Set.Ioo (yTop x) H, emb x y ∈ U) := by
    intro x hx
    set M : ℝ := R + 1 + s with hM
    have hMpos : 0 < M := by positivity
    set γ : ℝ → ℂ := fun t => emb x (yTop x + t * M) with hγ
    have hγcont : Continuous γ := (hembcont x).comp (by fun_prop)
    have hγ0int : γ 0 ∈ interior K := by
      have : γ 0 = emb x (yTop x) := by rw [hγ]; simp
      rw [this]; exact hpxint x hx
    have hγ0notF : γ 0 ∉ F' := by
      have : γ 0 = emb x (yTop x) := by rw [hγ]; simp
      rw [this]; exact hpxnotF x hx
    have hγ1notK : γ 1 ∉ K := by
      intro hmem
      have hle : ‖γ 1‖ ≤ R := by
        have := hKR hmem; rwa [Metric.mem_closedBall, dist_zero_right] at this
      have hheight : yTop x + M ≤ ‖γ 1‖ := by
        have : γ 1 = emb x (yTop x + 1 * M) := by rw [hγ]
        rw [this, hembnorm]
        have : yTop x + 1 * M ≤ Real.sqrt (x ^ 2 + (yTop x + 1 * M) ^ 2) := by
          rw [one_mul]
          calc yTop x + M ≤ |yTop x + M| := le_abs_self _
            _ = Real.sqrt ((yTop x + M) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
            _ ≤ Real.sqrt (x ^ 2 + (yTop x + M) ^ 2) :=
                Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
        linarith [this]
      have hge : yTop x + M ≥ -s + M := by linarith [hyTopge x hx]
      have : -s + M = R + 1 := by rw [hM]; ring
      linarith [hheight, hge, hle]
    obtain ⟨t, ht, htF, htbefore⟩ :=
      exists_first_hit_frontier hF'closed hfrontier hγcont hγ0int hγ0notF hγ1notK
    refine ⟨yTop x + t * M, ?_, ?_, ?_⟩
    · have : 0 < t * M := mul_pos ht.1 hMpos; linarith
    · have : γ t = emb x (yTop x + t * M) := rfl
      rw [← this]; exact htF
    · intro y hy
      -- `y = yTop x + u * M` for `u = (y - yTop x)/M ∈ (0, t)`.
      set u : ℝ := (y - yTop x) / M with hu
      have hu0 : 0 < u := div_pos (by linarith [hy.1]) hMpos
      have hut : u < t := by
        rw [hu, div_lt_iff₀ hMpos]; nlinarith [hy.2]
      have huy : yTop x + u * M = y := by rw [hu]; field_simp; ring
      have hKF := htbefore u ⟨hu0.le, hut⟩
      have hγu : γ u = emb x y := by change emb x (yTop x + u * M) = emb x y; rw [huy]
      rw [hγu] at hKF
      refine hUchar (emb x y) hKF.1 ?_ hKF.2
      exact hnotTop x hx y hy.1
  -- Plane-energy comparison: integrating a nonnegative fibre bound over the strip
  -- `(0,s) × (α,β)` is at most the full plane energy `∫ ρ²`.
  have plane_cmp : ∀ (α β : ℝ),
      (∫⁻ x in Set.Ioo (0 : ℝ) s, ∫⁻ y in Set.Ioo α β, (ρ (emb x y)) ^ 2) ≤ ∫⁻ z, (ρ z) ^ 2 := by
    intro α β
    have hcontseg2 : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℝ) * Complex.I) :=
      (Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
    have hmeas2 : Measurable
        (fun p : ℝ × ℝ => (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2) :=
      (hρmeas.comp hcontseg2.measurable).pow_const 2
    have hmono1 : (∫⁻ x in Set.Ioo (0 : ℝ) s, ∫⁻ y in Set.Ioo α β, (ρ (emb x y)) ^ 2)
        ≤ ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2 := by
      refine lintegral_mono' Measure.restrict_le_self (fun x => ?_)
      calc (∫⁻ y in Set.Ioo α β, (ρ (emb x y)) ^ 2)
          = ∫⁻ y in Set.Ioo α β, (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2 := by
            apply lintegral_congr; intro y; rw [hemb]
        _ ≤ ∫⁻ (y : ℝ), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2 := setLIntegral_le_lintegral _ _
    have hprod : (∫⁻ (x : ℝ), ∫⁻ (y : ℝ), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2)
        = ∫⁻ p : ℝ × ℝ, (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2 := by
      have hae : AEMeasurable (fun p : ℝ × ℝ => (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2)
          ((volume : Measure ℝ).prod volume) := by
        rw [← Measure.volume_eq_prod]; exact hmeas2.aemeasurable
      rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ)]
      exact (lintegral_prod _ hae).symm
    have hplane : (∫⁻ p : ℝ × ℝ, (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2)
        = ∫⁻ z, (ρ z) ^ 2 := by
      rw [← Complex.volume_preserving_equiv_real_prod.lintegral_comp_emb
        Complex.measurableEquivRealProd.measurableEmbedding
        (fun p : ℝ × ℝ => (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2)]
      apply lintegral_congr; intro z
      simp only [Complex.measurableEquivRealProd_apply]; congr 2; exact Complex.re_add_im z
    rw [hprod, hplane] at hmono1; exact hmono1
  -- ===== Dichotomy on whether `F'` stays within `closedBall 0 2`. =====
  by_cases hFbdd : F' ⊆ Metric.closedBall (0 : ℂ) 2
  · -- CASE B: `F'` bounded by radius 2 ⇒ every up-hit is at height `≤ 2`.
    have fibreB : ∀ x ∈ Set.Ioo (0 : ℝ) s,
        ENNReal.ofReal (1 / 3) ≤ ∫⁻ y in Set.Ioo (-1 : ℝ) 3, (ρ (emb x y)) ^ 2 := by
      intro x hx
      obtain ⟨H, hHtop, hHF, hHU⟩ := up_hit x hx
      -- The hit height is `≤ 2` since `emb x H ∈ F' ⊆ closedBall 0 2`.
      have hHle : H ≤ 2 := by
        have := hFbdd hHF
        rw [Metric.mem_closedBall, dist_zero_right, hembnorm] at this
        have hHabs : |H| ≤ 2 := by
          calc |H| = Real.sqrt (H ^ 2) := (Real.sqrt_sq_eq_abs _).symm
            _ ≤ Real.sqrt (x ^ 2 + H ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
            _ ≤ 2 := this
        linarith [le_abs_self H, neg_abs_le H, hHabs]
      have hlow := vseg_bound x (yTop x) H hHtop (hyTopMem x hx) hHF hHU
      have hcs := cs_window x (yTop x) H hHtop hlow
      -- `1/(H - yTop) ≥ 1/3` since `H - yTop ≤ 3`.
      have hlen : H - yTop x ≤ 3 := by linarith [hHle, hyTopge x hx]
      have hlenpos : 0 < H - yTop x := by linarith [hHtop]
      have h13 : ENNReal.ofReal (1 / 3) ≤ ENNReal.ofReal ((H - yTop x)⁻¹) := by
        apply ENNReal.ofReal_le_ofReal
        rw [one_div]; exact inv_anti₀ hlenpos hlen
      calc ENNReal.ofReal (1 / 3) ≤ ENNReal.ofReal ((H - yTop x)⁻¹) := h13
        _ ≤ ∫⁻ y in Set.Ioo (yTop x) H, (ρ (emb x y)) ^ 2 := hcs
        _ ≤ ∫⁻ y in Set.Ioo (-1 : ℝ) 3, (ρ (emb x y)) ^ 2 := by
            apply lintegral_mono_set
            intro y hy
            exact ⟨by linarith [hy.1, hyTopge x hx], by linarith [hy.2, hHle]⟩
    -- Integrate the fibre bound over `x ∈ (0, s)`.
    calc ENNReal.ofReal (s ^ 2 / 60)
        ≤ ENNReal.ofReal (s * (1 / 3)) := by
          apply ENNReal.ofReal_le_ofReal; nlinarith [hspos, hs1]
      _ = ∫⁻ _x in Set.Ioo (0 : ℝ) s, ENNReal.ofReal (1 / 3) := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero,
            ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/3), mul_comm]
      _ ≤ ∫⁻ x in Set.Ioo (0 : ℝ) s, ∫⁻ y in Set.Ioo (-1 : ℝ) 3, (ρ (emb x y)) ^ 2 := by
          apply lintegral_mono_ae
          exact ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => fibreB x hx)
      _ ≤ ∫⁻ z, (ρ z) ^ 2 := plane_cmp (-1) 3
  · -- CASE A: some point of `F'` has radius `> 2`.
    obtain ⟨w', hw'F, hw'out⟩ := Set.not_subset.mp hFbdd
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hw'out
    have hw'far : 2 < ‖w'‖ := hw'out
    -- `F'` is nonempty and compact; `infDist 0 F' = 1` is attained at some near point `w₁`.
    have hF'ne : F'.Nonempty := ⟨w', hw'F⟩
    have hF'cpt : IsCompact F' :=
      isCompact_of_isClosed_isBounded hF'closed (hKcpt.isBounded.subset hF'subK)
    obtain ⟨w₁, hw₁F, hw₁dist⟩ := hF'cpt.exists_infDist_eq_dist hF'ne (0 : ℂ)
    have hw₁norm : ‖w₁‖ = 1 := by
      rw [← dist_zero_right, dist_comm, ← hw₁dist, hb]
    -- `F'` meets every sphere of radius `ρ' ∈ (1, 2)`.
    have hF'sphere : ∀ ρ' : ℝ, 1 ≤ ρ' → ρ' ≤ 2 → ∃ w ∈ F', ‖w‖ = ρ' := by
      intro ρ' hρ'1 hρ'2
      obtain ⟨w, hwF, hwd⟩ := exists_mem_dist_eq_of_isConnected hF'conn hw₁F hw'F
        (c := 0) (r₁ := 1) (r₂ := 2)
        (by rw [dist_zero_right, hw₁norm]) (by rw [dist_zero_right]; exact hw'far.le) hρ'1 hρ'2
      exact ⟨w, hwF, by rw [← dist_zero_right]; exact hwd⟩
    -- A point on the circle of radius `r` at angle `θ`.
    set arcpt : ℝ → ℝ → ℂ := fun r θ => (r : ℂ) * Complex.exp ((θ : ℝ) * Complex.I) with harcpt
    have harcnorm : ∀ r θ : ℝ, 0 ≤ r → ‖arcpt r θ‖ = r := by
      intro r θ hr
      rw [harcpt, norm_mul, Complex.norm_real, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, mul_zero, mul_one, sub_zero, Real.exp_zero,
        Real.norm_eq_abs, abs_of_nonneg hr]
    have harccont : ∀ r : ℝ, Continuous (arcpt r) := by
      intro r
      exact continuous_const.mul (((Complex.continuous_ofReal.mul continuous_const)).cexp)
    -- The derivative of the arc `t ↦ arcpt r (α + t·Δ)` has constant norm `r·|Δ|`.
    have harcderiv : ∀ (r α Δ : ℝ) (t : ℝ),
        HasDerivAt (fun t : ℝ => arcpt r (α + t * Δ))
          ((r : ℂ) * (Complex.exp (((α + t * Δ : ℝ)) * Complex.I) * ((Δ : ℂ) * Complex.I))) t := by
      intro r α Δ t
      have h1 : HasDerivAt (fun t : ℝ => ((α + t * Δ : ℝ) : ℂ) * Complex.I)
          ((Δ : ℂ) * Complex.I) t := by
        have := (((hasDerivAt_id t).mul_const Δ).const_add α).ofReal_comp.mul_const Complex.I
        simpa using this
      have h2 := (Complex.hasDerivAt_exp _).comp t h1
      exact h2.const_mul (r : ℂ)
    have harcnormderiv : ∀ (r α Δ : ℝ), 0 ≤ r →
        ∀ t, ‖deriv (fun t : ℝ => arcpt r (α + t * Δ)) t‖ = r * |Δ| := by
      intro r α Δ hr t
      rw [(harcderiv r α Δ t).deriv, norm_mul, norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_exp, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
        abs_of_nonneg hr, Real.norm_eq_abs]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, mul_zero, mul_one, sub_zero, Real.exp_zero, one_mul]
    -- The arc curve is Lipschitz (hence AC) on `[0,1]`.
    have harclip : ∀ (r α Δ : ℝ), (hr : 0 ≤ r) →
        LipschitzWith (NNReal.mk (r * |Δ|) (mul_nonneg hr (abs_nonneg _)))
          (fun t : ℝ => arcpt r (α + t * Δ)) := by
      intro r α Δ hr
      apply lipschitzWith_of_nnnorm_deriv_le (fun t => (harcderiv r α Δ t).differentiableAt)
      intro t
      rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk, harcnormderiv r α Δ hr]
    -- Arc-length line integral as a `θ`-integral over `(α, α+Δ)` with `ds = r dθ`.
    have harclen : ∀ (r α Δ : ℝ), 0 ≤ r → 0 < Δ →
        arcLengthLineIntegral ρ (fun t => arcpt r (α + t * Δ))
          = ∫⁻ θ in Set.Ioo α (α + Δ), ENNReal.ofReal r * ρ (arcpt r θ) := by
      intro r α Δ hr hΔ
      set Lθ : ℝ → ℝ := fun t => α + t * Δ with hLθ
      have hLθimg : Lθ '' Set.Ioo (0 : ℝ) 1 = Set.Ioo α (α + Δ) := by
        ext y; simp only [Set.mem_image, Set.mem_Ioo, hLθ]
        constructor
        · rintro ⟨t, ht, rfl⟩; exact ⟨by nlinarith [ht.1, hΔ], by nlinarith [ht.2, hΔ]⟩
        · rintro ⟨hy1, hy2⟩
          exact ⟨(y - α) / Δ, ⟨by rw [lt_div_iff₀ hΔ]; linarith,
            by rw [div_lt_one hΔ]; linarith⟩, by field_simp; ring⟩
      have hLθderiv : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivWithinAt Lθ Δ (Set.Ioo (0:ℝ) 1) t := by
        intro t _
        have hd : HasDerivAt Lθ Δ t := by
          rw [hLθ]; simpa using (((hasDerivAt_id t).mul_const Δ).const_add α)
        exact hd.hasDerivWithinAt
      have hLθinj : Set.InjOn Lθ (Set.Ioo (0:ℝ) 1) := by
        intro u _ v _ huv; simp only [hLθ] at huv
        exact mul_right_cancel₀ hΔ.ne' (by linarith [huv])
      -- Change of variables on the `θ`-integral.
      have hcov : ∫⁻ θ in Set.Ioo α (α + Δ), ENNReal.ofReal r * ρ (arcpt r θ)
          = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal Δ * (ENNReal.ofReal r * ρ (arcpt r (Lθ t)))
              := by
        rw [← hLθimg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
          (f := Lθ) (f' := fun _ => Δ) hLθderiv hLθinj]
        apply lintegral_congr; intro t; rw [abs_of_pos hΔ]
      rw [hcov]
      unfold arcLengthLineIntegral
      rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm]
      apply lintegral_congr; intro t
      rw [show (‖deriv (fun t => arcpt r (α + t * Δ)) t‖₊ : ℝ≥0∞)
          = ENNReal.ofReal ‖deriv (fun t => arcpt r (α + t * Δ)) t‖ from by
        rw [ofReal_norm, enorm_eq_nnnorm], harcnormderiv r α Δ hr,
        ENNReal.ofReal_mul hr, abs_of_pos hΔ]
      change ρ (arcpt r (α + t * Δ)) * (ENNReal.ofReal r * ENNReal.ofReal Δ)
        = ENNReal.ofReal Δ * (ENNReal.ofReal r * ρ (arcpt r (Lθ t)))
      rw [hLθ]; ring
    -- Polar circle-slice comparison: the annulus `1 < |z| < 1+s` energy, sliced by circles
    -- `r = 1+x`, is at most the full plane energy.
    have circle_cmp :
        (∫⁻ x in Set.Ioo (0 : ℝ) s, ∫⁻ θ in Set.Ioo (-π) π, (ρ (arcpt (1 + x) θ)) ^ 2)
          ≤ ∫⁻ z, (ρ z) ^ 2 := by
      -- Joint measurability of `(r, θ) ↦ ρ(arcpt r θ)²`.
      have hjoint : Measurable (fun p : ℝ × ℝ => (ρ (arcpt p.1 p.2)) ^ 2) := by
        have : Measurable (fun p : ℝ × ℝ => arcpt p.1 p.2) := by
          simp only [harcpt]
          exact (Complex.measurable_ofReal.comp measurable_fst).mul
            ((Complex.measurable_ofReal.comp measurable_snd).mul_const _).cexp
        exact (hρmeas.comp this).pow_const 2
      -- Substitute `r = 1 + x` (measure preserving shift) on the outer integral.
      have hshift : (∫⁻ x in Set.Ioo (0 : ℝ) s, ∫⁻ θ in Set.Ioo (-π) π,
            (ρ (arcpt (1 + x) θ)) ^ 2)
          = ∫⁻ r in Set.Ioo (1 : ℝ) (1 + s), ∫⁻ θ in Set.Ioo (-π) π, (ρ (arcpt r θ)) ^ 2 := by
        have himg : (fun x => 1 + x) '' Set.Ioo (0:ℝ) s = Set.Ioo (1:ℝ) (1 + s) := by
          ext y; simp only [Set.mem_image, Set.mem_Ioo]
          constructor
          · rintro ⟨x, ⟨h1, h2⟩, rfl⟩; exact ⟨by linarith, by linarith⟩
          · rintro ⟨h1, h2⟩; exact ⟨y - 1, ⟨by linarith, by linarith⟩, by ring⟩
        have hd : ∀ t ∈ Set.Ioo (0:ℝ) s,
            HasDerivWithinAt (fun x => 1 + x) 1 (Set.Ioo (0:ℝ) s) t :=
          fun t _ => ((hasDerivAt_id t).const_add 1).hasDerivWithinAt
        have hinj : Set.InjOn (fun x => 1 + x) (Set.Ioo (0:ℝ) s) :=
          fun u _ v _ h => by simpa using h
        rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hd hinj]
        simp
      rw [hshift]
      -- Polar coordinates: `∫ρ² = ∫_{(0,∞)×(-π,π)} r·ρ(arcpt r θ)²`.
      have hpolar : (∫⁻ p in (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π),
            ENNReal.ofReal p.1 • (ρ (Complex.polarCoord.symm p)) ^ 2) = ∫⁻ z, (ρ z) ^ 2 := by
        have h := Complex.lintegral_comp_polarCoord_symm (fun z => (ρ z) ^ 2)
        rwa [polarCoord_target] at h
      -- Restrict polar integral to the annular slab `(1, 1+s) × (-π, π)` and use `r ≥ 1`.
      -- Identify `arcpt p.1 p.2` with `polarCoord.symm p`.
      have harceq : ∀ p : ℝ × ℝ, arcpt p.1 p.2 = Complex.polarCoord.symm p := by
        intro p
        simp only [harcpt]
        rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I]; push_cast; ring
      have hprod : (∫⁻ r in Set.Ioo (1 : ℝ) (1 + s), ∫⁻ θ in Set.Ioo (-π) π, (ρ (arcpt r θ)) ^ 2)
          = ∫⁻ p in (Set.Ioo (1:ℝ) (1+s) ×ˢ Set.Ioo (-π) π), (ρ (arcpt p.1 p.2)) ^ 2 :=
        (setLIntegral_prod _ hjoint.aemeasurable).symm
      rw [hprod]
      calc (∫⁻ p in (Set.Ioo (1:ℝ) (1+s) ×ˢ Set.Ioo (-π) π), (ρ (arcpt p.1 p.2)) ^ 2)
          ≤ ∫⁻ p in (Set.Ioo (1:ℝ) (1+s) ×ˢ Set.Ioo (-π) π),
              ENNReal.ofReal p.1 • (ρ (Complex.polarCoord.symm p)) ^ 2 := by
            apply setLIntegral_mono' (measurableSet_Ioo.prod measurableSet_Ioo)
            intro p hp
            have h1 : (1 : ℝ) ≤ p.1 := le_of_lt hp.1.1
            rw [harceq]
            calc (ρ (Complex.polarCoord.symm p)) ^ 2
                = (1 : ℝ≥0∞) • (ρ (Complex.polarCoord.symm p)) ^ 2 := by rw [one_smul]
              _ ≤ ENNReal.ofReal p.1 • (ρ (Complex.polarCoord.symm p)) ^ 2 := by
                  rw [smul_eq_mul, smul_eq_mul]
                  gcongr
                  rw [show (1:ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
                  exact ENNReal.ofReal_le_ofReal h1
        _ ≤ ∫⁻ p in (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π),
              ENNReal.ofReal p.1 • (ρ (Complex.polarCoord.symm p)) ^ 2 := by
            apply lintegral_mono_set'
            apply LE.le.eventuallyLE
            intro p hp
            exact ⟨lt_trans (by norm_num) hp.1.1, hp.2⟩
        _ = ∫⁻ z, (ρ z) ^ 2 := hpolar
    -- Per-`x` admissibility split: `1 ≤ A_x + B_x`, where `A_x` is the vertical window integral up
    -- to the splice height `T_x = √(1+2x)` (radius `1+x`) and `B_x = (1+x)·∫_{circle}` bounds the
    -- arc integral on the circle of radius `1+x`.
    have split : ∀ x ∈ Set.Ioo (0 : ℝ) s,
        1 ≤ (∫⁻ y in Set.Ioo (yTop x) (Real.sqrt (1 + 2 * x)), ρ (emb x y))
          + ENNReal.ofReal (1 + x) * ∫⁻ θ in Set.Ioo (-π) π, ρ (arcpt (1 + x) θ) := by
      intro x hx
      set Tx : ℝ := Real.sqrt (1 + 2 * x) with hTx
      have hxpos : 0 < x := hx.1
      have hxlt1 : x < 1 := lt_trans hx.2 hs1
      have h1xpos : 0 < 1 + x := by linarith
      have hTx2 : Tx ^ 2 = 1 + 2 * x := Real.sq_sqrt (by nlinarith [hxpos])
      have hTxpos : 0 < Tx := Real.sqrt_pos.mpr (by nlinarith [hxpos])
      -- `emb x Tx` sits on the circle of radius `1 + x`.
      have hembTxnorm : ‖emb x Tx‖ = 1 + x := by
        rw [hembnorm, hTx2, show x ^ 2 + (1 + 2 * x) = (1 + x) ^ 2 from by ring,
          Real.sqrt_sq h1xpos.le]
      -- `Tx > yTop x` (top slice point is below the splice height).
      have hTxgt1 : 1 < Tx := by
        have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1)
          (by nlinarith [hxpos] : (1:ℝ) < 1 + 2 * x)
        rwa [Real.sqrt_one, ← hTx] at h
      have hTxgtyTop : yTop x < Tx := lt_of_le_of_lt (hyTople x hx) (lt_trans (by linarith [hs1])
        hTxgt1)
      -- First hit `H` of the upward vertical.
      obtain ⟨H, hHtop, hHF, hHU⟩ := up_hit x hx
      by_cases hcase : H ≤ Tx
      · -- Sub-case (i): the vertical hits `F'` before the splice height.
        have hUsub : ∀ y ∈ Set.Ioo (yTop x) H, emb x y ∈ U := hHU
        have hlow := vseg_bound x (yTop x) H hHtop (hyTopMem x hx) hHF hUsub
        refine le_trans hlow (le_add_right ?_)
        apply lintegral_mono_set
        intro y hy; exact ⟨hy.1, lt_of_lt_of_le hy.2 hcase⟩
      · -- Sub-case (ii): the vertical reaches the splice height `Tx` inside `U`; finish by an arc.
        rw [not_le] at hcase
        set r : ℝ := 1 + x with hr
        -- `U ⊆ K` and `U ∩ F' = ∅`.
        have hUsubK : U ⊆ K := by
          rw [hUdef, hKdef]; exact image_mono (fun z hz => Metric.ball_subset_closedBall hz.1)
        have hUF'disj : Disjoint U F' := by
          rw [Set.disjoint_left]
          rintro z ⟨y, hy, rfl⟩ ⟨y', hy', hy'eq⟩
          have : y = y' := hinj hy'eq.symm
          subst this
          rw [Metric.mem_sphere] at hy'
          have hyb : dist y x₀ < b := Metric.mem_ball.mp hy.1
          exact absurd hy' (ne_of_lt hyb)
        -- `emb x Tx ∈ U`, off `F'`, hence in `interior K`.
        have hpU : emb x Tx ∈ U := hHU Tx ⟨hTxgtyTop, hcase⟩
        have hpnotF : emb x Tx ∉ F' := Set.disjoint_left.mp hUF'disj hpU
        have hpint : emb x Tx ∈ interior K := by
          rw [← self_sdiff_frontier K]
          exact ⟨hUsubK hpU, fun hfr => hpnotF (hfrontier hfr)⟩
        -- Polar identity: `emb x Tx = arcpt r φ` for `φ = arg (emb x Tx)`.
        set φ : ℝ := Complex.arg (emb x Tx) with hφ
        have hpolarid : arcpt r φ = emb x Tx := by
          rw [harcpt, hφ, ← hembTxnorm]; exact Complex.norm_mul_exp_arg_mul_I (emb x Tx)
        -- `F'` meets the circle of radius `r = 1 + x ∈ (1, 2)`.
        have hr1 : 1 ≤ r := by rw [hr]; linarith
        have hr2 : r ≤ 2 := by rw [hr]; linarith [hxlt1]
        obtain ⟨w, hwF, hwnorm⟩ := hF'sphere r hr1 hr2
        set ψ : ℝ := Complex.arg w with hψ
        have hwpolar : arcpt r ψ = w := by
          rw [harcpt, hψ, ← hwnorm]; exact Complex.norm_mul_exp_arg_mul_I w
        -- Angles lie in `(-π, π]`.
        have hφIoc : φ ∈ Set.Ioc (-π) π := hφ ▸ Complex.arg_mem_Ioc (emb x Tx)
        have hψIoc : ψ ∈ Set.Ioc (-π) π := hψ ▸ Complex.arg_mem_Ioc w
        have hψneφ : ψ ≠ φ := by
          intro heq
          have : w = emb x Tx := by rw [← hwpolar, ← hpolarid, heq]
          exact hpnotF (this ▸ hwF)
        -- The full sweep angle and the arc curve.
        set Δ : ℝ := ψ - φ with hΔ
        have hΔne : Δ ≠ 0 := sub_ne_zero.mpr hψneφ
        set arcγ : ℝ → ℂ := fun t => arcpt r (φ + t * Δ) with harcγ
        have harcγ0 : arcγ 0 = emb x Tx := by rw [harcγ]; simp [hpolarid]
        have harcγ1 : arcγ 1 = w := by
          rw [harcγ]; simp only [one_mul, hΔ]
          rw [show φ + (ψ - φ) = ψ from by ring, hwpolar]
        have harcγcont : Continuous arcγ := (harccont r).comp (by fun_prop)
        -- First hit of `F'` along the arc.
        set hitset : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ arcγ ⁻¹' F' with hhitset
        have hhitclosed : IsClosed hitset := isClosed_Icc.inter (hF'closed.preimage harcγcont)
        have hhitne : hitset.Nonempty := ⟨1, by
          rw [hhitset]; exact ⟨by norm_num, by rw [Set.mem_preimage, harcγ1]; exact hwF⟩⟩
        have hhitbdd : BddBelow hitset := ⟨0, fun t ht => ht.1.1⟩
        set ts : ℝ := sInf hitset with hts
        have htsmem : ts ∈ hitset := hhitclosed.csInf_mem hhitne hhitbdd
        have htsIcc : ts ∈ Set.Icc (0:ℝ) 1 := htsmem.1
        have htsF : arcγ ts ∈ F' := htsmem.2
        have htspos : 0 < ts := by
          rcases lt_or_eq_of_le htsIcc.1 with h | h
          · exact h
          · refine absurd ?_ hpnotF
            rw [← harcγ0, h]; exact htsF
        -- Before the first hit the arc avoids `F'` and stays in `interior K ⊆ K`, off `Ê`
        -- (radius `r = 1 + x > s`), hence in `U`.
        have hbeforeF : ∀ t ∈ Set.Ico (0:ℝ) ts, arcγ t ∉ F' := by
          intro t ht hmem
          have htIcc : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, le_trans ht.2.le htsIcc.2⟩
          exact absurd (csInf_le hhitbdd ⟨htIcc, hmem⟩) (not_le.mpr ht.2)
        have harcInt : ∀ t ∈ Set.Ico (0:ℝ) ts, arcγ t ∈ interior K := by
          have hstart : arcγ 0 ∈ interior K := by rw [harcγ0]; exact hpint
          intro t ht
          have hno : ∀ u ∈ Set.Icc (0:ℝ) t, arcγ u ∉ F' := by
            intro u hu; exact hbeforeF u ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩
          exact stays_in_interior hfrontier harcγcont hstart ht.1 hno t ⟨ht.1, le_refl t⟩
        -- `arcγ t ∈ U` for `t ∈ [0, ts)`.
        have harcnormt : ∀ t : ℝ, ‖arcγ t‖ = r := by
          intro t; rw [harcγ]; exact harcnorm r (φ + t * Δ) h1xpos.le
        have harcnormt : ∀ t : ℝ, ‖arcγ t‖ = r := by
          intro t; rw [harcγ]; exact harcnorm r (φ + t * Δ) h1xpos.le
        have harcU : ∀ t ∈ Set.Ico (0:ℝ) ts, arcγ t ∈ U := by
          intro t ht
          refine hUchar (arcγ t) (interior_subset (harcInt t ht)) ?_ (hbeforeF t ht)
          intro hmem
          have := hEsub hmem
          rw [Metric.mem_closedBall, dist_zero_right, harcnormt t] at this
          rw [hr] at this; linarith [hxpos]
        -- The truncated arc `arcT t = arcγ (t · ts) = arcpt r (φ + t · (ts·Δ))`.
        set Δ' : ℝ := ts * Δ with hΔ'
        set arcT : ℝ → ℂ := fun t => arcpt r (φ + t * Δ') with harcT
        have harcTeq : ∀ t, arcT t = arcγ (t * ts) := by
          intro t
          simp only [harcT, harcγ, hΔ']
          congr 1
          ring
        have harcT0 : arcT 0 = emb x Tx := by rw [harcTeq]; simp [harcγ0]
        have harcT1 : arcT 1 = arcγ ts := by rw [harcTeq]; simp
        have harcTcont : Continuous arcT := (harccont r).comp (by fun_prop)
        have harcTac : AbsolutelyContinuousOnInterval arcT 0 1 :=
          ((harclip r φ Δ' h1xpos.le).lipschitzOnWith
            (s := Set.uIcc 0 1)).absolutelyContinuousOnInterval
        -- The vertical `Vγ t = emb x (yTop x + t·(Tx - yTop x))`.
        set d : ℝ := Tx - yTop x with hd
        have hdpos : 0 < d := by rw [hd]; linarith [hTxgtyTop]
        set Vγ : ℝ → ℂ := fun t => emb x (yTop x + t * d) with hVγ
        have hVγ0 : Vγ 0 = emb x (yTop x) := by rw [hVγ]; simp
        have hVγ1 : Vγ 1 = emb x Tx := by rw [hVγ]; simp [hd]
        have hVγcont : Continuous Vγ := (hembcont x).comp (by fun_prop)
        have hVγderiv : ∀ t, HasDerivAt Vγ (((d : ℝ) : ℂ) * Complex.I) t := by
          intro t
          have h1 : HasDerivAt (fun t : ℝ => ((yTop x + t * d : ℝ) : ℂ) * Complex.I)
              (((d : ℝ) : ℂ) * Complex.I) t := by
            have := (((hasDerivAt_id t).mul_const d).const_add (yTop x)).ofReal_comp.mul_const
              Complex.I
            simpa using this
          simpa [hVγ, hemb] using h1.const_add (x : ℂ)
        have hVγac : AbsolutelyContinuousOnInterval Vγ 0 1 := by
          have hlip : LipschitzWith (NNReal.mk d hdpos.le) Vγ := by
            apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hVγderiv t).differentiableAt)
            intro t
            rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk, (hVγderiv t).deriv,
              norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
              abs_of_pos hdpos]
          exact (hlip.lipschitzOnWith (s := Set.uIcc 0 1)).absolutelyContinuousOnInterval
        -- Concatenate the vertical `Vγ` with the truncated arc `arcT` into an admissible L-curve.
        have hΔ'ne : Δ' ≠ 0 := mul_ne_zero (ne_of_gt htspos) hΔne
        have hVint : ∀ t ∈ Set.Ioo (0 : ℝ) 1, Vγ t ∈ U := by
          intro u hu
          rw [hVγ]
          refine hHU (yTop x + u * d) ⟨lt_add_of_pos_right _ (mul_pos hu.1 hdpos), ?_⟩
          have h1 : u * d < d := by
            have := mul_lt_mul_of_pos_right hu.2 hdpos; rwa [one_mul] at this
          rw [hd] at h1; linarith [hcase]
        have hAint : ∀ t ∈ Set.Ioo (0 : ℝ) 1, arcT t ∈ U := by
          intro u hu
          rw [harcTeq]
          refine harcU (u * ts) ⟨(mul_pos hu.1 htspos).le, ?_⟩
          have := mul_lt_mul_of_pos_right hu.2 htspos; rwa [one_mul] at this
        -- Vertical piece: `arcLengthLineIntegral ρ Vγ = ∫_{(yTop x, Tx)} ρ(emb x ·)`.
        have hVlen : arcLengthLineIntegral ρ Vγ = ∫⁻ y in Set.Ioo (yTop x) Tx, ρ (emb x y) := by
          have h := arcLength_vertical_seg ρ x (yTop x) d hdpos
          rw [show yTop x + d = Tx from by rw [hd]; ring] at h
          exact h
        -- Arc piece: change to the `θ`-integral over the swept sub-arc of `(-π, π)`.
        have harcTlen : arcLengthLineIntegral ρ arcT
            = ∫⁻ θ in Set.Ioo (min φ (φ + Δ')) (max φ (φ + Δ')),
                ENNReal.ofReal r * ρ (arcpt r θ) :=
          arcLength_arc_seg ρ r φ Δ' h1xpos.le hΔ'ne
        -- The swept sub-arc lies in `(-π, π)`.
        have hΔ'conv : φ + Δ' = (1 - ts) * φ + ts * ψ := by rw [hΔ', hΔ]; ring
        have hlowπ : -π < min φ (φ + Δ') := by
          rw [lt_min_iff]
          refine ⟨hφIoc.1, ?_⟩
          rw [hΔ'conv]
          have h1 : (1 - ts) * (-π) ≤ (1 - ts) * φ :=
            mul_le_mul_of_nonneg_left hφIoc.1.le (by linarith [htsIcc.2])
          have h2 : ts * (-π) < ts * ψ := mul_lt_mul_of_pos_left hψIoc.1 htspos
          have hid : (1 - ts) * (-π) + ts * (-π) = -π := by ring
          linarith [h1, h2, hid]
        have hhiπ : max φ (φ + Δ') ≤ π := by
          rw [max_le_iff]
          refine ⟨hφIoc.2, ?_⟩
          rw [hΔ'conv]
          have h1 : (1 - ts) * φ ≤ (1 - ts) * π :=
            mul_le_mul_of_nonneg_left hφIoc.2 (by linarith [htsIcc.2])
          have h2 : ts * ψ ≤ ts * π := mul_le_mul_of_nonneg_left hψIoc.2 htspos.le
          have hid : (1 - ts) * π + ts * π = π := by ring
          linarith [h1, h2, hid]
        have hsub : Set.Ioo (min φ (φ + Δ')) (max φ (φ + Δ')) ⊆ Set.Ioo (-π) π :=
          fun θ hθ => ⟨lt_of_lt_of_le hlowπ hθ.1.le, lt_of_lt_of_le hθ.2 hhiπ⟩
        -- Assemble: concatenate, split the length, and bound the swept arc by the full circle.
        exact lCurve_case_two_final hρadm hVγcont hVγac harcTcont harcTac
          (hVγ1.trans harcT0.symm) (hVγ0 ▸ hyTopMem x hx) (harcT1 ▸ htsF) hVint (hVγ1 ▸ hpU)
          hAint hVlen harcTlen ENNReal.ofReal_ne_top hsub
    -- Turn the split into a per-`x` energy bound via one-dimensional Cauchy–Schwarz on each piece.
    have fibreA : ∀ x ∈ Set.Ioo (0 : ℝ) s,
        ENNReal.ofReal (1 / 2)
          ≤ ENNReal.ofReal 3 * (∫⁻ y in Set.Ioo (-1 : ℝ) 3, (ρ (emb x y)) ^ 2)
            + ENNReal.ofReal (8 * π) * ∫⁻ θ in Set.Ioo (-π) π, (ρ (arcpt (1 + x) θ)) ^ 2 := by
      intro x hx
      set Tx : ℝ := Real.sqrt (1 + 2 * x) with hTx
      have hTxpos : 0 < Tx := Real.sqrt_pos.mpr (by nlinarith [hx.1])
      have hTx2 : Tx ^ 2 = 1 + 2 * x := Real.sq_sqrt (by nlinarith [hx.1])
      have hTxle : Tx ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by nlinarith [hx.1, hx.2, hs1])
      have hTxlt3 : Tx < 3 := lt_of_le_of_lt hTxle (by
        have : Real.sqrt 3 < Real.sqrt 9 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        rwa [show (9:ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num)] at this)
      set A : ℝ≥0∞ := ∫⁻ y in Set.Ioo (yTop x) Tx, ρ (emb x y) with hA
      set Bc : ℝ≥0∞ := ∫⁻ θ in Set.Ioo (-π) π, ρ (arcpt (1 + x) θ) with hBc
      set B : ℝ≥0∞ := ENNReal.ofReal (1 + x) * Bc with hB
      have hsplit := split x hx
      rw [← hA, ← hBc, ← hB] at hsplit
      -- `1 ≤ (A + B)² ≤ 2 A² + 2 B²`.
      have hsq : (1 : ℝ≥0∞) ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
        have h1 : (1 : ℝ≥0∞) ≤ (A + B) ^ 2 := by
          calc (1 : ℝ≥0∞) = 1 ^ 2 := (one_pow 2).symm
            _ ≤ (A + B) ^ 2 := by gcongr
        have h2 : (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
          have hexp : (A + B) ^ 2 = A ^ 2 + B ^ 2 + 2 * (A * B) := by ring
          rw [hexp]
          calc A ^ 2 + B ^ 2 + 2 * (A * B) ≤ A ^ 2 + B ^ 2 + (A ^ 2 + B ^ 2) := by
                gcongr; exact two_mul_mul_le_add_sq_enn A B
            _ = 2 * A ^ 2 + 2 * B ^ 2 := by ring
        exact le_trans h1 h2
      -- CS on the vertical window `(yTop x, Tx) ⊆ (-1, 3)`: `A² ≤ 3 · windowE`.
      have hAcs : A ^ 2 ≤ ENNReal.ofReal 3 * ∫⁻ y in Set.Ioo (-1 : ℝ) 3, (ρ (emb x y)) ^ 2 := by
        have hyge : -1 < yTop x := lt_of_lt_of_le (by linarith [hs1]) (hyTopge x hx)
        have hsqrt3lt2 : Real.sqrt 3 < 2 := by
          have : Real.sqrt 3 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
          rwa [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)] at this
        have hlen : Tx - yTop x ≤ 3 := by
          have h1 : Tx < 2 := lt_of_le_of_lt hTxle hsqrt3lt2
          linarith [hyge]
        have hTxgt1 : 1 < Tx := by
          have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1)
            (by nlinarith [hx.1] : (1:ℝ) < 1 + 2 * x)
          rwa [Real.sqrt_one, ← hTx] at h
        have hTxge : yTop x ≤ Tx := le_of_lt (lt_of_le_of_lt (hyTople x hx)
          (lt_trans (by linarith [hs1]) hTxgt1))
        have hsetle : (∫⁻ y in Set.Ioo (yTop x) Tx, (ρ (emb x y)) ^ 2)
            ≤ ∫⁻ y in Set.Ioo (-1 : ℝ) 3, (ρ (emb x y)) ^ 2 := by
          apply lintegral_mono_set
          intro y hy; exact ⟨by linarith [hy.1, hyge], by linarith [hy.2, hTxlt3]⟩
        calc A ^ 2 ≤ ENNReal.ofReal (Tx - yTop x)
              * ∫⁻ y in Set.Ioo (yTop x) Tx, (ρ (emb x y)) ^ 2 := by
              rw [hA]; exact cs_sq x (yTop x) Tx hTxge
          _ ≤ ENNReal.ofReal 3 * ∫⁻ y in Set.Ioo (-1 : ℝ) 3, (ρ (emb x y)) ^ 2 :=
              mul_le_mul (ENNReal.ofReal_le_ofReal hlen) hsetle (zero_le) (zero_le)
      -- CS on the full circle `(-π, π)`: `B² ≤ (8π) · circleE`.
      have hBcs : B ^ 2 ≤ ENNReal.ofReal (8 * π) * ∫⁻ θ in Set.Ioo (-π) π,
          (ρ (arcpt (1 + x) θ)) ^ 2 := by
        set circleE : ℝ≥0∞ := ∫⁻ θ in Set.Ioo (-π) π, (ρ (arcpt (1 + x) θ)) ^ 2 with hcircleE
        -- Hölder on `(-π, π)` gives `Bc² ≤ 2π · circleE`.
        have hBcsq : Bc ^ 2 ≤ ENNReal.ofReal (2 * π) * circleE := by
          set ν := volume.restrict (Set.Ioo (-π) π) with hν
          set fm : ℝ → ℝ≥0∞ := fun θ => ρ (arcpt (1 + x) θ) with hfm
          set gm : ℝ → ℝ≥0∞ := fun _ => 1 with hgm
          have hmeasf : AEMeasurable fm ν :=
            (hρmeas.comp (harccont (1 + x)).measurable).aemeasurable
          have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq ν
            (Real.HolderConjugate.two_two) hmeasf (aemeasurable_const (b := (1:ℝ≥0∞)))
          have hfg : ∫⁻ θ, (fm * gm) θ ∂ν = Bc := by
            rw [hν, hBc]; apply lintegral_congr; intro θ; simp [hfm, hgm]
          have hgsq : ∫⁻ θ, gm θ ^ (2 : ℝ) ∂ν = ENNReal.ofReal (2 * π) := by
            have : ∫⁻ θ, gm θ ^ (2 : ℝ) ∂ν = ∫⁻ _θ in Set.Ioo (-π) π, (1 : ℝ≥0∞) := by
              rw [hν]; apply lintegral_congr; intro θ; simp [hgm]
            rw [this, setLIntegral_const, Real.volume_Ioo]
            rw [show π - -π = 2 * π by ring]; simp [ENNReal.ofReal]
          have hfsq : ∫⁻ θ, fm θ ^ (2 : ℝ) ∂ν = circleE := by
            rw [hν, hcircleE]; apply lintegral_congr; intro θ; rw [hfm, ENNReal.rpow_two, sq]
          rw [hfg, hfsq, hgsq, show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num] at hholder
          have h := ENNReal.rpow_le_rpow hholder (show (0 : ℝ) ≤ 2 by norm_num)
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            show (2 : ℝ)⁻¹ * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one,
            ENNReal.rpow_two] at h
          rw [mul_comm (ENNReal.ofReal (2 * π))]; exact h
        -- Assemble: `B² = (1+x)²·Bc² ≤ (1+x)²·2π·circleE ≤ 4·2π·circleE = 8π·circleE`.
        have h1x : (1 + x) ^ 2 ≤ 4 := by nlinarith [hx.1, hx.2, hs1]
        calc B ^ 2 = ENNReal.ofReal ((1 + x) ^ 2) * Bc ^ 2 := by
              rw [hB, mul_pow, ← ENNReal.ofReal_pow (by linarith [hx.1])]
          _ ≤ ENNReal.ofReal ((1 + x) ^ 2) * (ENNReal.ofReal (2 * π) * circleE) :=
              mul_le_mul' (le_refl _) hBcsq
          _ = ENNReal.ofReal ((1 + x) ^ 2 * (2 * π)) * circleE := by
              rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (1+x)^2), mul_assoc]
          _ ≤ ENNReal.ofReal (8 * π) * circleE :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos, h1x])) (le_refl _)
      -- Combine: `1/2 ≤ A² + B² ≤ 3·windowE + 8π·circleE`.
      have : ENNReal.ofReal (1 / 2) ≤ A ^ 2 + B ^ 2 := by
        rw [show ENNReal.ofReal (1 / 2) = 1 / 2 from by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]; norm_num]
        rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
        calc (1 : ℝ≥0∞) ≤ 2 * A ^ 2 + 2 * B ^ 2 := hsq
          _ = (A ^ 2 + B ^ 2) * 2 := by ring
      exact le_trans this (add_le_add hAcs hBcs)
    -- Integrate the fibre bound over `x ∈ (0, s)` and compare with the plane energy.
    -- `∫_{(0,s)} (1/2) dx ≤ 3·(∫∫ window) + 8π·(∫∫ circle) ≤ (3 + 8π)·∫ρ²`.
    set W : ℝ≥0∞ := ∫⁻ z, (ρ z) ^ 2 with hW
    -- Measurability (in `x`) of the two inner slice-energy functions.
    have hmeasWin : Measurable
        (fun x : ℝ => ∫⁻ y in Set.Ioo (-1 : ℝ) 3, (ρ (emb x y)) ^ 2) := by
      have hj : Measurable (fun p : ℝ × ℝ => (ρ (emb p.1 p.2)) ^ 2) := by
        have : Measurable (fun p : ℝ × ℝ => emb p.1 p.2) := by
          simp only [hemb]
          exact (Complex.measurable_ofReal.comp measurable_fst).add
            ((Complex.measurable_ofReal.comp measurable_snd).mul_const _)
        exact (hρmeas.comp this).pow_const 2
      exact (hj.lintegral_prod_right' (ν := volume.restrict (Set.Ioo (-1 : ℝ) 3)))
    have hmeasCir : Measurable
        (fun x : ℝ => ∫⁻ θ in Set.Ioo (-π) π, (ρ (arcpt (1 + x) θ)) ^ 2) := by
      have hj : Measurable (fun p : ℝ × ℝ => (ρ (arcpt (1 + p.1) p.2)) ^ 2) := by
        have : Measurable (fun p : ℝ × ℝ => arcpt (1 + p.1) p.2) := by
          simp only [harcpt]
          exact ((Complex.measurable_ofReal.comp (measurable_const.add measurable_fst)).mul
            ((Complex.measurable_ofReal.comp measurable_snd).mul_const _).cexp)
        exact (hρmeas.comp this).pow_const 2
      exact (hj.lintegral_prod_right' (ν := volume.restrict (Set.Ioo (-π) π)))
    have hint : ENNReal.ofReal (s / 2) ≤ ENNReal.ofReal 3 * W + ENNReal.ofReal (8 * π) * W := by
      calc ENNReal.ofReal (s / 2)
          = ∫⁻ _x in Set.Ioo (0 : ℝ) s, ENNReal.ofReal (1 / 2) := by
            rw [setLIntegral_const, Real.volume_Ioo, sub_zero,
              ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
            congr 1; ring
        _ ≤ ∫⁻ x in Set.Ioo (0 : ℝ) s,
              (ENNReal.ofReal 3 * (∫⁻ y in Set.Ioo (-1 : ℝ) 3, (ρ (emb x y)) ^ 2)
                + ENNReal.ofReal (8 * π) * ∫⁻ θ in Set.Ioo (-π) π, (ρ (arcpt (1 + x) θ)) ^ 2) := by
            apply lintegral_mono_ae
            exact ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => fibreA x hx)
        _ = (∫⁻ x in Set.Ioo (0 : ℝ) s, ENNReal.ofReal 3
                * ∫⁻ y in Set.Ioo (-1 : ℝ) 3, (ρ (emb x y)) ^ 2)
              + ∫⁻ x in Set.Ioo (0 : ℝ) s, ENNReal.ofReal (8 * π)
                * ∫⁻ θ in Set.Ioo (-π) π, (ρ (arcpt (1 + x) θ)) ^ 2 :=
            lintegral_add_left (hmeasWin.const_mul _) _
        _ ≤ ENNReal.ofReal 3 * W + ENNReal.ofReal (8 * π) * W := by
            gcongr
            · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              exact mul_le_mul' (le_refl _) (plane_cmp (-1) 3)
            · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              exact mul_le_mul' (le_refl _) circle_cmp
    -- Conclude `ofReal (s²/60) ≤ W`.
    have hfactor : ENNReal.ofReal 3 * W + ENNReal.ofReal (8 * π) * W
        = ENNReal.ofReal (3 + 8 * π) * W := by
      rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by positivity)]
    rw [hfactor] at hint
    -- `ofReal (s/2) ≤ (3 + 8π)·W ⟹ ofReal (s²/60) ≤ W`.
    have hpi : (3 : ℝ) + 8 * π ≤ 30 := by nlinarith [Real.pi_lt_d2]
    have hden : ENNReal.ofReal (3 + 8 * π) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    calc ENNReal.ofReal (s ^ 2 / 60)
        ≤ ENNReal.ofReal (s / 2) / ENNReal.ofReal (3 + 8 * π) := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl hden) (Or.inl ENNReal.ofReal_ne_top),
            ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ s ^ 2 / 60)]
          apply ENNReal.ofReal_le_ofReal
          rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 60)]
          have hs2s : s ^ 2 ≤ s := by nlinarith [hspos, hs1]
          nlinarith [hspos, hpi, hs2s, mul_le_mul_of_nonneg_left hpi (sq_nonneg s)]
      _ ≤ (ENNReal.ofReal (3 + 8 * π) * W) / ENNReal.ofReal (3 + 8 * π) := by
          gcongr
      _ = W := by
          rw [mul_comm, mul_div_assoc, ENNReal.div_self hden ENNReal.ofReal_ne_top, mul_one]

/-- **The `ball \ closedBall` region is the round annulus.** For a base point `x₀` and radii
`a`, `b`, the set-difference `Metric.ball x₀ b \ Metric.closedBall x₀ a` equals the open round
annulus `RoundAnnulus x₀ a b = {a < dist · x₀ < b}`. -/
theorem ball_diff_closedBall_eq_roundAnnulus (x₀ : ℂ) (a b : ℝ) :
    Metric.ball x₀ b \ Metric.closedBall x₀ a = RoundAnnulus x₀ a b := by
  ext z
  simp only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, RoundAnnulus,
    Set.mem_ofPred_eq, not_le]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **The inner/outer circle is a metric sphere.** `innerCircle x₀ r = Metric.sphere x₀ r` and
likewise for `outerCircle`, both being `{z | dist z x₀ = r}`. -/
theorem innerCircle_eq_sphere (x₀ : ℂ) (r : ℝ) : innerCircle x₀ r = Metric.sphere x₀ r := rfl

/-- **The connecting family is unchanged when the inner boundary disk is replaced by its bounding
sphere.** Let `f : ℂ → ℂ` be a homeomorphism and `0 < a`. With ambient ring
`U := f '' RoundAnnulus x₀ a b` and outer boundary `F`, the connecting family whose inner boundary
is the *closed disk image* `f '' closedBall x₀ a` coincides with the one whose inner boundary is the
*sphere image* `f '' sphere x₀ a`.

The `⊇` inclusion is `image_mono` (`sphere ⊆ closedBall`). For `⊆`: a connecting curve `γ` starts
at `γ 0 ∈ f '' closedBall x₀ a` with interior `γ '' (0,1) ⊆ U`, and `U` is disjoint from
`f '' closedBall x₀ a` (injectivity: the round annulus is disjoint from the closed disk). Hence
`γ 0` is a limit of points off `f '' closedBall x₀ a`, so `γ 0 ∈ frontier (f '' closedBall x₀ a)`;
and `frontier (f '' closedBall x₀ a) = f '' sphere x₀ a` because a homeomorphism commutes with
`frontier` and `frontier (closedBall x₀ a) = sphere x₀ a` (as `a ≠ 0`). -/
theorem connectingCurveFamily_closedBall_eq_sphere {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {x₀ : ℂ} {a b : ℝ} (ha : 0 < a) {F : Set ℂ} :
    connectingCurveFamily (f '' Metric.closedBall x₀ a) F (f '' RoundAnnulus x₀ a b)
      = connectingCurveFamily (f '' Metric.sphere x₀ a) F (f '' RoundAnnulus x₀ a b) := by
  classical
  set U : Set ℂ := f '' RoundAnnulus x₀ a b with hU
  -- The image sphere is the topological frontier of the image closed disk.
  have hcoe : ∀ (s : Set ℂ), f '' s = ⇑(hf.homeomorph f) '' s := by
    intro s; ext w; constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, (IsHomeomorph.homeomorph_apply f hf y).symm⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, IsHomeomorph.homeomorph_apply f hf y⟩
  have hfront : frontier (f '' Metric.closedBall x₀ a) = f '' Metric.sphere x₀ a := by
    rw [hcoe (Metric.closedBall x₀ a), hcoe (Metric.sphere x₀ a),
      ← (hf.homeomorph f).image_frontier, frontier_closedBall x₀ ha.ne']
  -- `U` is disjoint from the image closed disk (injectivity + annulus ∩ closed disk = ∅).
  have hinj : Function.Injective f := hf.injective
  have hdisj : Disjoint U (f '' Metric.closedBall x₀ a) := by
    rw [Set.disjoint_left]
    rintro w ⟨y, hyA, rfl⟩ ⟨z, hzB, hzeq⟩
    have : z = y := hinj hzeq
    subst this
    simp only [RoundAnnulus, Set.mem_ofPred_eq] at hyA
    rw [Metric.mem_closedBall] at hzB
    linarith [hyA.1]
  apply Set.eq_of_subset_of_subset
  · -- `⊆`: relocate the start onto the frontier = image sphere.
    rintro γ ⟨hcont, hac, h0, h1, hint⟩
    refine ⟨hcont, hac, ?_, h1, hint⟩
    rw [← hfront]
    -- `γ 0 ∈ closure Uᶜ` (approached by interior points in `U ⊆ complement of the disk`).
    have hlim : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 (γ 0)) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ (f '' Metric.closedBall x₀ a)ᶜ := by
      have hsub : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
      filter_upwards [hsub] with t ht
      exact fun hmem => (Set.disjoint_left.mp hdisj) (hint t ht) hmem
    have hclos : γ 0 ∈ closure (f '' Metric.closedBall x₀ a)ᶜ :=
      mem_closure_of_tendsto hlim hev
    rw [frontier]
    refine ⟨subset_closure h0, ?_⟩
    rw [closure_compl] at hclos; exact hclos
  · -- `⊇`: `sphere ⊆ closedBall`, so the start already lies in the closed disk image.
    rintro γ ⟨hcont, hac, h0, h1, hint⟩
    exact ⟨hcont, hac, Set.image_mono Metric.sphere_subset_closedBall h0, h1, hint⟩

/-- **Sense-preservation is preserved under conformal affine post-composition.** For `c ≠ 0`, if
`f` is topologically sense-preserving then so is `affineMap c d ∘ f`. The image loop of
`affineMap c d ∘ f` about its centre is `c · (image loop of f)`, so a continuous logarithm of the
`f`-loop shifted by the constant `Complex.log c` is a continuous logarithm of the composite loop
with the *same* increment `2π i` over a turn (the constant shift cancels in the difference). -/
theorem sensePreserving_affine_comp {f : ℂ → ℂ} (hf : SensePreserving f) {c d : ℂ} (hc : c ≠ 0) :
    SensePreserving (affineMap c d ∘ f) := by
  refine ⟨(affineMap_isHomeomorph hc d).comp hf.1, ?_⟩
  filter_upwards [hf.2] with z₀ hz₀
  filter_upwards [hz₀] with r hr
  obtain ⟨L, hLcont, hLexp, hLincr⟩ := hr
  refine ⟨fun θ => L θ + Complex.log c, hLcont.add continuous_const, fun θ => ?_, ?_⟩
  · rw [Complex.exp_add, Complex.exp_log hc, Function.comp_apply, Function.comp_apply,
      affineMap_apply, affineMap_apply, hLexp θ]
    ring
  · have : (L (2 * Real.pi) + Complex.log c) - (L 0 + Complex.log c)
        = L (2 * Real.pi) - L 0 := by ring
    rw [this, hLincr]

/-- **Geometric quasiconformality is preserved under conformal affine post-composition.** For
`c ≠ 0`, `affineMap c d ∘ f` is geometrically `K`-quasiconformal whenever `f` is. The distortion
constant `K` is unchanged: the outer-conformal image-family modulus invariance
`curveModulus_imageCurveFamily_outer_conformal` gives
`M(Q.imageCurveFamily (affineMap c d ∘ f)) = M(Q.imageCurveFamily f) ≤ K · M(Q)`, and sense-
preservation transports by `sensePreserving_affine_comp`. -/
theorem isQCGeometric_affine_comp {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) {c d : ℂ}
    (hc : c ≠ 0) : IsQCGeometric (affineMap c d ∘ f) K := by
  refine ⟨hf.1, sensePreserving_affine_comp hf.2.1 hc, fun Q => ?_⟩
  rw [curveModulus_imageCurveFamily_outer_conformal (affineMap_isHomeomorph hc d)
    (affineMap_differentiable c d).differentiableOn f Q]
  exact hf.2.2 Q

/-- **Distance scaling under a conformal affine map.** `dist (affineMap c d w₁) (affineMap c d w₂)
= ‖c‖ · dist w₁ w₂`. -/
theorem dist_affineMap (c d w₁ w₂ : ℂ) :
    dist (affineMap c d w₁) (affineMap c d w₂) = ‖c‖ * dist w₁ w₂ := by
  simp only [affineMap_apply, dist_eq_norm]
  rw [show c * w₁ + d - (c * w₂ + d) = c * (w₁ - w₂) by ring, norm_mul]

open scoped Pointwise in
/-- **`infDist` scaling under a conformal affine map.** For `c ≠ 0`,
`infDist (affineMap c d p) (affineMap c d '' T) = ‖c‖ · infDist p T`. -/
theorem infDist_affineMap {c : ℂ} (hc : c ≠ 0) (d p : ℂ) (T : Set ℂ) :
    Metric.infDist (affineMap c d p) (affineMap c d '' T) = ‖c‖ * Metric.infDist p T := by
  have hisom : Isometry (fun w : ℂ => w + d) :=
    Isometry.of_dist_eq (fun x y => by simp [dist_eq_norm])
  have hsmul : c • T = (fun w => c * w) '' T := by
    ext w; simp only [Set.mem_smul_set, Set.mem_image, smul_eq_mul]
  have himg : affineMap c d '' T = (fun w => w + d) '' (c • T) := by
    rw [hsmul, ← Set.image_comp]
    apply Set.image_congr'
    intro w; simp only [affineMap_apply, Function.comp_apply]
  have hpt : affineMap c d p = (fun w => w + d) (c • p) := by
    simp only [affineMap_apply, smul_eq_mul]
  rw [himg, hpt, Metric.infDist_image hisom, infDist_smul₀ hc]

/-- **The normalized sandwich bound.** Let `f` be geometrically `K`-quasiconformal, `0 < a < b`, in
the *normalized* frame of the L-curve lower bound: `f x₀ = 0`, the inner disk image lies in
`closedBall 0 s` with `s` attained at `(s : ℂ) ∈ f '' closedBall x₀ a`, the image outer sphere has
`infDist 0 (f '' sphere x₀ b) = 1`, and the gate `s² < 1/2`. Then `s² / 60 ≤ K · (2π / log (b/a))`.

Chaining the L-curve lower bound `ofReal_le_curveModulus_lCurve` (`ofReal (s²/60) ≤` modulus of the
inner-disk connecting family), the family equality
`connectingCurveFamily_closedBall_eq_sphere` (replacing the inner disk boundary by its sphere), and
the transported ring modulus `geometric_ring_modulus_transport`
(`≤ ofReal K · ofReal (2π / log(b/a))`), then reading the resulting `ENNReal` inequality of
nonnegative reals back to `ℝ`. -/
theorem normalized_sandwich {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    {x₀ : ℂ} {a b s : ℝ} (ha : 0 < a) (hab : a < b) (hcenter : f x₀ = 0)
    (hspos : 0 < s) (hs2 : s ^ 2 < 1 / 2)
    (hEsub : f '' Metric.closedBall x₀ a ⊆ Metric.closedBall (0 : ℂ) s)
    (hsE : (s : ℂ) ∈ f '' Metric.closedBall x₀ a)
    (hb : Metric.infDist (0 : ℂ) (f '' Metric.sphere x₀ b) = 1) :
    s ^ 2 / 60 ≤ K * (2 * Real.pi / Real.log (b / a)) := by
  have hhomeo : IsHomeomorph f := hf.2.1.isHomeomorph
  -- L-curve lower bound on the inner-disk connecting family.
  have hlow := ofReal_le_curveModulus_lCurve hhomeo ha hab hcenter hspos hs2 hEsub hsE hb
  -- Rewrite the ambient region `ball b \ closedBall a` as `RoundAnnulus x₀ a b`.
  rw [ball_diff_closedBall_eq_roundAnnulus,
    connectingCurveFamily_closedBall_eq_sphere hhomeo ha] at hlow
  -- The transported ring modulus upper bound; `sphere = innerCircle/outerCircle`.
  have htr := geometric_ring_modulus_transport hf (z₀ := x₀) (r := a) (R := b) ha hab
  rw [← innerCircle_eq_sphere, ← innerCircle_eq_sphere] at hlow
  have hchain : ENNReal.ofReal (s ^ 2 / 60)
      ≤ ENNReal.ofReal K * ENNReal.ofReal (2 * Real.pi / Real.log (b / a)) :=
    le_trans hlow htr
  -- Read the `ENNReal` inequality back to `ℝ`.
  rw [← ENNReal.ofReal_mul (le_trans zero_le_one hf.1)] at hchain
  have hlogpos : 0 < Real.log (b / a) :=
    Real.log_pos ((one_lt_div ha).mpr hab)
  have hrhs_nonneg : 0 ≤ K * (2 * Real.pi / Real.log (b / a)) := by
    apply mul_nonneg (le_trans zero_le_one hf.1)
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hrhs_nonneg).mp hchain

/-- **The de-normalized shell-ratio sandwich (STAR).** For a geometrically `K`-quasiconformal `f`
and `0 < a < b`, write the two image shells about `f x₀`:

* `a' := sSup {r | ∃ ζ ∈ f '' closedBall x₀ a, r = dist ζ (f x₀)}` — the farthest image distance of
  the inner disk (attained: the image is compact);
* `b' := infDist (f x₀) (f '' sphere x₀ b)` — the nearest image distance of the outer sphere.

Under the nondegeneracy `0 < a'` and the gate `(a'/b')² < 1/2`, the shell ratio obeys
`(a'/b')² / 60 ≤ K · (2π / log (b/a))`.

Proof: normalize by the conformal affine similarity `φ w := c · (w − f x₀)` with `‖c‖ = 1/b'`,
rotated so the farthest image point lands on the positive real axis at `a'/b'`. Then `φ ∘ f` is
geometrically `K`-quasiconformal (`isQCGeometric_affine_comp`), `(φ∘f) x₀ = 0`, its inner disk image
lies in `closedBall 0 (a'/b')` with `a'/b'` attained at the real point, and its outer sphere has
`infDist 0 · = 1` (all by `dist_affineMap`/`infDist_affineMap`). `normalized_sandwich` with
`s := a'/b'` gives the bound. -/
theorem geometric_shellRatio_star {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    {x₀ : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (ha'pos : 0 < sSup {r : ℝ | ∃ ζ ∈ f '' Metric.closedBall x₀ a, r = dist ζ (f x₀)})
    (hgate : (sSup {r : ℝ | ∃ ζ ∈ f '' Metric.closedBall x₀ a, r = dist ζ (f x₀)}
        / Metric.infDist (f x₀) (f '' Metric.sphere x₀ b)) ^ 2 < 1 / 2) :
    (sSup {r : ℝ | ∃ ζ ∈ f '' Metric.closedBall x₀ a, r = dist ζ (f x₀)}
        / Metric.infDist (f x₀) (f '' Metric.sphere x₀ b)) ^ 2 / 60
      ≤ K * (2 * Real.pi / Real.log (b / a)) := by
  classical
  have hhomeo : IsHomeomorph f := hf.2.1.isHomeomorph
  set S : Set ℝ := {r : ℝ | ∃ ζ ∈ f '' Metric.closedBall x₀ a, r = dist ζ (f x₀)} with hSdef
  set a' : ℝ := sSup S with ha'
  set b' : ℝ := Metric.infDist (f x₀) (f '' Metric.sphere x₀ b) with hb'
  -- `S` is the `dist · (f x₀)`-image of the compact `f '' closedBall x₀ a`, so `a'` is attained.
  have hKcpt : IsCompact (f '' Metric.closedBall x₀ a) :=
    (isCompact_closedBall x₀ a).image hhomeo.continuous
  have hSimg : S = (fun ζ => dist ζ (f x₀)) '' (f '' Metric.closedBall x₀ a) := by
    ext r; simp only [hSdef, Set.mem_ofPred_eq, Set.mem_image]
    exact ⟨fun ⟨ζ, hζ, h⟩ => ⟨ζ, hζ, h.symm⟩, fun ⟨ζ, hζ, h⟩ => ⟨ζ, hζ, h.symm⟩⟩
  have hSne : (f '' Metric.closedBall x₀ a).Nonempty :=
    ⟨f x₀, x₀, Metric.mem_closedBall_self ha.le, rfl⟩
  have hbdd : BddAbove S := by
    rw [hSimg]; exact hKcpt.bddAbove_image (continuous_id.dist continuous_const).continuousOn
  have ha'mem : a' ∈ S := by
    rw [hSimg, ha']; rw [hSimg]
    exact (hKcpt.image (continuous_id.dist continuous_const)).sSup_mem (hSne.image _)
  obtain ⟨ζ₀, hζ₀E, hζ₀d⟩ := ha'mem
  -- Positivity of `b'`: `f x₀` is off the (closed, nonempty) image sphere by injectivity.
  have hb'nn : 0 ≤ b' := Metric.infDist_nonneg
  have hFcpt : IsCompact (f '' Metric.sphere x₀ b) :=
    (isCompact_sphere x₀ b).image hhomeo.continuous
  have hbpos : 0 < b := lt_trans ha hab
  have hFne : (f '' Metric.sphere x₀ b).Nonempty := by
    obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (x := x₀) (r := b)).mpr hbpos.le
    exact ⟨f w, w, hw, rfl⟩
  have hcenter_off : f x₀ ∉ f '' Metric.sphere x₀ b := by
    rintro ⟨y, hy, hyeq⟩
    have hxy : x₀ = y := hhomeo.injective hyeq.symm
    rw [← hxy, Metric.mem_sphere, dist_self] at hy
    exact hbpos.ne hy
  have hb'pos : 0 < b' := by
    rw [hb']
    exact (hFcpt.isClosed.notMem_iff_infDist_pos hFne).mp hcenter_off
  have ha'b' : a' < b' := by
    have hs1 : a' / b' < 1 := by
      by_contra hle
      have hge : 1 ≤ a' / b' := not_lt.mp hle
      nlinarith [hgate]
    rwa [div_lt_one hb'pos] at hs1
  set s : ℝ := a' / b' with hs
  have hspos : 0 < s := div_pos ha'pos hb'pos
  have hs2 : s ^ 2 < 1 / 2 := hgate
  -- The rotation aligning the farthest image point to the positive real axis.
  set θ : ℝ := Complex.arg (ζ₀ - f x₀) with hθ
  set c : ℂ := Complex.exp (-(θ : ℂ) * Complex.I) / (b' : ℂ) with hc
  have hb'C : (b' : ℂ) ≠ 0 := by exact_mod_cast hb'pos.ne'
  have hcne : c ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) hb'C
  have hcnorm : ‖c‖ = 1 / b' := by
    rw [hc, norm_div, Complex.norm_exp]
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, neg_zero, Real.exp_zero,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb'pos, one_div]
  set d : ℂ := -(c * f x₀) with hd
  set g : ℂ → ℂ := affineMap c d ∘ f with hg
  have hgQC : IsQCGeometric g K := isQCGeometric_affine_comp hf hcne
  have hgeq : ∀ w, g w = c * (f w - f x₀) := by
    intro w; simp only [hg, Function.comp_apply, affineMap_apply, hd]; ring
  -- `g x₀ = 0`.
  have hgcenter : g x₀ = 0 := by rw [hgeq]; ring
  -- Image sets as `affineMap`-images of the `f`-image sets.
  have hgimg : ∀ (T : Set ℂ), g '' T = affineMap c d '' (f '' T) := by
    intro T; rw [hg, Set.image_comp]
  -- Distance from `g w` to `0`: `‖c‖ · dist (f w) (f x₀)`.
  have hgdist : ∀ w, dist (g w) 0 = ‖c‖ * dist (f w) (f x₀) := by
    intro w; rw [hgeq, dist_zero_right, dist_eq_norm, norm_mul]
  -- (hEsub) inner disk image lies in `closedBall 0 s`.
  have hEsub : g '' Metric.closedBall x₀ a ⊆ Metric.closedBall (0 : ℂ) s := by
    rintro w ⟨y, hy, rfl⟩
    rw [Metric.mem_closedBall, hgdist, hcnorm, hs]
    have hle : dist (f y) (f x₀) ≤ a' :=
      le_csSup hbdd ⟨f y, ⟨y, hy, rfl⟩, rfl⟩
    rw [one_div, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  -- (hsE) the real point `s` is attained at the farthest image preimage.
  have hsE : (s : ℂ) ∈ g '' Metric.closedBall x₀ a := by
    obtain ⟨w₀, hw₀, hw₀eq⟩ := hζ₀E
    refine ⟨w₀, hw₀, ?_⟩
    rw [hgeq, hw₀eq]
    -- `ζ₀ - f x₀ = a' · exp(θ I)` (polar form), so `c · (ζ₀ - f x₀) = a'/b' = s`.
    have hpolar : ζ₀ - f x₀ = (a' : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      have hnorm : (a' : ℂ) = (‖ζ₀ - f x₀‖ : ℂ) := by
        rw [hζ₀d, dist_eq_norm]
      rw [hnorm, hθ]
      exact (Complex.norm_mul_exp_arg_mul_I (ζ₀ - f x₀)).symm
    rw [hpolar, hc]
    rw [show (Complex.exp (-(θ : ℂ) * Complex.I) / (b' : ℂ))
        * ((a' : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        = (a' : ℂ) / (b' : ℂ) * (Complex.exp (-(θ : ℂ) * Complex.I)
          * Complex.exp ((θ : ℂ) * Complex.I)) by ring]
    rw [← Complex.exp_add, show -(θ : ℂ) * Complex.I + (θ : ℂ) * Complex.I = 0 by ring,
      Complex.exp_zero, mul_one, hs, Complex.ofReal_div]
  -- (hb) the outer sphere image has `infDist 0 · = 1`.
  have hbnorm : Metric.infDist (0 : ℂ) (g '' Metric.sphere x₀ b) = 1 := by
    rw [hgimg, ← hgcenter, hg, Function.comp_apply, infDist_affineMap hcne, ← hb', hcnorm,
      one_div, inv_mul_cancel₀ hb'pos.ne']
  -- Apply the normalized sandwich to `g` and rewrite `s = a'/b'`.
  have hres := normalized_sandwich hgQC ha hab hgcenter hspos hs2 hEsub hsE hbnorm
  rwa [hs] at hres

end NoWanderingDomains
