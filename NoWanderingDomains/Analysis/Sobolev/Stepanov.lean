/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Stepanov's almost-everywhere differentiability theorem

This file proves **Stepanov's theorem** for `ℂ → ℂ` (`≅ ℝ² → ℝ²`):

> If `f : ℂ → ℂ` has a finite upper metric derivative at almost every point — i.e. for almost
> every `x` there is a constant `C` with `‖f y - f x‖ ≤ C ‖y - x‖` for all `y` near `x` — then
> `f` is (real-Fréchet-)differentiable at almost every point.

We follow **Malý's 1999 proof** ("A simple proof of the Stepanov theorem on differentiability
almost everywhere", Exposition. Math. 17), which avoids the Lebesgue density theorem and any
measurability requirement on the (uncountable) "pointwise-Lipschitz" cover sets. The ingredients
are:

* **Rademacher's theorem** (`LipschitzWith.ae_differentiableAt`) for the auxiliary global Lipschitz
  functions;
* a **sandwich / squeeze lemma** `hasFDerivAt_of_squeeze`: if `g ≤ f ≤ h` with `g x₀ = f x₀ = h x₀`
  and `g`, `h` are differentiable at `x₀`, then `f` is differentiable at `x₀` (Hajłasz, Geometric
  Analysis, Lemma 1.13);
* the **inf- and sup-convolutions** `infConv`/`supConv` producing, for a function bounded on a ball,
  its largest `n`-Lipschitz minorant and smallest `n`-Lipschitz majorant.

The reduction to real-valued functions is componentwise via `Complex.equivRealProdCLM`.

The real-valued core is `ae_differentiableAt_real_of_ae_isLittleO`; the main theorem is
`ae_differentiableAt_of_ae_limsup_slope_lt_top`.
-/

open MeasureTheory Metric Set Filter Topology Asymptotics
open scoped NNReal ENNReal

namespace NoWanderingDomains.Stepanov

/-! ## The squeeze (sandwich) lemma for Fréchet differentiability -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Sandwich lemma for differentiability.** If `g ≤ f ≤ h` on a finite-dimensional domain,
`g`, `h` are differentiable at `x₀`, and `g x₀ = f x₀ = h x₀`, then `f` is differentiable at `x₀`.
(The two derivatives of `g` and `h` are forced to agree by Fermat's theorem applied to `h - g`.) -/
theorem hasFDerivAt_of_squeeze {g f h : E → ℝ} {x₀ : E} {Lg Lh : E →L[ℝ] ℝ}
    (hg : HasFDerivAt g Lg x₀) (hh : HasFDerivAt h Lh x₀)
    (hgf : ∀ᶠ x in 𝓝 x₀, g x ≤ f x) (hfh : ∀ᶠ x in 𝓝 x₀, f x ≤ h x)
    (hgx : g x₀ = f x₀) (hhx : h x₀ = f x₀) :
    HasFDerivAt f Lg x₀ := by
  -- `h - g ≥ 0` near `x₀` with a zero at `x₀`, so `x₀` is a local min of `h - g`.
  have hmin : IsLocalMin (fun x => h x - g x) x₀ := by
    have hval : h x₀ - g x₀ = 0 := by rw [hgx, hhx]; ring
    filter_upwards [hgf, hfh] with x hx1 hx2
    change h x₀ - g x₀ ≤ h x - g x
    rw [hval]
    exact sub_nonneg.2 (hx1.trans hx2)
  -- Fermat: the derivative of `h - g` at `x₀` is zero, hence `Lh = Lg`.
  have hLeq : Lh = Lg := by
    have hd : HasFDerivAt (fun x => h x - g x) (Lh - Lg) x₀ := hh.sub hg
    have hz : Lh - Lg = 0 := hmin.hasFDerivAt_eq_zero hd
    exact sub_eq_zero.1 hz
  rw [hLeq] at hh
  -- Now squeeze: `|f x - f x₀ - Lg (x - x₀)| ≤ |g-part| + |h-part|`, both little-o.
  rw [hasFDerivAt_iff_isLittleO] at hg hh ⊢
  -- Eventual pointwise bound on the `f`-remainder by the sum of `g`- and `h`-remainders.
  have hbound : ∀ᶠ x in 𝓝 x₀, |f x - f x₀ - Lg (x - x₀)|
      ≤ |g x - g x₀ - Lg (x - x₀)| + |h x - h x₀ - Lg (x - x₀)| := by
    filter_upwards [hgf, hfh] with x hxgf hxfh
    have h₁ : g x - g x₀ - Lg (x - x₀) ≤ f x - f x₀ - Lg (x - x₀) := by
      rw [hgx]; linarith
    have h₂ : f x - f x₀ - Lg (x - x₀) ≤ h x - h x₀ - Lg (x - x₀) := by
      rw [hhx]; linarith
    rcases abs_cases (f x - f x₀ - Lg (x - x₀)) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]
      calc f x - f x₀ - Lg (x - x₀) ≤ h x - h x₀ - Lg (x - x₀) := h₂
        _ ≤ |h x - h x₀ - Lg (x - x₀)| := le_abs_self _
        _ ≤ |g x - g x₀ - Lg (x - x₀)| + |h x - h x₀ - Lg (x - x₀)| :=
              le_add_of_nonneg_left (abs_nonneg _)
    · rw [he]
      calc -(f x - f x₀ - Lg (x - x₀)) ≤ -(g x - g x₀ - Lg (x - x₀)) := by linarith
        _ ≤ |g x - g x₀ - Lg (x - x₀)| := neg_le_abs _
        _ ≤ |g x - g x₀ - Lg (x - x₀)| + |h x - h x₀ - Lg (x - x₀)| :=
              le_add_of_nonneg_right (abs_nonneg _)
  -- Conclude via the `ε`-criterion for little-o.
  rw [isLittleO_iff] at hg hh ⊢
  intro c hc
  filter_upwards [hg (half_pos hc), hh (half_pos hc), hbound] with x hxg hxh hxb
  rw [Real.norm_eq_abs] at hxg hxh ⊢
  calc |f x - f x₀ - Lg (x - x₀)|
      ≤ |g x - g x₀ - Lg (x - x₀)| + |h x - h x₀ - Lg (x - x₀)| := hxb
    _ ≤ c / 2 * ‖x - x₀‖ + c / 2 * ‖x - x₀‖ := by gcongr
    _ = c * ‖x - x₀‖ := by ring

/-! ## Inf- and sup-convolution: largest minorant / smallest majorant -/

variable {α : Type*} [PseudoMetricSpace α]

/-- The inf-convolution `infConv n s f y = ⨅ z ∈ s, f z + n * dist y z`. When `f` is bounded below
on the nonempty set `s`, this is the **largest** `n`-Lipschitz function lying below `f` on `s`. -/
noncomputable def infConv (n : ℝ≥0) (s : Set α) (f : α → ℝ) (y : α) : ℝ :=
  ⨅ z : s, f z + n * dist y z

/-- Auxiliary boundedness for `infConv`: if `f` is bounded below on `s` by `c`, then for each `y`
the family `z ↦ f z + n * dist y z` (over `z ∈ s`) is bounded below. -/
theorem bddBelow_infConv_family {n : ℝ≥0} {s : Set α} {f : α → ℝ} {c : ℝ}
    (hc : ∀ z ∈ s, c ≤ f z) (y : α) :
    BddBelow (Set.range fun z : s => f z + n * dist y z) := by
  refine ⟨c, ?_⟩
  rintro w ⟨z, rfl⟩
  have : (0 : ℝ) ≤ n * dist y z := by positivity
  have := hc z z.2
  linarith

/-- `infConv n s f` is `n`-Lipschitz (globally), provided `f` is bounded below on the nonempty
set `s`. -/
theorem lipschitzWith_infConv {n : ℝ≥0} {s : Set α} {f : α → ℝ} {c : ℝ}
    (hs : s.Nonempty) (hc : ∀ z ∈ s, c ≤ f z) :
    LipschitzWith n (infConv n s f) := by
  have : Nonempty s := hs.to_subtype
  refine LipschitzWith.of_le_add_mul n fun x y => ?_
  rw [← sub_le_iff_le_add]
  refine le_ciInf fun z => ?_
  rw [sub_le_iff_le_add, infConv]
  calc ⨅ z : s, f z + n * dist x z ≤ f z + n * dist x z :=
        ciInf_le (bddBelow_infConv_family hc x) z
    _ ≤ f z + n * dist y z + n * dist x y := by
        have htri : dist x (z : α) ≤ dist x y + dist y z := dist_triangle x y z
        have hn : (0 : ℝ) ≤ n := n.2
        nlinarith [htri, hn]

/-- `infConv n s f` lies below `f` on `s` (take `z = y` in the infimum). -/
theorem infConv_le_self {n : ℝ≥0} {s : Set α} {f : α → ℝ} {c : ℝ}
    (hc : ∀ z ∈ s, c ≤ f z) {y : α} (hy : y ∈ s) :
    infConv n s f y ≤ f y := by
  have : Nonempty s := ⟨⟨y, hy⟩⟩
  refine (ciInf_le (bddBelow_infConv_family hc y) ⟨y, hy⟩).trans ?_
  simp

/-- If `f` is controlled below from `x₀` on `s` — `f x₀ - n * dist x₀ z ≤ f z` for all `z ∈ s` —
then `infConv n s f` matches `f` at `x₀`. Combined with `infConv_le_self`, this gives
`infConv n s f x₀ = f x₀`. -/
theorem le_infConv_of_lowerControl {n : ℝ≥0} {s : Set α} {f : α → ℝ} {x₀ : α}
    (hs : s.Nonempty) (hctrl : ∀ z ∈ s, f x₀ - n * dist x₀ z ≤ f z) :
    f x₀ ≤ infConv n s f x₀ := by
  have : Nonempty s := hs.to_subtype
  refine le_ciInf fun z => ?_
  have hz := hctrl z z.2
  linarith

/-- The sup-convolution: the **smallest** `n`-Lipschitz function lying above `f` on `s`. Defined as
the negative of the inf-convolution of `-f`. -/
noncomputable def supConv (n : ℝ≥0) (s : Set α) (f : α → ℝ) (y : α) : ℝ :=
  -(infConv n s (fun z => -(f z)) y)

/-- `supConv n s f` is `n`-Lipschitz, provided `f` is bounded above on the nonempty set `s`. -/
theorem lipschitzWith_supConv {n : ℝ≥0} {s : Set α} {f : α → ℝ} {c : ℝ}
    (hs : s.Nonempty) (hc : ∀ z ∈ s, f z ≤ c) :
    LipschitzWith n (supConv n s f) := by
  have hlc : ∀ z ∈ s, -c ≤ -(f z) := fun z hz => neg_le_neg (hc z hz)
  have := lipschitzWith_infConv (n := n) (f := fun z => -(f z)) (c := -c) hs hlc
  unfold supConv
  exact this.neg

/-- `supConv n s f` lies above `f` on `s`. -/
theorem self_le_supConv {n : ℝ≥0} {s : Set α} {f : α → ℝ} {c : ℝ}
    (hc : ∀ z ∈ s, f z ≤ c) {y : α} (hy : y ∈ s) :
    f y ≤ supConv n s f y := by
  have hlc : ∀ z ∈ s, -c ≤ -(f z) := fun z hz => neg_le_neg (hc z hz)
  have := infConv_le_self (n := n) (f := fun z => -(f z)) (c := -c) hlc hy
  simp only [supConv]
  linarith

/-- If `f` is controlled above from `x₀` on `s` — `f z ≤ f x₀ + n * dist x₀ z` for all `z ∈ s` —
then `supConv n s f` matches `f` at `x₀` (combined with `self_le_supConv`). -/
theorem supConv_le_of_upperControl {n : ℝ≥0} {s : Set α} {f : α → ℝ} {x₀ : α}
    (hs : s.Nonempty) (hctrl : ∀ z ∈ s, f z ≤ f x₀ + n * dist x₀ z) :
    supConv n s f x₀ ≤ f x₀ := by
  have hlc : ∀ z ∈ s, (fun z => -(f z)) x₀ - n * dist x₀ z ≤ (fun z => -(f z)) z := by
    intro z hz
    have := hctrl z hz
    simp only
    linarith
  have := le_infConv_of_lowerControl (n := n) (f := fun z => -(f z)) hs hlc
  simp only [supConv]
  linarith

/-! ## The real-valued core of Stepanov's theorem -/

open scoped Classical in
/-- **Stepanov's theorem, real-valued core.** A function `f : ℂ → ℝ` which is pointwise Lipschitz
(finite upper metric derivative) at almost every point is (real-Fréchet-)differentiable at almost
every point.

The proof is Malý's: cover the pointwise-Lipschitz set by countably many balls `U j = ball c r`
with rational centre/radius; on each, sandwich `f` between its largest `n`-Lipschitz minorant
`infConv` and smallest `n`-Lipschitz majorant `supConv`, which are differentiable a.e. by
Rademacher; at a good point both touch `f` and the squeeze lemma gives differentiability of `f`. -/
theorem ae_differentiableAt_real_of_ae_isLittleO {f : ℂ → ℝ}
    (hlip : ∀ᵐ x : ℂ, ∃ C : ℝ, ∀ᶠ y in 𝓝 x, ‖f y - f x‖ ≤ C * ‖y - x‖) :
    ∀ᵐ x : ℂ, DifferentiableAt ℝ f x := by
  -- A countable dense subset `D` of `ℂ`.
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have : Countable D := hDc.to_subtype
  -- Index set: centre in `D`, positive rational radius, Lipschitz constant in `ℕ`.
  set J := D × { q : ℚ // 0 < q } × ℕ with hJ
  have : Countable J := by infer_instance
  -- For each index, the ball, the constant, and the two auxiliary Lipschitz functions.
  set U : J → Set ℂ := fun j => ball (j.1 : ℂ) (j.2.1 : ℝ) with hU
  set N : J → ℝ≥0 := fun j => (j.2.2 : ℝ≥0) with hN
  set a : J → ℂ → ℝ := fun j => infConv (N j) (U j) f with ha
  set b : J → ℂ → ℝ := fun j => supConv (N j) (U j) f with hb
  -- "Good" indices: those on which `f` is bounded (so `a j`, `b j` are globally Lipschitz).
  set good : J → Prop := fun j => (∃ cl : ℝ, ∀ z ∈ U j, cl ≤ f z) ∧ (∃ cu : ℝ, ∀ z ∈ U j, f z ≤ cu)
    with hgood
  -- Rademacher on each good piece: a.e. `x`, for every good index whose ball contains `x`,
  -- both `a j` and `b j` are differentiable at `x`.
  have hae_diff : ∀ᵐ x : ℂ, ∀ j : J,
      good j → x ∈ U j → DifferentiableAt ℝ (a j) x ∧ DifferentiableAt ℝ (b j) x := by
    rw [ae_all_iff]
    intro j
    by_cases hg : good j
    · obtain ⟨⟨cl, hcl⟩, ⟨cu, hcu⟩⟩ := hg
      have hUne : (U j).Nonempty := ⟨(j.1 : ℂ), mem_ball_self (by exact_mod_cast j.2.1.2)⟩
      have hLa : LipschitzWith (N j) (a j) := lipschitzWith_infConv hUne hcl
      have hLb : LipschitzWith (N j) (b j) := lipschitzWith_supConv hUne hcu
      filter_upwards [hLa.ae_differentiableAt, hLb.ae_differentiableAt]
        with x hxa hxb _ _ using ⟨hxa, hxb⟩
    · filter_upwards [] with x hgj using absurd hgj hg
  -- Combine with the pointwise-Lipschitz hypothesis.
  filter_upwards [hlip, hae_diff] with x ⟨C, hC⟩ hdiff
  -- Extract a uniform Lipschitz bound on a ball `ball x ρ`.
  rw [Metric.eventually_nhds_iff_ball] at hC
  obtain ⟨ρ, hρ, hball⟩ := hC
  -- Replace `C` by a nonnegative constant.
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hballC' : ∀ y ∈ ball x ρ, ‖f y - f x‖ ≤ C' * ‖y - x‖ := by
    intro y hy
    refine (hball y hy).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  -- Pick a natural Lipschitz constant `n ≥ C'`.
  obtain ⟨n, hn⟩ := exists_nat_ge C'
  -- Pick a rational ball `ball c q` with `x ∈ ball c q ⊆ ball x ρ`.
  obtain ⟨c, hcD, hcx⟩ := hDd.exists_dist_lt x (show (0:ℝ) < ρ / 4 by linarith)
  -- `hcx : dist x c < ρ / 4`. Choose a rational radius `q ∈ (dist x c, ρ - dist x c)`.
  have hlt : dist x c < ρ - dist x c := by linarith [hcx]
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  have hqpos : (0 : ℝ) < q := lt_of_le_of_lt dist_nonneg hq1
  have hqpos' : (0 : ℚ) < q := by exact_mod_cast hqpos
  -- The index.
  set j : J := (⟨c, hcD⟩, ⟨q, hqpos'⟩, n) with hjdef
  have hxUj : x ∈ U j := by
    simp only [hU, hjdef, mem_ball]
    exact hq1
  have hUjsub : U j ⊆ ball x ρ := by
    intro y hy
    simp only [hU, hjdef, mem_ball] at hy ⊢
    have htri : dist y x ≤ dist y c + dist c x := dist_triangle y c x
    rw [dist_comm c x] at htri
    -- `dist y c < q` and `dist x c < q`, with `q + dist x c ≤ ρ`.
    linarith [hq2]
  -- `j` is a good index: `f` is bounded on `U j ⊆ ball x ρ`.
  have hNj : (N j : ℝ) = n := by simp [hN, hjdef]
  have hfbound : ∀ z ∈ U j, ‖f z - f x‖ ≤ (n : ℝ) * ‖z - x‖ := by
    intro z hz
    refine (hballC' z (hUjsub hz)).trans ?_
    exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)
  -- Each point `z ∈ U j` satisfies `‖z - x‖ ≤ q + dist x c =: M`.
  set M : ℝ := (q : ℝ) + dist x c with hM
  have hzxbound : ∀ z ∈ U j, ‖z - x‖ ≤ M := by
    intro z hz
    have hzc : z ∈ U j := hz
    simp only [hU, hjdef, mem_ball] at hzc
    rw [← dist_eq_norm, hM]
    calc dist z x ≤ dist z c + dist c x := dist_triangle z c x
      _ ≤ (q:ℝ) + dist x c := by rw [dist_comm c x]; linarith
  have hgoodj : good j := by
    have hn0 : (0:ℝ) ≤ n := n.cast_nonneg
    refine ⟨⟨f x - n * M, fun z hz => ?_⟩, ⟨f x + n * M, fun z hz => ?_⟩⟩
    · have hb := hfbound z hz
      rw [Real.norm_eq_abs] at hb
      have habs := (abs_le.1 hb).1
      have hzx := hzxbound z hz
      nlinarith [habs, hzx, hn0, norm_nonneg (z - x)]
    · have hb := hfbound z hz
      rw [Real.norm_eq_abs] at hb
      have habs := (abs_le.1 hb).2
      have hzx := hzxbound z hz
      nlinarith [habs, hzx, hn0, norm_nonneg (z - x)]
  -- The two auxiliary functions are differentiable at `x`.
  obtain ⟨hda, hdb⟩ := hdiff j hgoodj hxUj
  obtain ⟨La, hLa⟩ := hda
  obtain ⟨Lb, hLb⟩ := hdb
  -- `U j` is a neighbourhood of `x`, so the sandwich holds eventually near `x`.
  have hUjnhds : U j ∈ 𝓝 x := isOpen_ball.mem_nhds hxUj
  obtain ⟨cl, hcl⟩ := hgoodj.1
  obtain ⟨cu, hcu⟩ := hgoodj.2
  have hUjne : (U j).Nonempty := ⟨x, hxUj⟩
  -- Sandwich inequalities, eventually near `x`.
  have ha_le : ∀ᶠ y in 𝓝 x, a j y ≤ f y := by
    filter_upwards [hUjnhds] with y hy using infConv_le_self hcl hy
  have hf_le : ∀ᶠ y in 𝓝 x, f y ≤ b j y := by
    filter_upwards [hUjnhds] with y hy using self_le_supConv hcu hy
  -- Lower and upper pointwise control of `f` from `x` on `U j` (for the value equalities).
  have hlower : ∀ z ∈ U j, f x - (N j : ℝ) * dist x z ≤ f z := by
    intro z hz
    have hb := hfbound z hz
    rw [Real.norm_eq_abs] at hb
    have habs := (abs_le.1 hb).1
    rw [hNj, dist_comm x z, dist_eq_norm]
    linarith [habs]
  have hupper : ∀ z ∈ U j, f z ≤ f x + (N j : ℝ) * dist x z := by
    intro z hz
    have hb := hfbound z hz
    rw [Real.norm_eq_abs] at hb
    have habs := (abs_le.1 hb).2
    rw [hNj, dist_comm x z, dist_eq_norm]
    linarith [habs]
  -- Hence `a j x = f x = b j x`.
  have ha_x : a j x = f x :=
    le_antisymm (infConv_le_self hcl hxUj) (le_infConv_of_lowerControl hUjne hlower)
  have hb_x : b j x = f x :=
    le_antisymm (supConv_le_of_upperControl hUjne hupper) (self_le_supConv hcu hxUj)
  -- Apply the squeeze lemma.
  exact (hasFDerivAt_of_squeeze hLa hLb ha_le hf_le ha_x hb_x).differentiableAt

/-! ## Stepanov's theorem for `ℂ → ℂ` -/

/-- **Stepanov's theorem.** A function `f : ℂ → ℂ` (`≅ ℝ² → ℝ²`) whose upper metric derivative is
finite almost everywhere — i.e. for almost every `x` there is a constant `C` with
`‖f y - f x‖ ≤ C ‖y - x‖` for all `y` near `x` — is real-Fréchet-differentiable almost everywhere.

This is the genuine Stepanov theorem (Stepanov 1923; Evans–Gariepy, *Measure Theory and Fine
Properties of Functions*, Thm 3.1.9). It is proved by reducing to the real-valued core
`ae_differentiableAt_real_of_ae_isLittleO` componentwise via `Complex.equivRealProdCLM`. -/
theorem ae_differentiableAt_of_ae_limsup_slope_lt_top {f : ℂ → ℂ}
    (hlip : ∀ᵐ x : ℂ, ∃ C : ℝ, ∀ᶠ y in 𝓝 x, ‖f y - f x‖ ≤ C * ‖y - x‖) :
    ∀ᵐ x : ℂ, DifferentiableAt ℝ f x := by
  -- The two real components inherit the pointwise-Lipschitz hypothesis.
  have hre : ∀ᵐ x : ℂ, ∃ C : ℝ, ∀ᶠ y in 𝓝 x, ‖(f y).re - (f x).re‖ ≤ C * ‖y - x‖ := by
    filter_upwards [hlip] with x ⟨C, hC⟩
    refine ⟨C, ?_⟩
    filter_upwards [hC] with y hy
    refine le_trans ?_ hy
    rw [Real.norm_eq_abs, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  have him : ∀ᵐ x : ℂ, ∃ C : ℝ, ∀ᶠ y in 𝓝 x, ‖(f y).im - (f x).im‖ ≤ C * ‖y - x‖ := by
    filter_upwards [hlip] with x ⟨C, hC⟩
    refine ⟨C, ?_⟩
    filter_upwards [hC] with y hy
    refine le_trans ?_ hy
    rw [Real.norm_eq_abs, ← Complex.sub_im]
    exact Complex.abs_im_le_norm _
  -- Apply the real-valued core to each component.
  have hdre := ae_differentiableAt_real_of_ae_isLittleO (f := fun z => (f z).re) hre
  have hdim := ae_differentiableAt_real_of_ae_isLittleO (f := fun z => (f z).im) him
  filter_upwards [hdre, hdim] with x hxre hxim
  -- Assemble `equivRealProdCLM ∘ f = (re ∘ f, im ∘ f)` differentiable, then transfer back to `f`.
  have hprod : DifferentiableAt ℝ (fun z => ((f z).re, (f z).im)) x := hxre.prodMk hxim
  have hcomp : DifferentiableAt ℝ (Complex.equivRealProdCLM ∘ f) x := by
    have : (Complex.equivRealProdCLM ∘ f) = fun z => ((f z).re, (f z).im) := rfl
    rw [this]; exact hprod
  exact (Complex.equivRealProdCLM.comp_differentiableAt_iff).1 hcomp

end NoWanderingDomains.Stepanov
