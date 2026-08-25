/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.LengthArea.BishopMaster

/-!
# Per-height slice bounds and their integration in the transverse variable

The one-dimensional consequences of the master per-height Rengel estimates, and their
integration over the transverse variable, for a geometric `K`-quasiconformal homeomorphism
`f : ℂ → ℂ`:

* `qc_slice_eVariationOn_le_horizontal` / `_vertical` — at a height where the image-area
  profile is differentiable, the **total variation** of the complex slice over the window
  is at most `√(2K·|window|·Φ′)` (Cauchy–Schwarz from the contact-allowed master sum).
* `qc_slice_deriv_energy_le_horizontal` / `_vertical` — at the same heights, the
  **squared slice-derivative energy** is at most `2K·Φ′` (equipartition difference
  quotients + Fatou), with the straddle micro-lemma `tendsto_straddle_diffQuotient`.
* `qc_forward_energy_box_horizontal` / `_vertical` — the finite **box integrals** of the
  squared slice variation and the slice-derivative energy, obtained by integrating the two
  per-height bounds against the derivative mass of the monotone profile.
* `AxisRectModulusBound.ae_horizontal_slice_absolutelyContinuous` /
  `ae_vertical_slice_absolutelyContinuous` — almost every slice is **absolutely
  continuous** on every compact interval (the ε–δ criterion from the one-sided master
  family estimate).
* the one-dimensional glue `LipschitzWith.comp_absolutelyContinuousOnInterval` and
  `AbsolutelyContinuousOnInterval.eVariationOn_le_lintegral_deriv` (absolute continuity
  forces the variation to be dominated by the derivative integral — the "no singular part"
  conversion, via the fundamental theorem of calculus for absolutely continuous functions).

Together these discharge the two length–area residuals of the forward (easy) direction of
the reverse length–area theorem: the finite slice-energy box bounds and the
no-singular-part variation bound for almost every slice.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace NoWanderingDomains

/-! ## One-dimensional glue: absolute continuity and variation -/

/-- **Lipschitz post-composition preserves interval absolute continuity.** If `g` is
`L`-Lipschitz and `F` is absolutely continuous on `[a,b]`, then so is `g ∘ F`.

*Proof sketch.* Verify the ε–δ criterion `absolutelyContinuousOnInterval_iff` on both
sides: given `ε > 0`, take the `δ` that `F` provides for `ε/(L+1)`; for any admissible
finite disjoint interval family, `∑ dist (g (F uᵢ)) (g (F vᵢ)) ≤ L · ∑ dist (F uᵢ) (F vᵢ)`.
(As of this Mathlib pin the `AbsolutelyContinuousOnInterval` namespace has closure under
`add`/`neg`/`sub`/`smul`/`mul` and the statement that a Lipschitz *function* is absolutely
continuous, but no post-composition lemma.) -/
theorem _root_.LipschitzWith.comp_absolutelyContinuousOnInterval
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {g : X → Y} {L : ℝ≥0} (hg : LipschitzWith L g)
    {F : ℝ → X} {a b : ℝ} (hF : AbsolutelyContinuousOnInterval F a b) :
    AbsolutelyContinuousOnInterval (g ∘ F) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hF ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (L + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  calc ∑ i ∈ Finset.range E.1, dist ((g ∘ F) (E.2 i).1) ((g ∘ F) (E.2 i).2)
      ≤ ∑ i ∈ Finset.range E.1, (L : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) :=
        Finset.sum_le_sum fun i _ => hg.dist_le_mul _ _
    _ = (L : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (L : ℝ) * (ε / (L + 1)) :=
        mul_le_mul_of_nonneg_left (hδ' E hE hlen).le L.coe_nonneg
    _ < ((L : ℝ) + 1) * (ε / (L + 1)) :=
        mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
    _ = ε := by
        rw [mul_div_assoc']
        exact mul_div_cancel_left₀ _ (by positivity)

/-- **Absolute continuity forces the variation to be dominated by the derivative
integral.** For a real function `g` absolutely continuous on `[a,b]`,
`eVariationOn g (Icc a b) ≤ ∫⁻ x in [a,b], ‖deriv g x‖₊` — the "no singular part"
inequality. (Purely one-dimensional; no quasiconformal input. Together with the reverse
inequality for functions with a.e. derivatives, this characterizes absolute continuity
inside bounded variation — the Banach–Zaretsky circle of ideas.)

*Proof sketch.* `eVariationOn` is a supremum over monotone partitions `u : ℕ → ℝ` with
values in `Icc a b`. Per step,
`edist (g (u (k+1))) (g (u k)) = ENNReal.ofReal |∫ x in u k..u (k+1), deriv g x|` by the
fundamental theorem of calculus for absolutely continuous functions
(`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`, applied to the subinterval
restriction `hg.mono`); this is at most `∫⁻ x in Ioc (u k) (u (k+1)), ‖deriv g x‖₊`
(integrability from `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv`, then the
`ofReal`-integral/`lintegral` bridge and the triangle inequality for integrals). The
consecutive `Ioc`s are pairwise disjoint and contained in `Icc a b`, so the step bounds sum
below the full integral; take `iSup_le`. -/
theorem _root_.AbsolutelyContinuousOnInterval.eVariationOn_le_lintegral_deriv
    {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    eVariationOn g (Set.Icc a b) ≤ ∫⁻ x in Set.Icc a b, ‖deriv g x‖₊ := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, us⟩
  dsimp only
  have hstep : ∀ i : ℕ, edist (g (u (i + 1))) (g (u i))
      ≤ ∫⁻ x in Set.Ioc (u i) (u (i + 1)), ‖deriv g x‖₊ := by
    intro i
    have hui : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    have hsub : Set.uIcc (u i) (u (i + 1)) ⊆ Set.uIcc a b := by
      rw [Set.uIcc_of_le hui, Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc (us i).1 (us (i + 1)).2
    have hgi : AbsolutelyContinuousOnInterval g (u i) (u (i + 1)) := hg.mono hsub
    have hIoc : MeasureTheory.IntegrableOn (deriv g) (Set.Ioc (u i) (u (i + 1))) volume := by
      rw [← Set.uIoc_of_le hui]
      exact hgi.intervalIntegrable_deriv.def'
    calc edist (g (u (i + 1))) (g (u i))
        = ENNReal.ofReal |g (u (i + 1)) - g (u i)| := by
          rw [edist_dist, Real.dist_eq]
      _ = ENNReal.ofReal |∫ x in (u i)..(u (i + 1)), deriv g x| := by
          rw [hgi.integral_deriv_eq_sub]
      _ ≤ ENNReal.ofReal (∫ x in (u i)..(u (i + 1)), |deriv g x|) :=
          ENNReal.ofReal_le_ofReal
            (intervalIntegral.abs_integral_le_integral_abs hui)
      _ = ENNReal.ofReal (∫ x in Set.Ioc (u i) (u (i + 1)), |deriv g x|) := by
          rw [intervalIntegral.integral_of_le hui]
      _ = ∫⁻ x in Set.Ioc (u i) (u (i + 1)), ENNReal.ofReal |deriv g x| :=
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIoc.abs
            (Filter.Eventually.of_forall fun x => abs_nonneg _)
      _ = ∫⁻ x in Set.Ioc (u i) (u (i + 1)), ‖deriv g x‖₊ := by
          simp only [← Real.enorm_eq_ofReal_abs, enorm_eq_nnnorm]
  calc ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i))
      ≤ ∑ i ∈ Finset.range n, ∫⁻ x in Set.Ioc (u i) (u (i + 1)), ‖deriv g x‖₊ :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = ∫⁻ x in ⋃ i ∈ Finset.range n, Set.Ioc (u i) (u (i + 1)), ‖deriv g x‖₊ :=
        (MeasureTheory.lintegral_biUnion_finset
          (hu.pairwise_disjoint_on_Ioc_succ.set_pairwise _)
          (fun i _ => measurableSet_Ioc) _).symm
    _ ≤ ∫⁻ x in Set.Icc a b, ‖deriv g x‖₊ := by
        refine MeasureTheory.lintegral_mono_set (Set.iUnion₂_subset fun i _ x hx => ?_)
        exact ⟨(us i).1.trans hx.1.le, hx.2.trans (us (i + 1)).2⟩

/-- **Straddling difference quotients converge to the derivative.** If `h` has derivative
`v` at `x` and `p n ≤ x < q n` with `q n − p n → 0`, then
`‖h (q n) − h (p n)‖/(q n − p n) → ‖v‖`.

*Proof sketch.* From the little-o characterization of `HasDerivAt`
(`hasDerivAt_iff_isLittleO`): for large `n`,
`‖h (q n) − h (p n) − v·(q n − p n)‖ ≤ ε(q n − x) + ε(x − p n) = ε·(q n − p n)`, writing the
increment as the difference of the two one-sided increments from `x`; divide and squeeze. -/
theorem tendsto_straddle_diffQuotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ → E} {x : ℝ} {v : E} (hd : HasDerivAt h v x) {p q : ℕ → ℝ}
    (hpq : ∀ n, p n ≤ x ∧ x < q n)
    (hmesh : Filter.Tendsto (fun n => q n - p n) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ‖h (q n) - h (p n)‖ / (q n - p n)) Filter.atTop
      (nhds ‖v‖) := by
  have hd0 : ∀ n, 0 < q n - p n := fun n => sub_pos.mpr ((hpq n).1.trans_lt (hpq n).2)
  -- The straddling endpoints converge to `x`.
  have hp_lim : Filter.Tendsto p Filter.atTop (nhds x) := by
    have hlo : ∀ n, x - (q n - p n) ≤ p n := fun n => by
      have := (hpq n).2.le; linarith
    have hxlim : Filter.Tendsto (fun n => x - (q n - p n)) Filter.atTop (nhds x) := by
      simpa using tendsto_const_nhds.sub hmesh
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hxlim tendsto_const_nhds hlo
      fun n => (hpq n).1
  have hq_lim : Filter.Tendsto q Filter.atTop (nhds x) := by
    have hhi : ∀ n, q n ≤ x + (q n - p n) := fun n => by
      have := (hpq n).1; linarith
    have hxlim : Filter.Tendsto (fun n => x + (q n - p n)) Filter.atTop (nhds x) := by
      simpa using tendsto_const_nhds.add hmesh
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hxlim
      (fun n => (hpq n).2.le) hhi
  -- The normalized straddling error tends to `0`.
  have key : Filter.Tendsto
      (fun n => ‖h (q n) - h (p n) - (q n - p n) • v‖ / (q n - p n))
      Filter.atTop (nhds 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    have hlo := (hasDerivAt_iff_isLittleO.mp hd).def (show (0 : ℝ) < ε / 2 by positivity)
    filter_upwards [hp_lim.eventually hlo, hq_lim.eventually hlo] with n hpn hqn
    have hid : h (q n) - h (p n) - (q n - p n) • v
        = (h (q n) - h x - (q n - x) • v) - (h (p n) - h x - (p n - x) • v) := by
      have hsmul : (q n - p n) • v = (q n - x) • v - (p n - x) • v := by
        rw [← sub_smul]; ring_nf
      rw [hsmul]; abel
    have hq' : ‖q n - x‖ = q n - x := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [(hpq n).2.le])]
    have hp' : ‖p n - x‖ = x - p n := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [(hpq n).1]), neg_sub]
    have hb : ‖h (q n) - h (p n) - (q n - p n) • v‖ ≤ ε / 2 * (q n - p n) := by
      rw [hid]
      calc ‖(h (q n) - h x - (q n - x) • v) - (h (p n) - h x - (p n - x) • v)‖
          ≤ ‖h (q n) - h x - (q n - x) • v‖ + ‖h (p n) - h x - (p n - x) • v‖ :=
            norm_sub_le _ _
        _ ≤ ε / 2 * ‖q n - x‖ + ε / 2 * ‖p n - x‖ := add_le_add hqn hpn
        _ = ε / 2 * (q n - p n) := by rw [hq', hp']; ring
    have hquot : ‖h (q n) - h (p n) - (q n - p n) • v‖ / (q n - p n) ≤ ε / 2 := by
      rw [div_le_iff₀ (hd0 n)]
      linarith [hb]
    have hquot0 : 0 ≤ ‖h (q n) - h (p n) - (q n - p n) • v‖ / (q n - p n) :=
      div_nonneg (norm_nonneg _) (hd0 n).le
    rw [Real.norm_eq_abs, abs_of_nonneg hquot0]
    linarith
  -- Squeeze the distance to `‖v‖` by the normalized error.
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) key
  rw [Real.dist_eq]
  have hd0n := hd0 n
  have hv : ‖v‖ = ‖(q n - p n) • v‖ / (q n - p n) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd0n, mul_comm, mul_div_assoc,
      div_self hd0n.ne', mul_one]
  rw [hv, div_sub_div_same, abs_div, abs_of_pos hd0n]
  gcongr
  exact abs_norm_sub_norm_le _ _

/-! ## Per-height slice bounds -/

/-- **Per-height slice variation bound (horizontal).** At a height `y > σ` where the
horizontal image-area profile of the window `[α,β]` is differentiable, the total variation
of the complex slice `x ↦ f ⟨x, y⟩` over `[α,β]` is at most `√(2K·(β−α)·Φ′(y))`.

*Proof sketch.* `eVariationOn` is a supremum over monotone partitions `(n, u)` with values
in `Icc α β`. Discard the degenerate steps (`u i = u (i+1)`, zero `edist`); enumerate the
nondegenerate steps in increasing order (`Finset.orderIsoOfFin`), producing an ordered
contact-allowed family `(A k, B k)` inside `[α,β]` — contacts arise where consecutive
partition points coincide, which the master estimate tolerates. Cauchy–Schwarz with the
splitting `r_k = √w_k · (r_k/√w_k)` gives
`∑ r_k ≤ √(∑ w_k) · √(∑ r_k²/w_k) ≤ √(β−α) · √(2K·Φ′(y))`
(the master sum `qc_master_sum_sq_div_le_horizontal`; `∑ w_k` telescopes below `β−α`).
Convert to `ℝ≥0∞` (`edist_dist`, `ENNReal.ofReal` of a finite nonnegative sum) and take
`iSup_le`. Nonnegativity of `Φ′(y)` comes from monotonicity of the profile
(`Monotone.ae_hasDerivAt_deriv`-style slope argument at the differentiability point).
-/
theorem qc_slice_eVariationOn_le_horizontal {f : ℂ → ℂ} {K : ℝ} (hf : AxisRectModulusBound f K)
    {α β σ y : ℝ} (hσy : σ < y)
    (hΦ : DifferentiableAt ℝ (imageAreaProfileY f α β σ) y) :
    eVariationOn (fun x : ℝ => f ⟨x, y⟩) (Set.Icc α β)
      ≤ ENNReal.ofReal
          (Real.sqrt (2 * K * (β - α) * deriv (imageAreaProfileY f α β σ) y)) := by
  classical
  refine iSup_le ?_
  rintro ⟨n, u, hu, us⟩
  dsimp only
  have hαβ : α ≤ β := (us 0).1.trans (us 0).2
  -- discard the degenerate steps
  set S : Finset ℕ := (Finset.range n).filter (fun i => u i < u (i + 1)) with hS
  have hsum0 : ∑ i ∈ Finset.range n, edist (f ⟨u (i + 1), y⟩) (f ⟨u i, y⟩)
      = ∑ i ∈ S, edist (f ⟨u (i + 1), y⟩) (f ⟨u i, y⟩) := by
    refine (Finset.sum_filter_of_ne fun i hi hne => ?_).symm
    by_contra hnot
    have heq : u i = u (i + 1) := le_antisymm (hu (Nat.le_succ i)) (not_lt.mp hnot)
    exact hne (by rw [heq, edist_self])
  rw [hsum0]
  -- convert to a real chord sum
  have hedist : ∀ i ∈ S, edist (f ⟨u (i + 1), y⟩) (f ⟨u i, y⟩)
      = ENNReal.ofReal ‖f ⟨u (i + 1), y⟩ - f ⟨u i, y⟩‖ := fun i _ => by
    rw [edist_dist, dist_eq_norm]
  rw [Finset.sum_congr rfl hedist,
    ← ENNReal.ofReal_sum_of_nonneg fun i _ => norm_nonneg _]
  refine ENNReal.ofReal_le_ofReal ?_
  -- enumerate the nondegenerate steps in increasing order
  set e : Fin S.card ↪o ℕ := S.orderEmbOfFin rfl with he
  have heS : ∀ k, e k ∈ S := fun k => Finset.orderEmbOfFin_mem S rfl k
  have hreidx : ∀ g : ℕ → ℝ, ∑ i ∈ S, g i = ∑ k : Fin S.card, g (e k) := by
    intro g
    calc ∑ i ∈ S, g i
        = ∑ i ∈ Finset.map (S.orderEmbOfFin rfl).toEmbedding Finset.univ, g i :=
          (Finset.sum_congr (Finset.map_orderEmbOfFin_univ S rfl) fun _ _ => rfl).symm
      _ = ∑ k : Fin S.card, g (S.orderEmbOfFin rfl k) := Finset.sum_map _ _ _
      _ = ∑ k : Fin S.card, g (e k) := by rw [he]
  have hAB : ∀ k : Fin S.card, u (e k) < u (e k + 1) := fun k =>
    (Finset.mem_filter.mp (heS k)).2
  have hord : ∀ k l : Fin S.card, k < l → u (e k + 1) ≤ u (e l) := fun k l hkl =>
    hu (Nat.succ_le_of_lt (e.strictMono hkl))
  have hmem : ∀ k : Fin S.card, α ≤ u (e k) ∧ u (e k + 1) ≤ β := fun k =>
    ⟨(us (e k)).1, (us (e k + 1)).2⟩
  have hmaster := qc_master_sum_sq_div_le_horizontal
    (A := fun k => u (e k)) (B := fun k => u (e k + 1)) hf hσy hΦ hAB hord hmem
  rw [hreidx]
  -- Cauchy–Schwarz with the splitting `r = √w · (r/√w)`
  have hsplit : ∀ k : Fin S.card, ‖f ⟨u (e k + 1), y⟩ - f ⟨u (e k), y⟩‖
      = Real.sqrt (u (e k + 1) - u (e k))
          * (‖f ⟨u (e k + 1), y⟩ - f ⟨u (e k), y⟩‖
              / Real.sqrt (u (e k + 1) - u (e k))) := by
    intro k
    rw [mul_comm, div_mul_cancel₀]
    exact (Real.sqrt_pos.mpr (sub_pos.mpr (hAB k))).ne'
  rw [Finset.sum_congr rfl fun k _ => hsplit k]
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun k => Real.sqrt (u (e k + 1) - u (e k)))
    (fun k => ‖f ⟨u (e k + 1), y⟩ - f ⟨u (e k), y⟩‖
      / Real.sqrt (u (e k + 1) - u (e k)))
  refine hCS.trans ?_
  -- identify the two quadratic sums
  have hw : ∀ k : Fin S.card, Real.sqrt (u (e k + 1) - u (e k)) ^ 2
      = u (e k + 1) - u (e k) := fun k =>
    Real.sq_sqrt (sub_pos.mpr (hAB k)).le
  have hr : ∀ k : Fin S.card,
      (‖f ⟨u (e k + 1), y⟩ - f ⟨u (e k), y⟩‖ / Real.sqrt (u (e k + 1) - u (e k))) ^ 2
        = ‖f ⟨u (e k + 1), y⟩ - f ⟨u (e k), y⟩‖ ^ 2 / (u (e k + 1) - u (e k)) :=
    fun k => by rw [div_pow, hw k]
  rw [Finset.sum_congr rfl fun k _ => hw k, Finset.sum_congr rfl fun k _ => hr k]
  -- the total width telescopes below `β − α`
  have hwsum : ∑ k : Fin S.card, (u (e k + 1) - u (e k)) ≤ β - α := by
    have h1 := hreidx fun i => u (i + 1) - u i
    have h2 : ∑ i ∈ S, (u (i + 1) - u i) ≤ ∑ i ∈ Finset.range n, (u (i + 1) - u i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun i _ _ => sub_nonneg.mpr (hu (Nat.le_succ i))
    rw [Finset.sum_range_sub (fun i => u i)] at h2
    have h3 : u n - u 0 ≤ β - α := sub_le_sub (us n).2 (us 0).1
    rw [← h1]; linarith
  -- assemble the square roots
  calc Real.sqrt (∑ k : Fin S.card, (u (e k + 1) - u (e k)))
        * Real.sqrt (∑ k : Fin S.card,
            ‖f ⟨u (e k + 1), y⟩ - f ⟨u (e k), y⟩‖ ^ 2 / (u (e k + 1) - u (e k)))
      ≤ Real.sqrt (β - α)
          * Real.sqrt (2 * K * deriv (imageAreaProfileY f α β σ) y) :=
        mul_le_mul (Real.sqrt_le_sqrt hwsum) (Real.sqrt_le_sqrt hmaster)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((β - α) * (2 * K * deriv (imageAreaProfileY f α β σ) y)) :=
        (Real.sqrt_mul (sub_nonneg.mpr hαβ) _).symm
    _ = Real.sqrt (2 * K * (β - α) * deriv (imageAreaProfileY f α β σ) y) := by
        congr 1
        ring

/-- **Per-height slice variation bound (vertical).** Mirror of
`qc_slice_eVariationOn_le_horizontal`: at an abscissa `x > α` where the vertical
image-area profile of the window `[σ,τ]` is differentiable, the total variation of the
complex slice `v ↦ f ⟨x, v⟩` over `[σ,τ]` is at most `√(2K·(τ−σ)·Ψ′(x))`. -/
theorem qc_slice_eVariationOn_le_vertical {f : ℂ → ℂ} {K : ℝ} (hf : AxisRectModulusBound f K)
    {α σ τ x : ℝ} (hαx : α < x)
    (hΨ : DifferentiableAt ℝ (imageAreaProfileX f α σ τ) x) :
    eVariationOn (fun v : ℝ => f ⟨x, v⟩) (Set.Icc σ τ)
      ≤ ENNReal.ofReal
          (Real.sqrt (2 * K * (τ - σ) * deriv (imageAreaProfileX f α σ τ) x)) := by
  classical
  refine iSup_le ?_
  rintro ⟨n, u, hu, us⟩
  dsimp only
  have hστ : σ ≤ τ := (us 0).1.trans (us 0).2
  -- discard the degenerate steps
  set Sf : Finset ℕ := (Finset.range n).filter (fun i => u i < u (i + 1)) with hSf
  have hsum0 : ∑ i ∈ Finset.range n, edist (f ⟨x, u (i + 1)⟩) (f ⟨x, u i⟩)
      = ∑ i ∈ Sf, edist (f ⟨x, u (i + 1)⟩) (f ⟨x, u i⟩) := by
    refine (Finset.sum_filter_of_ne fun i hi hne => ?_).symm
    by_contra hnot
    have heq : u i = u (i + 1) := le_antisymm (hu (Nat.le_succ i)) (not_lt.mp hnot)
    exact hne (by rw [heq, edist_self])
  rw [hsum0]
  -- convert to a real chord sum
  have hedist : ∀ i ∈ Sf, edist (f ⟨x, u (i + 1)⟩) (f ⟨x, u i⟩)
      = ENNReal.ofReal ‖f ⟨x, u (i + 1)⟩ - f ⟨x, u i⟩‖ := fun i _ => by
    rw [edist_dist, dist_eq_norm]
  rw [Finset.sum_congr rfl hedist,
    ← ENNReal.ofReal_sum_of_nonneg fun i _ => norm_nonneg _]
  refine ENNReal.ofReal_le_ofReal ?_
  -- enumerate the nondegenerate steps in increasing order
  set e : Fin Sf.card ↪o ℕ := Sf.orderEmbOfFin rfl with he
  have heS : ∀ k, e k ∈ Sf := fun k => Finset.orderEmbOfFin_mem Sf rfl k
  have hreidx : ∀ g : ℕ → ℝ, ∑ i ∈ Sf, g i = ∑ k : Fin Sf.card, g (e k) := by
    intro g
    calc ∑ i ∈ Sf, g i
        = ∑ i ∈ Finset.map (Sf.orderEmbOfFin rfl).toEmbedding Finset.univ, g i :=
          (Finset.sum_congr (Finset.map_orderEmbOfFin_univ Sf rfl) fun _ _ => rfl).symm
      _ = ∑ k : Fin Sf.card, g (Sf.orderEmbOfFin rfl k) := Finset.sum_map _ _ _
      _ = ∑ k : Fin Sf.card, g (e k) := by rw [he]
  have hST : ∀ k : Fin Sf.card, u (e k) < u (e k + 1) := fun k =>
    (Finset.mem_filter.mp (heS k)).2
  have hord : ∀ k l : Fin Sf.card, k < l → u (e k + 1) ≤ u (e l) := fun k l hkl =>
    hu (Nat.succ_le_of_lt (e.strictMono hkl))
  have hmem : ∀ k : Fin Sf.card, σ ≤ u (e k) ∧ u (e k + 1) ≤ τ := fun k =>
    ⟨(us (e k)).1, (us (e k + 1)).2⟩
  have hmaster := qc_master_sum_sq_div_le_vertical
    (S := fun k => u (e k)) (T := fun k => u (e k + 1)) hf hαx hΨ hST hord hmem
  rw [hreidx]
  -- Cauchy–Schwarz with the splitting `r = √w · (r/√w)`
  have hsplit : ∀ k : Fin Sf.card, ‖f ⟨x, u (e k + 1)⟩ - f ⟨x, u (e k)⟩‖
      = Real.sqrt (u (e k + 1) - u (e k))
          * (‖f ⟨x, u (e k + 1)⟩ - f ⟨x, u (e k)⟩‖
              / Real.sqrt (u (e k + 1) - u (e k))) := by
    intro k
    rw [mul_comm, div_mul_cancel₀]
    exact (Real.sqrt_pos.mpr (sub_pos.mpr (hST k))).ne'
  rw [Finset.sum_congr rfl fun k _ => hsplit k]
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun k => Real.sqrt (u (e k + 1) - u (e k)))
    (fun k => ‖f ⟨x, u (e k + 1)⟩ - f ⟨x, u (e k)⟩‖
      / Real.sqrt (u (e k + 1) - u (e k)))
  refine hCS.trans ?_
  -- identify the two quadratic sums
  have hw : ∀ k : Fin Sf.card, Real.sqrt (u (e k + 1) - u (e k)) ^ 2
      = u (e k + 1) - u (e k) := fun k =>
    Real.sq_sqrt (sub_pos.mpr (hST k)).le
  have hr : ∀ k : Fin Sf.card,
      (‖f ⟨x, u (e k + 1)⟩ - f ⟨x, u (e k)⟩‖ / Real.sqrt (u (e k + 1) - u (e k))) ^ 2
        = ‖f ⟨x, u (e k + 1)⟩ - f ⟨x, u (e k)⟩‖ ^ 2 / (u (e k + 1) - u (e k)) :=
    fun k => by rw [div_pow, hw k]
  rw [Finset.sum_congr rfl fun k _ => hw k, Finset.sum_congr rfl fun k _ => hr k]
  -- the total width telescopes below `τ − σ`
  have hwsum : ∑ k : Fin Sf.card, (u (e k + 1) - u (e k)) ≤ τ - σ := by
    have h1 := hreidx fun i => u (i + 1) - u i
    have h2 : ∑ i ∈ Sf, (u (i + 1) - u i) ≤ ∑ i ∈ Finset.range n, (u (i + 1) - u i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun i _ _ => sub_nonneg.mpr (hu (Nat.le_succ i))
    rw [Finset.sum_range_sub (fun i => u i)] at h2
    have h3 : u n - u 0 ≤ τ - σ := sub_le_sub (us n).2 (us 0).1
    rw [← h1]; linarith
  -- assemble the square roots
  calc Real.sqrt (∑ k : Fin Sf.card, (u (e k + 1) - u (e k)))
        * Real.sqrt (∑ k : Fin Sf.card,
            ‖f ⟨x, u (e k + 1)⟩ - f ⟨x, u (e k)⟩‖ ^ 2 / (u (e k + 1) - u (e k)))
      ≤ Real.sqrt (τ - σ)
          * Real.sqrt (2 * K * deriv (imageAreaProfileX f α σ τ) x) :=
        mul_le_mul (Real.sqrt_le_sqrt hwsum) (Real.sqrt_le_sqrt hmaster)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((τ - σ) * (2 * K * deriv (imageAreaProfileX f α σ τ) x)) :=
        (Real.sqrt_mul (sub_nonneg.mpr hστ) _).symm
    _ = Real.sqrt (2 * K * (τ - σ) * deriv (imageAreaProfileX f α σ τ) x) := by
        congr 1
        ring

/-- **Per-height slice-derivative energy bound (horizontal).** At a height `y > σ` where
the horizontal image-area profile of the window `[α,β] ⊇ [a,b]` is differentiable, the
squared energy of the slice derivative over `[a,b]` is at most `2K·Φ′(y)`.

*Proof sketch.* Let `h(x) := f ⟨x, y⟩`; it has finite variation on `[α,β]` by
`qc_slice_eVariationOn_le_horizontal`, hence is differentiable at a.e. `x ∈ [a,b]`
(one-dimensional `LocallyBoundedVariationOn.ae_differentiableAt` on the enclosing window;
interior points of `[α,β]` cover `[a,b]` up to a null set). For `m ≥ 1` equipartition
`[a,b]` at mesh `h_m = (b−a)/m` and form the measurable step function `G_m` whose value on
the `j`-th subinterval `[x_j, x_{j+1})` is the chord quotient `‖h x_{j+1} − h x_j‖/h_m`:
* the equipartition is an ordered contact-allowed family inside `[α,β]`, so the master sum
  (`qc_master_sum_sq_div_le_horizontal`) bounds
  `∫⁻ x in [a,b], (G_m x)² = ∑_j ofReal (‖h x_{j+1} − h x_j‖²/h_m) ≤ ofReal (2K·Φ′(y))`
  (disjoint `Ico`s of measure `h_m`, `lintegral_indicator`);
* at a.e. `x`, the straddling quotient converges: `G_m x → ‖deriv h x‖`
  (`tendsto_straddle_diffQuotient` with `p m := x_{j(m)}`, `q m := x_{j(m)+1}`);
* Fatou (`MeasureTheory.lintegral_liminf_le`; each `G_m` is a finite sum of indicator
  functions, hence measurable) transfers the uniform bound to the limit; the endpoint `b`
  and the non-differentiability set are null.
-/
theorem qc_slice_deriv_energy_le_horizontal {f : ℂ → ℂ} {K : ℝ} (hf : AxisRectModulusBound f K)
    {α β σ y : ℝ} (hσy : σ < y)
    (hΦ : DifferentiableAt ℝ (imageAreaProfileY f α β σ) y)
    {a b : ℝ} (hαa : α ≤ a) (hbβ : b ≤ β) :
    ∫⁻ x in Set.Icc a b, (‖deriv (fun u : ℝ => f ⟨u, y⟩) x‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal (2 * K * deriv (imageAreaProfileY f α β σ) y) := by
  classical
  rcases le_or_gt b a with hba | hab
  · -- degenerate interval: the integration domain is null
    have h0 : volume (Set.Icc a b) = 0 := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_eq_zero.mpr (by linarith)
    rw [MeasureTheory.setLIntegral_measure_zero _ _ h0]
    exact zero_le
  have hαβ : α ≤ β := hαa.trans (hab.le.trans hbβ)
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℂ, h = fun u : ℝ => f ⟨u, y⟩ := ⟨_, rfl⟩
  have happ : ∀ z : ℝ, h z = f ⟨z, y⟩ := fun z => by rw [hh]
  rw [← hh]
  -- the slice has bounded variation on the window, hence is a.e. differentiable
  have hbv : BoundedVariationOn h (Set.uIcc α β) := by
    rw [Set.uIcc_of_le hαβ, hh]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (qc_slice_eVariationOn_le_horizontal hf hσy hΦ)
  have hdiff : ∀ᵐ x : ℝ, x ∈ Set.uIcc α β → DifferentiableAt ℝ h x :=
    hbv.ae_differentiableAt_of_mem_uIcc
  -- the equipartition grid at scale `m`
  set δ : ℕ → ℝ := fun m => (b - a) / (m + 1) with hδ
  have hδpos : ∀ m : ℕ, 0 < δ m := fun m => div_pos (sub_pos.mpr hab) (by positivity)
  set X : ℕ → ℕ → ℝ := fun m j => a + j * δ m with hX
  have hXd : ∀ m j, X m (j + 1) - X m j = δ m := fun m j => by
    simp only [hX]; push_cast; ring
  have hXmono : ∀ m, Monotone (X m) := by
    intro m i i' hii'
    simp only [hX]
    have := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hii' : (i : ℝ) ≤ i') (hδpos m).le
    linarith
  have hX0 : ∀ m, X m 0 = a := fun m => by simp [hX]
  have hXlast : ∀ m : ℕ, X m (m + 1) = b := by
    intro m
    have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
    simp only [hX, hδ]
    push_cast
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hm]
    ring
  -- the squared chord-quotient step functions
  set G : ℕ → ℝ → ℝ≥0∞ := fun m x => ∑ j ∈ Finset.range (m + 1),
      (Set.Ico (X m j) (X m (j + 1))).indicator
        (fun _ => ENNReal.ofReal ((‖h (X m (j + 1)) - h (X m j)‖ / δ m) ^ 2)) x with hG
  have hGmeas : ∀ m, Measurable (G m) := fun m =>
    Finset.measurable_sum _ fun j _ => measurable_const.indicator measurableSet_Ico
  -- the master estimate bounds each step-function energy
  have hGbound : ∀ m : ℕ, ∫⁻ x in Set.Icc a b, G m x
      ≤ ENNReal.ofReal (2 * K * deriv (imageAreaProfileY f α β σ) y) := by
    intro m
    have hIco_sub : ∀ j ∈ Finset.range (m + 1),
        Set.Ico (X m j) (X m (j + 1)) ⊆ Set.Icc a b := by
      intro j hj z hz
      have h1 : a ≤ X m j := by
        have := hXmono m (Nat.zero_le j)
        rwa [hX0 m] at this
      have h2 : X m (j + 1) ≤ b := by
        have := hXmono m (Nat.succ_le_succ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
        rwa [hXlast m] at this
      exact ⟨h1.trans hz.1, hz.2.le.trans h2⟩
    have hcalc : ∫⁻ x in Set.Icc a b, G m x
        = ∑ j ∈ Finset.range (m + 1),
            ENNReal.ofReal ((‖h (X m (j + 1)) - h (X m j)‖ / δ m) ^ 2)
              * ENNReal.ofReal (δ m) := by
      simp only [hG]
      rw [MeasureTheory.lintegral_finsetSum _
        (fun j _ => measurable_const.indicator measurableSet_Ico)]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [MeasureTheory.lintegral_indicator measurableSet_Ico,
        MeasureTheory.Measure.restrict_restrict measurableSet_Ico,
        Set.inter_eq_self_of_subset_left (hIco_sub j hj),
        MeasureTheory.setLIntegral_const, Real.volume_Ico, hXd]
    rw [hcalc]
    have hterm : ∀ j ∈ Finset.range (m + 1),
        ENNReal.ofReal ((‖h (X m (j + 1)) - h (X m j)‖ / δ m) ^ 2)
            * ENNReal.ofReal (δ m)
          = ENNReal.ofReal (‖h (X m (j + 1)) - h (X m j)‖ ^ 2 / δ m) := by
      intro j _
      rw [← ENNReal.ofReal_mul (sq_nonneg (‖h (X m (j + 1)) - h (X m j)‖ / δ m))]
      congr 1
      rw [div_pow]
      field_simp
    have hsum_or : ENNReal.ofReal
        (∑ j ∈ Finset.range (m + 1), ‖h (X m (j + 1)) - h (X m j)‖ ^ 2 / δ m)
        = ∑ j ∈ Finset.range (m + 1),
            ENNReal.ofReal (‖h (X m (j + 1)) - h (X m j)‖ ^ 2 / δ m) :=
      ENNReal.ofReal_sum_of_nonneg fun j _ => div_nonneg (sq_nonneg _) (hδpos m).le
    rw [Finset.sum_congr rfl hterm, ← hsum_or]
    refine ENNReal.ofReal_le_ofReal ?_
    -- the equipartition is an ordered contact-allowed family
    have hAB : ∀ k : Fin (m + 1), X m (k : ℕ) < X m ((k : ℕ) + 1) := by
      intro k
      have h1 := hXd m (k : ℕ)
      have h2 := hδpos m
      linarith
    have hord : ∀ k l : Fin (m + 1), k < l → X m ((k : ℕ) + 1) ≤ X m (l : ℕ) :=
      fun k l hkl => hXmono m (Nat.succ_le_of_lt hkl)
    have hmem : ∀ k : Fin (m + 1), α ≤ X m (k : ℕ) ∧ X m ((k : ℕ) + 1) ≤ β := by
      intro k
      constructor
      · refine hαa.trans ?_
        have := hXmono m (Nat.zero_le (k : ℕ))
        rwa [hX0 m] at this
      · refine le_trans ?_ hbβ
        have := hXmono m (Nat.succ_le_of_lt k.isLt)
        rwa [hXlast m] at this
    have hmaster := qc_master_sum_sq_div_le_horizontal
      (A := fun k : Fin (m + 1) => X m (k : ℕ))
      (B := fun k : Fin (m + 1) => X m ((k : ℕ) + 1)) hf hσy hΦ hAB hord hmem
    calc ∑ j ∈ Finset.range (m + 1), ‖h (X m (j + 1)) - h (X m j)‖ ^ 2 / δ m
        = ∑ k : Fin (m + 1), ‖f ⟨X m ((k : ℕ) + 1), y⟩ - f ⟨X m (k : ℕ), y⟩‖ ^ 2
            / (X m ((k : ℕ) + 1) - X m (k : ℕ)) := by
          rw [← Fin.sum_univ_eq_sum_range
            (fun j => ‖h (X m (j + 1)) - h (X m j)‖ ^ 2 / δ m) (m + 1)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [happ, happ, hXd]
      _ ≤ 2 * K * deriv (imageAreaProfileY f α β σ) y := hmaster
  -- pointwise convergence of the step functions at differentiability points
  have hpoint : ∀ x ∈ Set.Ico a b, DifferentiableAt ℝ h x →
      Filter.Tendsto (fun m => G m x) Filter.atTop
        (nhds ((‖deriv h x‖₊ : ℝ≥0∞) ^ 2)) := by
    intro x hx hdx
    have hxa : 0 ≤ x - a := sub_nonneg.mpr hx.1
    -- the straddling grid index at scale `m`
    have hidx : ∀ m : ℕ, ∃ jm : ℕ, jm < m + 1 ∧ X m jm ≤ x ∧ x < X m (jm + 1) := by
      intro m
      refine ⟨⌊(x - a) / δ m⌋₊, ?_, ?_, ?_⟩
      · have h1 : (x - a) / δ m < ((m + 1 : ℕ) : ℝ) := by
          rw [div_lt_iff₀ (hδpos m)]
          have h2 : ((m + 1 : ℕ) : ℝ) * δ m = b - a := by
            have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
            simp only [hδ]
            push_cast
            rw [← mul_div_assoc]
            exact mul_div_cancel_left₀ _ hm
          rw [h2]
          linarith [hx.2]
        exact (Nat.floor_lt (div_nonneg hxa (hδpos m).le)).mpr h1
      · have h1 : (⌊(x - a) / δ m⌋₊ : ℝ) ≤ (x - a) / δ m :=
          Nat.floor_le (div_nonneg hxa (hδpos m).le)
        have h2 : (⌊(x - a) / δ m⌋₊ : ℝ) * δ m ≤ x - a := (le_div_iff₀ (hδpos m)).mp h1
        simp only [hX]
        linarith
      · have h1 : (x - a) / δ m < (⌊(x - a) / δ m⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        have h2 : x - a < ((⌊(x - a) / δ m⌋₊ : ℝ) + 1) * δ m :=
          (div_lt_iff₀ (hδpos m)).mp h1
        simp only [hX]
        push_cast
        linarith
    choose j hjm hpx hxq using hidx
    -- at `x` the step function reduces to the straddling chord quotient
    have hGx : ∀ m, G m x
        = ENNReal.ofReal ((‖h (X m (j m + 1)) - h (X m (j m))‖ / δ m) ^ 2) := by
      intro m
      simp only [hG]
      have hzero : ∀ k ∈ Finset.range (m + 1), k ≠ j m →
          (Set.Ico (X m k) (X m (k + 1))).indicator
            (fun _ => ENNReal.ofReal ((‖h (X m (k + 1)) - h (X m k)‖ / δ m) ^ 2)) x
            = 0 := by
        intro k _ hkj
        rw [Set.indicator_of_notMem]
        rintro ⟨hk1, hk2⟩
        rcases lt_or_gt_of_ne hkj with hlt | hgt
        · have hle : X m (k + 1) ≤ X m (j m) := hXmono m (Nat.succ_le_of_lt hlt)
          exact lt_irrefl x (hk2.trans_le (hle.trans (hpx m)))
        · have hle : X m (j m + 1) ≤ X m k := hXmono m (Nat.succ_le_of_lt hgt)
          exact lt_irrefl x ((hxq m).trans_le (hle.trans hk1))
      rw [Finset.sum_eq_single_of_mem (j m) (Finset.mem_range.mpr (hjm m)) hzero,
        Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hpx m, hxq m⟩)]
    -- the mesh collapses
    have hδlim : Filter.Tendsto δ Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (b - a) * (1 / ((n : ℝ) + 1)))
          Filter.atTop (nhds 0) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (b - a)
      refine h1.congr fun n => ?_
      simp only [hδ, mul_one_div]
    have hmesh : Filter.Tendsto (fun m => X m (j m + 1) - X m (j m))
        Filter.atTop (nhds 0) := by
      simpa only [hXd] using hδlim
    -- the straddle lemma
    have hstr := tendsto_straddle_diffQuotient hdx.hasDerivAt
      (p := fun m => X m (j m)) (q := fun m => X m (j m + 1))
      (fun m => ⟨hpx m, hxq m⟩) hmesh
    have hstr2 : Filter.Tendsto
        (fun m => ENNReal.ofReal ((‖h (X m (j m + 1)) - h (X m (j m))‖ / δ m) ^ 2))
        Filter.atTop (nhds (ENNReal.ofReal (‖deriv h x‖ ^ 2))) :=
      ENNReal.tendsto_ofReal
        (((hstr.congr fun m => by rw [hXd]).pow 2))
    have hval : ENNReal.ofReal (‖deriv h x‖ ^ 2) = (‖deriv h x‖₊ : ℝ≥0∞) ^ 2 := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
    rw [← hval]
    exact hstr2.congr fun m => (hGx m).symm
  -- almost-everywhere comparison with the liminf, then Fatou
  have h_ae : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)),
      (‖deriv h x‖₊ : ℝ≥0∞) ^ 2 ≤ Filter.liminf (fun m => G m x) Filter.atTop := by
    have h1 : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), x ∈ Set.Icc a b :=
      MeasureTheory.ae_restrict_mem measurableSet_Icc
    have h2 : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), x ≠ b :=
      MeasureTheory.ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
    have h3 : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)),
        x ∈ Set.uIcc α β → DifferentiableAt ℝ h x :=
      MeasureTheory.ae_restrict_of_ae hdiff
    filter_upwards [h1, h2, h3] with x hx hxb hxd
    have hx' : x ∈ Set.Ico a b := ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩
    have hdx : DifferentiableAt ℝ h x := hxd (by
      rw [Set.uIcc_of_le hαβ]
      exact ⟨hαa.trans hx.1, hx.2.trans hbβ⟩)
    exact le_of_eq ((hpoint x hx' hdx).liminf_eq).symm
  calc ∫⁻ x in Set.Icc a b, (‖deriv h x‖₊ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ x in Set.Icc a b, Filter.liminf (fun m => G m x) Filter.atTop :=
        MeasureTheory.lintegral_mono_ae h_ae
    _ ≤ Filter.liminf (fun m => ∫⁻ x in Set.Icc a b, G m x) Filter.atTop :=
        MeasureTheory.lintegral_liminf_le hGmeas
    _ ≤ ENNReal.ofReal (2 * K * deriv (imageAreaProfileY f α β σ) y) :=
        (Filter.liminf_le_liminf (Filter.Eventually.of_forall hGbound)).trans_eq
          (Filter.liminf_const _)

/-- **Per-height slice-derivative energy bound (vertical).** Mirror of
`qc_slice_deriv_energy_le_horizontal` for the vertical slice `v ↦ f ⟨x, v⟩` over
`[s,t] ⊆ [σ,τ]` at an abscissa `x > α` where the vertical image-area profile is
differentiable. -/
theorem qc_slice_deriv_energy_le_vertical {f : ℂ → ℂ} {K : ℝ} (hf : AxisRectModulusBound f K)
    {α σ τ x : ℝ} (hαx : α < x)
    (hΨ : DifferentiableAt ℝ (imageAreaProfileX f α σ τ) x)
    {s t : ℝ} (hσs : σ ≤ s) (htτ : t ≤ τ) :
    ∫⁻ v in Set.Icc s t, (‖deriv (fun u : ℝ => f ⟨x, u⟩) v‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal (2 * K * deriv (imageAreaProfileX f α σ τ) x) := by
  classical
  rcases le_or_gt t s with hts | hst
  · -- degenerate interval: the integration domain is null
    have h0 : volume (Set.Icc s t) = 0 := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_eq_zero.mpr (by linarith)
    rw [MeasureTheory.setLIntegral_measure_zero _ _ h0]
    exact zero_le
  have hστ : σ ≤ τ := hσs.trans (hst.le.trans htτ)
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℂ, h = fun u : ℝ => f ⟨x, u⟩ := ⟨_, rfl⟩
  have happ : ∀ z : ℝ, h z = f ⟨x, z⟩ := fun z => by rw [hh]
  rw [← hh]
  -- the slice has bounded variation on the window, hence is a.e. differentiable
  have hbv : BoundedVariationOn h (Set.uIcc σ τ) := by
    rw [Set.uIcc_of_le hστ, hh]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (qc_slice_eVariationOn_le_vertical hf hαx hΨ)
  have hdiff : ∀ᵐ v : ℝ, v ∈ Set.uIcc σ τ → DifferentiableAt ℝ h v :=
    hbv.ae_differentiableAt_of_mem_uIcc
  -- the equipartition grid at scale `m`
  set δ : ℕ → ℝ := fun m => (t - s) / (m + 1) with hδ
  have hδpos : ∀ m : ℕ, 0 < δ m := fun m => div_pos (sub_pos.mpr hst) (by positivity)
  set X : ℕ → ℕ → ℝ := fun m j => s + j * δ m with hX
  have hXd : ∀ m j, X m (j + 1) - X m j = δ m := fun m j => by
    simp only [hX]; push_cast; ring
  have hXmono : ∀ m, Monotone (X m) := by
    intro m i i' hii'
    simp only [hX]
    have := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hii' : (i : ℝ) ≤ i') (hδpos m).le
    linarith
  have hX0 : ∀ m, X m 0 = s := fun m => by simp [hX]
  have hXlast : ∀ m : ℕ, X m (m + 1) = t := by
    intro m
    have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
    simp only [hX, hδ]
    push_cast
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hm]
    ring
  -- the squared chord-quotient step functions
  set G : ℕ → ℝ → ℝ≥0∞ := fun m v => ∑ j ∈ Finset.range (m + 1),
      (Set.Ico (X m j) (X m (j + 1))).indicator
        (fun _ => ENNReal.ofReal ((‖h (X m (j + 1)) - h (X m j)‖ / δ m) ^ 2)) v with hG
  have hGmeas : ∀ m, Measurable (G m) := fun m =>
    Finset.measurable_sum _ fun j _ => measurable_const.indicator measurableSet_Ico
  -- the master estimate bounds each step-function energy
  have hGbound : ∀ m : ℕ, ∫⁻ v in Set.Icc s t, G m v
      ≤ ENNReal.ofReal (2 * K * deriv (imageAreaProfileX f α σ τ) x) := by
    intro m
    have hIco_sub : ∀ j ∈ Finset.range (m + 1),
        Set.Ico (X m j) (X m (j + 1)) ⊆ Set.Icc s t := by
      intro j hj z hz
      have h1 : s ≤ X m j := by
        have := hXmono m (Nat.zero_le j)
        rwa [hX0 m] at this
      have h2 : X m (j + 1) ≤ t := by
        have := hXmono m (Nat.succ_le_succ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
        rwa [hXlast m] at this
      exact ⟨h1.trans hz.1, hz.2.le.trans h2⟩
    have hcalc : ∫⁻ v in Set.Icc s t, G m v
        = ∑ j ∈ Finset.range (m + 1),
            ENNReal.ofReal ((‖h (X m (j + 1)) - h (X m j)‖ / δ m) ^ 2)
              * ENNReal.ofReal (δ m) := by
      simp only [hG]
      rw [MeasureTheory.lintegral_finsetSum _
        (fun j _ => measurable_const.indicator measurableSet_Ico)]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [MeasureTheory.lintegral_indicator measurableSet_Ico,
        MeasureTheory.Measure.restrict_restrict measurableSet_Ico,
        Set.inter_eq_self_of_subset_left (hIco_sub j hj),
        MeasureTheory.setLIntegral_const, Real.volume_Ico, hXd]
    rw [hcalc]
    have hterm : ∀ j ∈ Finset.range (m + 1),
        ENNReal.ofReal ((‖h (X m (j + 1)) - h (X m j)‖ / δ m) ^ 2)
            * ENNReal.ofReal (δ m)
          = ENNReal.ofReal (‖h (X m (j + 1)) - h (X m j)‖ ^ 2 / δ m) := by
      intro j _
      rw [← ENNReal.ofReal_mul (sq_nonneg (‖h (X m (j + 1)) - h (X m j)‖ / δ m))]
      congr 1
      rw [div_pow]
      field_simp
    have hsum_or : ENNReal.ofReal
        (∑ j ∈ Finset.range (m + 1), ‖h (X m (j + 1)) - h (X m j)‖ ^ 2 / δ m)
        = ∑ j ∈ Finset.range (m + 1),
            ENNReal.ofReal (‖h (X m (j + 1)) - h (X m j)‖ ^ 2 / δ m) :=
      ENNReal.ofReal_sum_of_nonneg fun j _ => div_nonneg (sq_nonneg _) (hδpos m).le
    rw [Finset.sum_congr rfl hterm, ← hsum_or]
    refine ENNReal.ofReal_le_ofReal ?_
    -- the equipartition is an ordered contact-allowed family
    have hST : ∀ k : Fin (m + 1), X m (k : ℕ) < X m ((k : ℕ) + 1) := by
      intro k
      have h1 := hXd m (k : ℕ)
      have h2 := hδpos m
      linarith
    have hord : ∀ k l : Fin (m + 1), k < l → X m ((k : ℕ) + 1) ≤ X m (l : ℕ) :=
      fun k l hkl => hXmono m (Nat.succ_le_of_lt hkl)
    have hmem : ∀ k : Fin (m + 1), σ ≤ X m (k : ℕ) ∧ X m ((k : ℕ) + 1) ≤ τ := by
      intro k
      constructor
      · refine hσs.trans ?_
        have := hXmono m (Nat.zero_le (k : ℕ))
        rwa [hX0 m] at this
      · refine le_trans ?_ htτ
        have := hXmono m (Nat.succ_le_of_lt k.isLt)
        rwa [hXlast m] at this
    have hmaster := qc_master_sum_sq_div_le_vertical
      (S := fun k : Fin (m + 1) => X m (k : ℕ))
      (T := fun k : Fin (m + 1) => X m ((k : ℕ) + 1)) hf hαx hΨ hST hord hmem
    calc ∑ j ∈ Finset.range (m + 1), ‖h (X m (j + 1)) - h (X m j)‖ ^ 2 / δ m
        = ∑ k : Fin (m + 1), ‖f ⟨x, X m ((k : ℕ) + 1)⟩ - f ⟨x, X m (k : ℕ)⟩‖ ^ 2
            / (X m ((k : ℕ) + 1) - X m (k : ℕ)) := by
          rw [← Fin.sum_univ_eq_sum_range
            (fun j => ‖h (X m (j + 1)) - h (X m j)‖ ^ 2 / δ m) (m + 1)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [happ, happ, hXd]
      _ ≤ 2 * K * deriv (imageAreaProfileX f α σ τ) x := hmaster
  -- pointwise convergence of the step functions at differentiability points
  have hpoint : ∀ v ∈ Set.Ico s t, DifferentiableAt ℝ h v →
      Filter.Tendsto (fun m => G m v) Filter.atTop
        (nhds ((‖deriv h v‖₊ : ℝ≥0∞) ^ 2)) := by
    intro v hv hdv
    have hvs : 0 ≤ v - s := sub_nonneg.mpr hv.1
    -- the straddling grid index at scale `m`
    have hidx : ∀ m : ℕ, ∃ jm : ℕ, jm < m + 1 ∧ X m jm ≤ v ∧ v < X m (jm + 1) := by
      intro m
      refine ⟨⌊(v - s) / δ m⌋₊, ?_, ?_, ?_⟩
      · have h1 : (v - s) / δ m < ((m + 1 : ℕ) : ℝ) := by
          rw [div_lt_iff₀ (hδpos m)]
          have h2 : ((m + 1 : ℕ) : ℝ) * δ m = t - s := by
            have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
            simp only [hδ]
            push_cast
            rw [← mul_div_assoc]
            exact mul_div_cancel_left₀ _ hm
          rw [h2]
          linarith [hv.2]
        exact (Nat.floor_lt (div_nonneg hvs (hδpos m).le)).mpr h1
      · have h1 : (⌊(v - s) / δ m⌋₊ : ℝ) ≤ (v - s) / δ m :=
          Nat.floor_le (div_nonneg hvs (hδpos m).le)
        have h2 : (⌊(v - s) / δ m⌋₊ : ℝ) * δ m ≤ v - s := (le_div_iff₀ (hδpos m)).mp h1
        simp only [hX]
        linarith
      · have h1 : (v - s) / δ m < (⌊(v - s) / δ m⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        have h2 : v - s < ((⌊(v - s) / δ m⌋₊ : ℝ) + 1) * δ m :=
          (div_lt_iff₀ (hδpos m)).mp h1
        simp only [hX]
        push_cast
        linarith
    choose j hjm hpv hvq using hidx
    -- at `v` the step function reduces to the straddling chord quotient
    have hGv : ∀ m, G m v
        = ENNReal.ofReal ((‖h (X m (j m + 1)) - h (X m (j m))‖ / δ m) ^ 2) := by
      intro m
      simp only [hG]
      have hzero : ∀ k ∈ Finset.range (m + 1), k ≠ j m →
          (Set.Ico (X m k) (X m (k + 1))).indicator
            (fun _ => ENNReal.ofReal ((‖h (X m (k + 1)) - h (X m k)‖ / δ m) ^ 2)) v
            = 0 := by
        intro k _ hkj
        rw [Set.indicator_of_notMem]
        rintro ⟨hk1, hk2⟩
        rcases lt_or_gt_of_ne hkj with hlt | hgt
        · have hle : X m (k + 1) ≤ X m (j m) := hXmono m (Nat.succ_le_of_lt hlt)
          exact lt_irrefl v (hk2.trans_le (hle.trans (hpv m)))
        · have hle : X m (j m + 1) ≤ X m k := hXmono m (Nat.succ_le_of_lt hgt)
          exact lt_irrefl v ((hvq m).trans_le (hle.trans hk1))
      rw [Finset.sum_eq_single_of_mem (j m) (Finset.mem_range.mpr (hjm m)) hzero,
        Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hpv m, hvq m⟩)]
    -- the mesh collapses
    have hδlim : Filter.Tendsto δ Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (t - s) * (1 / ((n : ℝ) + 1)))
          Filter.atTop (nhds 0) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (t - s)
      refine h1.congr fun n => ?_
      simp only [hδ, mul_one_div]
    have hmesh : Filter.Tendsto (fun m => X m (j m + 1) - X m (j m))
        Filter.atTop (nhds 0) := by
      simpa only [hXd] using hδlim
    -- the straddle lemma
    have hstr := tendsto_straddle_diffQuotient hdv.hasDerivAt
      (p := fun m => X m (j m)) (q := fun m => X m (j m + 1))
      (fun m => ⟨hpv m, hvq m⟩) hmesh
    have hstr2 : Filter.Tendsto
        (fun m => ENNReal.ofReal ((‖h (X m (j m + 1)) - h (X m (j m))‖ / δ m) ^ 2))
        Filter.atTop (nhds (ENNReal.ofReal (‖deriv h v‖ ^ 2))) :=
      ENNReal.tendsto_ofReal
        (((hstr.congr fun m => by rw [hXd]).pow 2))
    have hval : ENNReal.ofReal (‖deriv h v‖ ^ 2) = (‖deriv h v‖₊ : ℝ≥0∞) ^ 2 := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
    rw [← hval]
    exact hstr2.congr fun m => (hGv m).symm
  -- almost-everywhere comparison with the liminf, then Fatou
  have h_ae : ∀ᵐ v ∂(volume.restrict (Set.Icc s t)),
      (‖deriv h v‖₊ : ℝ≥0∞) ^ 2 ≤ Filter.liminf (fun m => G m v) Filter.atTop := by
    have h1 : ∀ᵐ v ∂(volume.restrict (Set.Icc s t)), v ∈ Set.Icc s t :=
      MeasureTheory.ae_restrict_mem measurableSet_Icc
    have h2 : ∀ᵐ v ∂(volume.restrict (Set.Icc s t)), v ≠ t :=
      MeasureTheory.ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
    have h3 : ∀ᵐ v ∂(volume.restrict (Set.Icc s t)),
        v ∈ Set.uIcc σ τ → DifferentiableAt ℝ h v :=
      MeasureTheory.ae_restrict_of_ae hdiff
    filter_upwards [h1, h2, h3] with v hv hvt hvd
    have hv' : v ∈ Set.Ico s t := ⟨hv.1, lt_of_le_of_ne hv.2 hvt⟩
    have hdv : DifferentiableAt ℝ h v := hvd (by
      rw [Set.uIcc_of_le hστ]
      exact ⟨hσs.trans hv.1, hv.2.trans htτ⟩)
    exact le_of_eq ((hpoint v hv' hdv).liminf_eq).symm
  calc ∫⁻ v in Set.Icc s t, (‖deriv h v‖₊ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ v in Set.Icc s t, Filter.liminf (fun m => G m v) Filter.atTop :=
        MeasureTheory.lintegral_mono_ae h_ae
    _ ≤ Filter.liminf (fun m => ∫⁻ v in Set.Icc s t, G m v) Filter.atTop :=
        MeasureTheory.lintegral_liminf_le hGmeas
    _ ≤ ENNReal.ofReal (2 * K * deriv (imageAreaProfileX f α σ τ) x) :=
        (Filter.liminf_le_liminf (Filter.Eventually.of_forall hGbound)).trans_eq
          (Filter.liminf_const _)

/-! ## Integration in the transverse variable: the finite box energies -/

/-- **Finite box energies (horizontal triple).** For a geometric `K`-quasiconformal `f`
and a nondegenerate box `(a,b) × (s,t)`, the squared variation of both real component
slices and the squared slice-derivative energy have finite integrals over the box.

*Proof sketch.* Let `Φ := imageAreaProfileY f (a−1) (b+1) (s−1)`, monotone by
`monotone_imageAreaProfileY`. For a.e. `y ∈ [s,t]` (where `HasDerivAt Φ (deriv Φ y) y` with
`deriv Φ y ≥ 0`, by `Monotone.ae_hasDerivAt_deriv` restricted to the box):
* the component variation over `[a,b]` is at most the complex slice variation over the
  window `[a−1, b+1]` (the projections `Complex.re`/`Complex.im` are `1`-Lipschitz —
  `RCLike.lipschitzWith_re`/`_im` — so `LipschitzWith.comp_eVariationOn_le` applies, then
  `eVariationOn.mono` into the window), whose square is at most
  `ofReal (2K(b−a+2)) * ofReal (deriv Φ y)` by `qc_slice_eVariationOn_le_horizontal`
  (`ENNReal.ofReal_pow`, `Real.sq_sqrt` with nonnegative argument, `ENNReal.ofReal_mul`);
* the inner slice energy is at most `ofReal (2K) * ofReal (deriv Φ y)` by
  `qc_slice_deriv_energy_le_horizontal`.
Integrate with `lintegral_mono_ae` (no measurability of the left-hand integrand needed) and
dominate `∫⁻ y in [s,t], ofReal (deriv Φ y)` by `ofReal (Φ t − Φ s)`
(`lintegral_ofReal_deriv_le_of_monotone`); both bounds are finite (`ENNReal.mul_ne_top`).
-/
theorem qc_forward_energy_box_horizontal {f : ℂ → ℂ} {K : ℝ} (hf : AxisRectModulusBound f K)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    (∫⁻ y in Set.Icc s t,
        (eVariationOn (fun x : ℝ => (f ⟨x, y⟩).re) (Set.Icc a b)) ^ 2) ≠ ⊤ ∧
    (∫⁻ y in Set.Icc s t,
        (eVariationOn (fun x : ℝ => (f ⟨x, y⟩).im) (Set.Icc a b)) ^ 2) ≠ ⊤ ∧
    (∫⁻ y in Set.Icc s t, ∫⁻ x in Set.Icc a b,
        (‖deriv (fun u : ℝ => f ⟨u, y⟩) x‖₊ : ℝ≥0∞) ^ 2) ≠ ⊤ := by
  classical
  have hcont : Continuous f := hf.2.1.continuous
  have hK1 : (1 : ℝ) ≤ K := hf.1
  have hre : LipschitzWith 1 Complex.re := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm, ← Complex.sub_re]
    exact Complex.abs_re_le_norm (z - w)
  have him : LipschitzWith 1 Complex.im := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm, ← Complex.sub_im]
    exact Complex.abs_im_le_norm (z - w)
  have hmono : Monotone (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) :=
    monotone_imageAreaProfileY hcont _ _ _
  -- the reusable integration step: an a.e. bound by `C · Φ′` forces a finite integral
  have hkey : ∀ (F : ℝ → ℝ≥0∞) (C : ℝ),
      (∀ᵐ y ∂(volume.restrict (Set.Icc s t)),
        F y ≤ ENNReal.ofReal C
          * ENNReal.ofReal (deriv (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y)) →
      (∫⁻ y in Set.Icc s t, F y) ≠ ⊤ := by
    intro F C hFae
    have h1 : ∫⁻ y in Set.Icc s t, F y
        ≤ ENNReal.ofReal C
            * ENNReal.ofReal (imageAreaProfileY f (a - 1) (b + 1) (s - 1) t
                - imageAreaProfileY f (a - 1) (b + 1) (s - 1) s) := by
      calc ∫⁻ y in Set.Icc s t, F y
          ≤ ∫⁻ y in Set.Icc s t, ENNReal.ofReal C
              * ENNReal.ofReal (deriv (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y) :=
            MeasureTheory.lintegral_mono_ae hFae
        _ = ENNReal.ofReal C * ∫⁻ y in Set.Icc s t,
              ENNReal.ofReal (deriv (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y) :=
            MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal C
              * ENNReal.ofReal (imageAreaProfileY f (a - 1) (b + 1) (s - 1) t
                  - imageAreaProfileY f (a - 1) (b + 1) (s - 1) s) := by
            gcongr
            exact lintegral_ofReal_deriv_le_of_monotone hmono hst.le
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h1
  -- almost every height carries the three per-height bounds
  have haeVar : ∀ᵐ y ∂(volume.restrict (Set.Icc s t)),
      ((eVariationOn (fun x : ℝ => (f ⟨x, y⟩).re) (Set.Icc a b)) ^ 2
          ≤ ENNReal.ofReal (2 * K * (b + 1 - (a - 1)))
            * ENNReal.ofReal (deriv (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y))
      ∧ ((eVariationOn (fun x : ℝ => (f ⟨x, y⟩).im) (Set.Icc a b)) ^ 2
          ≤ ENNReal.ofReal (2 * K * (b + 1 - (a - 1)))
            * ENNReal.ofReal (deriv (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y))
      ∧ ((∫⁻ x in Set.Icc a b, (‖deriv (fun u : ℝ => f ⟨u, y⟩) x‖₊ : ℝ≥0∞) ^ 2)
          ≤ ENNReal.ofReal (2 * K)
            * ENNReal.ofReal (deriv (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y)) := by
    have h1 : ∀ᵐ y ∂(volume.restrict (Set.Icc s t)),
        HasDerivAt (imageAreaProfileY f (a - 1) (b + 1) (s - 1))
          (deriv (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y) y
        ∧ 0 ≤ deriv (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y :=
      MeasureTheory.ae_restrict_of_ae hmono.ae_hasDerivAt_deriv
    have h2 : ∀ᵐ y ∂(volume.restrict (Set.Icc s t)), y ∈ Set.Icc s t :=
      MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [h1, h2] with y hy hymem
    have hσy : s - 1 < y := by have := hymem.1; linarith
    have hΦy : DifferentiableAt ℝ (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y :=
      hy.1.differentiableAt
    have hD0 : 0 ≤ deriv (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y := hy.2
    have hC0 : (0 : ℝ) ≤ 2 * K * (b + 1 - (a - 1)) := by nlinarith
    have hz0 : (0 : ℝ) ≤ 2 * K * (b + 1 - (a - 1))
        * deriv (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y := mul_nonneg hC0 hD0
    have hslice := qc_slice_eVariationOn_le_horizontal hf hσy hΦy
    -- squared component variation bound through the 1-Lipschitz projections
    have hproj : ∀ π : ℂ → ℝ, LipschitzWith 1 π →
        (eVariationOn (fun x : ℝ => π (f ⟨x, y⟩)) (Set.Icc a b)) ^ 2
          ≤ ENNReal.ofReal (2 * K * (b + 1 - (a - 1)))
            * ENNReal.ofReal (deriv (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y) := by
      intro π hπ
      have hπon : LipschitzOnWith 1 π Set.univ := hπ.lipschitzOnWith
      have hπ1 : eVariationOn (π ∘ fun x : ℝ => f ⟨x, y⟩) (Set.Icc a b)
          ≤ (1 : ℝ≥0) * eVariationOn (fun x : ℝ => f ⟨x, y⟩) (Set.Icc a b) :=
        hπon.comp_eVariationOn_le (Set.mapsTo_univ _ _)
      rw [ENNReal.coe_one, one_mul] at hπ1
      have hπ2 : eVariationOn (fun x : ℝ => f ⟨x, y⟩) (Set.Icc a b)
          ≤ eVariationOn (fun x : ℝ => f ⟨x, y⟩) (Set.Icc (a - 1) (b + 1)) :=
        eVariationOn.mono _ (Set.Icc_subset_Icc (by linarith) (by linarith))
      have hπ3 : eVariationOn (fun x : ℝ => π (f ⟨x, y⟩)) (Set.Icc a b)
          ≤ ENNReal.ofReal (Real.sqrt (2 * K * (b + 1 - (a - 1))
              * deriv (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y)) :=
        hπ1.trans (hπ2.trans hslice)
      calc (eVariationOn (fun x : ℝ => π (f ⟨x, y⟩)) (Set.Icc a b)) ^ 2
          ≤ (ENNReal.ofReal (Real.sqrt (2 * K * (b + 1 - (a - 1))
              * deriv (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y))) ^ 2 :=
            pow_le_pow_left' hπ3 2
        _ = ENNReal.ofReal (2 * K * (b + 1 - (a - 1))
              * deriv (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y) := by
            rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hz0]
        _ = ENNReal.ofReal (2 * K * (b + 1 - (a - 1)))
              * ENNReal.ofReal (deriv (imageAreaProfileY f (a - 1) (b + 1) (s - 1)) y) :=
            ENNReal.ofReal_mul hC0
    refine ⟨hproj Complex.re hre, hproj Complex.im him, ?_⟩
    have hen := qc_slice_deriv_energy_le_horizontal hf hσy hΦy
      (show a - 1 ≤ a by linarith) (show b ≤ b + 1 by linarith)
    rwa [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * K by linarith)] at hen
  exact ⟨hkey _ _ (haeVar.mono fun y hy => hy.1),
    hkey _ _ (haeVar.mono fun y hy => hy.2.1),
    hkey _ _ (haeVar.mono fun y hy => hy.2.2)⟩

/-- **Finite box energies (vertical triple).** Mirror of
`qc_forward_energy_box_horizontal`, with the abscissa `x ∈ [a,b]` outer and the vertical
slices over `[s,t]` inner, using the vertical profile
`Ψ := imageAreaProfileX f (a−1) (s−1) (t+1)` and the vertical per-height bounds. -/
theorem qc_forward_energy_box_vertical {f : ℂ → ℂ} {K : ℝ} (hf : AxisRectModulusBound f K)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    (∫⁻ x in Set.Icc a b,
        (eVariationOn (fun y : ℝ => (f ⟨x, y⟩).re) (Set.Icc s t)) ^ 2) ≠ ⊤ ∧
    (∫⁻ x in Set.Icc a b,
        (eVariationOn (fun y : ℝ => (f ⟨x, y⟩).im) (Set.Icc s t)) ^ 2) ≠ ⊤ ∧
    (∫⁻ x in Set.Icc a b, ∫⁻ y in Set.Icc s t,
        (‖deriv (fun u : ℝ => f ⟨x, u⟩) y‖₊ : ℝ≥0∞) ^ 2) ≠ ⊤ := by
  classical
  have hcont : Continuous f := hf.2.1.continuous
  have hK1 : (1 : ℝ) ≤ K := hf.1
  have hre : LipschitzWith 1 Complex.re := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm, ← Complex.sub_re]
    exact Complex.abs_re_le_norm (z - w)
  have him : LipschitzWith 1 Complex.im := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm, ← Complex.sub_im]
    exact Complex.abs_im_le_norm (z - w)
  have hmono : Monotone (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) :=
    monotone_imageAreaProfileX hcont _ _ _
  -- the reusable integration step: an a.e. bound by `C · Ψ′` forces a finite integral
  have hkey : ∀ (F : ℝ → ℝ≥0∞) (C : ℝ),
      (∀ᵐ x ∂(volume.restrict (Set.Icc a b)),
        F x ≤ ENNReal.ofReal C
          * ENNReal.ofReal (deriv (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x)) →
      (∫⁻ x in Set.Icc a b, F x) ≠ ⊤ := by
    intro F C hFae
    have h1 : ∫⁻ x in Set.Icc a b, F x
        ≤ ENNReal.ofReal C
            * ENNReal.ofReal (imageAreaProfileX f (a - 1) (s - 1) (t + 1) b
                - imageAreaProfileX f (a - 1) (s - 1) (t + 1) a) := by
      calc ∫⁻ x in Set.Icc a b, F x
          ≤ ∫⁻ x in Set.Icc a b, ENNReal.ofReal C
              * ENNReal.ofReal (deriv (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x) :=
            MeasureTheory.lintegral_mono_ae hFae
        _ = ENNReal.ofReal C * ∫⁻ x in Set.Icc a b,
              ENNReal.ofReal (deriv (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x) :=
            MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal C
              * ENNReal.ofReal (imageAreaProfileX f (a - 1) (s - 1) (t + 1) b
                  - imageAreaProfileX f (a - 1) (s - 1) (t + 1) a) := by
            gcongr
            exact lintegral_ofReal_deriv_le_of_monotone hmono hab.le
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h1
  -- almost every abscissa carries the three per-abscissa bounds
  have haeVar : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)),
      ((eVariationOn (fun y : ℝ => (f ⟨x, y⟩).re) (Set.Icc s t)) ^ 2
          ≤ ENNReal.ofReal (2 * K * (t + 1 - (s - 1)))
            * ENNReal.ofReal (deriv (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x))
      ∧ ((eVariationOn (fun y : ℝ => (f ⟨x, y⟩).im) (Set.Icc s t)) ^ 2
          ≤ ENNReal.ofReal (2 * K * (t + 1 - (s - 1)))
            * ENNReal.ofReal (deriv (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x))
      ∧ ((∫⁻ y in Set.Icc s t, (‖deriv (fun u : ℝ => f ⟨x, u⟩) y‖₊ : ℝ≥0∞) ^ 2)
          ≤ ENNReal.ofReal (2 * K)
            * ENNReal.ofReal (deriv (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x)) := by
    have h1 : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)),
        HasDerivAt (imageAreaProfileX f (a - 1) (s - 1) (t + 1))
          (deriv (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x) x
        ∧ 0 ≤ deriv (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x :=
      MeasureTheory.ae_restrict_of_ae hmono.ae_hasDerivAt_deriv
    have h2 : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), x ∈ Set.Icc a b :=
      MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [h1, h2] with x hx hxmem
    have hαx : a - 1 < x := by have := hxmem.1; linarith
    have hΨx : DifferentiableAt ℝ (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x :=
      hx.1.differentiableAt
    have hD0 : 0 ≤ deriv (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x := hx.2
    have hC0 : (0 : ℝ) ≤ 2 * K * (t + 1 - (s - 1)) := by nlinarith
    have hz0 : (0 : ℝ) ≤ 2 * K * (t + 1 - (s - 1))
        * deriv (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x := mul_nonneg hC0 hD0
    have hslice := qc_slice_eVariationOn_le_vertical hf hαx hΨx
    -- squared component variation bound through the 1-Lipschitz projections
    have hproj : ∀ π : ℂ → ℝ, LipschitzWith 1 π →
        (eVariationOn (fun y : ℝ => π (f ⟨x, y⟩)) (Set.Icc s t)) ^ 2
          ≤ ENNReal.ofReal (2 * K * (t + 1 - (s - 1)))
            * ENNReal.ofReal (deriv (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x) := by
      intro π hπ
      have hπon : LipschitzOnWith 1 π Set.univ := hπ.lipschitzOnWith
      have hπ1 : eVariationOn (π ∘ fun y : ℝ => f ⟨x, y⟩) (Set.Icc s t)
          ≤ (1 : ℝ≥0) * eVariationOn (fun y : ℝ => f ⟨x, y⟩) (Set.Icc s t) :=
        hπon.comp_eVariationOn_le (Set.mapsTo_univ _ _)
      rw [ENNReal.coe_one, one_mul] at hπ1
      have hπ2 : eVariationOn (fun y : ℝ => f ⟨x, y⟩) (Set.Icc s t)
          ≤ eVariationOn (fun y : ℝ => f ⟨x, y⟩) (Set.Icc (s - 1) (t + 1)) :=
        eVariationOn.mono _ (Set.Icc_subset_Icc (by linarith) (by linarith))
      have hπ3 : eVariationOn (fun y : ℝ => π (f ⟨x, y⟩)) (Set.Icc s t)
          ≤ ENNReal.ofReal (Real.sqrt (2 * K * (t + 1 - (s - 1))
              * deriv (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x)) :=
        hπ1.trans (hπ2.trans hslice)
      calc (eVariationOn (fun y : ℝ => π (f ⟨x, y⟩)) (Set.Icc s t)) ^ 2
          ≤ (ENNReal.ofReal (Real.sqrt (2 * K * (t + 1 - (s - 1))
              * deriv (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x))) ^ 2 :=
            pow_le_pow_left' hπ3 2
        _ = ENNReal.ofReal (2 * K * (t + 1 - (s - 1))
              * deriv (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x) := by
            rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hz0]
        _ = ENNReal.ofReal (2 * K * (t + 1 - (s - 1)))
              * ENNReal.ofReal (deriv (imageAreaProfileX f (a - 1) (s - 1) (t + 1)) x) :=
            ENNReal.ofReal_mul hC0
    refine ⟨hproj Complex.re hre, hproj Complex.im him, ?_⟩
    have hen := qc_slice_deriv_energy_le_vertical hf hαx hΨx
      (show s - 1 ≤ s by linarith) (show t ≤ t + 1 by linarith)
    rwa [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * K by linarith)] at hen
  exact ⟨hkey _ _ (haeVar.mono fun x hx => hx.1),
    hkey _ _ (haeVar.mono fun x hx => hx.2.1),
    hkey _ _ (haeVar.mono fun x hx => hx.2.2)⟩

/-! ## Almost-every slice absolute continuity -/

/-- **Almost every horizontal slice is absolutely continuous on every interval.** For a
geometric `K`-quasiconformal `f`, for almost every height `y` the complex slice
`x ↦ f ⟨x, y⟩` is `AbsolutelyContinuousOnInterval` on every `[a,b]`.

*Proof sketch.* Call `y` *good* if for every `n : ℕ` the profile
`imageAreaProfileY f (−n) n (−n)` is differentiable at `y` and the segment `[−n,n] × {y}`
has null image. Almost every `y` is good: per `n` combine `Monotone.ae_differentiableAt`
(the profile is monotone) with `countable_pos_volume_image_horizontalSeg`
(`Set.Countable.measure_zero`), then intersect over `n` (`ae_all_iff`). Fix a good `y` and
`a, b`; choose `n ≥ max (max |a| |b|) |y|` (`exists_nat_ge`). Verify the ε–δ criterion
`absolutelyContinuousOnInterval_iff`: given `ε > 0`, set `A′ := deriv` of the profile at
`y` (`≥ 0`) and `δ := ε²/(2(K·A′ + 1))`. For a finite disjoint family of subintervals of
`uIcc a b` with total length `< δ`: normalize each endpoint pair by `min`/`max` (the
`uIoc`s are pairwise disjoint), shrink each left endpoint by `s > 0` so that the *closed*
intervals `[uᵢ+s, vᵢ]` are pairwise disjoint (each is contained in its `Ioc (uᵢ) (vᵢ)`),
apply the one-sided master family estimate
(`AxisRectModulusBound.horizontal_family_sq_sum_le`) and Cauchy–Schwarz:
`∑ Dᵢ ≤ √(∑ wᵢ) · √(∑ Dᵢ²/wᵢ) ≤ √(δ · K·A′) < ε`; finally let `s → 0⁺` using continuity of
the slice at the finitely many left endpoints.

The hypothesis is load-bearing: the conclusion fails for the singular Cantor shear
`⟨x, y⟩ ↦ ⟨x, y + c(x)⟩` (`c` the Cantor function), a homeomorphism that is not
geometrically quasiconformal — the image separating families of thin strips over Cantor
intervals violate exactly the modulus bound consumed here.
-/
theorem AxisRectModulusBound.ae_horizontal_slice_absolutelyContinuous {f : ℂ → ℂ} {K : ℝ}
    (hf : AxisRectModulusBound f K) :
    ∀ᵐ y : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun x : ℝ => f ⟨x, y⟩) a b := by
  classical
  have hcont : Continuous f := hf.2.1.continuous
  have hinj : Function.Injective f := hf.2.1.injective
  have hK1 : (1 : ℝ) ≤ K := hf.1
  -- the good heights: differentiable profiles and null segments at every scale
  have hgood : ∀ᵐ y : ℝ, ∀ n : ℕ,
      (DifferentiableAt ℝ (imageAreaProfileY f (-(n : ℝ)) n (-(n : ℝ))) y
        ∧ 0 ≤ deriv (imageAreaProfileY f (-(n : ℝ)) n (-(n : ℝ))) y)
      ∧ volume (f '' axisRect (-(n : ℝ)) n y y) = 0 := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    have h1 := (monotone_imageAreaProfileY hcont (-(n : ℝ)) n (-(n : ℝ))).ae_hasDerivAt_deriv
    have h2 : ∀ᵐ y : ℝ, volume (f '' axisRect (-(n : ℝ)) n y y) = 0 := by
      have hnull : volume {y : ℝ | volume (f '' axisRect (-(n : ℝ)) n y y) ≠ 0} = 0 :=
        (countable_pos_volume_image_horizontalSeg hcont hinj (-(n : ℝ)) n).measure_zero _
      rw [MeasureTheory.ae_iff]
      simpa using hnull
    filter_upwards [h1, h2] with y hy1 hy2
    exact ⟨⟨hy1.1.differentiableAt, hy1.2⟩, hy2⟩
  filter_upwards [hgood] with y hy a b
  -- choose a window containing the interval and the height
  obtain ⟨n, hn⟩ := exists_nat_ge (max (max |a| |b|) |y|)
  have ha : |a| ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hb : |b| ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hyn : |y| ≤ n := le_trans (le_max_right _ _) hn
  rw [abs_le] at ha hb hyn
  obtain ⟨⟨hdiff, hD0⟩, hseg⟩ := hy n
  set A' := deriv (imageAreaProfileY f (-(n : ℝ)) n (-(n : ℝ))) y with hA'
  have hKA : (0 : ℝ) ≤ K * A' := mul_nonneg (by linarith) hD0
  -- the ε–δ criterion
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  refine ⟨ε ^ 2 / (K * A' + 1), div_pos (pow_pos hε 2) (by linarith), ?_⟩
  rintro ⟨N, I⟩ hE hlen
  simp only [AbsolutelyContinuousOnInterval.disjWithin, Set.mem_ofPred_eq] at hE
  dsimp only at hE hlen ⊢
  obtain ⟨hmemE, hdisjE⟩ := hE
  -- normalize the interval endpoints
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, u = fun i => min (I i).1 (I i).2 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℝ, v = fun i => max (I i).1 (I i).2 := ⟨_, rfl⟩
  have huv : ∀ i, u i = min (I i).1 (I i).2 := fun i => by rw [hu]
  have hvv : ∀ i, v i = max (I i).1 (I i).2 := fun i => by rw [hv]
  have humem : ∀ i ∈ Finset.range N, u i ∈ Set.uIcc a b := by
    intro i hi
    obtain ⟨h1, h2⟩ := hmemE i hi
    rw [huv]
    exact ⟨le_min h1.1 h2.1, (min_le_left _ _).trans h1.2⟩
  have hvmem : ∀ i ∈ Finset.range N, v i ∈ Set.uIcc a b := by
    intro i hi
    obtain ⟨h1, h2⟩ := hmemE i hi
    rw [hvv]
    exact ⟨h1.1.trans (le_max_left _ _), max_le h1.2 h2.2⟩
  have hwindow : Set.uIcc a b ⊆ Set.Icc (-(n : ℝ)) n :=
    Set.Icc_subset_Icc (le_min ha.1 hb.1) (max_le ha.2 hb.2)
  have hlen' : ∑ i ∈ Finset.range N, (v i - u i) < ε ^ 2 / (K * A' + 1) := by
    have hconv : ∀ i ∈ Finset.range N, v i - u i = dist (I i).1 (I i).2 := fun i _ => by
      rw [huv, hvv, Real.dist_eq, max_sub_min_eq_abs]
      exact abs_sub_comm _ _
    rwa [Finset.sum_congr rfl hconv]
  -- reduce the target sum to the normalized nondegenerate intervals
  have hswap : ∀ i ∈ Finset.range N,
      dist (f ⟨(I i).1, y⟩) (f ⟨(I i).2, y⟩) = dist (f ⟨u i, y⟩) (f ⟨v i, y⟩) := by
    intro i _
    rw [huv, hvv]
    rcases le_total (I i).1 (I i).2 with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
    · rw [min_eq_right hle, max_eq_left hle, dist_comm]
  rw [Finset.sum_congr rfl hswap]
  set T : Finset ℕ := (Finset.range N).filter (fun i => u i < v i) with hT
  have hTsum : ∑ i ∈ Finset.range N, dist (f ⟨u i, y⟩) (f ⟨v i, y⟩)
      = ∑ i ∈ T, dist (f ⟨u i, y⟩) (f ⟨v i, y⟩) := by
    refine (Finset.sum_filter_of_ne fun i hi hne => ?_).symm
    by_contra hnot
    have huvle : u i ≤ v i := by rw [huv, hvv]; exact min_le_max
    have heq : u i = v i := le_antisymm huvle (not_lt.mp hnot)
    exact hne (by rw [heq, dist_self])
  rw [hTsum]
  -- the σ-shrunk family estimate via Cauchy–Schwarz
  have hshrink : ∀ σ' : ℝ, 0 < σ' → (∀ i ∈ T, u i + σ' < v i) →
      ∑ i ∈ T, dist (f ⟨u i + σ', y⟩) (f ⟨v i, y⟩)
        ≤ Real.sqrt (ε ^ 2 / (K * A' + 1)) * Real.sqrt (K * A') := by
    intro σ' hσ' hgap
    set e : Fin T.card ↪o ℕ := T.orderEmbOfFin rfl with he
    have heT : ∀ k, e k ∈ T := fun k => Finset.orderEmbOfFin_mem T rfl k
    have heN : ∀ k, e k ∈ Finset.range N := fun k => Finset.filter_subset _ _ (heT k)
    have hreidx : ∀ g : ℕ → ℝ, ∑ i ∈ T, g i = ∑ k : Fin T.card, g (e k) := by
      intro g
      calc ∑ i ∈ T, g i
          = ∑ i ∈ Finset.map (T.orderEmbOfFin rfl).toEmbedding Finset.univ, g i :=
            (Finset.sum_congr (Finset.map_orderEmbOfFin_univ T rfl) fun _ _ => rfl).symm
        _ = ∑ k : Fin T.card, g (T.orderEmbOfFin rfl k) := Finset.sum_map _ _ _
        _ = ∑ k : Fin T.card, g (e k) := by rw [he]
    have hcd : ∀ k : Fin T.card, u (e k) + σ' < v (e k) := fun k => hgap _ (heT k)
    have hsub : ∀ k : Fin T.card,
        Set.Icc (u (e k) + σ') (v (e k)) ⊆ Set.Icc (-(n : ℝ)) n := by
      intro k z hz
      have h1 := hwindow (humem _ (heN k))
      have h2 := hwindow (hvmem _ (heN k))
      exact ⟨by linarith [h1.1, hz.1], le_trans hz.2 h2.2⟩
    have hIcc_sub : ∀ m : Fin T.card,
        Set.Icc (u (e m) + σ') (v (e m)) ⊆ Set.uIoc (I (e m)).1 (I (e m)).2 := by
      intro m z hz
      have h1 : u (e m) < z := by linarith [hz.1]
      have h2 : z ≤ v (e m) := hz.2
      rw [huv] at h1
      rw [hvv] at h2
      rw [Set.mem_uIoc]
      rcases le_total (I (e m)).1 (I (e m)).2 with hle | hle
      · rw [min_eq_left hle] at h1
        rw [max_eq_right hle] at h2
        exact Or.inl ⟨h1, h2⟩
      · rw [min_eq_right hle] at h1
        rw [max_eq_left hle] at h2
        exact Or.inr ⟨h1, h2⟩
    have hdisjF : Pairwise (Function.onFun Disjoint
        fun k : Fin T.card => Set.Icc (u (e k) + σ') (v (e k))) := by
      intro k l hkl
      have hkl' : e k ≠ e l := fun hEq => hkl (e.injective hEq)
      exact ((hdisjE (Finset.mem_coe.mpr (heN k)) (Finset.mem_coe.mpr (heN l))
        hkl').mono (hIcc_sub k) (hIcc_sub l))
    have hest := hf.horizontal_family_sq_sum_le (show -(n : ℝ) ≤ y from hyn.1)
      hdiff hseg (c := fun k : Fin T.card => u (e k) + σ')
      (d := fun k : Fin T.card => v (e k)) hcd hsub hdisjF
    rw [← hA'] at hest
    rw [hreidx]
    -- Cauchy–Schwarz with the splitting `D = √w · (D/√w)`
    have hsplit : ∀ k : Fin T.card, dist (f ⟨u (e k) + σ', y⟩) (f ⟨v (e k), y⟩)
        = Real.sqrt (v (e k) - (u (e k) + σ'))
            * (dist (f ⟨u (e k) + σ', y⟩) (f ⟨v (e k), y⟩)
                / Real.sqrt (v (e k) - (u (e k) + σ'))) := by
      intro k
      rw [mul_comm, div_mul_cancel₀]
      exact (Real.sqrt_pos.mpr (sub_pos.mpr (hcd k))).ne'
    rw [Finset.sum_congr rfl fun k _ => hsplit k]
    refine (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _).trans ?_
    have hw : ∀ k : Fin T.card, Real.sqrt (v (e k) - (u (e k) + σ')) ^ 2
        = v (e k) - (u (e k) + σ') := fun k => Real.sq_sqrt (sub_pos.mpr (hcd k)).le
    have hr : ∀ k : Fin T.card,
        (dist (f ⟨u (e k) + σ', y⟩) (f ⟨v (e k), y⟩)
            / Real.sqrt (v (e k) - (u (e k) + σ'))) ^ 2
          = dist (f ⟨u (e k) + σ', y⟩) (f ⟨v (e k), y⟩) ^ 2
              / (v (e k) - (u (e k) + σ')) := fun k => by rw [div_pow, hw k]
    rw [Finset.sum_congr rfl fun k _ => hw k, Finset.sum_congr rfl fun k _ => hr k]
    have hwsum : ∑ k : Fin T.card, (v (e k) - (u (e k) + σ'))
        ≤ ε ^ 2 / (K * A' + 1) := by
      have h1 := hreidx fun i => v i - u i
      have h2 : ∑ k : Fin T.card, (v (e k) - (u (e k) + σ'))
          ≤ ∑ k : Fin T.card, (v (e k) - u (e k)) :=
        Finset.sum_le_sum fun k _ => by linarith
      have h3 : ∑ i ∈ T, (v i - u i) ≤ ∑ i ∈ Finset.range N, (v i - u i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i _ _ => by rw [huv, hvv]; exact sub_nonneg.mpr min_le_max
      rw [h1] at h3
      linarith [hlen']
    exact mul_le_mul (Real.sqrt_le_sqrt hwsum) (Real.sqrt_le_sqrt hest)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- pass to the limit `σ' → 0⁺`
  have hle : ∑ i ∈ T, dist (f ⟨u i, y⟩) (f ⟨v i, y⟩)
      ≤ Real.sqrt (ε ^ 2 / (K * A' + 1)) * Real.sqrt (K * A') := by
    have hcont2 : Filter.Tendsto
        (fun σ' : ℝ => ∑ i ∈ T, dist (f ⟨u i + σ', y⟩) (f ⟨v i, y⟩))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∑ i ∈ T, dist (f ⟨u i + 0, y⟩) (f ⟨v i, y⟩))) := by
      refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      refine Continuous.tendsto ?_ 0
      refine continuous_finsetSum _ fun i _ => Continuous.dist ?_ continuous_const
      refine hcont.comp ?_
      have hmk : (fun σ' : ℝ => (⟨u i + σ', y⟩ : ℂ))
          = fun σ' : ℝ => (⟨u i, y⟩ : ℂ) + (σ' : ℂ) := by
        funext σ'
        apply Complex.ext <;> simp
      rw [hmk]
      exact continuous_const.add Complex.continuous_ofReal
    have hev : ∀ᶠ σ' in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∑ i ∈ T, dist (f ⟨u i + σ', y⟩) (f ⟨v i, y⟩)
          ≤ Real.sqrt (ε ^ 2 / (K * A' + 1)) * Real.sqrt (K * A') := by
      have hgapev : ∀ᶠ σ' in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i ∈ T, u i + σ' < v i := by
        rw [Filter.eventually_all_finset]
        intro i hi
        have hgapi : (0 : ℝ) < v i - u i := sub_pos.mpr (Finset.mem_filter.mp hi).2
        refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
        filter_upwards [eventually_lt_nhds hgapi] with σ' hσ'
        linarith
      filter_upwards [hgapev, eventually_mem_nhdsWithin] with σ' h1 h2
      exact hshrink σ' h2 h1
    have := le_of_tendsto hcont2 hev
    simpa using this
  -- conclude: the bound is strictly below `ε`
  have hlt : Real.sqrt (ε ^ 2 / (K * A' + 1)) * Real.sqrt (K * A') < ε := by
    rw [← Real.sqrt_mul (div_nonneg (sq_nonneg ε) (by linarith)) (K * A')]
    have h1 : ε ^ 2 / (K * A' + 1) * (K * A') < ε ^ 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith [pow_pos hε 2]
    calc Real.sqrt (ε ^ 2 / (K * A' + 1) * (K * A'))
        < Real.sqrt (ε ^ 2) :=
          Real.sqrt_lt_sqrt
            (mul_nonneg (div_nonneg (sq_nonneg ε) (by linarith)) hKA) h1
      _ = ε := Real.sqrt_sq hε.le
  exact lt_of_le_of_lt hle hlt

/-- **Almost every vertical slice is absolutely continuous on every interval.** Mirror of
`AxisRectModulusBound.ae_horizontal_slice_absolutelyContinuous`, using the vertical profiles
`imageAreaProfileX f (−n) (−n) n`, the null vertical segments
(`countable_pos_volume_image_verticalSeg`), and the vertical master family estimate
(`AxisRectModulusBound.vertical_family_sq_sum_le`). -/
theorem AxisRectModulusBound.ae_vertical_slice_absolutelyContinuous {f : ℂ → ℂ} {K : ℝ}
    (hf : AxisRectModulusBound f K) :
    ∀ᵐ x : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun y : ℝ => f ⟨x, y⟩) a b := by
  classical
  have hcont : Continuous f := hf.2.1.continuous
  have hinj : Function.Injective f := hf.2.1.injective
  have hK1 : (1 : ℝ) ≤ K := hf.1
  -- the good abscissas: differentiable profiles and null segments at every scale
  have hgood : ∀ᵐ x : ℝ, ∀ n : ℕ,
      (DifferentiableAt ℝ (imageAreaProfileX f (-(n : ℝ)) (-(n : ℝ)) n) x
        ∧ 0 ≤ deriv (imageAreaProfileX f (-(n : ℝ)) (-(n : ℝ)) n) x)
      ∧ volume (f '' axisRect x x (-(n : ℝ)) n) = 0 := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    have h1 :=
      (monotone_imageAreaProfileX hcont (-(n : ℝ)) (-(n : ℝ)) n).ae_hasDerivAt_deriv
    have h2 : ∀ᵐ x : ℝ, volume (f '' axisRect x x (-(n : ℝ)) n) = 0 := by
      have hnull : volume {x : ℝ | volume (f '' axisRect x x (-(n : ℝ)) n) ≠ 0} = 0 :=
        (countable_pos_volume_image_verticalSeg hcont hinj (-(n : ℝ)) n).measure_zero _
      rw [MeasureTheory.ae_iff]
      simpa using hnull
    filter_upwards [h1, h2] with x hx1 hx2
    exact ⟨⟨hx1.1.differentiableAt, hx1.2⟩, hx2⟩
  filter_upwards [hgood] with x hx a b
  -- choose a window containing the interval and the abscissa
  obtain ⟨n, hn⟩ := exists_nat_ge (max (max |a| |b|) |x|)
  have ha : |a| ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hb : |b| ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hxn : |x| ≤ n := le_trans (le_max_right _ _) hn
  rw [abs_le] at ha hb hxn
  obtain ⟨⟨hdiff, hD0⟩, hseg⟩ := hx n
  set A' := deriv (imageAreaProfileX f (-(n : ℝ)) (-(n : ℝ)) n) x with hA'
  have hKA : (0 : ℝ) ≤ K * A' := mul_nonneg (by linarith) hD0
  -- the ε–δ criterion
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  refine ⟨ε ^ 2 / (K * A' + 1), div_pos (pow_pos hε 2) (by linarith), ?_⟩
  rintro ⟨N, I⟩ hE hlen
  simp only [AbsolutelyContinuousOnInterval.disjWithin, Set.mem_ofPred_eq] at hE
  dsimp only at hE hlen ⊢
  obtain ⟨hmemE, hdisjE⟩ := hE
  -- normalize the interval endpoints
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, u = fun i => min (I i).1 (I i).2 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℝ, v = fun i => max (I i).1 (I i).2 := ⟨_, rfl⟩
  have huv : ∀ i, u i = min (I i).1 (I i).2 := fun i => by rw [hu]
  have hvv : ∀ i, v i = max (I i).1 (I i).2 := fun i => by rw [hv]
  have humem : ∀ i ∈ Finset.range N, u i ∈ Set.uIcc a b := by
    intro i hi
    obtain ⟨h1, h2⟩ := hmemE i hi
    rw [huv]
    exact ⟨le_min h1.1 h2.1, (min_le_left _ _).trans h1.2⟩
  have hvmem : ∀ i ∈ Finset.range N, v i ∈ Set.uIcc a b := by
    intro i hi
    obtain ⟨h1, h2⟩ := hmemE i hi
    rw [hvv]
    exact ⟨h1.1.trans (le_max_left _ _), max_le h1.2 h2.2⟩
  have hwindow : Set.uIcc a b ⊆ Set.Icc (-(n : ℝ)) n :=
    Set.Icc_subset_Icc (le_min ha.1 hb.1) (max_le ha.2 hb.2)
  have hlen' : ∑ i ∈ Finset.range N, (v i - u i) < ε ^ 2 / (K * A' + 1) := by
    have hconv : ∀ i ∈ Finset.range N, v i - u i = dist (I i).1 (I i).2 := fun i _ => by
      rw [huv, hvv, Real.dist_eq, max_sub_min_eq_abs]
      exact abs_sub_comm _ _
    rwa [Finset.sum_congr rfl hconv]
  -- reduce the target sum to the normalized nondegenerate intervals
  have hswap : ∀ i ∈ Finset.range N,
      dist (f ⟨x, (I i).1⟩) (f ⟨x, (I i).2⟩) = dist (f ⟨x, u i⟩) (f ⟨x, v i⟩) := by
    intro i _
    rw [huv, hvv]
    rcases le_total (I i).1 (I i).2 with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
    · rw [min_eq_right hle, max_eq_left hle, dist_comm]
  rw [Finset.sum_congr rfl hswap]
  set T : Finset ℕ := (Finset.range N).filter (fun i => u i < v i) with hT
  have hTsum : ∑ i ∈ Finset.range N, dist (f ⟨x, u i⟩) (f ⟨x, v i⟩)
      = ∑ i ∈ T, dist (f ⟨x, u i⟩) (f ⟨x, v i⟩) := by
    refine (Finset.sum_filter_of_ne fun i hi hne => ?_).symm
    by_contra hnot
    have huvle : u i ≤ v i := by rw [huv, hvv]; exact min_le_max
    have heq : u i = v i := le_antisymm huvle (not_lt.mp hnot)
    exact hne (by rw [heq, dist_self])
  rw [hTsum]
  -- the σ-shrunk family estimate via Cauchy–Schwarz
  have hshrink : ∀ σ' : ℝ, 0 < σ' → (∀ i ∈ T, u i + σ' < v i) →
      ∑ i ∈ T, dist (f ⟨x, u i + σ'⟩) (f ⟨x, v i⟩)
        ≤ Real.sqrt (ε ^ 2 / (K * A' + 1)) * Real.sqrt (K * A') := by
    intro σ' hσ' hgap
    set e : Fin T.card ↪o ℕ := T.orderEmbOfFin rfl with he
    have heT : ∀ k, e k ∈ T := fun k => Finset.orderEmbOfFin_mem T rfl k
    have heN : ∀ k, e k ∈ Finset.range N := fun k => Finset.filter_subset _ _ (heT k)
    have hreidx : ∀ g : ℕ → ℝ, ∑ i ∈ T, g i = ∑ k : Fin T.card, g (e k) := by
      intro g
      calc ∑ i ∈ T, g i
          = ∑ i ∈ Finset.map (T.orderEmbOfFin rfl).toEmbedding Finset.univ, g i :=
            (Finset.sum_congr (Finset.map_orderEmbOfFin_univ T rfl) fun _ _ => rfl).symm
        _ = ∑ k : Fin T.card, g (T.orderEmbOfFin rfl k) := Finset.sum_map _ _ _
        _ = ∑ k : Fin T.card, g (e k) := by rw [he]
    have hcd : ∀ k : Fin T.card, u (e k) + σ' < v (e k) := fun k => hgap _ (heT k)
    have hsub : ∀ k : Fin T.card,
        Set.Icc (u (e k) + σ') (v (e k)) ⊆ Set.Icc (-(n : ℝ)) n := by
      intro k z hz
      have h1 := hwindow (humem _ (heN k))
      have h2 := hwindow (hvmem _ (heN k))
      exact ⟨by linarith [h1.1, hz.1], le_trans hz.2 h2.2⟩
    have hIcc_sub : ∀ m : Fin T.card,
        Set.Icc (u (e m) + σ') (v (e m)) ⊆ Set.uIoc (I (e m)).1 (I (e m)).2 := by
      intro m z hz
      have h1 : u (e m) < z := by linarith [hz.1]
      have h2 : z ≤ v (e m) := hz.2
      rw [huv] at h1
      rw [hvv] at h2
      rw [Set.mem_uIoc]
      rcases le_total (I (e m)).1 (I (e m)).2 with hle | hle
      · rw [min_eq_left hle] at h1
        rw [max_eq_right hle] at h2
        exact Or.inl ⟨h1, h2⟩
      · rw [min_eq_right hle] at h1
        rw [max_eq_left hle] at h2
        exact Or.inr ⟨h1, h2⟩
    have hdisjF : Pairwise (Function.onFun Disjoint
        fun k : Fin T.card => Set.Icc (u (e k) + σ') (v (e k))) := by
      intro k l hkl
      have hkl' : e k ≠ e l := fun hEq => hkl (e.injective hEq)
      exact ((hdisjE (Finset.mem_coe.mpr (heN k)) (Finset.mem_coe.mpr (heN l))
        hkl').mono (hIcc_sub k) (hIcc_sub l))
    have hest := hf.vertical_family_sq_sum_le (show -(n : ℝ) ≤ x from hxn.1)
      hdiff hseg (c := fun k : Fin T.card => u (e k) + σ')
      (d := fun k : Fin T.card => v (e k)) hcd hsub hdisjF
    rw [← hA'] at hest
    rw [hreidx]
    -- Cauchy–Schwarz with the splitting `D = √w · (D/√w)`
    have hsplit : ∀ k : Fin T.card, dist (f ⟨x, u (e k) + σ'⟩) (f ⟨x, v (e k)⟩)
        = Real.sqrt (v (e k) - (u (e k) + σ'))
            * (dist (f ⟨x, u (e k) + σ'⟩) (f ⟨x, v (e k)⟩)
                / Real.sqrt (v (e k) - (u (e k) + σ'))) := by
      intro k
      rw [mul_comm, div_mul_cancel₀]
      exact (Real.sqrt_pos.mpr (sub_pos.mpr (hcd k))).ne'
    rw [Finset.sum_congr rfl fun k _ => hsplit k]
    refine (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _).trans ?_
    have hw : ∀ k : Fin T.card, Real.sqrt (v (e k) - (u (e k) + σ')) ^ 2
        = v (e k) - (u (e k) + σ') := fun k => Real.sq_sqrt (sub_pos.mpr (hcd k)).le
    have hr : ∀ k : Fin T.card,
        (dist (f ⟨x, u (e k) + σ'⟩) (f ⟨x, v (e k)⟩)
            / Real.sqrt (v (e k) - (u (e k) + σ'))) ^ 2
          = dist (f ⟨x, u (e k) + σ'⟩) (f ⟨x, v (e k)⟩) ^ 2
              / (v (e k) - (u (e k) + σ')) := fun k => by rw [div_pow, hw k]
    rw [Finset.sum_congr rfl fun k _ => hw k, Finset.sum_congr rfl fun k _ => hr k]
    have hwsum : ∑ k : Fin T.card, (v (e k) - (u (e k) + σ'))
        ≤ ε ^ 2 / (K * A' + 1) := by
      have h1 := hreidx fun i => v i - u i
      have h2 : ∑ k : Fin T.card, (v (e k) - (u (e k) + σ'))
          ≤ ∑ k : Fin T.card, (v (e k) - u (e k)) :=
        Finset.sum_le_sum fun k _ => by linarith
      have h3 : ∑ i ∈ T, (v i - u i) ≤ ∑ i ∈ Finset.range N, (v i - u i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i _ _ => by rw [huv, hvv]; exact sub_nonneg.mpr min_le_max
      rw [h1] at h3
      linarith [hlen']
    exact mul_le_mul (Real.sqrt_le_sqrt hwsum) (Real.sqrt_le_sqrt hest)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- pass to the limit `σ' → 0⁺`
  have hle : ∑ i ∈ T, dist (f ⟨x, u i⟩) (f ⟨x, v i⟩)
      ≤ Real.sqrt (ε ^ 2 / (K * A' + 1)) * Real.sqrt (K * A') := by
    have hcont2 : Filter.Tendsto
        (fun σ' : ℝ => ∑ i ∈ T, dist (f ⟨x, u i + σ'⟩) (f ⟨x, v i⟩))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∑ i ∈ T, dist (f ⟨x, u i + 0⟩) (f ⟨x, v i⟩))) := by
      refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      refine Continuous.tendsto ?_ 0
      refine continuous_finsetSum _ fun i _ => Continuous.dist ?_ continuous_const
      refine hcont.comp ?_
      have hmk : (fun σ' : ℝ => (⟨x, u i + σ'⟩ : ℂ))
          = fun σ' : ℝ => (⟨x, u i⟩ : ℂ) + (σ' : ℂ) * Complex.I := by
        funext σ'
        apply Complex.ext <;> simp
      rw [hmk]
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hev : ∀ᶠ σ' in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∑ i ∈ T, dist (f ⟨x, u i + σ'⟩) (f ⟨x, v i⟩)
          ≤ Real.sqrt (ε ^ 2 / (K * A' + 1)) * Real.sqrt (K * A') := by
      have hgapev : ∀ᶠ σ' in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i ∈ T, u i + σ' < v i := by
        rw [Filter.eventually_all_finset]
        intro i hi
        have hgapi : (0 : ℝ) < v i - u i := sub_pos.mpr (Finset.mem_filter.mp hi).2
        refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
        filter_upwards [eventually_lt_nhds hgapi] with σ' hσ'
        linarith
      filter_upwards [hgapev, eventually_mem_nhdsWithin] with σ' h1 h2
      exact hshrink σ' h2 h1
    have := le_of_tendsto hcont2 hev
    simpa using this
  -- conclude: the bound is strictly below `ε`
  have hlt : Real.sqrt (ε ^ 2 / (K * A' + 1)) * Real.sqrt (K * A') < ε := by
    rw [← Real.sqrt_mul (div_nonneg (sq_nonneg ε) (by linarith)) (K * A')]
    have h1 : ε ^ 2 / (K * A' + 1) * (K * A') < ε ^ 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith [pow_pos hε 2]
    calc Real.sqrt (ε ^ 2 / (K * A' + 1) * (K * A'))
        < Real.sqrt (ε ^ 2) :=
          Real.sqrt_lt_sqrt
            (mul_nonneg (div_nonneg (sq_nonneg ε) (by linarith)) hKA) h1
      _ = ε := Real.sqrt_sq hε.le
  exact lt_of_le_of_lt hle hlt

end NoWanderingDomains
