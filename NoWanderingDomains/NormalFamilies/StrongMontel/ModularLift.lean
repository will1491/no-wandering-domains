/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.ModularLambda.TriplyPunctured
import NoWanderingDomains.Hyperbolic.WindingNumber.StarShapedPrimitive

/-!
# Lifting machinery for the Montel–Carathéodory theorem

Three lifting-flavoured ingredients consumed by
`StrongMontel/MontelCaratheodory.lean`:

* `modularLambda_exists_holomorphic_lift_ball`: a holomorphic map from a
  ball into `ℂ ∖ {0, 1}` lifts through the covering
  `modularLambda : 𝔻 → ℂ ∖ {0, 1}` to a holomorphic map into `𝔻`, with a
  **prescribed** fibre point over the center. Prescribing the base point
  is what lets the Montel–Carathéodory argument keep the lifted family
  inside a fixed compact of `𝔻` at the center.
* `modularLambda_exists_compact_section`: over any compact
  `L ⊆ ℂ ∖ {0, 1}` there is a single compact `K ⊆ 𝔻` meeting every
  fibre. Extracted from finitely many local trivializations of the
  covering.
* `exists_log_of_ball_of_ne_zero`: a nonvanishing holomorphic function
  on a ball has a holomorphic logarithm (primitive of `f'/f` via
  `starPrimitive`). This powers the square-root trick in the
  degenerate cases of Montel–Carathéodory.
-/

namespace NoWanderingDomains

open Complex Metric Set

/-- **Holomorphic lifting through `modularLambda` on a ball, with
prescribed base point.** If `f` is holomorphic on `ball c r` omitting
`0` and `1`, and `e₀ ∈ 𝔻` lies over `f c`, then `f` lifts to a
holomorphic `F : ball c r → 𝔻` with `modularLambda ∘ F = f` and
`F c = e₀`. The continuous lift exists by the covering property of
`modularLambda` (`modularLambda_isCoveringMapOn`) and simple
connectivity of the ball; holomorphy follows from the local inverses
of `modularLambda` (`modularLambda_deriv_ne_zero`). -/
theorem modularLambda_exists_holomorphic_lift_ball {f : ℂ → ℂ}
    {c e₀ : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ f (ball c r))
    (hf : ∀ z ∈ ball c r, f z ≠ 0 ∧ f z ≠ 1)
    (hc : c ∈ ball c r)
    (he₀ : e₀ ∈ ball (0 : ℂ) 1) (he₀_eq : modularLambda e₀ = f c) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball c r) ∧
      Set.MapsTo F (ball c r) (ball (0 : ℂ) 1) ∧
      (∀ z ∈ ball c r, modularLambda (F z) = f z) ∧ F c = e₀ := by
  classical
  -- `he₀` is not needed: membership of the lift in the disk is re-derived
  -- below from the junk-value lemma.
  have _ := he₀
  -- Instances making the ball simply connected and locally path-connected.
  have : LocallyPathConnectedSpace (ball c r) :=
    Metric.isOpen_ball.locallyPathConnectedSpace
  have : ContractibleSpace (ball c r) :=
    (convex_ball c r).contractibleSpace ⟨c, hc⟩
  -- The map to lift, as a continuous map on the ball subtype.
  have hΦ_cont : Continuous fun a : ball c r => f ↑a :=
    continuousOn_iff_continuous_domRestrict.mp hd.continuousOn
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : C(ball c r, ℂ), ∀ a, Φ a = f ↑a :=
    ⟨⟨fun a => f ↑a, hΦ_cont⟩, fun _ => rfl⟩
  -- The prescribed fibre point lies over the value at the center.
  have he : modularLambda e₀ = Φ ⟨c, hc⟩ := by
    rw [hΦ]
    exact he₀_eq
  -- The continuous lift with the prescribed base point.
  obtain ⟨Fhat, ⟨hFbase, hFcomp⟩, -⟩ :=
    IsCoveringMapOn.existsUnique_continuousMap_lifts modularLambda_isCoveringMapOn Φ he
      (fun a => by rw [hΦ a]; exact hf _ a.2)
  have hcomm : ∀ z (hz : z ∈ ball c r),
      modularLambda (Fhat ⟨z, hz⟩) = f z := by
    intro z hz
    have h := congrFun hFcomp (⟨z, hz⟩ : ball c r)
    rw [Function.comp_apply, hΦ] at h
    exact h
  -- Extend the lift to all of `ℂ` by a junk value.
  set F : ℂ → ℂ := fun z => if h : z ∈ ball c r then Fhat ⟨z, h⟩ else 0 with hF_def
  have hF_eq : ∀ z (hz : z ∈ ball c r), F z = Fhat ⟨z, hz⟩ := by
    intro z hz
    simp only [hF_def]
    exact dif_pos hz
  have hF_comm : ∀ z ∈ ball c r, modularLambda (F z) = f z := by
    intro z hz
    rw [hF_eq z hz]
    exact hcomm z hz
  have hF_maps : Set.MapsTo F (ball c r) (ball (0 : ℂ) 1) := by
    intro z hz
    by_contra hout
    have h0 : modularLambda (F z) = 0 := modularLambda_eq_zero_of_not_mem_ball hout
    rw [hF_comm z hz] at h0
    exact (hf z hz).1 h0
  have hF_contOn : ContinuousOn F (ball c r) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hrestr : (ball c r).domRestrict F = ⇑Fhat := by
      funext a
      exact hF_eq a.1 a.2
    rw [hrestr]
    exact Fhat.continuous
  -- Holomorphy of the lift via the local inverse of `modularLambda`.
  have hF_diff : DifferentiableOn ℂ F (ball c r) := by
    intro z₀ hz₀
    have hy₀ : F z₀ ∈ ball (0 : ℂ) 1 := hF_maps hz₀
    have hA : AnalyticAt ℂ modularLambda (F z₀) :=
      modularLambda_differentiableOn.analyticAt (Metric.isOpen_ball.mem_nhds hy₀)
    have hstrict : HasStrictDerivAt modularLambda (deriv modularLambda (F z₀)) (F z₀) :=
      hA.hasStrictDerivAt
    have hne : deriv modularLambda (F z₀) ≠ 0 := modularLambda_deriv_ne_zero hy₀
    obtain ⟨g, hg_left, hg_diff⟩ :
        ∃ g : ℂ → ℂ, (∀ᶠ y in nhds (F z₀), g (modularLambda y) = y) ∧
          DifferentiableAt ℂ g (modularLambda (F z₀)) :=
      ⟨hstrict.localInverse modularLambda (deriv modularLambda (F z₀)) (F z₀) hne,
        hstrict.eventually_left_inverse hne,
        (HasStrictDerivAt.hasDerivAt (hstrict.to_localInverse hne)).differentiableAt⟩
    have hg_diff' : DifferentiableAt ℂ g (f z₀) := by
      rw [← hF_comm z₀ hz₀]
      exact hg_diff
    have hf_diff : DifferentiableAt ℂ f z₀ :=
      hd.differentiableAt (Metric.isOpen_ball.mem_nhds hz₀)
    have hRHS : DifferentiableAt ℂ (fun y => g (f y)) z₀ := hg_diff'.comp z₀ hf_diff
    have hF_cont : ContinuousAt F z₀ :=
      hF_contOn.continuousAt (Metric.isOpen_ball.mem_nhds hz₀)
    have hEq : F =ᶠ[nhds z₀] fun y => g (f y) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz₀, hF_cont.eventually hg_left]
        with y hy hgy
      rw [← hF_comm y hy, hgy]
    exact (hRHS.congr_of_eventuallyEq hEq).differentiableWithinAt
  -- The base-point condition.
  have hFc : F c = e₀ := by
    rw [hF_eq c hc]
    exact hFbase
  exact ⟨F, hF_diff, hF_maps, hF_comm, hFc⟩

/-- **A compact section domain for `modularLambda`.** For every compact
`L ⊆ ℂ ∖ {0, 1}` there is a compact `K ⊆ 𝔻` meeting the
`modularLambda`-fibre of every point of `L`. Cover `L` by finitely
many evenly-covered neighborhoods, take continuous local sections from
the trivializations, and collect their images over a compact shrinking
of the cover. -/
theorem modularLambda_exists_compact_section {L : Set ℂ}
    (hL : IsCompact L) (hL_sub : ∀ w ∈ L, w ≠ 0 ∧ w ≠ 1) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ ball (0 : ℂ) 1 ∧
      ∀ w ∈ L, ∃ z ∈ K, modularLambda z = w := by
  classical
  -- A continuous local section of `modularLambda` on a closed ball
  -- around each point of `L`, from the 1-D inverse function theorem.
  have hloc : ∀ i : L, ∃ (g : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧
      ContinuousOn g (closedBall (i : ℂ) ρ) ∧
      ∀ w' ∈ closedBall (i : ℂ) ρ, modularLambda (g w') = w' := by
    rintro ⟨w, hwL⟩
    -- A fibre point over `w`.
    have hw_mem : w ∈ modularLambda '' ball (0 : ℂ) 1 := by
      rw [modularLambda_image]
      exact hL_sub w hwL
    obtain ⟨z₀, hz₀_ball, hz₀_eq⟩ := hw_mem
    -- `modularLambda` is a strict local biholomorphism at `z₀`.
    have hA : AnalyticAt ℂ modularLambda z₀ :=
      modularLambda_differentiableOn.analyticAt (Metric.isOpen_ball.mem_nhds hz₀_ball)
    have hstrict : HasStrictDerivAt modularLambda (deriv modularLambda z₀) z₀ :=
      hA.hasStrictDerivAt
    have hne : deriv modularLambda z₀ ≠ 0 := modularLambda_deriv_ne_zero hz₀_ball
    have hstrictF := hstrict.hasStrictFDerivAt_equiv hne
    set e := hstrictF.toOpenPartialHomeomorph modularLambda
    have hcoe : ⇑e = modularLambda := hstrictF.toOpenPartialHomeomorph_coe
    have hw_target : w ∈ e.target := by
      have h := hstrictF.image_mem_toOpenPartialHomeomorph_target
      rwa [hz₀_eq] at h
    -- A closed ball inside the (open) target.
    obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.isOpen_iff.mp e.open_target w hw_target
    have hcb_sub : closedBall w (ε / 2) ⊆ e.target := fun x hx =>
      hε_sub (Metric.closedBall_subset_ball (half_lt_self hε_pos) hx)
    refine ⟨⇑e.symm, ε / 2, half_pos hε_pos, ?_, ?_⟩
    · exact e.continuousOn_symm.mono hcb_sub
    · intro w' hw'
      have h := e.right_inv (hcb_sub hw')
      rwa [hcoe] at h
  choose g ρ hρ hg hsec using hloc
  -- Finite subcover of `L` by the open balls.
  have hcover : L ⊆ ⋃ i : L, ball (i : ℂ) (ρ i) := fun w hw =>
    Set.mem_iUnion.mpr ⟨⟨w, hw⟩, mem_ball_self (hρ ⟨w, hw⟩)⟩
  obtain ⟨t, ht⟩ := hL.elim_finite_subcover (fun i : L => ball (i : ℂ) (ρ i))
    (fun _ => isOpen_ball) hcover
  -- The compact section domain.
  refine ⟨⋃ i ∈ t, g i '' (L ∩ closedBall (i : ℂ) (ρ i)), ?_, ?_, ?_⟩
  · -- Compactness: finite union of continuous images of compacts.
    exact t.isCompact_biUnion fun i _ =>
      (hL.inter_right isClosed_closedBall).image_of_continuousOn
        ((hg i).mono inter_subset_right)
  · -- Containment in the disk via the junk-value lemma.
    intro x hx
    obtain ⟨i, -, hx_mem⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨w', hw'_mem, hx_eq⟩ := hx_mem
    by_contra hout
    have h0 : modularLambda x = 0 := modularLambda_eq_zero_of_not_mem_ball hout
    rw [← hx_eq, hsec i w' hw'_mem.2] at h0
    exact (hL_sub w' hw'_mem.1).1 h0
  · -- Every fibre over `L` is met.
    intro w hw
    obtain ⟨i, hit, hw_ball⟩ := Set.mem_iUnion₂.mp (ht hw)
    have hw_cb : w ∈ closedBall (i : ℂ) (ρ i) := ball_subset_closedBall hw_ball
    exact ⟨g i w, Set.mem_iUnion₂.mpr ⟨i, hit, Set.mem_image_of_mem _ ⟨hw, hw_cb⟩⟩,
      hsec i w hw_cb⟩

/-- **Holomorphic logarithms on balls.** A nonvanishing holomorphic
function on a ball has a holomorphic logarithm: integrate `f'/f` from
the center (`starPrimitive`, the ball being star-shaped), then adjust
by a constant; `exp ∘ g / f` is locally constant on the (connected)
ball. -/
theorem exists_log_of_ball_of_ne_zero {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ f (ball c r))
    (hf : ∀ z ∈ ball c r, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c r) ∧
      ∀ z ∈ ball c r, Complex.exp (g z) = f z := by
  rcases le_or_gt r 0 with hr | hr
  · -- Empty ball: anything works.
    refine ⟨0, ?_, ?_⟩
    · rw [Metric.ball_eq_empty.mpr hr]
      exact differentiableOn_empty
    · intro z hz
      rw [Metric.ball_eq_empty.mpr hr] at hz
      simp at hz
  have hc : c ∈ ball c r := mem_ball_self hr
  -- The logarithmic derivative is holomorphic on the ball.
  have hderiv_diff : DifferentiableOn ℂ (deriv f) (ball c r) :=
    ((hd.analyticOnNhd Metric.isOpen_ball).deriv).differentiableOn
  have hh_diff : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball c r) :=
    hderiv_diff.div hd hf
  -- Its star-shaped primitive from the center.
  set Lg : ℂ → ℂ := starPrimitive c fun z => deriv f z / f z
  have hLg_deriv : ∀ z ∈ ball c r, HasDerivAt Lg (deriv f z / f z) z := fun z hz =>
    hasDerivAt_starPrimitive Metric.isOpen_ball ((convex_ball c r).starConvex hc)
      hh_diff hz
  have hLg_diff : DifferentiableOn ℂ Lg (ball c r) := fun z hz =>
    (hLg_deriv z hz).differentiableAt.differentiableWithinAt
  -- `exp Lg / f` has vanishing derivative on the ball ...
  have hq_deriv : ∀ z ∈ ball c r,
      HasDerivAt (fun y => Complex.exp (Lg y) / f y) 0 z := by
    intro z hz
    have hfz : f z ≠ 0 := hf z hz
    have hfd : HasDerivAt f (deriv f z) z :=
      (hd.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt
    have hexp : HasDerivAt (fun y => Complex.exp (Lg y))
        (Complex.exp (Lg z) * (deriv f z / f z)) z := (hLg_deriv z hz).cexp
    have hq := hexp.div hfd hfz
    have hval : (Complex.exp (Lg z) * (deriv f z / f z) * f z -
        Complex.exp (Lg z) * deriv f z) / f z ^ 2 = 0 := by
      rw [mul_assoc, div_mul_cancel₀ _ hfz, sub_self, zero_div]
    rwa [hval] at hq
  -- ... hence is constant on the (convex) ball.
  have hq_diff : DifferentiableOn ℂ (fun y => Complex.exp (Lg y) / f y) (ball c r) :=
    fun z hz => (hq_deriv z hz).differentiableAt.differentiableWithinAt
  have hq_fderiv : ∀ z ∈ ball c r,
      fderivWithin ℂ (fun y => Complex.exp (Lg y) / f y) (ball c r) z = 0 := by
    intro z hz
    have h0 : HasFDerivAt (fun y => Complex.exp (Lg y) / f y) (0 : ℂ →L[ℂ] ℂ) z := by
      have h := (hq_deriv z hz).hasFDerivAt
      rwa [ContinuousLinearMap.toSpanSingleton_zero] at h
    exact h0.hasFDerivWithinAt.fderivWithin (Metric.isOpen_ball.uniqueDiffWithinAt hz)
  have hconst : ∀ z ∈ ball c r,
      Complex.exp (Lg z) / f z = Complex.exp (Lg c) / f c := fun z hz =>
    (convex_ball c r).is_const_of_fderivWithin_eq_zero hq_diff hq_fderiv hz hc
  -- Adjust the primitive by a constant.
  refine ⟨fun z => Lg z - Lg c + Complex.log (f c), ?_, ?_⟩
  · exact (hLg_diff.sub_const (Lg c)).add_const (Complex.log (f c))
  · intro z hz
    have hfz : f z ≠ 0 := hf z hz
    have hfc : f c ≠ 0 := hf c hc
    have hec : Complex.exp (Lg c) ≠ 0 := Complex.exp_ne_zero (Lg c)
    have h1 : Complex.exp (Lg z) * f c = Complex.exp (Lg c) * f z := by
      have h := hconst z hz
      rwa [div_eq_div_iff hfz hfc] at h
    rw [Complex.exp_add, Complex.exp_sub, Complex.exp_log hfc,
      div_mul_eq_mul_div, div_eq_iff hec, h1]
    ring

end NoWanderingDomains
