/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.Deformation.DeltaOperator.Representation
import NoWanderingDomains.Dynamics.FatouComponents.Periodic
import NoWanderingDomains.Dynamics.FatouComponents.GrandOrbit

/-!
# Spreading a seed coefficient over a wandering grand orbit

Given a rational map `f` (through `r : RationalData`), a wandering Fatou
component `U` on which every iterate is injective, and a *seed* coefficient
`σ` carried by a set `S` whose points lie in `U`, this file constructs the
**spread** `spreadCoeff r S σ`: the `f`-invariant Beltrami coefficient on `ℂ`
that restricts to `σ` on `U` and vanishes off the grand-orbit saturation
of `S`.

The construction is by the invariance transport law. Iterating the pullback
convention `μ(z) = μ(f z)·conj(f′(z))/f′(z)` (see `IsInvariantBeltrami`)
along orbit segments, a point `z` with `f^[m] z = f^[n] y` for some `y ∈ S`
must carry the value

`μ(z) = σ(y) · Dⁿ(y)/conj(Dⁿ(y)) · conj(Dᵐ(z))/Dᵐ(z)`,

where `Dᵏ = iterDeriv r k` is the finite-chart derivative of the `k`-th
iterate (a product of `fderivRational` along the orbit, `iterDeriv`), and the
two unimodular quotients form the twist cocycle `spreadTwist`. The definition
selects a witness `(m, n, y)` by choice; crucially the selection predicate
depends only on `(r, S, z)` and *not* on `σ`, so `spreadCoeff` is genuinely
pointwise-linear in the seed (`spreadCoeff_add`, `spreadCoeff_smul`).

All dynamical content lives in the theorems, not the definition:

* *witness independence* — cross-time identifications are impossible because
  the components `fcOrbit f U k` are pairwise disjoint (wandering), same-time
  identifications collapse by injectivity of the iterates on `U`, and the
  twist values agree by the derivative cocycle. This yields the restriction
  law `spreadCoeff_restrict` (the spread extends `σ` pointwise on the finite
  part of `U`) and the invariance law `isInvariantBeltrami_spreadCoeff`.
* *size and regularity* — the twist is unimodular (or Lean-junk `0`, on the
  null set of points whose orbit segment meets a critical point or `∞`), so
  the essential sup does not grow (`spreadCoeff_eLpNormEssSup_le`); the
  countable decomposition of the saturation into `(m, n)`-pieces gives
  almost-everywhere measurability (`spreadCoeff_aemeasurable` — plain
  measurability is not available because the value on the exceptional null
  set is produced by an arbitrary choice function).
-/

open MeasureTheory Complex Metric Filter Topology Function OnePoint

namespace NoWanderingDomains

/-! ## The derivative cocycle along orbits -/

/-- The finite-chart derivative of the `m`-th iterate along the orbit of `z`:
the product of `fderivRational` at the finite readings of
`z, f z, …, f^[m−1] z`. Junk if the orbit segment meets `∞` (the reading `0`
is used); all statements either assume finiteness of the segment or work
almost everywhere. -/
noncomputable def iterDeriv (r : RationalData) (m : ℕ) : ℂ → ℂ := fun z =>
  ∏ j ∈ Finset.range m,
    fderivRational r (chartFiniteMap (r.toSphereMap^[j] ((z : ℂ̂))))

/-- The cocycle law for `iterDeriv`: the derivative of the `(m+n)`-th iterate
splits at time `m`, provided the time-`m` point is finite (so that its
finite-chart reading really is the point). -/
theorem iterDeriv_add (r : RationalData) (m n : ℕ) (z : ℂ)
    (hfin : r.toSphereMap^[m] ((z : ℂ̂)) ≠ ∞) :
    iterDeriv r (m + n) z
      = iterDeriv r m z
          * iterDeriv r n (chartFiniteMap (r.toSphereMap^[m] ((z : ℂ̂)))) := by
  have cf : ∀ x : ℂ, chartFiniteMap ((x : ℂ̂)) = x := fun _ => rfl
  obtain ⟨w, hw⟩ : ∃ w : ℂ, r.toSphereMap^[m] ((z : ℂ̂)) = ((w : ℂ̂)) := by
    cases hc : r.toSphereMap^[m] ((z : ℂ̂)) with
    | infty => exact absurd hc hfin
    | coe v => exact ⟨v, rfl⟩
  simp only [iterDeriv]
  rw [Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hw, cf, ← hw, add_comm m j, Function.iterate_add_apply]

/-- Along an orbit segment that stays finite, `iterDeriv` is the honest
derivative of the finite-chart reading of the iterate (chain rule telescoped
through `RationalData.deriv_reading`). -/
theorem iterDeriv_eq_deriv_iterate (r : RationalData) (m : ℕ) (z : ℂ)
    (hfin : ∀ j : ℕ, j ≤ m → r.toSphereMap^[j] ((z : ℂ̂)) ≠ ∞) :
    iterDeriv r m z
      = deriv (fun x : ℂ => chartFiniteMap (r.toSphereMap^[m] ((x : ℂ̂)))) z := by
  have cf : ∀ x : ℂ, chartFiniteMap ((x : ℂ̂)) = x := fun _ => rfl
  have key : ∀ (k : ℕ) (w : ℂ), (∀ j : ℕ, j ≤ k → r.toSphereMap^[j] ((w : ℂ̂)) ≠ ∞) →
      HasDerivAt (fun x : ℂ => chartFiniteMap (r.toSphereMap^[k] ((x : ℂ̂))))
        (iterDeriv r k w) w := by
    intro k
    induction k with
    | zero =>
        intro w _
        have h1 : iterDeriv r 0 w = 1 := by simp [iterDeriv]
        have h2 : (fun x : ℂ => chartFiniteMap (r.toSphereMap^[0] ((x : ℂ̂))))
            = fun x : ℂ => x := funext fun x => rfl
        rw [h1, h2]
        exact hasDerivAt_id w
    | succ k ih =>
        intro w hw
        -- the derivative of the `k`-th reading at `w`, from the induction hypothesis
        have hk := ih w fun j hj => hw j (Nat.le_succ_of_le hj)
        -- the finite reading `u` of the `k`-th iterate at `w`
        obtain ⟨u, hu⟩ : ∃ u : ℂ, r.toSphereMap^[k] ((w : ℂ̂)) = ((u : ℂ̂)) := by
          cases hc : r.toSphereMap^[k] ((w : ℂ̂)) with
          | infty => exact absurd hc (hw k (Nat.le_succ k))
          | coe v => exact ⟨v, rfl⟩
        have hhw : chartFiniteMap (r.toSphereMap^[k] ((w : ℂ̂))) = u := by
          rw [hu, cf]
        -- `u` is not a pole: the `(k+1)`-st point is finite
        have hfu : r.toSphereMap ((u : ℂ̂)) ≠ ∞ := by
          have h1 : r.toSphereMap^[k + 1] ((w : ℂ̂)) ≠ ∞ := hw (k + 1) le_rfl
          rw [Function.iterate_succ_apply', hu] at h1
          exact h1
        have hden : r.denReduced.eval u ≠ 0 := by
          intro h0
          apply hfu
          have hread : r.toSphereMap ((u : ℂ̂))
              = if r.denReduced.eval u = 0 then (∞ : ℂ̂)
                else ((r.numReduced.eval u / r.denReduced.eval u : ℂ) : ℂ̂) := rfl
          rw [hread, if_pos h0]
        -- the derivative of the reading of `f` at the non-pole `u`
        have hg : HasDerivAt (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
            (fderivRational r u) u := by
          have hdiv : HasDerivAt (fun x : ℂ => r.numReduced.eval x / r.denReduced.eval x)
              (((Polynomial.derivative r.numReduced).eval u * r.denReduced.eval u
                  - r.numReduced.eval u * (Polynomial.derivative r.denReduced).eval u)
                / r.denReduced.eval u ^ 2) u :=
            (r.numReduced.hasDerivAt u).div (r.denReduced.hasDerivAt u) hden
          have hev' : (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
              =ᶠ[𝓝 u] fun x : ℂ => r.numReduced.eval x / r.denReduced.eval x := by
            filter_upwards [r.denReduced.continuous.continuousAt.eventually_ne hden] with x hx
            have hread : r.toSphereMap ((x : ℂ̂))
                = if r.denReduced.eval x = 0 then (∞ : ℂ̂)
                  else ((r.numReduced.eval x / r.denReduced.eval x : ℂ) : ℂ̂) := rfl
            rw [hread, if_neg hx, cf]
          have hfd : fderivRational r u
              = ((Polynomial.derivative r.numReduced).eval u * r.denReduced.eval u
                  - r.numReduced.eval u * (Polynomial.derivative r.denReduced).eval u)
                / r.denReduced.eval u ^ 2 := by
            have hwr : r.wronskian.eval u
                = (Polynomial.derivative r.numReduced).eval u * r.denReduced.eval u
                  - r.numReduced.eval u * (Polynomial.derivative r.denReduced).eval u := by
              simp only [RationalData.wronskian, Polynomial.eval_sub, Polynomial.eval_mul]
            have hfd0 : fderivRational r u
                = r.wronskian.eval u / (r.denReduced.eval u) ^ 2 := rfl
            rw [hfd0, hwr]
          rw [hfd]
          exact hdiv.congr_of_eventuallyEq hev'
        -- the set where the `k`-th iterate stays finite is open
        have hopen : IsOpen {x : ℂ | r.toSphereMap^[k] ((x : ℂ̂)) ≠ ∞} := by
          have hc : Continuous fun x : ℂ => r.toSphereMap^[k] ((x : ℂ̂)) :=
            (r.continuous_toSphereMap.iterate k).comp OnePoint.continuous_coe
          exact OnePoint.isClosed_infty.isOpen_compl.preimage hc
        -- near `w`, the `(k+1)`-reading is the composite of the two readings
        have hev : ((fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
              ∘ fun x : ℂ => chartFiniteMap (r.toSphereMap^[k] ((x : ℂ̂))))
            =ᶠ[𝓝 w] fun x : ℂ => chartFiniteMap (r.toSphereMap^[k + 1] ((x : ℂ̂))) := by
          filter_upwards [hopen.mem_nhds (hw k (Nat.le_succ k))] with x hx
          obtain ⟨v, hv⟩ : ∃ v : ℂ, r.toSphereMap^[k] ((x : ℂ̂)) = ((v : ℂ̂)) := by
            cases hc : r.toSphereMap^[k] ((x : ℂ̂)) with
            | infty => exact absurd hc hx
            | coe v => exact ⟨v, rfl⟩
          simp only [Function.comp_apply]
          rw [Function.iterate_succ_apply', hv, cf]
        -- chain rule at the pair of matched points
        have hg2 : HasDerivAt (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
            (fderivRational r u)
            ((fun x : ℂ => chartFiniteMap (r.toSphereMap^[k] ((x : ℂ̂)))) w) := by
          change HasDerivAt _ _ (chartFiniteMap (r.toSphereMap^[k] ((w : ℂ̂))))
          rw [hhw]
          exact hg
        have hcomp := HasDerivAt.comp w hg2 hk
        -- convert the derivative value through the cocycle product
        have hval : iterDeriv r (k + 1) w = fderivRational r u * iterDeriv r k w := by
          have h1 : iterDeriv r (k + 1) w
              = iterDeriv r k w
                  * fderivRational r (chartFiniteMap (r.toSphereMap^[k] ((w : ℂ̂)))) := by
            simp only [iterDeriv]
            exact Finset.prod_range_succ _ k
          rw [h1, hhw, mul_comm]
        rw [hval]
        exact hcomp.congr_of_eventuallyEq hev.symm
  exact (key m z hfin).deriv.symm

/-! ## The spread coefficient -/

/-- The **twist cocycle** transporting a seed value at `y` (pushed forward
`n` steps) back to `z` (pulled back `m` steps):
`Dⁿ(y)/conj(Dⁿ(y)) · conj(Dᵐ(z))/Dᵐ(z)`. Unimodular whenever both iterate
derivatives are nonzero; the Lean junk value when one vanishes is `0`
(as `0/0 = 0`), which is measure-theoretically harmless — such `z` lie in
the countable union of iterated preimages of the critical points and `∞`,
a null set. -/
noncomputable def spreadTwist (r : RationalData) (m n : ℕ) (z y : ℂ) : ℂ :=
  iterDeriv r n y / starRingEnd ℂ (iterDeriv r n y)
    * (starRingEnd ℂ (iterDeriv r m z) / iterDeriv r m z)

/-- The **spread** of a seed `σ` carried by `S ⊆ ℂ` to a coefficient on all
of `ℂ`: at a point `z` of the grand-orbit saturation of `S` — i.e. admitting
`(m, n, y)` with `y ∈ S` and `f^[m] z = f^[n] y` — the value is the twisted
seed value `spreadTwist · σ(y)` at a chosen witness; elsewhere `0`.

The witness is produced by `Classical.choose` from a predicate that mentions
only `r`, `S`, and `z` — never `σ` — so the map `σ ↦ spreadCoeff r S σ` is
pointwise linear by construction. Independence of the value from the chosen
witness is *not* built into the definition; it is the content of the
restriction and invariance theorems below, under the wandering/injectivity
hypothesis package. -/
noncomputable def spreadCoeff (r : RationalData) (S : Set ℂ) (σ : ℂ → ℂ) :
    ℂ → ℂ := fun z =>
  open Classical in
  if h : ∃ p : ℕ × ℕ × ℂ, p.2.2 ∈ S ∧
      r.toSphereMap^[p.1] ((z : ℂ̂)) = r.toSphereMap^[p.2.1] ((p.2.2 : ℂ̂))
  then
    spreadTwist r (Classical.choose h).1 (Classical.choose h).2.1 z
        (Classical.choose h).2.2
      * σ (Classical.choose h).2.2
  else 0

/-- **Additivity in the seed.** The witness selection does not depend on the
seed, so the spread of a sum is the sum of the spreads, pointwise and
unconditionally. -/
theorem spreadCoeff_add (r : RationalData) (S : Set ℂ) (σ₁ σ₂ : ℂ → ℂ) :
    spreadCoeff r S (fun z => σ₁ z + σ₂ z)
      = fun z => spreadCoeff r S σ₁ z + spreadCoeff r S σ₂ z := by
  funext z
  unfold spreadCoeff
  by_cases h : ∃ p : ℕ × ℕ × ℂ, p.2.2 ∈ S ∧
      r.toSphereMap^[p.1] ((z : ℂ̂)) = r.toSphereMap^[p.2.1] ((p.2.2 : ℂ̂))
  · simp only [dif_pos h]
    ring
  · simp only [dif_neg h]
    ring

/-- **Homogeneity in the seed.** As for additivity: the selection is
seed-independent, so scalars pass through pointwise and unconditionally. -/
theorem spreadCoeff_smul (r : RationalData) (S : Set ℂ) (c : ℂ) (σ : ℂ → ℂ) :
    spreadCoeff r S (fun z => c * σ z)
      = fun z => c * spreadCoeff r S σ z := by
  funext z
  unfold spreadCoeff
  by_cases h : ∃ p : ℕ × ℕ × ℂ, p.2.2 ∈ S ∧
      r.toSphereMap^[p.1] ((z : ℂ̂)) = r.toSphereMap^[p.2.1] ((p.2.2 : ℂ̂))
  · simp only [dif_pos h]
    ring
  · simp only [dif_neg h]
    ring

/-! ## The hypothesis package

The dynamical theorems below share the following data: a wandering Fatou
component `U` of `f = r.toSphereMap` with all iterates injective on `U`,
whose forward orbit components avoid `∞`, with no critical point of any
iterate on `U` (phrased through the nonvanishing of `iterDeriv`); a carrier
`S` whose points lie in `U`; and a seed `σ` vanishing off `S`. The interface
theorem of `EventualInjectivity/Package.lean` produces exactly this package from an
arbitrary wandering component. -/

/-- **The spread extends the seed.** On the finite part of `U`, the spread
equals `σ` pointwise: a witness `(m, n, y)` for `z ∈ U` forces `m = n` (the
orbit components are pairwise disjoint) and then `y = z` (injectivity of
`f^[m]` on `U`), and the twist collapses to `1` because the iterate
derivative at `z` does not vanish; points of `U ∖ S` admit no witness at
all, matching `σ = 0` there. -/
theorem spreadCoeff_restrict {r : RationalData} (hd : 1 ≤ r.degree)
    {U : Set ℂ̂} {S : Set ℂ} {σ : ℂ → ℂ}
    (hU : IsFatouComponent r.toSphereMap U)
    (hW : IsWandering r.toSphereMap U)
    (hinj : ∀ n : ℕ, Set.InjOn (r.toSphereMap^[n]) U)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ U) → ∀ n : ℕ, iterDeriv r n z ≠ 0)
    (hS : ∀ z ∈ S, ((z : ℂ̂) ∈ U))
    (hσ : ∀ z : ℂ, z ∉ S → σ z = 0) :
    ∀ z : ℂ, ((z : ℂ̂) ∈ U) → spreadCoeff r S σ z = σ z := by
  -- the map is rational of degree ≥ 1, hence open
  have hfr : IsRational r.toSphereMap := ⟨r, rfl⟩
  have hdeg : 1 ≤ degreeOfRational r.toSphereMap := by
    rw [degreeOfRational_eq_of_witness r.toSphereMap r rfl]; exact hd
  have hfo : IsOpenMap r.toSphereMap := hfr.isOpenMap (hfr.ne_const hdeg)
  -- forward orbit membership in the orbit components
  have hmem : ∀ (w : ℂ̂), w ∈ U → ∀ k : ℕ,
      r.toSphereMap^[k] w ∈ fcOrbit r.toSphereMap U k := by
    intro w hw k
    have hfwd : ∀ j : ℕ, r.toSphereMap^[j] w ∈ FatouSet r.toSphereMap := by
      intro j
      induction j with
      | zero => simpa using hU.subset_fatouSet hw
      | succ j ih =>
          rw [Function.iterate_succ_apply']
          exact apply_mem_fatouSet hfo ih
    exact Set.mem_biUnion hw (mem_connectedComponentIn (hfwd k))
  -- witness independence: two witnesses over `U` force equal offsets and points
  have core : ∀ (x y y2 : ℂ) (m n m2 n2 : ℕ), ((y : ℂ̂)) ∈ U → ((y2 : ℂ̂)) ∈ U →
      r.toSphereMap^[m] ((x : ℂ̂)) = r.toSphereMap^[n] ((y : ℂ̂)) →
      r.toSphereMap^[m2] ((x : ℂ̂)) = r.toSphereMap^[n2] ((y2 : ℂ̂)) →
      n + m2 = n2 + m ∧ y = y2 := by
    intro x y y2 m n m2 n2 hyU hy2U hw1 hw2
    have e1 : r.toSphereMap^[n + m2] ((y : ℂ̂)) = r.toSphereMap^[n2 + m] ((y2 : ℂ̂)) := by
      calc r.toSphereMap^[n + m2] ((y : ℂ̂))
          = r.toSphereMap^[m2 + n] ((y : ℂ̂)) := by rw [Nat.add_comm n m2]
        _ = r.toSphereMap^[m2] (r.toSphereMap^[n] ((y : ℂ̂))) :=
            Function.iterate_add_apply _ m2 n _
        _ = r.toSphereMap^[m2] (r.toSphereMap^[m] ((x : ℂ̂))) := by rw [hw1]
        _ = r.toSphereMap^[m2 + m] ((x : ℂ̂)) := (Function.iterate_add_apply _ m2 m _).symm
        _ = r.toSphereMap^[m + m2] ((x : ℂ̂)) := by rw [Nat.add_comm m2 m]
        _ = r.toSphereMap^[m] (r.toSphereMap^[m2] ((x : ℂ̂))) :=
            Function.iterate_add_apply _ m m2 _
        _ = r.toSphereMap^[m] (r.toSphereMap^[n2] ((y2 : ℂ̂))) := by rw [hw2]
        _ = r.toSphereMap^[m + n2] ((y2 : ℂ̂)) := (Function.iterate_add_apply _ m n2 _).symm
        _ = r.toSphereMap^[n2 + m] ((y2 : ℂ̂)) := by rw [Nat.add_comm m n2]
    have htime : n + m2 = n2 + m := by
      by_contra hne
      have hdisj : Disjoint (fcOrbit r.toSphereMap U (n + m2))
          (fcOrbit r.toSphereMap U (n2 + m)) := hW hne
      have h1 : r.toSphereMap^[n + m2] ((y : ℂ̂)) ∈ fcOrbit r.toSphereMap U (n + m2) :=
        hmem ((y : ℂ̂)) hyU (n + m2)
      have h2 : r.toSphereMap^[n + m2] ((y : ℂ̂)) ∈ fcOrbit r.toSphereMap U (n2 + m) := by
        rw [e1]; exact hmem ((y2 : ℂ̂)) hy2U (n2 + m)
      exact Set.disjoint_left.mp hdisj h1 h2
    have hyy : ((y : ℂ̂)) = ((y2 : ℂ̂)) := by
      apply hinj (n + m2) hyU hy2U
      calc r.toSphereMap^[n + m2] ((y : ℂ̂))
          = r.toSphereMap^[n2 + m] ((y2 : ℂ̂)) := e1
        _ = r.toSphereMap^[n + m2] ((y2 : ℂ̂)) := by rw [htime]
    exact ⟨htime, OnePoint.coe_eq_coe.mp hyy⟩
  intro z hzU
  by_cases hzS : z ∈ S
  · -- on `S` the trivial witness `(0, 0, z)` exists and pins down the value
    have hex : ∃ p : ℕ × ℕ × ℂ, p.2.2 ∈ S ∧
        r.toSphereMap^[p.1] ((z : ℂ̂)) = r.toSphereMap^[p.2.1] ((p.2.2 : ℂ̂)) :=
      ⟨(0, 0, z), hzS, rfl⟩
    unfold spreadCoeff
    rw [dif_pos hex]
    obtain ⟨hyS, hw⟩ := Classical.choose_spec hex
    obtain ⟨htime, hyz⟩ := core z (Classical.choose hex).2.2 z (Classical.choose hex).1
      (Classical.choose hex).2.1 0 0 (hS _ hyS) hzU hw rfl
    have hnm : (Classical.choose hex).2.1 = (Classical.choose hex).1 := by omega
    rw [hyz, hnm]
    -- the twist collapses to 1 since the iterate derivative at z does not vanish
    have hDne : iterDeriv r (Classical.choose hex).1 z ≠ 0 := hcrit z hzU _
    have hDnec : (starRingEnd ℂ) (iterDeriv r (Classical.choose hex).1 z) ≠ 0 := by
      intro h0
      apply hDne
      have h1 := congrArg (starRingEnd ℂ) h0
      simpa using h1
    have h1 : spreadTwist r (Classical.choose hex).1 (Classical.choose hex).1 z z = 1 := by
      unfold spreadTwist
      rw [div_mul_div_comm, mul_comm (iterDeriv r (Classical.choose hex).1 z)
        ((starRingEnd ℂ) (iterDeriv r (Classical.choose hex).1 z))]
      exact div_self (mul_ne_zero hDnec hDne)
    rw [h1, one_mul]
  · -- off `S` there is no witness at all, matching `σ = 0`
    have hnex : ¬ ∃ p : ℕ × ℕ × ℂ, p.2.2 ∈ S ∧
        r.toSphereMap^[p.1] ((z : ℂ̂)) = r.toSphereMap^[p.2.1] ((p.2.2 : ℂ̂)) := by
      rintro ⟨⟨m, n, y⟩, hyS, hw⟩
      obtain ⟨-, hyz⟩ := core z y z m n 0 0 (hS _ hyS) hzU hw rfl
      exact hzS (hyz ▸ hyS)
    unfold spreadCoeff
    rw [dif_neg hnex]
    exact (hσ z hzS).symm

/-- **Almost-everywhere measurability of the spread.** The saturation
decomposes into the countable family of `(m, n)`-pieces; on each piece, off
the null set of orbit segments meeting critical points or `∞`, the witness
point `y` is uniquely determined (wandering plus injectivity) and depends on
`z` through local holomorphic inverse branches, so the spread agrees a.e.
with a measurable function. Plain measurability is not claimed: on the
exceptional null set the value is produced by an arbitrary choice
function. -/
theorem spreadCoeff_aemeasurable {r : RationalData} (hd : 1 ≤ r.degree)
    {U : Set ℂ̂} {S : Set ℂ} {σ : ℂ → ℂ}
    (hU : IsFatouComponent r.toSphereMap U)
    (hW : IsWandering r.toSphereMap U)
    (hinj : ∀ n : ℕ, Set.InjOn (r.toSphereMap^[n]) U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit r.toSphereMap U n)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ U) → ∀ n : ℕ, iterDeriv r n z ≠ 0)
    (hS : ∀ z ∈ S, ((z : ℂ̂) ∈ U)) (hSm : MeasurableSet S)
    (_hσ : ∀ z : ℂ, z ∉ S → σ z = 0) (hσm : Measurable σ) :
    AEMeasurable (spreadCoeff r S σ) volume := by
  classical
  -- the map is rational of degree ≥ 1, hence open
  have hfr : IsRational r.toSphereMap := ⟨r, rfl⟩
  have hdeg : 1 ≤ degreeOfRational r.toSphereMap := by
    rw [degreeOfRational_eq_of_witness r.toSphereMap r rfl]; exact hd
  have hfo : IsOpenMap r.toSphereMap := hfr.isOpenMap (hfr.ne_const hdeg)
  -- conjugation preserves nonvanishing
  have hconj_ne : ∀ x : ℂ, x ≠ 0 → (starRingEnd ℂ) x ≠ 0 := by
    intro x hx h0
    apply hx
    have h1 := congrArg (starRingEnd ℂ) h0
    simpa using h1
  -- forward orbit membership in the orbit components
  have hmem : ∀ (w : ℂ̂), w ∈ U → ∀ k : ℕ,
      r.toSphereMap^[k] w ∈ fcOrbit r.toSphereMap U k := by
    intro w hw k
    have hfwd : ∀ j : ℕ, r.toSphereMap^[j] w ∈ FatouSet r.toSphereMap := by
      intro j
      induction j with
      | zero => simpa using hU.subset_fatouSet hw
      | succ j ih =>
          rw [Function.iterate_succ_apply']
          exact apply_mem_fatouSet hfo ih
    exact Set.mem_biUnion hw (mem_connectedComponentIn (hfwd k))
  -- orbits of `U` avoid `∞`
  have hfinU : ∀ (y : ℂ), ((y : ℂ̂)) ∈ U → ∀ k : ℕ,
      r.toSphereMap^[k] ((y : ℂ̂)) ≠ ∞ :=
    fun y hy k h => hinf k (h ▸ hmem ((y : ℂ̂)) hy k)
  -- witness independence: two witnesses over `U` force equal offsets and points
  have core : ∀ (x y y2 : ℂ) (m n m2 n2 : ℕ), ((y : ℂ̂)) ∈ U → ((y2 : ℂ̂)) ∈ U →
      r.toSphereMap^[m] ((x : ℂ̂)) = r.toSphereMap^[n] ((y : ℂ̂)) →
      r.toSphereMap^[m2] ((x : ℂ̂)) = r.toSphereMap^[n2] ((y2 : ℂ̂)) →
      n + m2 = n2 + m ∧ y = y2 := by
    intro x y y2 m n m2 n2 hyU hy2U hw1 hw2
    have e1 : r.toSphereMap^[n + m2] ((y : ℂ̂)) = r.toSphereMap^[n2 + m] ((y2 : ℂ̂)) := by
      calc r.toSphereMap^[n + m2] ((y : ℂ̂))
          = r.toSphereMap^[m2 + n] ((y : ℂ̂)) := by rw [Nat.add_comm n m2]
        _ = r.toSphereMap^[m2] (r.toSphereMap^[n] ((y : ℂ̂))) :=
            Function.iterate_add_apply _ m2 n _
        _ = r.toSphereMap^[m2] (r.toSphereMap^[m] ((x : ℂ̂))) := by rw [hw1]
        _ = r.toSphereMap^[m2 + m] ((x : ℂ̂)) := (Function.iterate_add_apply _ m2 m _).symm
        _ = r.toSphereMap^[m + m2] ((x : ℂ̂)) := by rw [Nat.add_comm m2 m]
        _ = r.toSphereMap^[m] (r.toSphereMap^[m2] ((x : ℂ̂))) :=
            Function.iterate_add_apply _ m m2 _
        _ = r.toSphereMap^[m] (r.toSphereMap^[n2] ((y2 : ℂ̂))) := by rw [hw2]
        _ = r.toSphereMap^[m + n2] ((y2 : ℂ̂)) := (Function.iterate_add_apply _ m n2 _).symm
        _ = r.toSphereMap^[n2 + m] ((y2 : ℂ̂)) := by rw [Nat.add_comm m n2]
    have htime : n + m2 = n2 + m := by
      by_contra hne
      have hdisj : Disjoint (fcOrbit r.toSphereMap U (n + m2))
          (fcOrbit r.toSphereMap U (n2 + m)) := hW hne
      have h1 : r.toSphereMap^[n + m2] ((y : ℂ̂)) ∈ fcOrbit r.toSphereMap U (n + m2) :=
        hmem ((y : ℂ̂)) hyU (n + m2)
      have h2 : r.toSphereMap^[n + m2] ((y : ℂ̂)) ∈ fcOrbit r.toSphereMap U (n2 + m) := by
        rw [e1]; exact hmem ((y2 : ℂ̂)) hy2U (n2 + m)
      exact Set.disjoint_left.mp hdisj h1 h2
    have hyy : ((y : ℂ̂)) = ((y2 : ℂ̂)) := by
      apply hinj (n + m2) hyU hy2U
      calc r.toSphereMap^[n + m2] ((y : ℂ̂))
          = r.toSphereMap^[n2 + m] ((y2 : ℂ̂)) := e1
        _ = r.toSphereMap^[n + m2] ((y2 : ℂ̂)) := by rw [htime]
    exact ⟨htime, OnePoint.coe_eq_coe.mp hyy⟩
  -- the twist does not depend on the witness offsets, given the time relation
  have tweq : ∀ (x y : ℂ) (m n m2 n2 : ℕ), ((y : ℂ̂)) ∈ U →
      r.toSphereMap^[m] ((x : ℂ̂)) = r.toSphereMap^[n] ((y : ℂ̂)) →
      r.toSphereMap^[m2] ((x : ℂ̂)) = r.toSphereMap^[n2] ((y : ℂ̂)) →
      n + m2 = n2 + m →
      spreadTwist r m n x y = spreadTwist r m2 n2 x y := by
    intro x y m n m2 n2 hyU hw1 hw2 htime
    have hfy : ∀ k : ℕ, r.toSphereMap^[k] ((y : ℂ̂)) ≠ ∞ := hfinU y hyU
    have hxm : r.toSphereMap^[m] ((x : ℂ̂)) ≠ ∞ := by rw [hw1]; exact hfy n
    have hxm2 : r.toSphereMap^[m2] ((x : ℂ̂)) ≠ ∞ := by rw [hw2]; exact hfy n2
    have hc1 := iterDeriv_add r m m2 x hxm
    have hc2 := iterDeriv_add r m2 m x hxm2
    have hc3 := iterDeriv_add r n m2 y (hfy n)
    have hc4 := iterDeriv_add r n2 m y (hfy n2)
    rw [← hw1] at hc3
    rw [← hw2] at hc4
    have hane : iterDeriv r n y ≠ 0 := hcrit y hyU n
    have hbne : iterDeriv r n2 y ≠ 0 := hcrit y hyU n2
    have hNne : iterDeriv r (n + m2) y ≠ 0 := hcrit y hyU (n + m2)
    unfold spreadTwist
    set a := iterDeriv r n y with ha
    set b := iterDeriv r n2 y with hb
    set c := iterDeriv r m x with hc
    set d := iterDeriv r m2 x with hdd
    set p := iterDeriv r m2 (chartFiniteMap (r.toSphereMap^[m] ((x : ℂ̂)))) with hp
    set q := iterDeriv r m (chartFiniteMap (r.toSphereMap^[m2] ((x : ℂ̂)))) with hq
    have hapbq : a * p = b * q := by rw [← hc3, ← hc4, htime]
    have hcpdq : c * p = d * q := by rw [← hc1, ← hc2, Nat.add_comm m m2]
    have hapne : a * p ≠ 0 := by rw [← hc3]; exact hNne
    have hpne : p ≠ 0 := fun h => hapne (by rw [h, mul_zero])
    have hqne : q ≠ 0 := fun h => hapne (by rw [hapbq, h, mul_zero])
    by_cases hcz : c = 0
    · have hdz : d = 0 := by
        have h0 : d * q = 0 := by rw [← hcpdq, hcz, zero_mul]
        exact (mul_eq_zero.mp h0).resolve_right hqne
      rw [hcz, hdz]
      simp
    · have hdz : d ≠ 0 := by
        intro h0
        apply mul_ne_zero hcz hpne
        rw [hcpdq, h0, zero_mul]
      have had : a * d = b * c := by
        have h1 : a * d * (p * q) = b * c * (p * q) := by
          calc a * d * (p * q) = (a * p) * (d * q) := by ring
            _ = (b * q) * (c * p) := by rw [hapbq, ← hcpdq]
            _ = b * c * (p * q) := by ring
        exact mul_right_cancel₀ (mul_ne_zero hpne hqne) h1
      have hadc : (starRingEnd ℂ) a * (starRingEnd ℂ) d
          = (starRingEnd ℂ) b * (starRingEnd ℂ) c := by
        have h2 := congrArg (starRingEnd ℂ) had
        simpa [map_mul] using h2
      rw [div_mul_div_comm, div_mul_div_comm,
        div_eq_div_iff (mul_ne_zero (hconj_ne a hane) hcz)
          (mul_ne_zero (hconj_ne b hbne) hdz)]
      linear_combination ((starRingEnd ℂ) b * (starRingEnd ℂ) c) * had - (b * c) * hadc
  -- the spread evaluates through ANY witness, not just the chosen one
  have hval : ∀ (x y : ℂ) (k l : ℕ), y ∈ S →
      r.toSphereMap^[k] ((x : ℂ̂)) = r.toSphereMap^[l] ((y : ℂ̂)) →
      spreadCoeff r S σ x = spreadTwist r k l x y * σ y := by
    intro x y k l hyS hw
    have hex : ∃ p : ℕ × ℕ × ℂ, p.2.2 ∈ S ∧
        r.toSphereMap^[p.1] ((x : ℂ̂)) = r.toSphereMap^[p.2.1] ((p.2.2 : ℂ̂)) :=
      ⟨(k, l, y), hyS, hw⟩
    unfold spreadCoeff
    rw [dif_pos hex]
    obtain ⟨hy'S, hw'⟩ := Classical.choose_spec hex
    obtain ⟨htime, hyy⟩ := core x (Classical.choose hex).2.2 y (Classical.choose hex).1
      (Classical.choose hex).2.1 k l (hS _ hy'S) (hS _ hyS) hw' hw
    rw [hyy] at hw' ⊢
    rw [tweq x y (Classical.choose hex).1 (Classical.choose hex).2.1 k l
      (hS _ hyS) hw' hw htime]
  -- rational data for the iterates and the polynomial form of the readings
  have hRex : ∀ n : ℕ, ∃ s : RationalData, r.toSphereMap^[n] = s.toSphereMap :=
    fun n => hfr.iterate hdeg n
  choose R hR using hRex
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → ℂ → ℂ, ∀ (n : ℕ) (z : ℂ),
      F n z = chartFiniteMap (r.toSphereMap^[n] ((z : ℂ̂))) :=
    ⟨fun n z => chartFiniteMap (r.toSphereMap^[n] ((z : ℂ̂))), fun _ _ => rfl⟩
  have hFrat : ∀ (n : ℕ) (z : ℂ),
      F n z = ((R n).numReduced.eval z) / ((R n).denReduced.eval z) := by
    intro n z
    rw [hFdef n z, hR n]
    have hread : (R n).toSphereMap ((z : ℂ̂))
        = if (R n).denReduced.eval z = 0 then (∞ : ℂ̂)
          else ((((R n).numReduced.eval z) / ((R n).denReduced.eval z) : ℂ) : ℂ̂) := rfl
    rw [hread]
    by_cases h : (R n).denReduced.eval z = 0
    · rw [if_pos h, h, div_zero]
      rfl
    · rw [if_neg h]
      rfl
  have hpole : ∀ (n : ℕ) (z : ℂ),
      r.toSphereMap^[n] ((z : ℂ̂)) = ∞ ↔ (R n).denReduced.eval z = 0 := by
    intro n z
    rw [hR n]
    have hread : (R n).toSphereMap ((z : ℂ̂))
        = if (R n).denReduced.eval z = 0 then (∞ : ℂ̂)
          else ((((R n).numReduced.eval z) / ((R n).denReduced.eval z) : ℂ) : ℂ̂) := rfl
    rw [hread]
    by_cases h : (R n).denReduced.eval z = 0
    · simp [h]
    · simp [h, OnePoint.coe_ne_infty]
  have hcoeF : ∀ (n : ℕ) (z : ℂ), r.toSphereMap^[n] ((z : ℂ̂)) ≠ ∞ →
      ((F n z : ℂ) : ℂ̂) = r.toSphereMap^[n] ((z : ℂ̂)) := by
    intro n z hz
    obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hz
    rw [hFdef n z, ← hw]
    rfl
  have hFmeas : ∀ n : ℕ, Measurable (F n) := by
    intro n
    have h1 : F n = fun z => ((R n).numReduced.eval z) / ((R n).denReduced.eval z) :=
      funext (hFrat n)
    rw [h1]
    exact ((R n).numReduced.continuous.measurable).div
      ((R n).denReduced.continuous.measurable)
  -- the finite part of `U`
  set Uf : Set ℂ := (fun z : ℂ => ((z : ℂ̂))) ⁻¹' U with hUfdef
  have hUf_open : IsOpen Uf := hU.isOpen.preimage OnePoint.continuous_coe
  have hSUf : S ⊆ Uf := fun y hy => hS y hy
  have hUf_cont : ∀ n : ℕ, ContinuousOn (F n) Uf := by
    intro n
    have h1 : ContinuousOn
        (fun z : ℂ => ((R n).numReduced.eval z) / ((R n).denReduced.eval z)) Uf := by
      refine ContinuousOn.div ((R n).numReduced.continuous.continuousOn)
        ((R n).denReduced.continuous.continuousOn) ?_
      intro z hz h0
      exact hfinU z hz n ((hpole n z).mpr h0)
    have h2 : F n = fun z : ℂ => ((R n).numReduced.eval z) / ((R n).denReduced.eval z) :=
      funext (hFrat n)
    rw [h2]
    exact h1
  have hFinj : ∀ n : ℕ, Set.InjOn (F n) Uf := by
    intro n z1 hz1 z2 hz2 he
    have h1 : r.toSphereMap^[n] ((z1 : ℂ̂)) = r.toSphereMap^[n] ((z2 : ℂ̂)) := by
      rw [← hcoeF n z1 (hfinU z1 hz1 n), ← hcoeF n z2 (hfinU z2 hz2 n), he]
    exact OnePoint.coe_eq_coe.mp (hinj n hz1 hz2 h1)
  have hPol : PolishSpace ↥Uf := hUf_open.polishSpace
  have hemb : ∀ n : ℕ, MeasurableEmbedding (Uf.domRestrict (F n)) := by
    intro n
    exact Continuous.measurableEmbedding ((hUf_cont n).domRestrict)
      (Set.injOn_iff_injective.mp (hFinj n))
  -- measurability of the iterated derivative and the seed-side factor
  have hconj_meas : Measurable (fun w : ℂ => (starRingEnd ℂ) w) :=
    Complex.continuous_conj.measurable
  have hfd_meas : Measurable (fderivRational r) := by
    have h1 : fderivRational r
        = fun w => (r.wronskian.eval w) / ((r.denReduced.eval w) ^ 2) := rfl
    rw [h1]
    exact (r.wronskian.continuous.measurable).div
      ((r.denReduced.continuous.pow 2).measurable)
  have hiter_meas : ∀ n : ℕ, Measurable (fun z : ℂ => iterDeriv r n z) := by
    intro n
    have h1 : (fun z : ℂ => iterDeriv r n z)
        = fun z => ∏ j ∈ Finset.range n, fderivRational r (F j z) := by
      funext z
      simp only [iterDeriv]
      exact Finset.prod_congr rfl fun j _ => by rw [hFdef j z]
    rw [h1]
    exact Finset.measurable_prod _ fun j _ => hfd_meas.comp (hFmeas j)
  have hτ_meas : ∀ n : ℕ, Measurable (fun y : ℂ =>
      iterDeriv r n y / (starRingEnd ℂ) (iterDeriv r n y) * σ y) :=
    fun n => (((hiter_meas n).div (hconj_meas.comp (hiter_meas n))).mul hσm)
  -- measurable extension of the seed-side factor through the reading embedding
  have hext : ∀ n : ℕ, ∃ h : ℂ → ℂ, Measurable h ∧
      ∀ u : ↥Uf, h (Uf.domRestrict (F n) u)
        = iterDeriv r n (u : ℂ) / (starRingEnd ℂ) (iterDeriv r n (u : ℂ)) * σ (u : ℂ) := by
    intro n
    obtain ⟨h, hhm, hhc⟩ := (hemb n).exists_measurable_extend
      ((hτ_meas n).comp measurable_subtype_coe) (fun _ => ⟨(0 : ℂ)⟩)
    exact ⟨h, hhm, fun u => congrFun hhc u⟩
  choose HH hHm hHs using hext
  -- the pieces of the saturation
  set A : ℕ → ℕ → Set ℂ := fun m n => {z : ℂ | ∃ y ∈ S,
      r.toSphereMap^[m] ((z : ℂ̂)) = r.toSphereMap^[n] ((y : ℂ̂))} with hAdef
  have hAmeas : ∀ m n : ℕ, MeasurableSet (A m n) := by
    intro m n
    have hSsub : MeasurableSet ((Subtype.val : ↥Uf → ℂ) ⁻¹' S) :=
      measurable_subtype_coe hSm
    have himg : MeasurableSet (Uf.domRestrict (F n) '' (Subtype.val ⁻¹' S)) :=
      (hemb n).measurableSet_image' hSsub
    have hVopen : IsOpen {z : ℂ | r.toSphereMap^[m] ((z : ℂ̂)) ≠ ∞} := by
      have hc : Continuous fun z : ℂ => r.toSphereMap^[m] ((z : ℂ̂)) :=
        (r.continuous_toSphereMap.iterate m).comp OnePoint.continuous_coe
      exact OnePoint.isClosed_infty.isOpen_compl.preimage hc
    have hAeq : A m n = {z : ℂ | r.toSphereMap^[m] ((z : ℂ̂)) ≠ ∞}
        ∩ (F m) ⁻¹' (Uf.domRestrict (F n) '' (Subtype.val ⁻¹' S)) := by
      ext z
      constructor
      · rintro ⟨y, hyS, hw⟩
        have hyUf : y ∈ Uf := hSUf hyS
        have hfin : r.toSphereMap^[n] ((y : ℂ̂)) ≠ ∞ := hfinU y hyUf n
        have hzfin : r.toSphereMap^[m] ((z : ℂ̂)) ≠ ∞ := by rw [hw]; exact hfin
        refine ⟨hzfin, ⟨⟨y, hyUf⟩, hyS, ?_⟩⟩
        change F n y = F m z
        rw [hFdef n y, hFdef m z, hw]
      · rintro ⟨hzfin, u, huS, hu⟩
        refine ⟨(u : ℂ), huS, ?_⟩
        have h1 : ((F m z : ℂ) : ℂ̂) = r.toSphereMap^[m] ((z : ℂ̂)) := hcoeF m z hzfin
        have h2 : ((F n (u : ℂ) : ℂ) : ℂ̂) = r.toSphereMap^[n] (((u : ℂ) : ℂ̂)) :=
          hcoeF n (u : ℂ) (hfinU (u : ℂ) u.2 n)
        rw [← h1, ← h2]
        exact congrArg (fun w : ℂ => ((w : ℂ̂))) hu.symm
    rw [hAeq]
    exact hVopen.measurableSet.inter ((hFmeas m) himg)
  -- indexed pieces and the value functions
  set AP : ℕ → Set ℂ := fun k => A (Nat.unpair k).1 (Nat.unpair k).2 with hAPdef
  have hAPmeas : ∀ k : ℕ, MeasurableSet (AP k) := fun k => hAmeas _ _
  have hexiff : ∀ z : ℂ, (∃ p : ℕ × ℕ × ℂ, p.2.2 ∈ S ∧
      r.toSphereMap^[p.1] ((z : ℂ̂)) = r.toSphereMap^[p.2.1] ((p.2.2 : ℂ̂)))
      ↔ ∃ k : ℕ, z ∈ AP k := by
    intro z
    constructor
    · rintro ⟨⟨m, n, y⟩, hyS, hw⟩
      refine ⟨Nat.pair m n, ?_⟩
      change z ∈ A (Nat.unpair (Nat.pair m n)).1 (Nat.unpair (Nat.pair m n)).2
      simp only [Nat.unpair_pair]
      exact ⟨y, hyS, hw⟩
    · rintro ⟨k, y, hyS, hw⟩
      exact ⟨((Nat.unpair k).1, (Nat.unpair k).2, y), hyS, hw⟩
  set VF : ℕ → ℂ → ℂ := fun k z =>
    (starRingEnd ℂ) (iterDeriv r (Nat.unpair k).1 z) / iterDeriv r (Nat.unpair k).1 z
      * HH (Nat.unpair k).2 (F (Nat.unpair k).1 z) with hVFdef
  have hVFmeas : ∀ k : ℕ, Measurable (VF k) := fun k =>
    ((hconj_meas.comp (hiter_meas _)).div (hiter_meas _)).mul
      ((hHm _).comp (hFmeas _))
  -- on each piece the value function computes the spread
  have hpiece : ∀ k : ℕ, ∀ z ∈ AP k, spreadCoeff r S σ z = VF k z := by
    intro k z hz
    obtain ⟨y, hyS, hw⟩ := hz
    have hyUf : y ∈ Uf := hSUf hyS
    have h1 : spreadCoeff r S σ z
        = spreadTwist r (Nat.unpair k).1 (Nat.unpair k).2 z y * σ y :=
      hval z y (Nat.unpair k).1 (Nat.unpair k).2 hyS hw
    have hFeqz : F (Nat.unpair k).1 z = Uf.domRestrict (F (Nat.unpair k).2) ⟨y, hyUf⟩ := by
      change F (Nat.unpair k).1 z = F (Nat.unpair k).2 y
      rw [hFdef _ z, hFdef _ y, hw]
    have h2 := hHs (Nat.unpair k).2 ⟨y, hyUf⟩
    rw [h1]
    simp only [hVFdef]
    rw [hFeqz, h2]
    unfold spreadTwist
    ring
  -- assemble by countable priority selection
  set Q : ℕ → ℂ → Prop := fun k z => z ∈ AP k ∨ ∀ j : ℕ, z ∉ AP j with hQdef
  have hQmeas : ∀ k : ℕ, MeasurableSet {z : ℂ | Q k z} := by
    intro k
    have h1 : {z : ℂ | Q k z} = AP k ∪ (⋃ j : ℕ, AP j)ᶜ := by
      ext z
      simp only [hQdef, Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff,
        Set.mem_iUnion, not_exists]
    rw [h1]
    exact (hAPmeas k).union (MeasurableSet.iUnion hAPmeas).compl
  have hQtot : ∀ z : ℂ, ∃ k : ℕ, Q k z := by
    intro z
    by_cases h : ∃ j : ℕ, z ∈ AP j
    · obtain ⟨j, hj⟩ := h
      exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr fun j hj => h ⟨j, hj⟩⟩
  set G : ℕ → ℂ → ℂ := fun k z => if z ∈ AP k then VF k z else 0 with hGdef
  have hGmeas : ∀ k : ℕ, Measurable (G k) := by
    intro k
    exact Measurable.ite (by simpa using hAPmeas k) (hVFmeas k) measurable_const
  have hfind : Measurable fun z : ℂ => G (Nat.find (hQtot z)) z :=
    Measurable.find hGmeas hQmeas hQtot
  have hEq : spreadCoeff r S σ = fun z : ℂ => G (Nat.find (hQtot z)) z := by
    funext z
    by_cases hex : ∃ p : ℕ × ℕ × ℂ, p.2.2 ∈ S ∧
        r.toSphereMap^[p.1] ((z : ℂ̂)) = r.toSphereMap^[p.2.1] ((p.2.2 : ℂ̂))
    · have hk : ∃ k : ℕ, z ∈ AP k := (hexiff z).mp hex
      have hspec := Nat.find_spec (hQtot z)
      have hzk : z ∈ AP (Nat.find (hQtot z)) := by
        rcases hspec with h | h
        · exact h
        · obtain ⟨k, hk'⟩ := hk
          exact absurd hk' (h k)
      simp only [hGdef]
      rw [if_pos hzk]
      exact hpiece _ z hzk
    · have hno : ∀ j : ℕ, z ∉ AP j := by
        intro j hj
        exact hex ((hexiff z).mpr ⟨j, hj⟩)
      have h0 : spreadCoeff r S σ z = 0 := by
        unfold spreadCoeff
        rw [dif_neg hex]
      rw [h0]
      simp only [hGdef]
      rw [if_neg (hno _)]
  rw [hEq]
  exact hfind.aemeasurable

/-- **The spread does not increase the essential sup.** The twist is
unimodular off a null set (and Lean-junk `0` on it), and the seed value is
sampled through grand-orbit correspondences built from holomorphic maps,
which pull null sets back to null sets; hence
`‖spreadCoeff r S σ‖∞ ≤ ‖σ‖∞`. -/
theorem spreadCoeff_eLpNormEssSup_le {r : RationalData} (hd : 1 ≤ r.degree)
    {U : Set ℂ̂} {S : Set ℂ} {σ : ℂ → ℂ}
    (hU : IsFatouComponent r.toSphereMap U)
    (_hW : IsWandering r.toSphereMap U)
    (_hinj : ∀ n : ℕ, Set.InjOn (r.toSphereMap^[n]) U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit r.toSphereMap U n)
    (_hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ U) → ∀ n : ℕ, iterDeriv r n z ≠ 0)
    (hS : ∀ z ∈ S, ((z : ℂ̂) ∈ U)) (_hSm : MeasurableSet S)
    (_hσ : ∀ z : ℂ, z ∉ S → σ z = 0) (_hσm : Measurable σ) :
    eLpNormEssSup (spreadCoeff r S σ) volume
      ≤ eLpNormEssSup σ volume := by
  classical
  -- complex differentiability implies real differentiability (built directly, to
  -- avoid the `restrictScalars` type-class search)
  have hCtoR : ∀ (f : ℂ → ℂ) (x : ℂ), DifferentiableAt ℂ f x → DifferentiableAt ℝ f x := by
    intro f x hf
    have h1 : HasFDerivAt f ((deriv f x) • (ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ)) x := by
      rw [hasFDerivAt_iff_isLittleO]
      refine hf.hasDerivAt.isLittleO.congr_left fun y => ?_
      simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      ring
    exact h1.differentiableAt
  -- the map is rational of degree ≥ 1, hence open
  have hfr : IsRational r.toSphereMap := ⟨r, rfl⟩
  have hdeg : 1 ≤ degreeOfRational r.toSphereMap := by
    rw [degreeOfRational_eq_of_witness r.toSphereMap r rfl]; exact hd
  have hfo : IsOpenMap r.toSphereMap := hfr.isOpenMap (hfr.ne_const hdeg)
  -- forward orbit membership in the orbit components
  have hmem : ∀ (w : ℂ̂), w ∈ U → ∀ k : ℕ,
      r.toSphereMap^[k] w ∈ fcOrbit r.toSphereMap U k := by
    intro w hw k
    have hfwd : ∀ j : ℕ, r.toSphereMap^[j] w ∈ FatouSet r.toSphereMap := by
      intro j
      induction j with
      | zero => simpa using hU.subset_fatouSet hw
      | succ j ih =>
          rw [Function.iterate_succ_apply']
          exact apply_mem_fatouSet hfo ih
    exact Set.mem_biUnion hw (mem_connectedComponentIn (hfwd k))
  -- orbits of `U` avoid `∞`
  have hfinU : ∀ (y : ℂ), ((y : ℂ̂)) ∈ U → ∀ k : ℕ,
      r.toSphereMap^[k] ((y : ℂ̂)) ≠ ∞ :=
    fun y hy k h => hinf k (h ▸ hmem ((y : ℂ̂)) hy k)
  -- rational data for the iterates and the polynomial form of the readings
  have hRex : ∀ n : ℕ, ∃ s : RationalData, r.toSphereMap^[n] = s.toSphereMap :=
    fun n => hfr.iterate hdeg n
  choose R hR using hRex
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → ℂ → ℂ, ∀ (n : ℕ) (z : ℂ),
      F n z = chartFiniteMap (r.toSphereMap^[n] ((z : ℂ̂))) :=
    ⟨fun n z => chartFiniteMap (r.toSphereMap^[n] ((z : ℂ̂))), fun _ _ => rfl⟩
  have hFrat : ∀ (n : ℕ) (z : ℂ),
      F n z = ((R n).numReduced.eval z) / ((R n).denReduced.eval z) := by
    intro n z
    rw [hFdef n z, hR n]
    have hread : (R n).toSphereMap ((z : ℂ̂))
        = if (R n).denReduced.eval z = 0 then (∞ : ℂ̂)
          else ((((R n).numReduced.eval z) / ((R n).denReduced.eval z) : ℂ) : ℂ̂) := rfl
    rw [hread]
    by_cases h : (R n).denReduced.eval z = 0
    · rw [if_pos h, h, div_zero]
      rfl
    · rw [if_neg h]
      rfl
  have hpole : ∀ (n : ℕ) (z : ℂ),
      r.toSphereMap^[n] ((z : ℂ̂)) = ∞ ↔ (R n).denReduced.eval z = 0 := by
    intro n z
    rw [hR n]
    have hread : (R n).toSphereMap ((z : ℂ̂))
        = if (R n).denReduced.eval z = 0 then (∞ : ℂ̂)
          else ((((R n).numReduced.eval z) / ((R n).denReduced.eval z) : ℂ) : ℂ̂) := rfl
    rw [hread]
    by_cases h : (R n).denReduced.eval z = 0
    · simp [h]
    · simp [h, OnePoint.coe_ne_infty]
  have hcoeF : ∀ (n : ℕ) (z : ℂ), r.toSphereMap^[n] ((z : ℂ̂)) ≠ ∞ →
      ((F n z : ℂ) : ℂ̂) = r.toSphereMap^[n] ((z : ℂ̂)) := by
    intro n z hz
    obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hz
    rw [hFdef n z, ← hw]
    rfl
  -- the iterates have degree at least one, so their Wronskians are nonzero
  have hdegR : ∀ m : ℕ, 1 ≤ (R m).degree := by
    intro m
    have h1 : degreeOfRational (r.toSphereMap^[m]) = (R m).degree :=
      degreeOfRational_eq_of_witness _ _ (hR m)
    have h2 : degreeOfRational (r.toSphereMap^[m])
        = degreeOfRational r.toSphereMap ^ m := degreeOfRational_iterate hfr hdeg m
    rw [← h1, h2]
    exact Nat.one_le_pow _ _ hdeg
  have hwron : ∀ m : ℕ, (R m).wronskian ≠ 0 := by
    intro m h0
    have hcop : IsCoprime (R m).numReduced (R m).denReduced :=
      isCoprime_div_gcd_div_gcd (R m).den_ne_zero
    have hdenR_ne_zero : (R m).denReduced ≠ 0 := by
      unfold RationalData.denReduced
      intro hz
      have h1 : (R m).den
          = gcd (R m).num (R m).den * ((R m).den / gcd (R m).num (R m).den) :=
        (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right (R m).den_ne_zero)
          (gcd_dvd_right _ _)).symm
      rw [hz, mul_zero] at h1
      exact (R m).den_ne_zero h1
    have hid : Polynomial.derivative (R m).numReduced * (R m).denReduced
        = (R m).numReduced * Polynomial.derivative (R m).denReduced := by
      have h0' : Polynomial.derivative (R m).numReduced * (R m).denReduced
          - (R m).numReduced * Polynomial.derivative (R m).denReduced = 0 := h0
      exact sub_eq_zero.mp h0'
    have hdvd : (R m).denReduced
        ∣ (R m).numReduced * Polynomial.derivative (R m).denReduced := by
      rw [← hid]
      exact dvd_mul_left _ _
    have hdvd' : (R m).denReduced ∣ Polynomial.derivative (R m).denReduced :=
      hcop.symm.dvd_of_dvd_mul_left hdvd
    have hderD : Polynomial.derivative (R m).denReduced = 0 := by
      by_cases hd0 : (R m).denReduced.natDegree = 0
      · obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hd0
        rw [← hc, Polynomial.derivative_C]
      · exact Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd'
          (Polynomial.natDegree_derivative_lt hd0)
    have hdD : (R m).denReduced.natDegree = 0 :=
      Polynomial.derivative_eq_zero.mp hderD
    have hderN : Polynomial.derivative (R m).numReduced = 0 := by
      have h2 : Polynomial.derivative (R m).numReduced * (R m).denReduced = 0 := by
        rw [hid, hderD, mul_zero]
      exact (mul_eq_zero.mp h2).resolve_right hdenR_ne_zero
    have hdN : (R m).numReduced.natDegree = 0 :=
      Polynomial.derivative_eq_zero.mp hderN
    have hmax : (R m).degree
        = max (R m).numReduced.natDegree (R m).denReduced.natDegree := rfl
    have hge := hdegR m
    omega
  -- the essentially-large seed set is null
  set N : Set ℂ := {w : ℂ | ¬ ‖σ w‖ₑ ≤ eLpNormEssSup σ volume} with hNdef
  have hNnull : volume N = 0 := ae_iff.mp (enorm_ae_le_eLpNormEssSup σ volume)
  have hSNnull : volume (S ∩ N) = 0 := measure_mono_null Set.inter_subset_right hNnull
  -- the transported bad sets are null
  have hBadNull : ∀ m n : ℕ, volume {z : ℂ |
      r.toSphereMap^[m] ((z : ℂ̂)) ≠ ∞ ∧ F m z ∈ F n '' (S ∩ N)} = 0 := by
    intro m n
    -- the image of the bad seed set under the `n`-th reading is null
    have hTnull : volume (F n '' (S ∩ N)) = 0 := by
      have hFn_eq : F n = fun w : ℂ =>
          ((R n).numReduced.eval w) / ((R n).denReduced.eval w) := funext (hFrat n)
      have hdiff : DifferentiableOn ℝ (F n) (S ∩ N) := by
        intro y hy
        have hyU : ((y : ℂ̂)) ∈ U := hS y hy.1
        have hden : (R n).denReduced.eval y ≠ 0 := fun h0 =>
          hfinU y hyU n ((hpole n y).mpr h0)
        have hdC : DifferentiableAt ℂ (F n) y := by
          rw [hFn_eq]
          exact ((R n).numReduced.differentiableAt).div
            ((R n).denReduced.differentiableAt) hden
        exact (hCtoR (F n) y hdC).differentiableWithinAt
      exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        hdiff hSNnull
    -- split off the (finitely many) critical points of the `m`-th reading
    have hcritfin : ({z : ℂ | (R m).wronskian.IsRoot z} : Set ℂ).Finite :=
      Polynomial.finite_setOfPred_isRoot (hwron m)
    have hsplit : {z : ℂ | r.toSphereMap^[m] ((z : ℂ̂)) ≠ ∞ ∧ F m z ∈ F n '' (S ∩ N)}
        ⊆ {z : ℂ | (R m).wronskian.IsRoot z}
          ∪ {z : ℂ | ((R m).denReduced.eval z ≠ 0 ∧ (R m).wronskian.eval z ≠ 0)
              ∧ F m z ∈ F n '' (S ∩ N)} := by
      rintro z ⟨hzfin, hzmem⟩
      by_cases hwz : (R m).wronskian.eval z = 0
      · exact Or.inl hwz
      · exact Or.inr ⟨⟨fun h0 => hzfin ((hpole m z).mpr h0), hwz⟩, hzmem⟩
    refine measure_mono_null hsplit
      (measure_union_null (hcritfin.measure_zero volume) ?_)
    -- the non-critical part is locally null via holomorphic inverse branches
    refine measure_null_of_locally_null _ ?_
    rintro z0 ⟨⟨hden0, hwr0⟩, hmem0⟩
    -- the reading has nonvanishing derivative at `z0`
    have hderiv0 : deriv (F m) z0
        = (R m).wronskian.eval z0 / ((R m).denReduced.eval z0) ^ 2 := by
      have h2 : F m = fun x : ℂ => chartFiniteMap ((R m).toSphereMap ((x : ℂ̂))) := by
        funext x
        rw [hFdef m x, hR m]
      rw [h2]
      exact (R m).deriv_reading hden0
    have hd0 : deriv (F m) z0 ≠ 0 := by
      rw [hderiv0]
      exact div_ne_zero hwr0 (pow_ne_zero 2 hden0)
    -- analytic near `z0`, hence a strict derivative and a local left inverse
    have hOopen : IsOpen {w : ℂ | (R m).denReduced.eval w ≠ 0} := by
      have h1 : {w : ℂ | (R m).denReduced.eval w ≠ 0}
          = (fun w : ℂ => (R m).denReduced.eval w) ⁻¹' ({(0 : ℂ)}ᶜ) := rfl
      rw [h1]
      exact isOpen_compl_singleton.preimage (R m).denReduced.continuous
    have hFm_eq : F m = fun w : ℂ =>
        ((R m).numReduced.eval w) / ((R m).denReduced.eval w) := funext (hFrat m)
    have hFmdiff : DifferentiableOn ℂ (F m) {w : ℂ | (R m).denReduced.eval w ≠ 0} := by
      rw [hFm_eq]
      intro w hw
      exact (((R m).numReduced.differentiableAt).div
        ((R m).denReduced.differentiableAt) hw).differentiableWithinAt
    have han : AnalyticOnNhd ℂ (F m) {w : ℂ | (R m).denReduced.eval w ≠ 0} :=
      hFmdiff.analyticOnNhd hOopen
    have hstrict : HasStrictDerivAt (F m) (deriv (F m) z0) z0 :=
      (han z0 hden0).hasStrictDerivAt
    have hlinv := hstrict.eventually_left_inverse hd0
    obtain ⟨W1, hW1, hW1open, hz0W1⟩ := _root_.eventually_nhds_iff.mp hlinv
    -- a holomorphic branch of `f^[m]` through `z0`
    have hz0fin : r.toSphereMap^[m] ((z0 : ℂ̂)) ≠ ∞ := fun h => hden0 ((hpole m z0).mp h)
    have hcrit' : deriv (fun x : ℂ =>
        chartFiniteMap (r.toSphereMap^[m] ((x : ℂ̂)))) z0 ≠ 0 := by
      have h2 : (fun x : ℂ => chartFiniteMap (r.toSphereMap^[m] ((x : ℂ̂)))) = F m :=
        funext fun x => (hFdef m x).symm
      rw [h2]
      exact hd0
    obtain ⟨V, g, hVopen, haV, hga, hgdiff, hgsec⟩ :=
      exists_branch_of_deriv_ne_zero (hfr.iterate hdeg m) (hcoeF m z0 hz0fin).symm hcrit'
    -- near `z0` the branch inverts the reading
    have hFmc : ContinuousAt (F m) z0 := (han z0 hden0).continuousAt
    have hgc : ContinuousAt g (F m z0) :=
      (hgdiff.differentiableAt (hVopen.mem_nhds haV)).continuousAt
    have hz0W1' : g (F m z0) ∈ W1 := by rw [hga]; exact hz0W1
    have hev1 : ∀ᶠ x in 𝓝 z0, x ∈ W1 := hW1open.mem_nhds hz0W1
    have hev2 : ∀ᶠ x in 𝓝 z0, F m x ∈ V := hFmc.eventually_mem (hVopen.mem_nhds haV)
    have hev3 : ∀ᶠ x in 𝓝 z0, g (F m x) ∈ W1 :=
      (hgc.comp hFmc).eventually_mem (hW1open.mem_nhds hz0W1')
    have hkey : ∀ᶠ x in 𝓝 z0, F m x ∈ V ∧ g (F m x) = x := by
      filter_upwards [hev1, hev2, hev3] with x hx1 hx2 hx3
      refine ⟨hx2, ?_⟩
      have hsec := hgsec (F m x) hx2
      have hread : F m (g (F m x)) = F m x := by
        rw [hFdef m (g (F m x)), hsec]
        rfl
      have h1 := hW1 x hx1
      have h2 := hW1 _ hx3
      rw [hread] at h2
      rw [← h2]
      exact h1
    obtain ⟨W2, hW2, hW2open, hz0W2⟩ := _root_.eventually_nhds_iff.mp hkey
    refine ⟨W2 ∩ _, mem_nhdsWithin.mpr ⟨W2, hW2open, hz0W2, fun x hx => hx⟩, ?_⟩
    -- the intersection is carried into the branch image of a null set
    have himg : volume (g '' (V ∩ F n '' (S ∩ N))) = 0 := by
      have hgd : DifferentiableOn ℝ g (V ∩ F n '' (S ∩ N)) := by
        intro w hw
        exact (hCtoR g w ((hgdiff w hw.1).differentiableAt
          (hVopen.mem_nhds hw.1))).differentiableWithinAt
      exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hgd
        (measure_mono_null Set.inter_subset_right hTnull)
    refine measure_mono_null ?_ himg
    rintro x ⟨hxW2, _, hxmem⟩
    obtain ⟨hFV, hgF⟩ := hW2 x hxW2
    exact ⟨F m x, ⟨hFV, hxmem⟩, hgF⟩
  -- almost every point avoids all transported bad sets
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ ⋃ m : ℕ, ⋃ n : ℕ, {z : ℂ |
      r.toSphereMap^[m] ((z : ℂ̂)) ≠ ∞ ∧ F m z ∈ F n '' (S ∩ N)} :=
    measure_eq_zero_iff_ae_notMem.mp
      (measure_iUnion_null fun m => measure_iUnion_null fun n => hBadNull m n)
  -- conclude via the a.e. enorm bound
  refine eLpNormEssSup_le_of_ae_enorm_bound ?_
  filter_upwards [hae] with z hz
  by_cases hex : ∃ p : ℕ × ℕ × ℂ, p.2.2 ∈ S ∧
      r.toSphereMap^[p.1] ((z : ℂ̂)) = r.toSphereMap^[p.2.1] ((p.2.2 : ℂ̂))
  · unfold spreadCoeff
    rw [dif_pos hex]
    obtain ⟨hyS, hw⟩ := Classical.choose_spec hex
    have hyU : (((Classical.choose hex).2.2 : ℂ̂)) ∈ U := hS _ hyS
    have hfin : r.toSphereMap^[(Classical.choose hex).2.1]
        (((Classical.choose hex).2.2 : ℂ̂)) ≠ ∞ := hfinU _ hyU _
    -- the chosen seed value obeys the essential bound off the bad sets
    have hyN : ‖σ (Classical.choose hex).2.2‖ₑ ≤ eLpNormEssSup σ volume := by
      by_contra hcon
      apply hz
      refine Set.mem_iUnion.mpr ⟨(Classical.choose hex).1, Set.mem_iUnion.mpr
        ⟨(Classical.choose hex).2.1, ?_, ?_⟩⟩
      · rw [hw]; exact hfin
      · exact ⟨(Classical.choose hex).2.2, ⟨hyS, hcon⟩, by
          rw [hFdef (Classical.choose hex).2.1 (Classical.choose hex).2.2,
            hFdef (Classical.choose hex).1 z, hw]⟩
    -- the twist is unimodular or junk-zero, hence of norm at most one
    have htw : ‖spreadTwist r (Classical.choose hex).1 (Classical.choose hex).2.1 z
        (Classical.choose hex).2.2‖ ≤ 1 := by
      unfold spreadTwist
      rw [norm_mul, norm_div, norm_div, RCLike.norm_conj, RCLike.norm_conj]
      have h1 : ‖iterDeriv r (Classical.choose hex).2.1 (Classical.choose hex).2.2‖
          / ‖iterDeriv r (Classical.choose hex).2.1 (Classical.choose hex).2.2‖
          ≤ 1 := div_self_le_one _
      have h2 : ‖iterDeriv r (Classical.choose hex).1 z‖
          / ‖iterDeriv r (Classical.choose hex).1 z‖ ≤ 1 := div_self_le_one _
      have h3 : (0 : ℝ) ≤ ‖iterDeriv r (Classical.choose hex).1 z‖
          / ‖iterDeriv r (Classical.choose hex).1 z‖ :=
        div_nonneg (norm_nonneg _) (norm_nonneg _)
      calc ‖iterDeriv r (Classical.choose hex).2.1 (Classical.choose hex).2.2‖
            / ‖iterDeriv r (Classical.choose hex).2.1 (Classical.choose hex).2.2‖
            * (‖iterDeriv r (Classical.choose hex).1 z‖
              / ‖iterDeriv r (Classical.choose hex).1 z‖)
          ≤ 1 * (‖iterDeriv r (Classical.choose hex).1 z‖
              / ‖iterDeriv r (Classical.choose hex).1 z‖) :=
            mul_le_mul_of_nonneg_right h1 h3
        _ ≤ 1 := by rw [one_mul]; exact h2
    calc ‖spreadTwist r (Classical.choose hex).1 (Classical.choose hex).2.1 z
          (Classical.choose hex).2.2 * σ (Classical.choose hex).2.2‖ₑ
        = ‖spreadTwist r (Classical.choose hex).1 (Classical.choose hex).2.1 z
          (Classical.choose hex).2.2‖ₑ * ‖σ (Classical.choose hex).2.2‖ₑ :=
          enorm_mul _ _
      _ ≤ 1 * ‖σ (Classical.choose hex).2.2‖ₑ := by
          refine mul_le_mul' ?_ le_rfl
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_one.mpr htw
      _ = ‖σ (Classical.choose hex).2.2‖ₑ := one_mul _
      _ ≤ eLpNormEssSup σ volume := hyN
  · unfold spreadCoeff
    rw [dif_neg hex]
    simp

/-- **Invariance of the spread.** The spread satisfies the pullback law
`μ(z)·f′(z) = μ(f z)·conj(f′(z))` almost everywhere: the saturation is fully
invariant with witnesses shifting by one time step, the transported values
agree by witness independence (wandering, injectivity, and the twist
cocycle `iterDeriv_add`), the complement carries `0` on both sides, and the
finitely many poles together with the orbit segments through critical points
or `∞` form a null set. This is the hypothesis `Dynamics/Deformation/DeltaOperator/` consumes
to kill the weak `∂̄` of the deformation field. -/
theorem isInvariantBeltrami_spreadCoeff {r : RationalData} (hd : 1 ≤ r.degree)
    {U : Set ℂ̂} {S : Set ℂ} {σ : ℂ → ℂ}
    (hU : IsFatouComponent r.toSphereMap U)
    (hW : IsWandering r.toSphereMap U)
    (hinj : ∀ n : ℕ, Set.InjOn (r.toSphereMap^[n]) U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit r.toSphereMap U n)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ U) → ∀ n : ℕ, iterDeriv r n z ≠ 0)
    (hS : ∀ z ∈ S, ((z : ℂ̂) ∈ U)) (_hSm : MeasurableSet S)
    (_hσ : ∀ z : ℂ, z ∉ S → σ z = 0) (_hσm : Measurable σ) :
    IsInvariantBeltrami r (spreadCoeff r S σ) := by
  -- the map is rational of degree ≥ 1, hence open
  have hfr : IsRational r.toSphereMap := ⟨r, rfl⟩
  have hdeg : 1 ≤ degreeOfRational r.toSphereMap := by
    rw [degreeOfRational_eq_of_witness r.toSphereMap r rfl]; exact hd
  have hfo : IsOpenMap r.toSphereMap := hfr.isOpenMap (hfr.ne_const hdeg)
  -- conjugation preserves nonvanishing
  have hconj_ne : ∀ x : ℂ, x ≠ 0 → (starRingEnd ℂ) x ≠ 0 := by
    intro x hx h0
    apply hx
    have h1 := congrArg (starRingEnd ℂ) h0
    simpa using h1
  -- forward orbit membership in the orbit components
  have hmem : ∀ (w : ℂ̂), w ∈ U → ∀ k : ℕ,
      r.toSphereMap^[k] w ∈ fcOrbit r.toSphereMap U k := by
    intro w hw k
    have hfwd : ∀ j : ℕ, r.toSphereMap^[j] w ∈ FatouSet r.toSphereMap := by
      intro j
      induction j with
      | zero => simpa using hU.subset_fatouSet hw
      | succ j ih =>
          rw [Function.iterate_succ_apply']
          exact apply_mem_fatouSet hfo ih
    exact Set.mem_biUnion hw (mem_connectedComponentIn (hfwd k))
  -- orbits of `U` avoid `∞`
  have hfinU : ∀ (y : ℂ), ((y : ℂ̂)) ∈ U → ∀ k : ℕ,
      r.toSphereMap^[k] ((y : ℂ̂)) ≠ ∞ :=
    fun y hy k h => hinf k (h ▸ hmem ((y : ℂ̂)) hy k)
  -- witness independence: two witnesses over `U` force equal offsets and points
  have core : ∀ (x y y2 : ℂ) (m n m2 n2 : ℕ), ((y : ℂ̂)) ∈ U → ((y2 : ℂ̂)) ∈ U →
      r.toSphereMap^[m] ((x : ℂ̂)) = r.toSphereMap^[n] ((y : ℂ̂)) →
      r.toSphereMap^[m2] ((x : ℂ̂)) = r.toSphereMap^[n2] ((y2 : ℂ̂)) →
      n + m2 = n2 + m ∧ y = y2 := by
    intro x y y2 m n m2 n2 hyU hy2U hw1 hw2
    have e1 : r.toSphereMap^[n + m2] ((y : ℂ̂)) = r.toSphereMap^[n2 + m] ((y2 : ℂ̂)) := by
      calc r.toSphereMap^[n + m2] ((y : ℂ̂))
          = r.toSphereMap^[m2 + n] ((y : ℂ̂)) := by rw [Nat.add_comm n m2]
        _ = r.toSphereMap^[m2] (r.toSphereMap^[n] ((y : ℂ̂))) :=
            Function.iterate_add_apply _ m2 n _
        _ = r.toSphereMap^[m2] (r.toSphereMap^[m] ((x : ℂ̂))) := by rw [hw1]
        _ = r.toSphereMap^[m2 + m] ((x : ℂ̂)) := (Function.iterate_add_apply _ m2 m _).symm
        _ = r.toSphereMap^[m + m2] ((x : ℂ̂)) := by rw [Nat.add_comm m2 m]
        _ = r.toSphereMap^[m] (r.toSphereMap^[m2] ((x : ℂ̂))) :=
            Function.iterate_add_apply _ m m2 _
        _ = r.toSphereMap^[m] (r.toSphereMap^[n2] ((y2 : ℂ̂))) := by rw [hw2]
        _ = r.toSphereMap^[m + n2] ((y2 : ℂ̂)) := (Function.iterate_add_apply _ m n2 _).symm
        _ = r.toSphereMap^[n2 + m] ((y2 : ℂ̂)) := by rw [Nat.add_comm m n2]
    have htime : n + m2 = n2 + m := by
      by_contra hne
      have hdisj : Disjoint (fcOrbit r.toSphereMap U (n + m2))
          (fcOrbit r.toSphereMap U (n2 + m)) := hW hne
      have h1 : r.toSphereMap^[n + m2] ((y : ℂ̂)) ∈ fcOrbit r.toSphereMap U (n + m2) :=
        hmem ((y : ℂ̂)) hyU (n + m2)
      have h2 : r.toSphereMap^[n + m2] ((y : ℂ̂)) ∈ fcOrbit r.toSphereMap U (n2 + m) := by
        rw [e1]; exact hmem ((y2 : ℂ̂)) hy2U (n2 + m)
      exact Set.disjoint_left.mp hdisj h1 h2
    have hyy : ((y : ℂ̂)) = ((y2 : ℂ̂)) := by
      apply hinj (n + m2) hyU hy2U
      calc r.toSphereMap^[n + m2] ((y : ℂ̂))
          = r.toSphereMap^[n2 + m] ((y2 : ℂ̂)) := e1
        _ = r.toSphereMap^[n + m2] ((y2 : ℂ̂)) := by rw [htime]
    exact ⟨htime, OnePoint.coe_eq_coe.mp hyy⟩
  -- degree-0 and degree-1 values of the iterate derivative
  have hD0 : ∀ w : ℂ, iterDeriv r 0 w = 1 := fun w => by simp [iterDeriv]
  have hD1 : ∀ w : ℂ, iterDeriv r 1 w = fderivRational r w := by
    intro w
    simp only [iterDeriv, Finset.prod_range_one, Function.iterate_zero_apply]
    rfl
  -- the twist does not depend on the witness offsets, given the time relation
  have tweq : ∀ (x y : ℂ) (m n m2 n2 : ℕ), ((y : ℂ̂)) ∈ U →
      r.toSphereMap^[m] ((x : ℂ̂)) = r.toSphereMap^[n] ((y : ℂ̂)) →
      r.toSphereMap^[m2] ((x : ℂ̂)) = r.toSphereMap^[n2] ((y : ℂ̂)) →
      n + m2 = n2 + m →
      spreadTwist r m n x y = spreadTwist r m2 n2 x y := by
    intro x y m n m2 n2 hyU hw1 hw2 htime
    have hfy : ∀ k : ℕ, r.toSphereMap^[k] ((y : ℂ̂)) ≠ ∞ := hfinU y hyU
    have hxm : r.toSphereMap^[m] ((x : ℂ̂)) ≠ ∞ := by rw [hw1]; exact hfy n
    have hxm2 : r.toSphereMap^[m2] ((x : ℂ̂)) ≠ ∞ := by rw [hw2]; exact hfy n2
    -- cocycle splittings at `x` and at `y`, matched through the witness relations
    have hc1 := iterDeriv_add r m m2 x hxm
    have hc2 := iterDeriv_add r m2 m x hxm2
    have hc3 := iterDeriv_add r n m2 y (hfy n)
    have hc4 := iterDeriv_add r n2 m y (hfy n2)
    rw [← hw1] at hc3
    rw [← hw2] at hc4
    have hane : iterDeriv r n y ≠ 0 := hcrit y hyU n
    have hbne : iterDeriv r n2 y ≠ 0 := hcrit y hyU n2
    have hNne : iterDeriv r (n + m2) y ≠ 0 := hcrit y hyU (n + m2)
    unfold spreadTwist
    set a := iterDeriv r n y with ha
    set b := iterDeriv r n2 y with hb
    set c := iterDeriv r m x with hc
    set d := iterDeriv r m2 x with hdd
    set p := iterDeriv r m2 (chartFiniteMap (r.toSphereMap^[m] ((x : ℂ̂)))) with hp
    set q := iterDeriv r m (chartFiniteMap (r.toSphereMap^[m2] ((x : ℂ̂)))) with hq
    -- hc3 : iterDeriv r (n + m2) y = a * p ; hc4 : iterDeriv r (n2 + m) y = b * q
    have hapbq : a * p = b * q := by rw [← hc3, ← hc4, htime]
    have hcpdq : c * p = d * q := by rw [← hc1, ← hc2, Nat.add_comm m m2]
    have hapne : a * p ≠ 0 := by rw [← hc3]; exact hNne
    have hpne : p ≠ 0 := fun h => hapne (by rw [h, mul_zero])
    have hqne : q ≠ 0 := fun h => hapne (by rw [hapbq, h, mul_zero])
    by_cases hcz : c = 0
    · -- both twists vanish through the Lean junk value `0/0 = 0`
      have hdz : d = 0 := by
        have h0 : d * q = 0 := by rw [← hcpdq, hcz, zero_mul]
        exact (mul_eq_zero.mp h0).resolve_right hqne
      rw [hcz, hdz]
      simp
    · have hdz : d ≠ 0 := by
        intro h0
        apply mul_ne_zero hcz hpne
        rw [hcpdq, h0, zero_mul]
      have had : a * d = b * c := by
        have h1 : a * d * (p * q) = b * c * (p * q) := by
          calc a * d * (p * q) = (a * p) * (d * q) := by ring
            _ = (b * q) * (c * p) := by rw [hapbq, ← hcpdq]
            _ = b * c * (p * q) := by ring
        exact mul_right_cancel₀ (mul_ne_zero hpne hqne) h1
      have hadc : (starRingEnd ℂ) a * (starRingEnd ℂ) d
          = (starRingEnd ℂ) b * (starRingEnd ℂ) c := by
        have h2 := congrArg (starRingEnd ℂ) had
        simpa [map_mul] using h2
      rw [div_mul_div_comm, div_mul_div_comm,
        div_eq_div_iff (mul_ne_zero (hconj_ne a hane) hcz)
          (mul_ne_zero (hconj_ne b hbne) hdz)]
      linear_combination ((starRingEnd ℂ) b * (starRingEnd ℂ) c) * had - (b * c) * hadc
  -- the spread evaluates through ANY witness, not just the chosen one
  have hval : ∀ (x y : ℂ) (k l : ℕ), y ∈ S →
      r.toSphereMap^[k] ((x : ℂ̂)) = r.toSphereMap^[l] ((y : ℂ̂)) →
      spreadCoeff r S σ x = spreadTwist r k l x y * σ y := by
    intro x y k l hyS hw
    have hex : ∃ p : ℕ × ℕ × ℂ, p.2.2 ∈ S ∧
        r.toSphereMap^[p.1] ((x : ℂ̂)) = r.toSphereMap^[p.2.1] ((p.2.2 : ℂ̂)) :=
      ⟨(k, l, y), hyS, hw⟩
    unfold spreadCoeff
    rw [dif_pos hex]
    obtain ⟨hy'S, hw'⟩ := Classical.choose_spec hex
    obtain ⟨htime, hyy⟩ := core x (Classical.choose hex).2.2 y (Classical.choose hex).1
      (Classical.choose hex).2.1 k l (hS _ hy'S) (hS _ hyS) hw' hw
    rw [hyy] at hw' ⊢
    rw [tweq x y (Classical.choose hex).1 (Classical.choose hex).2.1 k l
      (hS _ hyS) hw' hw htime]
  -- almost every point avoids the finitely many poles
  have hdenne : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz0
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz0, mul_zero] at h1
    exact r.den_ne_zero h1
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), r.denReduced.eval z ≠ 0 := by
    rw [ae_iff]
    have hsub : {z : ℂ | ¬ r.denReduced.eval z ≠ 0} = {z : ℂ | r.denReduced.IsRoot z} := by
      ext w
      simp [Polynomial.IsRoot]
    rw [hsub]
    exact (Polynomial.finite_setOfPred_isRoot hdenne).measure_zero volume
  unfold IsInvariantBeltrami
  filter_upwards [hae] with z hz
  -- off the poles the image of `z` is finite and reads back faithfully
  have hread : r.toSphereMap ((z : ℂ̂))
      = if r.denReduced.eval z = 0 then (∞ : ℂ̂)
        else ((r.numReduced.eval z / r.denReduced.eval z : ℂ) : ℂ̂) := rfl
  have hfz : r.toSphereMap ((z : ℂ̂)) ≠ ∞ := by
    rw [hread, if_neg hz]
    exact OnePoint.coe_ne_infty _
  have hFz : ((chartFiniteMap (r.toSphereMap ((z : ℂ̂))) : ℂ̂)) = r.toSphereMap ((z : ℂ̂)) := by
    obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hfz
    rw [← hw]
    rfl
  by_cases hex : ∃ p : ℕ × ℕ × ℂ, p.2.2 ∈ S ∧
      r.toSphereMap^[p.1] ((z : ℂ̂)) = r.toSphereMap^[p.2.1] ((p.2.2 : ℂ̂))
  · -- on the saturation: shift the witness by one time step
    obtain ⟨⟨m, n, y⟩, hyS, hw⟩ := hex
    have hyU : ((y : ℂ̂)) ∈ U := hS y hyS
    have h1 : spreadCoeff r S σ z = spreadTwist r m n z y * σ y := hval z y m n hyS hw
    by_cases hm0 : m = 0
    · -- `z` is a forward image of the seed point: push the witness forward
      subst hm0
      have hw0 : ((z : ℂ̂)) = r.toSphereMap^[n] ((y : ℂ̂)) := by simpa using hw
      have hwF : r.toSphereMap^[0] ((chartFiniteMap (r.toSphereMap ((z : ℂ̂))) : ℂ̂))
          = r.toSphereMap^[n + 1] ((y : ℂ̂)) := by
        simp only [Function.iterate_zero_apply]
        rw [hFz, Function.iterate_succ_apply', ← hw0]
      have h2 : spreadCoeff r S σ (chartFiniteMap (r.toSphereMap ((z : ℂ̂))))
          = spreadTwist r 0 (n + 1) (chartFiniteMap (r.toSphereMap ((z : ℂ̂)))) y * σ y :=
        hval _ y 0 (n + 1) hyS hwF
      rw [h1, h2]
      -- cocycle at `y` through the finite point `z`
      have hfyn : r.toSphereMap^[n] ((y : ℂ̂)) ≠ ∞ := by
        rw [← hw0]; exact OnePoint.coe_ne_infty z
      have hcoc := iterDeriv_add r n 1 y hfyn
      rw [← hw0] at hcoc
      have hcfz : chartFiniteMap ((z : ℂ̂)) = z := rfl
      rw [hcfz, hD1 z] at hcoc
      have hane : iterDeriv r n y ≠ 0 := hcrit y hyU n
      have hfne : fderivRational r z ≠ 0 := by
        intro h0
        apply hcrit y hyU (n + 1)
        rw [hcoc, h0, mul_zero]
      have hanec := hconj_ne _ hane
      have hfnec := hconj_ne _ hfne
      unfold spreadTwist
      rw [hD0 z, hD0 (chartFiniteMap (r.toSphereMap ((z : ℂ̂)))), hcoc, map_one, map_mul]
      field_simp
    · -- `z` maps forward at least one step: pull the witness back
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k + 1 := ⟨m - 1, by omega⟩
      have hwF : r.toSphereMap^[k] ((chartFiniteMap (r.toSphereMap ((z : ℂ̂))) : ℂ̂))
          = r.toSphereMap^[n] ((y : ℂ̂)) := by
        rw [hFz, ← Function.iterate_succ_apply]
        exact hw
      have h2 : spreadCoeff r S σ (chartFiniteMap (r.toSphereMap ((z : ℂ̂))))
          = spreadTwist r k n (chartFiniteMap (r.toSphereMap ((z : ℂ̂)))) y * σ y :=
        hval _ y k n hyS hwF
      rw [h1, h2]
      -- cocycle at `z`: split off the first step
      have h1fin : r.toSphereMap^[1] ((z : ℂ̂)) ≠ ∞ := by
        rw [Function.iterate_one]; exact hfz
      have hcoc := iterDeriv_add r 1 k z h1fin
      rw [Function.iterate_one] at hcoc
      rw [hD1 z] at hcoc
      have hcoc' : iterDeriv r (k + 1) z
          = fderivRational r z
            * iterDeriv r k (chartFiniteMap (r.toSphereMap ((z : ℂ̂)))) := by
        rw [Nat.add_comm k 1]; exact hcoc
      have hane : iterDeriv r n y ≠ 0 := hcrit y hyU n
      have hanec := hconj_ne _ hane
      unfold spreadTwist
      rw [hcoc']
      by_cases hFne : fderivRational r z = 0
      · rw [hFne]
        simp
      · by_cases hene : iterDeriv r k (chartFiniteMap (r.toSphereMap ((z : ℂ̂)))) = 0
        · rw [hene]
          simp
        · have hFnec := hconj_ne _ hFne
          have henec := hconj_ne _ hene
          rw [map_mul]
          field_simp
  · -- off the saturation: the image is also off the saturation, both sides vanish
    have hex' : ¬ ∃ p : ℕ × ℕ × ℂ, p.2.2 ∈ S ∧
        r.toSphereMap^[p.1] ((chartFiniteMap (r.toSphereMap ((z : ℂ̂))) : ℂ̂))
          = r.toSphereMap^[p.2.1] ((p.2.2 : ℂ̂)) := by
      rintro ⟨⟨m2, n2, y2⟩, hy2S, hw2⟩
      apply hex
      refine ⟨(m2 + 1, n2, y2), hy2S, ?_⟩
      calc r.toSphereMap^[m2 + 1] ((z : ℂ̂))
          = r.toSphereMap^[m2] (r.toSphereMap ((z : ℂ̂))) :=
            Function.iterate_succ_apply _ _ _
        _ = r.toSphereMap^[m2] ((chartFiniteMap (r.toSphereMap ((z : ℂ̂))) : ℂ̂)) := by
            rw [hFz]
        _ = r.toSphereMap^[n2] ((y2 : ℂ̂)) := hw2
    unfold spreadCoeff
    rw [dif_neg hex, dif_neg hex']
    rw [zero_mul, zero_mul]

end NoWanderingDomains
