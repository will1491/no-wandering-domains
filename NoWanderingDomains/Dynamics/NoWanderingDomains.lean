/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.Sullivan.EventualInjectivity.Package
import NoWanderingDomains.Dynamics.Sullivan.Spreading
import NoWanderingDomains.Dynamics.Sullivan.SeedTriviality

/-!
# Sullivan's No Wandering Domains theorem

Every Fatou component of a rational map of degree at least two is eventually
periodic; equivalently, no component wanders. The proof is the infinitesimal
deformation argument:

1. *Normalization* (`exists_wandering_injective_package`): replace a
   wandering component by a later orbit component `U` on which every iterate
   is injective and whose orbit avoids `∞` and the critical points.
2. *Seeds and spreading*: fix a closed disk in the finite part of `U`
   (`IsFatouComponent.exists_closedBall_subset`); each seed combination
   `σ_c` (`seedCombo`, `K = 2d+2` seeds) spreads to an `f`-invariant
   coefficient `μ_c` on `ℂ` (`spreadCoeff`), agreeing with `σ_c` on `U` and
   with `‖μ_c‖∞ ≤ ‖σ_c‖∞`.
3. *Solve and project*: `v_c := dbarSolver μ_c` is a sphere vector field
   with `∂̄v_c = μ_c`; invariance places its deformation field
   `δv_c = f′·v_c − v_c∘f` in the `(2d+1)`-dimensional section space
   (`exists_sectionSpace_rep_deltaField`). The assignment `c ↦ [δv_c]` is
   linear — every stage (seed, spread, solver, delta, carrier
   representative) is linear — from a `(2d+2)`-dimensional space into a
   `(2d+1)`-dimensional one, so some `c ≠ 0` has `δv_c = 0` off the poles
   (`exists_nonzero_seed_with_deltaField_eq_zero`).
4. *Contradiction*: a trivial deformation vanishes on the Julia set
   (`sphereField_eq_zero_on_juliaSet_of_deltaField_eq_zero`), hence on the
   frontier of `U` (which lies in the Julia set); the seed-triviality
   criterion (`seed_vanish_of_sphereField_vanish_on_frontier`, with a
   damping point outside the closure of `U` supplied by the disjoint next
   orbit component) then forces `c = 0` — a contradiction
   (`not_isWandering_of_injective_package`).

The eventually-periodic form follows through the wandering dichotomy
`isWandering_iff_not_isEventuallyPeriodic`.
-/

open MeasureTheory Complex Metric Filter Topology Function OnePoint

namespace NoWanderingDomains

/-! ## Assembly nodes -/

/-- A Fatou component contains a closed disk in its finite part: the
component is open and nonempty, and it cannot reduce to `{∞}` since the
sphere has no isolated points, so it contains a finite point together with
a chart ball around it. -/
theorem IsFatouComponent.exists_closedBall_subset {f : ℂ̂ → ℂ̂} {U : Set ℂ̂}
    (hU : IsFatouComponent f U) :
    ∃ (a : ℂ) (ρ : ℝ), 0 < ρ ∧
      ∀ z ∈ Metric.closedBall a ρ, ((z : ℂ̂) ∈ U) := by
  have hopen : IsOpen U := hU.isOpen
  have hne : U.Nonempty := hU.nonempty
  have hdense : Dense (Set.range ((↑) : ℂ → ℂ̂)) := OnePoint.denseRange_coe
  obtain ⟨x, hxU, hxr⟩ := hdense.inter_open_nonempty U hopen hne
  obtain ⟨a, rfl⟩ := hxr
  have hpre : IsOpen {z : ℂ | ((z : ℂ̂) ∈ U)} :=
    hopen.preimage OnePoint.continuous_coe
  have haU : a ∈ {z : ℂ | ((z : ℂ̂) ∈ U)} := hxU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hpre a haU
  refine ⟨a, ε / 2, by positivity, fun z hz => ?_⟩
  exact hball (Metric.mem_ball.mpr
    (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)))

/-- The frontier of the finite part transfers to the frontier upstairs: the
coercion `ℂ → ℂ̂` is an open embedding, so a finite-chart frontier point of
`{z | ↑z ∈ U}` maps to a frontier point of `U`. -/
theorem frontier_finitePart_subset (U : Set ℂ̂) :
    frontier {z : ℂ | ((z : ℂ̂) ∈ U)}
      ⊆ {z : ℂ | ((z : ℂ̂) ∈ frontier U)} := by
  intro z hz
  have hc : Continuous ((↑) : ℂ → ℂ̂) := OnePoint.continuous_coe
  have hclU : ((z : ℂ̂)) ∈ closure U :=
    hc.closure_preimage_subset U hz.1
  have hintU : ((z : ℂ̂)) ∉ interior U := by
    intro hmem
    exact hz.2 (preimage_interior_subset_interior_preimage hc hmem)
  exact ⟨hclU, hintU⟩

/-- **A damping point exists** for a wandering component: some finite point
avoids the closure of the finite part of `U`. The next orbit component
`fcOrbit f U 1` is open, nonempty, and disjoint from `U`; were it contained
in the closure of `U` it would lie in the frontier of `U`, hence in the
Julia set — contradicting that it consists of Fatou points. A finite point
of it works. -/
theorem exists_damping_point {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (hW : IsWandering f U) :
    ∃ b : ℂ, b ∉ closure {z : ℂ | ((z : ℂ̂) ∈ U)} := by
  have hU₁ : IsFatouComponent f (fcOrbit f U 1) :=
    isFatouComponent_fcOrbit 1 hf hd hU
  have hdisj : Disjoint U (fcOrbit f U 1) := by
    have h01 := isWandering_iff.mp hW 0 1 (by norm_num)
    rwa [fcOrbit_zero hU] at h01
  have hdense : Dense (Set.range ((↑) : ℂ → ℂ̂)) := OnePoint.denseRange_coe
  obtain ⟨x, hxU₁, hxr⟩ := hdense.inter_open_nonempty _ hU₁.isOpen hU₁.nonempty
  obtain ⟨b, rfl⟩ := hxr
  refine ⟨b, fun hbcl => ?_⟩
  have hbU : b ∉ {z : ℂ | ((z : ℂ̂) ∈ U)} :=
    fun h => Set.disjoint_left.mp hdisj h hxU₁
  have hbfr : b ∈ frontier {z : ℂ | ((z : ℂ̂) ∈ U)} :=
    ⟨hbcl, fun h => hbU (interior_subset h)⟩
  have hfrU : ((b : ℂ̂)) ∈ frontier U := frontier_finitePart_subset U hbfr
  have hjul : ((b : ℂ̂)) ∈ JuliaSet f := hU.frontier_subset_juliaSet hfrU
  exact Set.disjoint_left.mp (disjoint_fatouSet_juliaSet f)
    (hU₁.subset_fatouSet hxU₁) hjul

/-- **Bridging critical-avoidance formats**: from stepwise nonvanishing of
the finite-chart derivative of `f` on every orbit component (the format
produced by `exists_wandering_injective_package`) to nonvanishing of the
orbit derivative cocycle `iterDeriv` on `U` (the format consumed by the
spreading theorems): the orbit of a point of `U` visits the successive orbit
components, stays finite, and each factor of the product is a nonzero
step derivative. -/
theorem iterDeriv_ne_zero_of_orbit_noncritical
    {r : RationalData} (hd : 1 ≤ r.degree) {U : Set ℂ̂}
    (hU : IsFatouComponent r.toSphereMap U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit r.toSphereMap U n)
    (hcrit : ∀ n : ℕ, ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit r.toSphereMap U n) →
      deriv (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂)))) z ≠ 0) :
    ∀ z : ℂ, ((z : ℂ̂) ∈ U) → ∀ n : ℕ, iterDeriv r n z ≠ 0 := by
  intro z hz n
  have hfr : IsRational r.toSphereMap := ⟨r, rfl⟩
  have hdeg : 1 ≤ degreeOfRational r.toSphereMap := by
    rw [degreeOfRational_eq_of_witness r.toSphereMap r rfl]; exact hd
  have hfo : IsOpenMap r.toSphereMap := hfr.isOpenMap (hfr.ne_const hdeg)
  have hfwd : ∀ k : ℕ,
      r.toSphereMap^[k] ((z : ℂ̂)) ∈ FatouSet r.toSphereMap := by
    intro k
    induction k with
    | zero => simpa using hU.subset_fatouSet hz
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact apply_mem_fatouSet hfo ih
  have hmem : ∀ k : ℕ,
      r.toSphereMap^[k] ((z : ℂ̂)) ∈ fcOrbit r.toSphereMap U k :=
    fun k => Set.mem_biUnion hz (mem_connectedComponentIn (hfwd k))
  unfold iterDeriv
  rw [Finset.prod_ne_zero_iff]
  intro j _hj
  have hjfin : r.toSphereMap^[j] ((z : ℂ̂)) ≠ ∞ := fun h => hinf j (h ▸ hmem j)
  obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hjfin
  have hwmem : ((w : ℂ̂)) ∈ fcOrbit r.toSphereMap U j := by
    rw [hw]; exact hmem j
  have hden : r.denReduced.eval w ≠ 0 := by
    intro h0
    have hnext : r.toSphereMap^[j + 1] ((z : ℂ̂)) = ∞ := by
      rw [Function.iterate_succ_apply', ← hw]
      show r.toSphereMap ((w : ℂ̂)) = ∞
      simp only [RationalData.toSphereMap]
      rw [if_pos h0]
    exact hinf (j + 1) (hnext ▸ hmem (j + 1))
  rw [← hw]
  have hread : chartFiniteMap ((w : ℂ̂)) = w := rfl
  rw [hread, fderivRational_eq_deriv_reading r hden]
  exact hcrit j w hwmem

/-- **The rank–nullity extraction.** Under the injectivity package and with
a seed disk in the finite part of `U`, some nonzero seed combination has
vanishing deformation field: the assignment

`c ↦ (carrier representative of) δ(dbarSolver (spreadCoeff (σ_c)))`

is a linear map from the `(2d+2)`-dimensional seed space into the
`(2d+1)`-dimensional section space — linearity composes from
`spreadCoeff_add`/`spreadCoeff_smul`, `dbarSolver_add`/`dbarSolver_smul`
(fed by `spreadCoeff_aemeasurable` and `spreadCoeff_eLpNormEssSup_le`),
pointwise linearity of `deltaField` in the field, and uniqueness of the
carrier representative (`sectionSpaceCarrier_eqOn_nonpoles_eq`) — so its
kernel is nontrivial by `finrank_sectionSpaceCarrier` and dimension
counting. A kernel element `c ≠ 0` has `δ(dbarSolver μ_c) = 0` at every
non-pole. -/
theorem exists_nonzero_seed_with_deltaField_eq_zero
    {r : RationalData} (hd : 2 ≤ r.degree)
    {U : Set ℂ̂} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hU : IsFatouComponent r.toSphereMap U)
    (hW : IsWandering r.toSphereMap U)
    (hinj : ∀ n : ℕ, Set.InjOn (r.toSphereMap^[n]) U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit r.toSphereMap U n)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ U) → ∀ n : ℕ, iterDeriv r n z ≠ 0)
    (hball : ∀ z ∈ Metric.closedBall a ρ, ((z : ℂ̂) ∈ U)) :
    ∃ c : Fin (2 * r.degree + 2) → ℂ, c ≠ 0 ∧
      ∀ z : ℂ, r.denReduced.eval z ≠ 0 →
        deltaField r
          (dbarSolver (spreadCoeff r (Metric.closedBall a ρ)
            (seedCombo a ρ (2 * r.degree + 2) c))) z = 0 := by
  classical
  have hd1 : 1 ≤ r.degree := le_trans one_le_two hd
  set K := 2 * r.degree + 2 with hK
  set S : Set ℂ := Metric.closedBall a ρ with hSdef
  have hSm : MeasurableSet S := measurableSet_closedBall
  -- ===== The seed package: vanishing off `S`, measurability, boundedness. =====
  have hσ0 : ∀ c : Fin K → ℂ, ∀ z : ℂ, z ∉ S → seedCombo a ρ K c z = 0 := by
    intro c z hz
    have hz' : z ∉ Metric.ball a ρ := fun h => hz (Metric.ball_subset_closedBall h)
    unfold seedCombo
    refine Finset.sum_eq_zero fun k _ => ?_
    unfold seedBasis
    rw [if_neg hz', mul_zero]
  have hσm : ∀ c : Fin K → ℂ, Measurable (seedCombo a ρ K c) := by
    intro c
    unfold seedCombo
    refine Finset.measurable_sum _ fun k _ => ?_
    refine Measurable.const_mul ?_ (c k)
    unfold seedBasis
    refine Measurable.ite measurableSet_ball ?_ measurable_const
    fun_prop
  have hσb : ∀ c : Fin K → ℂ, eLpNormEssSup (seedCombo a ρ K c) volume < ⊤ := by
    intro c
    have hρ0 : (0 : ℝ) ≤ ρ := le_of_lt hρ
    have hbd : ∀ z : ℂ, ‖seedCombo a ρ K c z‖
        ≤ ∑ k : Fin K, ‖c k‖ * (((k : ℕ) : ℝ) + 1) * ρ ^ (k : ℕ) := by
      intro z
      unfold seedCombo
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      unfold seedBasis
      by_cases hz : z ∈ Metric.ball a ρ
      · rw [if_pos hz, norm_mul, norm_pow, Complex.norm_conj]
        have h1 : ‖((k : ℕ) : ℂ) + 1‖ = ((k : ℕ) : ℝ) + 1 := by
          have h2 : ((k : ℕ) : ℂ) + 1 = (((k : ℕ) + 1 : ℕ) : ℂ) := by push_cast; ring
          rw [h2, Complex.norm_natCast]
          push_cast; ring
        rw [h1]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _)
          (le_of_lt (mem_ball_iff_norm.mp hz)) _
      · rw [if_neg hz, norm_zero]
        exact mul_nonneg (by positivity) (pow_nonneg hρ0 _)
    exact lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound (ae_of_all volume hbd))
      ENNReal.ofReal_lt_top
  -- ===== The spread package: measurability, boundedness, invariance. =====
  have hμm : ∀ c : Fin K → ℂ,
      AEMeasurable (spreadCoeff r S (seedCombo a ρ K c)) volume := fun c =>
    spreadCoeff_aemeasurable hd1 hU hW hinj hinf hcrit hball hSm (hσ0 c) (hσm c)
  have hμb : ∀ c : Fin K → ℂ,
      eLpNormEssSup (spreadCoeff r S (seedCombo a ρ K c)) volume < ⊤ := fun c =>
    lt_of_le_of_lt (spreadCoeff_eLpNormEssSup_le hd1 hU hW hinj hinf hcrit hball
      hSm (hσ0 c) (hσm c)) (hσb c)
  have hμinv : ∀ c : Fin K → ℂ,
      IsInvariantBeltrami r (spreadCoeff r S (seedCombo a ρ K c)) := fun c =>
    isInvariantBeltrami_spreadCoeff hd1 hU hW hinj hinf hcrit hball hSm
      (hσ0 c) (hσm c)
  -- ===== Linearity of the pipeline at the `deltaField` level. =====
  have hpipe_add : ∀ c c' : Fin K → ℂ, ∀ z : ℂ,
      deltaField r (dbarSolver (spreadCoeff r S (seedCombo a ρ K (c + c')))) z
        = deltaField r (dbarSolver (spreadCoeff r S (seedCombo a ρ K c))) z
          + deltaField r (dbarSolver (spreadCoeff r S (seedCombo a ρ K c'))) z := by
    intro c c' z
    have h1 : seedCombo a ρ K (c + c')
        = fun w => seedCombo a ρ K c w + seedCombo a ρ K c' w := by
      funext w
      simp only [seedCombo, Pi.add_apply, add_mul]
      exact Finset.sum_add_distrib
    have h3 : dbarSolver (spreadCoeff r S (seedCombo a ρ K (c + c')))
        = fun w => dbarSolver (spreadCoeff r S (seedCombo a ρ K c)) w
            + dbarSolver (spreadCoeff r S (seedCombo a ρ K c')) w := by
      rw [h1, spreadCoeff_add r S]
      exact dbarSolver_add (hμm c) (hμm c') (hμb c) (hμb c')
    simp only [deltaField, h3]
    ring
  have hpipe_smul : ∀ (t : ℂ) (c : Fin K → ℂ), ∀ z : ℂ,
      deltaField r (dbarSolver (spreadCoeff r S (seedCombo a ρ K (t • c)))) z
        = t * deltaField r (dbarSolver (spreadCoeff r S (seedCombo a ρ K c))) z := by
    intro t c z
    have h1 : seedCombo a ρ K (t • c)
        = fun w => t * seedCombo a ρ K c w := by
      funext w
      simp only [seedCombo, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    have h3 : dbarSolver (spreadCoeff r S (seedCombo a ρ K (t • c)))
        = fun w => t * dbarSolver (spreadCoeff r S (seedCombo a ρ K c)) w := by
      rw [h1, spreadCoeff_smul r S]
      exact dbarSolver_smul t _
    simp only [deltaField, h3]
    ring
  -- ===== The carrier representative of each deformation field. =====
  have hrep : ∀ c : Fin K → ℂ, ∃ s : SectionSpaceCarrier r, ∀ z : ℂ,
      r.denReduced.eval z ≠ 0 →
        deltaField r (dbarSolver (spreadCoeff r S (seedCombo a ρ K c))) z
          = (s : ℂ → ℂ) z := by
    intro c
    obtain ⟨s, hs, hagree⟩ := exists_sectionSpace_rep_deltaField hd1
      (isSphereVectorField_dbarSolver (hμm c) (hμb c))
      (hasL2WeakDzbar_dbarSolver (hμm c) (hμb c)) (hμinv c) (hμb c)
    exact ⟨⟨s, hs⟩, hagree⟩
  choose Θ hΘ using hrep
  -- ===== Linearity of `Θ` from uniqueness of the representative. =====
  have hadd : ∀ c c' : Fin K → ℂ, Θ (c + c') = Θ c + Θ c' := by
    intro c c'
    apply Subtype.ext
    apply sectionSpaceCarrier_eqOn_nonpoles_eq (Θ (c + c')).2 (Θ c + Θ c').2
    intro z hz
    rw [← hΘ (c + c') z hz, hpipe_add c c' z, hΘ c z hz, hΘ c' z hz]
    rfl
  have hsmul : ∀ (t : ℂ) (c : Fin K → ℂ), Θ (t • c) = t • Θ c := by
    intro t c
    apply Subtype.ext
    apply sectionSpaceCarrier_eqOn_nonpoles_eq (Θ (t • c)).2 (t • Θ c).2
    intro z hz
    rw [← hΘ (t • c) z hz, hpipe_smul t c z, hΘ c z hz]
    rfl
  let Θₗ : (Fin K → ℂ) →ₗ[ℂ] SectionSpaceCarrier r :=
    { toFun := Θ, map_add' := hadd, map_smul' := hsmul }
  -- ===== Dimension count: the kernel is nontrivial. =====
  have hfin1 : Module.Finite ℂ (Polynomial.degreeLT ℂ (2 * r.degree + 1)) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv ℂ (2 * r.degree + 1)).symm
  have hfin2 : Module.Finite ℂ (SectionSpaceCarrier r) :=
    Module.Finite.map (Polynomial.degreeLT ℂ (2 * r.degree + 1)) (polyOverDenSq r)
  obtain ⟨c, hc0, hcker⟩ : ∃ c : Fin K → ℂ, c ≠ 0 ∧ Θ c = 0 := by
    by_contra hcon
    push Not at hcon
    have hker : LinearMap.ker Θₗ = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro m hm
      by_contra hm0
      have hm' : Θ m = 0 := hm
      exact hcon m hm0 hm'
    have hinj' : Function.Injective Θₗ := LinearMap.ker_eq_bot.mp hker
    have hle := LinearMap.finrank_le_finrank_of_injective hinj'
    rw [Module.finrank_fin_fun, finrank_sectionSpaceCarrier] at hle
    omega
  -- ===== Unpack: the zero representative kills `δv_c` off the poles. =====
  refine ⟨c, hc0, fun z hz => ?_⟩
  rw [hΘ c z hz, hcker]
  rfl

/-- **The contradiction core.** A Fatou component carrying the full
injectivity package cannot wander: a nonzero seed `c` with trivial
deformation field exists by rank–nullity; the associated sphere field
`v_c = dbarSolver μ_c` vanishes on the (finite) Julia set, hence on the
frontier of the finite part of `U`; the seed-triviality criterion — with a
damping point from `exists_damping_point` and the restriction law
`spreadCoeff_restrict` identifying `∂̄v_c` with `σ_c` on `U` — forces
`c = 0`. -/
theorem not_isWandering_of_injective_package
    {r : RationalData} (hd : 2 ≤ r.degree) {U : Set ℂ̂}
    (hU : IsFatouComponent r.toSphereMap U)
    (hinj : ∀ n : ℕ, Set.InjOn (r.toSphereMap^[n]) U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit r.toSphereMap U n)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ U) → ∀ n : ℕ, iterDeriv r n z ≠ 0) :
    ¬ IsWandering r.toSphereMap U := by
  intro hW
  -- (1) a closed disk in the finite part of `U`
  obtain ⟨a, ρ, hρ, hball⟩ := hU.exists_closedBall_subset
  -- degree bookkeeping
  have hd1 : 1 ≤ r.degree := le_trans one_le_two hd
  have hfr : IsRational r.toSphereMap := ⟨r, rfl⟩
  have hdeg1 : 1 ≤ degreeOfRational r.toSphereMap := by
    rw [degreeOfRational_eq_of_witness r.toSphereMap r rfl]; exact hd1
  -- (2) a damping point outside the closure of the finite part
  obtain ⟨b, hb⟩ := exists_damping_point hfr hdeg1 hU hW
  -- (3) a nonzero kernel seed
  obtain ⟨c, hc0, hδ⟩ :=
    exists_nonzero_seed_with_deltaField_eq_zero hd hρ hU hW hinj hinf hcrit hball
  -- seed-combination facts: support, measurability, boundedness
  have hσ0 : ∀ z : ℂ, z ∉ Metric.closedBall a ρ →
      seedCombo a ρ (2 * r.degree + 2) c z = 0 := by
    intro z hz
    have hzb : z ∉ Metric.ball a ρ := fun h => hz (Metric.ball_subset_closedBall h)
    simp [seedCombo, seedBasis, hzb]
  have hσm : Measurable (seedCombo a ρ (2 * r.degree + 2) c) := by
    have hkm : ∀ k : Fin (2 * r.degree + 2),
        Measurable (fun z : ℂ => c k * seedBasis a ρ (k : ℕ) z) := by
      intro k
      have hbase : Measurable (seedBasis a ρ (k : ℕ)) := by
        unfold seedBasis
        exact Measurable.ite measurableSet_ball (by fun_prop) measurable_const
      exact hbase.const_mul (c k)
    exact Finset.measurable_sum Finset.univ (fun k _ => hkm k)
  have hSm : MeasurableSet (Metric.closedBall a ρ) := measurableSet_closedBall
  have hσbdd : eLpNormEssSup (seedCombo a ρ (2 * r.degree + 2) c) volume < ⊤ := by
    refine eLpNormEssSup_lt_top_of_ae_bound
      (C := ∑ k : Fin (2 * r.degree + 2),
        ‖c k‖ * ((((k : ℕ) : ℝ) + 1) * ρ ^ (k : ℕ)))
      (Filter.Eventually.of_forall fun z => ?_)
    unfold seedCombo
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    unfold seedBasis
    split_ifs with h
    · rw [norm_mul, norm_pow, Complex.norm_conj]
      have h1 : ‖(((k : ℕ) : ℂ)) + 1‖ = (((k : ℕ) : ℝ)) + 1 := by norm_cast
      rw [h1]
      have hza : ‖z - a‖ ≤ ρ := le_of_lt (mem_ball_iff_norm.mp h)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hza _) (by positivity)
    · rw [norm_zero]; positivity
  -- (4) the sphere field `v = dbarSolver μ` and its weak `∂̄`-data
  have hμm : AEMeasurable
      (spreadCoeff r (Metric.closedBall a ρ) (seedCombo a ρ (2 * r.degree + 2) c))
      volume :=
    spreadCoeff_aemeasurable hd1 hU hW hinj hinf hcrit hball hSm hσ0 hσm
  have hμb : eLpNormEssSup
      (spreadCoeff r (Metric.closedBall a ρ) (seedCombo a ρ (2 * r.degree + 2) c))
      volume < ⊤ :=
    lt_of_le_of_lt
      (spreadCoeff_eLpNormEssSup_le hd1 hU hW hinj hinf hcrit hball hSm hσ0 hσm)
      hσbdd
  have hv : IsSphereVectorField
      (dbarSolver (spreadCoeff r (Metric.closedBall a ρ)
        (seedCombo a ρ (2 * r.degree + 2) c))) :=
    isSphereVectorField_dbarSolver hμm hμb
  have hgrad : HasL2WeakDzbar
      (dbarSolver (spreadCoeff r (Metric.closedBall a ρ)
        (seedCombo a ρ (2 * r.degree + 2) c)))
      (spreadCoeff r (Metric.closedBall a ρ) (seedCombo a ρ (2 * r.degree + 2) c))
      Set.univ :=
    hasL2WeakDzbar_dbarSolver hμm hμb
  -- (5) `v` vanishes at every finite Julia point
  have hjul : ∀ z : ℂ, ((z : ℂ̂) ∈ JuliaSet r.toSphereMap) →
      dbarSolver (spreadCoeff r (Metric.closedBall a ρ)
        (seedCombo a ρ (2 * r.degree + 2) c)) z = 0 :=
    sphereField_eq_zero_on_juliaSet_of_deltaField_eq_zero hd hv hδ
  -- (6) hence on the frontier of the finite part of `U`
  have hU'open : IsOpen {z : ℂ | ((z : ℂ̂) ∈ U)} :=
    hU.isOpen.preimage OnePoint.continuous_coe
  have hball' : Metric.closedBall a ρ ⊆ {z : ℂ | ((z : ℂ̂) ∈ U)} :=
    fun z hz => hball z hz
  have hfront : ∀ p ∈ frontier {z : ℂ | ((z : ℂ̂) ∈ U)},
      dbarSolver (spreadCoeff r (Metric.closedBall a ρ)
        (seedCombo a ρ (2 * r.degree + 2) c)) p = 0 := fun p hp =>
    hjul p (hU.frontier_subset_juliaSet (frontier_finitePart_subset U hp))
  -- (7) the restriction law gives the local identification `μ = σ_c` on `U`
  have hrestr : ∀ z : ℂ, ((z : ℂ̂) ∈ U) →
      spreadCoeff r (Metric.closedBall a ρ) (seedCombo a ρ (2 * r.degree + 2) c) z
        = seedCombo a ρ (2 * r.degree + 2) c z :=
    spreadCoeff_restrict hd1 hU hW hinj hcrit hball hσ0
  have hloc : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ {z : ℂ | ((z : ℂ̂) ∈ U)} →
      spreadCoeff r (Metric.closedBall a ρ) (seedCombo a ρ (2 * r.degree + 2) c) z
        = seedCombo a ρ (2 * r.degree + 2) c z :=
    Filter.Eventually.of_forall fun z hz => hrestr z hz
  -- (8) seed triviality forces `c = 0`, contradiction
  exact hc0 (seed_vanish_of_sphereField_vanish_on_frontier hU'open hρ hball'
    ⟨b, hb⟩ hv hgrad hloc hfront)

/-! ## The theorem -/

/-- **Sullivan's No Wandering Domains theorem.** No Fatou component of a
rational map of degree at least two wanders. Bridge the map to a
`RationalData` witness, then normalize: `exists_wandering_injective_package`
returns a later orbit component `fcOrbit f U N` that still wanders and on
which every iterate is injective, its orbit avoiding `∞` and the critical
points. The contradiction core refutes the wandering of *that* component,
which the package supplies directly — no descent back to `U` is needed. -/
theorem sullivan_no_wandering_domains {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f) :
    ∀ U : Set ℂ̂, IsFatouComponent f U → ¬ IsWandering f U := by
  intro U hU hW
  -- Bridge the map to a `RationalData` witness.
  obtain ⟨r, rfl⟩ := hf
  have hfr : IsRational r.toSphereMap := ⟨r, rfl⟩
  have hdr : 2 ≤ r.degree := by
    rw [← degreeOfRational_eq_of_witness r.toSphereMap r rfl]; exact hd
  -- Normalize: pass to a later orbit component carrying the full package.
  obtain ⟨N, hUC, hWC, hinj, hinf, hcrit⟩ :=
    exists_wandering_injective_package hfr hd hU hW
  -- Convert stepwise critical-avoidance to the `iterDeriv` cocycle format.
  have hcrit' : ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit r.toSphereMap U N) →
      ∀ n : ℕ, iterDeriv r n z ≠ 0 :=
    iterDeriv_ne_zero_of_orbit_noncritical (le_trans one_le_two hdr)
      hUC hinf hcrit
  -- The contradiction core refutes the wandering of the relabeled component.
  exact not_isWandering_of_injective_package hdr hUC hinj hinf hcrit' hWC

/-- **Every Fatou component is eventually periodic** — the positive form of
Sullivan's theorem, through the wandering / eventually-periodic
dichotomy. -/
theorem fatouComponent_isEventuallyPeriodic {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) :
    IsEventuallyPeriodic f U := by
  by_contra hnep
  have hW : IsWandering f U :=
    (isWandering_iff_not_isEventuallyPeriodic hf
      (le_trans one_le_two hd) hU).mpr hnep
  exact sullivan_no_wandering_domains hf hd U hU hW

end NoWanderingDomains
