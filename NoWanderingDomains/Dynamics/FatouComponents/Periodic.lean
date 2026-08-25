/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.FatouComponents.Def

/-!
# Wandering, eventually periodic, and periodic Fatou components

Classify a Fatou component `U` by the behaviour of its orbit of components
`fcOrbit f U n`:

* `IsWandering f U` — the orbit components are pairwise disjoint;
* `IsEventuallyPeriodic f U` — two orbit components coincide;
* `IsPeriodicComponent f U` — some positive iterate returns to `U`.

For a rational map of degree `≥ 1` these are an exact dichotomy on Fatou
components: a component wanders if and only if it is not eventually periodic
(`isWandering_iff_not_isEventuallyPeriodic`), because distinct Fatou
components are disjoint, so "two orbit components meet" is the same as "two
orbit components are equal". An eventually periodic component lands, after
finitely many steps, on a genuinely periodic component
(`IsEventuallyPeriodic.exists_isPeriodicComponent`).

This is the *Sullivan-minimal* classification: the structural facts the No
Wandering Domains theorem consumes. The finer classification of periodic
components (attracting / parabolic / Siegel / Herman) is recorded in the
project plan and developed separately; it is not needed here.
-/

open Function

namespace NoWanderingDomains

variable {f : ℂ̂ → ℂ̂}

/-- A Fatou component `U` is *wandering* when its orbit of components is
pairwise disjoint. -/
def IsWandering (f : ℂ̂ → ℂ̂) (U : Set ℂ̂) : Prop :=
  Pairwise (Function.onFun Disjoint (fcOrbit f U))

/-- A Fatou component `U` is *eventually periodic* when two of its orbit
components coincide. -/
def IsEventuallyPeriodic (f : ℂ̂ → ℂ̂) (U : Set ℂ̂) : Prop :=
  ∃ m n : ℕ, m < n ∧ fcOrbit f U m = fcOrbit f U n

/-- A Fatou component `U` is *periodic* when some positive iterate of the
component dynamics returns to it. -/
def IsPeriodicComponent (f : ℂ̂ → ℂ̂) (U : Set ℂ̂) : Prop :=
  ∃ n : ℕ, 0 < n ∧ fcOrbit f U n = U

/-- Unfolding lemma for `IsWandering`. -/
theorem isWandering_iff {U : Set ℂ̂} :
    IsWandering f U ↔
      ∀ m n : ℕ, m ≠ n → Disjoint (fcOrbit f U m) (fcOrbit f U n) :=
  Iff.rfl

/-- **The wandering / eventually-periodic dichotomy.** For a rational map of
degree `≥ 1`, a Fatou component wanders iff it is not eventually periodic. -/
theorem isWandering_iff_not_isEventuallyPeriodic {U : Set ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    (h : IsFatouComponent f U) :
    IsWandering f U ↔ ¬ IsEventuallyPeriodic f U := by
  constructor
  · intro hw hep
    obtain ⟨m, n, hmn, heq⟩ := hep
    obtain ⟨x, hx⟩ := (isFatouComponent_fcOrbit n hf hd h).nonempty
    have hxm : x ∈ fcOrbit f U m := heq ▸ hx
    exact (Set.disjoint_left.mp (hw (ne_of_lt hmn)) hxm) hx
  · intro hnep i j hij
    by_contra hnd
    have hi := isFatouComponent_fcOrbit i hf hd h
    have hj := isFatouComponent_fcOrbit j hf hd h
    have heq : fcOrbit f U i = fcOrbit f U j := (hi.eq_or_disjoint hj).resolve_right hnd
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hnep ⟨i, j, hlt, heq⟩
    · exact hnep ⟨j, i, hgt, heq.symm⟩

/-- A periodic component is eventually periodic. -/
theorem IsPeriodicComponent.isEventuallyPeriodic {U : Set ℂ̂}
    (h : IsFatouComponent f U) (hp : IsPeriodicComponent f U) :
    IsEventuallyPeriodic f U := by
  obtain ⟨n, hn, hfix⟩ := hp
  exact ⟨0, n, hn, by rw [fcOrbit_zero h, hfix]⟩

/-- An eventually periodic component reaches a genuinely periodic component
after finitely many steps. -/
theorem IsEventuallyPeriodic.exists_isPeriodicComponent {U : Set ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    (h : IsFatouComponent f U) (hep : IsEventuallyPeriodic f U) :
    ∃ m : ℕ, IsPeriodicComponent f (fcOrbit f U m) := by
  obtain ⟨m, n, hmn, heq⟩ := hep
  refine ⟨m, n - m, Nat.sub_pos_of_lt hmn, ?_⟩
  rw [← fcOrbit_add m (n - m) hf hd h, Nat.add_sub_cancel' hmn.le]
  exact heq.symm

end NoWanderingDomains
