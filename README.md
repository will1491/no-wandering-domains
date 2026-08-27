# Sullivan's No Wandering Domains Theorem in Lean 4

A formalization of Sullivan's No Wandering Domains theorem — every Fatou component of a rational self-map of the Riemann sphere of degree at least two is eventually periodic — together with the supporting quasiconformal-analysis library.

## Highlighted Theorems

Headline results formalized — click to jump to the Lean source. Each is
sorry-free and depends only on the three standard Lean axioms (`propext`,
`Classical.choice`, `Quot.sound`).

1. **Sullivan's No Wandering Domains theorem** — [`sullivan_no_wandering_domains`](NoWanderingDomains/Dynamics/NoWanderingDomains.lean#L454): no Fatou component of a rational map of degree at least two wanders. Equivalently, in positive form, [`fatouComponent_isEventuallyPeriodic`](NoWanderingDomains/Dynamics/NoWanderingDomains.lean#L477): every Fatou component is eventually periodic.
2. **Measurable Riemann Mapping theorem** — [`mrmt_exists`](NoWanderingDomains/QC/MRMT/Existence.lean#L537): every Beltrami coefficient `‖μ‖∞ < 1` admits a quasiconformal solution of `∂̄f = μ ∂f`; [`mrmt_unique_normalized`](NoWanderingDomains/QC/MRMT/Uniqueness.lean#L401): the solution normalized by `f 0 = 0`, `f 1 = 1` is unique; [`mrmt_holomorphic_dependence_principal`](NoWanderingDomains/QC/MRMT/AnalyticDependence.lean#L63): the principal solution depends holomorphically on the coefficient.
3. **Montel–Carathéodory (strong Montel) theorem** — [`montel_caratheodory_sphere`](NoWanderingDomains/NormalFamilies/StrongMontel/SphereMontel.lean#L37): a family of sphere-holomorphic maps omitting three fixed values is normal.
4. **Equivalence of the analytic and geometric definitions of quasiconformality** — [`qc_analytic_iff_geometric`](NoWanderingDomains/QC/Equivalence.lean#L984): for `1 ≤ K`, a map carries an analytic-quasiconformal structure with Beltrami norm at most `(K−1)/(K+1)` if and only if it is `K`-quasiconformal in the geometric (modulus) sense.
5. **Schwarz–Pick inequality** — [`hyperbolicDistDisk_schwarzPick`](NoWanderingDomains/Hyperbolic/ModularLambda/TriplyPunctured.lean#L452): a holomorphic self-map of the open unit disk is non-expansive for the Poincaré hyperbolic distance.

## Foundations

Built on Mathlib, plus two vendored projects consumed directly rather than re-derived:

- **RMT4** (Beffara) — the Riemann mapping theorem and the normal-families / Montel / Hurwitz / Schwarz scaffolding the dynamics line builds on.
- **Carleson** (van Doorn et al., pinned at `v4.33.0`) — two-sided Calderón–Zygmund theory; the Beurling kernel `(z − ζ)⁻²` is registered as a two-sided CZ kernel, which is what gives the transform its `Lᵖ` bounds.

No new `axiom`, no `sorry`.

## Installation

Ensure you have [Lean 4](https://lean-lang.org/lean4/doc/setup.html) installed.

```bash
# Clone the repository
git clone https://github.com/will1491/no-wandering-domains
cd no-wandering-domains

# Build the library
lake build
```

## Verification

To check the axiom-cleanliness claims yourself, create a file containing

```lean
import NoWanderingDomains

#print axioms NoWanderingDomains.sullivan_no_wandering_domains
```

and run it with `lake env lean <file>` from the repository root (after `lake build`). The output is

```
'NoWanderingDomains.sullivan_no_wandering_domains' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Any other theorem in the library can be audited the same way.

## AI Disclaimer

Generative AI (Claude) was used in the development of this codebase. The high-level architecture is human-designed; AI agents assisted with formalizing individual proofs and writing boilerplate. All definitions and core theorem statements were human-verified for correctness. Since all proofs are verified by Lean's type checker, AI-generated and human-written code are held to the same standard of correctness.
