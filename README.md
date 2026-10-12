# Morphism Properties

Relative preservation of maps between pullbacks, and canonical pullback transport
between structured over-categories, using Mathlib's morphism-property classes.
The library is intended for categorical base-change arguments where absolute
stability or pullbacks of every object would be stronger than necessary.

## Headline results

All declarations below lie in `CategoryTheory.MorphismProperty`.
In the one-factor results, `f : S' ⟶ S` is a fixed base-change arrow.
For structure maps `v₁₂ : X ⟶ S`, `v₂₂ : Y ⟶ S`, and `g : X ⟶ Y` with
`v₁₂ = g ≫ v₂₂`, the induced map is `X ×[S] S' ⟶ Y ×[S] S'`.
In the two-factor result, instead, `f : X ⟶ S` and `g : Y ⟶ S` are structure
arrows into the common base, as are `f' : X' ⟶ S` and `g' : Y' ⟶ S`.
Maps `i₁ : X ⟶ X'` and `i₂ : Y ⟶ Y'` satisfying `f = i₁ ≫ f'` and
`g = i₂ ≫ g'` induce Mathlib's `pullback.map : X ×[S] Y ⟶ X' ×[S] Y'`.

- **Preservation along a target projection**
  ([`pullbackLift_fst_snd_of_isStableUnderBaseChangeAlong`](MorphismProperties/RelativeBaseChange.lean)).
  If `P g` and `P` is stable under base change along `Y ×[S] S' ⟶ Y`,
  the induced map has property `P`. Only the two endpoint pullbacks are required.
- **Relative preservation along an `E` arrow**
  ([`pullbackLift_fst_snd_of_isStableUnderBaseChangeAgainst`](MorphismProperties/RelativeBaseChange.lean)).
  Assume `P.IsStableUnderBaseChangeAgainst E`, `E.IsStableUnderBaseChange`,
  `E f`, and `P g`, with the two endpoint pullbacks. Then the induced map has `P`.
- **Relative slice-functor preservation**
  ([`overPullbackMap_of_isStableUnderBaseChangeAgainst`](MorphismProperties/RelativeBaseChange.lean)).
  Under the same stability and base-arrow hypotheses and
  `Limits.HasPullbacksAlong f`, Mathlib's existing `CategoryTheory.Over.pullback f`
  preserves `P` on underlying horizontal arrows.
- **Object-structured preservation**
  ([`pullbackLift_fst_snd_of_intersection_of_postcomp`](MorphismProperties/RelativeBaseChange.lean)).
  Assume `(P ⊓ E).IsStableUnderBaseChange`, `E.HasOfPostcompProperty E`,
  `E v₁₂`, `E v₂₂`, and `P g`. With the two endpoint pullbacks, the induced
  map belongs to `P ⊓ E` along arbitrary `f`, without `E f` or absolute
  stability of `P` or `E`.
- **One-factor preservation alternatives**
  ([`pullbackLift_fst_snd_of_relative_alternatives`](MorphismProperties/RelativeBaseChange.lean)).
  Assume stability of `P` against `E`, absolute stability of `P ⊓ E` and of
  `E`, cancellation of `E` under postcomposition by `E`, and `P g`. With the
  endpoint pullbacks, the induced map has `P` if either both structure maps
  belong to `E` or `f` belongs to `E`.
- **Two-factor relative preservation**
  ([`pullbackMap_of_relative_alternatives`](MorphismProperties/RelativeBaseChange.lean)).
  Assume composition closure of `P`, stability of `P` against `E`, absolute
  stability of `P ⊓ E` and `E`, and cancellation of `E` under postcomposition
  by `E`. If `P i₁` and `P i₂`, the canonical map has `P` provided either
  `E f ∧ E f'` or `E f ∧ E g'`. Besides the endpoint pullbacks of `(f, g)`
  and `(f', g')`, only the mixed pullback selected by the alternative is
  required: `(f', g)` in the first case, `(f, g')` in the second.
  No identity closure of `P` is assumed.
- **Absolute two-factor specialization**
  ([`pullbackMap_of_relative_alternatives_top`](MorphismProperties/RelativeBaseChange.lean)).
  With `E = ⊤`, absolute base-change stability and composition closure of `P`,
  `P i₁`, `P i₂`, and the same commuting equations suffice under Mathlib's
  `pullbackMap` hypotheses `Limits.HasPullbacksAlong f` and
  `Limits.HasPullbacksAlong g'`. The conclusion is membership for the same
  canonical map. No pullbacks along `g` or identity closure are added.
- **Either-leg criterion for existing squares**
  ([`isStableUnderBaseChange_either_iff`](MorphismProperties/RelativeBaseChange.lean)).
  For base-change-stable `E`, preservation of `P` on an existing square
  `IsPullback p q a b` whenever `P a` and `E a ∨ E b` is equivalent to
  `P.IsStableUnderBaseChangeAgainst E` and `(P ⊓ E).IsStableUnderBaseChange`.
  The preserved arrow is `q`; no pullback-existence assumption is made.
- **Canonical structured-over transport**
  ([`Over.pullbackOfIntersectionOfPostcomp`](MorphismProperties/OverPullback.lean)).
  A functor `E.Over P S ⥤ E.Over P S'` assuming `P.IsMultiplicative`,
  `E.HasPullbacksAlong f`, `E.IsStableUnderBaseChangeAlong f`,
  `(P ⊓ E).IsStableUnderBaseChange`, and `E.HasOfPostcompProperty E`.
  Here existence is required only for structure arrows satisfying `E`,
  not for every object over `S`.

The transport API characterizes objects, structure maps, underlying maps and
both projections, supplies membership in `P` and `P ⊓ E`, and gives the ambient
pullback universal property and uniqueness of the structured map and functor lift.
Identity and composition equations come from the assembled functor laws.
Under absolute stability of `P`, the functor agrees with Mathlib's structured
pullback. Under `Limits.HasPullbacksAlong f`, its forgetful factorization has
Mathlib's ordinary over-category pullback comparison isomorphism.

## Using the library

To use a published version, add this dependency to `lakefile.toml`:

```toml
[[require]]
name = "morphism-properties"
git = "https://github.com/FormalFrontier/morphism-properties.git"
rev = "main"
```

GitHub `main` is reserved for reviewed releases. Lake records the resolved commit
in `lake-manifest.json`; replace `main` with a full commit from that history for
an exact pin. Libraries used together must resolve the same Mathlib commit.
This project uses Lean `leanprover/lean4:v4.34.0-rc2` and Mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, with no other direct dependency.

```lean
import MorphismProperties
import MorphismPropertiesExamples.RelativeBaseChange

open CategoryTheory.MorphismProperty

example :
    (monomorphisms NonemptyFinsets.C ⊓ monomorphisms NonemptyFinsets.C)
      NonemptyFinsets.pullbackMap :=
  NonemptyFinsets.pullbackMap_mem_monomorphisms_inter
```

The example theorem is exercised in
[`MorphismPropertiesExamples.RelativeBaseChange`](MorphismPropertiesExamples/RelativeBaseChange.lean).
Leaf imports `MorphismProperties.RelativeBaseChange` and
`MorphismProperties.OverPullback` are also available.

## Building

The toolchain and complete Mathlib dependency graph are pinned in
`lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get && lake build
```

The default build includes both the library and all example modules.
The scientific CI workflow builds these targets and audits transitive axiom
dependencies, including private and generated declarations and used imports.

## Contents

| Module | Contents |
| --- | --- |
| [`MorphismProperties.RelativeBaseChange`](MorphismProperties/RelativeBaseChange.lean) | One- and two-factor relative preservation, either-leg criterion, absolute comparison and slice client. |
| [`MorphismProperties.OverPullback`](MorphismProperties/OverPullback.lean) | Canonical structured-over functor, characteristic API and Mathlib comparisons. |
| [`MorphismPropertiesExamples.RelativeBaseChange`](MorphismPropertiesExamples/RelativeBaseChange.lean) | Three- and four-object chains; endpoint pullbacks in nonempty finite subsets. |
| [`MorphismPropertiesExamples.OverPullback`](MorphismPropertiesExamples/OverPullback.lean) | Structured transport outside `E`, projections, uniqueness and nonisomorphic endpoints. |
| [`MorphismPropertiesExamples.PullbackMap`](MorphismPropertiesExamples/PullbackMap.lean) | Selected mixed existence, absolute comparison, proper finite-type inclusions isolating both alternatives, relative chain and finite-subset clients. |
| [`MorphismPropertiesExamples.IdentityClosure`](MorphismPropertiesExamples/IdentityClosure.lean) | A composition- and base-change-stable target-bound property excluding an identity, with both factors changing. |

## Conventions and limitations

Object and morphism universes are independent. The library retains Mathlib's
`CategoryTheory.MorphismProperty` namespaces, stability classes, comma categories,
pullback constructions and functor machinery; it introduces no new category or
existence class. One-factor pointwise results do not assume identity or
composition closure of the morphism properties. Two-factor preservation assumes
composition closure of `P`, but not identity closure of `P` or identity/composition
closure of `E`. Structured transport needs multiplicativity of `P`, but not
identity/composition closure of `E`, absolute stability of `P`, or `E f`.

The four-object-chain examples exhibit relative but not absolute stability and
transport `1 ⟶ 3` to `1 ⟶ 2` along `2 ⟶ 3`, outside `E`. The three-object chain
shows why relative stability alone does not imply the either-leg criterion.
Nonempty finite subsets of `Fin 3` have the two required endpoint pullbacks,
but the disjoint singleton `{2}` has no pullback along the same base arrow
`{0, 1} ⟶ {0, 1, 2}`. This separates the pointwise endpoint hypotheses from
whole-over and global pullback existence. Its two-factor example changes both
input inclusions; monomorphisms in that thin category are all arrows, so it tests
existence rather than a proper morphism property. The finite-type monomorphism
examples use proper inclusions in both factors and isolate the two alternatives.
The non-absolutely-stable four-object-chain two-factor example changes only the
second factor. On `Fin 4`, the property of having target at most `2` is stable
under composition and absolute base change but excludes the identity at `3`;
both input maps change and induce `0 ⟶ 1`. This shows why two-factor preservation
does not require identity closure.

The mathematical motivation includes pointwise B1 preservation and the first B2,
object-structured alternative in Fujiwara–Kato, Chapter 0, Proposition 1.4.1.
The one-factor results fix a base-change arrow, and the two-factor result fixes
a common base and asks only for the selected mixed pullback. These results do not
establish the full B1/B2 equivalence package, its converse, an adjunction, creation
of pullbacks in the structured category, or a functor on all base arrows.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*,
  [arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5) (2017),
  Chapter 0, §1.4(a), Proposition 1.4.1: mathematical motivation.
- [Mathlib](https://github.com/leanprover-community/mathlib4),
  `CategoryTheory.MorphismProperty.Limits`, `Comma`, and `OverAdjunction`:
  reused stability, cancellation, structured-category and pullback APIs.

## Credits and license

Authors: Formal Frontier Agents. See [CREDITS.md](CREDITS.md) for mathematical
and formalization credit, including Mathlib and AI involvement.
Licensed under Apache-2.0; see [LICENSE](LICENSE).
