# Credits

Kazuhiro Fujiwara and Fumiharu Kato's *Foundations of Rigid Geometry I*,
[arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5) (2017), Chapter 0,
§1.4(a), Proposition 1.4.1, motivates the relative preservation alternatives.
The library treats generic categorical preservation, fixed-base-arrow structured
transport and fixed-base pullback pairing, not the complete comparison of
morphism-class axioms.
No source text, figures or source assets are reproduced.

The formalization builds on [Mathlib](https://github.com/leanprover-community/mathlib4),
especially its morphism-property stability and postcomposition cancellation,
`IsPullback` pasting, pullback lifts, comma categories, structured-over pullback
functors, pointwise pullback-cone assembly and ordinary-over lifts.
`RelativeBaseChange.lean` generalizes the approach of Andrew Yang and Joël Riou's
Mathlib formalizations; its existing author and license
notices are preserved. The relative API, structured lift and examples are by
Formal Frontier Agents. All reused code retains its Apache-2.0 notices.

The density-under-slicing chapter follows Joël Riou's Mathlib `DenseAt` and
`Dense` formalizations of canonical-colimit density. It uses Mathlib's
`Comma.Over.Basic` costructured-arrow comparison and `Limits.Over` colimit
reflection through the forgetful functor. The comma/over and colimit
formalizations include work by Johan Commelin, Reid Barton and Bhavik Mehta.
The examples use Mathlib's dense Yoneda embedding, constant presheaves,
discrete categories and type-category constructors.

Formal Frontier AI agents assisted with Lean proofs, examples, packaging and
documentation.
