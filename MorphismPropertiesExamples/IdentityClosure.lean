/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MorphismPropertiesExamples.RelativeBaseChange
public import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Mathlib.Tactic.Subsingleton

/-!
# Composition and base change without identity closure

In the inherited preorder category on `Fin 4`, the property of having target at
most `2` is stable under composition and absolute base change, but excludes the
identity at `3`. Thus those two closure properties do not imply identity closure.

With structure property `⊤` and common base `3`, the two nonidentity arrows
`0 ⟶ 1` and `0 ⟶ 2` induce `0 ⟶ 1` between the pullbacks with vertices
`0 ⊓ 0 = 0` and `1 ⊓ 2 = 1`. The property holds for both input arrows and the
induced arrow. The two-factor relative preservation theorem applies with
`E = ⊤`, without identity closure. Membership of the induced arrow is also
proved directly from its target bound. This is an identity-closure boundary,
not an example of failure of absolute base-change stability.

## References

* Mathlib, `CategoryTheory.MorphismProperty.OfObjectProperty`, for constructing
  a morphism property from properties of its source and target.
* Mathlib, `CategoryTheory.Category.Preorder` and `CategoryTheory.Limits.Lattice`,
  for the inherited category and its pullback computations.
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty.FourChain

open Limits

/-- Morphisms whose target belongs to the initial segment `{0, 1, 2}` of the
four-object chain. No restriction is imposed on the source. -/
def targetAtMostTwo : MorphismProperty (Fin 4) :=
  ofObjectProperty ⊤ (fun t => t ≤ 2)

namespace targetAtMostTwo

/-- Membership is equivalent to the target being at most `2`. -/
@[simp] theorem mem_iff {x y : Fin 4} (f : x ⟶ y) :
    targetAtMostTwo f ↔ y ≤ 2 := by
  simp [targetAtMostTwo, ofObjectProperty_iff]

instance : targetAtMostTwo.IsStableUnderComposition where
  comp_mem f g _ hg := (mem_iff (f ≫ g)).mpr ((mem_iff g).mp hg)

instance : targetAtMostTwo.IsStableUnderBaseChange where
  of_isPullback {_ _ _ _} {f} {g} {_} {q} _ hg :=
    (mem_iff q).mpr ((leOfHom f).trans ((mem_iff g).mp hg))

/-- The identity of the largest object is excluded. -/
theorem identity_three_not_mem : ¬ targetAtMostTwo (𝟙 (3 : Fin 4)) := by
  rw [mem_iff]
  decide

/-- Composition and absolute base-change stability do not force this property
to contain every identity. -/
theorem not_containsIdentities : ¬ targetAtMostTwo.ContainsIdentities := by
  intro h
  exact identity_three_not_mem (h.id_mem 3)

/-- The first horizontal arrow, from `0` to `1`. -/
def zeroOne : (0 : Fin 4) ⟶ 1 := homOfLE (by decide)

/-- The second horizontal arrow, from `0` to `2`. -/
def zeroTwo : (0 : Fin 4) ⟶ 2 := homOfLE (by decide)

/-- The structure arrow of the second target object over the common base `3`. -/
def twoThree : (2 : Fin 4) ⟶ 3 := homOfLE (by decide)

/-- Both horizontal arrows belong to the property and are nonisomorphisms,
so in particular neither is an identity. -/
theorem horizontal_maps :
    targetAtMostTwo zeroOne ∧ targetAtMostTwo zeroTwo ∧
      ¬ IsIso zeroOne ∧ ¬ IsIso zeroTwo := by
  refine ⟨(mem_iff zeroOne).mpr (by decide), (mem_iff zeroTwo).mpr le_rfl, ?_, ?_⟩
  · rw [PartialOrder.isIso_iff_eq]
    decide
  · rw [PartialOrder.isIso_iff_eq]
    decide

/-- The horizontal arrows commute with their structure arrows to `3`. -/
theorem commuting_squares :
    zeroThree = zeroOne ≫ oneThree ∧ zeroThree = zeroTwo ≫ twoThree := by
  constructor <;> subsingleton

/-- All three structure arrows satisfy the structure property `⊤`. -/
theorem structure_maps_mem_top :
    (⊤ : MorphismProperty (Fin 4)) zeroThree ∧
      (⊤ : MorphismProperty (Fin 4)) oneThree ∧
      (⊤ : MorphismProperty (Fin 4)) twoThree := by
  simp

/-- The two endpoint pullbacks and both mixed spans exist. These are pointwise
witnesses for the two preservation alternatives. -/
theorem pointwise_pullbacks :
    HasPullback zeroThree zeroThree ∧ HasPullback oneThree twoThree ∧
      HasPullback oneThree zeroThree ∧ HasPullback zeroThree twoThree :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The map between the two endpoint pullbacks induced by both horizontal arrows. -/
noncomputable def inducedMap :
    pullback zeroThree zeroThree ⟶ pullback oneThree twoThree :=
  pullback.map zeroThree zeroThree oneThree twoThree zeroOne zeroTwo (𝟙 (3 : Fin 4))
    ((Category.comp_id _).trans commuting_squares.1)
    ((Category.comp_id _).trans commuting_squares.2)

/-- The source pullback is the meet `0 ⊓ 0 = 0`. -/
theorem source_pullback_eq : pullback zeroThree zeroThree = (0 : Fin 4) := by
  rw [CompleteLattice.pullback_eq_inf]
  decide

/-- The target pullback is the meet `1 ⊓ 2 = 1`. -/
theorem target_pullback_eq : pullback oneThree twoThree = (1 : Fin 4) := by
  rw [CompleteLattice.pullback_eq_inf]
  decide

/-- Under the endpoint identifications, the induced arrow is `0 ⟶ 1`. -/
theorem inducedMap_eq_zeroOne :
    eqToHom source_pullback_eq.symm ≫ inducedMap ≫ eqToHom target_pullback_eq = zeroOne := by
  subsingleton

/-- The induced arrow belongs to the property, by its target bound. -/
theorem inducedMap_mem : targetAtMostTwo inducedMap := by
  rw [mem_iff, target_pullback_eq]
  decide

/-- The two-factor relative preservation theorem applies to this induced map
with structure property `⊤`, although `targetAtMostTwo` does not contain all
identities. The object alternative uses the mixed span `1 ⟶ 3 ← 0`. -/
theorem inducedMap_mem_of_relative_alternatives : targetAtMostTwo inducedMap := by
  exact targetAtMostTwo.pullbackMap_of_relative_alternatives ⊤
    horizontal_maps.1 horizontal_maps.2.1 commuting_squares.1 commuting_squares.2
    (Or.inl ⟨structure_maps_mem_top.1, structure_maps_mem_top.2.1,
      pointwise_pullbacks.2.2.1⟩)

/-- The induced map is a nonisomorphism, hence not an identity. -/
theorem inducedMap_not_isIso : ¬ IsIso inducedMap := by
  rw [PartialOrder.isIso_iff_eq, source_pullback_eq, target_pullback_eq]
  decide

end targetAtMostTwo

end CategoryTheory.MorphismProperty.FourChain
