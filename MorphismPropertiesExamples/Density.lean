/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MorphismProperties.Density
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Sliced Yoneda over a two-point presheaf

Use the Yoneda embedding of `Discrete PUnit` and constant presheaves of
small types. Mathlib supplies density of this embedding independently of
slicing. The constant projection `Bool × Bool ⟶ Bool` has two distinct
points in each fibre. The empty constant presheaf has no representable
probes, but density under slicing still applies over it.

Presheaves on this singleton discrete category are equivalent to types;
this is the presheaf version of singleton probes over a two-point type,
not a construction of density for `Functor.fromPUnit` into `Type`.

## References

* Mathlib, `CategoryTheory.Functor.KanExtension.Dense`, for density of Yoneda.
* Mathlib's `Functor.const`, `TypeCat.ofHom`, and `Over.mk`, for the
  constant presheaves, projection, and slice object.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CategoryTheory

open Opposite

/-- Yoneda supplies the unsliced density hypothesis without a slicing result. -/
example : (yoneda (C := Discrete PUnit.{1})).IsDense := by
  infer_instance

/-- The two-point base gives a sliced dense functor. -/
example :
    (CostructuredArrow.toOver (yoneda (C := Discrete PUnit.{1}))
      ((Functor.const (Discrete PUnit.{1})ᵒᵖ).obj Bool)).IsDense := by
  infer_instance

/-- Pointwise density applies to the constant first projection over this base. -/
example :
    (CostructuredArrow.toOver (yoneda (C := Discrete PUnit.{1}))
      ((Functor.const (Discrete PUnit.{1})ᵒᵖ).obj Bool)).isDenseAt
        (Over.mk ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map
          (TypeCat.ofHom (_root_.Prod.fst : Bool × Bool → Bool)))) := by
  apply CostructuredArrow.isDenseAt_toOver
  exact Functor.IsDense.isDenseAt _ _

/-- Each fibre of the projection contains two distinct points. -/
example (b : Bool) :
    let p := (Functor.const (Discrete PUnit.{1})ᵒᵖ).map
      (TypeCat.ofHom (_root_.Prod.fst : Bool × Bool → Bool))
    ∃ z₀ z₁ : Bool × Bool,
      p.app (op (Discrete.mk PUnit.unit)) z₀ = b ∧
      p.app (op (Discrete.mk PUnit.unit)) z₁ = b ∧ z₀ ≠ z₁ := by
  refine ⟨(b, false), (b, true), rfl, rfl, ?_⟩
  intro h
  cases congrArg _root_.Prod.snd h

/-- There are no representable probes into the empty constant presheaf. -/
example :
    IsEmpty (CostructuredArrow (yoneda (C := Discrete PUnit.{1}))
      ((Functor.const (Discrete PUnit.{1})ᵒᵖ).obj PEmpty.{1})) := by
  refine ⟨fun Z ↦ ?_⟩
  exact PEmpty.elim (Z.hom.app (op Z.left) (𝟙 Z.left))

/-- The empty base requires no nonemptiness hypothesis. -/
example :
    (CostructuredArrow.toOver (yoneda (C := Discrete PUnit.{1}))
      ((Functor.const (Discrete PUnit.{1})ᵒᵖ).obj PEmpty.{1})).IsDense := by
  infer_instance

end CategoryTheory
