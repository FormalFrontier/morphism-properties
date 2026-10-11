/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MorphismProperties.OverPullback
public import MorphismPropertiesExamples.RelativeBaseChange

/-!
# Structured pullback transport on a four-object chain

The object `1 ⟶ 3` maps to the identity object over `3`. Pullback along
`2 ⟶ 3`, outside the structure property `E`, carries this horizontal map to
`1 ⟶ 2`. Both original and transported endpoints are distinct; the latter
are not isomorphic. The clients use the projection and membership API of the
structured pullback functor without unfolding its construction.
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty.FourChain

open Limits

private instance : (⊤ ⊓ E).IsStableUnderBaseChange := by
  simpa only [top_inf_eq] using (inferInstance : E.IsStableUnderBaseChange)

private def base : (2 : Fin 4) ⟶ 3 := homOfLE (by decide)
private def A : E.Over ⊤ (3 : Fin 4) := Over.mk ⊤ oneThree (by simp)
private def B : E.Over ⊤ (3 : Fin 4) := Over.mk ⊤ (𝟙 _) (by simp)
private def horizontal : A ⟶ B := Over.homMk oneThree (by subsingleton) trivial

/-- The base arrow need not belong to the structure property. -/
example : ¬ E base := by
  rw [e_iff]
  decide

/-- The original structured arrow has distinct endpoints. -/
example : A.left ≠ B.left := by decide

/-- Transport preserves horizontal membership and supplies the stronger
intersection membership on the nonidentity image. -/
example :
    (⊤ ⊓ E) ((Over.pullbackOfIntersectionOfPostcomp E ⊤ base).map horizontal).left :=
  Over.pullbackOfIntersectionOfPostcomp_map_mem_inf E ⊤ base horizontal

/-- The new structure map satisfies `E`. -/
example : E ((Over.pullbackOfIntersectionOfPostcomp E ⊤ base).obj A).hom :=
  Over.pullbackOfIntersectionOfPostcomp_obj_mem E ⊤ base A

/-- The first projection recovers the original horizontal arrow. -/
example :
    ((Over.pullbackOfIntersectionOfPostcomp E ⊤ base).map horizontal).left ≫
        pullback.fst B.hom base = pullback.fst A.hom base ≫ horizontal.left :=
  Over.pullbackOfIntersectionOfPostcomp_map_fst E ⊤ base horizontal

/-- The second projection is unchanged. -/
example :
    ((Over.pullbackOfIntersectionOfPostcomp E ⊤ base).map horizontal).left ≫
        pullback.snd B.hom base = pullback.snd A.hom base :=
  Over.pullbackOfIntersectionOfPostcomp_map_snd E ⊤ base horizontal

private lemma image_endpoints_ne :
    ((Over.pullbackOfIntersectionOfPostcomp E ⊤ base).obj A).left ≠
      ((Over.pullbackOfIntersectionOfPostcomp E ⊤ base).obj B).left := by
  rw [Over.pullbackOfIntersectionOfPostcomp_obj_left,
    Over.pullbackOfIntersectionOfPostcomp_obj_left,
    CompleteLattice.pullback_eq_inf, CompleteLattice.pullback_eq_inf]
  decide

/-- Pullback of the horizontal arrow `1 ⟶ 3` along `2 ⟶ 3` has distinct
endpoints. All object and morphism data are constructed in the structured slice. -/
theorem structured_transport_nonidentity :
    let f : (2 : Fin 4) ⟶ 3 := homOfLE (by decide)
    let X : E.Over ⊤ (3 : Fin 4) := Over.mk ⊤ oneThree (by simp)
    let Y : E.Over ⊤ (3 : Fin 4) := Over.mk ⊤ (𝟙 _) (by simp)
    ((Over.pullbackOfIntersectionOfPostcomp E ⊤ f).obj X).left ≠
      ((Over.pullbackOfIntersectionOfPostcomp E ⊤ f).obj Y).left :=
  image_endpoints_ne

/-- The transported arrow has nonisomorphic endpoints, hence is neither an
identity nor an isomorphism. -/
example : ¬ Nonempty
    ((Over.pullbackOfIntersectionOfPostcomp E ⊤ base).obj A ≅
      (Over.pullbackOfIntersectionOfPostcomp E ⊤ base).obj B) := by
  rintro ⟨i⟩
  exact image_endpoints_ne (le_antisymm (leOfHom i.hom.left) (leOfHom i.inv.left))

/-- The projection equations determine the structured map uniquely. -/
example (k : (Over.pullbackOfIntersectionOfPostcomp E ⊤ base).obj A ⟶
    (Over.pullbackOfIntersectionOfPostcomp E ⊤ base).obj B)
    (hfst : k.left ≫ pullback.fst B.hom base = pullback.fst A.hom base ≫ horizontal.left)
    (hsnd : k.left ≫ pullback.snd B.hom base = pullback.snd A.hom base) :
    k = (Over.pullbackOfIntersectionOfPostcomp E ⊤ base).map horizontal :=
  Over.pullbackOfIntersectionOfPostcomp_map_unique E ⊤ base horizontal k hfst hsnd

/-- The ambient pullback universal property constructs the unique arrow from
`1` with these two projections. -/
example : ∃! k : (1 : Fin 4) ⟶
    ((Over.pullbackOfIntersectionOfPostcomp E ⊤ base).obj A).left,
    k ≫ pullback.fst A.hom base = (𝟙 (1 : Fin 4)) ∧
      k ≫ pullback.snd A.hom base = (homOfLE (by decide) : (1 : Fin 4) ⟶ 2) :=
  Over.pullbackOfIntersectionOfPostcomp_existsUnique_lift E ⊤ base A
    (𝟙 _) (homOfLE (by decide)) (by subsingleton)

/-- At the absolutely stable horizontal boundary, the same nonidentity use
agrees with Mathlib's structured pullback functor. -/
example : Over.pullbackOfIntersectionOfPostcomp E ⊤ base = Over.pullback E ⊤ base :=
  Over.pullbackOfIntersectionOfPostcomp_eq_pullback E ⊤ base

end CategoryTheory.MorphismProperty.FourChain
