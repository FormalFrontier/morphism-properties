/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MorphismProperties.PullbackPairing
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.FinCases

/-!
# Selected pointwise pullback associativity

Applications of Mathlib's explicit pointwise limit construction to functors into
an ordinary over-category. Only the two inner pullback families and the
left-associated outer family are supplied. The right-associated family is
obtained from the limiting binary fans before assembling the right functor.
The selected binary-fan associator is a natural isomorphism of the assembled
functors. A separate comparison identifies the assembled pair with the
structured pullback pairing, preserving both projections in both directions.

The generic construction helpers in this example are private. No horizontal morphism
property is asserted for projections or for joint lifts.

The finite case has changing domains over a two-element base. Its chosen
left- and right-associated vertices are compared with full equal-bit triples by
projection-preserving isomorphisms. These comparisons are natural in the index;
the whole selected associator and its inverse become the identity natural
isomorphism in the common triple coordinates.

## References

* Mathlib, `CategoryTheory.Limits.Constructions.Over.Products`, for conversion
  between pullback cones and binary fans in an over-category.
* Mathlib, `CategoryTheory.Limits.FunctorCategory.Basic`, for assembling explicit
  pointwise limit cones into a limiting cone of functors.
* Mathlib, `CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan` and
  `CategoryTheory.Limits.HasLimits`, for the selected associator and comparison
  of specified limit cones with chosen limits.
-/

public section

universe v v₁ u u₁

namespace CategoryTheory.Limits

variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u} [Category.{v} C]
variable (S : C)

private noncomputable def pullbackPointFan (X Y : Over S)
    [HasPullback X.hom Y.hom] : BinaryFan X Y :=
  pullbackConeEquivBinaryFan.functor.obj (pullback.cone X.hom Y.hom)

private noncomputable def pullbackPointIsLimit (X Y : Over S)
    [HasPullback X.hom Y.hom] : IsLimit (pullbackPointFan S X Y) :=
  (pullback.isLimit X.hom Y.hom).pullbackConeEquivBinaryFanFunctor

private lemma pullbackPointFan_pt (X Y : Over S) [HasPullback X.hom Y.hom] :
    (pullbackPointFan S X Y).pt =
      Over.mk (pullback.fst X.hom Y.hom ≫ X.hom) := rfl

section Pair

variable (F G : J ⥤ Over S)
variable [hFG : ∀ j, HasPullback (F.obj j).hom (G.obj j).hom]

private noncomputable def pullbackPairPointData (j : J) :
    LimitCone ((pair F G).flip.obj j) where
  cone := (Cone.postcompose (diagramIsoPair ((pair F G).flip.obj j)).inv).obj
    (pullbackPointFan S (F.obj j) (G.obj j))
  isLimit :=
    (IsLimit.postcomposeInvEquiv (diagramIsoPair ((pair F G).flip.obj j))
      (pullbackPointFan S (F.obj j) (G.obj j))).symm
        (pullbackPointIsLimit S (F.obj j) (G.obj j))

private noncomputable def pullbackPairData : LimitCone (pair F G) where
  cone := combineCones (pair F G) (pullbackPairPointData S F G)
  isLimit := combinedIsLimit (pair F G) (pullbackPairPointData S F G)

private lemma pullbackPairData_obj (j : J) :
    (pullbackPairData S F G).cone.pt.obj j =
      Over.mk (pullback.fst (F.obj j).hom (G.obj j).hom ≫ (F.obj j).hom) := rfl

private lemma pullbackPairData_fst_app (j : J) :
    (BinaryFan.fst ((pullbackPairData S F G).cone)).app j =
      (pullbackPointFan S (F.obj j) (G.obj j)).fst := by
  change (pullbackPointFan S (F.obj j) (G.obj j)).fst ≫ 𝟙 _ = _
  exact Category.comp_id _

private lemma pullbackPairData_snd_app (j : J) :
    (BinaryFan.snd ((pullbackPairData S F G).cone)).app j =
      (pullbackPointFan S (F.obj j) (G.obj j)).snd := by
  change (pullbackPointFan S (F.obj j) (G.obj j)).snd ≫ 𝟙 _ = _
  exact Category.comp_id _

private lemma pullbackPairData_fst_app_left (j : J) :
    ((BinaryFan.fst ((pullbackPairData S F G).cone)).app j).left =
      pullback.fst (F.obj j).hom (G.obj j).hom := by
  rw [pullbackPairData_fst_app]
  rfl

private lemma pullbackPairData_snd_app_left (j : J) :
    ((BinaryFan.snd ((pullbackPairData S F G).cone)).app j).left =
      pullback.snd (F.obj j).hom (G.obj j).hom := by
  rw [pullbackPairData_snd_app]
  rfl

-- Existence is obtained from the specified cone, but the chosen point is
-- compared by an isomorphism rather than identified by a definitional equation.
private noncomputable def pullbackPairChosenIso :
    @limit _ _ _ _ (pair F G) (HasLimit.mk (pullbackPairData S F G)) ≅
      (pullbackPairData S F G).cone.pt := by
  letI : HasLimit (pair F G) := HasLimit.mk (pullbackPairData S F G)
  exact limit.isoLimitCone (pullbackPairData S F G)

private noncomputable def pullbackPairChosenPointIso (j : J) :
    (@limit _ _ _ _ (pair F G) (HasLimit.mk (pullbackPairData S F G))).obj j ≅
      Over.mk (pullback.fst (F.obj j).hom (G.obj j).hom ≫ (F.obj j).hom) :=
  (pullbackPairChosenIso S F G).app j

private lemma pullbackPairChosenIso_hom_fst :
    (pullbackPairChosenIso S F G).hom ≫ (BinaryFan.fst ((pullbackPairData S F G).cone)) =
      @limit.π _ _ _ _ (pair F G) (HasLimit.mk (pullbackPairData S F G))
        ⟨WalkingPair.left⟩ := by
  let : HasLimit (pair F G) := HasLimit.mk (pullbackPairData S F G)
  exact limit.isoLimitCone_hom_π (pullbackPairData S F G) ⟨WalkingPair.left⟩

private lemma pullbackPairChosenIso_hom_snd :
    (pullbackPairChosenIso S F G).hom ≫ (BinaryFan.snd ((pullbackPairData S F G).cone)) =
      @limit.π _ _ _ _ (pair F G) (HasLimit.mk (pullbackPairData S F G))
        ⟨WalkingPair.right⟩ := by
  let : HasLimit (pair F G) := HasLimit.mk (pullbackPairData S F G)
  exact limit.isoLimitCone_hom_π (pullbackPairData S F G) ⟨WalkingPair.right⟩

private lemma pullbackPairChosenIso_inv_fst :
    (pullbackPairChosenIso S F G).inv ≫
        @limit.π _ _ _ _ (pair F G) (HasLimit.mk (pullbackPairData S F G))
          ⟨WalkingPair.left⟩ =
      (BinaryFan.fst ((pullbackPairData S F G).cone)) := by
  let : HasLimit (pair F G) := HasLimit.mk (pullbackPairData S F G)
  exact limit.isoLimitCone_inv_π (pullbackPairData S F G) ⟨WalkingPair.left⟩

private lemma pullbackPairChosenIso_inv_snd :
    (pullbackPairChosenIso S F G).inv ≫
        @limit.π _ _ _ _ (pair F G) (HasLimit.mk (pullbackPairData S F G))
          ⟨WalkingPair.right⟩ =
      (BinaryFan.snd ((pullbackPairData S F G).cone)) := by
  let : HasLimit (pair F G) := HasLimit.mk (pullbackPairData S F G)
  exact limit.isoLimitCone_inv_π (pullbackPairData S F G) ⟨WalkingPair.right⟩

end Pair

section Triple

variable (F G H : J ⥤ Over S)
variable [hFG : ∀ j, HasPullback (F.obj j).hom (G.obj j).hom]
variable [hGH : ∀ j, HasPullback (G.obj j).hom (H.obj j).hom]
variable [hL : ∀ j, HasPullback
  (pullback.fst (F.obj j).hom (G.obj j).hom ≫ (F.obj j).hom) (H.obj j).hom]

private noncomputable def leftTripleData :
    LimitCone (pair (pullbackPairData S F G).cone.pt H) := by
  letI : ∀ j, HasPullback ((pullbackPairData S F G).cone.pt.obj j).hom (H.obj j).hom :=
    fun j ↦ hL j
  exact pullbackPairData S (pullbackPairData S F G).cone.pt H

omit hGH in
private lemma leftTripleData_obj (j : J) :
    (leftTripleData S F G H).cone.pt.obj j =
      Over.mk (pullback.fst
        (pullback.fst (F.obj j).hom (G.obj j).hom ≫ (F.obj j).hom) (H.obj j).hom ≫
          (pullback.fst (F.obj j).hom (G.obj j).hom ≫ (F.obj j).hom)) := rfl

-- This derivation is pointwise. It uses no preservation instance for evaluation
-- of a right-associated functor limit.
private lemma rightPullbackFamily : ∀ j, HasPullback (F.obj j).hom
    (pullback.fst (G.obj j).hom (H.obj j).hom ≫ (G.obj j).hom) := by
  intro j
  let bFG := pullbackPointFan S (F.obj j) (G.obj j)
  let bGH := pullbackPointFan S (G.obj j) (H.obj j)
  let : HasPullback bFG.pt.hom (H.obj j).hom := hL j
  let bL := pullbackPointFan S bFG.pt (H.obj j)
  let pFG : IsLimit bFG := pullbackPointIsLimit S (F.obj j) (G.obj j)
  let pGH : IsLimit bGH := pullbackPointIsLimit S (G.obj j) (H.obj j)
  let pL : IsLimit bL := pullbackPointIsLimit S bFG.pt (H.obj j)
  exact (Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.assoc (sXY := bFG) pGH bL) (pFG.assoc pGH pL)).hasPullback

private noncomputable def rightTripleData :
    LimitCone (pair F (pullbackPairData S G H).cone.pt) := by
  letI : ∀ j, HasPullback (F.obj j).hom ((pullbackPairData S G H).cone.pt.obj j).hom :=
    rightPullbackFamily S F G H
  exact pullbackPairData S F (pullbackPairData S G H).cone.pt

private lemma rightTripleData_obj (j : J) :
    (rightTripleData S F G H).cone.pt.obj j =
      Over.mk (@pullback.fst C _ (F.obj j).left
        (pullback (G.obj j).hom (H.obj j).hom) S (F.obj j).hom
        (pullback.fst (G.obj j).hom (H.obj j).hom ≫ (G.obj j).hom)
        (rightPullbackFamily S F G H j) ≫ (F.obj j).hom) := rfl

private noncomputable def pullbackAssociator :
    (leftTripleData S F G H).cone.pt ≅ (rightTripleData S F G H).cone.pt :=
  BinaryFan.associator (pullbackPairData S F G).isLimit
    (pullbackPairData S G H).isLimit (leftTripleData S F G H).isLimit
      (rightTripleData S F G H).isLimit

private lemma pullbackAssociator_hom_coordinates :
    ((pullbackAssociator S F G H).hom ≫ (BinaryFan.fst ((rightTripleData S F G H).cone)) =
      (BinaryFan.fst ((leftTripleData S F G H).cone)) ≫
        (BinaryFan.fst ((pullbackPairData S F G).cone))) ∧
    ((pullbackAssociator S F G H).hom ≫ (BinaryFan.snd ((rightTripleData S F G H).cone)) ≫
        (BinaryFan.fst ((pullbackPairData S G H).cone)) =
      (BinaryFan.fst ((leftTripleData S F G H).cone)) ≫
        (BinaryFan.snd ((pullbackPairData S F G).cone))) ∧
    ((pullbackAssociator S F G H).hom ≫ (BinaryFan.snd ((rightTripleData S F G H).cone)) ≫
        (BinaryFan.snd ((pullbackPairData S G H).cone)) =
      (BinaryFan.snd ((leftTripleData S F G H).cone))) := by
  let fg := pullbackPairData S F G
  let gh := pullbackPairData S G H
  let l := leftTripleData S F G H
  let r := rightTripleData S F G H
  let yz : l.cone.pt ⟶ gh.cone.pt :=
    BinaryFan.IsLimit.lift gh.isLimit (BinaryFan.fst l.cone ≫ BinaryFan.snd fg.cone)
      (BinaryFan.snd l.cone)
  have hf : (pullbackAssociator S F G H).hom ≫ BinaryFan.fst r.cone =
      BinaryFan.fst l.cone ≫ BinaryFan.fst fg.cone :=
    (fg.isLimit.assoc gh.isLimit l.isLimit).conePointUniqueUpToIso_hom_comp
      r.isLimit ⟨WalkingPair.left⟩
  have hs : (pullbackAssociator S F G H).hom ≫ BinaryFan.snd r.cone = yz :=
    (fg.isLimit.assoc gh.isLimit l.isLimit).conePointUniqueUpToIso_hom_comp
      r.isLimit ⟨WalkingPair.right⟩
  have hg : yz ≫ BinaryFan.fst gh.cone =
      BinaryFan.fst l.cone ≫ BinaryFan.snd fg.cone :=
    BinaryFan.IsLimit.lift_fst gh.isLimit _ _
  have hh : yz ≫ BinaryFan.snd gh.cone = BinaryFan.snd l.cone :=
    BinaryFan.IsLimit.lift_snd gh.isLimit _ _
  refine ⟨hf, ?_, ?_⟩
  · exact (Category.assoc (pullbackAssociator S F G H).hom
      (BinaryFan.snd r.cone) (BinaryFan.fst gh.cone)).symm.trans
      ((congrArg (fun k : l.cone.pt ⟶ gh.cone.pt ↦ k ≫ BinaryFan.fst gh.cone) hs).trans hg)
  · exact (Category.assoc (pullbackAssociator S F G H).hom
      (BinaryFan.snd r.cone) (BinaryFan.snd gh.cone)).symm.trans
      ((congrArg (fun k : l.cone.pt ⟶ gh.cone.pt ↦ k ≫ BinaryFan.snd gh.cone) hs).trans hh)

private lemma pullbackAssociator_inv_coordinates :
    ((pullbackAssociator S F G H).inv ≫ (BinaryFan.fst ((leftTripleData S F G H).cone)) ≫
        (BinaryFan.fst ((pullbackPairData S F G).cone)) =
      (BinaryFan.fst ((rightTripleData S F G H).cone))) ∧
    ((pullbackAssociator S F G H).inv ≫ (BinaryFan.fst ((leftTripleData S F G H).cone)) ≫
        (BinaryFan.snd ((pullbackPairData S F G).cone)) =
      (BinaryFan.snd ((rightTripleData S F G H).cone)) ≫
        (BinaryFan.fst ((pullbackPairData S G H).cone))) ∧
    ((pullbackAssociator S F G H).inv ≫ (BinaryFan.snd ((leftTripleData S F G H).cone)) =
      (BinaryFan.snd ((rightTripleData S F G H).cone)) ≫
        (BinaryFan.snd ((pullbackPairData S G H).cone))) := by
  let fg := pullbackPairData S F G
  let gh := pullbackPairData S G H
  let l := leftTripleData S F G H
  let r := rightTripleData S F G H
  let yz : l.cone.pt ⟶ gh.cone.pt :=
    BinaryFan.IsLimit.lift gh.isLimit (BinaryFan.fst l.cone ≫ BinaryFan.snd fg.cone)
      (BinaryFan.snd l.cone)
  have hf : (pullbackAssociator S F G H).inv ≫
      BinaryFan.fst l.cone ≫ BinaryFan.fst fg.cone = BinaryFan.fst r.cone :=
    (fg.isLimit.assoc gh.isLimit l.isLimit).conePointUniqueUpToIso_inv_comp
      r.isLimit ⟨WalkingPair.left⟩
  have hs : (pullbackAssociator S F G H).inv ≫ yz = BinaryFan.snd r.cone :=
    (fg.isLimit.assoc gh.isLimit l.isLimit).conePointUniqueUpToIso_inv_comp
      r.isLimit ⟨WalkingPair.right⟩
  have hg : yz ≫ BinaryFan.fst gh.cone =
      BinaryFan.fst l.cone ≫ BinaryFan.snd fg.cone :=
    BinaryFan.IsLimit.lift_fst gh.isLimit _ _
  have hh : yz ≫ BinaryFan.snd gh.cone = BinaryFan.snd l.cone :=
    BinaryFan.IsLimit.lift_snd gh.isLimit _ _
  refine ⟨hf, ?_, ?_⟩
  · exact (congrArg
      (fun k : l.cone.pt ⟶ G ↦ (pullbackAssociator S F G H).inv ≫ k) hg).symm.trans
      ((Category.assoc (pullbackAssociator S F G H).inv yz (BinaryFan.fst gh.cone)).symm.trans
        (congrArg (fun k : r.cone.pt ⟶ gh.cone.pt ↦ k ≫ BinaryFan.fst gh.cone) hs))
  · exact (congrArg
      (fun k : l.cone.pt ⟶ H ↦ (pullbackAssociator S F G H).inv ≫ k) hh).symm.trans
      ((Category.assoc (pullbackAssociator S F G H).inv yz (BinaryFan.snd gh.cone)).symm.trans
        (congrArg (fun k : r.cone.pt ⟶ gh.cone.pt ↦ k ≫ BinaryFan.snd gh.cone) hs))

private lemma pullbackAssociator_hom_naturality {j j' : J} (f : j ⟶ j') :
    (leftTripleData S F G H).cone.pt.map f ≫ (pullbackAssociator S F G H).hom.app j' =
      (pullbackAssociator S F G H).hom.app j ≫ (rightTripleData S F G H).cone.pt.map f :=
  (pullbackAssociator S F G H).hom.naturality f

private lemma pullbackAssociator_inv_naturality {j j' : J} (f : j ⟶ j') :
    (rightTripleData S F G H).cone.pt.map f ≫ (pullbackAssociator S F G H).inv.app j' =
      (pullbackAssociator S F G H).inv.app j ≫ (leftTripleData S F G H).cone.pt.map f :=
  (pullbackAssociator S F G H).inv.naturality f

end Triple

section StructuredPair

variable (E Q P : MorphismProperty C) [P.IsMultiplicative]
variable [h : ∀ A : E.Over P S, ∀ B : Q.Over P S, HasPullback A.hom B.hom]

private lemma structuredPairFamily :
    ∀ j : E.Over P S × Q.Over P S,
      HasPullback
        ((Prod.fst (E.Over P S) (Q.Over P S) ⋙
          MorphismProperty.Over.forget E P S).obj j).hom
        ((Prod.snd (E.Over P S) (Q.Over P S) ⋙
          MorphismProperty.Over.forget Q P S).obj j).hom := by
  intro j
  change HasPullback j.1.hom j.2.hom
  exact h j.1 j.2

private noncomputable def structuredPairData :
    LimitCone (pair
      (Prod.fst (E.Over P S) (Q.Over P S) ⋙ MorphismProperty.Over.forget E P S)
      (Prod.snd (E.Over P S) (Q.Over P S) ⋙ MorphismProperty.Over.forget Q P S)) := by
  letI := structuredPairFamily S E Q P
  exact pullbackPairData S _ _

private lemma structuredPairData_obj (A : E.Over P S) (B : Q.Over P S) :
    (structuredPairData S E Q P).cone.pt.obj (A, B) =
      Over.mk (pullback.fst A.hom B.hom ≫ A.hom) := by
  let := structuredPairFamily S E Q P
  exact pullbackPairData_obj S _ _ (A, B)

private lemma structuredPairData_obj_left (A : E.Over P S) (B : Q.Over P S) :
    ((structuredPairData S E Q P).cone.pt.obj (A, B)).left = pullback A.hom B.hom :=
  congrArg Over.left (structuredPairData_obj S E Q P A B)

private noncomputable def structuredPairIso :
    (structuredPairData S E Q P).cone.pt ≅ MorphismProperty.Over.pullbackPairing E Q P S :=
  (structuredPairData S E Q P).isLimit.conePointUniqueUpToIso
    (MorphismProperty.Over.pullbackPairingFan_isLimit E Q P S)

private lemma structuredPairIso_hom_fst :
    (structuredPairIso S E Q P).hom ≫ MorphismProperty.Over.pullbackPairingFst E Q P S =
      (BinaryFan.fst ((structuredPairData S E Q P).cone)) :=
  (structuredPairData S E Q P).isLimit.conePointUniqueUpToIso_hom_comp
    (MorphismProperty.Over.pullbackPairingFan_isLimit E Q P S) ⟨WalkingPair.left⟩

private lemma structuredPairIso_hom_snd :
    (structuredPairIso S E Q P).hom ≫ MorphismProperty.Over.pullbackPairingSnd E Q P S =
      (BinaryFan.snd ((structuredPairData S E Q P).cone)) :=
  (structuredPairData S E Q P).isLimit.conePointUniqueUpToIso_hom_comp
    (MorphismProperty.Over.pullbackPairingFan_isLimit E Q P S) ⟨WalkingPair.right⟩

private lemma structuredPairIso_inv_fst :
    (structuredPairIso S E Q P).inv ≫ (BinaryFan.fst ((structuredPairData S E Q P).cone)) =
      MorphismProperty.Over.pullbackPairingFst E Q P S :=
  (structuredPairData S E Q P).isLimit.conePointUniqueUpToIso_inv_comp
    (MorphismProperty.Over.pullbackPairingFan_isLimit E Q P S) ⟨WalkingPair.left⟩

private lemma structuredPairIso_inv_snd :
    (structuredPairIso S E Q P).inv ≫ (BinaryFan.snd ((structuredPairData S E Q P).cone)) =
      MorphismProperty.Over.pullbackPairingSnd E Q P S :=
  (structuredPairData S E Q P).isLimit.conePointUniqueUpToIso_inv_comp
    (MorphismProperty.Over.pullbackPairingFan_isLimit E Q P S) ⟨WalkingPair.right⟩

private lemma structuredPairData_fst_app_left (A : E.Over P S) (B : Q.Over P S) :
    ((BinaryFan.fst ((structuredPairData S E Q P).cone)).app (A, B)).left =
      pullback.fst A.hom B.hom := by
  let := structuredPairFamily S E Q P
  exact pullbackPairData_fst_app_left S _ _ (A, B)

private lemma structuredPairData_snd_app_left (A : E.Over P S) (B : Q.Over P S) :
    ((BinaryFan.snd ((structuredPairData S E Q P).cone)).app (A, B)).left =
      pullback.snd A.hom B.hom := by
  let := structuredPairFamily S E Q P
  exact pullbackPairData_snd_app_left S _ _ (A, B)

-- The comparison is identity transport along the object equations. Its projection
-- equations are compared as morphisms with these transported endpoints.
private lemma structuredPairIso_hom_app_left (A : E.Over P S) (B : Q.Over P S) :
    ((structuredPairIso S E Q P).hom.app (A, B)).left =
      eqToHom ((structuredPairData_obj_left S E Q P A B).trans
        (MorphismProperty.Over.pullbackPairing_obj_left E Q P S A B).symm) := by
  let := structuredPairFamily S E Q P
  let e := (structuredPairData_obj_left S E Q P A B).trans
    (MorphismProperty.Over.pullbackPairing_obj_left E Q P S A B).symm
  apply pullback.hom_ext (f := A.hom) (g := B.hom)
  · have hf : ((structuredPairIso S E Q P).hom.app (A, B)).left ≫
        ((MorphismProperty.Over.pullbackPairingFst E Q P S).app (A, B)).left =
        ((BinaryFan.fst (structuredPairData S E Q P).cone).app (A, B)).left := by
      simpa only [NatTrans.comp_app, Over.comp_left] using congrArg Over.Hom.left
        (congr_app (structuredPairIso_hom_fst S E Q P) (A, B))
    have hproj := (congrArg
      (fun k : ((MorphismProperty.Over.pullbackPairing E Q P S).obj (A, B)).left ⟶ A.left ↦
        ((structuredPairIso S E Q P).hom.app (A, B)).left ≫ k)
      (MorphismProperty.Over.pullbackPairingFst_app_left E Q P S A B)).symm.trans hf
    have htransport : eqToHom e ≫ pullback.fst A.hom B.hom =
        ((BinaryFan.fst (structuredPairData S E Q P).cone).app (A, B)).left :=
      eq_of_heq ((eqToHom_comp_heq (pullback.fst A.hom B.hom) e).trans
        (heq_of_eq (structuredPairData_fst_app_left S E Q P A B)).symm)
    exact hproj.trans htransport.symm
  · have hs : ((structuredPairIso S E Q P).hom.app (A, B)).left ≫
        ((MorphismProperty.Over.pullbackPairingSnd E Q P S).app (A, B)).left =
        ((BinaryFan.snd (structuredPairData S E Q P).cone).app (A, B)).left := by
      simpa only [NatTrans.comp_app, Over.comp_left] using congrArg Over.Hom.left
        (congr_app (structuredPairIso_hom_snd S E Q P) (A, B))
    have hproj := (congrArg
      (fun k : ((MorphismProperty.Over.pullbackPairing E Q P S).obj (A, B)).left ⟶ B.left ↦
        ((structuredPairIso S E Q P).hom.app (A, B)).left ≫ k)
      (MorphismProperty.Over.pullbackPairingSnd_app_left E Q P S A B)).symm.trans hs
    have htransport : eqToHom e ≫ pullback.snd A.hom B.hom =
        ((BinaryFan.snd (structuredPairData S E Q P).cone).app (A, B)).left :=
      eq_of_heq ((eqToHom_comp_heq (pullback.snd A.hom B.hom) e).trans
        (heq_of_eq (structuredPairData_snd_app_left S E Q P A B)).symm)
    exact hproj.trans htransport.symm

private lemma structuredPairIso_inv_app_left (A : E.Over P S) (B : Q.Over P S) :
    ((structuredPairIso S E Q P).inv.app (A, B)).left =
      eqToHom ((MorphismProperty.Over.pullbackPairing_obj_left E Q P S A B).trans
        (structuredPairData_obj_left S E Q P A B).symm) := by
  let := structuredPairFamily S E Q P
  let e := (MorphismProperty.Over.pullbackPairing_obj_left E Q P S A B).trans
    (structuredPairData_obj_left S E Q P A B).symm
  have hforward : ((structuredPairIso S E Q P).hom.app (A, B)).left = eqToHom e.symm :=
    structuredPairIso_hom_app_left S E Q P A B
  have hi : eqToHom e.symm ≫ ((structuredPairIso S E Q P).inv.app (A, B)).left =
      𝟙 ((structuredPairData S E Q P).cone.pt.obj (A, B)).left :=
    (congrArg
      (fun k : ((structuredPairData S E Q P).cone.pt.obj (A, B)).left ⟶
          ((MorphismProperty.Over.pullbackPairing E Q P S).obj (A, B)).left ↦
        k ≫ ((structuredPairIso S E Q P).inv.app (A, B)).left) hforward).symm.trans
      (Over.hom_left_inv_left ((structuredPairIso S E Q P).app (A, B)))
  have hinv : ((structuredPairIso S E Q P).inv.app (A, B)).left = eqToHom e ≫ 𝟙 _ :=
    (eqToHom_comp_iff e.symm _ _).1 hi
  exact hinv.trans (Category.comp_id _)

end StructuredPair

end CategoryTheory.Limits

/-!
# Finite diagrams of ordinary over objects

Three diagrams indexed by the preorder `Fin 2` have changing finite domains over
`(Fin 2 : Type)`. Their transition functions are two proper injections and
one surjection which is not a monomorphism. Equal-bit pairs and nested pairs
supply explicit coordinate pullback cones. The triple transition has fourteen
source points and eighteen target points, and is neither injective nor surjective.
A natural involution exchanges the first two points of the first diagram.

The coordinate objects are subtypes, not identifications of chosen categorical
pullbacks with subtypes. The two flattening equivalences below only describe
coordinates of nested pairs; they do not define a categorical associator.

## References

* Mathlib, `CategoryTheory.Category.Preorder`, for the category of a preorder.
* Mathlib, `CategoryTheory.Comma.Over.Basic` and `CategoryTheory.NatIso`, for
  ordinary over objects and natural isomorphisms.
* Mathlib, `CategoryTheory.Limits.Types.Pullbacks`, for explicit pullback cones
  and their universal properties.
* Mathlib, `Logic.Equiv.Basic` and `SetTheory.Cardinal.Finite`, for coordinate
  equivalences and cardinality transport along isomorphisms.
-/

namespace CategoryTheory
namespace FiniteDiagram

open Limits

private abbrev S : Type := Fin 2

private def α : (0 : Fin 2) ⟶ 1 := homOfLE (by decide)

private def fBaseZero : Fin 3 → Fin 2 := ![0, 0, 1]
private def fBaseOne : Fin 4 → Fin 2 := ![0, 0, 1, 1]
private def gBaseZero : Fin 4 → Fin 2 := ![0, 0, 1, 1]
private def gBaseOne : Fin 5 → Fin 2 := ![0, 0, 0, 1, 1]
private def hBaseZero : Fin 5 → Fin 2 := ![0, 0, 1, 1, 1]
private def hBaseOne : Fin 4 → Fin 2 := ![0, 1, 1, 1]

private def fStep : Fin 3 → Fin 4 := ![0, 1, 2]
private def gStep : Fin 4 → Fin 5 := ![0, 2, 3, 4]
private def hStep : Fin 5 → Fin 4 := ![0, 0, 1, 2, 3]

private lemma fStep_base (x : Fin 3) : fBaseOne (fStep x) = fBaseZero x := by
  fin_cases x <;> rfl

private lemma gStep_base (y : Fin 4) : gBaseOne (gStep y) = gBaseZero y := by
  fin_cases y <;> rfl

private lemma hStep_base (z : Fin 5) : hBaseOne (hStep z) = hBaseZero z := by
  fin_cases z <;> rfl

private abbrev fZero : Over S :=
  Over.mk (TypeCat.ofHom fBaseZero : (Fin 3 : Type) ⟶ S)
private abbrev fOne : Over S :=
  Over.mk (TypeCat.ofHom fBaseOne : (Fin 4 : Type) ⟶ S)
private abbrev gZero : Over S :=
  Over.mk (TypeCat.ofHom gBaseZero : (Fin 4 : Type) ⟶ S)
private abbrev gOne : Over S :=
  Over.mk (TypeCat.ofHom gBaseOne : (Fin 5 : Type) ⟶ S)
private abbrev hZero : Over S :=
  Over.mk (TypeCat.ofHom hBaseZero : (Fin 5 : Type) ⟶ S)
private abbrev hOne : Over S :=
  Over.mk (TypeCat.ofHom hBaseOne : (Fin 4 : Type) ⟶ S)

private noncomputable def fArrow : fZero ⟶ fOne :=
  Over.homMk (TypeCat.ofHom fStep) (by
    apply ConcreteCategory.hom_ext
    exact fStep_base)

private noncomputable def gArrow : gZero ⟶ gOne :=
  Over.homMk (TypeCat.ofHom gStep) (by
    apply ConcreteCategory.hom_ext
    exact gStep_base)

private noncomputable def hArrow : hZero ⟶ hOne :=
  Over.homMk (TypeCat.ofHom hStep) (by
    apply ConcreteCategory.hom_ext
    exact hStep_base)

private abbrev fObject (j : Fin 2) : Over S := Fin.cases fZero (fun _ => fOne) j
private abbrev gObject (j : Fin 2) : Over S := Fin.cases gZero (fun _ => gOne) j
private abbrev hObject (j : Fin 2) : Over S := Fin.cases hZero (fun _ => hOne) j

-- Recursion on the finite indices constructs data; lifted inequalities rule out the reverse case.
private noncomputable def fMap {i j : Fin 2} (u : i ⟶ j) : fObject i ⟶ fObject j := by
  revert u
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · intro _; exact 𝟙 _
    · intro _; exact fArrow
  · refine Fin.cases ?_ (fun j' => ?_) j
    · intro u
      exact False.elim (Nat.not_succ_le_zero _ (leOfHom u))
    · intro _; exact 𝟙 _

private noncomputable def gMap {i j : Fin 2} (u : i ⟶ j) : gObject i ⟶ gObject j := by
  revert u
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · intro _; exact 𝟙 _
    · intro _; exact gArrow
  · refine Fin.cases ?_ (fun j' => ?_) j
    · intro u
      exact False.elim (Nat.not_succ_le_zero _ (leOfHom u))
    · intro _; exact 𝟙 _

private noncomputable def hMap {i j : Fin 2} (u : i ⟶ j) : hObject i ⟶ hObject j := by
  revert u
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · intro _; exact 𝟙 _
    · intro _; exact hArrow
  · refine Fin.cases ?_ (fun j' => ?_) j
    · intro u
      exact False.elim (Nat.not_succ_le_zero _ (leOfHom u))
    · intro _; exact 𝟙 _

-- Uniqueness of morphisms in the indexing preorder reduces the map to its endpoint cases.
private lemma fMap_self {i : Fin 2} (u : i ⟶ i) : fMap u = 𝟙 (fObject i) := by
  have hu : u = 𝟙 i := Subsingleton.elim _ _
  subst u
  fin_cases i <;> rfl

private lemma gMap_self {i : Fin 2} (u : i ⟶ i) : gMap u = 𝟙 (gObject i) := by
  have hu : u = 𝟙 i := Subsingleton.elim _ _
  subst u
  fin_cases i <;> rfl

private lemma hMap_self {i : Fin 2} (u : i ⟶ i) : hMap u = 𝟙 (hObject i) := by
  have hu : u = 𝟙 i := Subsingleton.elim _ _
  subst u
  fin_cases i <;> rfl

private lemma fMap_zero_one (u : (0 : Fin 2) ⟶ 1) : fMap u = fArrow := by
  have hu : u = α := Subsingleton.elim _ _
  subst u
  rfl

private lemma gMap_zero_one (u : (0 : Fin 2) ⟶ 1) : gMap u = gArrow := by
  have hu : u = α := Subsingleton.elim _ _
  subst u
  rfl

private lemma hMap_zero_one (u : (0 : Fin 2) ⟶ 1) : hMap u = hArrow := by
  have hu : u = α := Subsingleton.elim _ _
  subst u
  rfl

private lemma fMap_comp {i j k : Fin 2} (u : i ⟶ j) (v : j ⟶ k) :
    fMap (u ≫ v) = fMap u ≫ fMap v := by
  have hij := leOfHom u
  have hjk := leOfHom v
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hij)
    | exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hjk)
    | (simp only [fMap_self, fMap_zero_one];
        first
        | exact (Category.id_comp (𝟙 fZero)).symm
        | exact (Category.id_comp fArrow).symm
        | exact (Category.comp_id fArrow).symm
        | exact (Category.id_comp (𝟙 fOne)).symm)

private lemma gMap_comp {i j k : Fin 2} (u : i ⟶ j) (v : j ⟶ k) :
    gMap (u ≫ v) = gMap u ≫ gMap v := by
  have hij := leOfHom u
  have hjk := leOfHom v
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hij)
    | exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hjk)
    | (simp only [gMap_self, gMap_zero_one];
        first
        | exact (Category.id_comp (𝟙 gZero)).symm
        | exact (Category.id_comp gArrow).symm
        | exact (Category.comp_id gArrow).symm
        | exact (Category.id_comp (𝟙 gOne)).symm)

private lemma hMap_comp {i j k : Fin 2} (u : i ⟶ j) (v : j ⟶ k) :
    hMap (u ≫ v) = hMap u ≫ hMap v := by
  have hij := leOfHom u
  have hjk := leOfHom v
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hij)
    | exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hjk)
    | (simp only [hMap_self, hMap_zero_one];
        first
        | exact (Category.id_comp (𝟙 hZero)).symm
        | exact (Category.id_comp hArrow).symm
        | exact (Category.comp_id hArrow).symm
        | exact (Category.id_comp (𝟙 hOne)).symm)

/-- The diagram with domains `Fin 3` and `Fin 4` over the two-element base. -/
@[expose]
noncomputable def F : Fin 2 ⥤ Over (Fin 2 : Type) where
  obj := Fin.cases
    (Over.mk (TypeCat.ofHom (![0, 0, 1] : Fin 3 → Fin 2)))
    (fun _ => Over.mk (TypeCat.ofHom (![0, 0, 1, 1] : Fin 4 → Fin 2)))
  map {i j} u := by
    revert u
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro _; exact 𝟙 _
      · intro _
        exact Over.homMk (TypeCat.ofHom (![0, 1, 2] : Fin 3 → Fin 4)) (by
          apply ConcreteCategory.hom_ext
          exact fStep_base)
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro u
        exact False.elim (Nat.not_succ_le_zero _ (leOfHom u))
      · intro _; exact 𝟙 _
  map_id j := by
    change fMap (𝟙 j) = 𝟙 (fObject j)
    exact fMap_self (𝟙 j)
  map_comp {i j k} u v := by
    change fMap (u ≫ v) = fMap u ≫ fMap v
    exact fMap_comp u v

/-- The diagram with domains `Fin 4` and `Fin 5` over the two-element base. -/
@[expose]
noncomputable def G : Fin 2 ⥤ Over (Fin 2 : Type) where
  obj := Fin.cases
    (Over.mk (TypeCat.ofHom (![0, 0, 1, 1] : Fin 4 → Fin 2)))
    (fun _ => Over.mk (TypeCat.ofHom (![0, 0, 0, 1, 1] : Fin 5 → Fin 2)))
  map {i j} u := by
    revert u
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro _; exact 𝟙 _
      · intro _
        exact Over.homMk (TypeCat.ofHom (![0, 2, 3, 4] : Fin 4 → Fin 5)) (by
          apply ConcreteCategory.hom_ext
          exact gStep_base)
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro u
        exact False.elim (Nat.not_succ_le_zero _ (leOfHom u))
      · intro _; exact 𝟙 _
  map_id j := by
    change gMap (𝟙 j) = 𝟙 (gObject j)
    exact gMap_self (𝟙 j)
  map_comp {i j k} u v := by
    change gMap (u ≫ v) = gMap u ≫ gMap v
    exact gMap_comp u v

/-- The diagram whose transition identifies two points over zero. -/
@[expose]
noncomputable def H : Fin 2 ⥤ Over (Fin 2 : Type) where
  obj := Fin.cases
    (Over.mk (TypeCat.ofHom (![0, 0, 1, 1, 1] : Fin 5 → Fin 2)))
    (fun _ => Over.mk (TypeCat.ofHom (![0, 1, 1, 1] : Fin 4 → Fin 2)))
  map {i j} u := by
    revert u
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro _; exact 𝟙 _
      · intro _
        exact Over.homMk (TypeCat.ofHom (![0, 0, 1, 2, 3] : Fin 5 → Fin 4)) (by
          apply ConcreteCategory.hom_ext
          exact hStep_base)
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro u
        exact False.elim (Nat.not_succ_le_zero _ (leOfHom u))
      · intro _; exact 𝟙 _
  map_id j := by
    change hMap (𝟙 j) = 𝟙 (hObject j)
    exact hMap_self (𝟙 j)
  map_comp {i j k} u v := by
    change hMap (u ≫ v) = hMap u ≫ hMap v
    exact hMap_comp u v

/-- The source object of `F`, including its structure map. -/
@[simp] theorem F_obj_zero :
    F.obj 0 = Over.mk (TypeCat.ofHom (![0, 0, 1] : Fin 3 → Fin 2)) := rfl

/-- The target object of `F`, including its structure map. -/
@[simp] theorem F_obj_one :
    F.obj 1 = Over.mk (TypeCat.ofHom (![0, 0, 1, 1] : Fin 4 → Fin 2)) := rfl

/-- The source object of `G`, including its structure map. -/
@[simp] theorem G_obj_zero :
    G.obj 0 = Over.mk (TypeCat.ofHom (![0, 0, 1, 1] : Fin 4 → Fin 2)) := rfl

/-- The target object of `G`, including its structure map. -/
@[simp] theorem G_obj_one :
    G.obj 1 = Over.mk (TypeCat.ofHom (![0, 0, 0, 1, 1] : Fin 5 → Fin 2)) := rfl

/-- The source object of `H`, including its structure map. -/
@[simp] theorem H_obj_zero :
    H.obj 0 = Over.mk (TypeCat.ofHom (![0, 0, 1, 1, 1] : Fin 5 → Fin 2)) := rfl

/-- The target object of `H`, including its structure map. -/
@[simp] theorem H_obj_one :
    H.obj 1 = Over.mk (TypeCat.ofHom (![0, 1, 1, 1] : Fin 4 → Fin 2)) := rfl

/-- The underlying transition of `F` on the nonidentity source arrow. -/
@[simp] theorem F_map_homOfLE_left :
    (F.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left =
      TypeCat.ofHom (![0, 1, 2] : Fin 3 → Fin 4) := rfl

/-- The underlying transition of `G` on the nonidentity source arrow. -/
@[simp] theorem G_map_homOfLE_left :
    (G.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left =
      TypeCat.ofHom (![0, 2, 3, 4] : Fin 4 → Fin 5) := rfl

/-- The underlying transition of `H` on the nonidentity source arrow. -/
@[simp] theorem H_map_homOfLE_left :
    (H.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left =
      TypeCat.ofHom (![0, 0, 1, 2, 3] : Fin 5 → Fin 4) := rfl

-- The domain instances follow the two object equations of each diagram.
-- No finite structure is chosen on a categorical pullback vertex.
private noncomputable instance F_domain_fintype (j : Fin 2) : Fintype (F.obj j).left :=
  Fin.cases (inferInstanceAs (Fintype (Fin 3)))
    (fun _ => inferInstanceAs (Fintype (Fin 4))) j

private noncomputable instance F_domain_decidableEq (j : Fin 2) : DecidableEq (F.obj j).left :=
  Fin.cases (inferInstanceAs (DecidableEq (Fin 3)))
    (fun _ => inferInstanceAs (DecidableEq (Fin 4))) j

private noncomputable instance G_domain_fintype (j : Fin 2) : Fintype (G.obj j).left :=
  Fin.cases (inferInstanceAs (Fintype (Fin 4)))
    (fun _ => inferInstanceAs (Fintype (Fin 5))) j

private noncomputable instance G_domain_decidableEq (j : Fin 2) : DecidableEq (G.obj j).left :=
  Fin.cases (inferInstanceAs (DecidableEq (Fin 4)))
    (fun _ => inferInstanceAs (DecidableEq (Fin 5))) j

private noncomputable instance H_domain_fintype (j : Fin 2) : Fintype (H.obj j).left :=
  Fin.cases (inferInstanceAs (Fintype (Fin 5)))
    (fun _ => inferInstanceAs (Fintype (Fin 4))) j

private noncomputable instance H_domain_decidableEq (j : Fin 2) : DecidableEq (H.obj j).left :=
  Fin.cases (inferInstanceAs (DecidableEq (Fin 5)))
    (fun _ => inferInstanceAs (DecidableEq (Fin 4))) j

private lemma F_obj (j : Fin 2) : F.obj j = fObject j := rfl
private lemma G_obj (j : Fin 2) : G.obj j = gObject j := rfl
private lemma H_obj (j : Fin 2) : H.obj j = hObject j := rfl
private lemma F_map_α : F.map α = fArrow := rfl
private lemma G_map_α : G.map α = gArrow := rfl
private lemma H_map_α : H.map α = hArrow := rfl

private lemma fStep_injective : Function.Injective fStep := by decide
private lemma gStep_injective : Function.Injective gStep := by decide
private lemma fStep_misses : ∀ x, fStep x ≠ 3 := by decide
private lemma gStep_misses : ∀ y, gStep y ≠ 1 := by decide
private lemma hStep_surjective : Function.Surjective hStep := by decide
private lemma hStep_collision : hStep 0 = hStep 1 ∧ (0 : Fin 5) ≠ 1 := by decide

private lemma fStep_not_surjective : ¬ Function.Surjective fStep := by
  intro h
  obtain ⟨x, hx⟩ := h 3
  exact fStep_misses x hx

private lemma gStep_not_surjective : ¬ Function.Surjective gStep := by
  intro h
  obtain ⟨y, hy⟩ := h 1
  exact gStep_misses y hy

private lemma hStep_not_injective : ¬ Function.Injective hStep := by
  intro h
  exact hStep_collision.2 (h hStep_collision.1)

private lemma steps_nonconstant :
    fStep 0 ≠ fStep 2 ∧ gStep 0 ≠ gStep 3 ∧ hStep 0 ≠ hStep 4 := by decide

private lemma fArrow_mono : Mono fArrow := by
  let : Mono fArrow.left := (mono_iff_injective _).2 fStep_injective
  exact Over.mono_of_mono_left fArrow

private lemma gArrow_mono : Mono gArrow := by
  let : Mono gArrow.left := (mono_iff_injective _).2 gStep_injective
  exact Over.mono_of_mono_left gArrow

private abbrev zeroPoint : Over S :=
  Over.mk (TypeCat.ofHom (fun _ : Fin 1 => (0 : Fin 2)))

private noncomputable def hPointZero : zeroPoint ⟶ hZero :=
  Over.homMk (TypeCat.ofHom (fun _ => (0 : Fin 5))) (by
    apply ConcreteCategory.hom_ext
    intro x
    rfl)

private noncomputable def hPointOne : zeroPoint ⟶ hZero :=
  Over.homMk (TypeCat.ofHom (fun _ => (1 : Fin 5))) (by
    apply ConcreteCategory.hom_ext
    intro x
    rfl)

private lemma hPoints_distinct : hPointZero ≠ hPointOne := by
  intro h
  have heq := ConcreteCategory.congr_hom
    (congrArg (fun k : zeroPoint ⟶ hZero => k.left) h) (0 : Fin 1)
  exact (by decide : (0 : Fin 5) ≠ 1) heq

private lemma hPoints_comp : hPointZero ≫ hArrow = hPointOne ≫ hArrow := by
  apply Over.OverMorphism.ext
  apply ConcreteCategory.hom_ext
  intro x
  rfl

private lemma hArrow_not_mono : ¬ Mono hArrow := by
  intro h
  let : Mono hArrow := h
  exact hPoints_distinct ((cancel_mono hArrow).1 hPoints_comp)

/-- The transition of `F` is a proper injection. -/
theorem F_transition_proper :
    Function.Injective (F.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left ∧
      ¬ Function.Surjective (F.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left :=
  ⟨fStep_injective, fStep_not_surjective⟩

/-- The transition of `G` is a proper injection. -/
theorem G_transition_proper :
    Function.Injective (G.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left ∧
      ¬ Function.Surjective (G.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left :=
  ⟨gStep_injective, gStep_not_surjective⟩

/-- The transition of `H` is onto but is not a monomorphism in the over-category. -/
theorem H_transition_surjective_not_mono :
    Function.Surjective (H.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left ∧
      ¬ Mono (H.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))) :=
  ⟨hStep_surjective, hArrow_not_mono⟩

/-! ## Coordinate cones and transitions -/

private abbrev fgPoints (j : Fin 2) :=
  Types.PullbackObj (F.obj j).hom (G.obj j).hom
private abbrev ghPoints (j : Fin 2) :=
  Types.PullbackObj (G.obj j).hom (H.obj j).hom

private noncomputable def fgBase (j : Fin 2) : (fgPoints j : Type) ⟶ S :=
  TypeCat.ofHom fun q => (F.obj j).hom q.val.1
private noncomputable def ghBase (j : Fin 2) : (ghPoints j : Type) ⟶ S :=
  TypeCat.ofHom fun q => (G.obj j).hom q.val.1

private noncomputable abbrev fgObject (j : Fin 2) : Over S := Over.mk (fgBase j)
private noncomputable abbrev ghObject (j : Fin 2) : Over S := Over.mk (ghBase j)
private abbrev leftPoints (j : Fin 2) := Types.PullbackObj (fgBase j) (H.obj j).hom
private abbrev rightPoints (j : Fin 2) := Types.PullbackObj (F.obj j).hom (ghBase j)

private noncomputable def fgLimitCone (j : Fin 2) :
    LimitCone (cospan (F.obj j).hom (G.obj j).hom) :=
  Types.pullbackLimitCone (F.obj j).hom (G.obj j).hom

private noncomputable def ghLimitCone (j : Fin 2) :
    LimitCone (cospan (G.obj j).hom (H.obj j).hom) :=
  Types.pullbackLimitCone (G.obj j).hom (H.obj j).hom

private noncomputable def leftLimitCone (j : Fin 2) : LimitCone (cospan (fgBase j) (H.obj j).hom) :=
  Types.pullbackLimitCone (fgBase j) (H.obj j).hom

private noncomputable def fgStep : fgPoints 0 → fgPoints 1 := fun q =>
  ⟨(fStep q.val.1, gStep q.val.2),
    (fStep_base _).trans (q.property.trans (gStep_base _).symm)⟩

private noncomputable def ghStep : ghPoints 0 → ghPoints 1 := fun q =>
  ⟨(gStep q.val.1, hStep q.val.2),
    (gStep_base _).trans (q.property.trans (hStep_base _).symm)⟩

private lemma fgStep_base (q : fgPoints 0) : fgBase 1 (fgStep q) = fgBase 0 q :=
  fStep_base q.val.1

private lemma ghStep_base (q : ghPoints 0) : ghBase 1 (ghStep q) = ghBase 0 q :=
  gStep_base q.val.1

private noncomputable def leftStep : leftPoints 0 → leftPoints 1 := fun q =>
  ⟨(fgStep q.val.1, hStep q.val.2),
    (fgStep_base _).trans (q.property.trans (hStep_base _).symm)⟩

private noncomputable def rightStep : rightPoints 0 → rightPoints 1 := fun q =>
  ⟨(fStep q.val.1, ghStep q.val.2),
    (fStep_base _).trans (q.property.trans (ghStep_base _).symm)⟩

private lemma fgStep_fst (q : fgPoints 0) : (fgStep q).val.1 = fStep q.val.1 := rfl
private lemma fgStep_snd (q : fgPoints 0) : (fgStep q).val.2 = gStep q.val.2 := rfl
private lemma ghStep_fst (q : ghPoints 0) : (ghStep q).val.1 = gStep q.val.1 := rfl
private lemma ghStep_snd (q : ghPoints 0) : (ghStep q).val.2 = hStep q.val.2 := rfl
private lemma leftStep_fst (q : leftPoints 0) : (leftStep q).val.1 = fgStep q.val.1 := rfl
private lemma leftStep_snd (q : leftPoints 0) : (leftStep q).val.2 = hStep q.val.2 := rfl
private lemma rightStep_fst (q : rightPoints 0) : (rightStep q).val.1 = fStep q.val.1 := rfl
private lemma rightStep_snd (q : rightPoints 0) : (rightStep q).val.2 = ghStep q.val.2 := rfl

/-- Equal-bit triples of points in the three finite diagrams. -/
abbrev Triple (j : Fin 2) : Type :=
  {q : (F.obj j).left × (G.obj j).left × (H.obj j).left //
    (F.obj j).hom q.1 = (G.obj j).hom q.2.1 ∧
      (G.obj j).hom q.2.1 = (H.obj j).hom q.2.2}

/-- Source triples are the equal-bit subtype of `Fin 3 × Fin 4 × Fin 5`. -/
@[simp] theorem Triple_zero :
    Triple 0 = {q : Fin 3 × Fin 4 × Fin 5 //
      (![0, 0, 1] : Fin 3 → Fin 2) q.1 =
          (![0, 0, 1, 1] : Fin 4 → Fin 2) q.2.1 ∧
        (![0, 0, 1, 1] : Fin 4 → Fin 2) q.2.1 =
          (![0, 0, 1, 1, 1] : Fin 5 → Fin 2) q.2.2} := rfl

/-- Target triples are the equal-bit subtype of `Fin 4 × Fin 5 × Fin 4`. -/
@[simp] theorem Triple_one :
    Triple 1 = {q : Fin 4 × Fin 5 × Fin 4 //
      (![0, 0, 1, 1] : Fin 4 → Fin 2) q.1 =
          (![0, 0, 0, 1, 1] : Fin 5 → Fin 2) q.2.1 ∧
        (![0, 0, 0, 1, 1] : Fin 5 → Fin 2) q.2.1 =
          (![0, 1, 1, 1] : Fin 4 → Fin 2) q.2.2} := rfl

/-- Equal-bit triples are determined by their three coordinates. -/
@[ext] theorem Triple.ext {j : Fin 2} {p q : Triple j}
    (hf : p.val.1 = q.val.1) (hg : p.val.2.1 = q.val.2.1)
    (hh : p.val.2.2 = q.val.2.2) : p = q := by
  apply Subtype.ext
  exact Prod.ext hf (Prod.ext hg hh)

-- Flat coordinates are auxiliary finite data, separate from any chosen pullback.
private abbrev triplePoints (j : Fin 2) := Triple j

private noncomputable def leftCoordinates (j : Fin 2) : leftPoints j ≃ triplePoints j where
  toFun q := ⟨(q.val.1.val.1, q.val.1.val.2, q.val.2),
    q.val.1.property, q.val.1.property.symm.trans q.property⟩
  invFun q := ⟨(⟨(q.val.1, q.val.2.1), q.property.1⟩, q.val.2.2),
    q.property.1.trans q.property.2⟩
  left_inv q := by apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl

private noncomputable def rightCoordinates (j : Fin 2) : rightPoints j ≃ triplePoints j where
  toFun q := ⟨(q.val.1, q.val.2.val.1, q.val.2.val.2), q.property, q.val.2.property⟩
  invFun q := ⟨(q.val.1, ⟨(q.val.2.1, q.val.2.2), q.property.2⟩), q.property.1⟩
  left_inv q := by apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl

private noncomputable def tripleStep : triplePoints 0 → triplePoints 1 := fun q =>
  ⟨(fStep q.val.1, gStep q.val.2.1, hStep q.val.2.2),
    (fStep_base _).trans (q.property.1.trans (gStep_base _).symm),
    (gStep_base _).trans (q.property.2.trans (hStep_base _).symm)⟩

private lemma leftCoordinates_step (q : leftPoints 0) :
    leftCoordinates 1 (leftStep q) = tripleStep (leftCoordinates 0 q) := rfl

private lemma rightCoordinates_step (q : rightPoints 0) :
    rightCoordinates 1 (rightStep q) = tripleStep (rightCoordinates 0 q) := rfl

private lemma pair_cards :
    Fintype.card (fgPoints 0) = 6 ∧ Fintype.card (fgPoints 1) = 10 ∧
      Fintype.card (ghPoints 0) = 10 ∧ Fintype.card (ghPoints 1) = 9 := by decide

private lemma triple_cards :
    Fintype.card (triplePoints 0) = 14 ∧ Fintype.card (triplePoints 1) = 18 := by decide

private lemma nested_cards :
    Fintype.card (leftPoints 0) = 14 ∧ Fintype.card (leftPoints 1) = 18 ∧
      Fintype.card (rightPoints 0) = 14 ∧ Fintype.card (rightPoints 1) = 18 := by decide

private lemma fgStep_injective : Function.Injective fgStep := by decide
private lemma transition_image_cards :
    (Finset.univ.image fgStep).card = 6 ∧
      (Finset.univ.image ghStep).card = 8 ∧
      (Finset.univ.image tripleStep).card = 10 := by decide

private noncomputable def ghCollisionZero : ghPoints 0 := ⟨((0 : Fin 4), (0 : Fin 5)), by decide⟩
private noncomputable def ghCollisionOne : ghPoints 0 := ⟨((0 : Fin 4), (1 : Fin 5)), by decide⟩
private noncomputable def ghMissing : ghPoints 1 := ⟨((1 : Fin 5), (0 : Fin 4)), by decide⟩
private noncomputable def fgMissing : fgPoints 1 := ⟨((0 : Fin 4), (1 : Fin 5)), by decide⟩

private lemma ghStep_collision :
    ghCollisionZero ≠ ghCollisionOne ∧ ghStep ghCollisionZero = ghStep ghCollisionOne :=
  by decide

private lemma ghStep_misses : ∀ q, ghStep q ≠ ghMissing := by decide
private lemma fgStep_misses : ∀ q, fgStep q ≠ fgMissing := by decide

private noncomputable def tripleCollisionZero : triplePoints 0 :=
  ⟨((0 : Fin 3), (0 : Fin 4), (0 : Fin 5)), by decide⟩
private noncomputable def tripleCollisionOne : triplePoints 0 :=
  ⟨((0 : Fin 3), (0 : Fin 4), (1 : Fin 5)), by decide⟩
private noncomputable def tripleNonzero : triplePoints 0 :=
  ⟨((2 : Fin 3), (2 : Fin 4), (2 : Fin 5)), by decide⟩
private noncomputable def tripleMissing : triplePoints 1 :=
  ⟨((0 : Fin 4), (1 : Fin 5), (0 : Fin 4)), by decide⟩

private lemma tripleStep_collision :
    tripleCollisionZero ≠ tripleCollisionOne ∧
      tripleStep tripleCollisionZero = tripleStep tripleCollisionOne := by decide

private lemma tripleStep_misses : ∀ q, tripleStep q ≠ tripleMissing := by decide

private lemma tripleStep_not_injective : ¬ Function.Injective tripleStep := by
  intro h
  exact tripleStep_collision.1 (h tripleStep_collision.2)

private lemma tripleStep_not_surjective : ¬ Function.Surjective tripleStep := by
  intro h
  obtain ⟨q, hq⟩ := h tripleMissing
  exact tripleStep_misses q hq

-- These coordinates describe all eight missing targets, including the two over bit zero.
private lemma tripleStep_missing_iff : ∀ q : triplePoints 1,
    (¬ ∃ p, tripleStep p = q) ↔
      q.val.1 = (3 : Fin 4) ∨ q.val.2.1 = (1 : Fin 5) := by
  -- Every other equal-bit target has equal-bit source coordinates.
  have hlift : ∀ x : Fin 4, ∀ y : Fin 5, ∀ z : Fin 4,
      fBaseOne x = gBaseOne y → gBaseOne y = hBaseOne z →
      x ≠ 3 → y ≠ 1 →
      ∃ a : Fin 3, ∃ b : Fin 4, ∃ c : Fin 5,
        fBaseZero a = gBaseZero b ∧ gBaseZero b = hBaseZero c ∧
          fStep a = x ∧ gStep b = y ∧ hStep c = z := by decide
  intro q
  constructor
  · intro hmissing
    by_contra hcoordinates
    have hx : q.val.1 ≠ (3 : Fin 4) := fun hx => hcoordinates (Or.inl hx)
    have hy : q.val.2.1 ≠ (1 : Fin 5) := fun hy => hcoordinates (Or.inr hy)
    obtain ⟨a, b, c, hab, hbc, ha, hb, hc⟩ :=
      hlift q.val.1 q.val.2.1 q.val.2.2 q.property.1 q.property.2 hx hy
    apply hmissing
    refine ⟨⟨(a, b, c), hab, hbc⟩, ?_⟩
    exact Triple.ext ha hb hc
  · rintro (hx | hy) ⟨p, hp⟩
    · exact fStep_misses p.val.1
        ((congrArg (fun q : triplePoints 1 => q.val.1) hp).trans hx)
    · exact gStep_misses p.val.2.1
        ((congrArg (fun q : triplePoints 1 => q.val.2.1) hp).trans hy)

private lemma tripleStep_nonconstant :
    tripleStep tripleCollisionZero ≠ tripleStep tripleNonzero := by decide

private lemma tripleStep_fibers :
    Fintype.card {q : triplePoints 1 //
      (Finset.univ.filter (fun p : triplePoints 0 => tripleStep p = q)).card = 2} = 4 ∧
    Fintype.card {q : triplePoints 1 //
      (Finset.univ.filter (fun p : triplePoints 0 => tripleStep p = q)).card = 1} = 6 ∧
    Fintype.card {q : triplePoints 1 //
      (Finset.univ.filter (fun p : triplePoints 0 => tripleStep p = q)).card = 0} = 8 :=
  by decide

private noncomputable def tripleBase (j : Fin 2) : (triplePoints j : Type) ⟶ S :=
  TypeCat.ofHom fun q => (F.obj j).hom q.val.1

/-- Equal-bit triples, regarded as an ordinary object over the two-element base. -/
@[expose]
noncomputable def tripleObject (j : Fin 2) : Over (Fin 2 : Type) :=
  Over.mk (TypeCat.ofHom fun q : Triple j => (F.obj j).hom q.val.1)

/-- The domain of the triple over object is the full equal-bit subtype. -/
@[simp] theorem tripleObject_left (j : Fin 2) :
    (tripleObject j).left = (Triple j : Type) := rfl

/-- The triple's structure map reads its first coordinate. -/
@[simp] theorem tripleObject_hom (j : Fin 2) :
    (tripleObject j).hom = TypeCat.ofHom (fun q : Triple j => (F.obj j).hom q.val.1) := rfl

private noncomputable def tripleArrow : tripleObject 0 ⟶ tripleObject 1 :=
  Over.homMk (TypeCat.ofHom tripleStep) (by
    apply ConcreteCategory.hom_ext
    intro q
    exact fStep_base q.val.1)

private noncomputable def triplePointZero : zeroPoint ⟶ tripleObject 0 :=
  Over.homMk (TypeCat.ofHom (fun _ => tripleCollisionZero)) (by
    apply ConcreteCategory.hom_ext
    intro x
    rfl)

private noncomputable def triplePointOne : zeroPoint ⟶ tripleObject 0 :=
  Over.homMk (TypeCat.ofHom (fun _ => tripleCollisionOne)) (by
    apply ConcreteCategory.hom_ext
    intro x
    rfl)

private lemma tripleArrow_not_mono : ¬ Mono tripleArrow := by
  intro h
  let : Mono tripleArrow := h
  have hcomp : triplePointZero ≫ tripleArrow = triplePointOne ≫ tripleArrow := by
    apply Over.OverMorphism.ext
    apply ConcreteCategory.hom_ext
    intro x
    exact tripleStep_collision.2
  have heq := ConcreteCategory.congr_hom
    (congrArg (fun k : zeroPoint ⟶ tripleObject 0 => k.left)
      ((cancel_mono tripleArrow).1 hcomp)) (0 : Fin 1)
  exact tripleStep_collision.1 heq

/-! ## An involution of the first diagram -/

private def fSwapZero : Fin 3 → Fin 3 := ![1, 0, 2]
private def fSwapOne : Fin 4 → Fin 4 := ![1, 0, 2, 3]

private lemma fSwapZero_base (x : Fin 3) : fBaseZero (fSwapZero x) = fBaseZero x := by
  fin_cases x <;> rfl

private lemma fSwapOne_base (x : Fin 4) : fBaseOne (fSwapOne x) = fBaseOne x := by
  fin_cases x <;> rfl

private lemma fSwap_square (x : Fin 3) : fSwapOne (fStep x) = fStep (fSwapZero x) := by
  fin_cases x <;> rfl

private def fSwapZeroEquiv : Fin 3 ≃ Fin 3 where
  toFun := fSwapZero
  invFun := fSwapZero
  left_inv x := by fin_cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl

private def fSwapOneEquiv : Fin 4 ≃ Fin 4 where
  toFun := fSwapOne
  invFun := fSwapOne
  left_inv x := by fin_cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl

private noncomputable def fSwapZeroIso : fZero ≅ fZero :=
  Over.isoMk fSwapZeroEquiv.toIso (by
    apply ConcreteCategory.hom_ext
    exact fSwapZero_base)

private noncomputable def fSwapOneIso : fOne ≅ fOne :=
  Over.isoMk fSwapOneEquiv.toIso (by
    apply ConcreteCategory.hom_ext
    exact fSwapOne_base)

private noncomputable def fSwapComponent (j : Fin 2) : F.obj j ≅ F.obj j :=
  Fin.cases fSwapZeroIso (fun _ => fSwapOneIso) j

private lemma fSwapComponent_identity_square (j : Fin 2) :
    F.map (𝟙 j) ≫ (fSwapComponent j).hom =
      (fSwapComponent j).hom ≫ F.map (𝟙 j) := by
  have hmap : F.map (𝟙 j) = 𝟙 (F.obj j) := Functor.map_id F j
  calc
    F.map (𝟙 j) ≫ (fSwapComponent j).hom =
        𝟙 (F.obj j) ≫ (fSwapComponent j).hom :=
      congrArg (fun k : F.obj j ⟶ F.obj j => k ≫ (fSwapComponent j).hom) hmap
    _ = (fSwapComponent j).hom := Category.id_comp _
    _ = (fSwapComponent j).hom ≫ 𝟙 (F.obj j) := (Category.comp_id _).symm
    _ = (fSwapComponent j).hom ≫ F.map (𝟙 j) :=
      congrArg (fun k : F.obj j ⟶ F.obj j => (fSwapComponent j).hom ≫ k) hmap.symm

/-- The natural involution exchanging the first two points of `F`. -/
noncomputable def σF : F ≅ F :=
  NatIso.ofComponents fSwapComponent (by
    intro i j u
    have hij := leOfHom u
    fin_cases i <;> fin_cases j
    · have hu : u = 𝟙 (0 : Fin 2) := Subsingleton.elim _ _
      subst u
      exact fSwapComponent_identity_square (0 : Fin 2)
    · apply Over.OverMorphism.ext
      apply ConcreteCategory.hom_ext
      exact fSwap_square
    · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hij)
    · have hu : u = 𝟙 (1 : Fin 2) := Subsingleton.elim _ _
      subst u
      exact fSwapComponent_identity_square (1 : Fin 2))

private lemma σF_components_left :
    (σF.hom.app 0).left = TypeCat.ofHom (![1, 0, 2] : Fin 3 → Fin 3) ∧
      (σF.hom.app 1).left = TypeCat.ofHom (![1, 0, 2, 3] : Fin 4 → Fin 4) ∧
      (σF.inv.app 0).left = TypeCat.ofHom (![1, 0, 2] : Fin 3 → Fin 3) ∧
      (σF.inv.app 1).left = TypeCat.ofHom (![1, 0, 2, 3] : Fin 4 → Fin 4) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The source component of the involution, as an explicit finite function. -/
@[simp] theorem σF_hom_app_zero_left :
    (σF.hom.app 0).left = TypeCat.ofHom (![1, 0, 2] : Fin 3 → Fin 3) :=
  σF_components_left.1

/-- The target component of the involution, including its fourth fixed point. -/
@[simp] theorem σF_hom_app_one_left :
    (σF.hom.app 1).left = TypeCat.ofHom (![1, 0, 2, 3] : Fin 4 → Fin 4) :=
  σF_components_left.2.1

/-- The source inverse component is the same finite involution. -/
@[simp] theorem σF_inv_app_zero_left :
    (σF.inv.app 0).left = TypeCat.ofHom (![1, 0, 2] : Fin 3 → Fin 3) :=
  σF_components_left.2.2.1

/-- The target inverse component is the same finite involution. -/
@[simp] theorem σF_inv_app_one_left :
    (σF.inv.app 1).left = TypeCat.ofHom (![1, 0, 2, 3] : Fin 4 → Fin 4) :=
  σF_components_left.2.2.2

private lemma σF_zero_apply (x : Fin 3) : (σF.hom.app 0).left x = fSwapZero x := by
  rw [σF_hom_app_zero_left]
  rfl

private lemma σF_one_apply (x : Fin 4) : (σF.hom.app 1).left x = fSwapOne x := by
  rw [σF_hom_app_one_left]
  rfl

private lemma σF_inv_zero_apply (x : Fin 3) : (σF.inv.app 0).left x = fSwapZero x := by
  rw [σF_inv_app_zero_left]
  rfl

private lemma σF_inv_one_apply (x : Fin 4) : (σF.inv.app 1).left x = fSwapOne x := by
  rw [σF_inv_app_one_left]
  rfl

/-- The involution of `F` is not the identity transformation. -/
theorem σF_nonidentity : σF.hom ≠ 𝟙 F := by
  intro h
  have hleft := congrArg (fun k : F ⟶ F => (k.app 0).left) h
  simp only [σF_hom_app_zero_left, NatTrans.id_app, Over.id_left] at hleft
  have heq : (1 : Fin 3) = 0 := ConcreteCategory.congr_hom hleft (0 : Fin 3)
  exact (by decide : (1 : Fin 3) ≠ 0) heq

/-- Applying the involution of `F` twice gives the identity transformation. -/
theorem σF_involution : σF.hom ≫ σF.hom = 𝟙 F := by
  apply NatTrans.ext
  funext j
  simp only [NatTrans.comp_app, NatTrans.id_app]
  fin_cases j
  · apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.id_left]
    apply ConcreteCategory.hom_ext
    intro x
    fin_cases x <;> rfl
  · apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.id_left]
    apply ConcreteCategory.hom_ext
    intro x
    fin_cases x <;> rfl

private noncomputable def σG : G ≅ G := Iso.refl G
private noncomputable def σH : H ≅ H := Iso.refl H

private noncomputable def fgSwap (j : Fin 2) : fgPoints j → fgPoints j := fun q =>
  ⟨((σF.hom.app j).left q.val.1, q.val.2),
    (ConcreteCategory.congr_hom (Over.w (σF.hom.app j)) q.val.1).trans q.property⟩

private lemma fgSwap_base (j : Fin 2) (q : fgPoints j) :
    fgBase j (fgSwap j q) = fgBase j q :=
  ConcreteCategory.congr_hom (Over.w (σF.hom.app j)) q.val.1

private noncomputable def leftSwap (j : Fin 2) : leftPoints j → leftPoints j := fun q =>
  ⟨(fgSwap j q.val.1, q.val.2), (fgSwap_base j _).trans q.property⟩

private noncomputable def rightSwap (j : Fin 2) : rightPoints j → rightPoints j := fun q =>
  ⟨((σF.hom.app j).left q.val.1, q.val.2),
    (ConcreteCategory.congr_hom (Over.w (σF.hom.app j)) q.val.1).trans q.property⟩

private noncomputable def tripleSwap (j : Fin 2) : triplePoints j → triplePoints j := fun q =>
  ⟨((σF.hom.app j).left q.val.1, q.val.2.1, q.val.2.2),
    (ConcreteCategory.congr_hom (Over.w (σF.hom.app j)) q.val.1).trans q.property.1,
    q.property.2⟩

private lemma leftCoordinates_swap (j : Fin 2) (q : leftPoints j) :
    leftCoordinates j (leftSwap j q) = tripleSwap j (leftCoordinates j q) := rfl

private lemma rightCoordinates_swap (j : Fin 2) (q : rightPoints j) :
    rightCoordinates j (rightSwap j q) = tripleSwap j (rightCoordinates j q) := rfl

private lemma tripleSwap_step (q : triplePoints 0) :
    tripleSwap 1 (tripleStep q) = tripleStep (tripleSwap 0 q) := by
  apply Subtype.ext
  exact Prod.ext (fSwap_square q.val.1) rfl

private lemma tripleSwap_involution (j : Fin 2) (q : triplePoints j) :
    tripleSwap j (tripleSwap j q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · have h := ConcreteCategory.congr_hom
      (congrArg (fun k : F ⟶ F => (k.app j).left) σF_involution) q.val.1
    exact h
  · rfl

private lemma tripleSwap_moves_iff (j : Fin 2) (q : triplePoints j) :
    tripleSwap j q ≠ q ↔ (σF.hom.app j).left q.val.1 ≠ q.val.1 := by
  constructor
  · intro h hf
    exact h (Triple.ext hf rfl rfl)
  · intro h hq
    exact h (congrArg (fun p : triplePoints j => p.val.1) hq)

private lemma tripleSwapZero_moves_iff : ∀ q : triplePoints 0,
    tripleSwap 0 q ≠ q ↔ q.val.1 = (0 : Fin 3) ∨ q.val.1 = (1 : Fin 3) := by
  intro q
  rw [tripleSwap_moves_iff, σF_hom_app_zero_left]
  exact (by decide : ∀ x : Fin 3,
    TypeCat.ofHom (![1, 0, 2] : Fin 3 → Fin 3) x ≠ x ↔ x = 0 ∨ x = 1) q.val.1

private lemma tripleSwapOne_moves_iff : ∀ q : triplePoints 1,
    tripleSwap 1 q ≠ q ↔ q.val.1 = (0 : Fin 4) ∨ q.val.1 = (1 : Fin 4) := by
  intro q
  rw [tripleSwap_moves_iff, σF_hom_app_one_left]
  exact (by decide : ∀ x : Fin 4,
    TypeCat.ofHom (![1, 0, 2, 3] : Fin 4 → Fin 4) x ≠ x ↔ x = 0 ∨ x = 1) q.val.1

private lemma tripleSwap_moved_cards :
    Fintype.card {q : triplePoints 0 // tripleSwap 0 q ≠ q} = 8 ∧
      Fintype.card {q : triplePoints 1 // tripleSwap 1 q ≠ q} = 6 := by decide

/-! ## Associativity of the finite diagrams -/

section PointCharacteristics

variable {K : Type u₁} [Category.{v₁} K] {T : Type u}
variable (A B : K ⥤ Over T) [∀ k, HasPullback (A.obj k).hom (B.obj k).hom]

private lemma pairPointIso_fst (k : K) :
    (eqToIso (pullbackPairData_obj T A B k)).hom ≫
        (pullbackPointFan T (A.obj k) (B.obj k)).fst =
      (BinaryFan.fst ((pullbackPairData T A B).cone)).app k := by
  exact eq_of_heq
    ((eqToHom_comp_heq (pullbackPointFan T (A.obj k) (B.obj k)).fst
      (pullbackPairData_obj T A B k)).trans
        (heq_of_eq (pullbackPairData_fst_app T A B k)).symm)

private lemma pairPointIso_snd (k : K) :
    (eqToIso (pullbackPairData_obj T A B k)).hom ≫
        (pullbackPointFan T (A.obj k) (B.obj k)).snd =
      (BinaryFan.snd ((pullbackPairData T A B).cone)).app k := by
  exact eq_of_heq
    ((eqToHom_comp_heq (pullbackPointFan T (A.obj k) (B.obj k)).snd
      (pullbackPairData_obj T A B k)).trans
        (heq_of_eq (pullbackPairData_snd_app T A B k)).symm)

private lemma pointFan_fst_left (k : K) :
    (pullbackPointFan T (A.obj k) (B.obj k)).fst.left =
      pullback.fst (A.obj k).hom (B.obj k).hom := rfl

private lemma pointFan_snd_left (k : K) :
    (pullbackPointFan T (A.obj k) (B.obj k)).snd.left =
      pullback.snd (A.obj k).hom (B.obj k).hom := rfl

private lemma pairPointIso_hom_left (k : K) :
    (eqToIso (pullbackPairData_obj T A B k)).hom.left =
      eqToHom (congrArg (fun X : Over T => X.left) (pullbackPairData_obj T A B k)) :=
  Over.eqToHom_left (pullbackPairData_obj T A B k)

private lemma pairPointIso_fst_apply (k : K)
    (p : ((pullbackPairData T A B).cone.pt.obj k).left) :
    pullback.fst (A.obj k).hom (B.obj k).hom
        ((eqToIso (pullbackPairData_obj T A B k)).hom.left p) =
      ((BinaryFan.fst ((pullbackPairData T A B).cone)).app k).left p := by
  have h :
      ((eqToIso (pullbackPairData_obj T A B k)).hom.left :
        ((pullbackPairData T A B).cone.pt.obj k).left ⟶
          pullback (A.obj k).hom (B.obj k).hom) ≫
        pullback.fst (A.obj k).hom (B.obj k).hom =
      (((BinaryFan.fst ((pullbackPairData T A B).cone)).app k :
        (pullbackPairData T A B).cone.pt.obj k ⟶ A.obj k)).left := by
    have e : ((pullbackPairData T A B).cone.pt.obj k).left =
        pullback (A.obj k).hom (B.obj k).hom :=
      congrArg (fun X : Over T => X.left) (pullbackPairData_obj T A B k)
    have htransport : eqToHom e ≫ pullback.fst (A.obj k).hom (B.obj k).hom =
        ((BinaryFan.fst ((pullbackPairData T A B).cone)).app k).left :=
      eq_of_heq ((eqToHom_comp_heq (pullback.fst (A.obj k).hom (B.obj k).hom) e).trans
        (heq_of_eq (pullbackPairData_fst_app_left T A B k)).symm)
    exact (congrArg
      (fun f : ((pullbackPairData T A B).cone.pt.obj k).left ⟶
          pullback (A.obj k).hom (B.obj k).hom =>
        f ≫ pullback.fst (A.obj k).hom (B.obj k).hom)
      (pairPointIso_hom_left A B k)).trans htransport
  exact (types_comp_apply
    (X := ((pullbackPairData T A B).cone.pt.obj k).left)
    (Y := pullback (A.obj k).hom (B.obj k).hom) (Z := (A.obj k).left)
    (eqToIso (pullbackPairData_obj T A B k)).hom.left
    (pullback.fst (A.obj k).hom (B.obj k).hom) p).symm.trans
      (ConcreteCategory.congr_hom h p)

private lemma pairPointIso_snd_apply (k : K)
    (p : ((pullbackPairData T A B).cone.pt.obj k).left) :
    pullback.snd (A.obj k).hom (B.obj k).hom
        ((eqToIso (pullbackPairData_obj T A B k)).hom.left p) =
      ((BinaryFan.snd ((pullbackPairData T A B).cone)).app k).left p := by
  have h :
      ((eqToIso (pullbackPairData_obj T A B k)).hom.left :
        ((pullbackPairData T A B).cone.pt.obj k).left ⟶
          pullback (A.obj k).hom (B.obj k).hom) ≫
        pullback.snd (A.obj k).hom (B.obj k).hom =
      (((BinaryFan.snd ((pullbackPairData T A B).cone)).app k :
        (pullbackPairData T A B).cone.pt.obj k ⟶ B.obj k)).left := by
    have e : ((pullbackPairData T A B).cone.pt.obj k).left =
        pullback (A.obj k).hom (B.obj k).hom :=
      congrArg (fun X : Over T => X.left) (pullbackPairData_obj T A B k)
    have htransport : eqToHom e ≫ pullback.snd (A.obj k).hom (B.obj k).hom =
        ((BinaryFan.snd ((pullbackPairData T A B).cone)).app k).left :=
      eq_of_heq ((eqToHom_comp_heq (pullback.snd (A.obj k).hom (B.obj k).hom) e).trans
        (heq_of_eq (pullbackPairData_snd_app_left T A B k)).symm)
    exact (congrArg
      (fun f : ((pullbackPairData T A B).cone.pt.obj k).left ⟶
          pullback (A.obj k).hom (B.obj k).hom =>
        f ≫ pullback.snd (A.obj k).hom (B.obj k).hom)
      (pairPointIso_hom_left A B k)).trans htransport
  exact (types_comp_apply
    (X := ((pullbackPairData T A B).cone.pt.obj k).left)
    (Y := pullback (A.obj k).hom (B.obj k).hom) (Z := (B.obj k).left)
    (eqToIso (pullbackPairData_obj T A B k)).hom.left
    (pullback.snd (A.obj k).hom (B.obj k).hom) p).symm.trans
      (ConcreteCategory.congr_hom h p)

end PointCharacteristics

private lemma fgObject_hom (j : Fin 2) : (fgObject j).hom = fgBase j := rfl

private lemma ghObject_hom (j : Fin 2) : (ghObject j).hom = ghBase j := rfl

private instance fgFamily : ∀ j, HasPullback (F.obj j).hom (G.obj j).hom :=
  fun j => HasLimit.mk (fgLimitCone j)

private instance ghFamily : ∀ j, HasPullback (G.obj j).hom (H.obj j).hom :=
  fun j => HasLimit.mk (ghLimitCone j)

-- Object transport is kept separate from the ambient pullback comparison.
private noncomputable def fgPointIso (j : Fin 2) :
    (pullbackPairData S F G).cone.pt.obj j ≅
      Over.mk (pullback.fst (F.obj j).hom (G.obj j).hom ≫ (F.obj j).hom) :=
  eqToIso (pullbackPairData_obj S F G j)

private noncomputable def ghPointIso (j : Fin 2) :
    (pullbackPairData S G H).cone.pt.obj j ≅
      Over.mk (pullback.fst (G.obj j).hom (H.obj j).hom ≫ (G.obj j).hom) :=
  eqToIso (pullbackPairData_obj S G H j)

private lemma fgPointIso_fst (j : Fin 2) :
    (fgPointIso j).hom ≫ (pullbackPointFan S (F.obj j) (G.obj j)).fst =
      (BinaryFan.fst ((pullbackPairData S F G).cone)).app j :=
  pairPointIso_fst F G j

private lemma fgPointIso_snd (j : Fin 2) :
    (fgPointIso j).hom ≫ (pullbackPointFan S (F.obj j) (G.obj j)).snd =
      (BinaryFan.snd ((pullbackPairData S F G).cone)).app j :=
  pairPointIso_snd F G j

private lemma ghPointIso_fst (j : Fin 2) :
    (ghPointIso j).hom ≫ (pullbackPointFan S (G.obj j) (H.obj j)).fst =
      (BinaryFan.fst ((pullbackPairData S G H).cone)).app j :=
  pairPointIso_fst G H j

private lemma ghPointIso_snd (j : Fin 2) :
    (ghPointIso j).hom ≫ (pullbackPointFan S (G.obj j) (H.obj j)).snd =
      (BinaryFan.snd ((pullbackPairData S G H).cone)).app j :=
  pairPointIso_snd G H j

private noncomputable def fgRawCoordinateIso (j : Fin 2) :
    Over.mk (pullback.fst (F.obj j).hom (G.obj j).hom ≫ (F.obj j).hom) ≅
      fgObject j :=
  Over.isoMk (Types.pullbackIsoPullback (F.obj j).hom (G.obj j).hom) (by
    apply ConcreteCategory.hom_ext
    intro p
    simpa only [fgBase, Over.mk_hom, types_comp_apply, TypeCat.ofHom_apply] using
      congrArg (fun x => (F.obj j).hom x)
        (Types.pullbackIsoPullback_hom_fst (F.obj j).hom (G.obj j).hom p))

private noncomputable def ghRawCoordinateIso (j : Fin 2) :
    Over.mk (pullback.fst (G.obj j).hom (H.obj j).hom ≫ (G.obj j).hom) ≅
      ghObject j :=
  Over.isoMk (Types.pullbackIsoPullback (G.obj j).hom (H.obj j).hom) (by
    apply ConcreteCategory.hom_ext
    intro p
    simpa only [ghBase, Over.mk_hom, types_comp_apply, TypeCat.ofHom_apply] using
      congrArg (fun x => (G.obj j).hom x)
        (Types.pullbackIsoPullback_hom_fst (G.obj j).hom (H.obj j).hom p))

private noncomputable def fgCoordinateIso (j : Fin 2) :
    (pullbackPairData S F G).cone.pt.obj j ≅ fgObject j :=
  fgPointIso j ≪≫ fgRawCoordinateIso j

private noncomputable def ghCoordinateIso (j : Fin 2) :
    (pullbackPairData S G H).cone.pt.obj j ≅ ghObject j :=
  ghPointIso j ≪≫ ghRawCoordinateIso j

private lemma fgCoordinateIso_hom_left_apply (j : Fin 2)
    (p : ((pullbackPairData S F G).cone.pt.obj j).left) :
    (fgCoordinateIso j).hom.left p =
      (Types.pullbackIsoPullback (F.obj j).hom (G.obj j).hom).hom
        ((fgPointIso j).hom.left p) := by
  change ((fgPointIso j).hom.left ≫
    (Types.pullbackIsoPullback (F.obj j).hom (G.obj j).hom).hom) p = _
  exact types_comp_apply
    (X := ((pullbackPairData S F G).cone.pt.obj j).left)
    (Y := pullback (F.obj j).hom (G.obj j).hom) (Z := fgPoints j)
    (fgPointIso j).hom.left
    (Types.pullbackIsoPullback (F.obj j).hom (G.obj j).hom).hom p

private lemma ghCoordinateIso_hom_left_apply (j : Fin 2)
    (p : ((pullbackPairData S G H).cone.pt.obj j).left) :
    (ghCoordinateIso j).hom.left p =
      (Types.pullbackIsoPullback (G.obj j).hom (H.obj j).hom).hom
        ((ghPointIso j).hom.left p) := by
  change ((ghPointIso j).hom.left ≫
    (Types.pullbackIsoPullback (G.obj j).hom (H.obj j).hom).hom) p = _
  exact types_comp_apply
    (X := ((pullbackPairData S G H).cone.pt.obj j).left)
    (Y := pullback (G.obj j).hom (H.obj j).hom) (Z := ghPoints j)
    (ghPointIso j).hom.left
    (Types.pullbackIsoPullback (G.obj j).hom (H.obj j).hom).hom p

private lemma fgCoordinateIso_fst (j : Fin 2)
    (p : ((pullbackPairData S F G).cone.pt.obj j).left) :
    ((fgCoordinateIso j).hom.left p).val.1 =
      ((BinaryFan.fst ((pullbackPairData S F G).cone)).app j).left p := by
  have h : pullback.fst (F.obj j).hom (G.obj j).hom
      ((fgPointIso j).hom.left p) =
      ((BinaryFan.fst ((pullbackPairData S F G).cone)).app j).left p :=
    pairPointIso_fst_apply F G j p
  calc
    ((fgCoordinateIso j).hom.left p).val.1 =
        pullback.fst (F.obj j).hom (G.obj j).hom ((fgPointIso j).hom.left p) := by
      rw [fgCoordinateIso_hom_left_apply]
      exact Types.pullbackIsoPullback_hom_fst (F.obj j).hom (G.obj j).hom
        ((fgPointIso j).hom.left p)
    _ = _ := h

private lemma fgCoordinateIso_snd (j : Fin 2)
    (p : ((pullbackPairData S F G).cone.pt.obj j).left) :
    ((fgCoordinateIso j).hom.left p).val.2 =
      ((BinaryFan.snd ((pullbackPairData S F G).cone)).app j).left p := by
  have h : pullback.snd (F.obj j).hom (G.obj j).hom
      ((fgPointIso j).hom.left p) =
      ((BinaryFan.snd ((pullbackPairData S F G).cone)).app j).left p :=
    pairPointIso_snd_apply F G j p
  calc
    ((fgCoordinateIso j).hom.left p).val.2 =
        pullback.snd (F.obj j).hom (G.obj j).hom ((fgPointIso j).hom.left p) := by
      rw [fgCoordinateIso_hom_left_apply]
      exact Types.pullbackIsoPullback_hom_snd (F.obj j).hom (G.obj j).hom
        ((fgPointIso j).hom.left p)
    _ = _ := h

private lemma ghCoordinateIso_fst (j : Fin 2)
    (p : ((pullbackPairData S G H).cone.pt.obj j).left) :
    ((ghCoordinateIso j).hom.left p).val.1 =
      ((BinaryFan.fst ((pullbackPairData S G H).cone)).app j).left p := by
  have h : pullback.fst (G.obj j).hom (H.obj j).hom
      ((ghPointIso j).hom.left p) =
      ((BinaryFan.fst ((pullbackPairData S G H).cone)).app j).left p :=
    pairPointIso_fst_apply G H j p
  calc
    ((ghCoordinateIso j).hom.left p).val.1 =
        pullback.fst (G.obj j).hom (H.obj j).hom ((ghPointIso j).hom.left p) := by
      rw [ghCoordinateIso_hom_left_apply]
      exact Types.pullbackIsoPullback_hom_fst (G.obj j).hom (H.obj j).hom
        ((ghPointIso j).hom.left p)
    _ = _ := h

private lemma ghCoordinateIso_snd (j : Fin 2)
    (p : ((pullbackPairData S G H).cone.pt.obj j).left) :
    ((ghCoordinateIso j).hom.left p).val.2 =
      ((BinaryFan.snd ((pullbackPairData S G H).cone)).app j).left p := by
  have h : pullback.snd (G.obj j).hom (H.obj j).hom
      ((ghPointIso j).hom.left p) =
      ((BinaryFan.snd ((pullbackPairData S G H).cone)).app j).left p :=
    pairPointIso_snd_apply G H j p
  calc
    ((ghCoordinateIso j).hom.left p).val.2 =
        pullback.snd (G.obj j).hom (H.obj j).hom ((ghPointIso j).hom.left p) := by
      rw [ghCoordinateIso_hom_left_apply]
      exact Types.pullbackIsoPullback_hom_snd (G.obj j).hom (H.obj j).hom
        ((ghPointIso j).hom.left p)
    _ = _ := h

-- The outer input uses the chosen inner pullback, not its coordinate subtype.
private noncomputable def leftDiagramIso (j : Fin 2) :
    cospan (pullback.fst (F.obj j).hom (G.obj j).hom ≫ (F.obj j).hom) (H.obj j).hom ≅
      cospan (fgBase j) (H.obj j).hom :=
  cospanExt ((Over.forget S).mapIso (fgRawCoordinateIso j)) (Iso.refl _) (Iso.refl S)
    (by
      have h :
          ((fgRawCoordinateIso j).hom.left :
            pullback (F.obj j).hom (G.obj j).hom ⟶ fgPoints j) ≫ fgBase j =
          pullback.fst (F.obj j).hom (G.obj j).hom ≫ (F.obj j).hom := by
        simpa only [fgObject_hom, Over.mk_hom] using Over.w (fgRawCoordinateIso j).hom
      rw [Functor.mapIso_hom, Over.forget_map, Iso.refl_hom, Category.comp_id]
      exact h) (by simp)

private noncomputable def selectedLeftLimitCone (j : Fin 2) :
    LimitCone (cospan
      (pullback.fst (F.obj j).hom (G.obj j).hom ≫ (F.obj j).hom) (H.obj j).hom) where
  cone := (Cone.postcompose (leftDiagramIso j).inv).obj (leftLimitCone j).cone
  isLimit := (IsLimit.postcomposeInvEquiv (leftDiagramIso j) (leftLimitCone j).cone).symm
    (leftLimitCone j).isLimit

private instance leftFamily : ∀ j, HasPullback
    (pullback.fst (F.obj j).hom (G.obj j).hom ≫ (F.obj j).hom) (H.obj j).hom :=
  fun j => HasLimit.mk (selectedLeftLimitCone j)

-- The right family is an output of the selected binary-fan construction.
private instance rightFamily : ∀ j, HasPullback (F.obj j).hom
    (pullback.fst (G.obj j).hom (H.obj j).hom ≫ (G.obj j).hom) :=
  rightPullbackFamily S F G H

/-- The left-associated finite diagram assembled from the selected pullback cones. -/
noncomputable def leftTriple : Fin 2 ⥤ Over (Fin 2 : Type) :=
  (leftTripleData S F G H).cone.pt

/-- The right-associated finite diagram, using the derived right pullback family. -/
noncomputable def rightTriple : Fin 2 ⥤ Over (Fin 2 : Type) :=
  (rightTripleData S F G H).cone.pt

/-- The first coordinate of the left-associated finite diagram. -/
noncomputable def leftF : leftTriple ⟶ F :=
  (BinaryFan.fst ((leftTripleData S F G H).cone)) ≫ (BinaryFan.fst ((pullbackPairData S F G).cone))

/-- The middle coordinate of the left-associated finite diagram. -/
noncomputable def leftG : leftTriple ⟶ G :=
  (BinaryFan.fst ((leftTripleData S F G H).cone)) ≫ (BinaryFan.snd ((pullbackPairData S F G).cone))

/-- The last coordinate of the left-associated finite diagram. -/
noncomputable def leftH : leftTriple ⟶ H := (BinaryFan.snd ((leftTripleData S F G H).cone))

/-- The first coordinate of the right-associated finite diagram. -/
noncomputable def rightF : rightTriple ⟶ F := (BinaryFan.fst ((rightTripleData S F G H).cone))

/-- The middle coordinate of the right-associated finite diagram. -/
noncomputable def rightG : rightTriple ⟶ G :=
  (BinaryFan.snd ((rightTripleData S F G H).cone)) ≫ (BinaryFan.fst ((pullbackPairData S G H).cone))

/-- The last coordinate of the right-associated finite diagram. -/
noncomputable def rightH : rightTriple ⟶ H :=
  (BinaryFan.snd ((rightTripleData S F G H).cone)) ≫ (BinaryFan.snd ((pullbackPairData S G H).cone))

/-- The binary-fan associator applied to the three finite diagrams. -/
noncomputable def associator : leftTriple ≅ rightTriple := pullbackAssociator S F G H

/-- The associator preserves the first coordinate. -/
@[reassoc] theorem associator_hom_f : associator.hom ≫ rightF = leftF :=
  (pullbackAssociator_hom_coordinates S F G H).1

/-- The associator preserves the middle coordinate. -/
@[reassoc] theorem associator_hom_g : associator.hom ≫ rightG = leftG :=
  (pullbackAssociator_hom_coordinates S F G H).2.1

/-- The associator preserves the last coordinate. -/
@[reassoc] theorem associator_hom_h : associator.hom ≫ rightH = leftH :=
  (pullbackAssociator_hom_coordinates S F G H).2.2

/-- The inverse associator preserves the first coordinate. -/
@[reassoc] theorem associator_inv_f : associator.inv ≫ leftF = rightF :=
  (pullbackAssociator_inv_coordinates S F G H).1

/-- The inverse associator preserves the middle coordinate. -/
@[reassoc] theorem associator_inv_g : associator.inv ≫ leftG = rightG :=
  (pullbackAssociator_inv_coordinates S F G H).2.1

/-- The inverse associator preserves the last coordinate. -/
@[reassoc] theorem associator_inv_h : associator.inv ≫ leftH = rightH :=
  (pullbackAssociator_inv_coordinates S F G H).2.2

private noncomputable def leftInnerCoordinates (j : Fin 2) :
    Types.PullbackObj ((pullbackPairData S F G).cone.pt.obj j).hom (H.obj j).hom ≃
      leftPoints j :=
  (Equiv.prodCongr ((Over.forget S).mapIso (fgCoordinateIso j)).toEquiv
    (Equiv.refl (H.obj j).left)).subtypeEquiv (by
      intro q
      change ((pullbackPairData S F G).cone.pt.obj j).hom q.1 = (H.obj j).hom q.2 ↔
        fgBase j ((fgCoordinateIso j).hom.left q.1) = (H.obj j).hom q.2
      have hw :
          ((fgCoordinateIso j).hom.left :
            ((pullbackPairData S F G).cone.pt.obj j).left ⟶ fgPoints j) ≫
              fgBase j = ((pullbackPairData S F G).cone.pt.obj j).hom := by
        simpa only [fgObject_hom] using Over.w (fgCoordinateIso j).hom
      have h : fgBase j ((fgCoordinateIso j).hom.left q.1) =
          ((pullbackPairData S F G).cone.pt.obj j).hom q.1 :=
        (types_comp_apply
          (X := ((pullbackPairData S F G).cone.pt.obj j).left)
          (Y := fgPoints j) (Z := S) (fgCoordinateIso j).hom.left
          (fgBase j) q.1).symm.trans (ConcreteCategory.congr_hom hw q.1)
      rw [h])

private noncomputable def rightInnerCoordinates (j : Fin 2) :
    Types.PullbackObj (F.obj j).hom ((pullbackPairData S G H).cone.pt.obj j).hom ≃
      rightPoints j :=
  (Equiv.prodCongr (Equiv.refl (F.obj j).left)
    ((Over.forget S).mapIso (ghCoordinateIso j)).toEquiv).subtypeEquiv (by
      intro q
      change (F.obj j).hom q.1 = ((pullbackPairData S G H).cone.pt.obj j).hom q.2 ↔
        (F.obj j).hom q.1 = ghBase j ((ghCoordinateIso j).hom.left q.2)
      have hw :
          ((ghCoordinateIso j).hom.left :
            ((pullbackPairData S G H).cone.pt.obj j).left ⟶ ghPoints j) ≫
              ghBase j = ((pullbackPairData S G H).cone.pt.obj j).hom := by
        simpa only [ghObject_hom] using Over.w (ghCoordinateIso j).hom
      have h : ghBase j ((ghCoordinateIso j).hom.left q.2) =
          ((pullbackPairData S G H).cone.pt.obj j).hom q.2 :=
        (types_comp_apply
          (X := ((pullbackPairData S G H).cone.pt.obj j).left)
          (Y := ghPoints j) (Z := S) (ghCoordinateIso j).hom.left
          (ghBase j) q.2).symm.trans (ConcreteCategory.congr_hom hw q.2)
      rw [h])

private noncomputable def leftOuterPointIso (j : Fin 2) :
    leftTriple.obj j ≅ Over.mk
      (pullback.fst ((pullbackPairData S F G).cone.pt.obj j).hom (H.obj j).hom ≫
        ((pullbackPairData S F G).cone.pt.obj j).hom) :=
  eqToIso (pullbackPairData_obj S (pullbackPairData S F G).cone.pt H j)

private noncomputable def rightOuterPointIso (j : Fin 2) :
    rightTriple.obj j ≅ Over.mk
      (pullback.fst (F.obj j).hom ((pullbackPairData S G H).cone.pt.obj j).hom ≫
        (F.obj j).hom) :=
  eqToIso (pullbackPairData_obj S F (pullbackPairData S G H).cone.pt j)

private lemma leftOuterPointIso_fst (j : Fin 2) :
    (leftOuterPointIso j).hom ≫
        (pullbackPointFan S ((pullbackPairData S F G).cone.pt.obj j) (H.obj j)).fst =
      (BinaryFan.fst ((leftTripleData S F G H).cone)).app j :=
  pairPointIso_fst (pullbackPairData S F G).cone.pt H j

private lemma leftOuterPointIso_snd (j : Fin 2) :
    (leftOuterPointIso j).hom ≫
        (pullbackPointFan S ((pullbackPairData S F G).cone.pt.obj j) (H.obj j)).snd =
      (BinaryFan.snd ((leftTripleData S F G H).cone)).app j :=
  pairPointIso_snd (pullbackPairData S F G).cone.pt H j

private lemma rightOuterPointIso_fst (j : Fin 2) :
    (rightOuterPointIso j).hom ≫
        (pullbackPointFan S (F.obj j) ((pullbackPairData S G H).cone.pt.obj j)).fst =
      (BinaryFan.fst ((rightTripleData S F G H).cone)).app j :=
  pairPointIso_fst F (pullbackPairData S G H).cone.pt j

private lemma rightOuterPointIso_snd (j : Fin 2) :
    (rightOuterPointIso j).hom ≫
        (pullbackPointFan S (F.obj j) ((pullbackPairData S G H).cone.pt.obj j)).snd =
      (BinaryFan.snd ((rightTripleData S F G H).cone)).app j :=
  pairPointIso_snd F (pullbackPairData S G H).cone.pt j

private noncomputable def leftOuterEquiv (j : Fin 2) : (leftTriple.obj j).left ≃
    Types.PullbackObj ((pullbackPairData S F G).cone.pt.obj j).hom (H.obj j).hom :=
  (((Over.forget S).mapIso (leftOuterPointIso j)).toEquiv).trans
    (Types.pullbackIsoPullback ((pullbackPairData S F G).cone.pt.obj j).hom
      (H.obj j).hom).toEquiv

private noncomputable def rightOuterEquiv (j : Fin 2) : (rightTriple.obj j).left ≃
    Types.PullbackObj (F.obj j).hom ((pullbackPairData S G H).cone.pt.obj j).hom :=
  (((Over.forget S).mapIso (rightOuterPointIso j)).toEquiv).trans
    (Types.pullbackIsoPullback (F.obj j).hom
      ((pullbackPairData S G H).cone.pt.obj j).hom).toEquiv

private lemma leftOuterEquiv_apply (j : Fin 2) (p : (leftTriple.obj j).left) :
    leftOuterEquiv j p =
      (Types.pullbackIsoPullback ((pullbackPairData S F G).cone.pt.obj j).hom
        (H.obj j).hom).hom ((leftOuterPointIso j).hom.left p) := rfl

private lemma rightOuterEquiv_apply (j : Fin 2) (p : (rightTriple.obj j).left) :
    rightOuterEquiv j p =
      (Types.pullbackIsoPullback (F.obj j).hom
        ((pullbackPairData S G H).cone.pt.obj j).hom).hom
          ((rightOuterPointIso j).hom.left p) := rfl

private lemma leftOuterEquiv_fst (j : Fin 2) (p : (leftTriple.obj j).left) :
    (leftOuterEquiv j p).val.1 =
      ((BinaryFan.fst ((leftTripleData S F G H).cone)).app j).left p := by
  have h : pullback.fst ((pullbackPairData S F G).cone.pt.obj j).hom (H.obj j).hom
      ((leftOuterPointIso j).hom.left p) =
      (((BinaryFan.fst ((leftTripleData S F G H).cone)).app j :
        leftTriple.obj j ⟶ (pullbackPairData S F G).cone.pt.obj j)).left p :=
    pairPointIso_fst_apply (pullbackPairData S F G).cone.pt H j p
  have hp := Types.pullbackIsoPullback_hom_fst
    ((pullbackPairData S F G).cone.pt.obj j).hom (H.obj j).hom
    ((leftOuterPointIso j).hom.left p)
  rw [leftOuterEquiv_apply]
  exact hp.trans h

private lemma leftOuterEquiv_snd (j : Fin 2) (p : (leftTriple.obj j).left) :
    (leftOuterEquiv j p).val.2 =
      ((BinaryFan.snd ((leftTripleData S F G H).cone)).app j).left p := by
  have h : pullback.snd ((pullbackPairData S F G).cone.pt.obj j).hom (H.obj j).hom
      ((leftOuterPointIso j).hom.left p) =
      (((BinaryFan.snd ((leftTripleData S F G H).cone)).app j :
        leftTriple.obj j ⟶ H.obj j)).left p :=
    pairPointIso_snd_apply (pullbackPairData S F G).cone.pt H j p
  have hp := Types.pullbackIsoPullback_hom_snd
    ((pullbackPairData S F G).cone.pt.obj j).hom (H.obj j).hom
    ((leftOuterPointIso j).hom.left p)
  rw [leftOuterEquiv_apply]
  exact hp.trans h

private lemma rightOuterEquiv_fst (j : Fin 2) (p : (rightTriple.obj j).left) :
    (rightOuterEquiv j p).val.1 =
      ((BinaryFan.fst ((rightTripleData S F G H).cone)).app j).left p := by
  have h : pullback.fst (F.obj j).hom ((pullbackPairData S G H).cone.pt.obj j).hom
      ((rightOuterPointIso j).hom.left p) =
      (((BinaryFan.fst ((rightTripleData S F G H).cone)).app j :
        rightTriple.obj j ⟶ F.obj j)).left p :=
    pairPointIso_fst_apply F (pullbackPairData S G H).cone.pt j p
  have hp := Types.pullbackIsoPullback_hom_fst (F.obj j).hom
    ((pullbackPairData S G H).cone.pt.obj j).hom ((rightOuterPointIso j).hom.left p)
  rw [rightOuterEquiv_apply]
  exact hp.trans h

private lemma rightOuterEquiv_snd (j : Fin 2) (p : (rightTriple.obj j).left) :
    (rightOuterEquiv j p).val.2 =
      ((BinaryFan.snd ((rightTripleData S F G H).cone)).app j).left p := by
  have h : pullback.snd (F.obj j).hom ((pullbackPairData S G H).cone.pt.obj j).hom
      ((rightOuterPointIso j).hom.left p) =
      (((BinaryFan.snd ((rightTripleData S F G H).cone)).app j :
        rightTriple.obj j ⟶ (pullbackPairData S G H).cone.pt.obj j)).left p :=
    pairPointIso_snd_apply F (pullbackPairData S G H).cone.pt j p
  have hp := Types.pullbackIsoPullback_hom_snd (F.obj j).hom
    ((pullbackPairData S G H).cone.pt.obj j).hom ((rightOuterPointIso j).hom.left p)
  rw [rightOuterEquiv_apply]
  exact hp.trans h

private noncomputable def leftFlatEquiv (j : Fin 2) : (leftTriple.obj j).left ≃ Triple j :=
  ((leftOuterEquiv j).trans (leftInnerCoordinates j)).trans (leftCoordinates j)

private noncomputable def rightFlatEquiv (j : Fin 2) : (rightTriple.obj j).left ≃ Triple j :=
  ((rightOuterEquiv j).trans (rightInnerCoordinates j)).trans (rightCoordinates j)

private lemma leftFst_app_left (j : Fin 2) :
    ((BinaryFan.fst ((leftTripleData S F G H).cone)).app j).left =
      pullback.fst ((pullbackPairData S F G).cone.pt.obj j).hom (H.obj j).hom :=
  pullbackPairData_fst_app_left S (pullbackPairData S F G).cone.pt H j

private lemma leftSnd_app_left (j : Fin 2) :
    ((BinaryFan.snd ((leftTripleData S F G H).cone)).app j).left =
      pullback.snd ((pullbackPairData S F G).cone.pt.obj j).hom (H.obj j).hom :=
  pullbackPairData_snd_app_left S (pullbackPairData S F G).cone.pt H j

private lemma rightFst_app_left (j : Fin 2) :
    ((BinaryFan.fst ((rightTripleData S F G H).cone)).app j).left =
      pullback.fst (F.obj j).hom ((pullbackPairData S G H).cone.pt.obj j).hom :=
  pullbackPairData_fst_app_left S F (pullbackPairData S G H).cone.pt j

private lemma rightSnd_app_left (j : Fin 2) :
    ((BinaryFan.snd ((rightTripleData S F G H).cone)).app j).left =
      pullback.snd (F.obj j).hom ((pullbackPairData S G H).cone.pt.obj j).hom :=
  pullbackPairData_snd_app_left S F (pullbackPairData S G H).cone.pt j

private lemma leftFlatEquiv_f (j : Fin 2) (p : (leftTriple.obj j).left) :
    (leftFlatEquiv j p).val.1 = (leftF.app j).left p := by
  change ((fgCoordinateIso j).hom.left (leftOuterEquiv j p).val.1).val.1 =
    ((BinaryFan.fst ((pullbackPairData S F G).cone)).app j).left
      (((BinaryFan.fst ((leftTripleData S F G H).cone)).app j).left p)
  rw [fgCoordinateIso_fst, leftOuterEquiv_fst]

private lemma leftFlatEquiv_g (j : Fin 2) (p : (leftTriple.obj j).left) :
    (leftFlatEquiv j p).val.2.1 = (leftG.app j).left p := by
  change ((fgCoordinateIso j).hom.left (leftOuterEquiv j p).val.1).val.2 =
    ((BinaryFan.snd ((pullbackPairData S F G).cone)).app j).left
      (((BinaryFan.fst ((leftTripleData S F G H).cone)).app j).left p)
  rw [fgCoordinateIso_snd, leftOuterEquiv_fst]

private lemma leftFlatEquiv_h (j : Fin 2) (p : (leftTriple.obj j).left) :
    (leftFlatEquiv j p).val.2.2 = (leftH.app j).left p := by
  change (leftOuterEquiv j p).val.2 = _
  exact leftOuterEquiv_snd j p

private lemma rightFlatEquiv_f (j : Fin 2) (p : (rightTriple.obj j).left) :
    (rightFlatEquiv j p).val.1 = (rightF.app j).left p := by
  change (rightOuterEquiv j p).val.1 = _
  exact rightOuterEquiv_fst j p

private lemma rightFlatEquiv_g (j : Fin 2) (p : (rightTriple.obj j).left) :
    (rightFlatEquiv j p).val.2.1 = (rightG.app j).left p := by
  change ((ghCoordinateIso j).hom.left (rightOuterEquiv j p).val.2).val.1 =
    ((BinaryFan.fst ((pullbackPairData S G H).cone)).app j).left
      (((BinaryFan.snd ((rightTripleData S F G H).cone)).app j).left p)
  rw [ghCoordinateIso_fst, rightOuterEquiv_snd]

private lemma rightFlatEquiv_h (j : Fin 2) (p : (rightTriple.obj j).left) :
    (rightFlatEquiv j p).val.2.2 = (rightH.app j).left p := by
  change ((ghCoordinateIso j).hom.left (rightOuterEquiv j p).val.2).val.2 =
    ((BinaryFan.snd ((pullbackPairData S G H).cone)).app j).left
      (((BinaryFan.snd ((rightTripleData S F G H).cone)).app j).left p)
  rw [ghCoordinateIso_snd, rightOuterEquiv_snd]

/-- Coordinates of the chosen left-associated vertex, preserving its structure map. -/
noncomputable def leftTripleCoordinates (j : Fin 2) : leftTriple.obj j ≅ tripleObject j :=
  Over.isoMk (leftFlatEquiv j).toIso (by
    apply ConcreteCategory.hom_ext
    intro p
    change (F.obj j).hom (leftFlatEquiv j p).val.1 = (leftTriple.obj j).hom p
    rw [leftFlatEquiv_f]
    simpa only [types_comp_apply] using
      ConcreteCategory.congr_hom (Over.w (leftF.app j)) p)

/-- Coordinates of the chosen right-associated vertex, preserving its structure map. -/
noncomputable def rightTripleCoordinates (j : Fin 2) : rightTriple.obj j ≅ tripleObject j :=
  Over.isoMk (rightFlatEquiv j).toIso (by
    apply ConcreteCategory.hom_ext
    intro p
    change (F.obj j).hom (rightFlatEquiv j p).val.1 = (rightTriple.obj j).hom p
    rw [rightFlatEquiv_f]
    simpa only [types_comp_apply] using
      ConcreteCategory.congr_hom (Over.w (rightF.app j)) p)

/-- The left coordinate isomorphism recovers the first projection. -/
@[simp] theorem leftTripleCoordinates_hom_f (j : Fin 2) (p : (leftTriple.obj j).left) :
    ((leftTripleCoordinates j).hom.left p).val.1 = (leftF.app j).left p :=
  leftFlatEquiv_f j p

/-- The left coordinate isomorphism recovers the middle projection. -/
@[simp] theorem leftTripleCoordinates_hom_g (j : Fin 2) (p : (leftTriple.obj j).left) :
    ((leftTripleCoordinates j).hom.left p).val.2.1 = (leftG.app j).left p :=
  leftFlatEquiv_g j p

/-- The left coordinate isomorphism recovers the last projection. -/
@[simp] theorem leftTripleCoordinates_hom_h (j : Fin 2) (p : (leftTriple.obj j).left) :
    ((leftTripleCoordinates j).hom.left p).val.2.2 = (leftH.app j).left p :=
  leftFlatEquiv_h j p

/-- The right coordinate isomorphism recovers the first projection. -/
@[simp] theorem rightTripleCoordinates_hom_f (j : Fin 2) (p : (rightTriple.obj j).left) :
    ((rightTripleCoordinates j).hom.left p).val.1 = (rightF.app j).left p :=
  rightFlatEquiv_f j p

/-- The right coordinate isomorphism recovers the middle projection. -/
@[simp] theorem rightTripleCoordinates_hom_g (j : Fin 2) (p : (rightTriple.obj j).left) :
    ((rightTripleCoordinates j).hom.left p).val.2.1 = (rightG.app j).left p :=
  rightFlatEquiv_g j p

/-- The right coordinate isomorphism recovers the last projection. -/
@[simp] theorem rightTripleCoordinates_hom_h (j : Fin 2) (p : (rightTriple.obj j).left) :
    ((rightTripleCoordinates j).hom.left p).val.2.2 = (rightH.app j).left p :=
  rightFlatEquiv_h j p

/-- On every point, the associator preserves all three flattened coordinates. -/
theorem associator_hom_apply (j : Fin 2) (p : (leftTriple.obj j).left) :
    (rightTripleCoordinates j).hom.left ((associator.hom.app j).left p) =
      (leftTripleCoordinates j).hom.left p := by
  apply Triple.ext
  · rw [rightTripleCoordinates_hom_f, leftTripleCoordinates_hom_f]
    exact ConcreteCategory.congr_hom
      (congrArg Over.Hom.left (congr_app associator_hom_f j)) p
  · rw [rightTripleCoordinates_hom_g, leftTripleCoordinates_hom_g]
    exact ConcreteCategory.congr_hom
      (congrArg Over.Hom.left (congr_app associator_hom_g j)) p
  · rw [rightTripleCoordinates_hom_h, leftTripleCoordinates_hom_h]
    exact ConcreteCategory.congr_hom
      (congrArg Over.Hom.left (congr_app associator_hom_h j)) p

/-- On every point, the inverse associator preserves all three flattened coordinates. -/
theorem associator_inv_apply (j : Fin 2) (p : (rightTriple.obj j).left) :
    (leftTripleCoordinates j).hom.left ((associator.inv.app j).left p) =
      (rightTripleCoordinates j).hom.left p := by
  apply Triple.ext
  · rw [leftTripleCoordinates_hom_f, rightTripleCoordinates_hom_f]
    exact ConcreteCategory.congr_hom
      (congrArg Over.Hom.left (congr_app associator_inv_f j)) p
  · rw [leftTripleCoordinates_hom_g, rightTripleCoordinates_hom_g]
    exact ConcreteCategory.congr_hom
      (congrArg Over.Hom.left (congr_app associator_inv_g j)) p
  · rw [leftTripleCoordinates_hom_h, rightTripleCoordinates_hom_h]
    exact ConcreteCategory.congr_hom
      (congrArg Over.Hom.left (congr_app associator_inv_h j)) p

private lemma associator_hom_coordinate_component (j : Fin 2) :
    associator.hom.app j ≫ (rightTripleCoordinates j).hom =
      (leftTripleCoordinates j).hom := by
  apply Over.OverMorphism.ext
  apply ConcreteCategory.hom_ext
  intro p
  simpa only [Over.comp_left, types_comp_apply] using associator_hom_apply j p

private lemma associator_inv_coordinate_component (j : Fin 2) :
    associator.inv.app j ≫ (leftTripleCoordinates j).hom =
      (rightTripleCoordinates j).hom := by
  apply Over.OverMorphism.ext
  apply ConcreteCategory.hom_ext
  intro p
  simpa only [Over.comp_left, types_comp_apply] using associator_inv_apply j p

/-- The whole component isomorphism becomes the identity in equal-bit triple coordinates. -/
theorem associator_coordinateIso (j : Fin 2) :
    (leftTripleCoordinates j).symm ≪≫ associator.app j ≪≫ rightTripleCoordinates j =
      Iso.refl (tripleObject j) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.refl_hom]
  rw [associator_hom_coordinate_component]
  exact (leftTripleCoordinates j).inv_hom_id

private lemma tripleCoordinates_inv_apply {X : Over S} (j : Fin 2)
    (e : X ≅ tripleObject j) (q : Triple j) :
    e.hom.left (e.inv.left q) = q := by
  have h : (e.inv.left : (Triple j : Type) ⟶ X.left) ≫
      (e.hom.left : X.left ⟶ (Triple j : Type)) = 𝟙 (Triple j : Type) :=
    Over.inv_left_hom_left (f := X) (g := tripleObject j) e
  have hcomp : e.hom.left (e.inv.left q) =
      ((e.inv.left : (Triple j : Type) ⟶ X.left) ≫
        (e.hom.left : X.left ⟶ (Triple j : Type))) q :=
    (types_comp_apply (X := (Triple j : Type)) (Y := X.left)
      (Z := (Triple j : Type)) e.inv.left e.hom.left q).symm
  have hid :
      ((e.inv.left : (Triple j : Type) ⟶ X.left) ≫
        (e.hom.left : X.left ⟶ (Triple j : Type))) q = q :=
    (types_congr_hom (X := (Triple j : Type)) (Y := (Triple j : Type)) h q).trans
      (types_id_apply (Triple j : Type) q)
  exact hcomp.trans hid

/-- The inverse left coordinate isomorphism recovers the F projection. -/
@[simp] theorem leftTripleCoordinates_inv_f (j : Fin 2) (q : Triple j) :
    (leftF.app j).left ((leftTripleCoordinates j).inv.left q) = q.val.1 := by
  calc
    (leftF.app j).left ((leftTripleCoordinates j).inv.left q) =
        ((leftTripleCoordinates j).hom.left
          ((leftTripleCoordinates j).inv.left q)).val.1 :=
      (leftTripleCoordinates_hom_f j ((leftTripleCoordinates j).inv.left q)).symm
    _ = q.val.1 := congrArg (fun r : Triple j => r.val.1)
      (tripleCoordinates_inv_apply j (leftTripleCoordinates j) q)

/-- The inverse left coordinate isomorphism recovers the G projection. -/
@[simp] theorem leftTripleCoordinates_inv_g (j : Fin 2) (q : Triple j) :
    (leftG.app j).left ((leftTripleCoordinates j).inv.left q) = q.val.2.1 := by
  calc
    (leftG.app j).left ((leftTripleCoordinates j).inv.left q) =
        ((leftTripleCoordinates j).hom.left
          ((leftTripleCoordinates j).inv.left q)).val.2.1 :=
      (leftTripleCoordinates_hom_g j ((leftTripleCoordinates j).inv.left q)).symm
    _ = q.val.2.1 := congrArg (fun r : Triple j => r.val.2.1)
      (tripleCoordinates_inv_apply j (leftTripleCoordinates j) q)

/-- The inverse left coordinate isomorphism recovers the H projection. -/
@[simp] theorem leftTripleCoordinates_inv_h (j : Fin 2) (q : Triple j) :
    (leftH.app j).left ((leftTripleCoordinates j).inv.left q) = q.val.2.2 := by
  calc
    (leftH.app j).left ((leftTripleCoordinates j).inv.left q) =
        ((leftTripleCoordinates j).hom.left
          ((leftTripleCoordinates j).inv.left q)).val.2.2 :=
      (leftTripleCoordinates_hom_h j ((leftTripleCoordinates j).inv.left q)).symm
    _ = q.val.2.2 := congrArg (fun r : Triple j => r.val.2.2)
      (tripleCoordinates_inv_apply j (leftTripleCoordinates j) q)

/-- The inverse right coordinate isomorphism recovers the F projection. -/
@[simp] theorem rightTripleCoordinates_inv_f (j : Fin 2) (q : Triple j) :
    (rightF.app j).left ((rightTripleCoordinates j).inv.left q) = q.val.1 := by
  calc
    (rightF.app j).left ((rightTripleCoordinates j).inv.left q) =
        ((rightTripleCoordinates j).hom.left
          ((rightTripleCoordinates j).inv.left q)).val.1 :=
      (rightTripleCoordinates_hom_f j ((rightTripleCoordinates j).inv.left q)).symm
    _ = q.val.1 := congrArg (fun r : Triple j => r.val.1)
      (tripleCoordinates_inv_apply j (rightTripleCoordinates j) q)

/-- The inverse right coordinate isomorphism recovers the G projection. -/
@[simp] theorem rightTripleCoordinates_inv_g (j : Fin 2) (q : Triple j) :
    (rightG.app j).left ((rightTripleCoordinates j).inv.left q) = q.val.2.1 := by
  calc
    (rightG.app j).left ((rightTripleCoordinates j).inv.left q) =
        ((rightTripleCoordinates j).hom.left
          ((rightTripleCoordinates j).inv.left q)).val.2.1 :=
      (rightTripleCoordinates_hom_g j ((rightTripleCoordinates j).inv.left q)).symm
    _ = q.val.2.1 := congrArg (fun r : Triple j => r.val.2.1)
      (tripleCoordinates_inv_apply j (rightTripleCoordinates j) q)

/-- The inverse right coordinate isomorphism recovers the H projection. -/
@[simp] theorem rightTripleCoordinates_inv_h (j : Fin 2) (q : Triple j) :
    (rightH.app j).left ((rightTripleCoordinates j).inv.left q) = q.val.2.2 := by
  calc
    (rightH.app j).left ((rightTripleCoordinates j).inv.left q) =
        ((rightTripleCoordinates j).hom.left
          ((rightTripleCoordinates j).inv.left q)).val.2.2 :=
      (rightTripleCoordinates_hom_h j ((rightTripleCoordinates j).inv.left q)).symm
    _ = q.val.2.2 := congrArg (fun r : Triple j => r.val.2.2)
      (tripleCoordinates_inv_apply j (rightTripleCoordinates j) q)

/-- The inverse whole component isomorphism also becomes the identity in triple coordinates. -/
theorem associator_inv_coordinateIso (j : Fin 2) :
    (rightTripleCoordinates j).symm ≪≫ associator.symm.app j ≪≫ leftTripleCoordinates j =
      Iso.refl (tripleObject j) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.refl_hom]
  rw [associator_inv_coordinate_component]
  exact (rightTripleCoordinates j).inv_hom_id

private lemma over_comp_left_apply {X Y Z : Over (Fin 2 : Type)}
    (f : X ⟶ Y) (g : Y ⟶ Z) (p : X.left) :
    (f ≫ g).left p = g.left (f.left p) := by
  have h : (f ≫ g).left = f.left ≫ g.left := Over.comp_left X Y Z f g
  exact (congrArg (fun k : X.left ⟶ Z.left => k p) h).trans
    (types_comp_apply (X := X.left) (Y := Y.left) (Z := Z.left) f.left g.left p)

private lemma over_naturality_apply {D E : Fin 2 ⥤ Over (Fin 2 : Type)}
    (t : D ⟶ E) {i j : Fin 2} (u : i ⟶ j) (p : (D.obj i).left) :
    (t.app j).left ((D.map u).left p) = (E.map u).left ((t.app i).left p) := by
  calc
    (t.app j).left ((D.map u).left p) = (D.map u ≫ t.app j).left p :=
      (over_comp_left_apply (D.map u) (t.app j) p).symm
    _ = (t.app i ≫ E.map u).left p :=
      congrArg (fun k : D.obj i ⟶ E.obj j => k.left p) (t.naturality u)
    _ = (E.map u).left ((t.app i).left p) :=
      over_comp_left_apply (t.app i) (E.map u) p

private lemma f_transition_apply (x : (F.obj 0).left) :
    (F.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left x =
      (![0, 1, 2] : Fin 3 → Fin 4) x := by
  have h : Eq (α := Fin 4)
      ((F.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left x)
      ((TypeCat.ofHom (X := Fin 3) (Y := Fin 4) (![0, 1, 2] : Fin 3 → Fin 4))
        (x : Fin 3)) :=
    types_congr_hom (X := (Fin 3 : Type)) (Y := (Fin 4 : Type))
      F_map_homOfLE_left (x : Fin 3)
  exact h.trans (TypeCat.ofHom_apply (X := Fin 3) (Y := Fin 4)
    (![0, 1, 2] : Fin 3 → Fin 4) (x : Fin 3))

private lemma g_transition_apply (x : (G.obj 0).left) :
    (G.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left x =
      (![0, 2, 3, 4] : Fin 4 → Fin 5) x := by
  have h : Eq (α := Fin 5)
      ((G.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left x)
      ((TypeCat.ofHom (X := Fin 4) (Y := Fin 5) (![0, 2, 3, 4] : Fin 4 → Fin 5))
        (x : Fin 4)) :=
    types_congr_hom (X := (Fin 4 : Type)) (Y := (Fin 5 : Type))
      G_map_homOfLE_left (x : Fin 4)
  exact h.trans (TypeCat.ofHom_apply (X := Fin 4) (Y := Fin 5)
    (![0, 2, 3, 4] : Fin 4 → Fin 5) (x : Fin 4))

private lemma h_transition_apply (x : (H.obj 0).left) :
    (H.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left x =
      (![0, 0, 1, 2, 3] : Fin 5 → Fin 4) x := by
  have h : Eq (α := Fin 4)
      ((H.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left x)
      ((TypeCat.ofHom (X := Fin 5) (Y := Fin 4) (![0, 0, 1, 2, 3] : Fin 5 → Fin 4))
        (x : Fin 5)) :=
    types_congr_hom (X := (Fin 5 : Type)) (Y := (Fin 4 : Type))
      H_map_homOfLE_left (x : Fin 5)
  exact h.trans (TypeCat.ofHom_apply (X := Fin 5) (Y := Fin 4)
    (![0, 0, 1, 2, 3] : Fin 5 → Fin 4) (x : Fin 5))

/-- The nonidentity transition of `leftTriple` acts coordinatewise on every source point. -/
theorem leftTriple_map_homOfLE (p : (leftTriple.obj 0).left) :
    ((leftTripleCoordinates 1).hom.left
      ((leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p)).val =
      ((![0, 1, 2] : Fin 3 → Fin 4)
          ((leftTripleCoordinates 0).hom.left p).val.1,
        (![0, 2, 3, 4] : Fin 4 → Fin 5)
          ((leftTripleCoordinates 0).hom.left p).val.2.1,
        (![0, 0, 1, 2, 3] : Fin 5 → Fin 4)
          ((leftTripleCoordinates 0).hom.left p).val.2.2) := by
  apply Prod.ext
  · rw [leftTripleCoordinates_hom_f, leftTripleCoordinates_hom_f]
    exact (over_naturality_apply leftF
      (homOfLE (by decide : (0 : Fin 2) ≤ 1)) p).trans
        (f_transition_apply ((leftF.app 0).left p))
  · apply Prod.ext
    · rw [leftTripleCoordinates_hom_g, leftTripleCoordinates_hom_g]
      exact (over_naturality_apply leftG
        (homOfLE (by decide : (0 : Fin 2) ≤ 1)) p).trans
          (g_transition_apply ((leftG.app 0).left p))
    · rw [leftTripleCoordinates_hom_h, leftTripleCoordinates_hom_h]
      exact (over_naturality_apply leftH
        (homOfLE (by decide : (0 : Fin 2) ≤ 1)) p).trans
          (h_transition_apply ((leftH.app 0).left p))

/-- The nonidentity transition of `rightTriple` acts coordinatewise on every source point. -/
theorem rightTriple_map_homOfLE (p : (rightTriple.obj 0).left) :
    ((rightTripleCoordinates 1).hom.left
      ((rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p)).val =
      ((![0, 1, 2] : Fin 3 → Fin 4)
          ((rightTripleCoordinates 0).hom.left p).val.1,
        (![0, 2, 3, 4] : Fin 4 → Fin 5)
          ((rightTripleCoordinates 0).hom.left p).val.2.1,
        (![0, 0, 1, 2, 3] : Fin 5 → Fin 4)
          ((rightTripleCoordinates 0).hom.left p).val.2.2) := by
  apply Prod.ext
  · rw [rightTripleCoordinates_hom_f, rightTripleCoordinates_hom_f]
    exact (over_naturality_apply rightF
      (homOfLE (by decide : (0 : Fin 2) ≤ 1)) p).trans
        (f_transition_apply ((rightF.app 0).left p))
  · apply Prod.ext
    · rw [rightTripleCoordinates_hom_g, rightTripleCoordinates_hom_g]
      exact (over_naturality_apply rightG
        (homOfLE (by decide : (0 : Fin 2) ≤ 1)) p).trans
          (g_transition_apply ((rightG.app 0).left p))
    · rw [rightTripleCoordinates_hom_h, rightTripleCoordinates_hom_h]
      exact (over_naturality_apply rightH
        (homOfLE (by decide : (0 : Fin 2) ≤ 1)) p).trans
          (h_transition_apply ((rightH.app 0).left p))

/-- Naturality of the finite associator on the nonidentity source arrow. -/
theorem associator_hom_naturality :
    leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) ≫ associator.hom.app 1 =
      associator.hom.app 0 ≫ rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) :=
  associator.hom.naturality _

/-- Naturality of the inverse finite associator on the nonidentity source arrow. -/
theorem associator_inv_naturality :
    rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) ≫ associator.inv.app 1 =
      associator.inv.app 0 ≫ leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) :=
  associator.inv.naturality _

private noncomputable def tripleMap {i j : Fin 2} (u : i ⟶ j) :
    tripleObject i ⟶ tripleObject j := by
  revert u
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · intro _; exact 𝟙 _
    · intro _; exact tripleArrow
  · refine Fin.cases ?_ (fun j' => ?_) j
    · intro u
      exact False.elim (Nat.not_succ_le_zero _ (leOfHom u))
    · intro _; exact 𝟙 _

private lemma tripleMap_self (j : Fin 2) (u : j ⟶ j) : tripleMap u = 𝟙 _ := by
  have hu : u = 𝟙 j := Subsingleton.elim _ _
  subst u
  fin_cases j <;> rfl

private lemma tripleMap_zero_one (u : (0 : Fin 2) ⟶ 1) :
    tripleMap u = tripleArrow := rfl

private lemma tripleMap_comp {i j k : Fin 2} (u : i ⟶ j) (v : j ⟶ k) :
    tripleMap (u ≫ v) = tripleMap u ≫ tripleMap v := by
  have hij := leOfHom u
  have hjk := leOfHom v
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hij)
    | exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hjk)
    | simp only [tripleMap_self, tripleMap_zero_one, Category.id_comp, Category.comp_id]

/-- The finite diagram of equal-bit triples with coordinatewise transition. -/
@[expose]
noncomputable def tripleDiagram : Fin 2 ⥤ Over (Fin 2 : Type) where
  obj := tripleObject
  map {i j} u := by
    revert u
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro _; exact 𝟙 _
      · intro _
        exact Over.homMk (TypeCat.ofHom (fun q : Triple 0 =>
          (⟨((![0, 1, 2] : Fin 3 → Fin 4) q.val.1,
            (![0, 2, 3, 4] : Fin 4 → Fin 5) q.val.2.1,
            (![0, 0, 1, 2, 3] : Fin 5 → Fin 4) q.val.2.2), by
              constructor
              · exact (fStep_base _).trans (q.property.1.trans (gStep_base _).symm)
              · exact (gStep_base _).trans (q.property.2.trans (hStep_base _).symm)⟩ :
                Triple 1))) (by
                  apply ConcreteCategory.hom_ext
                  intro q
                  exact fStep_base q.val.1)
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro u
        exact False.elim (Nat.not_succ_le_zero _ (leOfHom u))
      · intro _; exact 𝟙 _
  map_id j := by
    change tripleMap (𝟙 j) = 𝟙 (tripleObject j)
    exact tripleMap_self j (𝟙 j)
  map_comp {i j k} u v := by
    change tripleMap (u ≫ v) = tripleMap u ≫ tripleMap v
    exact tripleMap_comp u v

/-- The coordinate reference diagram has the full equal-bit object at each index. -/
@[simp] theorem tripleDiagram_obj (j : Fin 2) : tripleDiagram.obj j = tripleObject j := rfl

private lemma tripleDiagram_map_homOfLE_eq :
    tripleDiagram.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) = tripleArrow := rfl

private lemma tripleDiagram_map_homOfLE_val (q : Triple 0) :
    ((tripleDiagram.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left q).val =
      ((![0, 1, 2] : Fin 3 → Fin 4) q.val.1,
        (![0, 2, 3, 4] : Fin 4 → Fin 5) q.val.2.1,
        (![0, 0, 1, 2, 3] : Fin 5 → Fin 4) q.val.2.2) := rfl

/-- Its transition changes each coordinate by the corresponding finite transition. -/
theorem tripleDiagram_map_homOfLE_apply (q : Triple 0) :
    ((tripleDiagram.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left q).val =
      ((![0, 1, 2] : Fin 3 → Fin 4) q.val.1,
        (![0, 2, 3, 4] : Fin 4 → Fin 5) q.val.2.1,
        (![0, 0, 1, 2, 3] : Fin 5 → Fin 4) q.val.2.2) :=
  tripleDiagram_map_homOfLE_val q

private lemma leftTripleCoordinates_naturality {i j : Fin 2} (u : i ⟶ j) :
    leftTriple.map u ≫ (leftTripleCoordinates j).hom =
      (leftTripleCoordinates i).hom ≫ tripleDiagram.map u := by
  have hij := leOfHom u
  fin_cases i <;> fin_cases j
  · have hu : u = 𝟙 (0 : Fin 2) := Subsingleton.elim _ _
    subst u
    simp
  · have hu : u = homOfLE (by decide : (0 : Fin 2) ≤ 1) := Subsingleton.elim _ _
    subst u
    apply Over.OverMorphism.ext
    apply ConcreteCategory.hom_ext
    intro p
    have h := (leftTriple_map_homOfLE p).trans
      (tripleDiagram_map_homOfLE_apply
        ((leftTripleCoordinates 0).hom.left p)).symm
    exact (over_comp_left_apply (leftTriple.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))) (leftTripleCoordinates 1).hom p).trans
        ((Subtype.ext h).trans (over_comp_left_apply (leftTripleCoordinates 0).hom
          (tripleDiagram.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))) p).symm)
  · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hij)
  · have hu : u = 𝟙 (1 : Fin 2) := Subsingleton.elim _ _
    subst u
    simp

/-- The left chosen vertices and their transitions identify naturally with equal-bit triples. -/
noncomputable def leftTripleCoordinateNatIso : leftTriple ≅ tripleDiagram :=
  NatIso.ofComponents (F := leftTriple) (G := tripleDiagram)
    (fun j => leftTripleCoordinates j)
    (fun {i j} u => leftTripleCoordinates_naturality (i := i) (j := j) u)

private lemma rightTripleCoordinates_naturality {i j : Fin 2} (u : i ⟶ j) :
    rightTriple.map u ≫ (rightTripleCoordinates j).hom =
      (rightTripleCoordinates i).hom ≫ tripleDiagram.map u := by
  have hij := leOfHom u
  fin_cases i <;> fin_cases j
  · have hu : u = 𝟙 (0 : Fin 2) := Subsingleton.elim _ _
    subst u
    simp
  · have hu : u = homOfLE (by decide : (0 : Fin 2) ≤ 1) := Subsingleton.elim _ _
    subst u
    apply Over.OverMorphism.ext
    apply ConcreteCategory.hom_ext
    intro p
    have h := (rightTriple_map_homOfLE p).trans
      (tripleDiagram_map_homOfLE_apply
        ((rightTripleCoordinates 0).hom.left p)).symm
    exact (over_comp_left_apply (rightTriple.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))) (rightTripleCoordinates 1).hom p).trans
        ((Subtype.ext h).trans (over_comp_left_apply (rightTripleCoordinates 0).hom
          (tripleDiagram.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))) p).symm)
  · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hij)
  · have hu : u = 𝟙 (1 : Fin 2) := Subsingleton.elim _ _
    subst u
    simp

/-- The right chosen vertices and their transitions identify naturally with equal-bit triples. -/
noncomputable def rightTripleCoordinateNatIso : rightTriple ≅ tripleDiagram :=
  NatIso.ofComponents (F := rightTriple) (G := tripleDiagram)
    (fun j => rightTripleCoordinates j)
    (fun {i j} u => rightTripleCoordinates_naturality (i := i) (j := j) u)

private lemma leftTripleCoordinateNatIso_component (j : Fin 2) :
    leftTripleCoordinateNatIso.app j = leftTripleCoordinates j := by
  unfold leftTripleCoordinateNatIso
  exact NatIso.ofComponents.app (F := leftTriple) (G := tripleDiagram)
    (fun k => leftTripleCoordinates k)
    (fun {i j} u => leftTripleCoordinates_naturality (i := i) (j := j) u) j

/-- The left natural coordinate comparison has the specified chosen-vertex components. -/
@[simp] theorem leftTripleCoordinateNatIso_app (j : Fin 2) :
    leftTripleCoordinateNatIso.app j = leftTripleCoordinates j :=
  leftTripleCoordinateNatIso_component j

private lemma rightTripleCoordinateNatIso_component (j : Fin 2) :
    rightTripleCoordinateNatIso.app j = rightTripleCoordinates j := by
  unfold rightTripleCoordinateNatIso
  exact NatIso.ofComponents.app (F := rightTriple) (G := tripleDiagram)
    (fun k => rightTripleCoordinates k)
    (fun {i j} u => rightTripleCoordinates_naturality (i := i) (j := j) u) j

/-- The right natural coordinate comparison has the specified chosen-vertex components. -/
@[simp] theorem rightTripleCoordinateNatIso_app (j : Fin 2) :
    rightTripleCoordinateNatIso.app j = rightTripleCoordinates j :=
  rightTripleCoordinateNatIso_component j

/-- The whole finite associator becomes the identity natural isomorphism in triple coordinates. -/
theorem associator_coordinateNatIso :
    leftTripleCoordinateNatIso.symm ≪≫ associator ≪≫ rightTripleCoordinateNatIso =
      Iso.refl tripleDiagram := by
  apply Iso.ext
  apply NatTrans.ext
  funext j
  have h₁ : leftTripleCoordinateNatIso.inv.app j =
      (leftTripleCoordinates j).inv :=
    congrArg Iso.inv (leftTripleCoordinateNatIso_app j)
  have h₂ : rightTripleCoordinateNatIso.hom.app j =
      (rightTripleCoordinates j).hom :=
    congrArg Iso.hom (rightTripleCoordinateNatIso_app j)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.refl_hom, NatTrans.id_app, h₁, h₂, tripleDiagram_obj]
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.refl_hom] using
    congrArg Iso.hom (associator_coordinateIso j)

/-- The inverse whole finite associator has the same natural coordinate correspondence. -/
theorem associator_inv_coordinateNatIso :
    rightTripleCoordinateNatIso.symm ≪≫ associator.symm ≪≫ leftTripleCoordinateNatIso =
      Iso.refl tripleDiagram := by
  apply Iso.ext
  apply NatTrans.ext
  funext j
  have h₁ : rightTripleCoordinateNatIso.inv.app j =
      (rightTripleCoordinates j).inv :=
    congrArg Iso.inv (rightTripleCoordinateNatIso_app j)
  have h₂ : leftTripleCoordinateNatIso.hom.app j =
      (leftTripleCoordinates j).hom :=
    congrArg Iso.hom (leftTripleCoordinateNatIso_app j)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.refl_hom, NatTrans.id_app, h₁, h₂, tripleDiagram_obj]
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.refl_hom] using
    congrArg Iso.hom (associator_inv_coordinateIso j)

private lemma triple_card_zero : Nat.card (Triple 0) = 14 := by
  rw [Triple_zero, Nat.card_eq_fintype_card]
  exact triple_cards.1

private lemma triple_card_one : Nat.card (Triple 1) = 18 := by
  rw [Triple_one, Nat.card_eq_fintype_card]
  exact triple_cards.2

/-- The chosen left-associated vertex at `0` has exactly 14 points. -/
theorem leftTriple_card_zero : Nat.card (leftTriple.obj 0).left = 14 :=
  (Nat.card_congr ((Over.forget S).mapIso (leftTripleCoordinates 0)).toEquiv).trans
    triple_card_zero

/-- The chosen left-associated vertex at `1` has exactly 18 points. -/
theorem leftTriple_card_one : Nat.card (leftTriple.obj 1).left = 18 :=
  (Nat.card_congr ((Over.forget S).mapIso (leftTripleCoordinates 1)).toEquiv).trans
    triple_card_one

/-- The chosen right-associated vertex at `0` has exactly 14 points. -/
theorem rightTriple_card_zero : Nat.card (rightTriple.obj 0).left = 14 :=
  (Nat.card_congr ((Over.forget S).mapIso (rightTripleCoordinates 0)).toEquiv).trans
    triple_card_zero

/-- The chosen right-associated vertex at `1` has exactly 18 points. -/
theorem rightTriple_card_one : Nat.card (rightTriple.obj 1).left = 18 :=
  (Nat.card_congr ((Over.forget S).mapIso (rightTripleCoordinates 1)).toEquiv).trans
    triple_card_one

private lemma leftTransition_coordinates :
    (leftTripleCoordinates 0).inv ≫
      leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) ≫
        (leftTripleCoordinates 1).hom = tripleArrow := by
  have h := leftTripleCoordinateNatIso.hom.naturality
    (homOfLE (by decide : (0 : Fin 2) ≤ 1))
  have h₀ : leftTripleCoordinateNatIso.hom.app 0 =
      (leftTripleCoordinates 0).hom :=
    congrArg Iso.hom (leftTripleCoordinateNatIso_app 0)
  have h₁ : leftTripleCoordinateNatIso.hom.app 1 =
      (leftTripleCoordinates 1).hom :=
    congrArg Iso.hom (leftTripleCoordinateNatIso_app 1)
  rw [h₀, h₁, tripleDiagram_map_homOfLE_eq] at h
  calc
    (leftTripleCoordinates 0).inv ≫
        leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) ≫
          (leftTripleCoordinates 1).hom =
        (leftTripleCoordinates 0).inv ≫ (leftTripleCoordinates 0).hom ≫ tripleArrow :=
      congrArg (fun k : leftTriple.obj 0 ⟶ tripleObject 1 =>
        (leftTripleCoordinates 0).inv ≫ k) h
    _ = ((leftTripleCoordinates 0).inv ≫ (leftTripleCoordinates 0).hom) ≫ tripleArrow :=
      (Category.assoc (leftTripleCoordinates 0).inv (leftTripleCoordinates 0).hom
        tripleArrow).symm
    _ = 𝟙 (tripleObject 0) ≫ tripleArrow :=
      congrArg (fun k : tripleObject 0 ⟶ tripleObject 0 => k ≫ tripleArrow)
        (leftTripleCoordinates 0).inv_hom_id
    _ = tripleArrow := Category.id_comp tripleArrow

/-- The chosen left transition is neither mono nor onto, and changes some points. -/
theorem leftTriple_transition_boundary :
    ¬ Mono (leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))) ∧
      ¬ Function.Surjective
        (leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left ∧
      ∃ p q : (leftTriple.obj 0).left,
        (leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p ≠
          (leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left q := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    let : Mono (leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))) := h
    have hm : Mono ((leftTripleCoordinates 0).inv ≫
        leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) ≫
          (leftTripleCoordinates 1).hom) := inferInstance
    rw [leftTransition_coordinates] at hm
    exact tripleArrow_not_mono hm
  · intro h
    have hm : Function.Surjective ((leftTripleCoordinates 0).inv ≫
        leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) ≫
          (leftTripleCoordinates 1).hom).left :=
      ((Over.forget S).mapIso (leftTripleCoordinates 1)).toEquiv.surjective.comp
        (h.comp ((Over.forget S).mapIso (leftTripleCoordinates 0).symm).toEquiv.surjective)
    rw [leftTransition_coordinates] at hm
    exact tripleStep_not_surjective hm
  · refine ⟨(leftTripleCoordinates 0).inv.left tripleCollisionZero,
      (leftTripleCoordinates 0).inv.left tripleNonzero, ?_⟩
    intro h
    have h' := congrArg (fun q => (leftTripleCoordinates 1).hom.left q) h
    have hp := ConcreteCategory.congr_hom
      (congrArg Over.Hom.left leftTransition_coordinates) tripleCollisionZero
    have hq := ConcreteCategory.congr_hom
      (congrArg Over.Hom.left leftTransition_coordinates) tripleNonzero
    exact tripleStep_nonconstant (hp.symm.trans (h'.trans hq))

private lemma rightTransition_coordinates :
    (rightTripleCoordinates 0).inv ≫
      rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) ≫
        (rightTripleCoordinates 1).hom = tripleArrow := by
  have h := rightTripleCoordinateNatIso.hom.naturality
    (homOfLE (by decide : (0 : Fin 2) ≤ 1))
  have h₀ : rightTripleCoordinateNatIso.hom.app 0 =
      (rightTripleCoordinates 0).hom :=
    congrArg Iso.hom (rightTripleCoordinateNatIso_app 0)
  have h₁ : rightTripleCoordinateNatIso.hom.app 1 =
      (rightTripleCoordinates 1).hom :=
    congrArg Iso.hom (rightTripleCoordinateNatIso_app 1)
  rw [h₀, h₁, tripleDiagram_map_homOfLE_eq] at h
  calc
    (rightTripleCoordinates 0).inv ≫
        rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) ≫
          (rightTripleCoordinates 1).hom =
        (rightTripleCoordinates 0).inv ≫ (rightTripleCoordinates 0).hom ≫ tripleArrow :=
      congrArg (fun k : rightTriple.obj 0 ⟶ tripleObject 1 =>
        (rightTripleCoordinates 0).inv ≫ k) h
    _ = ((rightTripleCoordinates 0).inv ≫ (rightTripleCoordinates 0).hom) ≫ tripleArrow :=
      (Category.assoc (rightTripleCoordinates 0).inv (rightTripleCoordinates 0).hom
        tripleArrow).symm
    _ = 𝟙 (tripleObject 0) ≫ tripleArrow :=
      congrArg (fun k : tripleObject 0 ⟶ tripleObject 0 => k ≫ tripleArrow)
        (rightTripleCoordinates 0).inv_hom_id
    _ = tripleArrow := Category.id_comp tripleArrow

/-- The chosen right transition is neither mono nor onto, and changes some points. -/
theorem rightTriple_transition_boundary :
    ¬ Mono (rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))) ∧
      ¬ Function.Surjective
        (rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left ∧
      ∃ p q : (rightTriple.obj 0).left,
        (rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p ≠
          (rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left q := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    let : Mono (rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))) := h
    have hm : Mono ((rightTripleCoordinates 0).inv ≫
        rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) ≫
          (rightTripleCoordinates 1).hom) := inferInstance
    rw [rightTransition_coordinates] at hm
    exact tripleArrow_not_mono hm
  · intro h
    have hm : Function.Surjective ((rightTripleCoordinates 0).inv ≫
        rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) ≫
          (rightTripleCoordinates 1).hom).left :=
      ((Over.forget S).mapIso (rightTripleCoordinates 1)).toEquiv.surjective.comp
        (h.comp ((Over.forget S).mapIso (rightTripleCoordinates 0).symm).toEquiv.surjective)
    rw [rightTransition_coordinates] at hm
    exact tripleStep_not_surjective hm
  · refine ⟨(rightTripleCoordinates 0).inv.left tripleCollisionZero,
      (rightTripleCoordinates 0).inv.left tripleNonzero, ?_⟩
    intro h
    have h' := congrArg (fun q => (rightTripleCoordinates 1).hom.left q) h
    have hp := ConcreteCategory.congr_hom
      (congrArg Over.Hom.left rightTransition_coordinates) tripleCollisionZero
    have hq := ConcreteCategory.congr_hom
      (congrArg Over.Hom.left rightTransition_coordinates) tripleNonzero
    exact tripleStep_nonconstant (hp.symm.trans (h'.trans hq))

end FiniteDiagram
end CategoryTheory

namespace CategoryTheory.FiniteDiagram

open Limits

/-! ## Product involutions and their compatibility with associativity -/

private lemma leftF_comp {X : Fin 2 ⥤ Over (Fin 2 : Type)} (f : X ⟶ leftTriple) :
    f ≫ leftF =
      (f ≫ (BinaryFan.fst (leftTripleData S F G H).cone :
        leftTriple ⟶ (pullbackPairData S F G).cone.pt)) ≫
      (BinaryFan.fst (pullbackPairData S F G).cone :
        (pullbackPairData S F G).cone.pt ⟶ F) :=
  (Category.assoc f
    (BinaryFan.fst (leftTripleData S F G H).cone :
      leftTriple ⟶ (pullbackPairData S F G).cone.pt)
    (BinaryFan.fst (pullbackPairData S F G).cone :
      (pullbackPairData S F G).cone.pt ⟶ F)).symm

private lemma leftG_comp {X : Fin 2 ⥤ Over (Fin 2 : Type)} (f : X ⟶ leftTriple) :
    f ≫ leftG =
      (f ≫ (BinaryFan.fst (leftTripleData S F G H).cone :
        leftTriple ⟶ (pullbackPairData S F G).cone.pt)) ≫
      (BinaryFan.snd (pullbackPairData S F G).cone :
        (pullbackPairData S F G).cone.pt ⟶ G) :=
  (Category.assoc f
    (BinaryFan.fst (leftTripleData S F G H).cone :
      leftTriple ⟶ (pullbackPairData S F G).cone.pt)
    (BinaryFan.snd (pullbackPairData S F G).cone :
      (pullbackPairData S F G).cone.pt ⟶ G)).symm

private lemma leftH_comp {X : Fin 2 ⥤ Over (Fin 2 : Type)} (f : X ⟶ leftTriple) :
    f ≫ leftH =
      f ≫ (BinaryFan.snd (leftTripleData S F G H).cone : leftTriple ⟶ H) := rfl

private lemma rightF_comp {X : Fin 2 ⥤ Over (Fin 2 : Type)} (f : X ⟶ rightTriple) :
    f ≫ rightF =
      f ≫ (BinaryFan.fst (rightTripleData S F G H).cone : rightTriple ⟶ F) := rfl

private lemma rightG_comp {X : Fin 2 ⥤ Over (Fin 2 : Type)} (f : X ⟶ rightTriple) :
    f ≫ rightG =
      (f ≫ (BinaryFan.snd (rightTripleData S F G H).cone :
        rightTriple ⟶ (pullbackPairData S G H).cone.pt)) ≫
      (BinaryFan.fst (pullbackPairData S G H).cone :
        (pullbackPairData S G H).cone.pt ⟶ G) :=
  (Category.assoc f
    (BinaryFan.snd (rightTripleData S F G H).cone :
      rightTriple ⟶ (pullbackPairData S G H).cone.pt)
    (BinaryFan.fst (pullbackPairData S G H).cone :
      (pullbackPairData S G H).cone.pt ⟶ G)).symm

private lemma rightH_comp {X : Fin 2 ⥤ Over (Fin 2 : Type)} (f : X ⟶ rightTriple) :
    f ≫ rightH =
      (f ≫ (BinaryFan.snd (rightTripleData S F G H).cone :
        rightTriple ⟶ (pullbackPairData S G H).cone.pt)) ≫
      (BinaryFan.snd (pullbackPairData S G H).cone :
        (pullbackPairData S G H).cone.pt ⟶ H) :=
  (Category.assoc f
    (BinaryFan.snd (rightTripleData S F G H).cone :
      rightTriple ⟶ (pullbackPairData S G H).cone.pt)
    (BinaryFan.snd (pullbackPairData S G H).cone :
      (pullbackPairData S G H).cone.pt ⟶ H)).symm

private lemma σG_hom_identity : σG.hom = 𝟙 G := rfl

private lemma σH_hom_identity : σH.hom = 𝟙 H := rfl

private lemma leftTriple_hom_ext_of_projections {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    {f g : X ⟶ leftTriple} (hf : f ≫ leftF = g ≫ leftF)
    (hg : f ≫ leftG = g ≫ leftG) (hh : f ≫ leftH = g ≫ leftH) : f = g := by
  apply BinaryFan.IsLimit.hom_ext (W := X)
    (X := (pullbackPairData S F G).cone.pt) (Y := H)
    (s := (leftTripleData S F G H).cone) (leftTripleData S F G H).isLimit
    (f := f) (g := g)
  · apply BinaryFan.IsLimit.hom_ext (W := X) (X := F) (Y := G)
      (s := (pullbackPairData S F G).cone)
      (f := f ≫ (BinaryFan.fst (leftTripleData S F G H).cone :
        leftTriple ⟶ (pullbackPairData S F G).cone.pt))
      (g := g ≫ (BinaryFan.fst (leftTripleData S F G H).cone :
        leftTriple ⟶ (pullbackPairData S F G).cone.pt))
      (pullbackPairData S F G).isLimit
    · have hF :
          (f ≫ (BinaryFan.fst (leftTripleData S F G H).cone :
            leftTriple ⟶ (pullbackPairData S F G).cone.pt)) ≫
            (BinaryFan.fst (pullbackPairData S F G).cone :
              (pullbackPairData S F G).cone.pt ⟶ F) =
          (g ≫ (BinaryFan.fst (leftTripleData S F G H).cone :
            leftTriple ⟶ (pullbackPairData S F G).cone.pt)) ≫
            (BinaryFan.fst (pullbackPairData S F G).cone :
              (pullbackPairData S F G).cone.pt ⟶ F) :=
        (leftF_comp f).symm.trans (hf.trans (leftF_comp g))
      simpa only [pair_obj_left] using hF
    · have hG :
          (f ≫ (BinaryFan.fst (leftTripleData S F G H).cone :
            leftTriple ⟶ (pullbackPairData S F G).cone.pt)) ≫
            (BinaryFan.snd (pullbackPairData S F G).cone :
              (pullbackPairData S F G).cone.pt ⟶ G) =
          (g ≫ (BinaryFan.fst (leftTripleData S F G H).cone :
            leftTriple ⟶ (pullbackPairData S F G).cone.pt)) ≫
            (BinaryFan.snd (pullbackPairData S F G).cone :
              (pullbackPairData S F G).cone.pt ⟶ G) :=
        (leftG_comp f).symm.trans (hg.trans (leftG_comp g))
      simpa only [pair_obj_right] using hG
  · have hH :
        f ≫ (BinaryFan.snd (leftTripleData S F G H).cone : leftTriple ⟶ H) =
          g ≫ (BinaryFan.snd (leftTripleData S F G H).cone : leftTriple ⟶ H) :=
      (leftH_comp f).symm.trans (hh.trans (leftH_comp g))
    have hEndpoint (a : X ⟶ leftTriple) :
        HEq
          (a ≫ (BinaryFan.snd (leftTripleData S F G H).cone :
            leftTriple ⟶ (pair (pullbackPairData S F G).cone.pt H).obj
              ⟨WalkingPair.right⟩))
          (a ≫ (BinaryFan.snd (leftTripleData S F G H).cone : leftTriple ⟶ H)) :=
      heq_comp (C := Fin 2 ⥤ Over (Fin 2 : Type))
        (X := X) (Y := leftTriple)
        (Z := (pair (pullbackPairData S F G).cone.pt H).obj ⟨WalkingPair.right⟩)
        (X' := X) (Y' := leftTriple) (Z' := H)
        rfl rfl (pair_obj_right (pullbackPairData S F G).cone.pt H)
        (heq_of_eq (rfl : a = a)) (by rfl)
    exact eq_of_heq
      ((hEndpoint f).trans ((heq_of_eq hH).trans (hEndpoint g).symm))

/-- The three coordinate projections jointly determine a morphism into `leftTriple`. -/
@[ext] theorem leftTriple_hom_ext {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    {f g : X ⟶ leftTriple} (hf : f ≫ leftF = g ≫ leftF)
    (hg : f ≫ leftG = g ≫ leftG) (hh : f ≫ leftH = g ≫ leftH) : f = g :=
  leftTriple_hom_ext_of_projections hf hg hh

private lemma rightTriple_hom_ext_of_projections {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    {f g : X ⟶ rightTriple} (hf : f ≫ rightF = g ≫ rightF)
    (hg : f ≫ rightG = g ≫ rightG) (hh : f ≫ rightH = g ≫ rightH) : f = g := by
  apply BinaryFan.IsLimit.hom_ext (W := X)
    (X := F) (Y := (pullbackPairData S G H).cone.pt)
    (s := (rightTripleData S F G H).cone) (rightTripleData S F G H).isLimit
    (f := f) (g := g)
  · have hF :
        f ≫ (BinaryFan.fst (rightTripleData S F G H).cone : rightTriple ⟶ F) =
          g ≫ (BinaryFan.fst (rightTripleData S F G H).cone : rightTriple ⟶ F) :=
      (rightF_comp f).symm.trans (hf.trans (rightF_comp g))
    have hEndpoint (a : X ⟶ rightTriple) :
        HEq
          (a ≫ (BinaryFan.fst (rightTripleData S F G H).cone :
            rightTriple ⟶ (pair F (pullbackPairData S G H).cone.pt).obj
              ⟨WalkingPair.left⟩))
          (a ≫ (BinaryFan.fst (rightTripleData S F G H).cone : rightTriple ⟶ F)) :=
      heq_comp (C := Fin 2 ⥤ Over (Fin 2 : Type))
        (X := X) (Y := rightTriple)
        (Z := (pair F (pullbackPairData S G H).cone.pt).obj ⟨WalkingPair.left⟩)
        (X' := X) (Y' := rightTriple) (Z' := F)
        rfl rfl (pair_obj_left F (pullbackPairData S G H).cone.pt)
        (heq_of_eq (rfl : a = a)) (by rfl)
    exact eq_of_heq
      ((hEndpoint f).trans ((heq_of_eq hF).trans (hEndpoint g).symm))
  · apply BinaryFan.IsLimit.hom_ext (W := X) (X := G) (Y := H)
      (s := (pullbackPairData S G H).cone)
      (f := f ≫ (BinaryFan.snd (rightTripleData S F G H).cone :
        rightTriple ⟶ (pullbackPairData S G H).cone.pt))
      (g := g ≫ (BinaryFan.snd (rightTripleData S F G H).cone :
        rightTriple ⟶ (pullbackPairData S G H).cone.pt))
      (pullbackPairData S G H).isLimit
    · have hG :
          (f ≫ (BinaryFan.snd (rightTripleData S F G H).cone :
            rightTriple ⟶ (pullbackPairData S G H).cone.pt)) ≫
            (BinaryFan.fst (pullbackPairData S G H).cone :
              (pullbackPairData S G H).cone.pt ⟶ G) =
          (g ≫ (BinaryFan.snd (rightTripleData S F G H).cone :
            rightTriple ⟶ (pullbackPairData S G H).cone.pt)) ≫
            (BinaryFan.fst (pullbackPairData S G H).cone :
              (pullbackPairData S G H).cone.pt ⟶ G) :=
        (rightG_comp f).symm.trans (hg.trans (rightG_comp g))
      simpa only [pair_obj_left] using hG
    · have hH :
          (f ≫ (BinaryFan.snd (rightTripleData S F G H).cone :
            rightTriple ⟶ (pullbackPairData S G H).cone.pt)) ≫
            (BinaryFan.snd (pullbackPairData S G H).cone :
              (pullbackPairData S G H).cone.pt ⟶ H) =
          (g ≫ (BinaryFan.snd (rightTripleData S F G H).cone :
            rightTriple ⟶ (pullbackPairData S G H).cone.pt)) ≫
            (BinaryFan.snd (pullbackPairData S G H).cone :
              (pullbackPairData S G H).cone.pt ⟶ H) :=
        (rightH_comp f).symm.trans (hh.trans (rightH_comp g))
      simpa only [pair_obj_right] using hH

/-- The three coordinate projections jointly determine a morphism into `rightTriple`. -/
@[ext] theorem rightTriple_hom_ext {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    {f g : X ⟶ rightTriple} (hf : f ≫ rightF = g ≫ rightF)
    (hg : f ≫ rightG = g ≫ rightG) (hh : f ≫ rightH = g ≫ rightH) : f = g :=
  rightTriple_hom_ext_of_projections hf hg hh

-- Each map is induced by the corresponding limiting binary fan, before any
-- comparison with equal-bit triples. The identities on G and H are included
-- in the two inner products as well as the two outer products.
private noncomputable def σFGMorphism :
    (pullbackPairData S F G).cone.pt ⟶ (pullbackPairData S F G).cone.pt :=
  BinaryFan.IsLimit.lift (pullbackPairData S F G).isLimit
    ((BinaryFan.fst (pullbackPairData S F G).cone) ≫ σF.hom)
    ((BinaryFan.snd (pullbackPairData S F G).cone) ≫ σG.hom)

private noncomputable def σGHMorphism :
    (pullbackPairData S G H).cone.pt ⟶ (pullbackPairData S G H).cone.pt :=
  BinaryFan.IsLimit.lift (pullbackPairData S G H).isLimit
    ((BinaryFan.fst (pullbackPairData S G H).cone) ≫ σG.hom)
    ((BinaryFan.snd (pullbackPairData S G H).cone) ≫ σH.hom)

private noncomputable def σLeftMorphism : leftTriple ⟶ leftTriple :=
  BinaryFan.IsLimit.lift (leftTripleData S F G H).isLimit
    ((BinaryFan.fst (leftTripleData S F G H).cone) ≫ σFGMorphism)
    ((BinaryFan.snd (leftTripleData S F G H).cone) ≫ σH.hom)

private noncomputable def σRightMorphism : rightTriple ⟶ rightTriple :=
  BinaryFan.IsLimit.lift (rightTripleData S F G H).isLimit
    ((BinaryFan.fst (rightTripleData S F G H).cone) ≫ σF.hom)
    ((BinaryFan.snd (rightTripleData S F G H).cone) ≫ σGHMorphism)

@[reassoc (attr := simp)] private lemma σFGMorphism_f :
    σFGMorphism ≫ BinaryFan.fst (pullbackPairData S F G).cone =
      BinaryFan.fst (pullbackPairData S F G).cone ≫ σF.hom := by
  let p : (pullbackPairData S F G).cone.pt ⟶ F := BinaryFan.fst (pullbackPairData S F G).cone
  let q : (pullbackPairData S F G).cone.pt ⟶ G := BinaryFan.snd (pullbackPairData S F G).cone
  have h : (σFGMorphism ≫ p : (pullbackPairData S F G).cone.pt ⟶ F) = p ≫ σF.hom :=
    BinaryFan.IsLimit.lift_fst (W := (pullbackPairData S F G).cone.pt) (X := F) (Y := G)
      (s := (pullbackPairData S F G).cone) (pullbackPairData S F G).isLimit
      (p ≫ σF.hom) (q ≫ σG.hom)
  exact h

@[reassoc (attr := simp)] private lemma σFGMorphism_g :
    σFGMorphism ≫ BinaryFan.snd (pullbackPairData S F G).cone =
      BinaryFan.snd (pullbackPairData S F G).cone := by
  let p : (pullbackPairData S F G).cone.pt ⟶ F := BinaryFan.fst (pullbackPairData S F G).cone
  let q : (pullbackPairData S F G).cone.pt ⟶ G := BinaryFan.snd (pullbackPairData S F G).cone
  have h : (σFGMorphism ≫ q : (pullbackPairData S F G).cone.pt ⟶ G) = q ≫ σG.hom :=
    BinaryFan.IsLimit.lift_snd (W := (pullbackPairData S F G).cone.pt) (X := F) (Y := G)
      (s := (pullbackPairData S F G).cone) (pullbackPairData S F G).isLimit
      (p ≫ σF.hom) (q ≫ σG.hom)
  rw [σG_hom_identity] at h
  exact h.trans (Category.comp_id q)

@[reassoc (attr := simp)] private lemma σGHMorphism_g :
    σGHMorphism ≫ BinaryFan.fst (pullbackPairData S G H).cone =
      BinaryFan.fst (pullbackPairData S G H).cone := by
  let p : (pullbackPairData S G H).cone.pt ⟶ G := BinaryFan.fst (pullbackPairData S G H).cone
  let q : (pullbackPairData S G H).cone.pt ⟶ H := BinaryFan.snd (pullbackPairData S G H).cone
  have h : (σGHMorphism ≫ p : (pullbackPairData S G H).cone.pt ⟶ G) = p ≫ σG.hom :=
    BinaryFan.IsLimit.lift_fst (W := (pullbackPairData S G H).cone.pt) (X := G) (Y := H)
      (s := (pullbackPairData S G H).cone) (pullbackPairData S G H).isLimit
      (p ≫ σG.hom) (q ≫ σH.hom)
  rw [σG_hom_identity] at h
  exact h.trans (Category.comp_id p)

@[reassoc (attr := simp)] private lemma σGHMorphism_h :
    σGHMorphism ≫ BinaryFan.snd (pullbackPairData S G H).cone =
      BinaryFan.snd (pullbackPairData S G H).cone := by
  let p : (pullbackPairData S G H).cone.pt ⟶ G := BinaryFan.fst (pullbackPairData S G H).cone
  let q : (pullbackPairData S G H).cone.pt ⟶ H := BinaryFan.snd (pullbackPairData S G H).cone
  have h : (σGHMorphism ≫ q : (pullbackPairData S G H).cone.pt ⟶ H) = q ≫ σH.hom :=
    BinaryFan.IsLimit.lift_snd (W := (pullbackPairData S G H).cone.pt) (X := G) (Y := H)
      (s := (pullbackPairData S G H).cone) (pullbackPairData S G H).isLimit
      (p ≫ σG.hom) (q ≫ σH.hom)
  rw [σH_hom_identity] at h
  exact h.trans (Category.comp_id q)

@[reassoc (attr := simp)] private lemma σLeftMorphism_fg :
    σLeftMorphism ≫ BinaryFan.fst (leftTripleData S F G H).cone =
      BinaryFan.fst (leftTripleData S F G H).cone ≫ σFGMorphism := by
  let p : leftTriple ⟶ (pullbackPairData S F G).cone.pt :=
    BinaryFan.fst (leftTripleData S F G H).cone
  let q : leftTriple ⟶ H := BinaryFan.snd (leftTripleData S F G H).cone
  have h : (σLeftMorphism ≫ p : leftTriple ⟶ (pullbackPairData S F G).cone.pt) = p ≫ σFGMorphism :=
    BinaryFan.IsLimit.lift_fst (W := leftTriple) (X := (pullbackPairData S F G).cone.pt) (Y := H)
      (s := (leftTripleData S F G H).cone) (leftTripleData S F G H).isLimit
      (p ≫ σFGMorphism) (q ≫ σH.hom)
  exact h

@[reassoc (attr := simp)] private lemma σRightMorphism_gh :
    σRightMorphism ≫ BinaryFan.snd (rightTripleData S F G H).cone =
      BinaryFan.snd (rightTripleData S F G H).cone ≫ σGHMorphism := by
  let p : rightTriple ⟶ F := BinaryFan.fst (rightTripleData S F G H).cone
  let q : rightTriple ⟶ (pullbackPairData S G H).cone.pt :=
    BinaryFan.snd (rightTripleData S F G H).cone
  have h : (σRightMorphism ≫ q : rightTriple ⟶ (pullbackPairData S G H).cone.pt) =
      q ≫ σGHMorphism :=
    BinaryFan.IsLimit.lift_snd (W := rightTriple) (X := F) (Y := (pullbackPairData S G H).cone.pt)
      (s := (rightTripleData S F G H).cone) (rightTripleData S F G H).isLimit
      (p ≫ σF.hom) (q ≫ σGHMorphism)
  exact h

@[reassoc (attr := simp)] private lemma σLeftMorphism_f :
    σLeftMorphism ≫ leftF = leftF ≫ σF.hom := by
  let p : leftTriple ⟶ (pullbackPairData S F G).cone.pt :=
    BinaryFan.fst (leftTripleData S F G H).cone
  let q : (pullbackPairData S F G).cone.pt ⟶ F := BinaryFan.fst (pullbackPairData S F G).cone
  have h₁ : (σLeftMorphism ≫ leftF : leftTriple ⟶ F) = (σLeftMorphism ≫ p) ≫ q :=
    leftF_comp σLeftMorphism
  have h₂ : ((σLeftMorphism ≫ p) ≫ q : leftTriple ⟶ F) = (p ≫ σFGMorphism) ≫ q :=
    congrArg (fun k : leftTriple ⟶ (pullbackPairData S F G).cone.pt => k ≫ q) σLeftMorphism_fg
  have h₃ : ((p ≫ σFGMorphism) ≫ q : leftTriple ⟶ F) = p ≫ (q ≫ σF.hom) :=
    (Category.assoc p σFGMorphism q).trans
      (congrArg (fun k : (pullbackPairData S F G).cone.pt ⟶ F => p ≫ k) σFGMorphism_f)
  have h₄ : (p ≫ (q ≫ σF.hom) : leftTriple ⟶ F) = leftF ≫ σF.hom :=
    (Category.assoc p q σF.hom).symm
  exact h₁.trans (h₂.trans (h₃.trans h₄))

@[reassoc (attr := simp)] private lemma σLeftMorphism_g :
    σLeftMorphism ≫ leftG = leftG := by
  let p : leftTriple ⟶ (pullbackPairData S F G).cone.pt :=
    BinaryFan.fst (leftTripleData S F G H).cone
  let q : (pullbackPairData S F G).cone.pt ⟶ G := BinaryFan.snd (pullbackPairData S F G).cone
  have h₁ : (σLeftMorphism ≫ leftG : leftTriple ⟶ G) = (σLeftMorphism ≫ p) ≫ q :=
    leftG_comp σLeftMorphism
  have h₂ : ((σLeftMorphism ≫ p) ≫ q : leftTriple ⟶ G) = (p ≫ σFGMorphism) ≫ q :=
    congrArg (fun k : leftTriple ⟶ (pullbackPairData S F G).cone.pt => k ≫ q) σLeftMorphism_fg
  have h₃ : ((p ≫ σFGMorphism) ≫ q : leftTriple ⟶ G) = p ≫ q :=
    (Category.assoc p σFGMorphism q).trans
      (congrArg (fun k : (pullbackPairData S F G).cone.pt ⟶ G => p ≫ k) σFGMorphism_g)
  have h₄ : (p ≫ q : leftTriple ⟶ G) = leftG := rfl
  exact h₁.trans (h₂.trans (h₃.trans h₄))

@[reassoc (attr := simp)] private lemma σLeftMorphism_h :
    σLeftMorphism ≫ leftH = leftH := by
  let p : leftTriple ⟶ (pullbackPairData S F G).cone.pt :=
    BinaryFan.fst (leftTripleData S F G H).cone
  let q : leftTriple ⟶ H := BinaryFan.snd (leftTripleData S F G H).cone
  have h : (σLeftMorphism ≫ q : leftTriple ⟶ H) = q ≫ σH.hom :=
    BinaryFan.IsLimit.lift_snd (W := leftTriple) (X := (pullbackPairData S F G).cone.pt) (Y := H)
      (s := (leftTripleData S F G H).cone) (leftTripleData S F G H).isLimit
      (p ≫ σFGMorphism) (q ≫ σH.hom)
  rw [σH_hom_identity] at h
  exact h.trans (Category.comp_id q)

@[reassoc (attr := simp)] private lemma σRightMorphism_f :
    σRightMorphism ≫ rightF = rightF ≫ σF.hom := by
  let p : rightTriple ⟶ F := BinaryFan.fst (rightTripleData S F G H).cone
  let q : rightTriple ⟶ (pullbackPairData S G H).cone.pt :=
    BinaryFan.snd (rightTripleData S F G H).cone
  have h : (σRightMorphism ≫ p : rightTriple ⟶ F) = p ≫ σF.hom :=
    BinaryFan.IsLimit.lift_fst (W := rightTriple) (X := F) (Y := (pullbackPairData S G H).cone.pt)
      (s := (rightTripleData S F G H).cone) (rightTripleData S F G H).isLimit
      (p ≫ σF.hom) (q ≫ σGHMorphism)
  exact h

@[reassoc (attr := simp)] private lemma σRightMorphism_g :
    σRightMorphism ≫ rightG = rightG := by
  let p : rightTriple ⟶ (pullbackPairData S G H).cone.pt :=
    BinaryFan.snd (rightTripleData S F G H).cone
  let q : (pullbackPairData S G H).cone.pt ⟶ G := BinaryFan.fst (pullbackPairData S G H).cone
  have h₁ : (σRightMorphism ≫ rightG : rightTriple ⟶ G) = (σRightMorphism ≫ p) ≫ q :=
    rightG_comp σRightMorphism
  have h₂ : ((σRightMorphism ≫ p) ≫ q : rightTriple ⟶ G) = (p ≫ σGHMorphism) ≫ q :=
    congrArg (fun k : rightTriple ⟶ (pullbackPairData S G H).cone.pt => k ≫ q) σRightMorphism_gh
  have h₃ : ((p ≫ σGHMorphism) ≫ q : rightTriple ⟶ G) = p ≫ q :=
    (Category.assoc p σGHMorphism q).trans
      (congrArg (fun k : (pullbackPairData S G H).cone.pt ⟶ G => p ≫ k) σGHMorphism_g)
  have h₄ : (p ≫ q : rightTriple ⟶ G) = rightG := rfl
  exact h₁.trans (h₂.trans (h₃.trans h₄))

@[reassoc (attr := simp)] private lemma σRightMorphism_h :
    σRightMorphism ≫ rightH = rightH := by
  let p : rightTriple ⟶ (pullbackPairData S G H).cone.pt :=
    BinaryFan.snd (rightTripleData S F G H).cone
  let q : (pullbackPairData S G H).cone.pt ⟶ H := BinaryFan.snd (pullbackPairData S G H).cone
  have h₁ : (σRightMorphism ≫ rightH : rightTriple ⟶ H) = (σRightMorphism ≫ p) ≫ q :=
    rightH_comp σRightMorphism
  have h₂ : ((σRightMorphism ≫ p) ≫ q : rightTriple ⟶ H) = (p ≫ σGHMorphism) ≫ q :=
    congrArg (fun k : rightTriple ⟶ (pullbackPairData S G H).cone.pt => k ≫ q) σRightMorphism_gh
  have h₃ : ((p ≫ σGHMorphism) ≫ q : rightTriple ⟶ H) = p ≫ q :=
    (Category.assoc p σGHMorphism q).trans
      (congrArg (fun k : (pullbackPairData S G H).cone.pt ⟶ H => p ≫ k) σGHMorphism_h)
  have h₄ : (p ≫ q : rightTriple ⟶ H) = rightH := rfl
  exact h₁.trans (h₂.trans (h₃.trans h₄))

private lemma σLeftMorphism_square : σLeftMorphism ≫ σLeftMorphism = 𝟙 leftTriple := by
  apply leftTriple_hom_ext
  · simp [Category.assoc, σF_involution]
  · simp [Category.assoc]
  · simp [Category.assoc]

private lemma σRightMorphism_square : σRightMorphism ≫ σRightMorphism = 𝟙 rightTriple := by
  apply rightTriple_hom_ext
  · simp [Category.assoc, σF_involution]
  · simp [Category.assoc]
  · simp [Category.assoc]

/-- The product involution of the left-associated diagram induced by `σF` and identities. -/
noncomputable def σL : leftTriple ≅ leftTriple where
  hom := σLeftMorphism
  inv := σLeftMorphism
  hom_inv_id := σLeftMorphism_square
  inv_hom_id := σLeftMorphism_square

/-- The product involution of the right-associated diagram induced by `σF` and identities. -/
noncomputable def σR : rightTriple ≅ rightTriple where
  hom := σRightMorphism
  inv := σRightMorphism
  hom_inv_id := σRightMorphism_square
  inv_hom_id := σRightMorphism_square

/-- The left product involution acts by `σF` on the first coordinate. -/
@[reassoc (attr := simp)] theorem σL_hom_f : σL.hom ≫ leftF = leftF ≫ σF.hom :=
  σLeftMorphism_f

/-- The left product involution fixes the middle coordinate. -/
@[reassoc (attr := simp)] theorem σL_hom_g : σL.hom ≫ leftG = leftG :=
  σLeftMorphism_g

/-- The left product involution fixes the last coordinate. -/
@[reassoc (attr := simp)] theorem σL_hom_h : σL.hom ≫ leftH = leftH :=
  σLeftMorphism_h

/-- The right product involution acts by `σF` on the first coordinate. -/
@[reassoc (attr := simp)] theorem σR_hom_f : σR.hom ≫ rightF = rightF ≫ σF.hom :=
  σRightMorphism_f

/-- The right product involution fixes the middle coordinate. -/
@[reassoc (attr := simp)] theorem σR_hom_g : σR.hom ≫ rightG = rightG :=
  σRightMorphism_g

/-- The right product involution fixes the last coordinate. -/
@[reassoc (attr := simp)] theorem σR_hom_h : σR.hom ≫ rightH = rightH :=
  σRightMorphism_h

private lemma σL_inv_hom_characteristic : σL.inv = σL.hom := rfl

private lemma σR_inv_hom_characteristic : σR.inv = σR.hom := rfl

/-- The left product involution is its own inverse. -/
@[simp] theorem σL_inv_eq_hom : σL.inv = σL.hom := σL_inv_hom_characteristic

/-- The right product involution is its own inverse. -/
@[simp] theorem σR_inv_eq_hom : σR.inv = σR.hom := σR_inv_hom_characteristic

/-- Applying the left product involution twice gives the identity. -/
@[simp] theorem σL_involution : σL.hom ≫ σL.hom = 𝟙 leftTriple := σLeftMorphism_square

/-- Applying the right product involution twice gives the identity. -/
@[simp] theorem σR_involution : σR.hom ≫ σR.hom = 𝟙 rightTriple := σRightMorphism_square

/-- The associator intertwines the two product involutions. -/
@[reassoc] theorem associator_hom_equivariance :
    σL.hom ≫ associator.hom = associator.hom ≫ σR.hom := by
  apply rightTriple_hom_ext
  · simp only [Category.assoc, associator_hom_f, associator_hom_f_assoc,
      σL_hom_f, σR_hom_f]
  · simp only [Category.assoc, associator_hom_g, σL_hom_g, σR_hom_g]
  · simp only [Category.assoc, associator_hom_h, σL_hom_h, σR_hom_h]

/-- The inverse associator intertwines the two product involutions. -/
@[reassoc] theorem associator_inv_equivariance :
    σR.hom ≫ associator.inv = associator.inv ≫ σL.hom := by
  apply leftTriple_hom_ext
  · simp only [Category.assoc, associator_inv_f, associator_inv_f_assoc,
      σR_hom_f, σL_hom_f]
  · simp only [Category.assoc, associator_inv_g, σR_hom_g, σL_hom_g]
  · simp only [Category.assoc, associator_inv_h, σR_hom_h, σL_hom_h]

/-- The left product involution is natural on the nonidentity index arrow. -/
theorem σL_hom_naturality :
    leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) ≫ σL.hom.app 1 =
      σL.hom.app 0 ≫ leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) :=
  σL.hom.naturality _

/-- The inverse left product involution is natural on the nonidentity index arrow. -/
theorem σL_inv_naturality :
    leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) ≫ σL.inv.app 1 =
      σL.inv.app 0 ≫ leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) :=
  σL.inv.naturality _

/-- The right product involution is natural on the nonidentity index arrow. -/
theorem σR_hom_naturality :
    rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) ≫ σR.hom.app 1 =
      σR.hom.app 0 ≫ rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) :=
  σR.hom.naturality _

/-- The inverse right product involution is natural on the nonidentity index arrow. -/
theorem σR_inv_naturality :
    rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) ≫ σR.inv.app 1 =
      σR.inv.app 0 ≫ rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) :=
  σR.inv.naturality _

private lemma σL_coordinates (j : Fin 2) (p : (leftTriple.obj j).left) :
    (leftTripleCoordinates j).hom.left ((σL.hom.app j).left p) =
      tripleSwap j ((leftTripleCoordinates j).hom.left p) := by
  apply Subtype.ext
  apply Prod.ext
  · change ((leftTripleCoordinates j).hom.left ((σL.hom.app j).left p)).val.1 =
      (σF.hom.app j).left ((leftTripleCoordinates j).hom.left p).val.1
    rw [leftTripleCoordinates_hom_f, leftTripleCoordinates_hom_f]
    exact ConcreteCategory.congr_hom
      (congrArg Over.Hom.left (congr_app σL_hom_f j)) p
  · apply Prod.ext
    · change ((leftTripleCoordinates j).hom.left ((σL.hom.app j).left p)).val.2.1 =
        ((leftTripleCoordinates j).hom.left p).val.2.1
      rw [leftTripleCoordinates_hom_g, leftTripleCoordinates_hom_g]
      exact ConcreteCategory.congr_hom
        (congrArg Over.Hom.left (congr_app σL_hom_g j)) p
    · change ((leftTripleCoordinates j).hom.left ((σL.hom.app j).left p)).val.2.2 =
        ((leftTripleCoordinates j).hom.left p).val.2.2
      rw [leftTripleCoordinates_hom_h, leftTripleCoordinates_hom_h]
      exact ConcreteCategory.congr_hom
        (congrArg Over.Hom.left (congr_app σL_hom_h j)) p

private lemma σR_coordinates (j : Fin 2) (p : (rightTriple.obj j).left) :
    (rightTripleCoordinates j).hom.left ((σR.hom.app j).left p) =
      tripleSwap j ((rightTripleCoordinates j).hom.left p) := by
  apply Subtype.ext
  apply Prod.ext
  · change ((rightTripleCoordinates j).hom.left ((σR.hom.app j).left p)).val.1 =
      (σF.hom.app j).left ((rightTripleCoordinates j).hom.left p).val.1
    rw [rightTripleCoordinates_hom_f, rightTripleCoordinates_hom_f]
    exact ConcreteCategory.congr_hom
      (congrArg Over.Hom.left (congr_app σR_hom_f j)) p
  · apply Prod.ext
    · change ((rightTripleCoordinates j).hom.left ((σR.hom.app j).left p)).val.2.1 =
        ((rightTripleCoordinates j).hom.left p).val.2.1
      rw [rightTripleCoordinates_hom_g, rightTripleCoordinates_hom_g]
      exact ConcreteCategory.congr_hom
        (congrArg Over.Hom.left (congr_app σR_hom_g j)) p
    · change ((rightTripleCoordinates j).hom.left ((σR.hom.app j).left p)).val.2.2 =
        ((rightTripleCoordinates j).hom.left p).val.2.2
      rw [rightTripleCoordinates_hom_h, rightTripleCoordinates_hom_h]
      exact ConcreteCategory.congr_hom
        (congrArg Over.Hom.left (congr_app σR_hom_h j)) p

/-- On every left-associated point, the involution changes only its first coordinate. -/
theorem σL_hom_apply (j : Fin 2) (p : (leftTriple.obj j).left) :
    ((leftTripleCoordinates j).hom.left ((σL.hom.app j).left p)).val =
      ((σF.hom.app j).left ((leftTripleCoordinates j).hom.left p).val.1,
        ((leftTripleCoordinates j).hom.left p).val.2.1,
        ((leftTripleCoordinates j).hom.left p).val.2.2) :=
  congrArg Subtype.val (σL_coordinates j p)

/-- On every right-associated point, the involution changes only its first coordinate. -/
theorem σR_hom_apply (j : Fin 2) (p : (rightTriple.obj j).left) :
    ((rightTripleCoordinates j).hom.left ((σR.hom.app j).left p)).val =
      ((σF.hom.app j).left ((rightTripleCoordinates j).hom.left p).val.1,
        ((rightTripleCoordinates j).hom.left p).val.2.1,
        ((rightTripleCoordinates j).hom.left p).val.2.2) :=
  congrArg Subtype.val (σR_coordinates j p)

private lemma σL_moved_iff (j : Fin 2) (p : (leftTriple.obj j).left) :
    (σL.hom.app j).left p ≠ p ↔
      tripleSwap j ((leftTripleCoordinates j).hom.left p) ≠
        (leftTripleCoordinates j).hom.left p := by
  rw [← σL_coordinates]
  exact not_congr ((Over.forget S).mapIso (leftTripleCoordinates j)).toEquiv.injective.eq_iff.symm

private lemma σR_moved_iff (j : Fin 2) (p : (rightTriple.obj j).left) :
    (σR.hom.app j).left p ≠ p ↔
      tripleSwap j ((rightTripleCoordinates j).hom.left p) ≠
        (rightTripleCoordinates j).hom.left p := by
  rw [← σR_coordinates]
  exact not_congr ((Over.forget S).mapIso (rightTripleCoordinates j)).toEquiv.injective.eq_iff.symm

/-- Among the fourteen source points, precisely those with first coordinate 0 or 1 move. -/
theorem σL_moves_zero_iff (p : (leftTriple.obj 0).left) :
    (σL.hom.app 0).left p ≠ p ↔
      ((leftTripleCoordinates 0).hom.left p).val.1 = (0 : Fin 3) ∨
        ((leftTripleCoordinates 0).hom.left p).val.1 = (1 : Fin 3) :=
  (σL_moved_iff 0 p).trans (tripleSwapZero_moves_iff _)

/-- Among the eighteen target points, precisely those with first coordinate 0 or 1 move. -/
theorem σL_moves_one_iff (p : (leftTriple.obj 1).left) :
    (σL.hom.app 1).left p ≠ p ↔
      ((leftTripleCoordinates 1).hom.left p).val.1 = (0 : Fin 4) ∨
        ((leftTripleCoordinates 1).hom.left p).val.1 = (1 : Fin 4) :=
  (σL_moved_iff 1 p).trans (tripleSwapOne_moves_iff _)

/-- The right-associated source has the same moved-point criterion in its chosen coordinates. -/
theorem σR_moves_zero_iff (p : (rightTriple.obj 0).left) :
    (σR.hom.app 0).left p ≠ p ↔
      ((rightTripleCoordinates 0).hom.left p).val.1 = (0 : Fin 3) ∨
        ((rightTripleCoordinates 0).hom.left p).val.1 = (1 : Fin 3) :=
  (σR_moved_iff 0 p).trans (tripleSwapZero_moves_iff _)

/-- The right-associated target has the same moved-point criterion in its chosen coordinates. -/
theorem σR_moves_one_iff (p : (rightTriple.obj 1).left) :
    (σR.hom.app 1).left p ≠ p ↔
      ((rightTripleCoordinates 1).hom.left p).val.1 = (0 : Fin 4) ∨
        ((rightTripleCoordinates 1).hom.left p).val.1 = (1 : Fin 4) :=
  (σR_moved_iff 1 p).trans (tripleSwapOne_moves_iff _)

/-- The left product involution moves eight source points and six target points. -/
theorem σL_moved_cards :
    Nat.card {p : (leftTriple.obj 0).left // (σL.hom.app 0).left p ≠ p} = 8 ∧
      Nat.card {p : (leftTriple.obj 1).left // (σL.hom.app 1).left p ≠ p} = 6 := by
  constructor
  · calc
      Nat.card {p : (leftTriple.obj 0).left // (σL.hom.app 0).left p ≠ p} =
          Nat.card {q : Triple 0 // tripleSwap 0 q ≠ q} :=
        Nat.card_congr (((Over.forget S).mapIso (leftTripleCoordinates 0)).toEquiv.subtypeEquiv
          (σL_moved_iff 0))
      _ = 8 := by rw [Nat.card_eq_fintype_card]; exact tripleSwap_moved_cards.1
  · calc
      Nat.card {p : (leftTriple.obj 1).left // (σL.hom.app 1).left p ≠ p} =
          Nat.card {q : Triple 1 // tripleSwap 1 q ≠ q} :=
        Nat.card_congr (((Over.forget S).mapIso (leftTripleCoordinates 1)).toEquiv.subtypeEquiv
          (σL_moved_iff 1))
      _ = 6 := by rw [Nat.card_eq_fintype_card]; exact tripleSwap_moved_cards.2

/-- The right product involution moves eight source points and six target points. -/
theorem σR_moved_cards :
    Nat.card {p : (rightTriple.obj 0).left // (σR.hom.app 0).left p ≠ p} = 8 ∧
      Nat.card {p : (rightTriple.obj 1).left // (σR.hom.app 1).left p ≠ p} = 6 := by
  constructor
  · calc
      Nat.card {p : (rightTriple.obj 0).left // (σR.hom.app 0).left p ≠ p} =
          Nat.card {q : Triple 0 // tripleSwap 0 q ≠ q} :=
        Nat.card_congr (((Over.forget S).mapIso (rightTripleCoordinates 0)).toEquiv.subtypeEquiv
          (σR_moved_iff 0))
      _ = 8 := by rw [Nat.card_eq_fintype_card]; exact tripleSwap_moved_cards.1
  · calc
      Nat.card {p : (rightTriple.obj 1).left // (σR.hom.app 1).left p ≠ p} =
          Nat.card {q : Triple 1 // tripleSwap 1 q ≠ q} :=
        Nat.card_congr (((Over.forget S).mapIso (rightTripleCoordinates 1)).toEquiv.subtypeEquiv
          (σR_moved_iff 1))
      _ = 6 := by rw [Nat.card_eq_fintype_card]; exact tripleSwap_moved_cards.2

/-- The left product involution is not the identity transformation. -/
theorem σL_nonidentity : σL.hom ≠ 𝟙 leftTriple := by
  intro h
  let p := (leftTripleCoordinates 0).inv.left tripleCollisionZero
  have hp : (leftTripleCoordinates 0).hom.left p = tripleCollisionZero :=
    ConcreteCategory.congr_hom (Over.inv_left_hom_left (leftTripleCoordinates 0)) _
  have hm := (σL_moves_zero_iff p).2 (Or.inl (by rw [hp]; rfl))
  apply hm
  rw [h]
  rfl

/-- The right product involution is not the identity transformation. -/
theorem σR_nonidentity : σR.hom ≠ 𝟙 rightTriple := by
  intro h
  let p := (rightTripleCoordinates 0).inv.left tripleCollisionZero
  have hp : (rightTripleCoordinates 0).hom.left p = tripleCollisionZero :=
    ConcreteCategory.congr_hom (Over.inv_left_hom_left (rightTripleCoordinates 0)) _
  have hm := (σR_moves_zero_iff p).2 (Or.inl (by rw [hp]; rfl))
  apply hm
  rw [h]
  rfl

/-! ## The two top-level product projections -/

/-- The inner product of the finite diagrams `F` and `G`, with its selected cone. -/
noncomputable def fgPair : Fin 2 ⥤ Over (Fin 2 : Type) :=
  (pullbackPairData S F G).cone.pt

/-- The inner product of the finite diagrams `G` and `H`, with its selected cone. -/
noncomputable def ghPair : Fin 2 ⥤ Over (Fin 2 : Type) :=
  (pullbackPairData S G H).cone.pt

/-- The first projection of `fgPair`. -/
noncomputable def fgF : fgPair ⟶ F := (BinaryFan.fst (pullbackPairData S F G).cone)

/-- The second projection of `fgPair`. -/
noncomputable def fgG : fgPair ⟶ G := (BinaryFan.snd (pullbackPairData S F G).cone)

/-- The first projection of `ghPair`. -/
noncomputable def ghG : ghPair ⟶ G := (BinaryFan.fst (pullbackPairData S G H).cone)

/-- The second projection of `ghPair`. -/
noncomputable def ghH : ghPair ⟶ H := (BinaryFan.snd (pullbackPairData S G H).cone)

/-- The projections jointly determine a morphism into `fgPair`. -/
@[ext] theorem fgPair_hom_ext {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    {f g : X ⟶ fgPair} (hF : f ≫ fgF = g ≫ fgF) (hG : f ≫ fgG = g ≫ fgG) : f = g :=
  BinaryFan.IsLimit.hom_ext (pullbackPairData S F G).isLimit hF hG

/-- The projections jointly determine a morphism into `ghPair`. -/
@[ext] theorem ghPair_hom_ext {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    {f g : X ⟶ ghPair} (hG : f ≫ ghG = g ≫ ghG) (hH : f ≫ ghH = g ≫ ghH) : f = g :=
  BinaryFan.IsLimit.hom_ext (pullbackPairData S G H).isLimit hG hH

/-- The unique joint lift into the finite product `fgPair`. -/
noncomputable def fgLift {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (f : X ⟶ F) (g : X ⟶ G) : X ⟶ fgPair :=
  BinaryFan.IsLimit.lift (pullbackPairData S F G).isLimit f g

/-- The unique joint lift into the finite product `ghPair`. -/
noncomputable def ghLift {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (g : X ⟶ G) (h : X ⟶ H) : X ⟶ ghPair :=
  BinaryFan.IsLimit.lift (pullbackPairData S G H).isLimit g h

/-- The joint lift into `fgPair` has the specified first projection. -/
@[reassoc (attr := simp)] theorem fgLift_f {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (f : X ⟶ F) (g : X ⟶ G) : fgLift f g ≫ fgF = f :=
  BinaryFan.IsLimit.lift_fst (pullbackPairData S F G).isLimit f g

/-- The joint lift into `fgPair` has the specified second projection. -/
@[reassoc (attr := simp)] theorem fgLift_g {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (f : X ⟶ F) (g : X ⟶ G) : fgLift f g ≫ fgG = g :=
  BinaryFan.IsLimit.lift_snd (pullbackPairData S F G).isLimit f g

/-- The joint lift into `ghPair` has the specified first projection. -/
@[reassoc (attr := simp)] theorem ghLift_g {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (g : X ⟶ G) (h : X ⟶ H) : ghLift g h ≫ ghG = g :=
  BinaryFan.IsLimit.lift_fst (pullbackPairData S G H).isLimit g h

/-- The joint lift into `ghPair` has the specified second projection. -/
@[reassoc (attr := simp)] theorem ghLift_h {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (g : X ⟶ G) (h : X ⟶ H) : ghLift g h ≫ ghH = h :=
  BinaryFan.IsLimit.lift_snd (pullbackPairData S G H).isLimit g h

/-- A morphism with prescribed projections equals the joint lift into `fgPair`. -/
theorem fgLift_unique {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (f : X ⟶ F) (g : X ⟶ G) (m : X ⟶ fgPair)
    (hF : m ≫ fgF = f) (hG : m ≫ fgG = g) : m = fgLift f g :=
  fgPair_hom_ext (hF.trans (fgLift_f f g).symm) (hG.trans (fgLift_g f g).symm)

/-- A morphism with prescribed projections equals the joint lift into `ghPair`. -/
theorem ghLift_unique {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (g : X ⟶ G) (h : X ⟶ H) (m : X ⟶ ghPair)
    (hG : m ≫ ghG = g) (hH : m ≫ ghH = h) : m = ghLift g h :=
  ghPair_hom_ext (hG.trans (ghLift_g g h).symm) (hH.trans (ghLift_h g h).symm)

/-- The inner-pair projection of the left-associated diagram. -/
noncomputable def leftFG : leftTriple ⟶ fgPair := (BinaryFan.fst (leftTripleData S F G H).cone)

/-- The inner-pair projection of the right-associated diagram. -/
noncomputable def rightGH : rightTriple ⟶ ghPair := (BinaryFan.snd (rightTripleData S F G H).cone)

private lemma leftFG_f_characteristic : leftFG ≫ fgF = leftF := rfl

private lemma leftFG_g_characteristic : leftFG ≫ fgG = leftG := rfl

private lemma rightGH_g_characteristic : rightGH ≫ ghG = rightG := rfl

private lemma rightGH_h_characteristic : rightGH ≫ ghH = rightH := rfl

/-- The first coordinate of the left inner-pair projection. -/
@[reassoc (attr := simp)] theorem leftFG_f : leftFG ≫ fgF = leftF := leftFG_f_characteristic

/-- The second coordinate of the left inner-pair projection. -/
@[reassoc (attr := simp)] theorem leftFG_g : leftFG ≫ fgG = leftG := leftFG_g_characteristic

/-- The first coordinate of the right inner-pair projection. -/
@[reassoc (attr := simp)] theorem rightGH_g : rightGH ≫ ghG = rightG := rightGH_g_characteristic

/-- The second coordinate of the right inner-pair projection. -/
@[reassoc (attr := simp)] theorem rightGH_h : rightGH ≫ ghH = rightH := rightGH_h_characteristic

/-- The unique joint lift into the left-associated finite product. -/
noncomputable def leftLift {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (a : X ⟶ fgPair) (h : X ⟶ H) : X ⟶ leftTriple :=
  BinaryFan.IsLimit.lift (leftTripleData S F G H).isLimit a h

/-- The unique joint lift into the right-associated finite product. -/
noncomputable def rightLift {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (f : X ⟶ F) (b : X ⟶ ghPair) : X ⟶ rightTriple :=
  BinaryFan.IsLimit.lift (rightTripleData S F G H).isLimit f b

/-- The joint lift into `leftTriple` has the specified inner-pair projection. -/
@[reassoc (attr := simp)] theorem leftLift_fg {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (a : X ⟶ fgPair) (h : X ⟶ H) : leftLift a h ≫ leftFG = a :=
  BinaryFan.IsLimit.lift_fst (leftTripleData S F G H).isLimit a h

/-- The joint lift into `leftTriple` has the specified last projection. -/
@[reassoc (attr := simp)] theorem leftLift_h {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (a : X ⟶ fgPair) (h : X ⟶ H) : leftLift a h ≫ leftH = h :=
  BinaryFan.IsLimit.lift_snd (leftTripleData S F G H).isLimit a h

/-- The joint lift into `rightTriple` has the specified first projection. -/
@[reassoc (attr := simp)] theorem rightLift_f {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (f : X ⟶ F) (b : X ⟶ ghPair) : rightLift f b ≫ rightF = f :=
  BinaryFan.IsLimit.lift_fst (rightTripleData S F G H).isLimit f b

/-- The joint lift into `rightTriple` has the specified inner-pair projection. -/
@[reassoc (attr := simp)] theorem rightLift_gh {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (f : X ⟶ F) (b : X ⟶ ghPair) : rightLift f b ≫ rightGH = b :=
  BinaryFan.IsLimit.lift_snd (rightTripleData S F G H).isLimit f b

/-- The two outer projections jointly determine a morphism into `leftTriple`. -/
@[ext] theorem leftTriple_hom_ext_outer {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    {f g : X ⟶ leftTriple} (hFG : f ≫ leftFG = g ≫ leftFG)
    (hH : f ≫ leftH = g ≫ leftH) : f = g :=
  BinaryFan.IsLimit.hom_ext (leftTripleData S F G H).isLimit hFG hH

/-- The two outer projections jointly determine a morphism into `rightTriple`. -/
@[ext] theorem rightTriple_hom_ext_outer {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    {f g : X ⟶ rightTriple} (hF : f ≫ rightF = g ≫ rightF)
    (hGH : f ≫ rightGH = g ≫ rightGH) : f = g :=
  BinaryFan.IsLimit.hom_ext (rightTripleData S F G H).isLimit hF hGH

/-- A morphism with prescribed outer projections equals the left joint lift. -/
theorem leftLift_unique {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (a : X ⟶ fgPair) (h : X ⟶ H) (m : X ⟶ leftTriple)
    (hFG : m ≫ leftFG = a) (hH : m ≫ leftH = h) : m = leftLift a h :=
  leftTriple_hom_ext_outer (hFG.trans (leftLift_fg a h).symm)
    (hH.trans (leftLift_h a h).symm)

/-- A morphism with prescribed outer projections equals the right joint lift. -/
theorem rightLift_unique {X : Fin 2 ⥤ Over (Fin 2 : Type)}
    (f : X ⟶ F) (b : X ⟶ ghPair) (m : X ⟶ rightTriple)
    (hF : m ≫ rightF = f) (hGH : m ≫ rightGH = b) : m = rightLift f b :=
  rightTriple_hom_ext_outer (hF.trans (rightLift_f f b).symm)
    (hGH.trans (rightLift_gh f b).symm)

/-- The associator's two top-level projections are the first coordinate and the GH joint lift. -/
theorem associator_hom_projections :
    (associator.hom ≫ rightF = leftF) ∧
      (associator.hom ≫ rightGH = ghLift leftG leftH) := by
  refine ⟨associator_hom_f, ?_⟩
  apply ghLift_unique
  · simpa only [Category.assoc, rightGH_g] using associator_hom_g
  · simpa only [Category.assoc, rightGH_h] using associator_hom_h

/-- The inverse associator's two top-level projections are the FG joint lift and last coordinate. -/
theorem associator_inv_projections :
    (associator.inv ≫ leftFG = fgLift rightF rightG) ∧
      (associator.inv ≫ leftH = rightH) := by
  refine ⟨?_, associator_inv_h⟩
  apply fgLift_unique
  · simpa only [Category.assoc, leftFG_f] using associator_inv_f
  · simpa only [Category.assoc, leftFG_g] using associator_inv_g

/-- The associator is the outer joint lift of its first coordinate and inner GH lift. -/
theorem associator_hom_eq_rightLift :
    associator.hom = rightLift leftF (ghLift leftG leftH) :=
  rightLift_unique leftF (ghLift leftG leftH) associator.hom
    associator_hom_projections.1 associator_hom_projections.2

/-- The inverse associator is the outer joint lift of its inner FG lift and last coordinate. -/
theorem associator_inv_eq_leftLift :
    associator.inv = leftLift (fgLift rightF rightG) rightH :=
  leftLift_unique (fgLift rightF rightG) rightH associator.inv
    associator_inv_projections.1 associator_inv_projections.2

end CategoryTheory.FiniteDiagram

namespace CategoryTheory.FiniteDiagram

/-! ## Images and fibers of the triple transition

The natural coordinate comparisons transport the image and every fiber of each
associated diagram to the same equal-bit triple transition. Missing targets have
first coordinate `3` or middle coordinate `1`; among the remaining targets, the
last coordinate distinguishes double fibers from singleton fibers.
-/

private lemma tripleStatistics_image_card :
    Nat.card (Set.range (tripleDiagram.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left) = 10 := by
  change Nat.card {q : triplePoints 1 // ∃ p, tripleStep p = q} = 10
  rw [Nat.subtype_card (p := fun q : triplePoints 1 => ∃ p, tripleStep p = q)
    (Finset.univ.image tripleStep) (by
      intro q
      constructor
      · intro hq
        obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hq
        exact ⟨p, hp⟩
      · rintro ⟨p, hp⟩
        exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hp⟩)]
  exact transition_image_cards.2.2

private lemma tripleStatistics_fiber_card (q : Triple 1) :
    Nat.card {p : Triple 0 // (tripleDiagram.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} =
      @ite ℕ (Eq (α := Fin 4) q.val.1 3 ∨ Eq (α := Fin 5) q.val.2.1 1)
        (decidable_of_iff (q.val.1.val = 3 ∨ q.val.2.1.val = 1)
          (or_congr (show q.val.1.val = (3 : Fin 4).val ↔
                q.val.1 = (3 : Fin 4) from
              (Fin.val_injective (n := 4)).eq_iff
                (a := q.val.1) (b := (3 : Fin 4)))
            (show q.val.2.1.val = (1 : Fin 5).val ↔ q.val.2.1 = (1 : Fin 5) from
              (Fin.val_injective (n := 5)).eq_iff
                (a := q.val.2.1) (b := (1 : Fin 5)))))
        0 (@ite ℕ (Eq (α := Fin 4) q.val.2.2 0)
          (decidable_of_iff (q.val.2.2.val = 0)
            (show q.val.2.2.val = (0 : Fin 4).val ↔ q.val.2.2 = (0 : Fin 4) from
              (Fin.val_injective (n := 4)).eq_iff
                (a := q.val.2.2) (b := (0 : Fin 4)))) 2 1) := by
  change Nat.card {p : triplePoints 0 // tripleStep p = q} = _
  rw [Nat.card_eq_fintype_card]
  exact (show ∀ q : triplePoints 1,
    Fintype.card {p : triplePoints 0 // tripleStep p = q} =
      @ite ℕ (Eq (α := Fin 4) q.val.1 3 ∨ Eq (α := Fin 5) q.val.2.1 1)
        (decidable_of_iff (q.val.1.val = 3 ∨ q.val.2.1.val = 1)
          (or_congr (show q.val.1.val = (3 : Fin 4).val ↔
                q.val.1 = (3 : Fin 4) from
              (Fin.val_injective (n := 4)).eq_iff
                (a := q.val.1) (b := (3 : Fin 4)))
            (show q.val.2.1.val = (1 : Fin 5).val ↔ q.val.2.1 = (1 : Fin 5) from
              (Fin.val_injective (n := 5)).eq_iff
                (a := q.val.2.1) (b := (1 : Fin 5)))))
        0 (@ite ℕ (Eq (α := Fin 4) q.val.2.2 0)
          (decidable_of_iff (q.val.2.2.val = 0)
            (show q.val.2.2.val = (0 : Fin 4).val ↔ q.val.2.2 = (0 : Fin 4) from
              (Fin.val_injective (n := 4)).eq_iff
                (a := q.val.2.2) (b := (0 : Fin 4)))) 2 1)
    from by decide) q

private lemma tripleStatistics_fiber_counts :
    Nat.card {q : Triple 1 // Nat.card {p : Triple 0 // (tripleDiagram.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = 2} = 4 ∧
    Nat.card {q : Triple 1 // Nat.card {p : Triple 0 // (tripleDiagram.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = 1} = 6 ∧
    Nat.card {q : Triple 1 // Nat.card {p : Triple 0 // (tripleDiagram.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = 0} = 8 := by
  change Nat.card {q : triplePoints 1 // Nat.card {p : triplePoints 0 //
      tripleStep p = q} = 2} = 4 ∧
    Nat.card {q : triplePoints 1 // Nat.card {p : triplePoints 0 //
      tripleStep p = q} = 1} = 6 ∧
    Nat.card {q : triplePoints 1 // Nat.card {p : triplePoints 0 //
      tripleStep p = q} = 0} = 8
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using tripleStep_fibers

private lemma tripleStatistics_missing_card :
    Nat.card {q : Triple 1 // ¬ ∃ p : Triple 0, (tripleDiagram.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = 8 := by
  classical
  have hzero (q : Triple 1) :
      (¬ ∃ p : Triple 0, (tripleDiagram.map
        (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q) ↔
      Nat.card {p : Triple 0 // (tripleDiagram.map
        (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = 0 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
    constructor
    · intro h
      exact ⟨fun p => h ⟨p.val, p.property⟩⟩
    · intro h hp
      obtain ⟨p, hp⟩ := hp
      exact @IsEmpty.false _ h ⟨p, hp⟩
  exact (Nat.card_congr (Equiv.subtypeEquivRight hzero)).trans
    tripleStatistics_fiber_counts.2.2

private lemma leftStatistics_equiv_apply (j : Fin 2) (p : (leftTriple.obj j).left) :
    (((Over.forget (Fin 2)).mapIso (leftTripleCoordinateNatIso.app j)).toEquiv p : Triple j) =
      (leftTripleCoordinates j).hom.left p := by
  have hforget :
      (((Over.forget (Fin 2 : Type)).mapIso
        (leftTripleCoordinateNatIso.app j)).hom :
          (leftTriple.obj j).left ⟶ Triple j) =
      (leftTripleCoordinateNatIso.app j).hom.left :=
    (Functor.mapIso_hom (Over.forget (Fin 2 : Type))
      (leftTripleCoordinateNatIso.app j)).trans
        (Over.forget_map (X := (Fin 2 : Type))
          (U := leftTriple.obj j) (V := tripleDiagram.obj j)
          (f := (leftTripleCoordinateNatIso.app j).hom))
  have hcomponent :
      ((leftTripleCoordinateNatIso.app j).hom.left :
          (leftTriple.obj j).left ⟶ Triple j) =
      (leftTripleCoordinates j).hom.left :=
    congrArg Over.Hom.left (congrArg Iso.hom (leftTripleCoordinateNatIso_app j))
  exact (Iso.toEquiv_apply
    (X := ((leftTriple.obj j).left : Type)) (Y := (Triple j : Type))
    ((Over.forget (Fin 2 : Type)).mapIso (leftTripleCoordinateNatIso.app j)) p).trans
      ((types_congr_hom (X := (leftTriple.obj j).left) (Y := Triple j) hforget p).trans
        (types_congr_hom (X := (leftTriple.obj j).left) (Y := Triple j) hcomponent p))

private lemma rightStatistics_equiv_apply (j : Fin 2) (p : (rightTriple.obj j).left) :
    (((Over.forget (Fin 2)).mapIso (rightTripleCoordinateNatIso.app j)).toEquiv p : Triple j) =
      (rightTripleCoordinates j).hom.left p := by
  have hforget :
      (((Over.forget (Fin 2 : Type)).mapIso
        (rightTripleCoordinateNatIso.app j)).hom :
          (rightTriple.obj j).left ⟶ Triple j) =
      (rightTripleCoordinateNatIso.app j).hom.left :=
    (Functor.mapIso_hom (Over.forget (Fin 2 : Type))
      (rightTripleCoordinateNatIso.app j)).trans
        (Over.forget_map (X := (Fin 2 : Type))
          (U := rightTriple.obj j) (V := tripleDiagram.obj j)
          (f := (rightTripleCoordinateNatIso.app j).hom))
  have hcomponent :
      ((rightTripleCoordinateNatIso.app j).hom.left :
          (rightTriple.obj j).left ⟶ Triple j) =
      (rightTripleCoordinates j).hom.left :=
    congrArg Over.Hom.left (congrArg Iso.hom (rightTripleCoordinateNatIso_app j))
  exact (Iso.toEquiv_apply
    (X := ((rightTriple.obj j).left : Type)) (Y := (Triple j : Type))
    ((Over.forget (Fin 2 : Type)).mapIso (rightTripleCoordinateNatIso.app j)) p).trans
      ((types_congr_hom (X := (rightTriple.obj j).left) (Y := Triple j) hforget p).trans
        (types_congr_hom (X := (rightTriple.obj j).left) (Y := Triple j) hcomponent p))

private lemma leftStatistics_square (p : (leftTriple.obj 0).left) :
    (((Over.forget (Fin 2)).mapIso (leftTripleCoordinateNatIso.app 1)).toEquiv
      ((leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p) : Triple 1) =
    (tripleDiagram.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left
      (((Over.forget (Fin 2)).mapIso (leftTripleCoordinateNatIso.app 0)).toEquiv p :
        Triple 0) := by
  rw [leftStatistics_equiv_apply, leftStatistics_equiv_apply]
  have hp :
      (leftTripleCoordinateNatIso.hom.app 1).left
          ((leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p) =
        (tripleDiagram.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left
          ((leftTripleCoordinateNatIso.hom.app 0).left p) :=
    over_naturality_apply (D := leftTriple) (E := tripleDiagram)
      leftTripleCoordinateNatIso.hom (homOfLE (by decide : (0 : Fin 2) ≤ 1)) p
  have h₀ : leftTripleCoordinateNatIso.hom.app 0 = (leftTripleCoordinates 0).hom :=
    (Iso.app_hom leftTripleCoordinateNatIso 0).symm.trans
      (congrArg Iso.hom (leftTripleCoordinateNatIso_app 0))
  have h₁ : leftTripleCoordinateNatIso.hom.app 1 = (leftTripleCoordinates 1).hom :=
    (Iso.app_hom leftTripleCoordinateNatIso 1).symm.trans
      (congrArg Iso.hom (leftTripleCoordinateNatIso_app 1))
  rw [h₀, h₁] at hp
  exact hp

private lemma rightStatistics_square (p : (rightTriple.obj 0).left) :
    (((Over.forget (Fin 2)).mapIso (rightTripleCoordinateNatIso.app 1)).toEquiv
      ((rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p) : Triple 1) =
    (tripleDiagram.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left
      (((Over.forget (Fin 2)).mapIso (rightTripleCoordinateNatIso.app 0)).toEquiv p :
        Triple 0) := by
  rw [rightStatistics_equiv_apply, rightStatistics_equiv_apply]
  have hp :
      (rightTripleCoordinateNatIso.hom.app 1).left
          ((rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p) =
        (tripleDiagram.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left
          ((rightTripleCoordinateNatIso.hom.app 0).left p) :=
    over_naturality_apply (D := rightTriple) (E := tripleDiagram)
      rightTripleCoordinateNatIso.hom (homOfLE (by decide : (0 : Fin 2) ≤ 1)) p
  have h₀ : rightTripleCoordinateNatIso.hom.app 0 = (rightTripleCoordinates 0).hom :=
    (Iso.app_hom rightTripleCoordinateNatIso 0).symm.trans
      (congrArg Iso.hom (rightTripleCoordinateNatIso_app 0))
  have h₁ : rightTripleCoordinateNatIso.hom.app 1 = (rightTripleCoordinates 1).hom :=
    (Iso.app_hom rightTripleCoordinateNatIso 1).symm.trans
      (congrArg Iso.hom (rightTripleCoordinateNatIso_app 1))
  rw [h₀, h₁] at hp
  exact hp

private lemma leftStatistics_image_iff (q : (leftTriple.obj 1).left) :
    (∃ p, (leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q) ↔
      ∃ p : Triple 0, (tripleDiagram.map
        (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p =
          (leftTripleCoordinates 1).hom.left q := by
  let e₀ : (leftTriple.obj 0).left ≃ Triple 0 :=
    ((Over.forget (Fin 2)).mapIso (leftTripleCoordinateNatIso.app 0)).toEquiv
  let e₁ : (leftTriple.obj 1).left ≃ Triple 1 :=
    ((Over.forget (Fin 2)).mapIso (leftTripleCoordinateNatIso.app 1)).toEquiv
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨e₀ p, (leftStatistics_square p).symm.trans
      ((congrArg e₁ hp).trans (leftStatistics_equiv_apply 1 q))⟩
  · rintro ⟨r, hr⟩
    obtain ⟨p, rfl⟩ := e₀.surjective r
    exact ⟨p, e₁.injective ((leftStatistics_square p).trans
      (hr.trans (leftStatistics_equiv_apply 1 q).symm))⟩

private lemma rightStatistics_image_iff (q : (rightTriple.obj 1).left) :
    (∃ p, (rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q) ↔
      ∃ p : Triple 0, (tripleDiagram.map
        (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p =
          (rightTripleCoordinates 1).hom.left q := by
  let e₀ : (rightTriple.obj 0).left ≃ Triple 0 :=
    ((Over.forget (Fin 2)).mapIso (rightTripleCoordinateNatIso.app 0)).toEquiv
  let e₁ : (rightTriple.obj 1).left ≃ Triple 1 :=
    ((Over.forget (Fin 2)).mapIso (rightTripleCoordinateNatIso.app 1)).toEquiv
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨e₀ p, (rightStatistics_square p).symm.trans
      ((congrArg e₁ hp).trans (rightStatistics_equiv_apply 1 q))⟩
  · rintro ⟨r, hr⟩
    obtain ⟨p, rfl⟩ := e₀.surjective r
    exact ⟨p, e₁.injective ((rightStatistics_square p).trans
      (hr.trans (rightStatistics_equiv_apply 1 q).symm))⟩

private lemma leftStatistics_fiber_card (q : (leftTriple.obj 1).left) :
    Nat.card {p : (leftTriple.obj 0).left // (leftTriple.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} =
    Nat.card {p : Triple 0 // (tripleDiagram.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p =
        (leftTripleCoordinates 1).hom.left q} := by
  let e₀ : (leftTriple.obj 0).left ≃ Triple 0 :=
    ((Over.forget (Fin 2)).mapIso (leftTripleCoordinateNatIso.app 0)).toEquiv
  let e₁ : (leftTriple.obj 1).left ≃ Triple 1 :=
    ((Over.forget (Fin 2)).mapIso (leftTripleCoordinateNatIso.app 1)).toEquiv
  apply Nat.card_congr (e₀.subtypeEquiv ?_)
  intro p
  constructor
  · intro hp
    exact (leftStatistics_square p).symm.trans
      ((congrArg e₁ hp).trans (leftStatistics_equiv_apply 1 q))
  · intro hp
    exact e₁.injective ((leftStatistics_square p).trans
      (hp.trans (leftStatistics_equiv_apply 1 q).symm))

private lemma rightStatistics_fiber_card (q : (rightTriple.obj 1).left) :
    Nat.card {p : (rightTriple.obj 0).left // (rightTriple.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} =
    Nat.card {p : Triple 0 // (tripleDiagram.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p =
        (rightTripleCoordinates 1).hom.left q} := by
  let e₀ : (rightTriple.obj 0).left ≃ Triple 0 :=
    ((Over.forget (Fin 2)).mapIso (rightTripleCoordinateNatIso.app 0)).toEquiv
  let e₁ : (rightTriple.obj 1).left ≃ Triple 1 :=
    ((Over.forget (Fin 2)).mapIso (rightTripleCoordinateNatIso.app 1)).toEquiv
  apply Nat.card_congr (e₀.subtypeEquiv ?_)
  intro p
  constructor
  · intro hp
    exact (rightStatistics_square p).symm.trans
      ((congrArg e₁ hp).trans (rightStatistics_equiv_apply 1 q))
  · intro hp
    exact e₁.injective ((rightStatistics_square p).trans
      (hp.trans (rightStatistics_equiv_apply 1 q).symm))

private lemma leftStatistics_distribution (n : ℕ) :
    Nat.card {q : (leftTriple.obj 1).left // Nat.card {p : (leftTriple.obj 0).left //
      (leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = n} =
    Nat.card {q : Triple 1 // Nat.card {p : Triple 0 //
      (tripleDiagram.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = n} := by
  let e₁ : (leftTriple.obj 1).left ≃ Triple 1 :=
    ((Over.forget (Fin 2)).mapIso (leftTripleCoordinateNatIso.app 1)).toEquiv
  apply Nat.card_congr (e₁.subtypeEquiv ?_)
  intro q
  have hq : e₁ q = (leftTripleCoordinates 1).hom.left q :=
    leftStatistics_equiv_apply 1 q
  rw [hq, leftStatistics_fiber_card]

private lemma rightStatistics_distribution (n : ℕ) :
    Nat.card {q : (rightTriple.obj 1).left // Nat.card {p : (rightTriple.obj 0).left //
      (rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = n} =
    Nat.card {q : Triple 1 // Nat.card {p : Triple 0 //
      (tripleDiagram.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = n} := by
  let e₁ : (rightTriple.obj 1).left ≃ Triple 1 :=
    ((Over.forget (Fin 2)).mapIso (rightTripleCoordinateNatIso.app 1)).toEquiv
  apply Nat.card_congr (e₁.subtypeEquiv ?_)
  intro q
  have hq : e₁ q = (rightTripleCoordinates 1).hom.left q :=
    rightStatistics_equiv_apply 1 q
  rw [hq, rightStatistics_fiber_card]

/-- The left-associated transition has ten image points. -/
theorem leftTriple_image_card :
    Nat.card (Set.range (leftTriple.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left) = 10 := by
  let e₁ : (leftTriple.obj 1).left ≃ Triple 1 :=
    ((Over.forget (Fin 2)).mapIso (leftTripleCoordinateNatIso.app 1)).toEquiv
  have h : Nat.card (Set.range (leftTriple.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left) =
      Nat.card {q : Triple 1 // ∃ p : Triple 0, (tripleDiagram.map
        (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} := by
    apply Nat.card_congr (e₁.subtypeEquiv ?_)
    intro q
    have hq : e₁ q = (leftTripleCoordinates 1).hom.left q :=
      leftStatistics_equiv_apply 1 q
    rw [hq]
    exact leftStatistics_image_iff q
  exact h.trans tripleStatistics_image_card

/-- The right-associated transition has ten image points. -/
theorem rightTriple_image_card :
    Nat.card (Set.range (rightTriple.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left) = 10 := by
  let e₁ : (rightTriple.obj 1).left ≃ Triple 1 :=
    ((Over.forget (Fin 2)).mapIso (rightTripleCoordinateNatIso.app 1)).toEquiv
  have h : Nat.card (Set.range (rightTriple.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left) =
      Nat.card {q : Triple 1 // ∃ p : Triple 0, (tripleDiagram.map
        (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} := by
    apply Nat.card_congr (e₁.subtypeEquiv ?_)
    intro q
    have hq : e₁ q = (rightTripleCoordinates 1).hom.left q :=
      rightStatistics_equiv_apply 1 q
    rw [hq]
    exact rightStatistics_image_iff q
  exact h.trans tripleStatistics_image_card

/-- Every left-associated fiber has cardinality zero, two, or one as its coordinates dictate. -/
theorem leftTriple_fiber_card (q : (leftTriple.obj 1).left) :
    Nat.card {p : (leftTriple.obj 0).left // (leftTriple.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} =
      @ite ℕ (Eq (α := Fin 4) ((leftTripleCoordinates 1).hom.left q).val.1 3 ∨
          Eq (α := Fin 5) ((leftTripleCoordinates 1).hom.left q).val.2.1 1)
        (decidable_of_iff
          (((leftTripleCoordinates 1).hom.left q).val.1.val = 3 ∨
            ((leftTripleCoordinates 1).hom.left q).val.2.1.val = 1)
          (or_congr (show ((leftTripleCoordinates 1).hom.left q).val.1.val = (3 : Fin 4).val ↔
                ((leftTripleCoordinates 1).hom.left q).val.1 = (3 : Fin 4) from
              (Fin.val_injective (n := 4)).eq_iff
                (a := ((leftTripleCoordinates 1).hom.left q).val.1) (b := (3 : Fin 4)))
            (show ((leftTripleCoordinates 1).hom.left q).val.2.1.val = (1 : Fin 5).val ↔
                ((leftTripleCoordinates 1).hom.left q).val.2.1 = (1 : Fin 5) from
              (Fin.val_injective (n := 5)).eq_iff
                (a := ((leftTripleCoordinates 1).hom.left q).val.2.1) (b := (1 : Fin 5)))))
        0 (@ite ℕ (Eq (α := Fin 4) ((leftTripleCoordinates 1).hom.left q).val.2.2 0)
          (decidable_of_iff (((leftTripleCoordinates 1).hom.left q).val.2.2.val = 0)
            (show ((leftTripleCoordinates 1).hom.left q).val.2.2.val = (0 : Fin 4).val ↔
                ((leftTripleCoordinates 1).hom.left q).val.2.2 = (0 : Fin 4) from
              (Fin.val_injective (n := 4)).eq_iff
                (a := ((leftTripleCoordinates 1).hom.left q).val.2.2) (b := (0 : Fin 4)))) 2 1) :=
  (leftStatistics_fiber_card q).trans (tripleStatistics_fiber_card _)

/-- Every right-associated fiber has cardinality zero, two, or one as its coordinates dictate. -/
theorem rightTriple_fiber_card (q : (rightTriple.obj 1).left) :
    Nat.card {p : (rightTriple.obj 0).left // (rightTriple.map
      (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} =
      @ite ℕ (Eq (α := Fin 4) ((rightTripleCoordinates 1).hom.left q).val.1 3 ∨
          Eq (α := Fin 5) ((rightTripleCoordinates 1).hom.left q).val.2.1 1)
        (decidable_of_iff
          (((rightTripleCoordinates 1).hom.left q).val.1.val = 3 ∨
            ((rightTripleCoordinates 1).hom.left q).val.2.1.val = 1)
          (or_congr (show ((rightTripleCoordinates 1).hom.left q).val.1.val = (3 : Fin 4).val ↔
                ((rightTripleCoordinates 1).hom.left q).val.1 = (3 : Fin 4) from
              (Fin.val_injective (n := 4)).eq_iff
                (a := ((rightTripleCoordinates 1).hom.left q).val.1) (b := (3 : Fin 4)))
            (show ((rightTripleCoordinates 1).hom.left q).val.2.1.val = (1 : Fin 5).val ↔
                ((rightTripleCoordinates 1).hom.left q).val.2.1 = (1 : Fin 5) from
              (Fin.val_injective (n := 5)).eq_iff
                (a := ((rightTripleCoordinates 1).hom.left q).val.2.1) (b := (1 : Fin 5)))))
        0 (@ite ℕ (Eq (α := Fin 4) ((rightTripleCoordinates 1).hom.left q).val.2.2 0)
          (decidable_of_iff (((rightTripleCoordinates 1).hom.left q).val.2.2.val = 0)
            (show ((rightTripleCoordinates 1).hom.left q).val.2.2.val = (0 : Fin 4).val ↔
                ((rightTripleCoordinates 1).hom.left q).val.2.2 = (0 : Fin 4) from
              (Fin.val_injective (n := 4)).eq_iff
                (a := ((rightTripleCoordinates 1).hom.left q).val.2.2) (b := (0 : Fin 4)))) 2 1) :=
  (rightStatistics_fiber_card q).trans (tripleStatistics_fiber_card _)

/-- Exactly four targets of the left-associated transition have double fibers. -/
theorem leftTriple_double_fibers_card :
    Nat.card {q : (leftTriple.obj 1).left // Nat.card {p : (leftTriple.obj 0).left //
      (leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = 2} = 4 :=
  (leftStatistics_distribution 2).trans tripleStatistics_fiber_counts.1

/-- Exactly four targets of the right-associated transition have double fibers. -/
theorem rightTriple_double_fibers_card :
    Nat.card {q : (rightTriple.obj 1).left // Nat.card {p : (rightTriple.obj 0).left //
      (rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = 2} = 4 :=
  (rightStatistics_distribution 2).trans tripleStatistics_fiber_counts.1

/-- Exactly six targets of the left-associated transition have singleton fibers. -/
theorem leftTriple_singleton_fibers_card :
    Nat.card {q : (leftTriple.obj 1).left // Nat.card {p : (leftTriple.obj 0).left //
      (leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = 1} = 6 :=
  (leftStatistics_distribution 1).trans tripleStatistics_fiber_counts.2.1

/-- Exactly six targets of the right-associated transition have singleton fibers. -/
theorem rightTriple_singleton_fibers_card :
    Nat.card {q : (rightTriple.obj 1).left // Nat.card {p : (rightTriple.obj 0).left //
      (rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = 1} = 6 :=
  (rightStatistics_distribution 1).trans tripleStatistics_fiber_counts.2.1

/-- Exactly eight targets of the left-associated transition have empty fibers. -/
theorem leftTriple_empty_fibers_card :
    Nat.card {q : (leftTriple.obj 1).left // Nat.card {p : (leftTriple.obj 0).left //
      (leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = 0} = 8 :=
  (leftStatistics_distribution 0).trans tripleStatistics_fiber_counts.2.2

/-- Exactly eight targets of the right-associated transition have empty fibers. -/
theorem rightTriple_empty_fibers_card :
    Nat.card {q : (rightTriple.obj 1).left // Nat.card {p : (rightTriple.obj 0).left //
      (rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = 0} = 8 :=
  (rightStatistics_distribution 0).trans tripleStatistics_fiber_counts.2.2

/-- A left-associated target is missed precisely when its first or middle coordinate is missed. -/
theorem leftTriple_missing_iff (q : (leftTriple.obj 1).left) :
    (¬ ∃ p, (leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q) ↔
      ((leftTripleCoordinates 1).hom.left q).val.1 = (3 : Fin 4) ∨
        ((leftTripleCoordinates 1).hom.left q).val.2.1 = (1 : Fin 5) :=
  (not_congr (leftStatistics_image_iff q)).trans (tripleStep_missing_iff _)

/-- A right-associated target is missed precisely when its first or middle coordinate is missed. -/
theorem rightTriple_missing_iff (q : (rightTriple.obj 1).left) :
    (¬ ∃ p, (rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q) ↔
      ((rightTripleCoordinates 1).hom.left q).val.1 = (3 : Fin 4) ∨
        ((rightTripleCoordinates 1).hom.left q).val.2.1 = (1 : Fin 5) :=
  (not_congr (rightStatistics_image_iff q)).trans (tripleStep_missing_iff _)

/-- There are eight missing targets of the left-associated transition. -/
theorem leftTriple_missing_card :
    Nat.card {q : (leftTriple.obj 1).left // ¬ ∃ p,
      (leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = 8 := by
  let e₁ : (leftTriple.obj 1).left ≃ Triple 1 :=
    ((Over.forget (Fin 2)).mapIso (leftTripleCoordinateNatIso.app 1)).toEquiv
  have h : Nat.card {q : (leftTriple.obj 1).left // ¬ ∃ p,
      (leftTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} =
      Nat.card {q : Triple 1 // ¬ ∃ p : Triple 0, (tripleDiagram.map
        (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} := by
    apply Nat.card_congr (e₁.subtypeEquiv ?_)
    intro q
    have hq : e₁ q = (leftTripleCoordinates 1).hom.left q :=
      leftStatistics_equiv_apply 1 q
    rw [hq]
    exact not_congr (leftStatistics_image_iff q)
  exact h.trans tripleStatistics_missing_card

/-- There are eight missing targets of the right-associated transition. -/
theorem rightTriple_missing_card :
    Nat.card {q : (rightTriple.obj 1).left // ¬ ∃ p,
      (rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} = 8 := by
  let e₁ : (rightTriple.obj 1).left ≃ Triple 1 :=
    ((Over.forget (Fin 2)).mapIso (rightTripleCoordinateNatIso.app 1)).toEquiv
  have h : Nat.card {q : (rightTriple.obj 1).left // ¬ ∃ p,
      (rightTriple.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} =
      Nat.card {q : Triple 1 // ¬ ∃ p : Triple 0, (tripleDiagram.map
        (homOfLE (by decide : (0 : Fin 2) ≤ 1))).left p = q} := by
    apply Nat.card_congr (e₁.subtypeEquiv ?_)
    intro q
    have hq : e₁ q = (rightTripleCoordinates 1).hom.left q :=
      rightStatistics_equiv_apply 1 q
    rw [hq]
    exact not_congr (rightStatistics_image_iff q)
  exact h.trans tripleStatistics_missing_card

end CategoryTheory.FiniteDiagram
