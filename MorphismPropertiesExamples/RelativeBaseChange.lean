/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MorphismProperties.RelativeBaseChange
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Subsingleton

/-!
# Relative pullback preservation on a four-object chain

On `0 < 1 < 2 < 3`, let `P` consist of the identities and `0 ⟶ 1`, `0 ⟶ 3`,
and let `E` consist of the identities and `1 ⟶ 2`, `1 ⟶ 3`.
The property `E` is stable under base change and `P` is stable against `E`,
but `P` is not absolutely stable. The relative preservation theorem sends
`0 ⟶ 3` to the nonidentity arrow `0 ⟶ 1` after pullback along `1 ⟶ 3`.
The slice-category client uses exactly the existing `Over.pullback` functor.

The object-structured example instead sends `1 ⟶ 3` to `1 ⟶ 2` after
pullback along `2 ⟶ 3`, which is outside `E`. It exercises preservation in
`⊤ ⊓ E`, as well as the object alternative with `P = E`. The base-arrow
alternative retains the relatively stable, non-absolutely-stable `P`.
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

open Limits

private lemma eq_inf_of_isPullback {α : Type*} [SemilatticeInf α] {a b c d : α}
    {p : d ⟶ a} {q : d ⟶ b} {g : a ⟶ c} {f : b ⟶ c}
    (sq : IsPullback p q g f) : d = a ⊓ b := by
  apply le_antisymm (le_inf (leOfHom p) (leOfHom q))
  exact leOfHom (sq.lift (homOfLE inf_le_left) (homOfLE inf_le_right)
    (Subsingleton.elim _ _))

end CategoryTheory.MorphismProperty

namespace CategoryTheory.MorphismProperty.FourChain

open Limits

/-- Identities together with `0 ⟶ 1` and `0 ⟶ 3` in the four-object chain. -/
def P : MorphismProperty (Fin 4) :=
  fun {a b} _ => a = b ∨ (a = 0 ∧ (b = 1 ∨ b = 3))

/-- Identities together with `1 ⟶ 2` and `1 ⟶ 3` in the four-object chain. -/
def E : MorphismProperty (Fin 4) :=
  fun {a b} _ => a = b ∨ (a = 1 ∧ (b = 2 ∨ b = 3))

/-- Membership in `P` is determined by the source and target objects. -/
@[simp] theorem p_iff {a b : Fin 4} (f : a ⟶ b) :
    P f ↔ a = b ∨ (a = 0 ∧ (b = 1 ∨ b = 3)) := Iff.rfl

/-- Membership in `E` is determined by the source and target objects. -/
@[simp] theorem e_iff {a b : Fin 4} (f : a ⟶ b) :
    E f ↔ a = b ∨ (a = 1 ∧ (b = 2 ∨ b = 3)) := Iff.rfl

instance : E.IsStableUnderBaseChange where
  of_isPullback {b a d c} {f} {g} {p} {q} sq hg := by
    rw [e_iff] at hg ⊢
    have hb := leOfHom f
    rw [eq_inf_of_isPullback sq]
    rcases le_total a b with hab | hba
    · rw [inf_eq_left.mpr hab]
      omega
    · rw [inf_eq_right.mpr hba]
      exact Or.inl rfl

instance : P.IsStableUnderBaseChangeAgainst E where
  isStableUnderBaseChangeAlong {b c} f hf := by
    constructor
    intro a d p q g sq hg
    rw [e_iff] at hf
    rw [p_iff] at hg ⊢
    have ha := leOfHom g
    rw [eq_inf_of_isPullback sq]
    rcases le_total a b with hab | hba
    · rw [inf_eq_left.mpr hab]
      omega
    · rw [inf_eq_right.mpr hba]
      exact Or.inl rfl

/-- The arrow `0 ⟶ 3` of the four-object chain. -/
def zeroThree : (0 : Fin 4) ⟶ 3 := homOfLE (by decide)

/-- The arrow `1 ⟶ 3` used as the base arrow in the relative example. -/
def oneThree : (1 : Fin 4) ⟶ 3 := homOfLE (by decide)
private def twoThree : (2 : Fin 4) ⟶ 3 := homOfLE (by decide)

/-- The relative pointwise theorem gives a `P` map with unequal source and target
objects: the induced map is the arrow `0 ⟶ 1`. -/
theorem nonidentity_pullback_map :
    P (pullback.lift (f := 𝟙 (3 : Fin 4)) (g := oneThree)
      (pullback.fst zeroThree oneThree ≫ zeroThree)
      (pullback.snd zeroThree oneThree) (by subsingleton)) ∧
    pullback zeroThree oneThree ≠ pullback (𝟙 (3 : Fin 4)) oneThree := by
  constructor
  · exact P.pullbackLift_fst_snd_of_isStableUnderBaseChangeAgainst E oneThree
      (by exact Or.inr ⟨rfl, Or.inr rfl⟩) (by subsingleton)
      (by exact Or.inr ⟨rfl, Or.inr rfl⟩)
  · rw [CompleteLattice.pullback_eq_inf zeroThree oneThree,
      CompleteLattice.pullback_eq_inf (𝟙 (3 : Fin 4)) oneThree]
    decide

/-- The same nonidentity original arrow can be used as a morphism over `3`. -/
theorem slice_pullback_map :
    P ((Over.pullback oneThree).map
      (Over.homMk zeroThree (by subsingleton) : Over.mk zeroThree ⟶
        Over.mk (𝟙 (3 : Fin 4)))).left := by
  apply P.overPullbackMap_of_isStableUnderBaseChangeAgainst E oneThree
    (by exact Or.inr ⟨rfl, Or.inr rfl⟩)
  exact Or.inr ⟨rfl, Or.inr rfl⟩

/-- Pullback along `2 ⟶ 3` would produce `0 ⟶ 2`, which is not in `P`. -/
theorem not_isStableUnderBaseChange : ¬ P.IsStableUnderBaseChange := by
  intro h
  let := h
  have hp : P zeroThree := Or.inr ⟨rfl, Or.inr rfl⟩
  have hq := P.pullback_snd zeroThree twoThree hp
  rw [p_iff, CompleteLattice.pullback_eq_inf zeroThree twoThree] at hq
  norm_num at hq

/-- At the absolute boundary `E = ⊤`, the relative theorem preserves a
nonidentity monomorphism, with the conclusion of Mathlib's absolute theorem. -/
example :
    (monomorphisms (Fin 4)) (pullback.lift (f := 𝟙 (3 : Fin 4)) (g := oneThree)
      (pullback.fst zeroThree oneThree ≫ zeroThree)
      (pullback.snd zeroThree oneThree) (by subsingleton)) := by
  let := (isStableUnderBaseChangeAgainst_top_iff (monomorphisms (Fin 4))).mpr inferInstance
  apply (monomorphisms (Fin 4)).pullbackLift_fst_snd_of_isStableUnderBaseChangeAgainst
    ⊤ oneThree trivial (by subsingleton)
  infer_instance

/-- The absolute slice conclusion also follows by specializing the relative theorem
through Mathlib's equivalence for stability against all arrows. -/
example :
    (monomorphisms (Fin 4)) ((Over.pullback oneThree).map
      (Over.homMk zeroThree (by subsingleton) : Over.mk zeroThree ⟶
        Over.mk (𝟙 (3 : Fin 4)))).left := by
  let := (isStableUnderBaseChangeAgainst_top_iff (monomorphisms (Fin 4))).mpr inferInstance
  apply (monomorphisms (Fin 4)).overPullbackMap_of_isStableUnderBaseChangeAgainst
    ⊤ oneThree trivial
  infer_instance

instance : E.HasOfPostcompProperty E where
  of_postcomp {a b c} f g hg hfg := by
    rw [e_iff] at hg hfg ⊢
    have hab := leOfHom f
    have hbc := leOfHom g
    omega

private lemma intersection_iff {a b : Fin 4} (f : a ⟶ b) :
    (P ⊓ E) f ↔ a = b := by
  rw [inf_iff, p_iff, e_iff]
  constructor <;> omega

instance : (P ⊓ E).IsStableUnderBaseChange where
  of_isPullback {b a d c} {f} {g} {p} {q} sq hg := by
    rw [intersection_iff] at hg ⊢
    rw [eq_inf_of_isPullback sq, hg]
    exact inf_eq_right.mpr (leOfHom f)

/-- An arbitrary base arrow outside `E` gives an induced map in `⊤ ⊓ E`
between distinct objects: the map is `1 ⟶ 2`. -/
theorem structured_nonidentity_pullback_map :
    let f : (2 : Fin 4) ⟶ 3 := homOfLE (by decide)
    ¬ E f ∧
    (⊤ ⊓ E) (pullback.lift (f := 𝟙 (3 : Fin 4)) (g := f)
      (pullback.fst oneThree f ≫ oneThree)
      (pullback.snd oneThree f) (by subsingleton)) ∧
    pullback oneThree f ≠ pullback (𝟙 (3 : Fin 4)) f := by
  refine ⟨?_, ?_, ?_⟩
  · rw [e_iff]
    decide
  · exact (⊤ : MorphismProperty (Fin 4)).pullbackLift_fst_snd_of_intersection_of_postcomp
      E twoThree (by subsingleton) (by simp) (by simp) trivial
  · rw [CompleteLattice.pullback_eq_inf, CompleteLattice.pullback_eq_inf]
    decide

/-- The object-structured alternative preserves `E` for the same nonidentity
map `1 ⟶ 2`, without requiring its base arrow `2 ⟶ 3` to belong to `E`. -/
theorem structured_relative_alternatives :
    let f : (2 : Fin 4) ⟶ 3 := homOfLE (by decide)
    E (pullback.lift (f := 𝟙 (3 : Fin 4)) (g := f)
      (pullback.fst oneThree f ≫ oneThree)
      (pullback.snd oneThree f) (by subsingleton)) := by
  apply E.pullbackLift_fst_snd_of_relative_alternatives E twoThree (by subsingleton)
    (Or.inl ⟨by simp, by simp⟩)
  simp

/-- The base-arrow alternative preserves the relatively stable `P` on the
nonidentity map `0 ⟶ 1`, although the source structure arrow is outside `E`. -/
theorem against_relative_alternatives :
    ¬ E zeroThree ∧
    P (pullback.lift (f := 𝟙 (3 : Fin 4)) (g := oneThree)
      (pullback.fst zeroThree oneThree ≫ zeroThree)
      (pullback.snd zeroThree oneThree) (by subsingleton)) := by
  constructor
  · rw [e_iff]
    decide
  · apply P.pullbackLift_fst_snd_of_relative_alternatives E oneThree (by subsingleton)
      (Or.inr (by simp))
    simp

/-- With `E = ⊤`, the intersection theorem applies to monomorphisms and gives
both components on the nonidentity induced map `0 ⟶ 1`. -/
theorem absolute_structured_pullback_map :
    (monomorphisms (Fin 4) ⊓ ⊤)
      (pullback.lift (f := 𝟙 (3 : Fin 4)) (g := oneThree)
        (pullback.fst zeroThree oneThree ≫ zeroThree)
        (pullback.snd zeroThree oneThree) (by subsingleton)) := by
  apply (monomorphisms (Fin 4)).pullbackLift_fst_snd_of_intersection_of_postcomp
    ⊤ oneThree (by subsingleton) trivial trivial
  infer_instance

/-- Mathlib's absolute theorem applies to the same arrow and base change as
the `E = ⊤` intersection client. -/
theorem absolute_pullback_map :
    (monomorphisms (Fin 4))
      (pullback.lift (f := 𝟙 (3 : Fin 4)) (g := oneThree)
        (pullback.fst zeroThree oneThree ≫ zeroThree)
        (pullback.snd zeroThree oneThree) (by subsingleton)) := by
  apply (monomorphisms (Fin 4)).pullbackLift_fst_snd oneThree (by subsingleton)
  infer_instance

/-- With `E = ⊤`, the alternatives theorem has the same conclusion on the
same nonidentity arrow as Mathlib's absolute theorem. -/
theorem absolute_alternatives_pullback_map :
    (monomorphisms (Fin 4))
      (pullback.lift (f := 𝟙 (3 : Fin 4)) (g := oneThree)
        (pullback.fst zeroThree oneThree ≫ zeroThree)
        (pullback.snd zeroThree oneThree) (by subsingleton)) := by
  apply (monomorphisms (Fin 4)).pullbackLift_fst_snd_of_relative_alternatives
    ⊤ oneThree (by subsingleton) (Or.inl ⟨trivial, trivial⟩)
  infer_instance

end CategoryTheory.MorphismProperty.FourChain

namespace CategoryTheory.MorphismProperty.ThreeChain

open Limits

/-- Identities together with `0 ⟶ 2` in the three-object chain. -/
def P : MorphismProperty (Fin 3) :=
  fun {a b} _ => a = b ∨ (a = 0 ∧ b = 2)

/-- Identities together with all arrows out of `0` in the three-object chain. -/
def E : MorphismProperty (Fin 3) :=
  fun {a b} _ => a = b ∨ a = 0

/-- Membership in `P` is determined by the source and target objects. -/
@[simp] theorem p_iff {a b : Fin 3} (f : a ⟶ b) :
    P f ↔ a = b ∨ (a = 0 ∧ b = 2) := Iff.rfl

/-- Membership in `E` is determined by the source and target objects. -/
@[simp] theorem e_iff {a b : Fin 3} (f : a ⟶ b) :
    E f ↔ a = b ∨ a = 0 := Iff.rfl

instance : E.IsStableUnderBaseChange where
  of_isPullback {b a d c} {f} {g} {p} {q} sq hg := by
    rw [e_iff] at hg ⊢
    have hb := leOfHom f
    rw [eq_inf_of_isPullback sq]
    rcases le_total a b with hab | hba
    · rw [inf_eq_left.mpr hab]
      omega
    · rw [inf_eq_right.mpr hba]
      exact Or.inl rfl

instance : P.IsStableUnderBaseChangeAgainst E where
  isStableUnderBaseChangeAlong {b c} f hf := by
    constructor
    intro a d p q g sq hg
    rw [e_iff] at hf
    rw [p_iff] at hg ⊢
    have ha := leOfHom g
    rw [eq_inf_of_isPullback sq]
    rcases le_total a b with hab | hba
    · rw [inf_eq_left.mpr hab]
      omega
    · rw [inf_eq_right.mpr hba]
      exact Or.inl rfl

/-- The arrow `0 ⟶ 2` in the three-object chain. -/
def zeroTwo : (0 : Fin 3) ⟶ 2 := homOfLE (by decide)
/-- The arrow `1 ⟶ 2` along which the counterexample is pulled back. -/
def oneTwo : (1 : Fin 3) ⟶ 2 := homOfLE (by decide)

/-- Pulling back `0 ⟶ 2` along `1 ⟶ 2` yields `0 ⟶ 1`, outside `P`,
even though the original arrow belongs to both `P` and `E`. -/
theorem counterexample_square :
    IsPullback (pullback.fst zeroTwo oneTwo) (pullback.snd zeroTwo oneTwo)
      zeroTwo oneTwo ∧ P zeroTwo ∧ E zeroTwo ∧
      ¬ P (pullback.snd zeroTwo oneTwo) := by
  refine ⟨IsPullback.of_hasPullback _ _, ?_, ?_, ?_⟩
  · simp
  · simp
  · rw [p_iff, CompleteLattice.pullback_eq_inf zeroTwo oneTwo]
    norm_num

/-- Relative stability alone does not ensure the either-leg property. -/
theorem not_either_leg_stability :
    ¬ (∀ ⦃X Y Y' T : Fin 3⦄ (a : X ⟶ Y) (b : Y' ⟶ Y)
        (p : T ⟶ X) (q : T ⟶ Y'),
        IsPullback p q a b → P a → (E a ∨ E b) → P q) := by
  intro h
  obtain ⟨sq, hp, he, hn⟩ := counterexample_square
  exact hn (h zeroTwo oneTwo _ _ sq hp (Or.inl he))

/-- The second clause of the criterion fails although `P` is stable against `E`. -/
theorem not_inf_isStableUnderBaseChange : ¬ (P ⊓ E).IsStableUnderBaseChange := by
  intro h
  obtain ⟨sq, hp, he, hn⟩ := counterexample_square
  exact hn (h.of_isPullback sq ⟨hp, he⟩).1

/-- At `E = ⊤`, the criterion applies to monomorphisms on a nonidentity
existing pullback square, using Mathlib's absolute/relative stability bridge. -/
theorem nonidentity_monomorphism_pullback :
    (monomorphisms (Fin 3)) (pullback.snd zeroTwo oneTwo) ∧
      pullback zeroTwo oneTwo ≠ (1 : Fin 3) := by
  have hAgainst := (isStableUnderBaseChangeAgainst_top_iff
    (monomorphisms (Fin 3))).mpr inferInstance
  have hInf : (monomorphisms (Fin 3) ⊓ ⊤).IsStableUnderBaseChange := by
    simpa only [inf_top_eq] using
      (inferInstance : (monomorphisms (Fin 3)).IsStableUnderBaseChange)
  have h := (isStableUnderBaseChange_either_iff (monomorphisms (Fin 3)) ⊤).mpr
    ⟨hAgainst, hInf⟩
  constructor
  · exact h zeroTwo oneTwo _ _ (IsPullback.of_hasPullback _ _)
      (by infer_instance) (Or.inr trivial)
  · rw [CompleteLattice.pullback_eq_inf zeroTwo oneTwo]
    decide

end CategoryTheory.MorphismProperty.ThreeChain

/-!
## Endpoint pullbacks in nonempty finite subsets

The inherited inclusion-order category of nonempty subsets of `Fin 3` has the two
endpoint pullbacks used below. It has no pullback of the disjoint singleton `{2}`
along the same base arrow `{0, 1} ⟶ {0, 1, 2}`, so it has neither pullbacks along
that arrow for all objects nor all pullbacks.
-/

namespace CategoryTheory.MorphismProperty.NonemptyFinsets

open CategoryTheory Limits

/-- Nonempty subsets of a three-element set, ordered by inclusion. -/
abbrev C := {s : Finset (Fin 3) // s.Nonempty}

/-- The full three-element subset. -/
def S : C := ⟨{0, 1, 2}, by decide⟩

/-- The two-element subset used for base change. -/
def S' : C := ⟨{0, 1}, by decide⟩

/-- The singleton contained in the base-change subset. -/
def X : C := ⟨{0}, by decide⟩

/-- The full subset as the target of the original inclusion. -/
abbrev Y : C := S

/-- The singleton disjoint from the base-change subset. -/
def Z : C := ⟨{2}, by decide⟩

/-- Inclusion of the two-element subset into the full subset. -/
def f : S' ⟶ S := homOfLE (by decide)

/-- Inclusion of the singleton into the full subset. -/
def g : X ⟶ Y := homOfLE (by decide)

/-- The structure arrow of the singleton. -/
def v12 : X ⟶ S := homOfLE (by decide)

/-- The structure arrow of the full subset. -/
def v22 : Y ⟶ S := 𝟙 S

/-- Intersecting the singleton with the base-change subset leaves it unchanged. -/
theorem X_inter_S' : X.val ∩ S'.val = X.val := by decide

/-- Intersecting the full subset with the base-change subset gives that subset. -/
theorem Y_inter_S' : Y.val ∩ S'.val = S'.val := by decide

/-- The singleton intersection square. -/
def xPullbackCone : PullbackCone v12 f :=
  PullbackCone.mk (𝟙 X) (homOfLE (by decide : X ≤ S')) (by subsingleton)

/-- The singleton intersection satisfies the pullback universal property. -/
def xPullbackIsLimit : IsLimit xPullbackCone :=
  PullbackCone.isLimitAux xPullbackCone (fun s => s.fst)
    (fun _ => by subsingleton) (fun _ => by subsingleton)
    (fun _ _ _ => by subsingleton)

/-- The two-element intersection square. -/
def yPullbackCone : PullbackCone v22 f :=
  PullbackCone.mk f (𝟙 S') (by subsingleton)

/-- The two-element intersection satisfies the pullback universal property. -/
def yPullbackIsLimit : IsLimit yPullbackCone :=
  PullbackCone.isLimitAux yPullbackCone (fun s => s.snd)
    (fun _ => by subsingleton) (fun _ => by subsingleton)
    (fun _ _ _ => by subsingleton)

local instance : HasPullback v12 f := HasLimit.mk ⟨xPullbackCone, xPullbackIsLimit⟩
local instance : HasPullback v22 f := HasLimit.mk ⟨yPullbackCone, yPullbackIsLimit⟩

/-- The chosen singleton pullback is identified with the explicit intersection by
uniqueness of the limit cone. -/
noncomputable def pullbackXIso : pullback v12 f ≅ X :=
  IsLimit.conePointUniqueUpToIso (pullbackIsPullback v12 f) xPullbackIsLimit

/-- The chosen full-subset pullback is identified with the explicit intersection by
uniqueness of the limit cone. -/
noncomputable def pullbackYIso : pullback v22 f ≅ S' :=
  IsLimit.conePointUniqueUpToIso (pullbackIsPullback v22 f) yPullbackIsLimit

/-- The map of the two endpoint pullbacks induced by the singleton inclusion. -/
noncomputable def pullbackMap : pullback v12 f ⟶ pullback v22 f :=
  pullback.lift (pullback.fst v12 f ≫ g) (pullback.snd v12 f) (by subsingleton)

/-- Under the universal-property identifications, the induced map is the inclusion
of the singleton into the two-element subset. -/
theorem pullbackMap_eq_inclusion :
    pullbackXIso.inv ≫ pullbackMap ≫ pullbackYIso.hom =
      homOfLE (by decide : X ≤ S') := by
  subsingleton

/-- The object-structured preservation theorem applies to monomorphisms using only
the two endpoint pullback instances. -/
theorem pullbackMap_mem_monomorphisms_inter :
    (monomorphisms C ⊓ monomorphisms C) pullbackMap := by
  exact (monomorphisms C).pullbackLift_fst_snd_of_intersection_of_postcomp
    (monomorphisms C) f (by subsingleton)
    (by infer_instance) (by infer_instance) (by infer_instance)

/-- The base-change inclusion is not an isomorphism, hence not an identity. -/
theorem f_not_isIso : ¬ IsIso f := by
  rw [PartialOrder.isIso_iff_eq]
  decide

/-- The original singleton inclusion is not an isomorphism, hence not an identity. -/
theorem g_not_isIso : ¬ IsIso g := by
  rw [PartialOrder.isIso_iff_eq]
  decide

/-- The pullback endpoints are not isomorphic: their explicit intersection cones
have distinct vertices. -/
theorem pullbacks_not_isomorphic :
    ¬ Nonempty (pullback v12 f ≅ pullback v22 f) := by
  rintro ⟨e⟩
  have h : X = S' := (pullbackXIso.symm ≪≫ e ≪≫ pullbackYIso).to_eq
  exact (by decide : X ≠ S') h

/-- The induced pullback map is not an isomorphism, hence not an identity. -/
theorem pullbackMap_not_isIso : ¬ IsIso pullbackMap := by
  intro h
  let := h
  exact pullbacks_not_isomorphic ⟨asIso pullbackMap⟩

/-- The inclusion `{2} ⟶ {0, 1, 2}`. -/
def zToS : Z ⟶ S := homOfLE (by decide)

/-- The disjoint subsets `{2}` and `{0, 1}` have no pullback over the full set:
any pullback vertex would be a nonempty subset of both. -/
theorem not_hasPullback_disjoint_span : ¬ HasPullback zToS f := by
  intro h
  let : HasPullback zToS f := h
  obtain ⟨i, hi⟩ := (pullback zToS f).property
  have hiZ : i ∈ Z.1 := (leOfHom (pullback.fst zToS f)) hi
  have hiS' : i ∈ S'.1 := (leOfHom (pullback.snd zToS f)) hi
  have hiTwo : i = (2 : Fin 3) := by simpa [Z] using hiZ
  norm_num [S', hiTwo, Fin.ext_iff] at hiS'

/-- Pullbacks do not exist along the selected base arrow for every arrow into its codomain. -/
theorem not_hasPullbacksAlong_f : ¬ HasPullbacksAlong f := by
  intro h
  exact not_hasPullback_disjoint_span (h zToS)

/-- The category of nonempty finite subsets of `Fin 3` does not have all pullbacks. -/
theorem not_hasPullbacks : ¬ Limits.HasPullbacks C := by
  intro h
  let : Limits.HasPullbacks C := h
  exact not_hasPullback_disjoint_span inferInstance


end CategoryTheory.MorphismProperty.NonemptyFinsets
