/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.RepresentedCohomology
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Excision
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Strata.OpenPairs.Maps
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.PairOpenCoverGeometry
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-! # Excision for relative motives of literal opens -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable (X : Sm(k))

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The abelian structure on the additive sheaves of the open-pair construction. -/
local instance instAbelianOpenPair : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

private theorem isIso_cokerMap_of_pushout {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasCokernels C] (s : Square C) (hs : s.IsPushout) :
    IsIso ((coker C).map (Arrow.homMk' s.f₁₃ s.f₂₄ s.fac.symm)) :=
  isIso_cokernel_map_of_isPushout hs

private theorem isIso_openPairCoker_of_openUnion {C : Type*} [Category* C]
    [HasZeroMorphisms C] [HasCokernels C] (R : Sm(k) ⥤ C) (B V : X.left.Opens)
    (hp : ((openUnionCoverSquare X V B).map R).IsPushout) :
    IsIso ((R.mapArrow ⋙ coker C).map
      (relativeOpenPairRestriction k X (le_sup_right : B ≤ V ⊔ B) le_sup_left)) := by
  let s := (openUnionCoverSquare X V B).map R
  let f := relativeOpenPairRestriction k X (le_sup_right : B ≤ V ⊔ B) le_sup_left
  change IsIso ((coker C).map (R.mapArrow.map f))
  have hf : R.mapArrow.map f = Arrow.homMk' s.f₁₃ s.f₂₄ s.fac.symm := by
    apply Arrow.hom_ext <;> rfl
  rw [hf]
  exact isIso_cokerMap_of_pushout s hp

private theorem transferOpenUnion_isPushout (B V : X.left.Opens) :
    ((openUnionCoverSquare X V B).map (smoothTransferRepresentable k)).IsPushout := by
  let sq := openUnionCoverSquare X V B
  let h₂ : IsOpenImmersion sq.f₂₄.left := openUnionCoverSquare_f₂₄_isOpenImmersion X V B
  let h₃ : IsOpenImmersion sq.f₃₄.left := openUnionCoverSquare_f₃₄_isOpenImmersion X V B
  exact @transferSquare_isPushout_of_openCover k _ sq
    (openUnionCoverSquare_isPullback X V B) h₂ h₃ (openUnionCoverSquare_range_cover X V B)

private theorem isIso_openPairFunctor_map_of_openUnion {C : Type*} [Category* C]
    [HasZeroMorphisms C] [HasCokernels C] (R : Sm(k) ⥤ C) (P : Arrow Sm(k) ⥤ C)
    (hP : P = R.mapArrow ⋙ coker C) (B V : X.left.Opens)
    (hp : ((openUnionCoverSquare X V B).map R).IsPushout) :
    IsIso (P.map (relativeOpenPairRestriction k X (le_sup_right : B ≤ V ⊔ B) le_sup_left)) :=
  hP.symm ▸ isIso_openPairCoker_of_openUnion k X R B V hp

private theorem isIso_transferPairCokernel_openUnion (B V : X.left.Opens) :
    IsIso ((transferPairCokernelFunctor k).map
      (relativeOpenPairRestriction k X (le_sup_right : B ≤ V ⊔ B) le_sup_left)) := by
  let C := SheafWithTransfers.{u + 1} k
  let R : Sm(k) ⥤ C := smoothTransferRepresentable k
  let P : Arrow Sm(k) ⥤ C := transferPairCokernelFunctor k
  have hP : P = R.mapArrow ⋙ coker C := rfl
  have hp : ((openUnionCoverSquare X V B).map R).IsPushout :=
    transferOpenUnion_isPushout k X B V
  exact isIso_openPairFunctor_map_of_openUnion k X R P hP B V hp

/-- The original transfer quotient map of an open excision is an isomorphism. -/
theorem isIso_transferPairCokernel_openExcision {B U V : X.left.Opens}
    (h : B ≤ U) (hV : V ≤ U) (hcover : B ⊔ V = U) :
    IsIso ((transferPairCokernelFunctor k).map (relativeOpenPairRestriction k X h hV)) := by
  rw [sup_comm] at hcover
  subst U
  exact isIso_transferPairCokernel_openUnion k X B V

private theorem isIso_opComp_map_of_isIso {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    (R : A ⥤ B) (L : B ⥤ C) (H : Cᵒᵖ ⥤ D) {U V : A} (d : U ⟶ V)
    (h : IsIso (R.map d)) : IsIso (((R ⋙ L).op ⋙ H).map d.op) := by
  let : IsIso (R.map d) := h
  let : IsIso (L.map (R.map d)) := L.map_isIso _
  change IsIso (H.map (L.map (R.map d)).op)
  exact H.map_isIso _

private theorem isIso_contravariant_map_of_isIso {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    (R : A ⥤ B) (L : B ⥤ C) (H : Cᵒᵖ ⥤ D) (F : Aᵒᵖ ⥤ D)
    (hF : F = (R ⋙ L).op ⋙ H) {U V : A} (d : U ⟶ V) (h : IsIso (R.map d)) :
    IsIso (F.map d.op) :=
  hF.symm ▸ isIso_opComp_map_of_isIso R L H d h

private theorem isIso_openRestriction_of_eq {C : Type*} [Category* C]
    (H : (Arrow Sm(k))ᵒᵖ ⥤ C) {B U B' V : X.left.Opens}
    (h : B ≤ U) (h' : B' ≤ V) (hB : B' ≤ B) (hV : V ≤ U)
    (hinter : B' = V ⊓ B) (hi : IsIso (H.map (relativeOpenPairRestriction k X h hV).op)) :
    IsIso (H.map (relativeOpenPairMap k X h' h hB hV).op) := by
  subst B'
  exact hi

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "DM(" field ")" => EffectiveMotivesMinus field

private theorem effectivePairCohomology_map_isIso_of_transferPairCokernel (K : DM(k)) (n : ℤ)
    {A B : Arrow Sm(k)} (d : A ⟶ B) (h : IsIso ((transferPairCokernelFunctor k).map d)) :
    IsIso ((effectivePairCohomology k K n).map d.op) := by
  let C := SheafWithTransfers.{u + 1} k
  let R : Arrow Sm(k) ⥤ C := transferPairCokernelFunctor k
  let L : C ⥤ DM(k) := effectiveTransferSheaf k
  let H : DM(k)ᵒᵖ ⥤ AddCommGrpCat.{w'} := preadditiveYoneda.obj (K⟦n⟧)
  let F : (Arrow Sm(k))ᵒᵖ ⥤ AddCommGrpCat.{w'} := effectivePairCohomology k K n
  have hF : F = (R ⋙ L).op ⋙ H := rfl
  exact isIso_contravariant_map_of_isIso R L H F hF d h

/-- An open containing the support induces an isomorphism on relative cohomology. -/
theorem isIso_relativeOpenPairCohomology_openExcision (K : DM(k)) (n : ℤ)
    {B U V : X.left.Opens} (h : B ≤ U) (hV : V ≤ U) (hcover : B ⊔ V = U) :
    IsIso ((effectivePairCohomology k K n).map (relativeOpenPairRestriction k X h hV).op) := by
  let d := relativeOpenPairRestriction k X h hV
  have hd : IsIso ((transferPairCokernelFunctor k).map d) :=
    isIso_transferPairCokernel_openExcision k X h hV hcover
  exact effectivePairCohomology_map_isIso_of_transferPairCokernel k K n d hd

/-- Open excision identifies a restriction whose source complement is the specified intersection. -/
theorem isIso_relativeOpenPairCohomology_openExcision_of_eq (K : DM(k)) (n : ℤ)
    {B U B' V : X.left.Opens} (h : B ≤ U) (h' : B' ≤ V) (hB : B' ≤ B) (hV : V ≤ U)
    (hinter : B' = V ⊓ B) (hcover : B ⊔ V = U) :
    IsIso ((effectivePairCohomology k K n).map (relativeOpenPairMap k X h' h hB hV).op) := by
  let H := effectivePairCohomology k K n
  have hi : IsIso (H.map (relativeOpenPairRestriction k X h hV).op) :=
    isIso_relativeOpenPairCohomology_openExcision k X K n h hV hcover
  exact isIso_openRestriction_of_eq k X H h h' hB hV hinter hi

/-- An empty support has zero relative cohomology. -/
theorem isZero_relativeOpenPairCohomology_refl (K : DM(k)) (n : ℤ) (U : X.left.Opens) :
    IsZero ((effectivePairCohomology k K n).obj
      (op (relativeOpenPair k X (le_rfl : U ≤ U)))) := by
  let R := smoothTransferRepresentable k
  let j := relativeOpenInclusion k X (le_rfl : U ≤ U)
  let : IsIso (R.map j) := by
    change IsIso (R.map ((SmoothSite.opensFunctor X).map (homOfLE (le_rfl : U ≤ U))))
    rw [show homOfLE (le_rfl : U ≤ U) = 𝟙 U from Subsingleton.elim _ _,
      (SmoothSite.opensFunctor X).map_id U, R.map_id ((SmoothSite.opensFunctor X).obj U)]
    infer_instance
  have hz : IsZero (cokernel (R.map j)) := isZero_cokernel_of_epi _
  exact (preadditiveYoneda.obj (K⟦n⟧)).map_isZero
    ((effectiveTransferSheaf k).map_isZero hz).op

end AlgebraicGeometry.MotivicHomotopy
