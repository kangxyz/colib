/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.NeighborhoodGerms
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.Adjunction
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import Mathlib.CategoryTheory.Sites.Point.Category
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChange

/-!
# The actual small-base geometric stalk of smooth étale extension

The geometric germ comparison is transported through the native comapped-point
stalk isomorphism and the existing full-small dense-basis equivalence. The result
computes the fiber of the actual extension functor at the original smooth
neighborhood point. No counit invertibility or rigidity assertion is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {S : Scheme.{u}} [IsAffine S]

/-- The actual small-base inclusion preserves the terminal object. -/
instance toSmoothSite_base_preservesTerminal :
    PreservesLimit (Functor.empty.{0} (EtaleSeparatedFiniteType (SmoothSite.base S).left))
      (toSmoothSite (SmoothSite.base S)) := by
  let : smoothSeparatedFiniteType.{u}.ContainsIdentities :=
    ⟨fun X ↦ ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩⟩
  apply preservesLimit_of_preserves_limit_cone
    (MorphismProperty.Over.mkIdTerminal etaleSeparatedFiniteType S)
  refine (isLimitMapConeEmptyConeEquiv (toSmoothSite (SmoothSite.base S)) _).symm ?_
  exact (MorphismProperty.Over.mkIdTerminal smoothSeparatedFiniteType S).ofIso
    (MorphismProperty.Over.isoMk (Iso.refl S) (by simp [toSmoothSite, SmoothSite.base,
      SmoothSite.mk, MorphismProperty.Over.mk_hom]))

/-- The actual inclusion of small-base objects is representably flat. -/
instance toSmoothSite_base_representablyFlat :
    RepresentablyFlat (toSmoothSite (SmoothSite.base S)) := by
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) (toSmoothSite (SmoothSite.base S)) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  let : PreservesFiniteLimits (toSmoothSite (SmoothSite.base S)) :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  exact flat_of_preservesFiniteLimits _

/-- The literal basis inclusion into the full small site preserves finite limits. -/
instance toSmallEtale_preservesFiniteLimits : PreservesFiniteLimits (toSmallEtale S) := by
  have : PreservesFiniteLimits (toSmallEtale S ⋙ Etale.forget S) :=
    inferInstanceAs (PreservesFiniteLimits
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ S))
  exact preservesFiniteLimits_of_reflects_of_preserves (toSmallEtale S) (Etale.forget S)

/-- The literal basis inclusion is representably flat. -/
instance toSmallEtale_representablyFlat : RepresentablyFlat (toSmallEtale S) :=
  flat_of_preservesFiniteLimits _

local instance :
    (toSmallEtale S).IsDenseSubsite (etaleTopology S) S.smallEtaleTopology :=
  toSmallEtale_isDenseSubsite (SmoothSite.base S)

/-- The original basis inclusion preserves the full small-site covering sieves. -/
theorem toSmallEtale_coverPreserving :
    CoverPreserving (etaleTopology S) S.smallEtaleTopology (toSmallEtale S) :=
  Functor.IsDenseSubsite.coverPreserving _ _ _

variable (Y : SmoothSite S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ Y.left)

local instance : InitiallySmall.{u + 1} (SmoothSite.EtaleNeighborhood Y ξ) :=
  SmoothSite.etaleNeighborhoodInitiallySmall.{u, u + 1} Y ξ

/-- The native small-base geometric point, raised only to the coefficient universe. -/
abbrev baseGeometricPoint : S.smallEtaleTopology.Point.{u + 1} :=
  (pointSmallEtale (show Spec (.of Ω) ⟶ S from ξ ≫ Y.hom)).ulift.{u + 1}

local instance : InitiallySmall.{u + 1}
    (toSmoothSite (SmoothSite.base S) ⋙
      (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).fiber).Elements :=
  initiallySmall_of_essentiallySmall _

local instance : InitiallySmall.{u + 1}
    (toSmallEtale S ⋙ (baseGeometricPoint Y ξ).fiber).Elements :=
  initiallySmall_of_essentiallySmall _

/-- The smooth-neighborhood point comapped through the actual small-base inclusion. -/
abbrev smoothNeighborhoodComapPoint : (etaleTopology S).Point.{u + 1} :=
  (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).comap
    (toSmoothSite (SmoothSite.base S))
      (toSmoothSite_etale_coverPreserving (SmoothSite.base S))

/-- The native base geometric point comapped to the actual separated finite-type basis. -/
abbrev baseGeometricComapPoint : (etaleTopology S).Point.{u + 1} :=
  (baseGeometricPoint Y ξ).comap (toSmallEtale S) toSmallEtale_coverPreserving

/-- The comapped point is the native base geometric point on the actual basis.
Its underlying fiber isomorphism is evaluation of original scheme-map germs at the marking. -/
@[colib_tag "COL-1104"]
def smoothNeighborhoodBasePointIso :
    smoothNeighborhoodComapPoint Y ξ ≅ baseGeometricComapPoint Y ξ where
  hom := ⟨(etaleNeighborhoodBaseFiberIso Y ξ).inv⟩
  inv := ⟨(etaleNeighborhoodBaseFiberIso Y ξ).hom⟩
  hom_inv_id := by
    apply GrothendieckTopology.Point.Hom.ext
    exact (etaleNeighborhoodBaseFiberIso Y ξ).hom_inv_id
  inv_hom_id := by
    apply GrothendieckTopology.Point.Hom.ext
    exact (etaleNeighborhoodBaseFiberIso Y ξ).inv_hom_id

/-- The original comparison of points induces the corresponding comparison of sheaf fibers. -/
def smoothNeighborhoodBaseSheafFiberIso :
    (smoothNeighborhoodComapPoint Y ξ).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      (baseGeometricComapPoint Y ξ).sheafFiber where
  hom := (smoothNeighborhoodBasePointIso Y ξ).inv.sheafFiber
  inv := (smoothNeighborhoodBasePointIso Y ξ).hom.sheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, Iso.hom_inv_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, Iso.inv_hom_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]

/-- The native small-site pullback is canonically the actual dense-basis equivalence. -/
def toSmallEtalePullbackEquivIso :
    (toSmallEtale S).sheafPullback AddCommGrpCat.{u + 1}
        (etaleTopology S) S.smallEtaleTopology ≅
      (sheafEquivSmallEtale (SmoothSite.base S)).functor :=
  Adjunction.leftAdjointUniq
    ((toSmallEtale S).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (etaleTopology S) S.smallEtaleTopology)
    (sheafEquivSmallEtale (SmoothSite.base S)).toAdjunction

/-- The fiber of the actual basis extension is the native base stalk of its full-small sheaf. -/
def etaleExtendBaseSheafFiberIso :
    etaleExtend (SmoothSite.base S) ⋙
        (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).sheafFiber ≅
      (sheafEquivSmallEtale (SmoothSite.base S)).functor ⋙
        (baseGeometricPoint Y ξ).sheafFiber (A := AddCommGrpCat.{u + 1}) :=
  ((SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).sheafFiberComapIso
    (toSmoothSite (SmoothSite.base S))
      (toSmoothSite_etale_coverPreserving (SmoothSite.base S)) AddCommGrpCat.{u + 1}).symm ≪≫
    smoothNeighborhoodBaseSheafFiberIso Y ξ ≪≫
      (baseGeometricPoint Y ξ).sheafFiberComapIso (toSmallEtale S)
        toSmallEtale_coverPreserving AddCommGrpCat.{u + 1} ≪≫
          Functor.isoWhiskerRight (toSmallEtalePullbackEquivIso (S := S))
            (baseGeometricPoint Y ξ).sheafFiber

/-- The actual full-small extension has the native stalk at the composite base marking,
naturally in the original full-small coefficient sheaf. -/
def fullSmallEtaleExtendBaseSheafFiberIso :
    fullSmallEtaleExtend (SmoothSite.base S) ⋙
        (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).sheafFiber ≅
      (baseGeometricPoint Y ξ).sheafFiber (A := AddCommGrpCat.{u + 1}) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sheafEquivSmallEtale (SmoothSite.base S)).inverse
      (etaleExtendBaseSheafFiberIso Y ξ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafEquivSmallEtale (SmoothSite.base S)).counitIso
      (baseGeometricPoint Y ξ).sheafFiber ≪≫
    (baseGeometricPoint Y ξ).sheafFiber.leftUnitor

/-- Universe raising preserves the actual native small-base stalk, with its original
category of marked etale objects and no change of the coefficient sheaf. -/
def nativeBaseGeometricStalkIso (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (pointSmallEtale (ξ ≫ Y.hom)).sheafFiber.obj G ≅
      (baseGeometricPoint Y ξ).sheafFiber.obj G :=
  Functor.Final.colimitIso
    (Functor.Elements.uliftEquiv.{u + 1} (pointSmallEtale (ξ ≫ Y.hom)).fiber).functor.op
      ((Functor.Elements.π (baseGeometricPoint Y ξ).fiber).op ⋙ G.obj)

omit [IsAffine S] in
/-- The native-stalk universe comparison sends each original germ to the very same marked germ. -/
@[reassoc]
theorem toPresheafFiber_nativeBaseGeometricStalkIso_hom
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : S.Etale) (x : (pointSmallEtale (ξ ≫ Y.hom)).fiber.obj U) :
    (pointSmallEtale (ξ ≫ Y.hom)).toPresheafFiber U x G.obj ≫
        (nativeBaseGeometricStalkIso Y ξ G).hom =
      (baseGeometricPoint Y ξ).toPresheafFiber U (ULift.up x) G.obj :=
  Functor.Final.ι_colimitIso_hom
    (Functor.Elements.uliftEquiv.{u + 1} (pointSmallEtale (ξ ≫ Y.hom)).fiber).functor.op
    ((Functor.Elements.π (baseGeometricPoint Y ξ).fiber).op ⋙ G.obj)
    (op ((pointSmallEtale (ξ ≫ Y.hom)).fiber.elementsMk U x))

omit [IsAffine S] in
/-- The native-stalk universe comparison preserves the original coefficient maps. -/
@[reassoc]
theorem nativeBaseGeometricStalkIso_naturality
    {G H : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : G ⟶ H) :
    (pointSmallEtale (ξ ≫ Y.hom)).sheafFiber.map f ≫
        (nativeBaseGeometricStalkIso Y ξ H).hom =
      (nativeBaseGeometricStalkIso Y ξ G).hom ≫
        (baseGeometricPoint Y ξ).sheafFiber.map f := by
  apply (pointSmallEtale (ξ ≫ Y.hom)).presheafFiber_hom_ext
  intro U x
  change (pointSmallEtale (ξ ≫ Y.hom)).toPresheafFiber U x G.obj ≫
    ((pointSmallEtale (ξ ≫ Y.hom)).presheafFiber.map f.hom ≫ _) = _
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality_assoc,
    toPresheafFiber_nativeBaseGeometricStalkIso_hom]
  erw [toPresheafFiber_nativeBaseGeometricStalkIso_hom_assoc]
  exact ((baseGeometricPoint Y ξ).toPresheafFiber_naturality f.hom U (ULift.up x)).symm

/-- The actual full-small extension fiber is naturally the original native small-base stalk,
without a changed marking, coefficient object, or arbitrary chosen stalk model. -/
@[colib_tag "COL-1104", colib_ref "mathlib_stable_localization_pin"
  "Mathlib/CategoryTheory/Sites/Point/Comap.lean:63-73"
  "ingredient" "Native stalk comparison for the actual continuous-site pullback"]
def fullSmallEtaleExtendNativeBaseSheafFiberIso :
    fullSmallEtaleExtend (SmoothSite.base S) ⋙
        (SmoothSite.etaleNeighborhoodPoint.{u, u + 1} Y ξ).sheafFiber ≅
      (pointSmallEtale (ξ ≫ Y.hom)).sheafFiber (A := AddCommGrpCat.{u + 1}) :=
  fullSmallEtaleExtendBaseSheafFiberIso Y ξ ≪≫
    (NatIso.ofComponents (nativeBaseGeometricStalkIso Y ξ)
      (fun f ↦ nativeBaseGeometricStalkIso_naturality Y ξ f)).symm

/-- The point comparison evaluates an original smooth-neighborhood representative at its
actual marking, giving the native lift over the composite base point. -/
@[colib_tag "COL-1104", simp]
theorem smoothNeighborhoodBasePointIso_inv_hom_app_fiberMk
    (U : EtaleSeparatedFiniteType S) (A : SmoothSite.EtaleNeighborhood Y ξ)
    (f : (SmoothSite.etaleNeighborhoodToSmooth Y ξ).obj A ⟶
      (toSmoothSite (SmoothSite.base S)).obj U) :
    (smoothNeighborhoodBasePointIso Y ξ).inv.hom.app U
        (GrothendieckTopology.Point.ofIsCofiltered.fiberMk.{u + 1} f) =
      ULift.up (etaleNeighborhoodMapLift Y ξ U A f) :=
  etaleNeighborhoodGermToLift_fiberMk Y ξ U A f

/-- The dense-basis pullback comparison preserves the actual native adjunction unit. -/
@[reassoc]
theorem toSmallEtalePullbackEquivIso_unit_app
    (G : Sheaf (etaleTopology S) AddCommGrpCat.{u + 1}) :
    ((toSmallEtale S).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (etaleTopology S) S.smallEtaleTopology).unit.app G ≫
      (sheafEquivSmallEtale (SmoothSite.base S)).inverse.map
        ((toSmallEtalePullbackEquivIso (S := S)).hom.app G) =
      (sheafEquivSmallEtale (SmoothSite.base S)).toAdjunction.unit.app G :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ G

/-- The dense-basis pullback comparison preserves the actual native adjunction counit. -/
@[reassoc]
theorem toSmallEtalePullbackEquivIso_counit_app
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (toSmallEtalePullbackEquivIso (S := S)).hom.app
        ((sheafEquivSmallEtale (SmoothSite.base S)).inverse.obj G) ≫
      (sheafEquivSmallEtale (SmoothSite.base S)).toAdjunction.counit.app G =
      ((toSmallEtale S).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (etaleTopology S) S.smallEtaleTopology).counit.app G :=
  Adjunction.leftAdjointUniq_hom_app_counit _ _ G

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
