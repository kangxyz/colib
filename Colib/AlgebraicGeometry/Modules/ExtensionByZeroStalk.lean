/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.ExtensionByZero
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# Stalks of extension by zero outside an open immersion

Extension by zero along an arbitrary open immersion has zero stalks outside its image.
The proof is the free-Yoneda presentation argument of
`StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero`, specialized directly
to the scheme's image functor on opens and inverse section isomorphisms. A presheaf extension
has zero sections on every open not contained in the image. Sheafification preserves its
stalks. This proves the off-image assertion of Stacks Project, Tag 00AB, for arbitrary
scheme open immersions, without replacing the source by a literal open subspace.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

namespace ExtensionByZero

/-- The presheaf restriction underlying open restriction. -/
noncomputable abbrev presheafRestrict :=
  PresheafOfModules.pushforward.{u} (extensionByZeroRingHom j).hom

/-- The presheaf extension whose sheafification is extension by zero. -/
noncomputable abbrev presheafExtension :=
  PresheafOfModules.pullback.{u} (extensionByZeroRingHom j).hom

/-- The extension of a free Yoneda module represents sections on the image open. -/
noncomputable def freeYonedaIso (V : U.Opens) :
    (presheafExtension j).obj
        ((PresheafOfModules.free U.ringCatSheaf.obj).obj (yoneda.obj V)) ≅
      (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj (j.opensFunctor.obj V)) := by
  let M := (PresheafOfModules.free U.ringCatSheaf.obj).obj (yoneda.obj V)
  let h : (presheafRestrict j ⋙ coyoneda.obj (op M)).CorepresentableBy
      ((presheafExtension j).obj M) :=
    { homEquiv {N} := (PresheafOfModules.pullbackPushforwardAdjunction _).homEquiv M N
      homEquiv_comp := fun _ _ =>
        (PresheafOfModules.pullbackPushforwardAdjunction _).homEquiv_naturality_right _ _ }
  exact h.uniqueUpToIso
    (PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy _ V)

private lemma isZero_freeYoneda_obj {V W : X.Opens} (h : ¬ V ≤ W) :
    IsZero (((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj W)).obj (op V)) := by
  have : Subsingleton
      (((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj W)).obj (op V)) :=
    ⟨fun _ _ => Finsupp.ext fun f => (h (leOfHom f)).elim⟩
  exact ModuleCat.isZero_of_subsingleton _

private lemma not_le_image {V : X.Opens} (hV : ¬ (V : Set X) ⊆ Set.range j)
    (W : U.Opens) : ¬ V ≤ j.opensFunctor.obj W := by
  intro h
  apply hV
  intro x hx
  obtain ⟨y, _, hy⟩ := h hx
  exact ⟨y, hy⟩

private lemma isZero_presheafExtension_freeYoneda (W : U.Opens) {V : X.Opens}
    (hV : ¬ (V : Set X) ⊆ Set.range j) :
    IsZero (((presheafExtension j).obj
      ((PresheafOfModules.free U.ringCatSheaf.obj).obj (yoneda.obj W))).obj (op V)) :=
  (isZero_freeYoneda_obj (not_le_image j hV W)).of_iso
    ((PresheafOfModules.evaluation X.ringCatSheaf.obj (op V)).mapIso (freeYonedaIso j W))

instance : PreservesColimitsOfSize.{u, u} (presheafExtension j) :=
  (PresheafOfModules.pullbackPushforwardAdjunction _).leftAdjoint_preservesColimits

instance : PreservesColimitsOfSize.{0, 0} (presheafExtension j) :=
  (PresheafOfModules.pullbackPushforwardAdjunction _).leftAdjoint_preservesColimits

private lemma isZero_presheafExtension_of_isColimit {J : Type*} [Category J] {F : J ⥤ _}
    {c : Cocone F} {V : X.Opens}
    [PreservesColimit F
      (presheafExtension j ⋙ PresheafOfModules.evaluation X.ringCatSheaf.obj (op V))]
    (hc : IsColimit c)
    (h : ∀ k, IsZero (((presheafExtension j).obj (F.obj k)).obj (op V))) :
    IsZero (((presheafExtension j).obj c.pt).obj (op V)) :=
  IsColimit.isZero_pt (isColimitOfPreserves
    (presheafExtension j ⋙ PresheafOfModules.evaluation X.ringCatSheaf.obj (op V)) hc)
    (Functor.isZero _ h)

private lemma isZero_presheafExtension_freeYonedaCoproduct
    (M : _root_.PresheafOfModules.{u} U.ringCatSheaf.obj) {V : X.Opens}
    (hV : ¬ (V : Set X) ⊆ Set.range j) :
    IsZero (((presheafExtension j).obj M.freeYonedaCoproduct).obj (op V)) :=
  isZero_presheafExtension_of_isColimit j (colimit.isColimit _) fun m =>
    isZero_presheafExtension_freeYoneda j m.as.1.unop hV

/-- A presheaf extension has zero sections on opens not contained in the image. -/
lemma isZero_presheafExtension_obj (M : _root_.PresheafOfModules.{u} U.ringCatSheaf.obj)
    {V : X.Opens} (hV : ¬ (V : Set X) ⊆ Set.range j) :
    IsZero (((presheafExtension j).obj M).obj (op V)) :=
  isZero_presheafExtension_of_isColimit j M.isColimitFreeYonedaCoproductsCokernelCofork
    fun k => by
      cases k <;> exact isZero_presheafExtension_freeYonedaCoproduct j _ hV

/-- The presheaf extension has zero stalks outside the image. -/
lemma isZero_stalk_presheafExtension (M : _root_.PresheafOfModules.{u} U.ringCatSheaf.obj)
    (x : X) (hx : x ∉ Set.range j) :
    IsZero (TopCat.Presheaf.stalk (X := X) ((presheafExtension j).obj M).presheaf x) := by
  refine IsColimit.isZero_pt (colimit.isColimit _) (Functor.isZero _ fun V => ?_)
  exact @AddCommGrpCat.isZero_of_subsingleton _
    (ModuleCat.isZero_iff_subsingleton.1
      (isZero_presheafExtension_obj j M fun h => hx (h V.unop.2)))

/-- The underlying abelian presheaf of extension by zero is the sheafification of the
underlying presheaf extension. -/
noncomputable def presheafIso (M : U.Modules) :
    ((extensionByZero j).obj M).val.presheaf ≅
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          ((presheafExtension j).obj M.val).presheaf) :=
  (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf X.ringCatSheaf.obj).mapIso
      ((SheafOfModules.pullbackIso (extensionByZeroRingHom j)).app M) ≪≫
    (PresheafOfModules.sheafificationCompForgetCompToPresheaf (𝟙 X.ringCatSheaf.obj)).app _

end ExtensionByZero

/-- Extension by zero has zero stalk at every point outside the open immersion's image. -/
theorem isZero_stalk_extensionByZero (M : U.Modules) (x : X) (hx : x ∉ Set.range j) :
    IsZero (TopCat.Presheaf.stalk (X := X) ((extensionByZero j).obj M).val.presheaf x) := by
  have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X)
        ((ExtensionByZero.presheafExtension j).obj M.val).presheaf)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _
  exact ((ExtensionByZero.isZero_stalk_presheafExtension j M.val x hx).of_iso
    (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X)
        ((ExtensionByZero.presheafExtension j).obj M.val).presheaf))).symm).of_iso
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      (ExtensionByZero.presheafIso j M))

end AlgebraicGeometry.Scheme.Modules
