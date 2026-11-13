/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Quillen.Localization.Serre.Naturality
public import Colib.RingTheory.KTheory.GTheory.FiniteModules.Localization
public import Colib.KTheory.Quillen.SmallModel.Functoriality

/-!
# Naturality of the original finite-module localization boundary

An ordinary natural isomorphism between two composites of exact finite-module
functors induces a square on the actual chosen small-model localization
sequences. The support functor is the restriction of the original small-model
ambient functor. Preservation of the kernel is a consequence of the ordinary
localization square.

`connectingHom_naturality` retains the original `connectingHom` on both sides
and the original `smallKMap` on localized modules. The proof transports the
canonical Serre boundary theorem through both actual `SmallModelLocalization.standardKEquiv`
comparisons. All endpoints use the common native universe `u`.
-/

/-! Implementation source: `Quillen/GTheory/FiniteModules/LocalizationNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; original maps and hypotheses are retained. -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory ModuleCat

namespace FGModuleCat.Localization

attribute [local instance] Abelian.hasFiniteBiproducts

variable {R R' : Type u} [CommRing R] [CommRing R'] [IsNoetherianRing R] [IsNoetherianRing R']
  (S : Submonoid R) (T : Submonoid R')
  (V : ExactFunctor ((abelianExactStructure (FGModuleCat.{u} R))) ((abelianExactStructure
    (FGModuleCat.{u} R'))))
  (W : ExactFunctor ((abelianExactStructure (FGModuleCat.{u} (Localization S))))
    ((abelianExactStructure (FGModuleCat.{u} (Localization T)))))
  (hV : ∀ X : SmallModel.{u} (FGModuleCat.{u} R), FGModuleCat.Localization.supported.{u, u} S X →
    FGModuleCat.Localization.supported.{u, u} T (V.smallModel.toFunctor.obj X))
  (e : ((FGModuleCat.localizationExactFunctor S).comp W).toFunctor ≅ (V.comp
    (FGModuleCat.localizationExactFunctor T)).toFunctor)

/-- Restrict the original small-model ambient functor to the actual support kernels. -/
def inducedSupportedExactFunctor : ExactFunctor ((abelianExactStructure
  (FGModuleCat.Localization.supported.{u, u} S).FullSubcategory)) ((abelianExactStructure
  (FGModuleCat.Localization.supported.{u, u} T).FullSubcategory)) :=
  SerreLocalization.inducedSupportExactFunctor (FGModuleCat.Localization.supported.{u, u} S)
    (FGModuleCat.Localization.supported.{u, u} T)
    (CategoryTheory.SmallModel.mapAbelianExactFunctor V) hV

/-- The given ordinary square transported through the canonical small-model
composition isomorphisms, with all original localization functors retained. -/
def smallLocalizationSquareIso :
    (FGModuleCat.localizationExactFunctor S).smallModel.toFunctor ⋙
      (CategoryTheory.SmallModel.mapAbelianExactFunctor W).toFunctor ≅
      (CategoryTheory.SmallModel.mapAbelianExactFunctor V).toFunctor ⋙
        (FGModuleCat.localizationExactFunctor T).smallModel.toFunctor :=
  (ExactFunctor.smallModelCompIso (FGModuleCat.localizationExactFunctor S) W).symm ≪≫
    ExactFunctor.smallModelNatIso e ≪≫ ExactFunctor.smallModelCompIso V
      (FGModuleCat.localizationExactFunctor T)

include e in
/-- An exact localization square carries its actual Serre kernel into the target kernel. -/
theorem smallTorsion_map_of_exactSquare (X : SmallModel.{u} (FGModuleCat.{u} R))
    (hX : FGModuleCat.Localization.supported.{u, u} S X) : FGModuleCat.Localization.supported.{u,
      u} T (V.smallModel.toFunctor.obj X) := by
  have hz : IsZero ((CategoryTheory.SmallModel.mapAbelianExactFunctor W).toFunctor.obj
    (((FGModuleCat.localizationExactFunctor S).smallModel.toFunctor).obj X)) :=
    (CategoryTheory.SmallModel.mapAbelianExactFunctor W).toFunctor.map_isZero hX
  exact hz.of_iso ((smallLocalizationSquareIso S T V W e).app X).symm

/-- The canonical restricted exact functor whose kernel preservation follows
from the given ordinary localization square. -/
def inducedSupportedExactFunctorOfSquare : ExactFunctor
    ((abelianExactStructure (FGModuleCat.Localization.supported.{u, u} S).FullSubcategory))
    ((abelianExactStructure (FGModuleCat.Localization.supported.{u, u} T).FullSubcategory)) :=
  inducedSupportedExactFunctor S T V (smallTorsion_map_of_exactSquare S T V W e)

include e

set_option maxHeartbeats 800000 in
-- The two native boundaries unfold their canonical small-model comparisons.
/-- Naturality of the original finite-module boundary, retaining any supplied
proof that the original ambient functor preserves the actual support kernel. -/
theorem connectingHom_naturality_of_exactSquare (n : ℕ) :
    ((inducedSupportedExactFunctor S T V hV).KMap n).comp (connectingHom S n) =
      (connectingHom T n).comp (W.smallKMap (n + 1)) := by
  let U := CategoryTheory.SmallModel.mapAbelianExactFunctor W
  have hn := SerreLocalization.actualConnectingHom_naturality
    (FGModuleCat.Localization.supported.{u, u} S) (FGModuleCat.Localization.supported.{u, u} T)
    (CategoryTheory.SmallModel.mapAbelianExactFunctor V) hV
      ((FGModuleCat.localizationExactFunctor S).smallModel.toFunctor)
      ((FGModuleCat.localizationExactFunctor T).smallModel.toFunctor)
    U (smallLocalizationSquareIso S T V W e) n
  apply MonoidHom.ext
  intro a
  change (inducedSupportedExactFunctor S T V hV).KMap n
      (SerreLocalization.actualConnectingHom (FGModuleCat.Localization.supported.{u, u} S)
        ((FGModuleCat.localizationExactFunctor S).smallModel.toFunctor) n
        (SmallModelLocalization.standardKEquiv (FGModuleCat.{u} (Localization S)) (n + 1) a)) =
    SerreLocalization.actualConnectingHom (FGModuleCat.Localization.supported.{u, u} T)
      ((FGModuleCat.localizationExactFunctor T).smallModel.toFunctor) n
      (SmallModelLocalization.standardKEquiv (FGModuleCat.{u} (Localization T)) (n + 1)
        (W.smallKMap (n + 1) a))
  have hu := DFunLike.congr_fun (SmallModelLocalization.smallKMap_comparison W (n + 1)) a
  change SmallModelLocalization.standardKEquiv (FGModuleCat.{u} (Localization T)) (n + 1)
    (W.smallKMap (n + 1) a) =
    U.KMap (n + 1) (SmallModelLocalization.standardKEquiv (FGModuleCat.{u} (Localization S)) (n +
      1) a) at hu
  exact (DFunLike.congr_fun hn (SmallModelLocalization.standardKEquiv (FGModuleCat.{u}
    (Localization S)) (n + 1) a)).trans
    (congrArg (SerreLocalization.actualConnectingHom (FGModuleCat.Localization.supported.{u, u}
      T) ((FGModuleCat.localizationExactFunctor T).smallModel.toFunctor) n) hu.symm)

/-- Naturality of the original finite-module boundary from the actual ordinary
localization square, with no separate support-compatibility hypothesis. -/
theorem connectingHom_naturality (n : ℕ) :
    ((inducedSupportedExactFunctorOfSquare S T V W e).KMap n).comp (connectingHom S n) =
      (connectingHom T n).comp (W.smallKMap (n + 1)) :=
  connectingHom_naturality_of_exactSquare S T V W
    (smallTorsion_map_of_exactSquare S T V W e) e n

end FGModuleCat.Localization
