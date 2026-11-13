/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.Restriction
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.Topology.Sheaves.RingedSpace.FlatModulePullback

/-!
# Original coherent pullback on native sheaf categories

The native module pullback preserves coherence when the source scheme is
locally Noetherian. Flatness is used only for exactness, through the existing
Stacks flat module-pullback theorem. The identity, composition and open
restriction comparisons are the original geometric natural isomorphisms.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y Z : Scheme.{u}}

/-- Actual coherent pullback; no flatness hypothesis is needed to preserve coherence. -/
def coherentPullback [IsLocallyNoetherian X] (f : X ⟶ Y) :
    SheafOfModules.CoherentModules Y.ringCatSheaf ⥤
      SheafOfModules.CoherentModules X.ringCatSheaf :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ pullback f)
    (fun M => isCoherent_pullback f M.obj)

instance coherentPullback_additive [IsLocallyNoetherian X] (f : X ⟶ Y) :
    (coherentPullback f).Additive where
  map_add {M N a b} := by
    apply ObjectProperty.hom_ext
    exact (pullback f).map_add

/-- Flatness makes the original coherent pullback exact. -/
def coherentExactPullback [IsLocallyNoetherian X] (f : X ⟶ Y) [Flat f] :
    ExactFunctor (coherentExactStructure Y) (coherentExactStructure X) where
  toFunctor := coherentPullback f
  map_conflation S hS := by
    have : PreservesFiniteLimits (pullback f) :=
      RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat
        f.toLRSHom.toShHom (fun x => Flat.stalkMap f x)
    apply (coherent_shortExact_iff_map X _).2
    exact ((coherent_shortExact_iff_map Y S).1 hS).map_of_exact (pullback f)

/-- The identity comparison is the original module-pullback identity. -/
def coherentPullbackIdIso (X : Scheme.{u}) [IsLocallyNoetherian X] :
    coherentPullback (𝟙 X) ≅ 𝟭 (SheafOfModules.CoherentModules X.ringCatSheaf) :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
    (Functor.isoWhiskerLeft (ObjectProperty.ι _) (pullbackId X))

/-- Composition is compared by the original module-pullback associativity isomorphism. -/
def coherentPullbackCompIso [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    coherentPullback (f ≫ g) ≅ coherentPullback g ⋙ coherentPullback f :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
    (Functor.isoWhiskerLeft (ObjectProperty.ι _) (pullbackComp f g).symm)

/-- On an open immersion the original coherent restriction is the same geometric pullback. -/
def coherentRestrictIsoPullback [IsLocallyNoetherian X] (j : X ⟶ Y) [IsOpenImmersion j] :
    coherentRestrict j ≅ coherentPullback j :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
    (Functor.isoWhiskerLeft (ObjectProperty.ι _) (restrictFunctorIsoPullback j))

end AlgebraicGeometry.Scheme.Modules
