/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.Coherent.ClosedPushforward
public import Colib.AlgebraicGeometry.KTheory.CoherentAffineComparison
public import Colib.Algebra.Category.FGModuleCat.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# Closed direct image and the affine G-comparison

The map is induced by actual coherent sheaf direct image. On affine schemes it
agrees with scalar restriction under the canonical global-sections comparison.
This is a comparison of the original functors, not a replacement definition of
geometric direct image. See the Stacks Project, Tag 087T, for the coherent image.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme

/-- Actual closed direct image on the existing coherent G-groups. -/
def closedPushforwardG {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsLocallyNoetherian X] (n : ℕ) : G Z n →* G X n :=
  (Modules.Coherent.closedPushforwardExact i).smallKMap.{u + 1} n

namespace Modules.Coherent
variable {R S : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing S]
  (φ : R ⟶ S) [IsClosedImmersion (Spec.map φ)] (hf : φ.hom.Finite)

/-- The literal affine closed pushforward becomes finite scalar restriction. -/
def closedPushforwardGlobalSectionsIso :
    ((closedPushforwardExact (Spec.map φ)).comp
      (affineGlobalSectionsExact R)).toFunctor ≅
    ((affineGlobalSectionsExact S).comp
      (FGModuleCat.finiteRestrictionExact φ.hom hf)).toFunctor := by
  apply Functor.fullyFaithfulCancelRight (forget₂ (FGModuleCat R) (ModuleCat R))
  exact Functor.isoWhiskerLeft (ObjectProperty.ι (fun M : (Spec S).Modules => M.IsCoherent))
    (AlgebraicGeometry.pushforwardΓIso R S φ)

/-- Compatibility on the original base-universe K-maps. -/
theorem closedPushforward_globalSections_smallKMap (n : ℕ) :
    ((affineGlobalSectionsExact R).smallKMap.{u} n).comp
      ((closedPushforwardExact (Spec.map φ)).smallKMap.{u} n) =
    ((FGModuleCat.finiteRestrictionExact φ.hom hf).smallKMap.{u} n).comp
      ((affineGlobalSectionsExact S).smallKMap.{u} n) := by
  have h := ExactFunctor.smallKMap_eq_of_natIso.{u}
    (closedPushforwardGlobalSectionsIso φ hf) n
  simpa only [ExactFunctor.smallKMap_comp] using h

/-- Actual geometric closed direct image agrees with finite restriction in every degree. -/
theorem publicSpecGRingEquiv_closedPushforward (n : ℕ) :
    (publicSpecGRingEquiv R n).toMonoidHom.comp
      (Scheme.closedPushforwardG (Spec.map φ) n) =
    ((FGModuleCat.finiteRestrictionExact φ.hom hf).smallKMap.{u} n).comp
      (publicSpecGRingEquiv S n).toMonoidHom := by
  let F := closedPushforwardExact (Spec.map φ)
  have hn := ExactFunctor.smallKUniverseEquiv_naturality.{u+1,u} F n
  ext a
  change specGRingEquiv R n
      ((coherentExactStructure (Spec R)).smallKUniverseEquiv.{u+1,u} n
        (Scheme.closedPushforwardG (Spec.map φ) n a)) =
    (FGModuleCat.finiteRestrictionExact φ.hom hf).smallKMap n
      (specGRingEquiv S n
        ((coherentExactStructure (Spec S)).smallKUniverseEquiv.{u+1,u} n a))
  have ht := DFunLike.congr_fun (specGRingEquiv_eq_globalSectionsKMap R n)
    ((coherentExactStructure (Spec R)).smallKUniverseEquiv.{u+1,u} n
      (Scheme.closedPushforwardG (Spec.map φ) n a))
  have hs := DFunLike.congr_fun (specGRingEquiv_eq_globalSectionsKMap S n)
    ((coherentExactStructure (Spec S)).smallKUniverseEquiv.{u+1,u} n a)
  change specGRingEquiv R n _ = _ at ht
  change specGRingEquiv S n _ = _ at hs
  rw [ht, hs]
  exact (congrArg ((affineGlobalSectionsExact R).smallKMap.{u} n)
    (DFunLike.congr_fun hn a).symm).trans
      (DFunLike.congr_fun (closedPushforward_globalSections_smallKMap φ hf n)
        ((coherentExactStructure (Spec S)).smallKUniverseEquiv.{u+1,u} n a))

end Modules.Coherent
end AlgebraicGeometry.Scheme
