/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.GTheory.FiniteModules.ScalarBoundary
import Colib.Topology.Homotopy.HomotopyGroup.PeriodicLoopFamilies

open Topology CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped unitInterval ModuleCat.Algebra
noncomputable section
universe u v w

section ActualSerre
variable {C D : Type u} [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D]
  (P : ObjectProperty C) [P.IsSerreClass]
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]
  (R : Type w) [Ring R] [Linear R C] [Linear R D] [L.Linear R]
attribute [local instance] Abelian.hasFiniteBiproducts

-- No linear structure on the formal Serre quotient is required.
example (r : Rˣ) (a : (abelianExactStructure D).K 1) :
    SerreLocalization.actualConnectingHom P L 1
        (ScalarUnit.kOneAction R (abelianExactStructure D) r a) =
      (ScalarUnit.kZeroAction R (abelianExactStructure P.FullSubcategory) r
        (SerreLocalization.actualConnectingHom P L 0 a))⁻¹ :=
  SerreBoundary.actualConnectingHom_scalar P R L r a

-- Both source and unit laws belong to the actual operation, not supplied premises.
example (r s : Rˣ) (a b : (abelianExactStructure C).K 0) :
    ScalarUnit.kZeroAction R (abelianExactStructure C) (r * s) (a * b) =
      (ScalarUnit.kZeroAction R (abelianExactStructure C) r a *
        ScalarUnit.kZeroAction R (abelianExactStructure C) s a) *
      (ScalarUnit.kZeroAction R (abelianExactStructure C) r b *
        ScalarUnit.kZeroAction R (abelianExactStructure C) s b) := by
  rw [ScalarUnit.kZeroAction_source_mul, ScalarUnit.kZeroAction_unit_mul,
    ScalarUnit.kZeroAction_unit_mul]
end ActualSerre

section FiniteModules
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v, u} R]
  (S : Submonoid R)
attribute [local instance] Abelian.hasFiniteBiproducts

-- This uses the existing finite-module boundary and its literal kernel support term.
example (r : Rˣ) (a : FGModuleCat.FractionLocalization.G.{u, v} (Localization S) 1) :
    FGModuleCat.Localization.connectingHom S 1
        (ScalarUnit.smallModelKOneAction R
          (abelianExactStructure (FGModuleCat.{v} (Localization S))) r a) =
      (FGModuleCat.Localization.supportedScalarKZeroAction S r
        (FGModuleCat.Localization.connectingHom S 0 a))⁻¹ :=
  FGModuleCat.Localization.connectingHom_scalar S r a

-- The supported operation inherits the inverse law in its original source group.
example (r : Rˣ) (a : FGModuleCat.Localization.SupportedG.{u, v} S 0) :
    FGModuleCat.Localization.supportedScalarKZeroAction S r a⁻¹ =
      (FGModuleCat.Localization.supportedScalarKZeroAction S r a)⁻¹ :=
  map_inv _ _

-- No assumption excludes localization at a multiplicative set containing zero.
example (r : Rˣ)
    (a : FGModuleCat.FractionLocalization.G.{u, v} (Localization (⊤ : Submonoid R)) 1) :
    FGModuleCat.Localization.connectingHom (⊤ : Submonoid R) 1
        (ScalarUnit.smallModelKOneAction R
          (abelianExactStructure (FGModuleCat.{v} (Localization (⊤ : Submonoid R)))) r a) =
      (FGModuleCat.Localization.supportedScalarKZeroAction (⊤ : Submonoid R) r
        (FGModuleCat.Localization.connectingHom (⊤ : Submonoid R) 0 a))⁻¹ :=
  FGModuleCat.Localization.connectingHom_scalar (⊤ : Submonoid R) r a
end FiniteModules

section WholeFiberPath
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (y : Y)
  (HX : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
  (HY : (ContinuousMap.id Y).Homotopy (ContinuousMap.id Y))
  (hY : ∀ t, HY (t, y) = y) (hsq : ∀ t a, HY (t, f a) = f (HX (t, a)))

-- Every stored fiber-path point is retained, not only the two path endpoints.
example (t s : unitInterval) (z : HomotopyFiber f y) :
    (HomotopyFiber.identityHomotopy f y HX HY hY hsq (t, z)).1.2 s =
      HY (t, z.1.2 s) := rfl
end WholeFiberPath

section OriginalSign
variable {X : Type u} [TopologicalSpace X] {x : X}
  (H : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
  (hH : ∀ t, H (t, x) = x)

-- The track-first versus spatial-first normalization has the original inverse sign.
example (p : GenLoop (Fin 1) X x) :
    IdentityTrack.operation H hH 0 ⟦p⟧ =
      (loopKOneNormalization (genLoopHomeomorphOfUnique (Fin 1) p)
        (FundamentalGroup.fromPath
          ⟦(IdentityTrack.track H hH 0 p).map
            (genLoopHomeomorphOfUnique (Fin 1)).continuous⟧))⁻¹ :=
  IdentityTrack.operation_zero_normalization H hH p
end OriginalSign

section OriginalQNormalization
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (u : 𝟭 C ≅ 𝟭 C)

-- The original Q-operation wrapper keeps the generic inverse-normalization equation.
example (p : GenLoop (Fin 1) E.KSpace E.kBasepoint) :
    IdentityAutomorphism.kZeroAction E u ⟦p⟧ =
      (loopKOneNormalization (genLoopHomeomorphOfUnique (Fin 1) p)
        (FundamentalGroup.fromPath
          ⟦(IdentityTrack.track (IdentityAutomorphism.homotopy E u).toHomotopy
            (IdentityAutomorphism.homotopy_fixed E u) 0 p).map
            (genLoopHomeomorphOfUnique (Fin 1)).continuous⟧))⁻¹ :=
  IdentityTrack.operation_zero_normalization _ _ p
end OriginalQNormalization

section FiniteNaturalAutomorphisms
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v, u} R]
  (S : Submonoid R)
attribute [local instance] Abelian.hasFiniteBiproducts

-- The source's separate finite-module adapter is the native general action theorem.
example (u : Aut (𝟭 (SmallModel.{u} (FGModuleCat.{v} R))))
    (v : Aut (𝟭 (SmallModel.{u} (FGModuleCat.{v} (Localization S)))))
    (h : ∀ X, (FGModuleCat.localizationExactFunctor S).smallModel.toFunctor.map
      (u.asIso.hom.app X) =
        v.asIso.hom.app ((FGModuleCat.localizationExactFunctor S).smallModel.toFunctor.obj X))
    (a : FGModuleCat.FractionLocalization.G.{u, v} (Localization S) 1) :
    FGModuleCat.Localization.connectingHom S 1
        (IdentityAutomorphism.kOneAction
          (abelianExactStructure (FGModuleCat.{v} (Localization S))).smallModel v.asIso a) =
      (IdentityAutomorphism.kZeroAction
        (abelianExactStructure (FGModuleCat.Localization.supported S).FullSubcategory)
        (SerreBoundary.restrictedNatAut (FGModuleCat.Localization.supported S) u.asIso)
        (FGModuleCat.Localization.connectingHom S 0 a))⁻¹ :=
  SmallModelBoundary.connectingHom_action (FGModuleCat.localizationExactFunctor S) u v h a
end FiniteNaturalAutomorphisms

section CanonicalLoopProduct
variable {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z] {x : X}

-- The normalization and periodic-family owners share the very same native operation.
example (f g : C(Z, Path x x)) (z : Z) :
    IdentityTrack.loopProduct f g z = (f z).trans (g z) := rfl
end CanonicalLoopProduct
