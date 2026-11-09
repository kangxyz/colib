/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Quillen.LowDegreeScalarAction.SerreBoundary
public import Colib.KTheory.Quillen.Localization.SmallModel

/-!
# Scalar operations and the original SmallModel localization boundary

The canonical comparison with the standard abelian exact structure is induced
by its actual exact identity functor. Ordinary natural-automorphism compatibility
therefore proves action transport through this precise K-equivalence.
The resulting boundary formula uses the original SmallK source and the actual
kernel support term, retaining the original inverse sign.

The supported scalar automorphism is the restriction of the original lifted
SmallModel scalar automorphism. No linear structure on a chosen model or on the
formal Serre quotient is introduced.

The native finite-module specialization already uses the abelian exact structure
and the general SmallModelGLocalization comparison. Its former separate comparison
adapters are therefore instances of the general theorems here. At the ring owner,
ordinary linearity of the actual localization map gives the original finite-module
boundary formula, with the literal kernel support term and base-ring scalars.
-/
/-! Implementation provenance: `Quillen/KTheory/LowDegreeScalarAction/SmallModelBoundary.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual native exact-model functors and
the canonical boundary are retained; finite-module specializations have their ring owner. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Linear
attribute [local instance] Abelian.hasFiniteBiproducts
universe r w u₁ v₁ u₂ v₂
namespace CategoryTheory.ExactCategory.SmallModelBoundary

section StandardComparison
variable (C : Type u₁) [Category.{v₁} C] [Abelian C] [EssentiallySmall.{w} C]

/-- The original standard comparison transports degree-(0,1) action through
its actual exact identity functor. -/
theorem standardKEquiv_kZeroAction (u : Aut (𝟭 (SmallModel.{w} C)))
    (a : (abelianExactStructure C).SmallK.{w} 0) :
    SmallModelLocalization.standardKEquiv C 1
        (IdentityAutomorphism.kZeroAction (abelianExactStructure C).smallModel u.asIso a) =
      IdentityAutomorphism.kZeroAction (abelianExactStructure (SmallModel.{w} C)) u.asIso
        (SmallModelLocalization.standardKEquiv C 0 a) :=
  IdentityAutomorphism.kZeroAction_natural.{w, w}
    (CategoryTheory.SmallModel.abelianExactComparison.{w} C) u.asIso u.asIso (fun _ => rfl) a

/-- The original standard comparison transports degree-(1,1) action through
its actual exact identity functor. -/
theorem standardKEquiv_kOneAction (u : Aut (𝟭 (SmallModel.{w} C)))
    (a : (abelianExactStructure C).SmallK.{w} 1) :
    SmallModelLocalization.standardKEquiv C 2
        (IdentityAutomorphism.kOneAction (abelianExactStructure C).smallModel u.asIso a) =
      IdentityAutomorphism.kOneAction (abelianExactStructure (SmallModel.{w} C)) u.asIso
        (SmallModelLocalization.standardKEquiv C 1 a) :=
  IdentityAutomorphism.kOneAction_natural.{w, w}
    (CategoryTheory.SmallModel.abelianExactComparison.{w} C) u.asIso u.asIso (fun _ => rfl) a
end StandardComparison

section Restriction
variable {A : Type w} [Category.{w} A] [Abelian A] (P : ObjectProperty A)

/-- Actual restriction of identity automorphisms preserves their group product. -/
def restrictedNatAutHom : Aut (𝟭 A) →* Aut (𝟭 P.FullSubcategory) where
  toFun u := ⟨SerreBoundary.restrictedNatAut P u.asIso⟩
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply NatTrans.ext
    funext X
    rfl
  map_mul' u v := by
    apply Aut.ext
    apply Iso.ext
    apply NatTrans.ext
    funext X
    rfl
end Restriction

section Localization
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D))
  [PreservesFiniteLimits F.toFunctor] [PreservesFiniteColimits F.toFunctor]
  [F.toFunctor.IsLocalization F.toFunctor.kernel.isoModSerre]

/-- The original SmallModel boundary has the signed identity-automorphism
formula from ordinary compatibility of the actual chosen-model functor. -/
theorem connectingHom_action (u : Aut (𝟭 (SmallModel.{w} C)))
    (v : Aut (𝟭 (SmallModel.{w} D)))
    (h : ∀ X, F.smallModel.toFunctor.map (u.asIso.hom.app X) =
      v.asIso.hom.app (F.smallModel.toFunctor.obj X))
    (a : (abelianExactStructure D).SmallK.{w} 1) :
    SmallModelGLocalization.connectingHom F 1
        (IdentityAutomorphism.kOneAction (abelianExactStructure D).smallModel v.asIso a) =
      (IdentityAutomorphism.kZeroAction
        (abelianExactStructure (SmallModelGLocalization.supported F).FullSubcategory)
        (SerreBoundary.restrictedNatAut (SmallModelGLocalization.supported F) u.asIso)
        (SmallModelGLocalization.connectingHom F 0 a))⁻¹ := by
  change SerreLocalization.actualConnectingHom (SmallModelGLocalization.supported F)
      F.smallModel.toFunctor 1
      (SmallModelLocalization.standardKEquiv D 2
        (IdentityAutomorphism.kOneAction (abelianExactStructure D).smallModel v.asIso a)) = _
  rw [standardKEquiv_kOneAction]
  exact SerreBoundary.actualConnectingHom_action (SmallModelGLocalization.supported F) u.asIso
    F.smallModel.toFunctor v.asIso h
    (SmallModelLocalization.standardKEquiv D 1 a)

variable (R : Type r) [Ring R] [Linear R C]

/-- The actual supported degree-(0,1) scalar operation, obtained by restricting
the original lifted scalar automorphism to the literal kernel subcategory. -/
def supportedKZeroAction :
    Rˣ →* (SmallModelGLocalization.SupportedK.{w} F 0 →*
      SmallModelGLocalization.SupportedK.{w} F 1) :=
  ScalarUnit.kZeroActionOf.{r, w, w} R
    (abelianExactStructure (SmallModelGLocalization.supported F).FullSubcategory)
    ((restrictedNatAutHom (SmallModelGLocalization.supported F)).comp
      (smallModelScalarNatAut R C))

omit [F.toFunctor.IsLocalization F.toFunctor.kernel.isoModSerre] in
/-- The supported operation retains exactly the restricted original automorphism. -/
@[simp] theorem supportedKZeroAction_apply (r : Rˣ)
    (a : SmallModelGLocalization.SupportedK.{w} F 0) :
    supportedKZeroAction F R r a = IdentityAutomorphism.kZeroAction
      (abelianExactStructure (SmallModelGLocalization.supported F).FullSubcategory)
      (SerreBoundary.restrictedNatAut (SmallModelGLocalization.supported F)
        (smallModelScalarNatAut R C r).asIso) a := rfl

variable [Linear R D] [F.toFunctor.Linear R]

/-- Scalar compatibility for the original SmallK boundary follows from ordinary
linearity and the actual lifted automorphisms; neither model needs a linear structure. -/
theorem connectingHom_scalar (r : Rˣ) (a : (abelianExactStructure D).SmallK.{w} 1) :
    SmallModelGLocalization.connectingHom F 1
        (ScalarUnit.smallModelKOneAction R (abelianExactStructure D) r a) =
      (supportedKZeroAction F R r (SmallModelGLocalization.connectingHom F 0 a))⁻¹ :=
  connectingHom_action F (smallModelScalarNatAut R C r) (smallModelScalarNatAut R D r)
    (ScalarUnit.smallModelScalarNatAut_map R F r) a
end Localization


end CategoryTheory.ExactCategory.SmallModelBoundary

attribute [colib_ref "quillen"
  "Quillen/KTheory/LowDegreeScalarAction/SmallModelBoundary.lean:47-149"
  "adaptation" "Original maps, whole tracks, native model comparisons and signs"]
  CategoryTheory.ExactCategory.SmallModelBoundary.standardKEquiv_kZeroAction
  CategoryTheory.ExactCategory.SmallModelBoundary.standardKEquiv_kOneAction
  CategoryTheory.ExactCategory.SmallModelBoundary.restrictedNatAutHom
  CategoryTheory.ExactCategory.SmallModelBoundary.connectingHom_action
  CategoryTheory.ExactCategory.SmallModelBoundary.supportedKZeroAction
  CategoryTheory.ExactCategory.SmallModelBoundary.supportedKZeroAction_apply
  CategoryTheory.ExactCategory.SmallModelBoundary.connectingHom_scalar

attribute [colib_tag "COL-0377"]
  CategoryTheory.ExactCategory.SmallModelBoundary.connectingHom_scalar
