/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Parameter
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Cokernels
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Parameters
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Presheaf
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Contraction of actual presheaves with transfers

`contraction P` is the cokernel of restriction from the actual affine-line
product to its Laurent principal open. Its transfer action descends the actual
signed exterior correspondence, and its sections are the literal group quotient.
No sheafification or strict A¹-invariance is used.

Adapted from `motivic_source_a6805c4`,
`Motivic/Transfers/Presheaf/Contraction.lean:43-162`.
The actual categorical cokernel is taken in the native bundled additive-functor
category, using its existing section-quotient comparison. Graph restriction is
identified with the previously constructed ordinary geometric quotient,
including its actual projection. General exterior composition is an imported
source-level dependency still pending native validation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

local instance : PreservesFiniteColimits (toPresheaf.{v} k) := by
  dsimp [toPresheaf, restrictAlong]
  infer_instance

/-- Coefficients on the genuine affine-line cylinder. -/
abbrev affineLineSections (P : PresheafWithTransfers.{v} k) : PresheafWithTransfers.{v} k :=
  withParameter P (SmoothSite.additiveGroupObject (Spec (.of k)))

/-- Coefficients on the genuine Laurent cylinder. -/
abbrev torusSections (P : PresheafWithTransfers.{v} k) : PresheafWithTransfers.{v} k :=
  withParameter P (SmoothSite.multiplicativeGroupObject (Spec (.of k)))

/-- Restriction along the literal Laurent open inclusion. -/
def contractionRestriction (P : PresheafWithTransfers.{v} k) :
    affineLineSections P ⟶ torusSections P :=
  parameterPullback P (SmoothSite.multiplicativeGroupOpen (Spec (.of k)))

@[simp] theorem contractionRestriction_app (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    (contractionRestriction P).hom.app (op X) =
      transfer P ((Cor.graphFunctor k).map
        (SmoothSite.Contraction.openInclusion.app X.toSmoothSite)) := rfl

/-- The actual contraction, with additive transfers induced by exterior signed cycles. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Presheaf/Contraction.lean:66-77"
  "adaptation" "Native additive-functor cokernel of the actual positive Laurent restriction"]
def contraction (P : PresheafWithTransfers.{v} k) : PresheafWithTransfers.{v} k :=
  cokernel (contractionRestriction P)

/-- The canonical quotient from Laurent-cylinder sections. -/
def toContraction (P : PresheafWithTransfers.{v} k) : torusSections P ⟶ contraction P :=
  cokernel.π (contractionRestriction P)

@[reassoc (attr := simp)] theorem contractionRestriction_toContraction
    (P : PresheafWithTransfers.{v} k) :
    contractionRestriction P ≫ toContraction P = 0 :=
  cokernel.condition _

/-- The quotient map commutes with arbitrary genuine signed transfers. -/
@[reassoc] theorem toContraction_naturality (P : PresheafWithTransfers.{v} k)
    {X Y : Cor k} (α : X ⟶ Y) :
    transfer (torusSections P) α ≫ (toContraction P).hom.app (op X) =
      (toContraction P).hom.app (op Y) ≫ transfer (contraction P) α :=
  transfer_naturality (toContraction P) α

/-- On a represented quotient class the transfer is precisely exterior pullback. -/
theorem contraction_transfer_apply (P : PresheafWithTransfers.{v} k)
    {X Y : Cor k} (α : X ⟶ Y) (s : sections (torusSections P) Y) :
    transfer (contraction P) α ((toContraction P).hom.app (op Y) s) =
      (toContraction P).hom.app (op X)
        (transfer P (Stacks.Chow.nativeExterior X.toSmoothSite Y.toSmoothSite
          (SmoothSite.multiplicativeGroupObject (Spec (.of k))) α) s) :=
  (NatTrans.naturality_apply (toContraction P).hom α.op s).symm

/-- Graph restrictions use exactly the actual relative product of the scheme map. -/
theorem contraction_graph_apply (P : PresheafWithTransfers.{v} k)
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y)
    (s : sections (torusSections P) (Cor.mk Y)) :
    transfer (contraction P) ((Cor.graphFunctor k).map f)
        ((toContraction P).hom.app (op (Cor.mk Y)) s) =
      (toContraction P).hom.app (op (Cor.mk X))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.productMap f
            (𝟙 (SmoothSite.multiplicativeGroupObject (Spec (.of k)))))) s) := by
  have h := contraction_transfer_apply P (X := Cor.mk X) (Y := Cor.mk Y)
    ((Cor.graphFunctor k).map f) s
  change _ = (toContraction P).hom.app (op (Cor.mk X))
      (transfer P ((Cor.parameterProduct _).map ((Cor.graphFunctor k).map f)) s) at h
  rw [Cor.parameterProduct_graph] at h
  exact h

/-- Every contraction section has a genuine Laurent-cylinder representative. -/
theorem toContraction_surjective (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    Function.Surjective ((toContraction P).hom.app (op X)) :=
  cokernel_π_app_surjective (contractionRestriction P) X

/-- Objectwise contraction is the ordinary quotient by the actual open-restriction image. -/
def contractionSectionsIsoQuotient (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    sections (contraction P) X ≅ AddCommGrpCat.of
      (sections (torusSections P) X ⧸
        ((contractionRestriction P).hom.app (op X)).hom.range) :=
  cokernelSectionsIsoQuotient (contractionRestriction P) X

/-- The section comparison retains the actual quotient projection. -/
@[reassoc (attr := simp)]
theorem toContraction_sectionsIsoQuotient_hom (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    (toContraction P).hom.app (op X) ≫ (contractionSectionsIsoQuotient P X).hom =
      AddCommGrpCat.ofHom
        (QuotientAddGroup.mk' ((contractionRestriction P).hom.app (op X)).hom.range) :=
  cokernel_π_sectionsIsoQuotient_hom (contractionRestriction P) X

/-- Descend a transfer-natural map killing the actual affine-line restriction. -/
def contractionDesc (P : PresheafWithTransfers.{v} k)
    {Q : PresheafWithTransfers.{v} k} (η : torusSections P ⟶ Q)
    (hη : contractionRestriction P ≫ η = 0) : contraction P ⟶ Q :=
  cokernel.desc _ η hη

@[reassoc (attr := simp)] theorem toContraction_desc (P : PresheafWithTransfers.{v} k)
    {Q : PresheafWithTransfers.{v} k} (η : torusSections P ⟶ Q)
    (hη : contractionRestriction P ≫ η = 0) :
    toContraction P ≫ contractionDesc P η hη = η :=
  cokernel.π_desc _ _ _

/-- Coefficient natural transformations induce genuine contraction morphisms. -/
def contractionMap {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q) :
    contraction P ⟶ contraction Q :=
  contractionDesc P
    (withParameterMap η (SmoothSite.multiplicativeGroupObject (Spec (.of k))) ≫
      toContraction Q) (by
    rw [← Category.assoc, contractionRestriction, parameterPullback_coefficient_naturality,
      Category.assoc]
    change withParameterMap η (SmoothSite.additiveGroupObject (Spec (.of k))) ≫
      (contractionRestriction Q ≫ toContraction Q) = 0
    rw [contractionRestriction_toContraction, comp_zero])

@[reassoc (attr := simp)] theorem toContraction_map
    {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q) :
    toContraction P ≫ contractionMap η =
      withParameterMap η (SmoothSite.multiplicativeGroupObject (Spec (.of k))) ≫ toContraction Q :=
  toContraction_desc P _ _

/-- The actual transfer restriction becomes the already chosen ordinary open restriction. -/
@[reassoc]
theorem contractionRestriction_underlying (P : PresheafWithTransfers.{v} k) :
    (toPresheaf k).map (contractionRestriction P) ≫
        (withParameterUnderlyingIso P
          (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom =
      (withParameterUnderlyingIso P
          (SmoothSite.additiveGroupObject (Spec (.of k)))).hom ≫
        SmoothSite.Contraction.restriction ((toPresheaf k).obj P) := by
  apply NatTrans.ext
  funext X
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp only [Category.comp_id, Category.id_comp]
  rfl

/-- The signed-transfer contraction extends the exact ordinary Laurent quotient.
The comparison is induced by graph restriction and identities on the two cylinders. -/
def contractionUnderlyingIso (P : PresheafWithTransfers.{v} k) :
    (toPresheaf k).obj (contraction P) ≅
      SmoothSite.Contraction.presheaf ((toPresheaf k).obj P) :=
  PreservesCokernel.iso (toPresheaf k) (contractionRestriction P) ≪≫
    cokernel.mapIso _ (SmoothSite.Contraction.restriction ((toPresheaf k).obj P))
      (withParameterUnderlyingIso P (SmoothSite.additiveGroupObject (Spec (.of k))))
      (withParameterUnderlyingIso P (SmoothSite.multiplicativeGroupObject (Spec (.of k))))
      (contractionRestriction_underlying P)

/-- The comparison identifies the actual projections, not only the quotient objects. -/
@[reassoc (attr := simp)]
theorem toContraction_underlyingIso_hom (P : PresheafWithTransfers.{v} k) :
    (toPresheaf k).map (toContraction P) ≫ (contractionUnderlyingIso P).hom =
      (withParameterUnderlyingIso P
          (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom ≫
        SmoothSite.Contraction.quotient ((toPresheaf k).obj P) := by
  simp only [contractionUnderlyingIso, Iso.trans_hom, ← Category.assoc, toContraction,
    PreservesCokernel.π_iso_hom, cokernel.mapIso_hom, cokernel.π_desc,
    SmoothSite.Contraction.quotient]

/-- A represented class is unchanged by the graph-restriction comparison. -/
theorem contractionUnderlyingIso_quotient_apply (P : PresheafWithTransfers.{v} k)
    (X : SmoothSite (Spec (.of k))) (s : sections (torusSections P) (Cor.mk X)) :
    (contractionUnderlyingIso P).hom.app (op X)
        ((toContraction P).hom.app (op (Cor.mk X)) s) =
      (SmoothSite.Contraction.quotient ((toPresheaf k).obj P)).app (op X) s := by
  have h := congrArg (fun η => η.app (op X)) (toContraction_underlyingIso_hom P)
  exact ConcreteCategory.congr_hom h s

end AlgebraicGeometry.PresheafWithTransfers
