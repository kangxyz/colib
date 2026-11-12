/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Sheafification
public import Colib.CategoryTheory.Preadditive.AdditiveFunctorAbelian

/-!
# The image of the transfer Nisnevich sheafification unit

The image of the actual unit is Nisnevich separated and locally generates its
target. Homotopy invariance descends to the image along the pointwise
epimorphism, with the original zero-section restriction as inverse.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Presheaf/Sheafification/Image.lean`, blob
`42e31faa393939ff26b8ab80a3e5ec2324b71e52`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w'

namespace AlgebraicGeometry.A1
open _root_.AlgebraicGeometry.Scheme
open SmoothSite.Contraction

variable (R : CommRingCat.{u}) {A : Type w} [Category.{w'} A]

private theorem isInvariant_of_epi_app
    {P Q : (SmoothSite (Spec R))ᵒᵖ ⥤ A} (η : P ⟶ Q)
    [∀ X, Epi (η.app X)] (hP : IsInvariant R P) : IsInvariant R Q := by
  intro X
  let p := projectionPullback R Q X
  let s := sectionPullback R Q X 0
  have hs : s ≫ p = 𝟙 _ := by
    apply (cancel_epi (η.app (op (affineLineCylinder.obj X)))).mp
    have hn := η.naturality (nativeAffineSection R X 0).op
    have hm := η.naturality ((projection (SmoothSite.additiveGroupObject (Spec R))).app X).op
    change sectionPullback R P X 0 ≫ η.app (op X) =
      η.app (op (affineLineCylinder.obj X)) ≫ s at hn
    change projectionPullback R P X ≫ η.app (op (affineLineCylinder.obj X)) =
      η.app (op X) ≫ p at hm
    rw [← Category.assoc, ← hn, Category.assoc, ← hm, ← Category.assoc,
      sectionPullback_projectionPullback R P hP X 0, Category.id_comp, Category.comp_id]
  exact ⟨⟨s, projectionPullback_sectionPullback R Q X 0, hs⟩⟩

end AlgebraicGeometry.A1

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- Homotopy invariance descends through a transfer morphism that is epi on sections. -/
theorem isA1Invariant_of_epi_app
    {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q)
    [∀ X : Cor k, Epi (η.hom.app (op X))] (hP : P.IsA1Invariant) :
    Q.IsA1Invariant := by
  have (X : (SmoothSite (Spec (.of k)))ᵒᵖ) : Epi (((toPresheaf k).map η).app X) :=
    inferInstanceAs (Epi (η.hom.app (op (Cor.mk X.unop))))
  exact A1.isInvariant_of_epi_app (.of k) ((toPresheaf k).map η) hP

variable [HasWeakSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]

/-- The image of the actual transfer-preserving Nisnevich unit. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Presheaf/Sheafification/Image.lean:77-93"
  "adaptation" "Image factorization of the native transfer Nisnevich sheafification unit"]
def nisnevichImage (P : PresheafWithTransfers.{u + 1} k) :
    PresheafWithTransfers.{u + 1} k :=
  image (toNisnevichSheafify k P)

/-- The epimorphism from the original presheaf to the image of its unit. -/
def toNisnevichImage (P : PresheafWithTransfers.{u + 1} k) : P ⟶ nisnevichImage P :=
  factorThruImage (toNisnevichSheafify k P)

/-- The inclusion of the unit image in the actual sheafification. -/
def nisnevichImageι (P : PresheafWithTransfers.{u + 1} k) :
    nisnevichImage P ⟶ ((nisnevichSheafify k).obj P).obj :=
  image.ι (toNisnevichSheafify k P)

@[reassoc (attr := simp)]
theorem toNisnevichImage_ι (P : PresheafWithTransfers.{u + 1} k) :
    toNisnevichImage P ≫ nisnevichImageι P = toNisnevichSheafify k P :=
  image.fac _

instance (P : PresheafWithTransfers.{u + 1} k) : Epi (toNisnevichImage P) :=
  inferInstanceAs (Epi (factorThruImage (toNisnevichSheafify k P)))

instance (P : PresheafWithTransfers.{u + 1} k) : Mono (nisnevichImageι P) :=
  inferInstanceAs (Mono (image.ι (toNisnevichSheafify k P)))

instance (P : PresheafWithTransfers.{u + 1} k) : Epi (toNisnevichImage P).hom :=
  inferInstanceAs (Epi ((forget).map (toNisnevichImage P)))

instance (P : PresheafWithTransfers.{u + 1} k) : Mono (nisnevichImageι P).hom :=
  inferInstanceAs (Mono ((forget).map (nisnevichImageι P)))

instance (P : PresheafWithTransfers.{u + 1} k) (X : Cor k) :
    Epi ((toNisnevichImage P).hom.app (op X)) := inferInstance

instance (P : PresheafWithTransfers.{u + 1} k) (X : Cor k) :
    Mono ((nisnevichImageι P).hom.app (op X)) := inferInstance

instance (P : PresheafWithTransfers.{u + 1} k) :
    Mono ((toPresheaf k).map (nisnevichImageι P)) := by
  have (X : (SmoothSite (Spec (.of k)))ᵒᵖ) :
      Mono (((toPresheaf k).map (nisnevichImageι P)).app X) :=
    inferInstanceAs (Mono ((nisnevichImageι P).hom.app (op (Cor.mk X.unop))))
  exact NatTrans.mono_of_mono_app _

/-- The unit image is homotopy invariant if the original transfer presheaf is. -/
theorem nisnevichImage_isA1Invariant (P : PresheafWithTransfers.{u + 1} k)
    (hP : P.IsA1Invariant) : (nisnevichImage P).IsA1Invariant :=
  isA1Invariant_of_epi_app (toNisnevichImage P) hP

/-- The unit image is separated for the smooth Nisnevich topology. -/
theorem nisnevichImage_isSeparated (P : PresheafWithTransfers.{u + 1} k) :
    Presheaf.IsSeparated (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).obj (nisnevichImage P)) := by
  intro X R hR x y hxy
  let m := (toPresheaf k).map (nisnevichImageι P)
  have hm : Mono (m.app (op X)) :=
    inferInstanceAs (Mono ((nisnevichImageι P).hom.app (op (Cor.mk X))))
  have hF : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).obj ((nisnevichSheafify k).obj P).obj) :=
    ((nisnevichSheafify k).obj P).property
  apply (AddCommGrpCat.mono_iff_injective (m.app (op X))).mp hm
  apply hF.isSeparated X R hR
  intro Y f hf
  rw [← m.naturality_apply, ← m.naturality_apply, hxy Y f hf]

/-- The image inclusion locally generates the underlying ordinary sheafification. -/
instance isLocallySurjective_nisnevichImageι (P : PresheafWithTransfers.{u + 1} k) :
    Presheaf.IsLocallySurjective (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).map (nisnevichImageι P)) := by
  apply Presheaf.isLocallySurjective_of_isLocallySurjective_fac
    (SmoothSite.nisnevichTopology (Spec (.of k)))
    (f₁ := (toPresheaf k).map (toNisnevichImage P))
    (f₃ := (toPresheaf k).map (toNisnevichSheafify k P))
  rw [← Functor.map_comp, toNisnevichImage_ι]

instance isLocallyInjective_nisnevichImageι (P : PresheafWithTransfers.{u + 1} k) :
    Presheaf.IsLocallyInjective (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).map (nisnevichImageι P)) := by
  apply Presheaf.isLocallyInjective_of_injective
  intro X
  exact (AddCommGrpCat.mono_iff_injective _).mp
    (inferInstanceAs (Mono ((nisnevichImageι P).hom.app (op (Cor.mk X.unop)))))

section OrdinaryComparison

variable [HasWeakSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]

/-- The canonical ordinary sheafification comparison induced by the actual image inclusion. -/
def nisnevichImageSheafificationComparison (P : PresheafWithTransfers.{u + 1} k) :
    (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj (nisnevichImage P)) ⟶
    (SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P) :=
  ⟨sheafifyLift _ ((toPresheaf k).map (nisnevichImageι P))
    ((nisnevichSheafify k).obj P).property⟩

variable [(SmoothSite.nisnevichTopology (Spec (.of k))).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(SmoothSite.nisnevichTopology (Spec (.of k))).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]

instance (P : PresheafWithTransfers.{u + 1} k) :
    IsIso (nisnevichImageSheafificationComparison P) := by
  apply (ObjectProperty.isIso_hom_iff _).mp
  exact isIso_sheafifyLift_of_isLocallyBijective
    (SmoothSite.nisnevichTopology (Spec (.of k)))
    ((toPresheaf k).map (nisnevichImageι P)) ((nisnevichSheafify k).obj P).property

/-- Ordinary sheafification of the unit image recovers the underlying transfer sheafification. -/
def nisnevichImageSheafificationIso (P : PresheafWithTransfers.{u + 1} k) :
    (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj (nisnevichImage P)) ≅
    (SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P) :=
  asIso (nisnevichImageSheafificationComparison P)

/-- The comparison carries the ordinary unit to the actual image inclusion. -/
@[reassoc (attr := simp)]
theorem toSheafify_nisnevichImageSheafificationIso
    (P : PresheafWithTransfers.{u + 1} k) :
    toSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).obj (nisnevichImage P)) ≫
      (nisnevichImageSheafificationIso P).hom.hom =
        (toPresheaf k).map (nisnevichImageι P) :=
  toSheafify_sheafifyLift _ _ _

end OrdinaryComparison

end AlgebraicGeometry.PresheafWithTransfers
