/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.CofibrationClosedSubcategory
public import Colib.CategoryTheory.Waldhausen.Complexes
public import Colib.CategoryTheory.Waldhausen.Cylinder.JointSource
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.SubcategoryZero
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.AmbientRelative
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.Pushout
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Embeddings

/-! # Joint cylinders for the literal ambient-monomorphism full subcategory

The structure throughout is `CofibrationClosedSubcategory.waldhausenStructure
(complexes A) P H`. In particular, relative cofibrations mean ambient monomorphisms,
not inflations in an auxiliary exact category. Extension closure is used only to
construct the actual biproduct objects reused from the pure complex layer.
No shift-closure hypothesis is needed.

Proof pattern adapted from `Quillen/Waldhausen/Cylinder/JointFunctor.lean` and
`JointExact.lean` at c561118b7795eb9780be9ed391c3251d6a4d0afd, with the essential
relative-cofibration argument replaced by ambient monicity. Source-only draft.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
open CategoryTheory.ExactCategory CochainComplex.SplitFactorization
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.Waldhausen.CofibrationClosedCylinder
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (H : CofibrationClosedSubcategory.Closed (complexes A) P)
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))

/-- The unchanged joint endpoint inclusion is an ambient monomorphism. -/
theorem jointInclusion_cof (f : Arrow P.FullSubcategory) :
    (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H).cof
      (subcategoryJointInclusion P hcone f) := by
  change Mono (jointInclusion f.hom.hom)
  exact (jointSequence_shortExact f.hom.hom).mono_f

/-- The literal joint inclusion as an object of the original cofibration-arrow category. -/
def jointFunctor : Arrow P.FullSubcategory ⥤ ExtensionCategory.Obj
  (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H) where
  obj f := ⟨Arrow.mk (subcategoryJointInclusion P hcone f), jointInclusion_cof P H hcone f⟩
  map α := (ExtensionCategory.objects (CofibrationClosedSubcategory.waldhausenStructure (complexes
    A) P H)).homMk
    (Arrow.homMk (P.homMk (biprod.map α.left.hom α.right.hom))
      ((subcategoryMiddleFunctor P hcone).map α)
      (ObjectProperty.hom_ext _ (jointInclusion_naturality (P.ι.mapArrow.map α)).symm))
  map_id f := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · apply ObjectProperty.hom_ext
      apply biprod.hom_ext <;> simp
    · exact (subcategoryMiddleFunctor P hcone).map_id f
  map_comp α β := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · apply ObjectProperty.hom_ext
      apply biprod.hom_ext <;> simp
    · exact (subcategoryMiddleFunctor P hcone).map_comp α β

@[simp] theorem jointFunctor_obj_hom (f : Arrow P.FullSubcategory) :
    ((jointFunctor P H hcone).obj f).obj.hom.hom = jointInclusion f.hom.hom := rfl

@[simp] theorem jointFunctor_comp_source :
    jointFunctor P H hcone ⋙ ExtensionCategory.source
      (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H) =
      subcategoryJointSourceFunctor P := rfl

@[simp] theorem jointFunctor_comp_middle :
    jointFunctor P H hcone ⋙ ExtensionCategory.middle
      (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H) =
      subcategoryMiddleFunctor P hcone := rfl

/-- Actual pointwise pushouts are preserved by the unchanged middle functor. -/
theorem middle_map_isPushout
    {K L M N : Arrow P.FullSubcategory} {f : K ⟶ L} {g : K ⟶ M}
    {i : L ⟶ N} {j : M ⟶ N}
    (hf : ArrowCategory.cof (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H) f)
    (hL : IsPushout f.left g.left i.left j.left)
    (hR : IsPushout f.right g.right i.right j.right) :
    IsPushout ((subcategoryMiddleFunctor P hcone).map f)
      ((subcategoryMiddleFunctor P hcone).map g)
      ((subcategoryMiddleFunctor P hcone).map i)
      ((subcategoryMiddleFunctor P hcone).map j) := by
  apply IsPushout.of_map_of_faithful P.ι
  exact middleFunctor_map_isPushout
    (CofibrationClosedSubcategory.inclusion_map_pushout (complexes A) P H hf.1 hL)
    (CofibrationClosedSubcategory.inclusion_map_pushout (complexes A) P H hf.2 hR)

/-- The relative map for the genuine Reedy cofibration condition is ambient monic.
Only monicity of the source component is needed, in addition to the endpoint-sum cofibration. -/
theorem jointFunctor_map_cof_of_source
    {f g : Arrow P.FullSubcategory} (α : f ⟶ g)
    (hα : (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H).cof α.left)
    (hs : (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H).cof
      (P.homMk (biprod.map α.left.hom α.right.hom) :
        subcategoryJointSource P f ⟶ subcategoryJointSource P g)) :
    ExtensionCategory.cof (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H)
      ((jointFunctor P H hcone).map α) := by
  let W := CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H
  let b : subcategoryJointSource P f ⟶ subcategoryJointSource P g :=
    P.homMk (biprod.map α.left.hom α.right.hom)
  obtain ⟨R, i, j, h⟩ := W.pushout_exists (subcategoryJointInclusion P hcone f) b
    (jointInclusion_cof P H hcone f)
  let k : R ⟶ (subcategoryMiddleFunctor P hcone).obj g :=
    h.desc ((subcategoryMiddleFunctor P hcone).map α)
      (subcategoryJointInclusion P hcone g)
      (ObjectProperty.hom_ext _ (jointInclusion_naturality (P.ι.mapArrow.map α)))
  have hi : i ≫ k = (subcategoryMiddleFunctor P hcone).map α := h.inl_desc _ _ _
  have hj : j ≫ k = subcategoryJointInclusion P hcone g := h.inr_desc _ _ _
  apply ExtensionCategory.cof_of_relative W ((jointFunctor P H hcone).map α) hs h k hi hj
  let γ := P.ι.mapArrow.map α
  let : Mono γ.left := hα
  change Mono k.hom
  exact relative_jointInclusion_mono γ
    (CofibrationClosedSubcategory.inclusion_map_pushout (complexes A) P H
      (jointInclusion_cof P H hcone f) h)
    k.hom (congrArg (fun z ↦ z.hom) hi) (congrArg (fun z ↦ z.hom) hj)

/-- Genuine exactness from pointwise ambient cofibrations to Reedy ambient cofibrations. -/
theorem jointFunctor_exact :
    IsExact (ArrowCategory.waldhausenStructure (CofibrationClosedSubcategory.waldhausenStructure
      (complexes A) P H)).cof
      (ArrowCategory.waldhausenStructure (CofibrationClosedSubcategory.waldhausenStructure
        (complexes A) P H)).weq
      (ExtensionCategory.waldhausenStructure (CofibrationClosedSubcategory.waldhausenStructure
        (complexes A) P H)).cof
      (ExtensionCategory.waldhausenStructure (CofibrationClosedSubcategory.waldhausenStructure
        (complexes A) P H)).weq
      (jointFunctor P H hcone) where
  zero h := ExtensionCategory.isZero_of_components (CofibrationClosedSubcategory.waldhausenStructure
    (complexes A) P H) _
    ((SplitFactorization.subcategoryJointSourceFunctor_isExact P
      (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H)).zero h)
    (subcategoryMiddleFunctor_zero P hcone h)
  cofibration α hα := jointFunctor_map_cof_of_source P H hcone α hα.1
    ((SplitFactorization.subcategoryJointSourceFunctor_isExact P
      (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H)).cofibration α hα)
  weak α hα := by
    refine ⟨(SplitFactorization.subcategoryJointSourceFunctor_isExact P
      (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H)).weak α hα, ?_⟩
    let : QuasiIso (P.ι.mapArrow.map α).right := hα.2
    exact middleFunctor_map_quasiIso (P.ι.mapArrow.map α)
  pushout hf h := by
    obtain ⟨hL, hR⟩ := ArrowCategory.pointwise_of_isPushout
      (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H) hf h
    apply IsPushout.of_map_of_faithful (ExtensionCategory.forget
      (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H))
    exact ExtensionCategory.arrow_isPushout _ _ _ _
      ((SplitFactorization.subcategoryJointSourceFunctor_isExact P
        (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H)).pushout hf h)
      (middle_map_isPushout P H hcone hf hL hR)

/-- The projection is literally the original cylinder projection on every object. -/
def projection : jointFunctor P H hcone ⋙ ExtensionCategory.middle
  (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H) ⟶
    Arrow.rightFunc where
  app f := P.homMk (CochainComplex.SplitFactorization.projection f.hom.hom)
  naturality _ _ α := ObjectProperty.hom_ext _
    (projection_naturality (P.ι.mapArrow.map α))

@[simp] theorem projection_app_hom (f : Arrow P.FullSubcategory) :
    ((projection P H hcone).app f).hom =
      CochainComplex.SplitFactorization.projection f.hom.hom := rfl

end CategoryTheory.Waldhausen.CofibrationClosedCylinder
