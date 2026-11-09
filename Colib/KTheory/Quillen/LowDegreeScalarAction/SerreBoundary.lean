/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Quillen.LowDegreeScalarAction.ExactNaturality
public import Colib.KTheory.Quillen.LowDegreeScalarAction.ScalarUnitZero
public import Colib.Topology.HomotopyFiber.SelfHomotopy
public import Colib.KTheory.Quillen.Localization.Serre.Target

/-!
# Scalar identity operations and the original Serre boundary

An ambient identity natural automorphism restricts to the actual Serre full
subcategory. Ordinary compatibility with a quotient identity automorphism gives
a whole based self-homotopy of the original path-space fiber. The maintained
Serre comparison intertwines it with the original supported-category homotopy.

The complete epsilon cylinder is retained. Its categorical image consists of
original Q-zero objects. Two double-cylinder maps therefore agree on every
simplex: their object values agree, and the actual zero-target hom sets are
subsingletons. Inverse-cylinder naturality realizes these equalities as strict
invariance in both homotopy parameters, including every point of the stored path.

The canonical comparison's proved bijectivity transfers the signed fiber formula
to the original Serre connecting maps. For an actual localization target, full
faithfulness of the canonical target lift constructs the required formal-quotient
automorphism. Ordinary linearity then gives the scalar-unit boundary formula,
without requiring a linear structure on the formal quotient.

The displayed categories use the native Serre theorem's common small universe.
Comparison with other chosen exact models and ordered-symbol/product marking
are separate applications.
-/
/-! Implementation provenance: `Quillen/KTheory/LowDegreeScalarAction/SerreBoundary.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original Serre full subcategory
uses its native abelian exact structure, with unchanged actual maps and whole null tracks. -/
@[expose] public section

noncomputable section
open Topology CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open MonoidalCategory CartesianMonoidalCategory Opposite SSet
open scoped ZeroObject Topology unitInterval Simplicial
universe u w
namespace CategoryTheory.ExactCategory.SerreBoundary

private theorem identityCylinder_obj {A : Type u} [Category.{u} A]
    (α : 𝟭 A ⟶ 𝟭 A) (i : Fin 2) (a : A) :
    (naturalTransformationCylinderFunctor α).obj (i, a) = a := by
  fin_cases i <;> rfl

private theorem thinCylinder_pre {A D : Type u} [Category.{u} A] [Category.{u} D]
    {F G : A ⥤ D} (ε : F ⟶ G)
    (hthin : ∀ z : Fin 2 × A, ∀ Y : D,
      Subsingleton (Y ⟶ (naturalTransformationCylinderFunctor ε).obj z))
    (α : 𝟭 A ⟶ 𝟭 A) :
    (naturalTransformationNerveCylinder α ▷ Δ[1]) ≫ naturalTransformationNerveCylinder ε =
      (fst (nerve A) Δ[1] ▷ Δ[1]) ≫ naturalTransformationNerveCylinder ε := by
  ext n z : 4
  let S := z.2.down.toOrderHom.monotone.functor
  let T := z.1.2.down.toOrderHom.monotone.functor
  let a := z.1.1
  change (S.prod' (T.prod' a ⋙ naturalTransformationCylinderFunctor α)) ⋙
      naturalTransformationCylinderFunctor ε =
    S.prod' a ⋙ naturalTransformationCylinderFunctor ε
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · exact congrArg (fun b => (naturalTransformationCylinderFunctor ε).obj (S.obj i, b))
      (identityCylinder_obj α (T.obj i) (a.obj i))
  · intro i j f
    exact (hthin (S.obj j,
      (naturalTransformationCylinderFunctor α).obj (T.obj j, a.obj j)) _).elim _ _

private theorem thinCylinder_post {A D : Type u} [Category.{u} A] [Category.{u} D]
    {F G : A ⥤ D} (ε : F ⟶ G)
    (hthin : ∀ z : Fin 2 × A, ∀ Y : D,
      Subsingleton (Y ⟶ (naturalTransformationCylinderFunctor ε).obj z))
    (β : 𝟭 D ⟶ 𝟭 D) :
    (naturalTransformationNerveCylinder ε ▷ Δ[1]) ≫ naturalTransformationNerveCylinder β =
      fst (nerve A ⊗ Δ[1]) Δ[1] ≫ naturalTransformationNerveCylinder ε := by
  ext n z : 4
  let S := z.1.2.down.toOrderHom.monotone.functor
  let T := z.2.down.toOrderHom.monotone.functor
  let a := z.1.1
  change (T.prod' (S.prod' a ⋙ naturalTransformationCylinderFunctor ε)) ⋙
      naturalTransformationCylinderFunctor β =
    S.prod' a ⋙ naturalTransformationCylinderFunctor ε
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · exact identityCylinder_obj β (T.obj i)
      ((naturalTransformationCylinderFunctor ε).obj (S.obj i, a.obj i))
  · intro i j f
    have hs : Subsingleton
        (((T.prod' (S.prod' a ⋙ naturalTransformationCylinderFunctor ε)) ⋙
          naturalTransformationCylinderFunctor β).obj i ⟶
        ((T.prod' (S.prod' a ⋙ naturalTransformationCylinderFunctor ε)) ⋙
          naturalTransformationCylinderFunctor β).obj j) := by
      change Subsingleton (_ ⟶ (naturalTransformationCylinderFunctor β).obj
        (T.obj j, (naturalTransformationCylinderFunctor ε).obj (S.obj j, a.obj j)))
      rw [identityCylinder_obj]
      exact hthin (S.obj j, a.obj j) _
    exact hs.elim _ _

private theorem cylinderProjection (X : SSet.{u}) (z : |X|) (t : unitInterval) :
    SSet.toTop.map (fst X Δ[1]) ((realizationCylinderIso X).inv (z, ULift.up t)) = z := by
  have hp := congrArg _root_.Prod.fst (ConcreteCategory.congr_hom
    (realizationCylinderIso X).inv_hom_id (z, ULift.up t))
  exact hp

private theorem realization_doubleCylinder {X Y Z : SSet.{u}}
    (h : X ⊗ Δ[1] ⟶ Y) (k : Y ⊗ Δ[1] ⟶ Z) (z : |X|) (t s : unitInterval) :
    SSet.toTop.map k ((realizationCylinderIso Y).inv
      (SSet.toTop.map h ((realizationCylinderIso X).inv (z, ULift.up t)), ULift.up s)) =
    SSet.toTop.map ((h ▷ Δ[1]) ≫ k)
      ((realizationCylinderIso (X ⊗ Δ[1])).inv
        ((realizationCylinderIso X).inv (z, ULift.up t), ULift.up s)) := by
  have hn := ConcreteCategory.congr_hom (realizationCylinderIso_inv_naturality h)
    ((realizationCylinderIso X).inv (z, ULift.up t), ULift.up s)
  change SSet.toTop.map (h ▷ Δ[1])
      ((realizationCylinderIso (X ⊗ Δ[1])).inv
        ((realizationCylinderIso X).inv (z, ULift.up t), ULift.up s)) =
    (realizationCylinderIso Y).inv
      (SSet.toTop.map h ((realizationCylinderIso X).inv (z, ULift.up t)), ULift.up s) at hn
  rw [← hn, SSet.toTop.map_comp]
  rfl

private theorem thinHomotopy_pre {A D : Type u} [Category.{u} A] [Category.{u} D]
    {F G : A ⥤ D} (ε : F ⟶ G)
    (hthin : ∀ z : Fin 2 × A, ∀ Y : D,
      Subsingleton (Y ⟶ (naturalTransformationCylinderFunctor ε).obj z))
    (α : 𝟭 A ⟶ 𝟭 A) (t s : unitInterval) (z : ClassifyingSpace A) :
    classifyingSpaceNaturalTransformationHomotopy ε
        (s, classifyingSpaceNaturalTransformationHomotopy α (t, z)) =
      classifyingSpaceNaturalTransformationHomotopy ε (s, z) := by
  change |nerve A| at z
  change SSet.toTop.map (naturalTransformationNerveCylinder ε)
    ((realizationCylinderIso (nerve A)).inv
      (SSet.toTop.map (naturalTransformationNerveCylinder α)
        ((realizationCylinderIso (nerve A)).inv (z, ULift.up t)), ULift.up s)) = _
  rw [realization_doubleCylinder, thinCylinder_pre ε hthin α,
    ← realization_doubleCylinder, cylinderProjection]
  rfl

private theorem thinHomotopy_post {A D : Type u} [Category.{u} A] [Category.{u} D]
    {F G : A ⥤ D} (ε : F ⟶ G)
    (hthin : ∀ z : Fin 2 × A, ∀ Y : D,
      Subsingleton (Y ⟶ (naturalTransformationCylinderFunctor ε).obj z))
    (β : 𝟭 D ⟶ 𝟭 D) (t s : unitInterval) (z : ClassifyingSpace A) :
    classifyingSpaceNaturalTransformationHomotopy β
        (t, classifyingSpaceNaturalTransformationHomotopy ε (s, z)) =
      classifyingSpaceNaturalTransformationHomotopy ε (s, z) := by
  change |nerve A| at z
  change SSet.toTop.map (naturalTransformationNerveCylinder β)
    ((realizationCylinderIso (nerve D)).inv
      (SSet.toTop.map (naturalTransformationNerveCylinder ε)
        ((realizationCylinderIso (nerve A)).inv (z, ULift.up s)), ULift.up t)) = _
  rw [realization_doubleCylinder, thinCylinder_post ε hthin β,
    SSet.toTop.map_comp, TopCat.comp_app, cylinderProjection]
  rfl

private theorem castIdentityHomotopy {A : Type u} [Category.{u} A]
    {F : A ⥤ A} (h : F = 𝟭 A) (α : F ⟶ F)
    (t : unitInterval) (z : ClassifyingSpace A) :
    classifyingSpaceNaturalTransformationHomotopy
        (eqToHom h.symm ≫ α ≫ eqToHom h) (t, z) =
      classifyingSpaceNaturalTransformationHomotopy α (t, z) := by
  subst F
  simp

private def identityQTransformation {A : Type u} [Category.{u} A]
    [Preadditive A] [HasFiniteBiproducts A] (E : ExactStructure A)
    (u : 𝟭 A ≅ 𝟭 A) : 𝟭 E.QCategory ⟶ 𝟭 E.QCategory :=
  eqToHom (IdentityAutomorphism.normalizedIdentityQ E).symm ≫
    (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) u).hom ≫
      eqToHom (IdentityAutomorphism.normalizedIdentityQ E)

private theorem identityQTransformation_homotopy {A : Type u} [Category.{u} A]
    [Preadditive A] [HasFiniteBiproducts A] (E : ExactStructure A)
    (u : 𝟭 A ≅ 𝟭 A) (t : unitInterval) (z : E.KSpace) :
    classifyingSpaceNaturalTransformationHomotopy (identityQTransformation E u) (t, z) =
      IdentityAutomorphism.homotopy E u (t, z) :=
  castIdentityHomotopy (IdentityAutomorphism.normalizedIdentityQ E) _ t z

open SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] CategoryTheory.ExactCategory.SerreLocalization.canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- Restrict the original identity natural automorphism to the actual Serre full subcategory. -/
def restrictedNatAut (u : 𝟭 C ≅ 𝟭 C) :
    𝟭 P.FullSubcategory ≅ 𝟭 P.FullSubcategory :=
  NatIso.ofComponents (fun A => P.isoMk (u.app A.obj)) (by
    intro A B f
    apply ObjectProperty.hom_ext
    exact u.hom.naturality f.hom)

private theorem normalizedQ_obj_nonbase
    {A B : Type u} [Category.{u} A] [Category.{u} B]
    [Preadditive A] [Preadditive B] [HasFiniteBiproducts A] [HasFiniteBiproducts B]
    {EA : ExactStructure A} {EB : ExactStructure B} (F : ExactFunctor EA EB)
    (X : EA.QCategory) (h : X ≠ EA.qZero) :
    F.normalizedQ.obj X = F.mapQ.obj X := by
  change rebaseObj F.mapQ EA.qZero EB.qZero X = F.mapQ.obj X
  simp only [rebaseObj, ite_eq_right h]

private theorem normalizedComposite_isZero
    (X : (abelianExactStructure P.FullSubcategory).QCategory) :
    IsZero ((((ObjectProperty.exactInclusion P).normalizedQ ⋙
      (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ).obj X).obj.of) := by
  classical
  let J := ObjectProperty.exactInclusion P
  let QF := ExactFunctor.serreLocalization P P.isoModSerre.Q
  by_cases hX : X = (abelianExactStructure P.FullSubcategory).qZero
  · subst X
    rw [normalizedComposite_obj_zero]
    exact isZero_zero _
  · change IsZero ((QF.normalizedQ.obj (J.normalizedQ.obj X)).obj.of)
    rw [normalizedQ_obj_nonbase J X hX]
    by_cases hI : J.mapQ.obj X = (abelianExactStructure C).qZero
    · rw [hI]
      change IsZero ((rebaseObj QF.mapQ (abelianExactStructure C).qZero
        (abelianExactStructure P.isoModSerre.Localization).qZero
        (abelianExactStructure C).qZero).obj.of)
      simp only [rebaseObj]
      exact isZero_zero _
    · rw [normalizedQ_obj_nonbase QF (J.mapQ.obj X) hI]
      exact (quotient_isZero_obj_iff P X.obj.of.obj).2 X.obj.of.property

private theorem epsilon_thin (z : Fin 2 × (abelianExactStructure P.FullSubcategory).QCategory)
    (Y : (abelianExactStructure P.isoModSerre.Localization).QCategory) :
    Subsingleton (Y ⟶
      (naturalTransformationCylinderFunctor (normalizedQuotientInclusionZeroIso P).hom).obj z) := by
  rcases z with ⟨i, X⟩
  fin_cases i
  · apply (abelianExactStructure P.isoModSerre.Localization).qHom_subsingleton_of_isZero
    exact normalizedComposite_isZero P X
  · apply (abelianExactStructure P.isoModSerre.Localization).qHom_subsingleton_of_isZero
    exact isZero_zero _

private theorem epsilon_homotopy_pre (u : 𝟭 C ≅ 𝟭 C)
    (t s : unitInterval) (z : (abelianExactStructure P.FullSubcategory).KSpace) :
    normalizedQuotientInclusionHomotopy P
        (s, IdentityAutomorphism.homotopy (abelianExactStructure P.FullSubcategory)
          (restrictedNatAut P u) (t, z)) =
      normalizedQuotientInclusionHomotopy P (s, z) := by
  have h := thinHomotopy_pre (normalizedQuotientInclusionZeroIso P).hom (epsilon_thin P)
    (identityQTransformation (abelianExactStructure P.FullSubcategory) (restrictedNatAut P u))
    t s z
  rw [identityQTransformation_homotopy] at h
  exact h

private theorem epsilon_homotopy_post
    (v : 𝟭 P.isoModSerre.Localization ≅ 𝟭 P.isoModSerre.Localization)
    (t s : unitInterval) (z : (abelianExactStructure P.FullSubcategory).KSpace) :
    IdentityAutomorphism.homotopy (abelianExactStructure P.isoModSerre.Localization) v
        (t, normalizedQuotientInclusionHomotopy P (s, z)) =
      normalizedQuotientInclusionHomotopy P (s, z) := by
  have h := thinHomotopy_post (normalizedQuotientInclusionZeroIso P).hom (epsilon_thin P)
    (identityQTransformation (abelianExactStructure P.isoModSerre.Localization) v) t s z
  rw [identityQTransformation_homotopy] at h
  exact h

variable (u : 𝟭 C ≅ 𝟭 C)
  (v : 𝟭 P.isoModSerre.Localization ≅ 𝟭 P.isoModSerre.Localization)
  (h : ∀ A, P.isoModSerre.Q.map (u.hom.app A) =
    v.hom.app (P.isoModSerre.Q.obj A))

/-- The actual identity homotopy on the original normalized Serre fiber,
from the ordinary ambient/quotient compatibility equation. -/
def fiberIdentityHomotopy :
    (ContinuousMap.id (NormalizedLocalizationFiber P)).Homotopy
      (ContinuousMap.id (NormalizedLocalizationFiber P)) :=
  HomotopyFiber.identityHomotopy
    (classifyingSpaceMap (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ).hom
    (abelianExactStructure P.isoModSerre.Localization).kBasepoint
    (IdentityAutomorphism.homotopy (abelianExactStructure C) u).toHomotopy
    (IdentityAutomorphism.homotopy (abelianExactStructure P.isoModSerre.Localization) v).toHomotopy
    (IdentityAutomorphism.homotopy_fixed (abelianExactStructure P.isoModSerre.Localization) v)
    (fun t z => (IdentityAutomorphism.identityHomotopy_natural.{u, u}
      (ExactFunctor.serreLocalization P P.isoModSerre.Q) u v h t z).symm)

/-- The whole original fiber homotopy fixes its original constant-path basepoint. -/
theorem fiberIdentityHomotopy_based (t : unitInterval) :
    fiberIdentityHomotopy P u v h (t, normalizedFiberBasepoint P) =
      normalizedFiberBasepoint P :=
  HomotopyFiber.identityHomotopy_based
    (classifyingSpaceMap (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ).hom
    (abelianExactStructure C).kBasepoint
    (abelianExactStructure P.isoModSerre.Localization).kBasepoint
    (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ_map_point
    (IdentityAutomorphism.homotopy (abelianExactStructure C) u).toHomotopy
    (IdentityAutomorphism.homotopy (abelianExactStructure P.isoModSerre.Localization) v).toHomotopy
    (IdentityAutomorphism.homotopy_fixed (abelianExactStructure C) u)
    (IdentityAutomorphism.homotopy_fixed (abelianExactStructure P.isoModSerre.Localization) v)
    (fun t z => (IdentityAutomorphism.identityHomotopy_natural.{u, u}
      (ExactFunctor.serreLocalization P P.isoModSerre.Q) u v h t z).symm) t

/-- The original Serre comparison intertwines the whole supported-category
and fiber identity homotopies, including every point of the stored epsilon path. -/
theorem fiberComparison_identityHomotopy (t : unitInterval)
    (z : (abelianExactStructure P.FullSubcategory).KSpace) :
    basedLocalizationFiberComparison P
        (IdentityAutomorphism.homotopy (abelianExactStructure P.FullSubcategory)
          (restrictedNatAut P u) (t, z)) =
      fiberIdentityHomotopy P u v h (t, basedLocalizationFiberComparison P z) := by
  apply Subtype.ext
  apply Prod.ext
  · exact IdentityAutomorphism.identityHomotopy_natural.{u, u} (ObjectProperty.exactInclusion P)
      (restrictedNatAut P u) u (fun _ => rfl) t z
  · apply ContinuousMap.ext
    intro s
    exact (epsilon_homotopy_pre P u t s z).trans (epsilon_homotopy_post P v t s z).symm

/-- The original comparison preserves the degree-(0,1) operation by its whole
based homotopy square, without an assumed group-level compatibility law. -/
theorem fiberComparison_kZeroAction
    (a : (abelianExactStructure P.FullSubcategory).K 0) :
    localizationFiberComparisonHom P 1
        (IdentityAutomorphism.kZeroAction (abelianExactStructure P.FullSubcategory)
          (restrictedNatAut P u) a) =
      IdentityTrack.operation (fiberIdentityHomotopy P u v h)
        (fiberIdentityHomotopy_based P u v h) 0 (localizationFiberComparisonHom P 0 a) :=
  IdentityTrack.operation_natural
    (IdentityAutomorphism.homotopy (abelianExactStructure P.FullSubcategory)
      (restrictedNatAut P u)).toHomotopy
    (IdentityAutomorphism.homotopy_fixed (abelianExactStructure P.FullSubcategory)
      (restrictedNatAut P u))
    (fiberIdentityHomotopy P u v h) (fiberIdentityHomotopy_based P u v h)
    (basedLocalizationFiberComparison P) (basedLocalizationFiberComparison_basepoint P)
    (fiberComparison_identityHomotopy P u v h) 0 a

include h in
/-- The original Serre boundary anti-commutes with the actual identity-automorphism
operations, with the sign fixed by the original loop-shift coordinates. -/
theorem connectingHom_action
    (a : (abelianExactStructure P.isoModSerre.Localization).K 1) :
    connectingHom P 1
        (IdentityAutomorphism.kOneAction (abelianExactStructure P.isoModSerre.Localization) v a) =
      (IdentityAutomorphism.kZeroAction (abelianExactStructure P.FullSubcategory)
        (restrictedNatAut P u) (connectingHom P 0 a))⁻¹ := by
  apply (localizationFiberComparisonHom_bijective P 1).injective
  rw [map_inv, fiberComparison_kZeroAction P u v h]
  have h₀ := DFunLike.congr_fun (comparison_comp_connectingHom P 0) a
  have h₁ := DFunLike.congr_fun (comparison_comp_connectingHom P 1)
    (IdentityAutomorphism.kOneAction (abelianExactStructure P.isoModSerre.Localization) v a)
  change localizationFiberComparisonHom P 0 (connectingHom P 0 a) =
    fiberConnectingHom P 0 a at h₀
  change localizationFiberComparisonHom P 1 (connectingHom P 1
      (IdentityAutomorphism.kOneAction (abelianExactStructure P.isoModSerre.Localization) v a)) =
    fiberConnectingHom P 1
      (IdentityAutomorphism.kOneAction (abelianExactStructure P.isoModSerre.Localization) v a) at h₁
  rw [h₀, h₁]
  exact HomotopyFiber.connectingHom_operation
    (classifyingSpaceMap (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ).hom
    (abelianExactStructure C).kBasepoint
    (abelianExactStructure P.isoModSerre.Localization).kBasepoint
    (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ_map_point
    (IdentityAutomorphism.homotopy (abelianExactStructure C) u).toHomotopy
    (IdentityAutomorphism.homotopy (abelianExactStructure P.isoModSerre.Localization) v).toHomotopy
    (IdentityAutomorphism.homotopy_fixed (abelianExactStructure C) u)
    (IdentityAutomorphism.homotopy_fixed (abelianExactStructure P.isoModSerre.Localization) v)
    (fun t z => (IdentityAutomorphism.identityHomotopy_natural.{u, u}
      (ExactFunctor.serreLocalization P P.isoModSerre.Q) u v h t z).symm) a

private def pullbackNatAut {A D : Type u} [Category.{u} A] [Category.{u} D]
    (F : A ⥤ D) [F.Full] [F.Faithful] (v : 𝟭 D ≅ 𝟭 D) : 𝟭 A ≅ 𝟭 A :=
  NatIso.ofComponents (fun A => F.preimageIso (v.app (F.obj A))) (by
    intro A B f
    apply F.map_injective
    simp only [Functor.id_map, Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
    exact v.hom.naturality (F.map f))

private theorem pullbackNatAut_map {A D : Type u} [Category.{u} A] [Category.{u} D]
    (F : A ⥤ D) [F.Full] [F.Faithful] (v : 𝟭 D ≅ 𝟭 D) (A : A) :
    F.map ((pullbackNatAut F v).hom.app A) = v.hom.app (F.obj A) :=
  F.map_preimage _

section ActualTarget
variable {D : Type u} [Category.{u} D] [Abelian D]
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]
  (vD : 𝟭 D ≅ 𝟭 D)
  (hL : ∀ A, L.map (u.hom.app A) = vD.hom.app (L.obj A))

include hL in
/-- The original boundary for an actual localization target has the same sign.
Its formal-quotient automorphism is constructed by full faithfulness of the
canonical target lift, rather than supplied as a further compatibility law. -/
theorem actualConnectingHom_action (a : (abelianExactStructure D).K 1) :
    actualConnectingHom P L 1
        (IdentityAutomorphism.kOneAction (abelianExactStructure D) vD a) =
      (IdentityAutomorphism.kZeroAction (abelianExactStructure P.FullSubcategory)
        (restrictedNatAut P u) (actualConnectingHom P L 0 a))⁻¹ := by
  let T := targetLift P L
  let w := pullbackNatAut T vD
  have hw (A : C) : P.isoModSerre.Q.map (u.hom.app A) =
      w.hom.app (P.isoModSerre.Q.obj A) := by
    apply T.map_injective
    rw [pullbackNatAut_map]
    change (P.isoModSerre.Q ⋙ targetLift P L).map (u.hom.app A) =
      vD.hom.app ((P.isoModSerre.Q ⋙ targetLift P L).obj A)
    rw [targetLift_fac]
    exact hL A
  obtain ⟨b, rfl⟩ := (targetKEquiv P L 1).surjective a
  have hn := IdentityAutomorphism.kOneAction_natural.{u, u} (targetLiftExactFunctor P L)
    w vD (pullbackNatAut_map T vD) b
  change (targetLiftExactFunctor P L).KMap 2
      (IdentityAutomorphism.kOneAction (abelianExactStructure P.isoModSerre.Localization) w b) =
    IdentityAutomorphism.kOneAction (abelianExactStructure D) vD
      ((targetLiftExactFunctor P L).KMap 1 b) at hn
  change actualConnectingHom P L 1
      (IdentityAutomorphism.kOneAction (abelianExactStructure D) vD
        ((targetLiftExactFunctor P L).KMap 1 b)) =
    (IdentityAutomorphism.kZeroAction (abelianExactStructure P.FullSubcategory)
      (restrictedNatAut P u)
      (actualConnectingHom P L 0 ((targetLiftExactFunctor P L).KMap 1 b)))⁻¹
  rw [← hn]
  have hδ₁ := DFunLike.congr_fun (actualConnectingHom_comp_targetLiftKMap P L 1)
    (IdentityAutomorphism.kOneAction (abelianExactStructure P.isoModSerre.Localization) w b)
  have hδ₀ := DFunLike.congr_fun (actualConnectingHom_comp_targetLiftKMap P L 0) b
  change actualConnectingHom P L 1 ((targetLiftExactFunctor P L).KMap 2
      (IdentityAutomorphism.kOneAction (abelianExactStructure P.isoModSerre.Localization) w b)) =
    connectingHom P 1
      (IdentityAutomorphism.kOneAction
        (abelianExactStructure P.isoModSerre.Localization) w b) at hδ₁
  change actualConnectingHom P L 0 ((targetLiftExactFunctor P L).KMap 1 b) =
    connectingHom P 0 b at hδ₀
  rw [hδ₁, hδ₀]
  exact connectingHom_action P u w hw b
end ActualTarget

section Scalar
open CategoryTheory.Linear
variable (R : Type w) [Ring R] [Linear R C]

omit [P.IsSerreClass] in
/-- Restricting the original scalar automorphism retains the same scalar on
the actual full-subcategory hom modules. -/
theorem restrictedNatAut_scalar (r : Rˣ) :
    restrictedNatAut P (scalarNatAut R C r).asIso = (scalarNatAut R P.FullSubcategory r).asIso := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply ObjectProperty.hom_ext
  rfl

variable {D : Type u} [Category.{u} D] [Abelian D] [Linear R D]
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive] [L.Linear R]

/-- Ordinary linearity gives the signed scalar-unit formula for the original
actual-target Serre boundary. No linear structure on the formal quotient is required. -/
theorem actualConnectingHom_scalar (r : Rˣ) (a : (abelianExactStructure D).K 1) :
    actualConnectingHom P L 1 (ScalarUnit.kOneAction.{w, u, u} R (abelianExactStructure D) r a) =
      (ScalarUnit.kZeroAction.{w, u, u} R (abelianExactStructure P.FullSubcategory) r
        (actualConnectingHom P L 0 a))⁻¹ := by
  have h := actualConnectingHom_action P (scalarNatAut R C r).asIso L (scalarNatAut R D r).asIso
    (scalarNatAut_map R L r) a
  rw [restrictedNatAut_scalar P R r] at h
  exact h
end Scalar

end CategoryTheory.ExactCategory.SerreBoundary

attribute [colib_ref "quillen"
  "Quillen/KTheory/LowDegreeScalarAction/SerreBoundary.lean:189-455"
  "adaptation" "Original maps, whole tracks, native model comparisons and signs"]
  CategoryTheory.ExactCategory.SerreBoundary.restrictedNatAut
  CategoryTheory.ExactCategory.SerreBoundary.fiberIdentityHomotopy
  CategoryTheory.ExactCategory.SerreBoundary.fiberIdentityHomotopy_based
  CategoryTheory.ExactCategory.SerreBoundary.fiberComparison_identityHomotopy
  CategoryTheory.ExactCategory.SerreBoundary.fiberComparison_kZeroAction
  CategoryTheory.ExactCategory.SerreBoundary.connectingHom_action
  CategoryTheory.ExactCategory.SerreBoundary.actualConnectingHom_action
  CategoryTheory.ExactCategory.SerreBoundary.restrictedNatAut_scalar
  CategoryTheory.ExactCategory.SerreBoundary.actualConnectingHom_scalar

attribute [colib_tag "COL-0377"]
  CategoryTheory.ExactCategory.SerreBoundary.connectingHom_action
  CategoryTheory.ExactCategory.SerreBoundary.actualConnectingHom_action
  CategoryTheory.ExactCategory.SerreBoundary.actualConnectingHom_scalar
