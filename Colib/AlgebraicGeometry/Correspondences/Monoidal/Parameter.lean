/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Exterior
public import Colib.AlgebraicGeometry.Chow.IntegralFundamental
public import Colib.AlgebraicGeometry.Chow.FiniteOpenRestriction
public import Colib.AlgebraicGeometry.Correspondences.Exterior.Composition
public import Colib.AlgebraicGeometry.Correspondences.Graph.FlatFiber

/-!
# Comparison with the existing parameter exterior operation

The new two-variable cycle product agrees with `nativeExterior` when its
second input is the identity of a geometrically integral smooth parameter.
The comparison identifies the actual support schemes and closed inclusions.
It therefore transports the existing incidence Tor composition theorem to
this restriction of the new product, with every signed coefficient intact.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

/-- The existing parameter prime is the whole cycle of its actual integral support. -/
theorem nativeExteriorPrime_val_eq_fundamentalCycle :
    letI : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt z)) := hz.1
    letI := Scheme.isNoetherian_of_finiteType_of_isNoetherian
      (exteriorIdentitySource X Y T (integralComponentAt z))
    (nativeExteriorPrime X Y T z hz).val =
      finiteCyclePushforward (exteriorIdentityInclusion X Y T (integralComponentAt z))
        (AlgebraicCycle.fundamentalCycle
          (exteriorIdentitySupport X Y T (integralComponentAt z))) := by
  classical
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt z)) := hz.1
  let := Scheme.isNoetherian_of_finiteType_of_isNoetherian
    (exteriorIdentitySource X Y T (integralComponentAt z))
  let := nativeExteriorSupport_isIntegral X Y T z hz
  let e := exteriorIdentityInclusion X Y T (integralComponentAt z)
  let : IsIntegral e.ker.subscheme := nativeExteriorImage_isIntegral X Y T z hz
  let : IsIso e.toImage := IsClosedImmersion.instIsIsoSchemeToImage e
  rw [finiteCyclePushforward_fundamentalCycle_integral]
  change single (nativeExteriorPoint X Y T z hz) 1 =
    single (e (genericPoint (exteriorIdentitySupport X Y T (integralComponentAt z)))) 1
  apply congrArg (fun p => single p (1 : ℤ))
  have h := congrArg e.imageι (genericPoint_eq_of_isOpenImmersion e.toImage)
  rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι] at h
  exact h.symm

section Diagonal

variable [IsIntegral T.left] (s : genericPoints T.left)

local notation "δ" => correspondenceGraphMap T.hom T.hom (𝟙 T.left) (Category.id_comp _) s.val
local notation "hδ" => isFiniteCorrespondencePoint_graphMap T.hom T.hom
  (𝟙 T.left) (Category.id_comp _) s
local notation "pδ" => exteriorSupportSourceProjection T T (integralComponentAt δ)
local notation "D" => correspondenceExteriorSupport X Y T T
  (integralComponentAt z) (integralComponentAt δ)
local notation "E" => exteriorIdentitySupport X Y T (integralComponentAt z)

/-- Replacing the diagonal graph support by its source identifies the two literal supports. -/
def correspondenceExteriorDiagonalSupportIso : D ≅ E := by
  letI : IsIntegral ((𝟭 Scheme).obj T.left) := inferInstanceAs (IsIntegral T.left)
  letI : IsIso pδ := isIso_integralGraph_sourceProjection T.hom T.hom
    (𝟙 T.left) (Category.id_comp _) s
  let m : D ⟶ E := pullback.map
    (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
    (pδ ≫ T.hom)
    (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom) T.hom
    (𝟙 (integralComponentAt z).subscheme) pδ (𝟙 _) (by simp) (by simp)
  letI : IsIso m := by
    dsimp only [m]
    infer_instance
  exact asIso m

omit [GeometricallyIntegral T.hom] in
/-- The support isomorphism preserves the actual closed inclusion in the product ambient. -/
theorem correspondenceExteriorDiagonalSupportIso_inclusion :
    (correspondenceExteriorDiagonalSupportIso X Y T z s).hom ≫
      exteriorIdentityInclusion X Y T (integralComponentAt z) =
        correspondenceExteriorInclusion X Y T T
          (integralComponentAt z) (integralComponentAt δ) := by
  have hdiag : exteriorSupportTargetProjection T T (integralComponentAt δ) = pδ := by
    have h := integralComponentAt_graphMap_snd T.hom T.hom
      (𝟙 T.left) (Category.id_comp _) s.val
    change exteriorSupportTargetProjection T T (integralComponentAt δ) = pδ ≫ 𝟙 T.left at h
    simpa only [Category.comp_id] using h
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [correspondenceExteriorDiagonalSupportIso, correspondenceExteriorInclusion,
        correspondenceExteriorSource, correspondenceExteriorTarget, pullback.map, Category.assoc]
  · apply pullback.hom_ext
    · simp [correspondenceExteriorDiagonalSupportIso, correspondenceExteriorInclusion,
        correspondenceExteriorSource, correspondenceExteriorTarget, pullback.map, Category.assoc]
    · simpa [correspondenceExteriorDiagonalSupportIso, correspondenceExteriorInclusion,
        correspondenceExteriorSource, correspondenceExteriorTarget, pullback.map,
        Category.assoc] using
        congrArg (fun t => pullback.snd
          (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
          (pδ ≫ T.hom) ≫ t) hdiag.symm

/-- Exterior product with the actual diagonal prime is the existing native parameter prime. -/
theorem correspondenceExteriorPrime_diagonal :
    correspondenceExteriorPrime X Y T T z δ hz hδ = nativeExteriorPrime X Y T z hz := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt z)) := hz.1
  let : IsFinite pδ := hδ.1
  let := correspondenceExteriorSupport_isNoetherian X Y T T z δ hz hδ
  let := Scheme.isNoetherian_of_finiteType_of_isNoetherian
    (exteriorIdentitySource X Y T (integralComponentAt z))
  let e := correspondenceExteriorDiagonalSupportIso X Y T z s
  apply Subtype.ext
  rw [correspondenceExteriorPrime_val, nativeExteriorPrime_val_eq_fundamentalCycle,
    ← finiteCyclePushforward_fundamentalCycle_iso e, finiteCyclePushforward_comp_apply]
  exact finiteCyclePushforward_congr _ _
    (correspondenceExteriorDiagonalSupportIso_inclusion X Y T z s).symm _

end Diagonal

omit z hz in
omit [GeometricallyIntegral T.hom] in
/-- The full identity of an integral parameter is its single actual diagonal component. -/
theorem integralParameter_identity_eq_single [IsIntegral T.left] (s : genericPoints T.left) :
    𝟙 (Cor.mk T) =
      singleFiniteCorrespondence T.hom T.hom
        (correspondenceGraphMap T.hom T.hom (𝟙 T.left) (Category.id_comp _) s.val)
        (isFiniteCorrespondencePoint_graphMap T.hom T.hom
          (𝟙 T.left) (Category.id_comp _) s) 1 := by
  classical
  let hT := Cor.finite_genericPoints k (Cor.mk T)
  have hs : s.val = genericPoint T.left := by
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using s.property
  have hpoints : genericPoints T.left = {s.val} := by
    exact genericPoints_eq_singleton.trans
      (congrArg (fun t : T.left => ({t} : Set T.left)) hs.symm)
  have hfin : hT.toFinset = {s.val} := by
    ext x
    simp only [Set.Finite.mem_toFinset, hpoints, Set.mem_singleton_iff, Finset.mem_singleton]
  apply Subtype.ext
  change (∑ x ∈ hT.toFinset,
    single (correspondenceGraphMap T.hom T.hom (𝟙 T.left) (Category.id_comp _) x) (1 : ℤ)) =
      single (correspondenceGraphMap T.hom T.hom (𝟙 T.left) (Category.id_comp _) s.val) (1 : ℤ)
  rw [hfin, Finset.sum_singleton]

omit z hz in
/-- Equality with the existing parameter operation on every signed correspondence. -/
theorem correspondenceExterior_identity_right (α : finiteCorrespondences X.hom Y.hom) :
    correspondenceExterior X Y T T α (𝟙 (Cor.mk T)) = nativeExterior X Y T α := by
  let : IsIntegral T.left := GeometricallyIntegral.isIntegral_of_subsingleton
    (show T.left ⟶ Spec (.of k) from T.hom)
  let s : genericPoints T.left := ⟨genericPoint T.left, genericPoint_mem_genericPoints T.left⟩
  have h : (correspondenceExterior X Y T T).flip (𝟙 (Cor.mk T)) = nativeExterior X Y T := by
    apply finiteCorrespondences.addHom_ext_one X.hom Y.hom
    intro z hz
    simp only [AddMonoidHom.flip_apply, integralParameter_identity_eq_single T s,
      correspondenceExterior_single, one_mul, one_smul, nativeExterior_single]
    exact correspondenceExteriorPrime_diagonal X Y T z hz s
  exact congrArg (fun F : finiteCorrespondences X.hom Y.hom →+
    finiteCorrespondences (SmoothSite.product X T).hom (SmoothSite.product Y T).hom => F α) h

end Stacks.Chow

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- The two-variable product restricts to the chosen native parameter map. -/
theorem exteriorProduct_identity_right {X Y : Cor k} (α : X ⟶ Y) :
    exteriorProduct α (𝟙 (Cor.mk T)) =
      Stacks.Chow.nativeExterior X.toSmoothSite Y.toSmoothSite T α :=
  Stacks.Chow.correspondenceExterior_identity_right X.toSmoothSite Y.toSmoothSite T α

/-- Composition interchange with the fixed parameter identity, on actual signed cycles. -/
theorem exteriorProduct_comp_identity {X Y Z : Cor k} (α : X ⟶ Y) (β : Y ⟶ Z) :
    exteriorProduct (α ≫ β) (𝟙 (Cor.mk T)) =
      exteriorProduct α (𝟙 (Cor.mk T)) ≫ exteriorProduct β (𝟙 (Cor.mk T)) := by
  simp only [exteriorProduct_identity_right]
  exact Stacks.Chow.nativeExterior_incidenceTorPairing
    X.toSmoothSite Y.toSmoothSite Z.toSmoothSite T α β

end AlgebraicGeometry.Cor
