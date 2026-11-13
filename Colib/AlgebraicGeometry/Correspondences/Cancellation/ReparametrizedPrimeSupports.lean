/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.PrimeSupport
public import Colib.CategoryTheory.Limits.Shapes.Pullback.ParameterGraph
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureRelativeClosure

/-!
# Actual native prime support identifications for reparametrization

The left exterior support uses the free parameter over its original
middle map. The closed integral right graph is its own reduced
component. These identifications retain the literal original
projections used by the common incidence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] (U X T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) U.hom X.hom)
  (hz : IsFiniteCorrespondencePoint U.hom X.hom z)

local notation3 (prettyPrint := false) "Q" => (integralComponentAt z).subscheme
local notation3 (prettyPrint := false) "p" =>
  exteriorSupportTargetProjection U X (integralComponentAt z)
local notation3 (prettyPrint := false) "q" =>
  exteriorSupportSourceProjection U X (integralComponentAt z)
local notation3 (prettyPrint := false) "zT" => nativeExteriorPoint U X T z hz
local notation3 (prettyPrint := false) "f" => (SmoothSite.product U T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product X T).hom

/-- The canonical exterior support over the old middle coordinate. -/
def reparametrizedExteriorSupportIso :
    pullback (p ≫ X.hom) T.hom ≅ (integralComponentAt zT).subscheme :=
  pullback.congrHom (exteriorSupport_projection_base U X (integralComponentAt z)).symm rfl ≪≫
    nativeExteriorSupportIso U X T z hz

local notation3 (prettyPrint := false) "e" => reparametrizedExteriorSupportIso U X T z hz

/-- The actual exterior target map is the free extension of the old middle map. -/
@[reassoc]
theorem reparametrizedExteriorSupportIso_target :
    (e).hom ≫ ((integralComponentAt zT).subschemeι ≫ pullback.snd f g) =
      pullbackParameterExtensionMap p X.hom T.hom := by
  apply pullback.hom_ext («f» := X.hom) («g» := T.hom)
  · simp only [reparametrizedExteriorSupportIso, Iso.trans_hom, Category.assoc,
      nativeExteriorSupportIso_hom_target_assoc, exteriorIdentityTarget_fst,
      pullbackParameterExtensionMap_fst, pullback.congrHom_hom, pullback.lift_fst_assoc,
      Category.id_comp]
  · simp only [reparametrizedExteriorSupportIso, Iso.trans_hom, Category.assoc,
      nativeExteriorSupportIso_hom_target_assoc, exteriorIdentityTarget_snd,
      pullbackParameterExtensionMap_snd, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]

/-- The old source coordinate is unchanged by extending by the parameter. -/
@[reassoc]
theorem reparametrizedExteriorSupportIso_source_fst :
    (e).hom ≫ (integralComponentAt zT).subschemeι ≫ pullback.fst f g ≫
      pullback.fst U.hom T.hom = pullback.fst (p ≫ X.hom) T.hom ≫ q := by
  simp only [reparametrizedExteriorSupportIso, Iso.trans_hom, Category.assoc,
    nativeExteriorSupportIso_hom_source_assoc, exteriorIdentitySource_fst,
    pullback.congrHom_hom, pullback.lift_fst_assoc, Category.id_comp]

/-- The parameter of the actual exterior source is the free left parameter. -/
@[reassoc]
theorem reparametrizedExteriorSupportIso_source_snd :
    (e).hom ≫ (integralComponentAt zT).subschemeι ≫ pullback.fst f g ≫
      pullback.snd U.hom T.hom = pullback.snd (p ≫ X.hom) T.hom := by
  simp only [reparametrizedExteriorSupportIso, Iso.trans_hom, Category.assoc,
    nativeExteriorSupportIso_hom_source_assoc, exteriorIdentitySource_snd,
    pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]

section ClosedIntegral

variable {P D : Scheme.{u}} [IsIntegral P] (j : P ⟶ D) [IsClosedImmersion j]

/-- The reduced closure of the generic point of an integral scheme is the
scheme itself, via its actual inclusion. -/
theorem isIso_integralComponentAt_genericPoint_inclusion :
    IsIso (integralComponentAt (genericPoint P)).subschemeι := by
  have hcl : Closeds.closure ({genericPoint P} : Set P) = ⊤ :=
    Closeds.ext (genericPoint_spec P).def
  apply (Scheme.isIso_subschemeι_iff_eq_bot _).2
  rw [integralComponentAt, hcl, Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]

/-- A closed integral support is the actual native component at its image
generic point. -/
def closedIntegralSupportIso : P ≅ (integralComponentAt (j (genericPoint P))).subscheme := by
  let : IsIso (integralComponentAt (genericPoint P)).subschemeι :=
    isIso_integralComponentAt_genericPoint_inclusion (P := P)
  exact (asIso (integralComponentAt (genericPoint P)).subschemeι).symm ≪≫
    integralComponentIso j (genericPoint P)

/-- The identification retains the literal original closed immersion. -/
@[reassoc (attr := simp)]
theorem closedIntegralSupportIso_hom_inclusion :
    (closedIntegralSupportIso j).hom ≫
      (integralComponentAt (j (genericPoint P))).subschemeι = j := by
  simp only [closedIntegralSupportIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
    integralComponentIso, asIso_hom, integralComponentMap_subschemeι, IsIso.inv_hom_id_assoc]

/-- The same identification when the image point is named separately. -/
def closedIntegralSupportIsoOfEq (w : D) (h : j (genericPoint P) = w) :
    P ≅ (integralComponentAt w).subscheme := by
  subst w
  exact closedIntegralSupportIso j

@[reassoc (attr := simp)]
theorem closedIntegralSupportIsoOfEq_hom_inclusion (w : D) (h : j (genericPoint P) = w) :
    (closedIntegralSupportIsoOfEq j w h).hom ≫ (integralComponentAt w).subschemeι = j := by
  subst w
  exact closedIntegralSupportIso_hom_inclusion j

end ClosedIntegral

end Stacks.Chow
