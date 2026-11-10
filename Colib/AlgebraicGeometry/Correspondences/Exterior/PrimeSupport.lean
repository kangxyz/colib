/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Postcomposition

/-!
# Literal exterior support and native integral-component support

The closed image ideal equals integralComponentAt of its actual generic point.
Transport the existing closed-immersion toImage isomorphism along this native
ideal equality. The resulting isomorphism retains the actual ambient inclusion,
so it can be used in incidence comparisons without introducing a support model.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
universe u
namespace Stacks.Chow

private theorem subscheme_eqToIso_hom_ι {A : Scheme.{u}} (I J : A.IdealSheafData)
    (h : I = J) : (eqToIso (congrArg (fun W => W.subscheme) h)).hom ≫ J.subschemeι =
      I.subschemeι := by
  subst J
  simp

variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

/-- The native component ideal is exactly the actual exterior closed image ideal. -/
theorem nativeExteriorPoint_ideal :
    integralComponentAt (nativeExteriorPoint X Y T z hz) =
      (exteriorIdentityInclusion X Y T (integralComponentAt z)).ker :=
  integralComponentAt_genericPointOf _ _

/-- The actual literal support is isomorphic to the native cycle's actual integral support. -/
def nativeExteriorSupportIso : exteriorIdentitySupport X Y T (integralComponentAt z) ≅
    (integralComponentAt (nativeExteriorPoint X Y T z hz)).subscheme := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt z)) := hz.1
  let e := exteriorIdentityInclusion X Y T (integralComponentAt z)
  let : IsIso e.toImage := IsClosedImmersion.instIsIsoSchemeToImage e
  exact asIso e.toImage ≪≫
    eqToIso (congrArg (fun W => W.subscheme) (nativeExteriorPoint_ideal X Y T z hz).symm)

/-- The isomorphism retains the literal ambient inclusion, not only its point image. -/
@[reassoc]
theorem nativeExteriorSupportIso_hom_inclusion :
    (nativeExteriorSupportIso X Y T z hz).hom ≫
      (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι =
      exteriorIdentityInclusion X Y T (integralComponentAt z) := by
  dsimp only [nativeExteriorSupportIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, subscheme_eqToIso_hom_ι _ _ (nativeExteriorPoint_ideal X Y T z hz).symm]
  exact Scheme.Hom.toImage_imageι _

@[reassoc]
theorem nativeExteriorSupportIso_hom_source :
    (nativeExteriorSupportIso X Y T z hz).hom ≫
      (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι ≫
        pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom =
      exteriorIdentitySource X Y T (integralComponentAt z) := by
  rw [← Category.assoc, nativeExteriorSupportIso_hom_inclusion,
    exteriorIdentityInclusion_fst]

@[reassoc]
theorem nativeExteriorSupportIso_hom_target :
    (nativeExteriorSupportIso X Y T z hz).hom ≫
      (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom =
      exteriorIdentityTarget X Y T (integralComponentAt z) := by
  rw [← Category.assoc, nativeExteriorSupportIso_hom_inclusion,
    exteriorIdentityInclusion_snd]

@[reassoc]
theorem nativeExteriorSupportIso_inv_source :
    (nativeExteriorSupportIso X Y T z hz).inv ≫
      exteriorIdentitySource X Y T (integralComponentAt z) =
      (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι ≫
        pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom := by
  rw [← nativeExteriorSupportIso_hom_source X Y T z hz, Iso.inv_hom_id_assoc]

@[reassoc]
theorem nativeExteriorSupportIso_inv_target :
    (nativeExteriorSupportIso X Y T z hz).inv ≫
      exteriorIdentityTarget X Y T (integralComponentAt z) =
      (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom := by
  rw [← nativeExteriorSupportIso_hom_target X Y T z hz, Iso.inv_hom_id_assoc]

attribute [colib_tag "COL-0386", colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Basic.lean:219-238"
  "adaptation" "Native cycle support, maps and explicitly stated hypotheses"]
  nativeExteriorSupportIso
  nativeExteriorPoint_ideal

end Stacks.Chow
