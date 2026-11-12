/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.RelativeLine.HigherVanishing
public import Colib.AlgebraicGeometry.Sites.Smooth.AffineLine.WholeBase.CylinderTransport
public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.CylinderOpenImage

/-! # Higher ordinary cylinder classes vanish over the original generic base open

The class and its final whole-cylinder restriction are over the unchanged
smooth-site object. This is the degree-at-least-two branch, for any ordinary
abelian sheaf. Degree one and the strict-invariance endpoint are not asserted.
-/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/GenericBase/CylinderZero.lean`, blob
`6e20cde5034c63a871c1069e78c3e680742ed752`.
The active affine cylinder remains the existing native additive group object.
The polynomial spectrum is only an explicit comparison target.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.PolynomialLaurent
universe w u
namespace AlgebraicGeometry.SheafCohomology
open _root_.AlgebraicGeometry.Scheme _root_.Stacks.Cohomology.FreeYonedaUnivLE
open _root_.Algebra.Smooth
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineSectionCoordinates
variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
attribute [local instance] away_smooth

/-- Every ordinary cylinder class in degree at least two becomes zero over an
affine open containing the original generic point. The restriction is literally
the native cylinder functor on the original base-open inclusion. -/
theorem exists_generic_base_cylinder_h_add_two_zero
    (F : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) (n : ℕ)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (x : (cohomologyPresheaf.{w, u + 1} F (n + 2)).obj
      (op (Contraction.affineLineCylinder.obj X))) :
    ∃ V : X.left.Opens, IsAffineOpen V ∧ genericPoint X.left ∈ V ∧
      (cohomologyPresheaf.{w, u + 1} F (n + 2)).map
        (Contraction.affineLineCylinder.map (SmoothSite.openInclusion X V)).op x = 0 := by
  let R := Γ(X.left, ⊤)
  let : Algebra k R := sectionsAlgebra X
  let P := cohomologyPresheaf.{w, u + 1} F (n + 2)
  let e := affineIso X
  let x' : P.obj (op (lineSite (k := k) (R := R))) :=
    P.map (affineLineIso X).hom.op x
  obtain ⟨r, hr, s, hs, V, hV, hη, hz⟩ :=
    exists_relative_generic_base_h_add_two_zero F n x'
  let : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
  let : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
  let φ : R →ₐ[k] Localization.Away r := IsScalarTower.toAlgHom k R (Localization.Away r)
  let ψ : Localization.Away r →ₐ[k] Localization.Away s :=
    IsScalarTower.toAlgHom k (Localization.Away r) (Localization.Away s)
  let Y := (opensFunctor (affineSite k (Localization.Away s))).obj V
  let : IsAffine Y.left := hV
  let : Nonempty Y.left := ⟨⟨genericPoint (Spec (.of (Localization.Away s))), hη⟩⟩
  let j : Y ⟶ X := SmoothSite.openInclusion (affineSite k (Localization.Away s)) V ≫
    affineMorphism ψ ≫ affineMorphism φ ≫ e.hom
  have : IsOpenImmersion j.left := by
    change IsOpenImmersion (V.ι ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away r) (Localization.Away s))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ X.left.isoSpec.inv)
    infer_instance
  have hz' : P.map (Contraction.affineLineCylinder.map j).op x = 0 := by
    apply cylinder_restriction_zero_of_lineBaseOpen P e φ ψ V x
    exact hz
  exact exists_affine_generic_open_cylinder_zero_of_openImmersion P j x hz'

end AlgebraicGeometry.SheafCohomology
