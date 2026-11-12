/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.RelativeLine.MonicDegreeOne
public import Colib.AlgebraicGeometry.Sites.Smooth.AffineLine.WholeBase.CylinderTransport
public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.CylinderOpenImage

/-! # Degree-one vanishing on the whole cylinder over a generic base open

Adapted from `Motivic/Cohomology/A1/LocalVanishing/GenericBase/H1Zero.lean`
and `Motivic/Cohomology/A1/LocalVanishing/GenericBase/CylinderZero.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
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

/-- Every ordinary degree-one cylinder class becomes zero over an
affine open containing the original generic point. The restriction is literally
the native cylinder functor on the original base-open inclusion. -/
theorem exists_generic_base_cylinder_h_one_zero
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (x : (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).obj
      (op (Contraction.affineLineCylinder.obj X))) :
    ∃ V : X.left.Opens, IsAffineOpen V ∧ genericPoint X.left ∈ V ∧
      (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).map
        (Contraction.affineLineCylinder.map (SmoothSite.openInclusion X V)).op x = 0 := by
  let R := Γ(X.left, ⊤)
  let : Algebra k R := SmoothSite.AffineSectionCoordinates.sectionsAlgebra X
  let : Algebra.Smooth k R := SmoothSite.AffineSectionCoordinates.sections_smooth X
  let P := cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1
  let e : affineSite k R ≅ X := affineIso X
  let x' : P.obj (op (lineSite (k := k) (R := R))) :=
    P.map (affineLineIso X).hom.op x
  obtain ⟨r, hr, s, hs, V, hV, hη, hz⟩ :=
    exists_relative_generic_base_h_one_zero (k := k) (R := R) F hF x'
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
  have hz' : P.map (Contraction.affineLineCylinder.map j).op x = 0 :=
    cylinder_restriction_zero_of_lineBaseOpen (k := k) (X := X) P e φ ψ V x hz
  exact exists_affine_generic_open_cylinder_zero_of_openImmersion (k := k) (Y := Y) (X := X)
    P j x hz'

end AlgebraicGeometry.SheafCohomology
