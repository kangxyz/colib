/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.PolynomialGeometry
public import Colib.AlgebraicGeometry.Correspondences.Principal.RetainedCurveMap

/-! # Geometry of the literal twice-retained open

The retained open after the closed base refinement and marked component restriction is
still affine. A retained section supplies its nonemptiness, hence integrality and dominance
inside the same actual integral normal component. No boundary nonemptiness is inferred here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme

/-- The original affine retained source stays affine through both closed restrictions. -/
theorem isAffine_baseComponent_retained
    {X Xnew Y : Scheme.{u}} [IsLocallyNoetherian Xnew] [IsNormal Xnew] [IsAffine Y]
    (F : Xnew ⟶ X) [IsClosedImmersion F] (j : Y ⟶ X) (x : Xnew) :
    IsAffine (pullback (normalComponentOpen x).ι (pullback.fst F j)) := by
  let h := pullback.snd (normalComponentOpen x).ι (pullback.fst F j) ≫ pullback.snd F j
  let : IsAffineHom h := inferInstance
  exact isAffine_of_isAffineHom h

/-- A section of the twice-retained open gives its nonemptiness. Its actual inclusion in the
marked integral component is consequently dominant; all Noetherian hypotheses are inherited. -/
theorem baseComponent_retained_geometry_of_section
    {X Xnew Y A : Scheme.{u}} [IsNoetherian Xnew] [IsNormal Xnew] [IsAffine Y]
    (F : Xnew ⟶ X) [IsClosedImmersion F] (j : Y ⟶ X) [IsOpenImmersion j]
    (x : Xnew) (σRet : A ⟶ pullback (normalComponentOpen x).ι (pullback.fst F j))
    (a : A) :
    IsAffine (pullback (normalComponentOpen x).ι (pullback.fst F j)) ∧
    IsIntegral (pullback (normalComponentOpen x).ι (pullback.fst F j)) ∧
    IsNoetherian (pullback (normalComponentOpen x).ι (pullback.fst F j)) ∧
    IsDominant (pullback.fst (normalComponentOpen x).ι (pullback.fst F j)) := by
  let : Nonempty (pullback (normalComponentOpen x).ι (pullback.fst F j) : Scheme.{u}) :=
    ⟨σRet a⟩
  let : IsNoetherian (normalComponentOpen x).toScheme :=
    PrincipalFamilyUnitOpen.retainedCurve_isNoetherian (normalComponentOpen x).ι
  let : IsIntegral (pullback (normalComponentOpen x).ι (pullback.fst F j)) :=
    isIntegral_of_isOpenImmersion (pullback.fst (normalComponentOpen x).ι (pullback.fst F j))
  exact ⟨isAffine_baseComponent_retained F j x, inferInstance,
    PrincipalFamilyUnitOpen.retainedCurve_isNoetherian
      (pullback.fst (normalComponentOpen x).ι (pullback.fst F j)),
    isDominant_normalComponentRetainedOpen (pullback.fst F j) x⟩

end AlgebraicGeometry.Scheme
