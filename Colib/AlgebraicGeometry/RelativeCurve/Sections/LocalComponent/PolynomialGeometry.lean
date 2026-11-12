/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.StrictLocal
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.Integral
public import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Noetherian retained components and their actual polynomial cylinders

The proper component over a Noetherian affine base is Noetherian. Its retained open is also
Noetherian, and is quasi-affine or affine whenever the corresponding original open is. The
literal polynomial parameter space used by the principal family is integral and Noetherian.
None of these statements substitutes a different ambient curve or polynomial cylinder.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Scheme

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- Properness over an affine base makes the locally Noetherian component Noetherian. -/
theorem isNoetherian_normalComponentOpen
    {R : Type u} [CommRing R] (p : X ⟶ Spec (.of R)) [IsProper p] (x : X) :
    IsNoetherian (normalComponentOpen x).toScheme := by
  have : CompactSpace (normalComponentOpen x).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace ((normalComponentOpen x).ι ≫ p)
  exact ⟨⟩

/-- The retained open of the same component is Noetherian. -/
theorem isNoetherian_normalComponentRetainedOpen
    {R : Type u} [CommRing R] (p : X ⟶ Spec (.of R)) [IsProper p]
    (j : Y ⟶ X) [IsOpenImmersion j] (x : X) :
    IsNoetherian (pullback (normalComponentOpen x).ι j) := by
  have := isNoetherian_normalComponentOpen p x
  have : IsLocallyNoetherian (pullback (normalComponentOpen x).ι j) :=
    isLocallyNoetherian_of_isOpenImmersion (pullback.fst (normalComponentOpen x).ι j)
  have : TopologicalSpace.NoetherianSpace (pullback (normalComponentOpen x).ι j : Scheme.{u}) :=
    (pullback.fst (normalComponentOpen x).ι j).isOpenEmbedding.isEmbedding.isInducing
      |>.noetherianSpace
  exact ⟨⟩

/-- Restriction to the same clopen component preserves quasi-affineness of the original open. -/
theorem isQuasiAffine_normalComponentRetainedOpen (j : Y ⟶ X) [Y.IsQuasiAffine] (x : X) :
    (pullback (normalComponentOpen x).ι j : Scheme.{u}).IsQuasiAffine :=
  IsQuasiAffine.of_isAffineHom (pullback.snd (normalComponentOpen x).ι j)

/-- If the original retained open is affine, its actual component pullback is affine. -/
theorem isAffine_normalComponentRetainedOpen (j : Y ⟶ X) [IsAffine Y] (x : X) :
    IsAffine (pullback (normalComponentOpen x).ι j) :=
  isAffine_of_isAffineHom (pullback.snd (normalComponentOpen x).ι j)

/-- The nonempty retained open is dense in the chosen integral component. -/
theorem isDominant_normalComponentRetainedOpen (j : Y ⟶ X) [IsOpenImmersion j] (x : X)
    [Nonempty (pullback (normalComponentOpen x).ι j : Scheme.{u})] :
    IsDominant (pullback.fst (normalComponentOpen x).ι j) :=
  ⟨(pullback.fst (normalComponentOpen x).ι j).isOpenMap.isOpen_range.dense
    (Set.range_nonempty _)⟩

/-- The original principal-family polynomial cylinder over the component is integral. -/
theorem isIntegral_normalComponentParameterSpace
    {R : Type u} [CommRing R] (p : X ⟶ Spec (.of R)) (x : X) :
    IsIntegral (PrincipalFamilyUnitOpen.parameterSpace ((normalComponentOpen x).ι ≫ p)) :=
  PrincipalFamilyUnitOpen.isIntegral_parameterSpace _

/-- The same literal polynomial cylinder is Noetherian. -/
theorem isNoetherian_normalComponentParameterSpace
    {R : Type u} [CommRing R] (p : X ⟶ Spec (.of R)) [IsProper p] (x : X) :
    IsNoetherian (PrincipalFamilyUnitOpen.parameterSpace ((normalComponentOpen x).ι ≫ p)) := by
  have := isNoetherian_normalComponentOpen p x
  exact PrincipalFamilyUnitOpen.isNoetherian_parameterSpace _

end Scheme

namespace Scheme

/-- An affine retained morphism stays affine over the actual affine base change. This applies
to the original affine source over the affine base in the good-neighborhood construction. -/
theorem isAffine_pullback_retainedOpen
    {X Y S : Scheme.{u}} {R : Type u} [CommRing R]
    (p : X ⟶ S) (j : Y ⟶ X) (g : Spec (.of R) ⟶ S) [IsAffineHom (j ≫ p)] :
    IsAffine (pullback (pullback.fst p g) j) := by
  have h := (IsPullback.of_hasPullback (pullback.fst p g) j).flip.paste_vert
    (IsPullback.of_hasPullback p g)
  have : IsAffineHom (pullback.fst (pullback.fst p g) j ≫ pullback.snd p g) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) h inferInstance
  exact isAffine_of_isAffineHom (pullback.fst (pullback.fst p g) j ≫ pullback.snd p g)

end Scheme

end AlgebraicGeometry
