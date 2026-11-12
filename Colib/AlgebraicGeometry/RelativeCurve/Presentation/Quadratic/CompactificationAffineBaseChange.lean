/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ActualCartesianAffineChart
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal

/-! # The original quadratic compactification after an affine smooth base change

The actual curve uses the base-first pullback ordering of EtaleChart and EtaleLimit.
Finite covers and both coordinate charts are transported by the existing actual-Cartesian
interfaces. Normality comes from smoothness over the original normal compactification;
no irreducibility assertion is made for the new curve.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme
variable {A R : Type u} [CommRing A] [CommRing R]
  {N : Scheme.{u}} (p : N ⟶ Spec (.of A)) (f : A →+* R)

/-- The real compactification in base-first ordering. -/
abbrev quadraticCompactificationBaseChange := pullback (Spec.map (CommRingCat.ofHom f)) p

/-- The canonical Cartesian square, not an extra compatibility input. -/
theorem quadraticCompactificationBaseChange_square :
    IsPullback (pullback.snd (Spec.map (CommRingCat.ofHom f)) p)
      (pullback.fst (Spec.map (CommRingCat.ofHom f)) p) p (Spec.map (CommRingCat.ofHom f)) :=
  (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom f)) p).flip

/-- Smooth change of base gives a normal actual curve over the original normal model. -/
theorem quadraticCompactificationBaseChange_isNormal
    [IsNormal N] [Smooth (Spec.map (CommRingCat.ofHom f))] :
    IsNormal (quadraticCompactificationBaseChange p f) := by
  exact isNormal_of_smooth (pullback.snd (Spec.map (CommRingCat.ofHom f)) p)

/-- Properness is preserved on the original projection. -/
instance quadraticCompactificationBaseChange_isProper [IsProper p] :
    IsProper (pullback.fst (Spec.map (CommRingCat.ofHom f)) p) := inferInstance

variable (π : N ⟶ projectiveLine A)
  (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p)

/-- The same original finite polynomial cover on the actual base-changed curve. -/
abbrev quadraticCompactificationBaseChangeCover :
    quadraticCompactificationBaseChange p f ⟶ projectiveLine R :=
  projectiveLineCoverOfActualCartesian p f _ _
    (quadraticCompactificationBaseChange_square p f) π hπ

instance quadraticCompactificationBaseChangeCover_isFinite [IsFinite π] :
    IsFinite (quadraticCompactificationBaseChangeCover p f π hπ) := by
  unfold quadraticCompactificationBaseChangeCover
  infer_instance

@[reassoc] theorem quadraticCompactificationBaseChangeCover_structure :
    quadraticCompactificationBaseChangeCover p f π hπ ≫
      (projectiveLine R ↘ Spec (.of R)) = pullback.fst (Spec.map (CommRingCat.ofHom f)) p :=
  projectiveLineCoverOfActualCartesian_structure p f _ _
    (quadraticCompactificationBaseChange_square p f) π hπ

variable {E : Scheme.{u}} (e : E ⟶ N)
  (a : E ⟶ Spec (.of (Polynomial A)))
  (ha : a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = e ≫ p)

/-- Apply separately to the retained chart and the independent etale chart. -/
abbrev quadraticCompactificationBaseChangeChart :
    pullback (pullback.snd (Spec.map (CommRingCat.ofHom f)) p) e ⟶ Spec (.of (Polynomial R)) :=
  affineLineChartOfActualCartesian p f _ _
    (quadraticCompactificationBaseChange_square p f) e a ha

instance quadraticCompactificationBaseChangeChart_etale [Etale a] :
    Etale (quadraticCompactificationBaseChangeChart p f e a ha) := by
  unfold quadraticCompactificationBaseChangeChart
  infer_instance

@[reassoc] theorem quadraticCompactificationBaseChangeChart_structure :
    quadraticCompactificationBaseChangeChart p f e a ha ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
      pullback.fst (pullback.snd (Spec.map (CommRingCat.ofHom f)) p) e ≫
        pullback.fst (Spec.map (CommRingCat.ofHom f)) p :=
  affineLineChartOfActualCartesian_structure p f _ _
    (quadraticCompactificationBaseChange_square p f) e a ha

theorem quadraticCompactificationBaseChangeChart_cover
    (he : e ≫ π = a ≫ projectiveLineXChart A) :
    pullback.fst (pullback.snd (Spec.map (CommRingCat.ofHom f)) p) e ≫
        quadraticCompactificationBaseChangeCover p f π hπ =
      quadraticCompactificationBaseChangeChart p f e a ha ≫ projectiveLineXChart R :=
  affineLineChartOfActualCartesian_comp_XChart p f _ _
    (quadraticCompactificationBaseChange_square p f) e a ha π hπ he
end AlgebraicGeometry.Scheme
