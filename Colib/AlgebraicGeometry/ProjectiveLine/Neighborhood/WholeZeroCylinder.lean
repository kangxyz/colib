/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.Neighborhood.WholeZeroLifting
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholePolynomialCylinder
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.Restriction

/-! # The constructed second correction on the actual whole native torus

The entire second source is identified with the native multiplicative cylinder.
The first source is an actual open of the whole native additive cylinder and
contains its complete zero section. All original overlap and ambient maps
remain the generic pencil's actual pullback maps, with beta-minus-alpha sign.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open AlgebraicGeometry.Scheme.RelativeCurvePencil
open AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine.ZeroNeighborhood
variable {k : Type u} [Field k] (R : Type u) [CommRing R]
  [Algebra k R] [Algebra.Smooth k R]
  (O : (Spec (.of (Polynomial R))).Opens) [IsAffine O.toScheme]
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k R))
local notation "q" => coordinateLineProjection R
local notation "π" => compactProjection R
local notation "j" => O.ι ≫ chart R
local notation "hq" => inclusion_projection R O
local notation "a" => Scheme.Opens.ι (puncture R)
local notation "v" => retainedInclusion R O
local notation "φ" => overlapToRetained R O
local notation "hφ" => overlapToRetained_projective R O
local instance : IsAffine (puncture R).toScheme := IsAffineOpen.Spec_basicOpen _
local instance : IsAffine (punctureOpen R O).toScheme :=
  punctureOpen_affine R O (show IsAffineOpen O from ‹IsAffine O.toScheme›)
local instance : SmoothOfRelativeDimension 1 (v ≫ π) := by
  simpa only [compactProjection, Category.id_comp] using
    (inferInstance : SmoothOfRelativeDimension 1
      (retainedInclusion R O ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))))

section Geometry
variable (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]
local instance : IsAffine (parameterOpen q ⊤ V).toScheme := by
  change IsAffineOpen (parameterOpen q ⊤ V)
  have h : IsAffineOpen (q ⁻¹ᵁ V) := (show IsAffineOpen V from ‹IsAffine V.toScheme›).preimage q
  simpa only [parameterOpen, top_inf_eq] using h

/-- The first original pullback projects to the unchanged parameter. -/
def wholeZeroFirstParameter : refinedFirstSite b q ⊤ V π j O.ι hq ⟶
    wholeParameterSite (k := k) V :=
  SmoothSite.homMk (firstMap q ⊤ V O.ι) (by
    change firstMap q ⊤ V O.ι ≫ (parameterProjection q ⊤ V ≫ V.ι ≫ b) =
      (firstInclusion q ⊤ V π j O.ι hq ≫ compactificationProjection π V) ≫ (V.ι ≫ b)
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ (V.ι ≫ b)) (firstInclusion_projection q ⊤ V π j O.ι hq).symm))

/-- This is the actual first-source open inside the whole native cylinder. -/
def wholeZeroFirstCylinder : refinedFirstSite b q ⊤ V π j O.ι hq ⟶
    Contraction.affineLineCylinder.obj ((opensFunctor (affineSite k R)).obj V) :=
  wholeZeroFirstParameter (k := k) R O V ≫ (wholeParameterCylinderIso (k := k) V).hom

instance : IsOpenImmersion (wholeZeroFirstCylinder (k := k) R O V).left := by
  change IsOpenImmersion (pullback.snd O.ι (parameterOpen q ⊤ V).ι ≫
    (wholeParameterCylinderIso (k := k) V).hom.left)
  infer_instance

/-- The actual signed beta, now with the whole native torus as codomain. -/
def wholeZeroBeta : refinedOverlapSite b q ⊤ V π j O.ι hq a ⟶
    Contraction.torusCylinder.obj ((opensFunctor (affineSite k R)).obj V) :=
  refinedBeta b q ⊤ V π j O.ι hq a ≫ (wholeSecondTorusIso (k := k) V).hom

/-- The whole signed overlap remains Cartesian after the exact native comparisons. -/
theorem wholeZeroCylinder_isPullback :
    IsPullback (wholeZeroBeta (k := k) R O V) (refinedAlpha b q ⊤ V π j O.ι hq a)
      (Contraction.openInclusion.app ((opensFunctor (affineSite k R)).obj V))
      (wholeZeroFirstCylinder (k := k) R O V) := by
  have H : IsPullback (refinedBeta b q ⊤ V π j O.ι hq a)
      (refinedAlpha b q ⊤ V π j O.ι hq a)
      (wholeSecondParameter (k := k) V) (wholeZeroFirstParameter (k := k) R O V) := by
    apply IsPullback.of_map_of_faithful (forgetScheme (Spec (.of k)))
    exact (IsPullback.of_hasPullback (firstMap q ⊤ V O.ι) (secondMap q ⊤ V a)).flip
  apply H.of_iso (Iso.refl _) (wholeSecondTorusIso (k := k) V)
    (Iso.refl _) (wholeParameterCylinderIso (k := k) V)
  · simp only [Iso.refl_hom, Category.id_comp, wholeZeroBeta]
  · simp
  · exact (wholeSecondTorusIso_open (k := k) V).symm
  · simp only [Iso.refl_hom, Category.id_comp, wholeZeroFirstCylinder]

/-- The complete base V lifts to the first source through the original zero. -/
def wholeZeroFirstSection (hO : Set.range (polynomialZero R) ⊆ O) :
    V.toScheme ⟶ (refinedFirstSite b q ⊤ V π j O.ι hq).left :=
  pullback.lift (V.ι ≫ zeroLift R O hO) (wholeParameterZero (k := k) V).left
    (((Category.assoc _ _ _).trans (congrArg (V.ι ≫ ·) (zeroLift_original R O hO))).trans
      (wholeParameterZero_original (k := k) V).symm)

@[reassoc (attr := simp)] theorem wholeZeroFirstSection_original
    (hO : Set.range (polynomialZero R) ⊆ O) :
    wholeZeroFirstSection (k := k) R O V hO ≫ pullback.fst O.ι (parameterOpen q ⊤ V).ι =
      V.ι ≫ zeroLift R O hO := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem wholeZeroFirstSection_parameter
    (hO : Set.range (polynomialZero R) ⊆ O) :
    wholeZeroFirstSection (k := k) R O V hO ≫ pullback.snd O.ι (parameterOpen q ⊤ V).ι =
      (wholeParameterZero (k := k) V).left := pullback.lift_snd _ _ _

/-- The entire section maps to native zero, with its original scheme structure. -/
@[reassoc] theorem wholeZeroFirstSection_cylinder
    (hO : Set.range (polynomialZero R) ⊆ O) :
    wholeZeroFirstSection (k := k) R O V hO ≫ (wholeZeroFirstCylinder (k := k) R O V).left =
      (Contraction.nativeAffineSection (.of k)
        ((opensFunctor (affineSite k R)).obj V) 0).left := by
  change wholeZeroFirstSection (k := k) R O V hO ≫
    (pullback.snd O.ι (parameterOpen q ⊤ V).ι ≫
      (wholeParameterCylinderIso (k := k) V).hom.left) = _
  rw [← Category.assoc, wholeZeroFirstSection_parameter]
  exact congrArg (fun f => f.left) (wholeParameterZero_cylinder (k := k) V)

/-- This is a full Cartesian zero square, not just a section equality on points. -/
theorem wholeZeroFirstSection_isPullback
    (hO : Set.range (polynomialZero R) ⊆ O) :
    IsPullback (wholeZeroFirstSection (k := k) R O V hO) (𝟙 _)
      (wholeZeroFirstCylinder (k := k) R O V).left
      (Contraction.nativeAffineSection (.of k)
        ((opensFunctor (affineSite k R)).obj V) 0).left :=
  IsPullback.of_vert_isIso_mono ⟨by
    simpa only [Category.id_comp] using wholeZeroFirstSection_cylinder (k := k) R O V hO⟩

/-- The native first-cylinder map retains the original polynomial ambient arrow. -/
@[reassoc] theorem wholeZeroFirstCylinder_original :
    (wholeZeroFirstCylinder (k := k) R O V).left ≫
      (Contraction.affineLineCylinder.map (SmoothSite.openInclusion (affineSite k R) V)).left =
    pullback.fst O.ι (parameterOpen q ⊤ V).ι ≫ O.ι ≫
      (lineCylinderIso (k := k) (R := R)).hom.left := by
  change (pullback.snd O.ι (parameterOpen q ⊤ V).ι ≫
    (wholeParameterCylinderIso (k := k) V).hom.left) ≫ _ = _
  rw [Category.assoc, wholeParameterCylinderIso_original, ← Category.assoc]
  exact (congrArg (· ≫ (lineCylinderIso (k := k) (R := R)).hom.left)
    (pullback.condition (f := O.ι) (g := (parameterOpen q ⊤ V).ι)).symm).trans
      (Category.assoc _ _ _)

end Geometry

/-- The second signed correction is constructed from HI on the full native
puncture cylinder. Its zero and Cartesian equations are the declarations above. -/
theorem exists_wholeZero_native_torus_lifting
    (hO : Set.range (polynomialZero R) ⊆ O) (w : Spec (.of R))
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V), w ∈ V ∧
      letI : IsAffine V.toScheme := hV
      letI : IsAffine (parameterOpen q ⊤ V).toScheme := by
        change IsAffineOpen (parameterOpen q ⊤ V)
        have h : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
        simpa only [parameterOpen, top_inf_eq] using h
      PresheafWithTransfers.HasRestrictionDifferenceLifting P
        (refinedGraph b q ⊤ V π j O.ι hq a v φ hφ)
        (wholeZeroBeta (k := k) R O V) (refinedAlpha b q ⊤ V π j O.ι hq a) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  obtain ⟨V, hV, hw, hW, hL⟩ := exists_wholeZero_base_lifting (k := k) R b O hO w P hP
  let : IsAffine V.toScheme := hV
  let : IsAffine (parameterOpen q ⊤ V).toScheme := hW
  exact ⟨V, hV, hw,
    PresheafWithTransfers.HasRestrictionDifferenceLifting.iso_right P hL
      (wholeSecondTorusIso (k := k) V)⟩

end AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine.ZeroNeighborhood
