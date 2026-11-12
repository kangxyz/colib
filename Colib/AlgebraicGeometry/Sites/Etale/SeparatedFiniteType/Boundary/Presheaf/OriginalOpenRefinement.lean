/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.Geometry
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.SmoothNeighborhood
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison

/-! # Original cylinder refinement along an actual base open

All objects are literal original scheme pullbacks. The whole zero section and
both puncture projections are retained before any scalar extension or section
argument. The original base open is also packaged in its native small site.
-/

/-! Adapted from the original `Boundary/Presheaf/OriginalOpenRefinement.lean`,
blob `a63621dbec07257589f54ed9a7008caa08dcfc00` at motivic commit
`a6805c4a87cdfd7717dd7a94039246a167f15380`. -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k]
  {V U Y : SmoothSite (Spec (.of k))}
  (q₀ : Y ⟶ Contraction.affineLineCylinder.obj V) [Etale q₀.left] (j : U ⟶ V)

/-- The original ambient restricted along the actual base cylinder map. -/
def originalOpenRefinement : SmoothSite (Spec (.of k)) :=
  etalePullback q₀ (Contraction.affineLineCylinder.map j)

/-- The actual ambient projection to the original ambient object. -/
def originalOpenRefinementAmbient : originalOpenRefinement q₀ j ⟶ Y :=
  etalePullbackFst q₀ (Contraction.affineLineCylinder.map j)

/-- The actual cylinder projection after original base restriction. -/
def originalOpenRefinementCylinder : originalOpenRefinement q₀ j ⟶
    Contraction.affineLineCylinder.obj U :=
  etalePullbackSnd q₀ (Contraction.affineLineCylinder.map j)

instance originalOpenRefinementCylinder_etale :
    Etale (originalOpenRefinementCylinder q₀ j).left :=
  inferInstanceAs (Etale (pullback.snd q₀.left (Contraction.affineLineCylinder.map j).left))

instance originalOpenRefinement_affine [IsAffine Y.left] [IsAffine U.left]
    [IsAffine V.left] : IsAffine (originalOpenRefinement q₀ j).left := by
  have : IsAffine ((𝟭 Scheme).obj U.left) := inferInstanceAs (IsAffine U.left)
  have : IsAffine ((𝟭 Scheme).obj V.left) := inferInstanceAs (IsAffine V.left)
  let : IsAffine ((𝟭 Scheme).obj (additiveGroupObject (Spec (.of k))).left) :=
    IsAffine.of_isIso (AlgebraicGeometry.nativePolynomialAffineLineIso (.of k)).hom
  let : IsAffine (Contraction.affineLineCylinder.obj U).left := by
    change IsAffine (pullback U.hom ((SmoothSite.additiveGroupObject (Spec (.of k))).hom))
    exact Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
      (show U.left ⟶ Spec (.of k) from U.hom)
      ((SmoothSite.additiveGroupObject (Spec (.of k))).hom)
  let : IsAffine (Contraction.affineLineCylinder.obj V).left := by
    change IsAffine (pullback V.hom ((SmoothSite.additiveGroupObject (Spec (.of k))).hom))
    exact Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
      (show V.left ⟶ Spec (.of k) from V.hom)
      ((SmoothSite.additiveGroupObject (Spec (.of k))).hom)
  exact Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine q₀.left
    (Contraction.affineLineCylinder.map j).left

/-- The original ambient and cylinder square commutes literally. -/
@[reassoc] theorem originalOpenRefinement_condition :
    originalOpenRefinementAmbient q₀ j ≫ q₀ =
      originalOpenRefinementCylinder q₀ j ≫ Contraction.affineLineCylinder.map j :=
  (etalePullbackCone q₀ (Contraction.affineLineCylinder.map j)).condition

variable (z₀ : V ⟶ Y) (hz₀ : z₀ ≫ q₀ = Contraction.nativeAffineSection (.of k) V 0)

/-- The entire original zero section lifts to the literal restricted ambient. -/
def originalOpenRefinementZero : U ⟶ originalOpenRefinement q₀ j :=
  (IsPullback.of_isLimit (etalePullbackConeIsLimit q₀ (Contraction.affineLineCylinder.map j))).lift
    (j ≫ z₀) (Contraction.nativeAffineSection (.of k) U 0) (by
      rw [Category.assoc, hz₀]
      exact (Contraction.nativeAffineSection_naturality (.of k) j 0).symm)

/-- The lifted whole zero section retains the original ambient mark. -/
@[reassoc] theorem originalOpenRefinementZero_ambient :
    originalOpenRefinementZero q₀ j z₀ hz₀ ≫ originalOpenRefinementAmbient q₀ j = j ≫ z₀ :=
  IsPullback.lift_fst _ _ _ _

/-- The lifted whole zero section is the literal zero section over the new base. -/
@[reassoc] theorem originalOpenRefinementZero_cylinder :
    originalOpenRefinementZero q₀ j z₀ hz₀ ≫ originalOpenRefinementCylinder q₀ j =
      Contraction.nativeAffineSection (.of k) U 0 :=
  IsPullback.lift_snd _ _ _ _

end AlgebraicGeometry.Scheme.SmoothSite

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (W : EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left)
  {V U Y : SmoothSite (Spec (.of k))}
  (v₀ : V ⟶ (toSmoothSite X).obj
    ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W))
  [IsOpenImmersion v₀.left]
  (j : U ⟶ V) [IsOpenImmersion j.left]

local instance originalOpenBase_etale : Etale
    (j ≫ v₀ ≫ toBase X
      ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W)).left := by
  change Etale (j.left ≫ v₀.left ≫
    ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W).hom)
  infer_instance

/-- Package the actual original base open in the native small etale site. -/
def originalOpenBase : EtaleSeparatedFiniteType X.left :=
  ofSmoothMap X U (j ≫ v₀ ≫ toBase X
    ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W))

/-- This canonical comparison is identity on the original underlying open scheme. -/
def originalOpenBaseIso : U ≅ (toSmoothSite X).obj (originalOpenBase X W v₀ j) :=
  ofSmoothMapIso X U (j ≫ v₀ ≫ toBase X
    ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W))

/-- The original small-site image arrow is the composite of the two actual opens. -/
def originalOpenBaseToZero : originalOpenBase X W v₀ j ⟶
    (baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W :=
  MorphismProperty.Over.homMk (j.left ≫ v₀.left) rfl

instance originalOpenBaseToZero_open : IsOpenImmersion (originalOpenBaseToZero X W v₀ j).left :=
  inferInstanceAs (IsOpenImmersion (j.left ≫ v₀.left))

/-- The base packaging leaves the actual original open inclusion unchanged. -/
theorem originalOpenBaseToZero_left :
    (originalOpenBaseToZero X W v₀ j).left = j.left ≫ v₀.left := rfl

variable (q₀ : Y ⟶ SmoothSite.Contraction.affineLineCylinder.obj V) [Etale q₀.left]
  (e₀ : Y ⟶ (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).obj W)
  (hambient : q₀ ≫ SmoothSite.Contraction.affineLineCylinder.map (v₀ ≫ toBase X
    ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W)) =
    e₀ ≫ toBase (SmoothSite.Contraction.affineLineCylinder.obj X) W)

omit [IsOpenImmersion v₀.left] [IsOpenImmersion j.left] in
include hambient in
/-- The restricted ambient retains its original map over the original cylinder. -/
theorem originalOpenRefinement_ambient :
    (SmoothSite.originalOpenRefinementAmbient q₀ j ≫ e₀) ≫
        toBase (SmoothSite.Contraction.affineLineCylinder.obj X) W =
      SmoothSite.originalOpenRefinementCylinder q₀ j ≫
        SmoothSite.Contraction.affineLineCylinder.map (j ≫ v₀ ≫ toBase X
          ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W)) := by
  rw [Category.assoc, ← hambient, ← Category.assoc,
    SmoothSite.originalOpenRefinement_condition, Category.assoc,
    ← Functor.map_comp]

/-- Restricting a whole original zero mark preserves its original zero-fiber map. -/
theorem originalOpenRefinement_mark
    (z₀ : V ⟶ Y) (hz₀ : z₀ ≫ q₀ = SmoothSite.Contraction.nativeAffineSection (.of k) V 0)
    (hmark : z₀.left ≫ e₀.left = v₀.left ≫
      pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left) :
    (SmoothSite.originalOpenRefinementZero q₀ j z₀ hz₀).left ≫
        (SmoothSite.originalOpenRefinementAmbient q₀ j).left ≫ e₀.left =
      (originalOpenBaseToZero X W v₀ j).left ≫
        pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left := by
  have h := congrArg (fun f => f.left)
    (SmoothSite.originalOpenRefinementZero_ambient q₀ j z₀ hz₀)
  change (SmoothSite.originalOpenRefinementZero q₀ j z₀ hz₀).left ≫
    (SmoothSite.originalOpenRefinementAmbient q₀ j).left = j.left ≫ z₀.left at h
  change _ = (j.left ≫ v₀.left) ≫ _
  erw [← Category.assoc, h, Category.assoc, hmark, Category.assoc]

/-- A retained original point remains in the range of the actual small-site open. -/
theorem originalOpenBaseToZero_retains (x : V.left) (hx : x ∈ Set.range j.left) :
    v₀.left x ∈ Set.range (originalOpenBaseToZero X W v₀ j).left := by
  obtain ⟨u, rfl⟩ := hx
  exact ⟨u, rfl⟩

include hambient in
/-- The actual restricted puncture maps directly to the original punctured neighborhood. -/
def originalOpenRefinementToPunctured :
    SmoothSite.etalePullback (SmoothSite.originalOpenRefinementCylinder q₀ j)
      (SmoothSite.Contraction.openInclusion.app U) ⟶
    (toSmoothSite (SmoothSite.Contraction.torusCylinder.obj X)).obj
      ((baseChange (SmoothSite.Contraction.openInclusion.app X).left).obj W) := by
  let q := SmoothSite.originalOpenRefinementCylinder q₀ j
  let r := SmoothSite.originalOpenRefinementAmbient q₀ j
  let a := SmoothSite.etalePullbackFst q (SmoothSite.Contraction.openInclusion.app U)
  let b := SmoothSite.etalePullbackSnd q (SmoothSite.Contraction.openInclusion.app U)
  let f := j ≫ v₀ ≫ toBase X
    ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W)
  let t := SmoothSite.productMap f (𝟙 (SmoothSite.multiplicativeGroupObject (Spec (.of k))))
  have hc : (a ≫ r ≫ e₀) ≫ toBase (SmoothSite.Contraction.affineLineCylinder.obj X) W =
      (b ≫ t) ≫ SmoothSite.Contraction.openInclusion.app X := by
    have h := originalOpenRefinement_ambient X W v₀ j q₀ e₀ hambient
    have hPB := (SmoothSite.etalePullbackCone q (SmoothSite.Contraction.openInclusion.app
U)).condition
    change a ≫ q = b ≫ SmoothSite.Contraction.openInclusion.app U at hPB
    calc
      _ = a ≫ q ≫ SmoothSite.Contraction.affineLineCylinder.map f := by
        simpa only [Category.assoc] using congrArg (fun g => a ≫ g) h
      _ = b ≫ SmoothSite.Contraction.openInclusion.app U ≫
SmoothSite.Contraction.affineLineCylinder.map f := by
        rw [← Category.assoc, hPB, Category.assoc]
      _ = _ := by rw [← SmoothSite.Contraction.openInclusion.naturality]; rfl
  exact SmoothSite.homMk
    (pullback.lift (a.left ≫ r.left ≫ e₀.left) (b.left ≫ t.left)
      (congrArg (fun f => f.left) hc)) (by
        change pullback.lift _ _ _ ≫
          (pullback.snd W.hom (SmoothSite.Contraction.openInclusion.app X).left ≫
            (SmoothSite.Contraction.torusCylinder.obj X).hom) = _
        rw [pullback.lift_snd_assoc]
        exact MorphismProperty.Over.w (b ≫ t))

omit [IsOpenImmersion v₀.left] [IsOpenImmersion j.left] in
/-- The direct puncture map retains its actual ambient projection. -/
@[reassoc] theorem originalOpenRefinementToPunctured_fst :
    (originalOpenRefinementToPunctured X W v₀ j q₀ e₀ hambient).left ≫
      pullback.fst W.hom (SmoothSite.Contraction.openInclusion.app X).left =
    (SmoothSite.etalePullbackFst (SmoothSite.originalOpenRefinementCylinder q₀ j)
      (SmoothSite.Contraction.openInclusion.app U)).left ≫
        (SmoothSite.originalOpenRefinementAmbient q₀ j).left ≫ e₀.left := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

omit [IsOpenImmersion v₀.left] [IsOpenImmersion j.left] in
/-- The direct puncture map retains its actual Laurent projection. -/
@[reassoc] theorem originalOpenRefinementToPunctured_snd :
    (originalOpenRefinementToPunctured X W v₀ j q₀ e₀ hambient).left ≫
      pullback.snd W.hom (SmoothSite.Contraction.openInclusion.app X).left =
    (SmoothSite.etalePullbackSnd (SmoothSite.originalOpenRefinementCylinder q₀ j)
      (SmoothSite.Contraction.openInclusion.app U)).left ≫
        (SmoothSite.productMap (j ≫ v₀ ≫ toBase X
          ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W))
          (𝟙 (SmoothSite.multiplicativeGroupObject (Spec (.of k))))).left := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  exact pullback.lift_snd _ _ _

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
