/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSphere
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison

import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.ZeroComparison

/-!
# The native affine-line contraction relative to its point one

The actual affine-space comparison supplies the coordinate of the native
line. The contraction on its native relative product sends coordinates
`x` and `t` to `b + t * (x - b)`, where `b` is the pullback of the original
point one. The literal polynomial-evaluation endpoints give the constant
map at the chosen point and the identity.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "S" => Spec R
local notation "L" => additiveGroupObject (Spec R)

private def nativeLineCoordinate : Γ((L).left, ⊤) :=
  let e : (L).left ≅ AffineSpace (ULift.{u} Unit) S := additiveGroupBaseChangeAffineSpaceIso S
  e.hom.appTop (AffineSpace.coord S (ULift.up ()))

private def pullLineCoordinate {U : SmoothSite S} (f : U ⟶ L) : Γ(U.left, ⊤) :=
  f.left.appTop (nativeLineCoordinate R)

private theorem pullLineCoordinate_comp {U V : SmoothSite S} (f : U ⟶ V) (g : V ⟶ L) :
    pullLineCoordinate R (f ≫ g) = f.left.appTop (pullLineCoordinate R g) := by
  change ((f.left ≫ g.left).appTop) (nativeLineCoordinate R) =
    f.left.appTop (g.left.appTop (nativeLineCoordinate R))
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

private theorem pullLineCoordinate_injective (U : SmoothSite S) :
    Function.Injective (pullLineCoordinate R (U := U)) := by
  intro f g h
  let e : (L).left ≅ AffineSpace (ULift.{u} Unit) S := additiveGroupBaseChangeAffineSpaceIso S
  let p : AffineSpace (ULift.{u} Unit) S ⟶ S := AffineSpace (ULift.{u} Unit) S ↘ S
  have he : e.hom ≫ p = (L).hom := additiveGroupBaseChangeAffineSpaceIso_hom_over S
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono e.hom).1
  apply AffineSpace.hom_ext
  · have hover (a : U ⟶ L) : (a.left ≫ e.hom) ≫ p = U.hom :=
      (Category.assoc _ _ _).trans
        ((congrArg (a.left ≫ ·) he).trans (MorphismProperty.Over.w a))
    exact (hover f).trans (hover g).symm
  · intro i
    have hi : i = ULift.up () := Subsingleton.elim _ _
    subst i
    let t := AffineSpace.coord S (ULift.up ())
    have hcoord (a : U ⟶ L) : ((a.left ≫ e.hom).appTop) t = pullLineCoordinate R a := by
      change ((a.left ≫ e.hom).appTop) t = a.left.appTop (e.hom.appTop t)
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    exact (hcoord f).trans (h.trans (hcoord g).symm)

private def nativeLineMap (U : SmoothSite S) (x : Γ(U.left, ⊤)) : U ⟶ L := by
  let e : (L).left ≅ AffineSpace (ULift.{u} Unit) S := additiveGroupBaseChangeAffineSpaceIso S
  let p : U.left ⟶ S := U.hom
  let q : AffineSpace (ULift.{u} Unit) S ⟶ S := AffineSpace (ULift.{u} Unit) S ↘ S
  let f : U.left ⟶ AffineSpace (ULift.{u} Unit) S := AffineSpace.homOfVector p (fun _ => x)
  refine homMk (f ≫ e.inv) ?_
  have he : e.hom ≫ q = (L).hom := additiveGroupBaseChangeAffineSpaceIso_hom_over S
  change (f ≫ e.inv) ≫ (L).hom = p
  calc
    _ = f ≫ e.inv ≫ e.hom ≫ q :=
      (Category.assoc _ _ _).trans (congrArg (fun a => f ≫ e.inv ≫ a) he.symm)
    _ = f ≫ q := congrArg (f ≫ ·) (e.inv_hom_id_assoc q)
    _ = _ := AffineSpace.homOfVector_over p (fun _ => x)

private theorem nativeLineMap_coordinate (U : SmoothSite S) (x : Γ(U.left, ⊤)) :
    pullLineCoordinate R (nativeLineMap R U x) = x := by
  let e : (L).left ≅ AffineSpace (ULift.{u} Unit) S := additiveGroupBaseChangeAffineSpaceIso S
  let p : U.left ⟶ S := U.hom
  let f : U.left ⟶ AffineSpace (ULift.{u} Unit) S := AffineSpace.homOfVector p (fun _ => x)
  change ((f ≫ e.inv).appTop) (e.hom.appTop (AffineSpace.coord S (ULift.up ()))) = _
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  exact AffineSpace.homOfVector_appTop_coord p (fun _ => x) (ULift.up ())

/-- The original evaluation point in the native affine-line parameter. -/
abbrev affineLineParameterPoint (a : R) : base S ⟶ L :=
  polynomialAffinePoint R a ≫ (affineLinePolynomialIso R).inv

private theorem affineLineParameterPoint_coordinate (a : R) :
    pullLineCoordinate R (affineLineParameterPoint R a) = (Scheme.ΓSpecIso R).inv a := by
  let e : (L).left ≅ AffineSpace (ULift.{u} Unit) S := additiveGroupBaseChangeAffineSpaceIso S
  have he : (affineLinePolynomialIso R).inv.left ≫ e.hom = (polynomialAffineSpaceIso R).hom := by
    change (nativePolynomialAffineLineIso R).inv ≫ e.hom = (polynomialAffineSpaceIso R).hom
    simp only [nativePolynomialAffineLineIso, Iso.trans_inv, Iso.symm_inv, e, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  change (((polynomialAffinePoint R a).left ≫ (affineLinePolynomialIso R).inv.left).appTop)
      (e.hom.appTop (AffineSpace.coord S (ULift.up ()))) = _
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Category.assoc, he]
  change (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫
      (polynomialAffineSpaceIso R).hom).appTop (AffineSpace.coord S (ULift.up ())) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, polynomialAffineSpaceIso_hom_appTop_coord]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  change (Scheme.ΓSpecIso R).inv (Polynomial.eval a Polynomial.X) = _
  rw [Polynomial.eval_X]

/-- The actual contraction of the native line at its chosen point one. -/
@[no_expose]
def affineLineContractionAtOne : product L L ⟶ L :=
  let P := product L L
  let b := pullLineCoordinate R (toBase P ≫ affineLineOne R)
  let x := pullLineCoordinate R (productFst L L)
  let t := pullLineCoordinate R (productSnd L L)
  nativeLineMap R P (b + t * (x - b))

private theorem affineLineContractionAtOne_coordinate {U : SmoothSite S} (f : U ⟶ product L L) :
    pullLineCoordinate R (f ≫ affineLineContractionAtOne R) =
      pullLineCoordinate R (toBase U ≫ affineLineOne R) +
        pullLineCoordinate R (f ≫ productSnd L L) *
          (pullLineCoordinate R (f ≫ productFst L L) -
            pullLineCoordinate R (toBase U ≫ affineLineOne R)) := by
  let b := toBase (product L L) ≫ affineLineOne R
  let x := productFst L L
  let t := productSnd L L
  have hb : f ≫ b = toBase U ≫ affineLineOne R := by
    change f ≫ toBase (product L L) ≫ affineLineOne R = _
    rw [← Category.assoc, comp_toBase]
  have h : pullLineCoordinate R (affineLineContractionAtOne R) =
      pullLineCoordinate R b + pullLineCoordinate R t *
        (pullLineCoordinate R x - pullLineCoordinate R b) := nativeLineMap_coordinate R _ _
  have hfb : f.left.appTop (pullLineCoordinate R b) =
      pullLineCoordinate R (toBase U ≫ affineLineOne R) :=
    (pullLineCoordinate_comp R f b).symm.trans (congrArg (pullLineCoordinate R) hb)
  rw [pullLineCoordinate_comp R f (affineLineContractionAtOne R), h, map_add, map_mul, map_sub,
    hfb, ← pullLineCoordinate_comp R f t, ← pullLineCoordinate_comp R f x]

/-- The contraction fixes the whole cylinder on the actual chosen point. -/
@[reassoc]
theorem affineLineContractionAtOne_pointAxis :
    productLift (toBase L ≫ affineLineOne R) (𝟙 L) ≫ affineLineContractionAtOne R =
      toBase L ≫ affineLineOne R := by
  apply pullLineCoordinate_injective R L
  rw [affineLineContractionAtOne_coordinate, productLift_fst, productLift_snd]
  rw [sub_self, mul_zero, add_zero]

/-- Evaluation at the original parameter zero gives the chosen constant map. -/
@[reassoc]
theorem affineLineContractionAtOne_zero :
    nativeAffineSection R L 0 ≫ affineLineContractionAtOne R = toBase L ≫ affineLineOne R := by
  apply pullLineCoordinate_injective R L
  let s : L ⟶ product L L := nativeAffineSection R L 0
  change pullLineCoordinate R (s ≫ affineLineContractionAtOne R) = _
  have hs : s ≫ productSnd L L =
      toBase L ≫ affineLineParameterPoint R 0 :=
    productLift_snd _ _
  rw [affineLineContractionAtOne_coordinate R s, hs,
    pullLineCoordinate_comp R (toBase L) (affineLineParameterPoint R 0),
    affineLineParameterPoint_coordinate]
  let p : (L).left ⟶ S := (toBase L).left
  let b := pullLineCoordinate R (toBase L ≫ affineLineOne R)
  let x := pullLineCoordinate R (s ≫ productFst L L)
  change b + p.appTop ((Scheme.ΓSpecIso R).inv (0 : R)) * (x - b) = b
  rw [map_zero, map_zero, zero_mul, add_zero]

/-- Evaluation at the original parameter one gives the identity. -/
@[reassoc]
theorem affineLineContractionAtOne_one :
    nativeAffineSection R L 1 ≫ affineLineContractionAtOne R = 𝟙 L := by
  apply pullLineCoordinate_injective R L
  let s : L ⟶ product L L := nativeAffineSection R L 1
  change pullLineCoordinate R (s ≫ affineLineContractionAtOne R) = _
  have hf : s ≫ productFst L L = 𝟙 L := productLift_fst _ _
  have hs : s ≫ productSnd L L =
      toBase L ≫ affineLineParameterPoint R 1 :=
    productLift_snd _ _
  rw [affineLineContractionAtOne_coordinate R s, hf, hs,
    pullLineCoordinate_comp R (toBase L) (affineLineParameterPoint R 1),
    affineLineParameterPoint_coordinate]
  let p : (L).left ⟶ S := (toBase L).left
  let b := pullLineCoordinate R (toBase L ≫ affineLineOne R)
  let x := pullLineCoordinate R (𝟙 L)
  change b + p.appTop ((Scheme.ΓSpecIso R).inv (1 : R)) * (x - b) = x
  rw [map_one, map_one, one_mul, ← add_sub_assoc, add_comm b x, add_sub_cancel_right]

end AlgebraicGeometry.MotivicHomotopy
