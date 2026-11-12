/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

/-! # Actual maps on the retained image open

The image of an open under an open immersion is not identified definitionally
with the original open. Its target and coordinate maps are transported using
the inverse of the native image isomorphism, with literal recovery equations.
-/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme

/-- The actual inverse from the retained image open to the original open. -/
def retainedImageToOpen {U N : Scheme.{u}} (i : U ⟶ N) [IsOpenImmersion i]
    (W : U.Opens) : (i ''ᵁ W).toScheme ⟶ W.toScheme :=
  (i.isoImage W).inv

/-- The inverse recovers the literal inclusion of the image open. -/
@[reassoc]
theorem retainedImageToOpen_ι {U N : Scheme.{u}} (i : U ⟶ N) [IsOpenImmersion i]
    (W : U.Opens) : retainedImageToOpen i W ≫ W.ι ≫ i = (i ''ᵁ W).ι :=
  i.isoImage_inv_ι W

/-- Transport a target or coordinate map to the actual image open. -/
def retainedImageMap {U N T : Scheme.{u}} (i : U ⟶ N) [IsOpenImmersion i]
    (W : U.Opens) (t : U ⟶ T) : (i ''ᵁ W).toScheme ⟶ T :=
  retainedImageToOpen i W ≫ W.ι ≫ t

/-- Pulling the transported map back by the native image isomorphism gives
exactly the original map restricted to the original open. -/
@[reassoc]
theorem isoImage_hom_retainedImageMap {U N T : Scheme.{u}}
    (i : U ⟶ N) [IsOpenImmersion i] (W : U.Opens) (t : U ⟶ T) :
    (i.isoImage W).hom ≫ retainedImageMap i W t = W.ι ≫ t := by
  simp only [retainedImageMap, retainedImageToOpen, Iso.hom_inv_id_assoc]

/-- The transported target map preserves the original structure morphism. -/
theorem retainedImageMap_structure {U N T S : Scheme.{u}}
    (i : U ⟶ N) [IsOpenImmersion i] (W : U.Opens)
    (t : U ⟶ T) (tS : T ⟶ S) (p : N ⟶ S) (ht : t ≫ tS = i ≫ p) :
    retainedImageMap i W t ≫ tS = (i ''ᵁ W).ι ≫ p := by
  dsimp only [retainedImageMap]
  rw [Category.assoc, Category.assoc, ht]
  rw [← Category.assoc W.ι i p, ← Category.assoc,
    retainedImageToOpen_ι]

/-- The actual coordinate on the image open retains the original finite-chart
factorization, with no identification of the two open subscheme objects. -/
theorem retainedImageMap_coordinate {U N C Y : Scheme.{u}}
    (i : U ⟶ N) [IsOpenImmersion i] (W : U.Opens)
    (c : U ⟶ C) (π : N ⟶ Y) (xChart : C ⟶ Y)
    (hc : i ≫ π = c ≫ xChart) :
    (i ''ᵁ W).ι ≫ π = retainedImageMap i W c ≫ xChart :=
  (retainedImageMap_structure i W c xChart π hc.symm).symm

end AlgebraicGeometry.Scheme
