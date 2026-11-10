/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.CategoryTheory.Limits.PointedSmash
public import Colib.CategoryTheory.Sites.Simplicial.PointedPresheaf
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Limits.Over

/-!
# Reduced mapping cofibers of strict pointed presheaf maps

The reduced cone is the smash with the simplicial interval pointed at its
last vertex. Attaching that cone along the first vertex defines the strict
pointed mapping-cofiber construction. Its legs and its maps are the native
pushout maps.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C]

/-- The constant simplicial interval presheaf. -/
abbrev interval : Cᵒᵖ ⥤ SSet.{w} :=
  (Functor.const Cᵒᵖ).obj (Δ[1] : SSet.{w})

/-- The global endpoint given by the indicated face of the one-simplex. -/
def intervalEndpoint (i : Fin 2) : (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⟶ interval C where
  app U := SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.stdSimplex.δ i
  naturality U V f := by
    change (⊤_ (Cᵒᵖ ⥤ SSet.{w})).map f ≫ (_ ≫ _) = (_ ≫ _) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc]
    exact congrArg (fun g => g ≫ SSet.stdSimplex.δ i)
      (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

/-- The simplicial interval with vertex one as the specified basepoint. -/
def basedInterval : PointedSimplicialPresheaf.{w} C :=
  Under.mk (intervalEndpoint C (0 : Fin 2))

variable {C}

/-- The reduced cone of a pointed simplicial presheaf. -/
abbrev reducedCone (X : PointedSimplicialPresheaf.{w} C) : PointedSimplicialPresheaf.{w} C :=
  Under.smash X (basedInterval C)

/-- The cone inclusion is the restriction to vertex zero of the interval. -/
def reducedConeInclusion (X : PointedSimplicialPresheaf.{w} C) : X ⟶ reducedCone X :=
  Under.smashRightPoint X (basedInterval C) (intervalEndpoint C (1 : Fin 2))

/-- The map of cones induced by a pointed presheaf map. -/
def reducedConeMap {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y) :
    reducedCone X ⟶ reducedCone Y :=
  Under.smashMap f (𝟙 (basedInterval C))

@[reassoc (attr := simp)]
theorem reducedConeInclusion_naturality {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y) :
    reducedConeInclusion X ≫ reducedConeMap f = f ≫ reducedConeInclusion Y :=
  Under.smashRightPoint_naturality (Y := basedInterval C) f (intervalEndpoint C (1 : Fin 2))

@[simp]
theorem reducedConeMap_id (X : PointedSimplicialPresheaf.{w} C) :
    reducedConeMap (𝟙 X) = 𝟙 (reducedCone X) :=
  Under.smashMap_id _ _

theorem reducedConeMap_comp {X Y Z : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    reducedConeMap (f ≫ g) = reducedConeMap f ≫ reducedConeMap g := by
  simpa only [reducedConeMap, Category.id_comp] using
    (Under.smashMap_comp f g (𝟙 (basedInterval C)) (𝟙 (basedInterval C))).symm

/-- The strict reduced mapping cofiber is the pushout attaching the reduced cone. -/
def reducedMappingCofiber {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y) :
    PointedSimplicialPresheaf.{w} C :=
  pushout f (reducedConeInclusion X)

/-- The map of the target into the reduced mapping cofiber. -/
def toReducedMappingCofiber {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y) :
    Y ⟶ reducedMappingCofiber f :=
  pushout.inl f (reducedConeInclusion X)

/-- The map of the cone into the reduced mapping cofiber. -/
def reducedConeToMappingCofiber {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y) :
    reducedCone X ⟶ reducedMappingCofiber f :=
  pushout.inr f (reducedConeInclusion X)

@[reassoc]
theorem reducedMappingCofiber_condition {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y) :
    f ≫ toReducedMappingCofiber f = reducedConeInclusion X ≫ reducedConeToMappingCofiber f :=
  pushout.condition

/-- The defining mapping-cofiber square is a pointed pushout. -/
theorem reducedMappingCofiber_isPushout {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y) :
    IsPushout f (reducedConeInclusion X) (toReducedMappingCofiber f)
      (reducedConeToMappingCofiber f) :=
  IsPushout.of_hasPushout f (reducedConeInclusion X)

/-- A strict commutative square gives its literal induced map of reduced mapping cofibers. -/
def reducedMappingCofiberMap {f g : Arrow (PointedSimplicialPresheaf.{w} C)} (s : f ⟶ g) :
    reducedMappingCofiber f.hom ⟶ reducedMappingCofiber g.hom :=
  pushout.map f.hom (reducedConeInclusion f.left) g.hom (reducedConeInclusion g.left)
    s.right (reducedConeMap s.left) s.left (Arrow.w s).symm
    (reducedConeInclusion_naturality s.left)

@[reassoc (attr := simp)]
theorem toReducedMappingCofiber_map {f g : Arrow (PointedSimplicialPresheaf.{w} C)} (s : f ⟶ g) :
    toReducedMappingCofiber f.hom ≫ reducedMappingCofiberMap s =
      s.right ≫ toReducedMappingCofiber g.hom := by
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem reducedConeToMappingCofiber_map {f g : Arrow (PointedSimplicialPresheaf.{w} C)}
    (s : f ⟶ g) :
    reducedConeToMappingCofiber f.hom ≫ reducedMappingCofiberMap s =
      reducedConeMap s.left ≫ reducedConeToMappingCofiber g.hom := by
  exact pushout.inr_desc _ _ _

end CategoryTheory.PointedSimplicialPresheaf

attribute [colib_tag "COL-0385"]
  CategoryTheory.PointedSimplicialPresheaf.reducedMappingCofiber
  CategoryTheory.PointedSimplicialPresheaf.reducedMappingCofiber_isPushout
attribute [colib_ref "Voevodsky2003ModTwo" "Section 7, proof of Proposition 7.1, p. 95" "ingredient"
  "Strict pointed cone construction for the augmented Cech object"]
  CategoryTheory.PointedSimplicialPresheaf.reducedMappingCofiber
