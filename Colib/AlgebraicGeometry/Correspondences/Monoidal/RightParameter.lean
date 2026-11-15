/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.GraphProduct
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Interchange

/-!
# The finite correspondence functor for a smooth parameter

A smooth parameter acts on a signed finite correspondence by exterior
product with its identity. The product formula for ordinary graphs
identifies its restriction to the smooth site.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

/-- The literal exterior product preserves ordinary graphs. -/
theorem exteriorGraphProduct : ExteriorGraphProduct k :=
  fun f g => exteriorProduct_graph f g

variable [PerfectField k]

/-- Adjoin a smooth parameter on the right of each signed finite correspondence. -/
def rightExteriorParameterFunctor (T : SmoothSite (Spec (.of k))) : Cor k ⥤ Cor k where
  obj X := tensorObj X (Cor.mk T)
  map f := exteriorProduct f (𝟙 (Cor.mk T))
  map_id X := exterior_id exteriorGraphProduct X (Cor.mk T)
  map_comp {X Y Z} f g := by
    have h := exteriorInterchange f (𝟙 (Cor.mk T)) g (𝟙 (Cor.mk T))
    exact (h.trans (congrArg (exteriorProduct (f ≫ g)) (Category.id_comp _))).symm

/-- The fixed-parameter exterior product is additive on the original correspondences. -/
instance rightExteriorParameterFunctor_additive (T : SmoothSite (Spec (.of k))) :
    (rightExteriorParameterFunctor T).Additive where
  map_add {X Y} := exteriorProduct_add_left (X := X) (Y := Y) _ _ (𝟙 (Cor.mk T))

/-- The graph of a parameter morphism acts naturally on all signed correspondences. -/
def rightExteriorParameterMap {T T' : SmoothSite (Spec (.of k))} (f : T ⟶ T') :
    rightExteriorParameterFunctor T ⟶ rightExteriorParameterFunctor T' where
  app X := exteriorProduct (𝟙 X) ((graphFunctor k).map f)
  naturality X Y a := by
    let b := (graphFunctor k).map f
    change exteriorProduct a (𝟙 (Cor.mk T)) ≫ exteriorProduct (𝟙 Y) b =
      exteriorProduct (𝟙 X) b ≫ exteriorProduct a (𝟙 (Cor.mk T'))
    have left : exteriorProduct a (𝟙 (Cor.mk T)) ≫ exteriorProduct (𝟙 Y) b =
        exteriorProduct a b :=
      (exteriorInterchange a (𝟙 (Cor.mk T)) (𝟙 Y) b).trans
        (congrArg₂ (fun c d => exteriorProduct c d) (Category.comp_id a) (Category.id_comp b))
    have right : exteriorProduct (𝟙 X) b ≫ exteriorProduct a (𝟙 (Cor.mk T')) =
        exteriorProduct a b :=
      (exteriorInterchange (𝟙 X) b a (𝟙 (Cor.mk T'))).trans
        (congrArg₂ (fun c d => exteriorProduct c d) (Category.id_comp a) (Category.comp_id b))
    exact left.trans right.symm

/-- At each object the parameter map is the graph of its actual smooth scheme product map. -/
theorem rightExteriorParameterMap_app {T T' : SmoothSite (Spec (.of k))}
    (f : T ⟶ T') (X : Cor k) :
    (rightExteriorParameterMap f).app X =
      (graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite) f) := by
  change exteriorProduct (𝟙 X) ((graphFunctor k).map f) = _
  have hId : (graphFunctor k).map (𝟙 X.toSmoothSite) = 𝟙 X :=
    (graphFunctor k).map_id X.toSmoothSite
  exact (congrArg (fun c => exteriorProduct c ((graphFunctor k).map f)) hId.symm).trans
    (exteriorProduct_graph (𝟙 X.toSmoothSite) f)

/-- On ordinary graphs the fixed-parameter functor is the ordinary scheme product. -/
def graphFunctorCompRightExteriorParameterIso (T : SmoothSite (Spec (.of k))) :
    graphFunctor k ⋙ rightExteriorParameterFunctor T ≅
      SmoothSite.Contraction.parameterProduct T ⋙ graphFunctor k :=
  NatIso.ofComponents (fun X => Iso.refl (Cor.mk (SmoothSite.product X T))) fun {X Y} f => by
    change exteriorProduct ((graphFunctor k).map f) (𝟙 (Cor.mk T)) ≫
        𝟙 (Cor.mk (SmoothSite.product Y T)) =
      𝟙 (Cor.mk (SmoothSite.product X T)) ≫
        (graphFunctor k).map (SmoothSite.productMap f (𝟙 T))
    have hId : (graphFunctor k).map (𝟙 T) = 𝟙 (Cor.mk T) := (graphFunctor k).map_id T
    exact (Category.comp_id _).trans
      ((congrArg (exteriorProduct ((graphFunctor k).map f)) hId.symm).trans
        ((exteriorProduct_graph f (𝟙 T)).trans (Category.id_comp _).symm))

end AlgebraicGeometry.Cor
