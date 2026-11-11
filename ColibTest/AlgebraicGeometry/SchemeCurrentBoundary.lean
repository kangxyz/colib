/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowCurrentBoundary

noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Functor.IdentityAutomorphism
open Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open KTheory.Bass.NaturalTrack KTheory.Bass.GeometricSquareInterchange
open KTheory.Bass.GeometricSeedCospan KTheory.Bass.HomotopyWord
open KTheory.Bass.ModelDiagramRowInterchange
open scoped Topology unitInterval
universe u v w

namespace KTheory.Bass.GeometricSeedCospan
section
variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (H : ∀ X, Homotopy (F.map (coefficient.app X)) (F.map (coefficient.app X)))
    (hH : ∀ {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
      (x : (F.obj X).space n),
      (F.map (laurent.op.map g)).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map g).map n x))

example : Natural (sourceTrack F H) :=
  sourceTrack_naturality F H hH

end
end KTheory.Bass.GeometricSeedCospan

namespace KTheory.Bass.SchemeNaturalSeed
section
variable {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

example (A : Track laurent.op coefficient F) :
    F ⟶ (strictDiagramFunctor squareFunctor).obj F :=
  seed A

end
end KTheory.Bass.SchemeNaturalSeed

namespace KTheory.Bass.SchemeNaturalSeed
section
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

example (A : Track laurent.op coefficient F) (i : ℕ) :
    Track laurent.op coefficient ((strictDiagramIterate squareFunctor i).obj F) :=
  stageTrack A i

example (A : Track laurent.op coefficient F) (i : ℕ) :
    (strictDiagramIterate squareFunctor i).obj F ⟶
      (strictDiagramIterate squareFunctor (i + 1)).obj F :=
  currentTransition A i

end
end KTheory.Bass.SchemeNaturalSeed

namespace KTheory.Bass.SchemeModelRowSeed
section
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M.obj (laurent.op.obj X)).obj.Obj)
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).hom.toFunctor (unit X) (unit Y))

example (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    forward M unit hunit i X =
      (SchemeNaturalSeed.currentTransition
        (ofModelUnits laurent.op coefficient M unit hunit) i).app X ≫
        ModelRowZigzagSequentialization.backward squareFunctor M X i :=
  forward_eq_current M unit hunit i X

end
end KTheory.Bass.SchemeModelRowSeed

namespace KTheory.Bass.SchemeModelRowSeed
section
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M.obj (laurent.op.obj X)).obj.Obj)
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).hom.toFunctor (unit X) (unit Y))

example (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    Homotopy (normalizedBoundary M unit hunit i X)
      ((SchemeNaturalSeed.currentTransition
        (ofModelUnits laurent.op coefficient M unit hunit) i).app X ≫
        ModelRowZigzagSequentialization.backward squareFunctor M X i) :=
  normalizedBoundaryCurrentHomotopy M unit hunit i X

end
end KTheory.Bass.SchemeModelRowSeed
