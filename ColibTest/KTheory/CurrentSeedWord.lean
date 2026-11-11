/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.KTheory.Bass.WholeSeedWord

noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open KTheory.Bass.PushoutCofiberSquare KTheory.Bass.SquareConeStrength
open KTheory.Bass.HomotopyWord
open scoped Topology unitInterval
universe u v w

namespace Topology.LoopPrespectrum
section
variable {C : Type u} [Category.{v} C]
variable {F G K : C ⥤ LoopPrespectrum.{w}} (a : F ⟶ G)

example : C ⥤ LoopPrespectrum.{w} :=
  mappingConeDiagram a

end
end Topology.LoopPrespectrum

namespace KTheory.Bass.SquareConeStrength
section
variable {C : Type u} [Category.{v} C]
variable (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w})))

example (X : C) :
    Homotopy (((S.left.hom ≫ S.hom.right) ≫ coneInclusion (comparison S)).app X)
      ((diagramZeroMap S.left.left (mappingConeDiagram (comparison S))).app X) :=
  sourceNull S X

end
end KTheory.Bass.SquareConeStrength

namespace KTheory.Bass.HomotopyWord
section
variable {C : Type u} [Category.{v} C]
variable {F G : C ⥤ LoopPrespectrum.{w}} {a b c : F ⟶ G}

example (H : ∀ X, Homotopy (a.app X) (b.app X)) (hH : Natural H) :
    Natural (fun X => (H X).symm) :=
  natural_symm H hH

example (H : ∀ X, Homotopy (a.app X) (b.app X))
    (K : ∀ X, Homotopy (b.app X) (c.app X)) (hH : Natural H) (hK : Natural K) :
    Natural (fun X => (H X).trans (K X)) :=
  natural_trans H K hH hK

end
end KTheory.Bass.HomotopyWord

namespace KTheory.Bass.WholeSeedCospan
section
variable {C : Type u} [Category.{v} C]
variable (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w})))
  (A : ∀ X, Homotopy ((S.left.hom ≫ S.hom.right).app X)
    ((S.left.hom ≫ S.hom.right).app X)) (hA : Natural A)

example : Natural (coneAction S A) :=
  coneAction_naturality S A hA

example : S.left.left ⟶ mappingConeDiagram (comparison S) ⋙ parameterLoopingFunctor :=
  seed S A hA

end
end KTheory.Bass.WholeSeedCospan
