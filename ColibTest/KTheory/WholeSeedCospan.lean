module
import Colib.KTheory.Bass.WholeSeedCospan
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass.WholeSeedCospan
open PushoutCofiberSquare SquareConeStrength HomotopyWord
variable {C : Type u} [Category.{v} C]

example {S T : Arrow (Arrow (C ⥤ LoopPrespectrum.{w}))}
    (e : S ⟶ T) (X : C) :
    mappingConeInclusion ((comparison S).app X) ≫ (squareConeMap e).app X =
      e.right.right.app X ≫ mappingConeInclusion ((comparison T).app X) :=
  squareConeMap_inclusion e X

variable (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w})))
  (A : ∀ X, Homotopy ((S.left.hom ≫ S.hom.right).app X)
    ((S.left.hom ≫ S.hom.right).app X)) (hA : Natural A)


variable (Q : C ⥤ Arrow (Arrow C))
  {T : Arrow (Arrow (C ⥤ LoopPrespectrum.{w}))} (e : T ⟶ bassSquare S Q)

example (X : C) :
    mappingConeInclusion ((comparison T).app X) ≫ (chiAlong S Q e).app X =
      e.right.right.app X ≫
        (((strictDiagramFunctor Q).map (coneInclusion (comparison S))).app X) :=
  chiAlong_inclusion S Q e X

example (X : C) (n : ℕ) (r : unitInterval)
    (x : (T.left.left.obj X).space n) :
    ((chiAlong S Q e).app X).map n ((sourceNull T X).level n (r,x)) =
      (strictDiagramMapHomotopy (sourceNull S) (sourceNull_naturality S) Q X).level n
        (r, (e.left.left.app X).map n x) :=
  chiAlong_sourceNull S Q e X n r x

variable (A' : ∀ X, Homotopy ((T.left.hom ≫ T.hom.right).app X)
    ((T.left.hom ≫ T.hom.right).app X)) (hA' : Natural A')
  (hunit : ∀ X r,
    (A' X).at r ≫ e.right.right.app X =
      e.left.left.app X ≫ (strictDiagramMapHomotopy A hA Q X).at r)

example (X : C) (n : ℕ) :
    ((word T A' X).postcomp ((chiAlong S Q e).app X)).level n =
      ((strictDiagramMapHomotopy (word S A) (word_naturality S A hA) Q X).precomp
        (e.left.left.app X)).level n :=
  chiAlong_word S A hA Q e A' hunit X n

example (X : C) :
    (seed T A' hA').app X ≫ parameterLoopingMap ((chiAlong S Q e).app X) =
      e.left.left.app X ≫ (((strictDiagramFunctor Q).map (seed S A hA)).app X) ≫
        LoopStrength.strength Q (mappingConeDiagram (comparison S)) X :=
  seed_cospan S A hA Q e A' hA' hunit X

end KTheory.Bass.WholeSeedCospan
