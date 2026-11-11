/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricSquareInterchange
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricSourceTrack
public import Colib.Topology.Prespectrum.LoopTranspose
public import Colib.KTheory.Bass.WholeSeedCospan
public import Colib.KTheory.Bass.ConeTrackUnitSquare

/-!
# The actual finite geometric seed cospan

A genuine natural Laurent projection track induces its current-stage action
on the original cone and parameter loops. The original index interchange
cancels its actual inverse, so the whole-unit square is proved rather than
assumed. The common-target seed equality retains the original null word and
loop strength. This is one finite comparison, not an all-stage tower map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace KTheory.Bass.GeometricSeedCospan
open GeometricSquareInterchange WholeSeedCospan
open SquareConeStrength HomotopyWord


variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (H : ∀ X, Homotopy (F.map (coefficient.app X)) (F.map (coefficient.app X)))
    (hH : ∀ {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
      (x : (F.obj X).space n),
      (F.map (laurent.op.map g)).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map g).map n x))

/-- Endpoint casts disappear already on the original natural time-slice transformation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricSeedCospan.lean:60"
  "adaptation" "Original actual geometric seed cospan and whole unit square."]
theorem sourceTrack_timeSlice (r : unitInterval) :
    diagramHomotopyAt (sourceTrack F H) (sourceTrack_naturality F H hH) r =
      diagramHomotopyAt (η := Functor.whiskerRight coefficient F)
        (θ := Functor.whiskerRight coefficient F) H hH r := by
  apply NatTrans.ext
  funext X
  apply Hom.ext
  funext n
  ext x
  rfl

/-- The actual induced cone action, followed by the original parameter looping. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricSeedCospan.lean:72"
  "adaptation" "Original actual geometric seed cospan and whole unit square."]
def bassTrack (X : Scheme.{u}ᵒᵖ) :
    Homotopy (((geometricSquare ((strictDiagramFunctor squareFunctor).obj F)).left.hom ≫
      (geometricSquare ((strictDiagramFunctor squareFunctor).obj F)).hom.right).app X)
      (((geometricSquare ((strictDiagramFunctor squareFunctor).obj F)).left.hom ≫
      (geometricSquare ((strictDiagramFunctor squareFunctor).obj F)).hom.right).app X) :=
  (ConeTrack.action squareFunctor laurent.op coefficient
    (interchange (laurentProjection (.of (ULift.{u} ℤ))))
    (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ))))
    F H hH X).parameterLooping.cast
      (congrArg (fun a => a.app X)
        (geometricSquare_diagonal ((strictDiagramFunctor squareFunctor).obj F))).symm
      (congrArg (fun a => a.app X)
        (geometricSquare_diagonal ((strictDiagramFunctor squareFunctor).obj F))).symm

/-- The induced whole track is natural in every actual scheme map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricSeedCospan.lean:87"
  "adaptation" "Original actual geometric seed cospan and whole unit square."]
theorem bassTrack_naturality : Natural (bassTrack F H hH) := by
  intro X Y g n r γ
  change Path (((ConeTrack.diagram squareFunctor F).obj X).point n)
    (((ConeTrack.diagram squareFunctor F).obj X).point n) at γ
  apply Path.ext
  funext t
  exact ConeTrack.action_naturality squareFunctor laurent.op coefficient
    (interchange (laurentProjection (.of (ULift.{u} ℤ))))
    (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ))))
    F H hH g n r (γ t)

/-- The actual forward eta cancels the specified inverse in the induced whole action. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricSeedCospan.lean:99"
  "adaptation" "Original actual geometric seed cospan and whole unit square."]
theorem wholeUnitSquare (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    (bassTrack F H hH X).at r ≫
        (eta (laurentProjection (.of (ULift.{u} ℤ))) F).hom.app X =
      (strictDiagramMapHomotopy (sourceTrack F H) (sourceTrack_naturality F H hH)
        squareFunctor X).at r := by
  have h := ConeTrack.looped_action_index squareFunctor laurent.op coefficient
    (interchange (laurentProjection (.of (ULift.{u} ℤ))))
    (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ)))) F H hH X r
  have hb : (strictDiagramMapHomotopy (sourceTrack F H)
      (sourceTrack_naturality F H hH) squareFunctor X).at r =
      (strictDiagramMapHomotopy (η := Functor.whiskerRight coefficient F)
        (θ := Functor.whiskerRight coefficient F) H hH squareFunctor X).at r := by
    rw [strictDiagramMapHomotopy_at, strictDiagramMapHomotopy_at, sourceTrack_timeSlice]
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact (congrArg (fun a => a.map n x) h).trans
    (congrArg (fun a => a.map n x) hb.symm)

/-- The actual geometric cone comparison to the common positive-direction target. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricSeedCospan.lean:120"
  "adaptation" "Original actual geometric seed cospan and whole unit square."]
def chiGeom :
    mappingConeDiagram (comparison (geometricSquare ((strictDiagramFunctor squareFunctor).obj F))) ⟶
      (strictDiagramFunctor squareFunctor).obj
        (mappingConeDiagram (comparison (geometricSquare F))) :=
  chiAlong (geometricSquare F) squareFunctor (squareInterchangeMap F)

/-- Every original source-null time is retained by the actual geometric comparison. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricSeedCospan.lean:127"
  "adaptation" "Original actual geometric seed cospan and whole unit square."]
theorem chiGeom_sourceNull (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramFunctor squareFunctor).obj F).obj X).space n) :
    ((chiGeom F).app X).map n
        ((sourceNull (geometricSquare ((strictDiagramFunctor squareFunctor).obj F)) X).level n
          (r,x)) =
      (strictDiagramMapHomotopy (sourceNull (geometricSquare F))
        (sourceNull_naturality (geometricSquare F)) squareFunctor X).level n (r,x) := by
  have h := chiAlong_sourceNull (geometricSquare F) squareFunctor
    (squareInterchangeMap F) X n r x
  rw [squareInterchange_base] at h
  exact h

/-- The whole finite seed cospan for the actual induced action, with no unit-square input. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricSeedCospan.lean:140"
  "adaptation" "Original actual geometric seed cospan and whole unit square."]
theorem seed_cospan (X : Scheme.{u}ᵒᵖ) :
    (WholeSeedCospan.seed
      (geometricSquare ((strictDiagramFunctor squareFunctor).obj F))
      (bassTrack F H hH) (bassTrack_naturality F H hH)).app X ≫
        parameterLoopingMap ((chiGeom F).app X) =
      (((strictDiagramFunctor squareFunctor).map
        (WholeSeedCospan.seed (geometricSquare F) (sourceTrack F H)
          (sourceTrack_naturality F H hH))).app X) ≫
        LoopStrength.strength squareFunctor
          (mappingConeDiagram (comparison (geometricSquare F))) X := by
  have hu : ∀ Y r, (bassTrack F H hH Y).at r ≫
      (squareInterchangeMap F).right.right.app Y =
      (squareInterchangeMap F).left.left.app Y ≫
        (strictDiagramMapHomotopy (sourceTrack F H) (sourceTrack_naturality F H hH)
          squareFunctor Y).at r := by
    intro Y r
    rw [squareInterchange_base, squareInterchange_laurent, NatTrans.id_app]
    exact (wholeUnitSquare F H hH Y r).trans (Category.id_comp _).symm
  have hs := WholeSeedCospan.seed_cospan (geometricSquare F)
    (sourceTrack F H) (sourceTrack_naturality F H hH) squareFunctor
    (squareInterchangeMap F) (bassTrack F H hH) (bassTrack_naturality F H hH) hu X
  rw [squareInterchange_base, NatTrans.id_app] at hs
  exact hs.trans (Category.id_comp _)

end KTheory.Bass.GeometricSeedCospan
