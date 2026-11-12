/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleLimit

/-! # The original boundary over the actual etale-neighborhood curve diagram

The boundary and curve diagrams use the same neighborhoods and the same strict
henselization cone. All maps below are literal native pullback lifts.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The literal base change of an original boundary inclusion, in the ordering
used by the existing curve diagrams. No immersion assumption is needed. -/
def etaleBoundaryBaseChangeMap {T A N Z : Scheme.{u}}
    (a : A ⟶ T) (p : N ⟶ T) (i : Z ⟶ N) :
    pullback a (i ≫ p) ⟶ pullback a p :=
  pullback.lift (pullback.fst a (i ≫ p)) (pullback.snd a (i ≫ p) ≫ i)
    (by rw [Category.assoc, pullback.condition])

@[simp, reassoc] theorem etaleBoundaryBaseChangeMap_fst {T A N Z : Scheme.{u}}
    (a : A ⟶ T) (p : N ⟶ T) (i : Z ⟶ N) :
    etaleBoundaryBaseChangeMap a p i ≫ pullback.fst a p = pullback.fst a (i ≫ p) :=
  pullback.lift_fst _ _ _

@[simp, reassoc] theorem etaleBoundaryBaseChangeMap_snd {T A N Z : Scheme.{u}}
    (a : A ⟶ T) (p : N ⟶ T) (i : Z ⟶ N) :
    etaleBoundaryBaseChangeMap a p i ≫ pullback.snd a p =
      pullback.snd a (i ≫ p) ≫ i :=
  pullback.lift_snd _ _ _

/-- This exact lift, not an unspecified isomorphic map, is Cartesian over the
original boundary map. -/
theorem etaleBoundaryBaseChangeMap_isPullback {T A N Z : Scheme.{u}}
    (a : A ⟶ T) (p : N ⟶ T) (i : Z ⟶ N) :
    IsPullback (etaleBoundaryBaseChangeMap a p i) (pullback.snd a (i ≫ p))
      (pullback.snd a p) i := by
  refine IsPullback.of_right ?_ (etaleBoundaryBaseChangeMap_snd a p i)
    (IsPullback.of_hasPullback a p)
  rw [etaleBoundaryBaseChangeMap_fst]
  exact IsPullback.of_hasPullback a (i ≫ p)

instance etaleBoundaryBaseChangeMap_isClosedImmersion {T A N Z : Scheme.{u}}
    (a : A ⟶ T) (p : N ⟶ T) (i : Z ⟶ N) [IsClosedImmersion i] :
    IsClosedImmersion (etaleBoundaryBaseChangeMap a p i) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (etaleBoundaryBaseChangeMap_isPullback a p i).flip inferInstance

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N Z : Scheme.{u}} (p : N ⟶ X.left) (i : Z ⟶ N)

/-- The boundary-to-curve map on the actual original neighborhood diagrams. -/
def etaleBoundaryDiagramMap : etaleCurveDiagram X s (i ≫ p) ⟶ etaleCurveDiagram X s p where
  app a := etaleBoundaryBaseChangeMap ((smallEtaleNeighborhoodOver X s).obj a).hom p i
  naturality a b v := by
    change pullback.lift _ _ _ ≫ etaleBoundaryBaseChangeMap _ p i =
      etaleBoundaryBaseChangeMap _ p i ≫ pullback.lift _ _ _
    apply pullback.hom_ext
    · simp only [etaleBoundaryBaseChangeMap, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc]
    · simp only [etaleBoundaryBaseChangeMap, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc]

/-- Every actual stage boundary map is the base change of the original map. -/
theorem etaleBoundaryDiagramMap_isPullback (a : SmallEtaleNeighborhood X s) :
    IsPullback ((etaleBoundaryDiagramMap X s p i).app a)
      (pullback.snd ((smallEtaleNeighborhoodOver X s).obj a).hom (i ≫ p))
      (pullback.snd ((smallEtaleNeighborhoodOver X s).obj a).hom p) i :=
  etaleBoundaryBaseChangeMap_isPullback _ p i

instance etaleBoundaryDiagramMap_isClosedImmersion [IsClosedImmersion i]
    (a : SmallEtaleNeighborhood X s) :
    IsClosedImmersion ((etaleBoundaryDiagramMap X s p i).app a) :=
  inferInstanceAs (IsClosedImmersion (etaleBoundaryBaseChangeMap _ p i))

variable (B : BigEtaleSite.{u}) (hX : B.Contains X.left)

/-- The actual strict-local full-boundary map between the existing cone vertices. -/
def etaleBoundaryLimitMap : (etaleCurveCone X B hX s (i ≫ p)).pt ⟶
    (etaleCurveCone X B hX s p).pt :=
  etaleBoundaryBaseChangeMap (strictHenselizationToBase B X.left hX s) p i

/-- The two original cone legs commute with the boundary map at every stage. -/
theorem etaleBoundaryCone_square (a : SmallEtaleNeighborhood X s) :
    (etaleCurveCone X B hX s (i ≫ p)).π.app a ≫
      (etaleBoundaryDiagramMap X s p i).app a =
    etaleBoundaryLimitMap X s p i B hX ≫ (etaleCurveCone X B hX s p).π.app a := by
  change pullback.lift _ _ _ ≫ etaleBoundaryBaseChangeMap _ p i =
    etaleBoundaryBaseChangeMap _ p i ≫ pullback.lift _ _ _
  apply pullback.hom_ext
  · simp only [etaleBoundaryBaseChangeMap, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc]
  · simp only [etaleBoundaryBaseChangeMap, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc]

/-- The original cone-vertex boundary map is the actual strict-local base change. -/
theorem etaleBoundaryLimitMap_isPullback :
    IsPullback (etaleBoundaryLimitMap X s p i B hX)
      (pullback.snd (strictHenselizationToBase B X.left hX s) (i ≫ p))
      (pullback.snd (strictHenselizationToBase B X.left hX s) p) i :=
  etaleBoundaryBaseChangeMap_isPullback _ p i

instance etaleBoundaryLimitMap_isClosedImmersion [IsClosedImmersion i] :
    IsClosedImmersion (etaleBoundaryLimitMap X s p i B hX) :=
  inferInstanceAs (IsClosedImmersion (etaleBoundaryBaseChangeMap _ p i))

end AlgebraicGeometry.Scheme.SmoothSite
