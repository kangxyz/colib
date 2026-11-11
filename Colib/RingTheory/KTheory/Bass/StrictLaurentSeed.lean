/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.CategoryTheory.Functor.IdentityAutomorphismEvaluation
public import Colib.CategoryTheory.Functor.IdentityAutomorphismSquare
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIsoNaturality
public import Colib.Topology.Prespectrum.StrictSquareNull
public import Colib.Topology.Prespectrum.NullLoopNaturality
public import Colib.KTheory.Bass.StrictDiagramHomotopy

/-!
# Bass seeds from original coefficient-natural Laurent actions

One construction retains the original four-corner square, source-leg null cylinder and
prescribed scalar/null concatenation. Identity actions on a Model diagram supply the Laurent
track. A map preserving that track preserves the entire seed, with no replacement of its null.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.LaurentSeed
variable {R : CommRingCat.{u}}

/-- The original four corners obtained by applying the supplied coefficient diagram. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:35"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def square (F : Under R ⥤ LoopPrespectrum.{w}) (a : Under R) :
    Arrow (Arrow LoopPrespectrum.{w}) := F.mapArrow.mapArrow.obj (laurentUnderSquare R a)

/-- The original strict-square mapping cone. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:39"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def cone (F : Under R ⥤ LoopPrespectrum.{w}) (a : Under R) : LoopPrespectrum.{w} :=
  mappingCone (StrictSquare.comparison (square F a))

/-- The original positive source leg has the unchanged Laurent coefficient composite. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:43"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem square_source (F : Under R ⥤ LoopPrespectrum.{w}) (a : Under R) :
    (square F a).left.hom ≫ (square F a).hom.right =
      F.map ((laurentUnderCoefficient R).app a) := by
  change F.map ((polynomialUnderCoefficient R).app a) ≫
    F.map ((underToLaurent R).app a) = _
  rw [← Functor.map_comp, polynomialUnderCoefficient_toLaurent]

/-- The inverse-coordinate source leg retains the same Laurent coefficient composite. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:51"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem square_source_inverse (F : Under R ⥤ LoopPrespectrum.{w}) (a : Under R) :
    (square F a).hom.left ≫ (square F a).right.hom =
      F.map ((laurentUnderCoefficient R).app a) := by
  change F.map ((polynomialUnderCoefficient R).app a) ≫
    F.map ((underToLaurentInvert R).app a) = _
  rw [← Functor.map_comp, polynomialUnderCoefficient_toLaurentInvert]

/-- The unchanged source-leg cone cylinder, with only its displayed endpoint cast. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:59"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def sourceNull (F : Under R ⥤ LoopPrespectrum.{w}) (a : Under R) :
    Homotopy (F.map ((laurentUnderCoefficient R).app a) ≫
      mappingConeInclusion (StrictSquare.comparison (square F a)))
      (zeroHom (F.obj a) (cone F a)) :=
  (StrictSquare.sourceNullHomotopy (square F a)).cast (by rw [square_source]; rfl) rfl

/-- A whole Laurent track, natural at the same time under every actual coefficient map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:66"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
structure Track (F : Under R ⥤ LoopPrespectrum.{w}) where
  /-- The original whole Laurent self-track at this coefficient. -/
  homotopy (a : Under R) : Homotopy (F.map ((laurentUnderCoefficient R).app a))
    (F.map ((laurentUnderCoefficient R).app a))
  /-- Coefficient changes preserve the same original track time. -/
  naturality {a b : Under R} (g : a ⟶ b) (n : ℕ) (t : unitInterval) (x : (F.obj a).space n) :
    (F.map ((laurentUnderFunctor R).map g)).map n ((homotopy a).level n (t, x)) =
      (homotopy b).level n (t, (F.map g).map n x)

/-- A forward identity action on the original Laurent Model at every coefficient. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:76"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
structure ModelAction (C : Under R ⥤ WideSubcategory preservesZero.{w}) where
  /-- The prescribed forward unit on the original Laurent coefficient Model. -/
  unit (a : Under R) : 𝟭 (C.obj ((laurentUnderFunctor R).obj a)).obj.Obj ≅
    𝟭 (C.obj ((laurentUnderFunctor R).obj a)).obj.Obj
  /-- The unchanged Laurent coefficient functors preserve this same unit. -/
  naturality {a b : Under R} (g : a ⟶ b) :
    Preserves (C.map ((laurentUnderFunctor R).map g)).hom.toFunctor (unit a) (unit b)

/-- Realization of those original identity actions supplies the entire natural Laurent track. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:85"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def ModelAction.track {C : Under R ⥤ WideSubcategory preservesZero.{w}} (A : ModelAction C) :
    Track (C ⋙ prespectrumFunctor) where
  homotopy a := prespectrumIsoHomotopy (C.map ((laurentUnderCoefficient R).app a))
    (onFunctor (C.map ((laurentUnderCoefficient R).app a)).hom.toFunctor (A.unit a))
  naturality {a b} g n t x := by
    have h : C.map ((laurentUnderCoefficient R).app a) ≫
        C.map ((laurentUnderFunctor R).map g) =
        C.map g ≫ C.map ((laurentUnderCoefficient R).app b) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg C.map ((laurentUnderCoefficient R).naturality g).symm
    exact prespectrumIsoHomotopy_square_apply _ _ _ _ _ _ h
      (onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg (fun k ↦ k.hom.toFunctor) h))
        (A.unit a) (A.unit b) (A.naturality g).whisker) n t x

/-- Realization preserves the same scalar track under an action-preserving Model transformation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:100"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem ModelAction.track_square {C D : Under R ⥤ WideSubcategory preservesZero.{w}}
    (A : ModelAction C) (B : ModelAction D) (r : C ⟶ D)
    (h : ∀ a, Preserves (r.app ((laurentUnderFunctor R).obj a)).hom.toFunctor (A.unit a) (B.unit a))
    (a : Under R) (n : ℕ) (t : unitInterval) (x : (prespectrum (C.obj a)).space n) :
    (prespectrumMap (r.app ((laurentUnderFunctor R).obj a))).map n
        ((A.track.homotopy a).level n (t, x)) =
      (B.track.homotopy a).level n (t, (prespectrumMap (r.app a)).map n x) :=
  prespectrumIsoHomotopy_square_apply _ _ _ _ _ _ (r.naturality _)
    (onFunctor_whisker_square _ _ _ _
      (eqToHom (congrArg (fun k ↦ k.hom.toFunctor) (r.naturality ((laurentUnderCoefficient R).app
        a))))
      (A.unit a) (B.unit a) (h a).whisker) n t x

/-- The original scalar action conjugated by the original source-leg cone null. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:113"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def Track.seedMap {F : Under R ⥤ LoopPrespectrum.{w}} (A : Track F) (a : Under R) :
    F.obj a ⟶ parameterLooping (cone F a) :=
  ((A.homotopy a).postcomp
    (mappingConeInclusion (StrictSquare.comparison (square F a)))).nullLoopMap (sourceNull F a)

/-- Original coefficient maps induce the same four-corner cone maps. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:119"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def coefficientConeMap (F : Under R ⥤ LoopPrespectrum.{w}) {a b : Under R} (g : a ⟶ b) :
    cone F a ⟶ cone F b :=
  mappingConeMap (strictSquareComparisonFunctor.map
    (F.mapArrow.mapArrow.map (laurentUnderSquareMap R g)))

/-- The source-leg null keeps its original cylinder coordinate under coefficient change. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:125"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem sourceNull_coefficient (F : Under R ⥤ LoopPrespectrum.{w}) {a b : Under R}
    (g : a ⟶ b) (n : ℕ) (t : unitInterval) (x : (F.obj a).space n) :
    (coefficientConeMap F g).map n ((sourceNull F a).level n (t, x)) =
      (sourceNull F b).level n (t, (F.map g).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply
    (F.mapArrow.mapArrow.map (laurentUnderSquareMap R g)) n t x

/-- The prescribed concatenated seed is coefficient-natural. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:133"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem Track.seedMap_naturality {F : Under R ⥤ LoopPrespectrum.{w}} (A : Track F)
    {a b : Under R} (g : a ⟶ b) :
    A.seedMap a ≫ parameterLoopingMap (coefficientConeMap F g) = F.map g ≫ A.seedMap b := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion (StrictSquare.comparison (square F b))).map n
      ((F.map ((laurentUnderFunctor R).map g)).map n ((A.homotopy a).level n (t, x))) =
      (mappingConeInclusion (StrictSquare.comparison (square F b))).map n
        ((A.homotopy b).level n (t, (F.map g).map n x))
    rw [A.naturality]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact sourceNull_coefficient F g n t x

/-- The actual natural Bass seed into the existing strict Bass endofunctor. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:151"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def Track.seed {F : Under R ⥤ LoopPrespectrum.{w}} (A : Track F) :
    F ⟶ (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj F where
  app := A.seedMap
  naturality _ _ g := (A.seedMap_naturality g).symm

/-- The seed value keeps its original scalar/null concatenation at every loop coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:157"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem Track.seedMap_apply {F : Under R ⥤ LoopPrespectrum.{w}} (A : Track F)
    (a : Under R) (n : ℕ) (x : (F.obj a).space n) (t : unitInterval) :
    Path.toContinuousMap ((A.seedMap a).map n x) t =
      (((A.homotopy a).postcomp (mappingConeInclusion (StrictSquare.comparison (square F a))))
        |>.conjugateToZero (sourceNull F a)).level n (t, x) := rfl

/-- Original four-corner maps induced by a transformation act on the same cones. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:164"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def transformationConeMap {F G : Under R ⥤ LoopPrespectrum.{w}} (η : F ⟶ G) (a : Under R) :
    cone F a ⟶ cone G a :=
  mappingConeMap (strictSquareComparisonFunctor.map (diagramSquareMap η (laurentUnderSquare R a)))

/-- Transformation naturality preserves the original source-leg cylinder at its identical time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:169"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem sourceNull_transformation {F G : Under R ⥤ LoopPrespectrum.{w}} (η : F ⟶ G)
    (a : Under R) (n : ℕ) (t : unitInterval) (x : (F.obj a).space n) :
    (transformationConeMap η a).map n ((sourceNull F a).level n (t, x)) =
      (sourceNull G a).level n (t, (η.app a).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply
    (diagramSquareMap η (laurentUnderSquare R a)) n t x

/-- The unchanged Bass seed square follows from equality of the whole Laurent tracks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictLaurentSeed.lean:177"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem Track.seed_square {F G : Under R ⥤ LoopPrespectrum.{w}}
    (A : Track F) (B : Track G) (η : F ⟶ G)
    (h : ∀ (a : Under R) (n : ℕ) (t : unitInterval) (x : (F.obj a).space n),
      (η.app ((laurentUnderFunctor R).obj a)).map n ((A.homotopy a).level n (t, x)) =
        (B.homotopy a).level n (t, (η.app a).map n x)) :
    A.seed ≫ (strictDiagramFunctor (laurentUnderSquareFunctor R)).map η = η ≫ B.seed := by
  apply NatTrans.ext
  funext a
  change A.seedMap a ≫ parameterLoopingMap (transformationConeMap η a) = η.app a ≫ B.seedMap a
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion (StrictSquare.comparison (square G a))).map n
        ((η.app ((laurentUnderFunctor R).obj a)).map n ((A.homotopy a).level n (t, x))) =
      (mappingConeInclusion (StrictSquare.comparison (square G a))).map n
        ((B.homotopy a).level n (t, (η.app a).map n x))
    rw [h]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact sourceNull_transformation η a n t x

end KTheory.Bass.LaurentSeed

