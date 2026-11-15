/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.SmoothParameterEndpoints

/-! # The original product cones for a smooth parameter -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k

/-- The canonical abelian structure on sheaves with transfers. -/
local instance smoothParameterCochainAbelian : Abelian NST := SheafWithTransfers.abelian k
set_option quotPrecheck false in
local notation "a" => nisnevichSheafify k
local notation "c" => ComplexShape.up ℤ
set_option quotPrecheck false in
local notation "s" => CochainComplex.singleFunctor NST 0

variable {T : SmoothSite (Spec (CommRingCat.of k))} {F : Cor k ⥤ Cor k} [F.Additive]
  (e : Cor.graphFunctor k ⋙ F ≅ parameterProduct T ⋙ Cor.graphFunctor k)

set_option quotPrecheck false in
local notation "H" => coendPushforward F
set_option quotPrecheck false in
local notation "J" => (H ⋙ a)
set_option quotPrecheck false in
local notation "G" => parameterProduct T

/-- The original projective graph arrow used in the parameter cone. -/
abbrev smoothParameterSourceArrow (j : Arrow Sm) : Arrow (CochainComplex PST ℤ) :=
  Arrow.mk ((projectivePairArrow k).app j)

/-- The square of original projective graphs induced by a pair map. -/
abbrev smoothParameterSourceArrowMap {i j : Arrow Sm} (φ : i ⟶ j) :
    smoothParameterSourceArrow i ⟶ smoothParameterSourceArrow j :=
  Arrow.homMk' ((projectiveSmoothSingle k).map φ.left)
    ((projectiveSmoothSingle k).map φ.right) ((projectivePairArrow k).naturality φ)

/-- The original sheaf graph arrow of the smooth product pair. -/
abbrev smoothParameterTargetArrow (j : Arrow Sm) : Arrow (CochainComplex NST ℤ) :=
  Arrow.mk (cochainTransferPair k ((G).mapArrow.obj j)).f

/-- The square of original sheaf graphs on the product pair. -/
abbrev smoothParameterTargetArrowMap {i j : Arrow Sm} (φ : i ⟶ j) :
    smoothParameterTargetArrow (T := T) i ⟶ smoothParameterTargetArrow (T := T) j :=
  ShortComplex.fFunctor.map
    ((s).mapShortComplex.map (transferPairSequenceMap k ((G).mapArrow.map φ)))

set_option maxHeartbeats 450000 in
-- The source and the target are the two literal represented arrows.
/-- The product comparison on the original cochain arrows. -/
def smoothParameterCochainArrowIso (j : Arrow Sm) :
    ((J).mapHomologicalComplex c).mapArrow.obj (smoothParameterSourceArrow (k := k) j) ≅
      smoothParameterTargetArrow (T := T) j := by
  let f := (projectivePairArrow k).app j
  let g := ((J).mapHomologicalComplex c).map f
  let h := (cochainTransferPair k ((G).mapArrow.obj j)).f
  let e₁ := smoothParameterCochainEndpointIso e j.left
  let e₂ := smoothParameterCochainEndpointIso e j.right
  have he : e₁.hom ≫ h = g ≫ e₂.hom := (smoothParameterCochainEndpointIso_naturality e j.hom).symm
  exact Arrow.isoMk (f := Arrow.mk g) (g := Arrow.mk h) e₁ e₂ he

/-- The signed cone on the arrows of transfer sheaf complexes. -/
abbrev smoothParameterTargetConeFunctor :
    Arrow (CochainComplex NST ℤ) ⥤ CochainComplex NST ℤ :=
  CochainComplex.mappingConeNatTransFunctor Arrow.leftToRight

/-- The termwise coefficient comparison on the original projective cone. -/
abbrev smoothParameterConeMapIso (j : Arrow Sm) :
    ((J).mapHomologicalComplex c).obj ((projectivePairCochain k).obj j) ≅
      (smoothParameterTargetConeFunctor (k := k)).obj
        (((J).mapHomologicalComplex c).mapArrow.obj (smoothParameterSourceArrow j)) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso (smoothParameterSourceArrow j).hom J

/-- The termwise parameter product of the original cone compares with the
    transfer quotient cone of the literal product pair. -/
@[no_expose]
def smoothParameterCochainComparison (j : Arrow Sm) :
    ((J).mapHomologicalComplex c).obj ((projectivePairCochain k).obj j) ≅
      cochainTransferPairCone k ((G).mapArrow.obj j) :=
  smoothParameterConeMapIso (F := F) j ≪≫
    (smoothParameterTargetConeFunctor (k := k)).mapIso (smoothParameterCochainArrowIso e j)

set_option maxHeartbeats 650000 in
-- The two constituent cone isomorphisms are kept at their typed endpoints.
/-- The cone comparison is the termwise comparison followed by the product arrow map. -/
theorem smoothParameterCochainComparison_hom (j : Arrow Sm) :
    (smoothParameterCochainComparison e j).hom =
      (smoothParameterConeMapIso (F := F) j).hom ≫
        (smoothParameterTargetConeFunctor (k := k)).map
          (smoothParameterCochainArrowIso e j).hom := by
  unfold smoothParameterCochainComparison
  rfl

/-- The product arrow comparison identifies the component maps of a pair morphism. -/
theorem smoothParameterCochainArrowIso_naturality {i j : Arrow Sm} (φ : i ⟶ j) :
    ((J).mapHomologicalComplex c).mapArrow.map (smoothParameterSourceArrowMap φ) ≫
        (smoothParameterCochainArrowIso e j).hom =
      (smoothParameterCochainArrowIso e i).hom ≫
        smoothParameterTargetArrowMap (T := T) φ := by
  apply Arrow.hom_ext
  · exact smoothParameterCochainEndpointIso_naturality e φ.left
  · exact smoothParameterCochainEndpointIso_naturality e φ.right

section ParameterMap

variable {T' : SmoothSite (Spec (CommRingCat.of k))} (g : T ⟶ T')

/-- The original parameter transformation induces the literal map of the product arrows. -/
def smoothParameterArrowMap (j : Arrow Sm) :
    ((G).mapArrow.obj j) ⟶ ((parameterProduct T').mapArrow.obj j) :=
  Arrow.homMk' ((parameterMap g).app j.left) ((parameterMap g).app j.right)
    ((parameterMap g).naturality j.hom).symm

end ParameterMap

end AlgebraicGeometry.MotivicHomotopy
