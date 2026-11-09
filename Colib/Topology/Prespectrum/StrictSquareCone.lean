/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.HomotopyPushout
public import Colib.Topology.Prespectrum.MappingCone
public import Colib.Topology.Prespectrum.ParameterLooping
public import Colib.Topology.Prespectrum.HomotopyTransport

/-!
# A strict functor on commuting prespectrum squares

An object of the iterated arrow category is an actual commuting square. Its constant-track
comparison from the original double mapping cylinder is functorial for strict square maps.
Taking the original mapping cone and parameter looping therefore gives an actual functor.
This owner does not rectify a homotopy-commuting geometric diagram.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/StrictSquareCone.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum
namespace StrictSquare

variable (S : Arrow (Arrow LoopPrespectrum.{u}))

/-- The original double mapping cylinder of the two source legs. -/
def span : LoopPrespectrum.{u} :=
  HomotopyPushout.prespectrum S.left.hom S.hom.left

/-- The literal constant track supplied by the strict square equation. -/
def track : Homotopy (S.left.hom ≫ S.hom.right) (S.hom.left ≫ S.right.hom) :=
  (Homotopy.refl (S.left.hom ≫ S.hom.right)).cast rfl S.hom.w.symm

/-- Comparison to the final corner, retaining both legs and the constant cylinder. -/
def comparison : span S ⟶ S.right.right :=
  HomotopyPushout.desc S.left.hom S.hom.left S.hom.right S.right.hom (track S)

variable {S T U : Arrow (Arrow LoopPrespectrum.{u})}

/-- A strict map of squares acts on the entire original double cylinder. -/
def spanMap (a : S ⟶ T) : span S ⟶ span T :=
  HomotopyPushout.map S.left.hom S.hom.left T.left.hom T.hom.left
    a.left.left a.left.right a.right.left a.left.w.symm
    (congrArg (fun f => f.left) a.w).symm

@[simp] theorem spanMap_id (S : Arrow (Arrow LoopPrespectrum.{u})) :
    spanMap (𝟙 S) = 𝟙 (span S) := by
  exact HomotopyPushout.map_id _ _

@[simp] theorem spanMap_comp (a : S ⟶ T) (b : T ⟶ U) :
    spanMap (a ≫ b) = spanMap a ≫ spanMap b := by
  exact (HomotopyPushout.map_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).symm

/-- Strict naturality holds on both original endpoints and on every cylinder point. -/
theorem comparison_naturality (a : S ⟶ T) :
    spanMap a ≫ comparison T = comparison S ≫ a.right.right := by
  apply HomotopyPushout.hom_ext
  · apply Hom.ext
    funext n
    ext x
    exact congrArg (fun f => f.map n x) (congrArg (fun f => f.right) a.w)
  · apply Hom.ext
    funext n
    ext x
    exact congrArg (fun f => f.map n x) a.right.w
  · intro n s x
    change (a.left.left ≫ T.left.hom ≫ T.hom.right).map n x =
      (S.left.hom ≫ S.hom.right ≫ a.right.right).map n x
    have h := congrArg (fun f => f.right) a.w
    change a.left.right ≫ T.hom.right = S.hom.right ≫ a.right.right at h
    rw [← Category.assoc, a.left.w, Category.assoc, h]

end StrictSquare

/-- The original strict-square comparison is a functor into actual prespectrum arrows. -/
def strictSquareComparisonFunctor :
    Arrow (Arrow LoopPrespectrum.{u}) ⥤ Arrow LoopPrespectrum.{u} where
  obj S := Arrow.mk (StrictSquare.comparison S)
  map a := Arrow.homMk (StrictSquare.spanMap a) a.right.right
    (StrictSquare.comparison_naturality a)
  map_id S := by
    apply Arrow.hom_ext
    · exact StrictSquare.spanMap_id S
    · rfl
  map_comp a b := by
    apply Arrow.hom_ext
    · exact StrictSquare.spanMap_comp a b
    · rfl

/-- Parameter looping of the actual square cone, functorial for strict square maps. -/
def strictSquareLoopedConeFunctor : Arrow (Arrow LoopPrespectrum.{u}) ⥤ LoopPrespectrum.{u} :=
  strictSquareComparisonFunctor ⋙ mappingConeFunctor ⋙ parameterLoopingFunctor

end Topology.LoopPrespectrum

attribute [colib_tag "COL-0338",
  colib_ref "quillen" "Quillen/Topology/Prespectrum/StrictSquareCone.lean" "adaptation"
    "Actual strict-square cylinder, cone-loop maps and supplied-seed finite iteration"]
  Topology.LoopPrespectrum.strictSquareComparisonFunctor
  Topology.LoopPrespectrum.strictSquareLoopedConeFunctor
