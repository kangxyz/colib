/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedPencilEndpoints
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.ConstantFamily

/-!
# The actual whole polynomial family minus the actual constant pole

Both terms are the existing whole finite-flat span construction on literal
native zero schemes. The constant family is constructed from the original pole
by actual Cartesian base change, so its finite flatness is derived rather than
postulated. The two endpoint identities retain the entire original zero schemes.
The family and pole can belong to different invertible modules.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Cor

open Scheme Scheme.PolynomialSectionPencil Scheme.SmoothSite.Contraction

variable {k : Type u} [Field k] {S X V : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) [IsSeparated t] (q : X ⟶ S) (r : V ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]
  (L P : (pullback q r).Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property P]
  (a c : Γ(L, ⊤)) (u : Γ(P, ⊤))

local notation "U" => SmoothSite.mk (q ≫ t)
local notation "W" => SmoothSite.mk (r ≫ t)
local notation "F" => familySource (q ≫ t) (pullback.fst q r) L a c ≫
  (nativeParameterIso (.of k) U).inv
local notation "FP" => familySource (q ≫ t) (pullback.fst q r) P u u ≫
  (nativeParameterIso (.of k) U).inv

variable [IsFinite F] [Flat F]
  [IsFinite ((zeroScheme (pullback q r) P u).subschemeι ≫ pullback.fst q r)]
  [Flat ((zeroScheme (pullback q r) P u).subschemeι ≫ pullback.fst q r)]

/-- The actual constant pole family is finite, by base change of the original whole pole. -/
theorem nativeRetainedConstantSource_isFinite : IsFinite FP := by
  haveI := isFinite_constantFamilySource (q ≫ t) (pullback.fst q r) P u
  infer_instance

/-- The actual constant pole family is flat, by base change of the original whole pole. -/
theorem nativeRetainedConstantSource_flat : Flat FP := by
  haveI := flat_constantFamilySource (q ≫ t) (pullback.fst q r) P u
  infer_instance

/-- The genuine whole polynomial-family correspondence minus the genuine
constant-pole correspondence. Neither term is reduced or replaced by components. -/
def retainedPencilDifference : Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk W := by
  haveI := nativeRetainedConstantSource_isFinite t q r P u
  haveI := nativeRetainedConstantSource_flat t q r P u
  exact ofFiniteFlatSpan F (retainedFamilyTarget t q r L a c)
    (nativeRetainedFamily_base t q r L a c) -
      ofFiniteFlatSpan FP (retainedFamilyTarget t q r P u u)
        (nativeRetainedFamily_base t q r P u u)

/-- The zero endpoint of the actual difference is the complete original zero
scheme minus the complete original pole, with both literal retained-product legs. -/
theorem retainedPencilDifference_zero :
    letI := nativeZeroSource_isFinite U (pullback.fst q r) L a c
    letI := nativeZeroSource_flat U (pullback.fst q r) L a c
    (graphFunctor k).map (nativeAffineSection (.of k) U 0) ≫
      retainedPencilDifference t q r L P a c u =
      ofFiniteFlatSpan ((zeroScheme (pullback q r) L a).subschemeι ≫ pullback.fst q r)
        ((zeroScheme (pullback q r) L a).subschemeι ≫ pullback.snd q r)
        (retainedZero_base t q r L a) -
      ofFiniteFlatSpan ((zeroScheme (pullback q r) P u).subschemeι ≫ pullback.fst q r)
        ((zeroScheme (pullback q r) P u).subschemeι ≫ pullback.snd q r)
        (retainedZero_base t q r P u) := by
  haveI := nativeZeroSource_isFinite U (pullback.fst q r) L a c
  haveI := nativeZeroSource_flat U (pullback.fst q r) L a c
  haveI := nativeRetainedConstantSource_isFinite t q r P u
  haveI := nativeRetainedConstantSource_flat t q r P u
  unfold retainedPencilDifference
  rw [Preadditive.comp_sub, nativeRetainedFamily_zero, nativeRetainedFamily_zero]

/-- The one endpoint retains the second complete zero scheme and exactly the
same complete constant pole, with no extra constant-family flatness assumption. -/
theorem retainedPencilDifference_one :
    letI := nativeOneSource_isFinite U (pullback.fst q r) L a c
    letI := nativeOneSource_flat U (pullback.fst q r) L a c
    (graphFunctor k).map (nativeAffineSection (.of k) U 1) ≫
      retainedPencilDifference t q r L P a c u =
      ofFiniteFlatSpan ((zeroScheme (pullback q r) L c).subschemeι ≫ pullback.fst q r)
        ((zeroScheme (pullback q r) L c).subschemeι ≫ pullback.snd q r)
        (retainedZero_base t q r L c) -
      ofFiniteFlatSpan ((zeroScheme (pullback q r) P u).subschemeι ≫ pullback.fst q r)
        ((zeroScheme (pullback q r) P u).subschemeι ≫ pullback.snd q r)
        (retainedZero_base t q r P u) := by
  haveI := nativeOneSource_isFinite U (pullback.fst q r) L a c
  haveI := nativeOneSource_flat U (pullback.fst q r) L a c
  haveI := nativeRetainedConstantSource_isFinite t q r P u
  haveI := nativeRetainedConstantSource_flat t q r P u
  unfold retainedPencilDifference
  rw [Preadditive.comp_sub, nativeRetainedFamily_one, nativeRetainedFamily_one]

end AlgebraicGeometry.Cor
