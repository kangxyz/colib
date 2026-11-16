/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPairPullback
public import Colib.AlgebraicGeometry.Modules.PerfectFlatPullback
public import Colib.AlgebraicGeometry.Modules.PerfectSupport
public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Support

/-! # Support under flat pullback

For a square of open pairs with flat vertical morphisms, the ordinary cochain
pullback preserves acyclicity on the indicated open. The comparison uses the
actual square and does not replace the ambient perfect complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- An additive homology-preserving functor takes an acyclic cochain complex to
an acyclic complex. -/
theorem acyclic_mapCochainComplex_of_preservesHomology {A B : Type*}
    [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    {K : CochainComplex A ℤ} (hK : K.Acyclic) :
    ((F.mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let z : (0 : CochainComplex A ℤ) ⟶ K := 0
  have hz := HomologicalComplex.acyclic_of_isZero (0 : CochainComplex A ℤ) (isZero_zero _)
  have : QuasiIso z := (quasiIso_iff z).2 fun n =>
    (quasiIsoAt_iff_exactAt z n (hz n)).2 (hK n)
  have hG : QuasiIso (G.map z) := HomologicalComplex.quasiIso_map_of_preservesHomology z F
  have hzG := HomologicalComplex.acyclic_of_isZero (G.obj 0) (G.map_isZero (isZero_zero _))
  exact fun n => (quasiIsoAt_iff_exactAt (G.map z) n (hzG n)).1
    ((quasiIso_iff _).1 hG n)

/-- Flat termwise pullback sends an acyclic cochain complex to an acyclic complex. -/
theorem acyclic_mapCochainComplex_pullback_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] {K : CochainComplex Y.Modules ℤ} (hK : K.Acyclic) :
    (((pullback f).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  let : PreservesFiniteLimits (pullback f) := pullback_preservesFiniteLimits_of_flat f
  exact acyclic_mapCochainComplex_of_preservesHomology (pullback f) hK

variable {A B : Scheme.OpenPairs.{u}} (f : A ⟶ B) [Flat f.left] [Flat f.right]

/-- The flat pullback of the original supported complex retains its support. -/
theorem perfectSupported_flatPairPullback {K : CochainComplex B.right.Modules ℤ}
    (hK : perfectSupported B.hom K) :
    perfectSupported A.hom (((pullback f.right).mapHomologicalComplex (.up ℤ)).obj K) := by
  refine ⟨Complex.isPerfectComplex_flatPullback f.right K hK.1, ?_⟩
  have h := acyclic_mapCochainComplex_pullback_of_flat f.left hK.2
  exact fun n => (h n).of_iso ((pullbackComplexOpenPairIso f).app K).symm

/-- The supported flat pullback uses the same complexes and arrows as the ambient pullback. -/
def perfectSupportedFlatPairPullback :
    (perfectSupported B.hom).FullSubcategory ⥤ (perfectSupported A.hom).FullSubcategory :=
  (perfectSupported A.hom).lift
    ((perfectSupported B.hom).ι ⋙ (pullback f.right).mapHomologicalComplex (.up ℤ))
    (fun K => perfectSupported_flatPairPullback f K.property)

/-- The same flat pullback is exact on the literal supported full subcategories. -/
theorem perfectSupportedFlatPairPullback_exact :
    Waldhausen.IsExact (perfectSupportedWaldhausen B.hom).cof
      (perfectSupportedWaldhausen B.hom).weq (perfectSupportedWaldhausen A.hom).cof
      (perfectSupportedWaldhausen A.hom).weq (perfectSupportedFlatPairPullback f) := by
  let F := (pullback f.right).mapHomologicalComplex (ComplexShape.up ℤ)
  let P := perfectSupported B.hom
  let Q := perfectSupported A.hom
  let : PreservesFiniteLimits (pullback f.right) := pullback_preservesFiniteLimits_of_flat f.right
  refine { zero := ?_, cofibration := ?_, weak := ?_, pushout := ?_ }
  · intro Z hZ
    apply IsZero.of_full_of_faithful_of_isZero Q.ι
    exact F.map_isZero ((Waldhausen.CofibrationClosedSubcategory.inclusion_exact
      (Waldhausen.complexes B.right.Modules) P (perfectSupported_cofibrationClosed B.hom)).zero hZ)
  · intro K L g hg
    change Mono (F.map g.hom)
    have : Mono (C := CochainComplex B.right.Modules ℤ) g.hom := hg
    infer_instance
  · intro K L g hg
    change QuasiIso (F.map g.hom)
    have : QuasiIso (C := B.right.Modules) g.hom := hg
    infer_instance
  · intro K L D Z g h a b hg sq
    apply IsPushout.of_map_of_faithful Q.ι
    exact (Waldhausen.CofibrationClosedSubcategory.inclusion_map_pushout
      (Waldhausen.complexes B.right.Modules) P
      (perfectSupported_cofibrationClosed B.hom) hg sq).map F

end AlgebraicGeometry.Scheme.Modules
