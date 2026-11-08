/- Regression tests for coarse joint data on the original native perfect category. -/
module

import Colib.CategoryTheory.Waldhausen.Fibration.Rows.CoarseJoint
import Colib.AlgebraicGeometry.Modules.PerfectOpenJoint

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen AlgebraicGeometry
open CategoryTheory.Waldhausen.Fibration RowFactorization
open Scheme.Modules

noncomputable section
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
local notation "P" => RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
local notation "W" => perfectOpenWeakWaldhausen j
local notation "D" => JointData.coarseReflexive (perfectOpenNested j) (perfectOpenJointData j)

-- No geometric finiteness, approximation or additional exactness premise is supplied.
example : JointData (NestedWeakEquivalences.refl W) := D

example : IsExact (ArrowCategory.waldhausenStructure W).cof
    (ArrowCategory.waldhausenStructure W).weq
    (ExtensionCategory.waldhausenStructure W).cof
    (ExtensionCategory.waldhausenStructure W).weq (D).joint := (D).exact

-- Cofibrations stay ambient monomorphisms; the original identity-cone maps stay literal.
example {K L : ObjectProperty.FullSubcategory P} (f : K ⟶ L) :
    (W).cof f ↔ Mono f.hom := Iff.rfl

example (f : Arrow (ObjectProperty.FullSubcategory P)) :
    ((D).joint.obj f).obj.right.obj = CochainComplex.SplitFactorization.middle f.hom.hom := rfl

example (f : Arrow (ObjectProperty.FullSubcategory P)) :
    ((D).joint.obj f).obj.hom.hom =
      CochainComplex.SplitFactorization.jointInclusion f.hom.hom := rfl

example (f : Arrow (ObjectProperty.FullSubcategory P)) :
    ((D).projection.app f).hom = CochainComplex.SplitFactorization.projection f.hom.hom := rfl

example : SecondEndpointSection (NestedWeakEquivalences.refl W) D :=
  perfectOpenJointData_secondEndpointSection j

example (f : Arrow (ObjectProperty.FullSubcategory P)) :
    (W).weq ((D).projection.app f) := (D).weak f

example (n : SimplexCategory) : FunctorialFactorization (QuotientRows.waldhausenStructure W n) :=
  QuotientRows.factorizationOfJointData W D n

example {n : SimplexCategory} (f : Arrow (QuotientRows.Obj W n)) (p : Interval n) :
    (((QuotientRows.factorizationOfJointData W D n).projection.app f).hom.app p).hom =
      CochainComplex.SplitFactorization.projection (f.hom.hom.app p).hom := rfl
