/- Regression client for the native perfect joint cylinder. -/
module
import Colib.AlgebraicGeometry.Modules.PerfectOpenJoint

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry StrictlyPerfect
namespace NativePerfectJointRegression
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
local notation "P" => RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "D" => Scheme.Modules.perfectOpenJointData j

-- The public result is accepted at the actual existing fine structure.
example : Waldhausen.Fibration.RowFactorization.JointData
    (Scheme.Modules.perfectOpenNested j) := D

-- No user-supplied exactness or section assumptions.
example : Waldhausen.IsExact (Waldhausen.ArrowCategory.waldhausenStructure V).cof
    (Waldhausen.ArrowCategory.waldhausenStructure V).weq
    (Waldhausen.ExtensionCategory.waldhausenStructure V).cof
    (Waldhausen.ExtensionCategory.waldhausenStructure V).weq (D).joint := (D).exact

example : Waldhausen.Fibration.RowFactorization.SecondEndpointSection
    (Scheme.Modules.perfectOpenNested j) D :=
  Scheme.Modules.perfectOpenJointData_secondEndpointSection j

-- The original native ambient-monomorphism class is retained.
example {K L : (ObjectProperty.FullSubcategory P)} (f : K ⟶ L) : (V).cof f ↔ Mono f.hom := Iff.rfl

-- The middle is literally Cone(id K) ⊞ L, not a derived-category replacement.
example (f : Arrow (ObjectProperty.FullSubcategory P)) :
    ((D).joint.obj f).obj.right.obj = CochainComplex.SplitFactorization.middle f.hom.hom := rfl

example (f : Arrow (ObjectProperty.FullSubcategory P)) :
    ((D).joint.obj f).obj.hom.hom = CochainComplex.SplitFactorization.jointInclusion f.hom.hom := rfl

example (f : Arrow (ObjectProperty.FullSubcategory P)) :
    ((D).projection.app f).hom = CochainComplex.SplitFactorization.projection f.hom.hom := rfl

example (f : Arrow (ObjectProperty.FullSubcategory P)) :
    (Scheme.Modules.perfectOpenNested j).coarse.weq ((D).projection.app f) := (D).weak f

end NativePerfectJointRegression
