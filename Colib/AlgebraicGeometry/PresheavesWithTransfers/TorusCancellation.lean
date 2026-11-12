/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ContractionHI
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RepresentableLarge
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Presheaf

/-!
# The comparison map for torus cancellation

The target coefficient of a representable is the quotient of its torus
product by the unit section. The source torus is reduced by taking the
actual unit kernel on that quotient. The map of Suslin complexes is induced
by exterior product on signed correspondences.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject Sₖ
local notation "Bₖ" => SmoothSite.base Sₖ

/-- The literal unit-section correspondence in base-product coordinates. -/
abbrev torusUnitCorrespondence (X : Cor k) :
    (Cor.parameterProduct Bₖ).obj X ⟶ (Cor.parameterProduct Gₘ).obj X :=
  (Cor.parameterProductMap (SmoothSite.torusOne Sₖ)).app X

/-- A torus-product representable modulo the image of its unit section. -/
def torusCancellationCoefficients (Y : Cor k) : PresheafWithTransfers.{u + 1} k :=
  cokernel ((representableLarge k).map (torusUnitCorrespondence k Y))

/-- The quotient of the actual signed torus-product correspondences. -/
abbrev toTorusCancellationCoefficients (Y : Cor k) :
    (representableLarge k).obj ((Cor.parameterProduct Gₘ).obj Y) ⟶
      torusCancellationCoefficients k Y :=
  cokernel.π ((representableLarge k).map (torusUnitCorrespondence k Y))

/-- The source unit kernel of the target unit quotient. -/
def torusCancellationTarget (Y : Cor k) : PresheafWithTransfers.{u + 1} k :=
  contractionKernel (torusCancellationCoefficients k Y)

/-- Exterior product on the actual representable signed correspondences. -/
def torusExteriorRepresentableMap (Y : Cor k) :
    (representableLarge k).obj Y ⟶
      torusSections ((representableLarge k).obj ((Cor.parameterProduct Gₘ).obj Y)) :=
  ⟨{
    app U := AddCommGrpCat.ofHom {
      toFun := fun (α : ULift.{u + 1} (U.unop ⟶ Y)) ↦
        ULift.up ((Cor.parameterProduct Gₘ).map α.down)
      map_zero' := by
        change ULift.up ((Cor.parameterProduct Gₘ).map (0 : U.unop ⟶ Y)) = ULift.up 0
        simp
      map_add' α β := by
        change ULift.up ((Cor.parameterProduct Gₘ).map (α.down + β.down)) =
          ULift.up ((Cor.parameterProduct Gₘ).map α.down + (Cor.parameterProduct Gₘ).map β.down)
        rw [Functor.map_add] }
    naturality U V f := by
      apply AddCommGrpCat.hom_ext
      ext a
      let α : ULift.{u + 1} (U.unop ⟶ Y) := a
      change ULift.up ((Cor.parameterProduct Gₘ).map (f.unop ≫ α.down)) =
        ULift.up ((Cor.parameterProduct Gₘ).map f.unop ≫
          (Cor.parameterProduct Gₘ).map α.down)
      rw [Functor.map_comp] }⟩

/-- Exterior product followed by the target unit quotient. -/
def torusCancellationParameterMap (Y : Cor k) :
    (representableLarge k).obj Y ⟶ torusSections (torusCancellationCoefficients k Y) :=
  torusExteriorRepresentableMap k Y ≫ withParameterMap (toTorusCancellationCoefficients k Y) Gₘ

theorem torusCancellationParameterMap_app_apply (Y X : Cor k) (α : X ⟶ Y) :
    (torusCancellationParameterMap k Y).hom.app (op X) (ULift.up α) =
      (toTorusCancellationCoefficients k Y).hom.app (op ((Cor.parameterProduct Gₘ).obj X))
        (ULift.up ((Cor.parameterProduct Gₘ).map α)) := rfl

/-- The parameter map restricts to zero along the actual source unit section. -/
@[reassoc]
theorem torusCancellationParameterMap_unit (Y : Cor k) :
    torusCancellationParameterMap k Y ≫ torusUnit (torusCancellationCoefficients k Y) = 0 := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext a
  obtain ⟨α⟩ := a
  let X := U.unop
  let F := Cor.parameterProduct Gₘ
  let F₀ := Cor.parameterProduct Bₖ
  let q := toTorusCancellationCoefficients k Y
  let i := torusUnitCorrespondence k X
  change transfer (torusCancellationCoefficients k Y) i
    ((torusCancellationParameterMap k Y).hom.app (op X) (ULift.up α)) = 0
  rw [torusCancellationParameterMap_app_apply]
  have h := ConcreteCategory.congr_hom (transfer_naturality q i) (ULift.up (F.map α))
  change q.hom.app (op (F₀.obj X))
      (transfer ((representableLarge k).obj (F.obj Y)) i (ULift.up (F.map α))) =
    transfer (torusCancellationCoefficients k Y) i
      (q.hom.app (op (F.obj X)) (ULift.up (F.map α))) at h
  rw [← h, representableLarge_transfer_apply]
  have hi : F₀.map α ≫ torusUnitCorrespondence k Y = i ≫ F.map α :=
    (Cor.parameterProductMap (SmoothSite.torusOne Sₖ)).naturality α
  rw [← hi]
  have hzero := congrArg
    (fun f : (representableLarge k).obj (F₀.obj Y) ⟶ torusCancellationCoefficients k Y ↦
      f.hom.app (op (F₀.obj X)) (ULift.up (F₀.map α)))
    (cokernel.condition ((representableLarge k).map (torusUnitCorrespondence k Y)))
  change q.hom.app (op (F₀.obj X))
      (((representableLarge k).map (torusUnitCorrespondence k Y)).hom.app (op (F₀.obj X))
        (ULift.up (F₀.map α))) = 0 at hzero
  rw [representableLarge_map_app_apply] at hzero
  exact hzero

/-- Exterior product as a map into the quotient with both unit sections reduced. -/
def torusCancellationMap (Y : Cor k) :
    (representableLarge k).obj Y ⟶ torusCancellationTarget k Y :=
  kernel.lift _ (torusCancellationParameterMap k Y) (torusCancellationParameterMap_unit k Y)

@[reassoc]
theorem torusCancellationMap_ι (Y : Cor k) :
    torusCancellationMap k Y ≫ kernel.ι (torusUnit (torusCancellationCoefficients k Y)) =
      torusCancellationParameterMap k Y :=
  kernel.lift_ι _ _ _

/-- The induced map of the actual signed Suslin complexes. -/
@[colib_tag "COL-1039", colib_ref "Voevodsky2010Cancellation" "Corollary 4.9, p. 684"
  "ingredient" "The exterior-product comparison into the two unit reductions"]
def torusCancellationChainMap (Y : Cor k) :
    singularComplex ((representableLarge k).obj Y) ⟶
      singularComplex (torusCancellationTarget k Y) :=
  singularComplexMap (torusCancellationMap k Y)

/-- The chain map applies the same exterior product to the actual simplex. -/
theorem torusCancellationChainMap_f_app (Y X : Cor k) (n : ℕ) :
    ((torusCancellationChainMap k Y).f n).hom.app (op X) =
      (torusCancellationMap k Y).hom.app (op (Cor.simplexProduct X n)) :=
  singularComplexMap_f_app _ _ _

end AlgebraicGeometry.PresheafWithTransfers
