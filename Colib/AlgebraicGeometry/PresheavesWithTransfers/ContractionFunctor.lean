/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ContractionHI
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterFunctor

/-!
# The split contraction functor with transfers

The original Laurent sections split by the literal unit and projection.
The kernel functor retains the corresponding complementary summand on
each coefficient map and on each cochain degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "Bₖ" => SmoothSite.base (Spec (CommRingCat.of k))

/-- The induced map on the kernel of the literal torus unit. -/
def contractionKernelMap {P Q : PresheafWithTransfers.{v} k} (f : P ⟶ Q) :
    contractionKernel P ⟶ contractionKernel Q :=
  kernel.lift (torusUnit Q) (kernel.ι (torusUnit P) ≫ withParameterMap f Gₘ) (by
    change (kernel.ι (torusUnit P) ≫ withParameterMap f Gₘ) ≫ torusUnit Q = 0
    have h : withParameterMap f Gₘ ≫ torusUnit Q = torusUnit P ≫ withParameterMap f Bₖ :=
      (parameterPullback_coefficient_naturality f (SmoothSite.torusOne (Spec (.of k)))).symm
    rw [Category.assoc, h, ← Category.assoc, kernel.condition, zero_comp])

@[reassoc (attr := simp)]
theorem contractionKernelMap_ι {P Q : PresheafWithTransfers.{v} k} (f : P ⟶ Q) :
    contractionKernelMap f ≫ kernel.ι (torusUnit Q) =
      kernel.ι (torusUnit P) ≫ withParameterMap f Gₘ := kernel.lift_ι _ _ _

/-- Induced kernel maps retain the original composition. -/
theorem contractionKernelMap_comp {P Q R : PresheafWithTransfers.{v} k}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    contractionKernelMap (f ≫ g) = contractionKernelMap f ≫ contractionKernelMap g := by
  apply (cancel_mono (kernel.ι (torusUnit R))).mp
  rw [contractionKernelMap_ι, Category.assoc, contractionKernelMap_ι,
    contractionKernelMap_ι_assoc]
  rfl

/-- The complementary summand of the original Laurent reindexing functor. -/
def contractionKernelFunctor :
    PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k where
  obj := contractionKernel
  map := contractionKernelMap
  map_id P := by
    apply (cancel_mono (kernel.ι (torusUnit P))).mp
    simp only [contractionKernelMap_ι, Category.id_comp]
    exact Category.comp_id _
  map_comp f g := contractionKernelMap_comp f g

@[simp]
theorem contractionKernelFunctor_obj (P : PresheafWithTransfers.{v} k) :
    contractionKernelFunctor.obj P = contractionKernel P := by
  unfold contractionKernelFunctor
  rfl

instance : (contractionKernelFunctor :
    PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k).Additive where
  map_add {P Q} f g := by
    unfold contractionKernelFunctor
    change contractionKernelMap (f + g) = contractionKernelMap f + contractionKernelMap g
    apply (cancel_mono (kernel.ι (torusUnit Q))).mp
    simp only [Preadditive.add_comp, contractionKernelMap_ι]
    let T : PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k :=
      withParameterFunctor Gₘ
    let j : contractionKernel P ⟶ T.obj P := kernel.ι (torusUnit P)
    change j ≫ T.map (f + g) = j ≫ T.map f + j ≫ T.map g
    have h : T.map (f + g) = T.map f + T.map g := T.map_add
    exact (congrArg (fun m => j ≫ m) h).trans (Preadditive.comp_add _ _ _ j (T.map f) (T.map g))

/-- The actual complementary inclusion is natural for coefficient maps. -/
def contractionKernelInclusion :
    contractionKernelFunctor ⟶
      (withParameterFunctor Gₘ :
        PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k) := by
  unfold contractionKernelFunctor
  refine { app := fun P => kernel.ι (torusUnit P), naturality := ?_ }
  intro P Q f
  change contractionKernelMap f ≫ kernel.ι (torusUnit Q) =
    kernel.ι (torusUnit P) ≫ withParameterMap f Gₘ
  exact contractionKernelMap_ι f

/-- The actual splitting is natural for coefficient maps. -/
def contractionKernelRetraction :
    (withParameterFunctor Gₘ :
      PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k) ⟶
      contractionKernelFunctor := by
  unfold contractionKernelFunctor
  refine { app := contractionKernelProjection, naturality := ?_ }
  intro P Q f
  have h₁ : withParameterMap f Gₘ ≫ torusUnit Q = torusUnit P ≫ withParameterMap f Bₖ :=
    (parameterPullback_coefficient_naturality f (SmoothSite.torusOne (Spec (.of k)))).symm
  have h₂ : withParameterMap f Bₖ ≫ torusConstant Q =
      torusConstant P ≫ withParameterMap f Gₘ :=
    (parameterPullback_coefficient_naturality f (toBase Gₘ)).symm
  change withParameterMap f Gₘ ≫ contractionKernelProjection Q =
    contractionKernelProjection P ≫ contractionKernelMap f
  apply (cancel_mono (kernel.ι (torusUnit Q))).mp
  calc
    _ = withParameterMap f Gₘ ≫ (𝟙 _ - torusUnit Q ≫ torusConstant Q) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun m => withParameterMap f Gₘ ≫ m) (contractionKernelProjection_ι Q))
    _ = (𝟙 _ - torusUnit P ≫ torusConstant P) ≫ withParameterMap f Gₘ := by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp,
        ← Category.assoc (withParameterMap f Gₘ), h₁, Category.assoc, h₂,
        Category.assoc (torusUnit P)]
    _ = (contractionKernelProjection P ≫ kernel.ι (torusUnit P)) ≫ withParameterMap f Gₘ :=
      congrArg (fun m => m ≫ withParameterMap f Gₘ) (contractionKernelProjection_ι P).symm
    _ = contractionKernelProjection P ≫ kernel.ι (torusUnit P) ≫ withParameterMap f Gₘ :=
      Category.assoc _ _ _
    _ = contractionKernelProjection P ≫ contractionKernelMap f ≫ kernel.ι (torusUnit Q) :=
      congrArg (fun m => contractionKernelProjection P ≫ m) (contractionKernelMap_ι f).symm
    _ = _ := (Category.assoc _ _ _).symm

@[simp]
theorem contractionKernelInclusion_retraction :
    (contractionKernelInclusion (k := k) :
      (contractionKernelFunctor : PresheafWithTransfers.{v} k ⥤ _) ⟶ _) ≫
      contractionKernelRetraction = 𝟙 _ := by
  apply NatTrans.ext
  funext P
  unfold contractionKernelInclusion contractionKernelRetraction contractionKernelFunctor
  change kernel.ι (torusUnit P) ≫ contractionKernelProjection P =
    𝟙 (contractionKernel P)
  apply (cancel_mono (kernel.ι (torusUnit P))).mp
  rw [Category.assoc, contractionKernelProjection_ι, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc, kernel.condition, zero_comp, sub_zero]
  exact (Category.id_comp _).symm

end AlgebraicGeometry.PresheafWithTransfers
