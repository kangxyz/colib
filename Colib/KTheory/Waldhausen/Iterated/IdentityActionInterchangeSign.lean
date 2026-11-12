/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.SelfTrackStableInterchange
public import Colib.KTheory.Waldhausen.Iterated.TransformationInterchange
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIsoNaturality
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperation

/-!
Source: `Quillen/Waldhausen/SConstruction/Iterated/IdentityActionInterchangeSign.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The sign for two original identity-action operations

Two arbitrary natural automorphisms of the identity have independent actual
transformation-cylinder times. Their interchange follows from naturality,
without a scalar-commutation premise. The literal square yields the stable
sign and then anti-commuting operations on every original nonnegative K-group,
including K-zero, through the existing original stable comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Topology unitInterval
universe u v
namespace CategoryTheory.Waldhausen.IteratedS

/-- The two original identity-automorphism homotopies have literal pointwise interchange. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/IdentityActionInterchangeSign.lean:32"
  "adaptation" "Original independent identity-action times and anti-commuting K-operations."]
theorem prespectrumIsoHomotopy_identityAction_interchange
    (V : WideSubcategory preservesZero.{u}) (e e' : 𝟭 V.obj.Obj ≅ 𝟭 V.obj.Obj)
    (n : ℕ) (s t : unitInterval)
    (x : (prespectrum V).space n) :
    (prespectrumIsoHomotopy (𝟙 V) e).level n
        (s, (prespectrumIsoHomotopy (𝟙 V) e').level n (t, x)) =
      (prespectrumIsoHomotopy (𝟙 V) e').level n
        (t, (prespectrumIsoHomotopy (𝟙 V) e).level n (s, x)) :=
  prespectrumTransformationHomotopy_identityAction_interchange
    (V := V) (W := V) (F := 𝟙 V) (G := 𝟙 V) e.hom e'.hom e'.hom
    (fun _ ↦ V.obj.waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ V.obj.waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ V.obj.waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ rfl) (fun _ ↦ rfl) n s t x

/-- Two independent original identity actions anti-commute on nonnegative stable groups. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/IdentityActionInterchangeSign.lean:47"
  "adaptation" "Original independent identity-action times and anti-commuting K-operations."]
theorem stableIdentityAction_interchange_sign
    (V : WideSubcategory preservesZero.{u}) (e e' : 𝟭 V.obj.Obj ≅ 𝟭 V.obj.Obj) (n : ℕ)
    (a : stableHomotopyGroup (prespectrum V) (n : ℤ)) :
    (prespectrumIsoHomotopy (𝟙 V) e').stableOperation ((n + 1 : ℕ) : ℤ)
        ((prespectrumIsoHomotopy (𝟙 V) e).stableOperation (n : ℤ) a) =
      -((prespectrumIsoHomotopy (𝟙 V) e).stableOperation ((n + 1 : ℕ) : ℤ)
        ((prespectrumIsoHomotopy (𝟙 V) e').stableOperation (n : ℤ) a)) :=
  (prespectrumIsoHomotopy (𝟙 V) e).stableOperation_interchange_sign
    (prespectrumIsoHomotopy (𝟙 V) e') (prespectrumIsoHomotopy (𝟙 V) e)
    (prespectrumIsoHomotopy (𝟙 V) e')
    (prespectrumIsoHomotopy_identityAction_interchange V e e') (prespectrum_isOmega V) n a

set_option backward.isDefEq.respectTransparency.types false in
/-- Two identity automorphisms induce anti-commuting operations on every original K-group. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/IdentityActionInterchangeSign.lean:61"
  "adaptation" "Original independent identity-action times and anti-commuting K-operations."]
theorem originalKIdentityAction_interchange_sign
    {C : Type u} [Category.{v} C] (W : Structure C)
    (e e' : 𝟭 (AsSmall.{0} C) ≅ 𝟭 (AsSmall.{0} C)) (n : ℕ) (a : W.K n) :
    originalKSelfTrackOperation W W (prespectrumIsoHomotopy (𝟙 (asSmallCategory W)) e') (n + 1)
        (originalKSelfTrackOperation W W (prespectrumIsoHomotopy (𝟙 (asSmallCategory W)) e) n a) =
      (originalKSelfTrackOperation W W (prespectrumIsoHomotopy (𝟙 (asSmallCategory W)) e) (n + 1)
        (originalKSelfTrackOperation W W
          (prespectrumIsoHomotopy (𝟙 (asSmallCategory W)) e') n a))⁻¹ := by
  let H := prespectrumIsoHomotopy (𝟙 (asSmallCategory W)) e
  let J := prespectrumIsoHomotopy (𝟙 (asSmallCategory W)) e'
  let b := originalKSelfTrackOperation W W H n a
  let c := originalKSelfTrackOperation W W J n a
  let E := originalKStableEquiv W (n + 2)
  have hsign : E (Additive.ofMul (originalKSelfTrackOperation W W J (n + 1) b)) =
      E (-Additive.ofMul (originalKSelfTrackOperation W W H (n + 1) c)) := by
    calc
      _ = J.stableOperation ((n + 1 : ℕ) : ℤ)
          (originalKStableEquiv W (n + 1) (Additive.ofMul b)) :=
        originalKSelfTrackOperation_stable W W J (n + 1) b
      _ = J.stableOperation ((n + 1 : ℕ) : ℤ)
          (H.stableOperation (n : ℤ) (originalKStableEquiv W n (Additive.ofMul a))) :=
        congrArg (J.stableOperation ((n + 1 : ℕ) : ℤ))
          (originalKSelfTrackOperation_stable W W H n a)
      _ = -(H.stableOperation ((n + 1 : ℕ) : ℤ)
          (J.stableOperation (n : ℤ) (originalKStableEquiv W n (Additive.ofMul a)))) :=
        stableIdentityAction_interchange_sign (asSmallCategory W) e e' n _
      _ = -(H.stableOperation ((n + 1 : ℕ) : ℤ)
          (originalKStableEquiv W (n + 1) (Additive.ofMul c))) :=
        congrArg (fun z ↦ -(H.stableOperation ((n + 1 : ℕ) : ℤ) z))
          (originalKSelfTrackOperation_stable W W J n a).symm
      _ = -(E (Additive.ofMul (originalKSelfTrackOperation W W H (n + 1) c))) :=
        congrArg Neg.neg (originalKSelfTrackOperation_stable W W H (n + 1) c).symm
      _ = _ := (map_neg E _).symm
  have hAdd : Additive.ofMul (originalKSelfTrackOperation W W J (n + 1) b) =
      -Additive.ofMul (originalKSelfTrackOperation W W H (n + 1) c) := E.injective hsign
  have hMul := congrArg Additive.toMul hAdd
  simpa only [toMul_neg, toMul_ofMul] using hMul

end CategoryTheory.Waldhausen.IteratedS
