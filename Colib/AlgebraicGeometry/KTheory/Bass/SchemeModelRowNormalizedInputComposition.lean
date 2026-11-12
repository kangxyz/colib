/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowNormalizedInput
public import Colib.KTheory.Bass.ModelDiagramRowInputComposition
public import Colib.Topology.Prespectrum.ZigzagSequentializationTelescopeNull

/-! # Original Model composition on normalized row presentations -/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
private theorem telescopeMap_congr
    {E V E' V' : ℕ → Topology.LoopPrespectrum.{w}}
    {a : ∀ n, E n ⟶ V n} {b : ∀ n, E (n + 1) ⟶ V n}
    {a' : ∀ n, E' n ⟶ V' n} {b' : ∀ n, E' (n + 1) ⟶ V' n}
    (d d' : ∀ n, E n ⟶ E' n) (v v' : ∀ n, V n ⟶ V' n)
    (ha : ∀ n, a n ≫ v n = d n ≫ a' n)
    (hb : ∀ n, b n ≫ v n = d (n + 1) ≫ b' n)
    (ha' : ∀ n, a n ≫ v' n = d' n ≫ a' n)
    (hb' : ∀ n, b n ≫ v' n = d' (n + 1) ≫ b' n)
    (hd : d = d') (hv : v = v') :
    ZigzagSequentialization.inducedTelescopeMap E V a b E' V' a' b' d v ha hb =
      ZigzagSequentialization.inducedTelescopeMap E V a b E' V' a' b' d' v' ha' hb' := by
  subst d'
  subst v'
  rfl

namespace KTheory.Bass.SchemeModelRowSeed
open GeometricSeedCospan ModelRowZigzagSequentialization
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M.obj (laurent.op.obj X)).obj.Obj)
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).hom.toFunctor (unit X) (unit Y))
  (M' : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit' : ∀ X, 𝟭 (M'.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M'.obj (laurent.op.obj X)).obj.Obj)
  (hunit' : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M'.map (laurent.op.map g)).hom.toFunctor (unit' X) (unit' Y))
  (M'' : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit'' : ∀ X, 𝟭 (M''.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M''.obj (laurent.op.obj X)).obj.Obj)
  (hunit'' : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M''.map (laurent.op.map g)).hom.toFunctor (unit'' X) (unit'' Y))
  (η : M ⟶ M')
  (hη : ∀ X, Preserves (η.app (laurent.op.obj X)).hom.toFunctor (unit X) (unit' X))
  (θ : M' ⟶ M'')
  (hθ : ∀ X, Preserves (θ.app (laurent.op.obj X)).hom.toFunctor (unit' X) (unit'' X))

include hη hθ in
/-- Composition of the actual Model inputs preserves the original units. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInputComposition.lean:58"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem inputPreserves_comp (X : Scheme.{u}ᵒᵖ) :
    Preserves ((η ≫ θ).app (laurent.op.obj X)).hom.toFunctor (unit X) (unit'' X) := by
  intro A
  change (θ.app (laurent.op.obj X)).hom.toFunctor.map
    ((η.app (laurent.op.obj X)).hom.toFunctor.map ((unit X).hom.app A)) = _
  rw [hη, hθ]
  rfl

/-- Every finite vertex keeps actual Model composition. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInputComposition.lean:67"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem stageInput_comp (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    stageInput M M'' (η ≫ θ) i X = stageInput M M' η i X ≫ stageInput M' M'' θ i X := by
  simp only [stageInput, Functor.whiskerRight_comp, Functor.map_comp, NatTrans.comp_app]

/-- Every proper-row target keeps the same actual Model composition. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInputComposition.lean:72"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem targetInput_comp (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    targetInput M M'' (η ≫ θ) i X = targetInput M M' η i X ≫ targetInput M' M'' θ i X :=
  congrArg (fun a => a.app X)
    (ModelDiagramRowStabilizedTarget.inputNatTrans_comp squareFunctor i η θ)

variable
  (hηθ : ∀ X, Preserves ((η ≫ θ).app (laurent.op.obj X)).hom.toFunctor (unit X) (unit'' X))

/-- The canonical normalized maps preserve actual input composition, for any proof of its unit law.
-/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInputComposition.lean:82"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedInputMap_comp (X : Scheme.{u}ᵒᵖ) :
    normalizedInputMap M unit hunit M' unit' hunit' η hη X ≫
        normalizedInputMap M' unit' hunit' M'' unit'' hunit'' θ hθ X =
      normalizedInputMap M unit hunit M'' unit'' hunit'' (η ≫ θ) hηθ X := by
  unfold normalizedInputMap
  rw [ZigzagSequentialization.inducedTelescopeMap_comp]
  have hd : (fun i => stageInput M M' η i X ≫ stageInput M' M'' θ i X) =
      (fun i => stageInput M M'' (η ≫ θ) i X) :=
    funext (fun i => (stageInput_comp M M' M'' η θ i X).symm)
  have hv : (fun i => targetInput M M' η i X ≫ targetInput M' M'' θ i X) =
      (fun i => targetInput M M'' (η ≫ θ) i X) :=
    funext (fun i => (targetInput_comp M M' M'' η θ i X).symm)
  exact telescopeMap_congr _ _ _ _ _ _ _ _ hd hv

/-- Equal original inputs give the same normalized map, independently of unit-proof spelling. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInputComposition.lean:97"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedInputMap_congr
    (η' : M ⟶ M')
    (hη' : ∀ X, Preserves (η'.app (laurent.op.obj X)).hom.toFunctor (unit X) (unit' X))
    (h : η = η') (X : Scheme.{u}ᵒᵖ) :
    normalizedInputMap M unit hunit M' unit' hunit' η hη X =
      normalizedInputMap M unit hunit M' unit' hunit' η' hη' X := by
  subst η'
  rfl

include hηθ in
/-- A prescribed original composite equality gives its literal normalized-map square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInputComposition.lean:108"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedInputMap_comp_eq
    (ρ : M ⟶ M'')
    (hρ : ∀ X, Preserves (ρ.app (laurent.op.obj X)).hom.toFunctor (unit X) (unit'' X))
    (h : η ≫ θ = ρ) (X : Scheme.{u}ᵒᵖ) :
    normalizedInputMap M unit hunit M' unit' hunit' η hη X ≫
        normalizedInputMap M' unit' hunit' M'' unit'' hunit'' θ hθ X =
      normalizedInputMap M unit hunit M'' unit'' hunit'' ρ hρ X :=
  (normalizedInputMap_comp M unit hunit M' unit' hunit' M'' unit'' hunit''
    η hη θ hθ hηθ X).trans
      (normalizedInputMap_congr M unit hunit M'' unit'' hunit'' (η ≫ θ) hηθ ρ hρ h X)

end KTheory.Bass.SchemeModelRowSeed
