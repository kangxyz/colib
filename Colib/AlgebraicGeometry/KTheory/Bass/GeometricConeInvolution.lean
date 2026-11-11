/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeCells
public import Colib.Topology.Prespectrum.StrictSquareCellInduction

/-!
# The actual geometric cone permutation is involutive

The proof uses every original quotient cell. Each pair of independent parameter
blocks is returned in its original order, and the two specified opposite scheme
swaps cancel by the original base-product involution. No sign or boundary
identification is inferred from this point-set theorem.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.GeometricConeInterchange

/-- The two actual opposite swaps cancel under any original spectrum diagram. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:33"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem map_swaps_cancel {S T : Scheme.{u}} (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}) (n : ℕ)
    (x : (F.obj (op ((baseProductFunctor q).obj ((baseProductFunctor p).obj X)))).space n) :
    (F.map (baseProductSwapMap p q X).op).map n
      ((F.map (baseProductSwapMap q p X).op).map n x) = x := by
  have hs : (baseProductSwapMap q p X).op ≫ (baseProductSwapMap p q X).op = 𝟙 _ :=
    Quiver.Hom.unop_inj (baseProductSwapMap_comp p q X)
  have hm : F.map (baseProductSwapMap q p X).op ≫
      F.map (baseProductSwapMap p q X).op = 𝟙 _ := by
    rw [← F.map_comp, hs, F.map_id]
  exact congrArg (fun k => k.map n x) hm


/-- Twice the actual target/target exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:47"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_target_target (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (x : (F.obj (laurent.op.obj (laurent.op.obj X))).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.target ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n (Cell.target (F.mapArrow.mapArrow.obj (square
        (laurent.op.obj X))) n (x)))) = Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n (Cell.target (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (x))
        := by
  rw [permutation_target_target, permutation_target_target, map_swaps_cancel]

/-- Twice the actual target/upper exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:58"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_target_upper (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (t : unitInterval)
    (x : (F.obj (polynomial.op.obj (laurent.op.obj X))).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.target ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n (Cell.upper (F.mapArrow.mapArrow.obj (square
        (laurent.op.obj X))) n t (x)))) = Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n (Cell.upper (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (x))
        := by
  rw [permutation_target_upper, permutation_upper_target, map_swaps_cancel]

/-- Twice the actual target/lower exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:69"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_target_lower (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (t : unitInterval)
    (x : (F.obj (polynomial.op.obj (laurent.op.obj X))).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.target ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n (Cell.lower (F.mapArrow.mapArrow.obj (square
        (laurent.op.obj X))) n t (x)))) = Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n (Cell.lower (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (x))
        := by
  rw [permutation_target_lower, permutation_lower_target, map_swaps_cancel]

/-- Twice the actual target/overlap exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:80"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_target_overlap (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (t v : unitInterval)
    (x : (F.obj (laurent.op.obj X)).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.target ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n (Cell.overlap (F.mapArrow.mapArrow.obj (square
        (laurent.op.obj X))) n t v (x)))) = Cell.target ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n (Cell.overlap (F.mapArrow.mapArrow.obj (square
        (laurent.op.obj X))) n t v (x)) := by
  rw [permutation_target_overlap, permutation_overlap_target]

/-- Twice the actual upper/target exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:91"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_upper_target (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : (F.obj (laurent.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.upper ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.target (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n (x)))) = Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.target (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
        (x)) := by
  rw [permutation_upper_target, permutation_target_upper, map_swaps_cancel]

/-- Twice the actual upper/upper exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:102"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_upper_upper (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t : unitInterval)
    (x : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.upper ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)))) = Cell.upper ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)) := by
  rw [permutation_upper_upper, permutation_upper_upper, map_swaps_cancel]

/-- Twice the actual upper/lower exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:113"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_upper_lower (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t : unitInterval)
    (x : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.upper ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)))) = Cell.upper ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)) := by
  rw [permutation_upper_lower, permutation_lower_upper, map_swaps_cancel]

/-- Twice the actual upper/overlap exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:124"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_upper_overlap (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t v : unitInterval)
    (x : (F.obj (polynomial.op.obj X)).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.upper ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t v (x)))) = Cell.upper ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t v (x)) := by
  rw [permutation_upper_overlap, permutation_overlap_upper]

/-- Twice the actual lower/target exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:135"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_lower_target (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : (F.obj (laurent.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.lower ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.target (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n (x)))) = Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.target (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
        (x)) := by
  rw [permutation_lower_target, permutation_target_lower, map_swaps_cancel]

/-- Twice the actual lower/upper exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:146"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_lower_upper (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t : unitInterval)
    (x : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.lower ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)))) = Cell.lower ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)) := by
  rw [permutation_lower_upper, permutation_upper_lower, map_swaps_cancel]

/-- Twice the actual lower/lower exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:157"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_lower_lower (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t : unitInterval)
    (x : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.lower ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)))) = Cell.lower ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)) := by
  rw [permutation_lower_lower, permutation_lower_lower, map_swaps_cancel]

/-- Twice the actual lower/overlap exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:168"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_lower_overlap (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t v : unitInterval)
    (x : (F.obj (polynomial.op.obj X)).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.lower ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t v (x)))) = Cell.lower ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t v (x)) := by
  rw [permutation_lower_overlap, permutation_overlap_lower]

/-- Twice the actual overlap/target exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:179"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_overlap_target (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r s : unitInterval)
    (x : (F.obj (laurent.op.obj X)).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.overlap ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r s (Cell.target (F.mapArrow.mapArrow.obj (square
        X)) n (x)))) = Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s
        (Cell.target (F.mapArrow.mapArrow.obj (square X)) n (x)) := by
  rw [permutation_overlap_target, permutation_target_overlap]

/-- Twice the actual overlap/upper exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:189"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_overlap_upper (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r s t : unitInterval)
    (x : (F.obj (polynomial.op.obj X)).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.overlap ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r s (Cell.upper (F.mapArrow.mapArrow.obj (square
        X)) n t (x)))) = Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r
        s (Cell.upper (F.mapArrow.mapArrow.obj (square X)) n t (x)) := by
  rw [permutation_overlap_upper, permutation_upper_overlap]

/-- Twice the actual overlap/lower exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:199"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_overlap_lower (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r s t : unitInterval)
    (x : (F.obj (polynomial.op.obj X)).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.overlap ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r s (Cell.lower (F.mapArrow.mapArrow.obj (square
        X)) n t (x)))) = Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r
        s (Cell.lower (F.mapArrow.mapArrow.obj (square X)) n t (x)) := by
  rw [permutation_overlap_lower, permutation_lower_overlap]

/-- Twice the actual overlap/overlap exchange returns every original coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:209"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_twice_overlap_overlap (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r s t v : unitInterval)
    (x : (F.obj X).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.overlap ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap (F.mapArrow.mapArrow.obj
        (square X)) n t v (x)))) = Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.overlap (F.mapArrow.mapArrow.obj (square X)) n t v (x)) := by
  rw [permutation_overlap_overlap, permutation_overlap_overlap]

/-- The actual geometric permutation is involutive on the entire original double quotient. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:219"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_comp (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    (permutation F X).hom ≫ (permutation F X).hom = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  change (permutation F X).hom.map n ((permutation F X).hom.map n x) = x
  refine Cell.inductionOn ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n x
    ?_ ?_ ?_ ?_
  · intro y
    refine Cell.inductionOn (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n y
      ?_ ?_ ?_ ?_
    · intro z
      exact permutation_twice_target_target F X n z
    · intro t z
      exact permutation_twice_target_upper F X n t z
    · intro t z
      exact permutation_twice_target_lower F X n t z
    · intro t v z
      exact permutation_twice_target_overlap F X n t v z
  · intro r y
    refine Cell.inductionOn (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n y
      ?_ ?_ ?_ ?_
    · intro z
      exact permutation_twice_upper_target F X n r z
    · intro t z
      exact permutation_twice_upper_upper F X n r t z
    · intro t z
      exact permutation_twice_upper_lower F X n r t z
    · intro t v z
      exact permutation_twice_upper_overlap F X n r t v z
  · intro r y
    refine Cell.inductionOn (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n y
      ?_ ?_ ?_ ?_
    · intro z
      exact permutation_twice_lower_target F X n r z
    · intro t z
      exact permutation_twice_lower_upper F X n r t z
    · intro t z
      exact permutation_twice_lower_lower F X n r t z
    · intro t v z
      exact permutation_twice_lower_overlap F X n r t v z
  · intro r s y
    refine Cell.inductionOn (F.mapArrow.mapArrow.obj (square X)) n y
      ?_ ?_ ?_ ?_
    · intro z
      exact permutation_twice_overlap_target F X n r s z
    · intro t z
      exact permutation_twice_overlap_upper F X n r s t z
    · intro t z
      exact permutation_twice_overlap_lower F X n r s t z
    · intro t v z
      exact permutation_twice_overlap_overlap F X n r s t v z

/-- The specified inverse equals the original forward geometric permutation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeInvolution.lean:274"
  "adaptation" "Original sixteen-cell involution of the actual geometric cone permutation."]
theorem permutation_inv_eq_hom (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    (permutation F X).inv = (permutation F X).hom := by
  apply (cancel_epi (permutation F X).hom).mp
  rw [Iso.hom_inv_id, permutation_comp]

end KTheory.Bass.GeometricConeInterchange
