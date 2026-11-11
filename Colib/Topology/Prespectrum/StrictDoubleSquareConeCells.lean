/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.StrictDoubleSquareCone

/-!
# All sixteen original cells of the two-totalization interchange

The four original total-cone quotient strata give sixteen ordered cell types.
The actual interchange exchanges their complete parameter blocks. The deepest
cell preserves four independent parameters, with no reparametrization. The
target remains the actual pointwise-cone square of the original comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.StrictSquare
namespace Cell
variable (S : Arrow (Arrow LoopPrespectrum.{u})) (n : ℕ)

/-- The original target-inclusion stratum of the total cone. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:30"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
def target (x : S.right.right.space n) : (totalFunctor.obj S).space n :=
  (mappingConeInclusion (comparison S)).map n x

/-- The original upper-chart cylinder with its unchanged cone height. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:34"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
def upper (r : unitInterval) (x : S.left.right.space n) : (totalFunctor.obj S).space n :=
  (mappingConeHomotopy (comparison S)).level n
    (r, HomotopyPushout.left S.left.hom S.hom.left n x)

/-- The original lower-chart cylinder with its unchanged cone height. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:39"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
def lower (r : unitInterval) (x : S.right.left.space n) : (totalFunctor.obj S).space n :=
  (mappingConeHomotopy (comparison S)).level n
    (r, HomotopyPushout.right S.left.hom S.hom.left n x)

/-- The original overlap stratum with independent cone height and overlap time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:44"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
def overlap (r s : unitInterval) (x : S.left.left.space n) : (totalFunctor.obj S).space n :=
  (mappingConeHomotopy (comparison S)).level n
    (r, HomotopyPushout.cylinder S.left.hom S.hom.left n (s,x))

end Cell
namespace Double
variable (E : Arrow (Arrow (Arrow (Arrow LoopPrespectrum.{u}))))

/-- The original target/target cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:53"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_target_target (n : ℕ)
    (x : E.right.right.right.right.space n) :
    (interchangeIso E).hom.map n
      (Cell.target (totalFunctor.mapArrow.mapArrow.obj E) n
        (Cell.target E.right.right n x)) =
      Cell.target (coneSquare (comparisonMap E)) n
        (Cell.target ((Arrow.rightFunc ⋙ Arrow.rightFunc).mapArrow.mapArrow.obj E) n x) := rfl

/-- The original target/upper cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:62"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_target_upper (n : ℕ) (t : unitInterval)
    (x : E.right.right.left.right.space n) :
    (interchangeIso E).hom.map n
      (Cell.target (totalFunctor.mapArrow.mapArrow.obj E) n
        (Cell.upper E.right.right n t x)) =
      Cell.upper (coneSquare (comparisonMap E)) n t
        (Cell.target ((Arrow.leftFunc ⋙ Arrow.rightFunc).mapArrow.mapArrow.obj E) n x) := rfl

/-- The original target/lower cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:71"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_target_lower (n : ℕ) (t : unitInterval)
    (x : E.right.right.right.left.space n) :
    (interchangeIso E).hom.map n
      (Cell.target (totalFunctor.mapArrow.mapArrow.obj E) n
        (Cell.lower E.right.right n t x)) =
      Cell.lower (coneSquare (comparisonMap E)) n t
        (Cell.target ((Arrow.rightFunc ⋙ Arrow.leftFunc).mapArrow.mapArrow.obj E) n x) := rfl

/-- The original target/overlap cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:80"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_target_overlap (n : ℕ) (t v : unitInterval)
    (x : E.right.right.left.left.space n) :
    (interchangeIso E).hom.map n
      (Cell.target (totalFunctor.mapArrow.mapArrow.obj E) n
        (Cell.overlap E.right.right n t v x)) =
      Cell.overlap (coneSquare (comparisonMap E)) n t v
        (Cell.target ((Arrow.leftFunc ⋙ Arrow.leftFunc).mapArrow.mapArrow.obj E) n x) := rfl

/-- The original upper/target cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:89"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_upper_target (n : ℕ) (r : unitInterval)
    (x : E.left.right.right.right.space n) :
    (interchangeIso E).hom.map n
      (Cell.upper (totalFunctor.mapArrow.mapArrow.obj E) n r
        (Cell.target E.left.right n x)) =
      Cell.target (coneSquare (comparisonMap E)) n
        (Cell.upper ((Arrow.rightFunc ⋙ Arrow.rightFunc).mapArrow.mapArrow.obj E) n r x) := rfl

/-- The original upper/upper cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:98"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_upper_upper (n : ℕ) (r t : unitInterval)
    (x : E.left.right.left.right.space n) :
    (interchangeIso E).hom.map n
      (Cell.upper (totalFunctor.mapArrow.mapArrow.obj E) n r
        (Cell.upper E.left.right n t x)) =
      Cell.upper (coneSquare (comparisonMap E)) n t
        (Cell.upper ((Arrow.leftFunc ⋙ Arrow.rightFunc).mapArrow.mapArrow.obj E) n r x) := rfl

/-- The original upper/lower cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:107"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_upper_lower (n : ℕ) (r t : unitInterval)
    (x : E.left.right.right.left.space n) :
    (interchangeIso E).hom.map n
      (Cell.upper (totalFunctor.mapArrow.mapArrow.obj E) n r
        (Cell.lower E.left.right n t x)) =
      Cell.lower (coneSquare (comparisonMap E)) n t
        (Cell.upper ((Arrow.rightFunc ⋙ Arrow.leftFunc).mapArrow.mapArrow.obj E) n r x) := rfl

/-- The original upper/overlap cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:116"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_upper_overlap (n : ℕ) (r t v : unitInterval)
    (x : E.left.right.left.left.space n) :
    (interchangeIso E).hom.map n
      (Cell.upper (totalFunctor.mapArrow.mapArrow.obj E) n r
        (Cell.overlap E.left.right n t v x)) =
      Cell.overlap (coneSquare (comparisonMap E)) n t v
        (Cell.upper ((Arrow.leftFunc ⋙ Arrow.leftFunc).mapArrow.mapArrow.obj E) n r x) := rfl

/-- The original lower/target cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:125"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_lower_target (n : ℕ) (r : unitInterval)
    (x : E.right.left.right.right.space n) :
    (interchangeIso E).hom.map n
      (Cell.lower (totalFunctor.mapArrow.mapArrow.obj E) n r
        (Cell.target E.right.left n x)) =
      Cell.target (coneSquare (comparisonMap E)) n
        (Cell.lower ((Arrow.rightFunc ⋙ Arrow.rightFunc).mapArrow.mapArrow.obj E) n r x) := rfl

/-- The original lower/upper cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:134"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_lower_upper (n : ℕ) (r t : unitInterval)
    (x : E.right.left.left.right.space n) :
    (interchangeIso E).hom.map n
      (Cell.lower (totalFunctor.mapArrow.mapArrow.obj E) n r
        (Cell.upper E.right.left n t x)) =
      Cell.upper (coneSquare (comparisonMap E)) n t
        (Cell.lower ((Arrow.leftFunc ⋙ Arrow.rightFunc).mapArrow.mapArrow.obj E) n r x) := rfl

/-- The original lower/lower cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:143"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_lower_lower (n : ℕ) (r t : unitInterval)
    (x : E.right.left.right.left.space n) :
    (interchangeIso E).hom.map n
      (Cell.lower (totalFunctor.mapArrow.mapArrow.obj E) n r
        (Cell.lower E.right.left n t x)) =
      Cell.lower (coneSquare (comparisonMap E)) n t
        (Cell.lower ((Arrow.rightFunc ⋙ Arrow.leftFunc).mapArrow.mapArrow.obj E) n r x) := rfl

/-- The original lower/overlap cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:152"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_lower_overlap (n : ℕ) (r t v : unitInterval)
    (x : E.right.left.left.left.space n) :
    (interchangeIso E).hom.map n
      (Cell.lower (totalFunctor.mapArrow.mapArrow.obj E) n r
        (Cell.overlap E.right.left n t v x)) =
      Cell.overlap (coneSquare (comparisonMap E)) n t v
        (Cell.lower ((Arrow.leftFunc ⋙ Arrow.leftFunc).mapArrow.mapArrow.obj E) n r x) := rfl

/-- The original overlap/target cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:161"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_overlap_target (n : ℕ) (r s : unitInterval)
    (x : E.left.left.right.right.space n) :
    (interchangeIso E).hom.map n
      (Cell.overlap (totalFunctor.mapArrow.mapArrow.obj E) n r s
        (Cell.target E.left.left n x)) =
      Cell.target (coneSquare (comparisonMap E)) n
        (Cell.overlap ((Arrow.rightFunc ⋙ Arrow.rightFunc).mapArrow.mapArrow.obj E) n r s x) := rfl

/-- The original overlap/upper cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:170"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_overlap_upper (n : ℕ) (r s t : unitInterval)
    (x : E.left.left.left.right.space n) :
    (interchangeIso E).hom.map n
      (Cell.overlap (totalFunctor.mapArrow.mapArrow.obj E) n r s
        (Cell.upper E.left.left n t x)) =
      Cell.upper (coneSquare (comparisonMap E)) n t
        (Cell.overlap ((Arrow.leftFunc ⋙ Arrow.rightFunc).mapArrow.mapArrow.obj E) n r s x) := rfl

/-- The original overlap/lower cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:179"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_overlap_lower (n : ℕ) (r s t : unitInterval)
    (x : E.left.left.right.left.space n) :
    (interchangeIso E).hom.map n
      (Cell.overlap (totalFunctor.mapArrow.mapArrow.obj E) n r s
        (Cell.lower E.left.left n t x)) =
      Cell.lower (coneSquare (comparisonMap E)) n t
        (Cell.overlap ((Arrow.rightFunc ⋙ Arrow.leftFunc).mapArrow.mapArrow.obj E) n r s x) := rfl

/-- The original overlap/overlap cell exchanges its two complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareConeCells.lean:188"
  "adaptation" "Original sixteen actual quotient cells and four independent parameters."]
theorem interchange_overlap_overlap (n : ℕ) (r s t v : unitInterval)
    (x : E.left.left.left.left.space n) :
    (interchangeIso E).hom.map n
      (Cell.overlap (totalFunctor.mapArrow.mapArrow.obj E) n r s
        (Cell.overlap E.left.left n t v x)) =
      Cell.overlap (coneSquare (comparisonMap E)) n t v
        (Cell.overlap ((Arrow.leftFunc ⋙ Arrow.leftFunc).mapArrow.mapArrow.obj E) n r s x) := rfl

end Double
end Topology.LoopPrespectrum.StrictSquare
