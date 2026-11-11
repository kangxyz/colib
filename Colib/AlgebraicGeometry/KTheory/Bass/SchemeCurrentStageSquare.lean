/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeSeedIterates
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentTransition

/-! # Original current-stage seed and normalized-stage compatibility

The whole original seed, independent loop times and literal association transports are
retained. This is the original equality of actual maps, not a stable-class replacement.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan
open FiniteParameterLooping IteratedLoopStrength FiniteLoopWords NormalizedStageMap
variable {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The original action on each unlooped finite cone stage. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeCurrentStageSquare.lean:36"
  "adaptation" "Original whole seed and fixed-order normalized transition square."]
def coneTrack (A : Track laurent.op coefficient F) (i : ℕ) :
    Track laurent.op coefficient (FiniteConeTopology.iterate squareFunctor i F) :=
  A.cones (L := laurent.op) (c := coefficient) squareFunctor
    (interchange (laurentProjection (.of (ULift.{u} ℤ))))
    (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ)))) i

/-- The unpermuted normalized transition is exactly the i-fold loop of the current cone seed. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeCurrentStageSquare.lean:49"
  "adaptation" "Original whole seed and fixed-order normalized transition square."]
def normalizedTransition (A : Track laurent.op coefficient F) (i : ℕ) :
    normalized squareFunctor i F ⟶ normalized squareFunctor (i + 1) F :=
  loopMap i (seed (coneTrack A i)) ≫ eqToHom (normalized_succ_eq squareFunctor i F)

private theorem adjacent_comp {C : Type*} [Category* C]
    {A B B' D E T : C} (h : B' = B) (s : A ⟶ B) (f : B ⟶ T)
    (e : A ⟶ D) (t : D ⟶ T) (k : T ⟶ E) (g : D ⟶ E)
    (hs : s ≫ f = e ≫ t) (ht : t ≫ k = g) :
    (s ≫ eqToHom h.symm) ≫ (eqToHom h ≫ f ≫ k) = e ≫ g := by
  subst B'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [← Category.assoc, hs, Category.assoc, ht]

/-- The unchanged stage map carries each actual current-stage seed to the unpermuted transition. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeCurrentStageSquare.lean:63"
  "adaptation" "Original whole seed and fixed-order normalized transition square."]
theorem currentTransition_stageMap (A : Track laurent.op coefficient F) (i : ℕ) :
    currentTransition A i ≫ stageMap squareFunctor (i + 1) F =
      stageMap squareFunctor i F ≫ normalizedTransition A i := by
  have h := seed_square (stageTrack A i) ((coneTrack A i).loops i)
    (stageMap squareFunctor i F)
    (stageMap_equivariant (L := laurent.op) (c := coefficient) squareFunctor
      (interchange (laurentProjection (.of (ULift.{u} ℤ))))
      (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ)))) A i)
  apply adjacent_comp (bass_succ_eq squareFunctor i F)
    (seed (stageTrack A i)) _ _ (seed ((coneTrack A i).loops i)) _ _ h
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ eqToHom (normalized_succ_eq squareFunctor i F))
      (seed_iteratedStrength (coneTrack A i) i))

end KTheory.Bass.SchemeNaturalSeed
