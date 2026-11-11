/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientTelescope
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeSeedNaturality
public import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterOpenTrack
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientRestriction
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalFullOpenTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalLocalizationTelescopeMaps

/-! # The actual parameter full-open arrow on the original Bass telescope -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- Realize the original full-open parameter restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterFullRestrictionTelescope.lean:28"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
def parameterRestrictionMap : parameterDiagram Q ⟶ parameterDiagram P :=
  Functor.whiskerRight (parameterFullRestriction f) prespectrumFunctor

/-- The full-open parameter restriction preserves the same original Bass seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterFullRestrictionTelescope.lean:32"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem parameterRestriction_seed :
    KTheory.Bass.SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left) ≫
        (strictDiagramFunctor squareFunctor).map (parameterRestrictionMap f) =
      parameterRestrictionMap f ≫
        KTheory.Bass.SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack P.left) := by
  apply KTheory.Bass.SchemeNaturalSeed.seed_square
  have h := (ParameterLaurentTrack.changeWeak_equivariant f.left).comp
    (ParameterLaurentTrack.openRestriction_equivariant f.left)
  simpa only [parameterRestrictionMap, parameterFullRestriction,
    Functor.whiskerRight_comp] using h

/-- Original full-open restriction at each parameter Bass stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterFullRestrictionTelescope.lean:44"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
def parameterFiniteRestriction (i : ℕ) :
    (strictDiagramIterate squareFunctor i).obj (parameterDiagram Q) ⟶
      (strictDiagramIterate squareFunctor i).obj (parameterDiagram P) :=
  (strictDiagramIterate squareFunctor i).map (parameterRestrictionMap f)

/-- The original seed square gives every actual finite restriction transition. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterFullRestrictionTelescope.lean:50"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem parameterFiniteRestriction_transition (i : ℕ) :
    parameterFiniteRestriction f i ≫ strictDiagramTransition squareFunctor
        (KTheory.Bass.SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack P.left)) i =
      strictDiagramTransition squareFunctor
        (KTheory.Bass.SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left)) i ≫
        parameterFiniteRestriction f (i + 1) :=
  (strictDiagramTransition_map squareFunctor
    (KTheory.Bass.SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left))
    (KTheory.Bass.SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack P.left))
    (parameterRestrictionMap f) (parameterRestriction_seed f) i).symm

/-- The complete original parameter telescope restricts to the actual open product telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterFullRestrictionTelescope.lean:62"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
def parameterTelescopeRestriction : parameterTelescope Q.left ⟶ parameterTelescope P.left :=
  Telescope.diagramMap
    (fun i => (strictDiagramIterate squareFunctor i).obj (parameterDiagram Q))
    (fun i => (strictDiagramIterate squareFunctor i).obj (parameterDiagram P))
    (strictDiagramTransition squareFunctor
      (KTheory.Bass.SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left)))
    (strictDiagramTransition squareFunctor
      (KTheory.Bass.SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack P.left)))
    (parameterFiniteRestriction f) (parameterFiniteRestriction_transition f)

/-- The original global full-open factorization is the same actual Model arrow. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterFullRestrictionTelescope.lean:73"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem globalFullRestriction_factor :
    openRowChangeWeak f ≫ globalOpenRestriction f = globalOpenFineRestriction f := by
  apply NatTrans.ext
  funext a
  apply WideSubcategory.hom_ext
  apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
  change (𝟭 _) ⋙ ((globalOpenFineRestriction f).app a).hom.toFunctor = _
  exact CategoryTheory.Functor.id_comp _

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

