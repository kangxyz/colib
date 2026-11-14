/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleTraceNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Sequence

/-!
# The native trace on the restricted Kummer complex

This constructs the Gm trace and the trace morphism of the genuine restricted
Kummer complex. It does not identify the multiplicative trace with algebraic norm.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Stacks.EtaleCohomology
open Stacks.Kummer
variable {S Y : Scheme.{u}} (g : Y ⟶ S) [Etale g]

/-- Étale restriction does not change the global-function units on each object.
Both sides evaluate to units of global functions on the same scheme. -/
def etaleRestrictionMultiplicativeSheafIso :
    (etaleRestriction.{u, 0} g).obj (multiplicativeSheaf.{u, 0} S) ≅
      multiplicativeSheaf.{u, 0} Y :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

/-- Actual native additive-sheaf trace transported to Gm_Y. On split charts this
should be product of pullbacks because Gm is represented additively.
It is NOT YET identified with the algebraic determinant norm. -/
def finiteEtaleMultiplicativeTrace [IsFinite g] :
    (etaleAbelianDirectImage.{u, 0} g).obj (multiplicativeSheaf.{u, 0} Y) ⟶
      multiplicativeSheaf.{u, 0} S :=
  (etaleAbelianDirectImage.{u, 0} g).map
    (etaleRestrictionMultiplicativeSheafIso g).inv ≫
      finiteEtaleTrace g (multiplicativeSheaf.{u, 0} S)

/-- Genuine map from the pushed restricted Kummer complex to the base Kummer
complex. This does not take either commutative square as a hypothesis.
The remaining comparison with the Kummer complex on Y is separate. -/
def restrictedKummerTraceMorphism [IsFinite g] (n : ℕ) :
    ((kummerSequence.{u, 0} S n).map
      (etaleRestriction.{u, 0} g ⋙ etaleAbelianDirectImage.{u, 0} g)) ⟶
        kummerSequence.{u, 0} S n where
  τ₁ := finiteEtaleTrace g (kummerSequence.{u, 0} S n).X₁
  τ₂ := finiteEtaleTrace g (kummerSequence.{u, 0} S n).X₂
  τ₃ := finiteEtaleTrace g (kummerSequence.{u, 0} S n).X₃
  comm₁₂ := (finiteEtaleTrace_naturality g (kummerSequence.{u, 0} S n).f).symm
  comm₂₃ := (finiteEtaleTrace_naturality g (kummerSequence.{u, 0} S n).g).symm

end Stacks.EtaleCohomology
end
