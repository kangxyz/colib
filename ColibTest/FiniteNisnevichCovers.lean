module

import Colib.AlgebraicGeometry.Sites.Smooth.FiniteCovers

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.SmoothSite

universe u v

noncomputable section

variable {S : Scheme.{u}}

-- The chosen binary coproduct is the actual native scheme disjoint union.
example (X Y : SmoothSite S) : (coproduct X Y).left = (X.left ⨿ Y.left) := rfl

example (X Y : SmoothSite S) : IsFinite (coproductInl X Y).left := inferInstance

example (X Y : SmoothSite S) : IsClosedImmersion (coproductInr X Y).left := inferInstance

example : HasBinaryCoproducts (SmoothSite S) := inferInstance

-- The zero-index object is the empty scheme, without a nonempty base hypothesis.
example : (finiteCoproduct (S := S) (fun i : Fin 0 => Fin.elim0 i)).left =
    (∅ : Scheme.{u}) := rfl

-- An empty family covers an empty target; there is no forced positive size.
example {X : SmoothSite S} [IsEmpty X.left] :
    Presieve.singleton (finiteCoproductDesc (X := X)
      (Y := fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i)).left ∈
      Nisnevich.precoverage X.left := by
  apply finiteCoproductDesc_mem_precoverage
  rw [Nisnevich.ofArrows_mem_precoverage_iff]
  exact ⟨fun i => Fin.elim0 i, fun x => isEmptyElim x⟩

-- The original indexing universe is independent of the scheme universe.
example {X : SmoothSite S} [IsNoetherian X.left] {ι : Type v}
    {Y : ι → SmoothSite S} (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows (fun i => (Y i).left) (fun i => (f i).left) ∈
      Nisnevich.precoverage X.left) : FiniteNisnevichCoverNormalization f :=
  normalizeFiniteNisnevichCoverOfMem f hf

-- Every normalized component still has the original map, not a replacement arrow.
example {X : SmoothSite S} {ι : Type v} {Y : ι → SmoothSite S}
    {f : ∀ i, Y i ⟶ X} (N : FiniteNisnevichCoverNormalization f) (i : Fin N.size) :
    N.inclusion i ≫ N.map = f (N.index i) := N.inclusion_map i

example {X : SmoothSite S} {ι : Type v} {Y : ι → SmoothSite S}
    {f : ∀ i, Y i ⟶ X} (N : FiniteNisnevichCoverNormalization f) :
    Function.Injective N.index := N.injective_index

-- The actual singleton map retains residue-field isomorphisms at all target points.
example {X : SmoothSite S} {ι : Type v} {Y : ι → SmoothSite S}
    {f : ∀ i, Y i ⟶ X} (N : FiniteNisnevichCoverNormalization f) (x : X.left) :
    ∃ y : N.total.left, N.map.left y = x ∧ IsIso (N.map.left.residueFieldMap y) :=
  N.residueFieldLifting x

example {X : SmoothSite S} {ι : Type v} {Y : ι → SmoothSite S}
    {f : ∀ i, Y i ⟶ X} (N : FiniteNisnevichCoverNormalization f) :
    Presieve.singleton N.map.left ∈ Nisnevich.precoverage X.left := N.mem_precoverage

-- Finite extraction requires local finite type, not etaleness or reducedness of the base.
example {X : Scheme.{u}} [IsNoetherian X] {ι : Type v} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, LocallyOfFiniteType (f i)]
    (hf : ∀ x : X, ∃ (i : ι) (y : Y i),
      f i y = x ∧ IsIso ((f i).residueFieldMap y)) :
    ∃ s : Finset ι, ∀ x : X, ∃ i ∈ s, ∃ y : Y i,
      f i y = x ∧ IsIso ((f i).residueFieldMap y) :=
  Nisnevich.exists_finset_residueFieldLifting f hf
