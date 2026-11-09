/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeEventualHomotopy
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Original telescope homotopy groups as filtered colimits

In every homotopy degree, including zero, the unchanged homotopy set of an
original reduced telescope of T1 stages is a categorical filtered colimit of
the original stage homotopy sets and original transition maps. The cocone is
built from the actual stage inclusions. It is proved colimiting using the
finite-stage representability and eventual-equality theorems.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1)) (k n : ℕ)

/-- Original stage homotopy sets with the actual finite-transition maps. -/
def homotopyDiagram : ℕ ⥤ Type u where
  obj i := HomotopyGroup.Pi n ((E i).space k) ((E i).point k)
  map {i j} h := TypeCat.ofHom
    (HomotopyGroup.map ((transition E f i j (leOfHom h)).map k)
      ((transition E f i j (leOfHom h)).map_point k))
  map_id i := by
    ext a
    change HomotopyGroup.map ((transition E f i i le_rfl).map k)
      ((transition E f i i le_rfl).map_point k) a = a
    rw [transition_refl]
    exact HomotopyGroup.map_id a
  map_comp {i j l} h h' := by
    ext a
    change HomotopyGroup.map ((transition E f i l (leOfHom (h ≫ h'))).map k)
      ((transition E f i l (leOfHom (h ≫ h'))).map_point k) a = _
    rw [transition_comp E f i j l (leOfHom h) (leOfHom h')]
    exact HomotopyGroup.map_comp ((transition E f i j (leOfHom h)).map k)
      ((transition E f i j (leOfHom h)).map_point k)
      ((transition E f j l (leOfHom h')).map k)
      ((transition E f j l (leOfHom h')).map_point k) a

/-- The original stage inclusions form the canonical homotopy-set cocone. -/
def homotopyCocone : Cocone (homotopyDiagram E f k n) where
  pt := HomotopyGroup.Pi n (Space E f k) (point E f k)
  ι :=
    { app := fun i ↦ TypeCat.ofHom
        (HomotopyGroup.map ((inclusion E f i).map k) ((inclusion E f i).map_point k))
      naturality := fun i j h ↦ by
        ext a
        exact (inclusion_transition_homotopyGroupMap E f (leOfHom h) k n a).symm }

variable [∀ i, T1Space ((E i).space k)]

/-- The original homotopy-set cocone is genuinely colimiting, including degree zero. -/
def homotopyCoconeIsColimit : IsColimit (homotopyCocone E f k n) :=
  Types.FilteredColimit.isColimitOf _ _
    (fun a ↦ by
      obtain ⟨i, b, hb⟩ := exists_homotopyGroup_representative E f k n a
      exact ⟨i, b, hb.symm⟩)
    (fun i j a b hab ↦ by
      obtain ⟨N, hi, hj, hN⟩ := exists_eventual_homotopyGroup_eq E f k n a b hab
      exact ⟨N, homOfLE hi, homOfLE hj, hN⟩)

/-- The canonical filtered-colimit comparison with the unchanged original homotopy set. -/
def homotopyColimitIso : colimit (homotopyDiagram E f k n) ≅
    HomotopyGroup.Pi n (Space E f k) (point E f k) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (homotopyCoconeIsColimit E f k n)

/-- The canonical comparison preserves each actual original stage homotopy map. -/
@[reassoc (attr := simp)] theorem homotopyColimitIso_ι_hom (i : ℕ) :
    colimit.ι (homotopyDiagram E f k n) i ≫ (homotopyColimitIso E f k n).hom =
      TypeCat.ofHom
        (HomotopyGroup.map ((inclusion E f i).map k) ((inclusion E f i).map_point k)) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (homotopyCoconeIsColimit E f k n) i

end Topology.LoopPrespectrum.Telescope
