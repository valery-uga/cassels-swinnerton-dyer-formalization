import PfaffianDescent.VoisinFieldBaseChangeFiniteFreeCover

/-!
# Finite affine trivializing covers from local trivializations

The fixed-linear-system construction consumes a finite affine cover with a
uniform finite free rank. Compactness of the underlying scheme extracts this
finite cover from pointwise affine local trivializations.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

/-- A compact scheme module locally isomorphic to the same finite free module
on affine neighborhoods admits a finite affine trivializing cover in the
exact form used by the global-sections base-change theorem. -/
theorem exists_finiteFreeAffineCover_of_localTrivializations
    {X : Scheme.{u}} [CompactSpace X] (M : X.Modules)
    (I : Type u) [Fintype I]
    (hlocal : ∀ x : X, ∃ U : X.Opens,
      x ∈ U ∧ IsAffine (U : Scheme.{u}) ∧
        Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅
          M.over U)) :
    ∃ (C : SchemeModuleFiniteFreeAffineCover M I),
      Nonempty (Fintype C.ι) := by
  let T := {U : X.Opens // IsAffine (U : Scheme.{u}) ∧
    Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)}
  have hcover : (Set.univ : Set X) ⊆ ⋃ t : T, (t.1 : Set X) := by
    intro x _
    obtain ⟨U, hxU, hUa, hUt⟩ := hlocal x
    exact Set.mem_iUnion.mpr ⟨⟨U, hUa, hUt⟩, hxU⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun t : T => (t.1 : Set X)) (fun t => t.1.2) hcover
  let J := {t : T // t ∈ S}
  letI : Fintype J := Finset.fintypeCoeSort S
  let C : SchemeModuleFiniteFreeAffineCover M I := {
    ι := J
    U := fun j => j.1.1
    covers := by
      apply le_antisymm le_top
      intro x _
      have hx := hS (Set.mem_univ x)
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx
      obtain ⟨htS, hxt⟩ := Set.mem_iUnion.mp ht
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨t, htS⟩, hxt⟩
    affine := fun j => j.1.2.1
    trivialization := fun j => Classical.choice j.1.2.2
  }
  exact ⟨C, ⟨inferInstance⟩⟩

/-- Field extension commutes with global sections of a locally free module
of a fixed finite rank on a compact separated scheme. The map here is the
literal pullback map used by the fixed-linear-system descent endpoint. -/
theorem globalSectionsFieldBaseChangeLinearMap_bijective_of_localTrivializations
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} [CompactSpace X]
    (base : X ⟶ Spec (.of K)) [IsSeparated base]
    (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (I : Type u) [Fintype I]
    (hlocal : ∀ x : X, ∃ U : X.Opens,
      x ∈ U ∧ IsAffine (U : Scheme.{u}) ∧
        Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅
          M.over U)) :
    Function.Bijective
      (schemeModuleGlobalSectionsFieldBaseChangeLinearMap (L := L) base M) := by
  classical
  obtain ⟨C, ⟨hfinite⟩⟩ :=
    exists_finiteFreeAffineCover_of_localTrivializations M I hlocal
  letI : Fintype C.ι := hfinite
  exact C.globalSectionsFieldBaseChangeLinearMap_bijective (L := L) base M

end

end PfaffianDescent
