import PfaffianDescent.HilbertBurchSemilocalOptionMatrix318

/-!
Constructs the whole generator row and exact rectangular matrix for an
arbitrary finite-colength ideal on a semilocal regular surface. A zero
generator pads the finite family to the actual Option indexing, so no
positive-generator-count premise is hidden in the construction.
-/

noncomputable section

namespace PfaffianDescent

open AllCharacteristics.HilbertSurfaceDraft

theorem semilocalSurface_exists_wholeIdeal_exact_option_presentation018
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    [Finite (MaximalSpectrum R)] (J : Ideal R) [IsArtinianRing (R ⧸ J)]
    (hreg : ∀ (p : Ideal R) (_ : p.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime p))
    (hdim : ∀ (p : Ideal R) (_ : p.IsMaximal),
      ringKrullDim (Localization.AtPrime p) = 2) :
    ∃ (m : ℕ) (a : Option (Fin m) → R)
      (M : Matrix (Option (Fin m)) (Fin m) R),
      J = Ideal.span (Set.range a) ∧ Function.Injective M.mulVecLin ∧
      LinearMap.range M.mulVecLin = LinearMap.ker (rowFunctional008 a) := by
  obtain ⟨m, t, ht⟩ := Module.Finite.exists_fin (R := R) (M := J)
  let a₀ : Fin m → R := fun j ↦ (t j : R)
  have hJ₀ : J = Ideal.span (Set.range a₀) := by
    have h := congrArg (Submodule.map J.subtype) ht
    have hfamily : (⇑(Submodule.subtype J) ∘ t : Fin m → R) = a₀ := by
      funext j
      rfl
    apply Ideal.ext
    intro x
    have hx := congrArg (fun U : Submodule R R => x ∈ U) h.symm
    simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      Submodule.range_subtype, Ideal.submodule_span_eq, hfamily] using Iff.of_eq hx
  let a : Option (Fin m) → R := fun i ↦ Option.elim i 0 a₀
  have hspan : Ideal.span (Set.range a) = Ideal.span (Set.range a₀) := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      cases i with
      | none => exact Ideal.zero_mem _
      | some j => exact Ideal.subset_span (Set.mem_range_self j)
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Ideal.subset_span ⟨some j, rfl⟩
  have hJ : J = Ideal.span (Set.range a) := hJ₀.trans hspan.symm
  letI : IsArtinianRing (R ⧸ Ideal.span (Set.range a)) := by
    rw [← hJ]
    infer_instance
  obtain ⟨M, hMinj, hMrange⟩ := semilocalSurface_exists_exact_option_matrix017 m a hreg hdim
  exact ⟨m, a, M, hJ, hMinj, hMrange⟩

end PfaffianDescent
