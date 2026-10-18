import PfaffianDescent.HilbertBurchResidueMaximalLocalization318
import PfaffianDescent.SemilocalChosenMatrixCofactorEquality318
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Artinian.Ring

/-!
Construct all localized residue data required for cofactor comparison from
one original residue surjection and one actual exact residue matrix. The
regularity/dimension assumptions concern the actual residue local rings.
-/

noncomputable section

namespace AllCharacteristics

open Matrix HilbertSurfaceDraft PfaffianDescent

theorem cofactorIdeal_eq_of_relative_presentation_and_regularSurface_residue020
    {S A A₀ ι : Type*}
    [CommRing S] [CommRing A] [CommRing A₀]
    [Algebra S A] [Module.Flat S A]
    [Fintype ι] [DecidableEq ι]
    (I : Ideal S) [I.IsMaximal] (hI : IsNilpotent I)
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = I.map (algebraMap S A))
    (J : Ideal A) [IsArtinianRing (A₀ ⧸ J.map π)]
    (M : Matrix (Option ι) ι A) (a : Option ι → A)
    (hJa : J = Ideal.span (Set.range a))
    (hMrange : LinearMap.range M.mulVecLin = LinearMap.ker (rowFunctional008 a))
    (hresinj : Function.Injective (M.map π).mulVecLin)
    (hresrange : LinearMap.range (M.map π).mulVecLin =
      LinearMap.ker (rowFunctional008 (fun i => π (a i))))
    (hreg : ∀ (P : Ideal A₀) (_ : P.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime P))
    (hdim : ∀ (P : Ideal A₀) (_ : P.IsMaximal),
      ringKrullDim (Localization.AtPrime P) = 2) :
    Ideal.span (Set.range (hilbertBurchCofactors318 M)) = J := by
  have hNil : IsNilpotent (RingHom.ker π) := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    rw [hker, ← Ideal.map_pow, hn]
    simp only [Ideal.zero_eq_bot, Ideal.map_bot]
  let Q (P : MaximalSpectrum A) := residueMaximal019 π hπ hNil P
  let C (P : MaximalSpectrum A) := Localization.AtPrime (Q P).asIdeal
  let ρ (P : MaximalSpectrum A) : Localization.AtPrime P.asIdeal →+* C P :=
    localizedResidueMap019 π hπ hNil P
  letI : ∀ P, IsRegularLocalRing (C P) := fun P =>
    hreg (Q P).asIdeal (Q P).isMaximal
  refine cofactorIdeal_eq_of_localized_regularSurface_fibers318
    I hI J M a hJa hMrange C ρ ?_ ?_ ?_ ?_ ?_ ?_
  · intro P
    exact localizedResidueMap_surjective019 π hπ hNil P
  · intro P
    rw [localizedResidueMap_ker019, hker, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  · intro P
    exact hdim (Q P).asIdeal (Q P).isMaximal
  · intro P
    let loc := algebraMap A (Localization.AtPrime P.asIdeal)
    let loc₀ := algebraMap A₀ (C P)
    have heq : (J.map loc).map (ρ P) = (J.map π).map loc₀ := by
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      apply RingHom.ext
      intro x
      exact localizedResidueMap_algebraMap019 π hπ hNil P x
    rw [heq]
    exact IsArtinianRing.localization_artinian
      (Algebra.algebraMapSubmonoid (A₀ ⧸ J.map π) (Q P).asIdeal.primeCompl) _
  · intro P
    have hMmap :
        ((M.map (algebraMap A (Localization.AtPrime P.asIdeal))).map (ρ P)) =
          (M.map π).map (algebraMap A₀ (C P)) := by
      ext i j
      exact localizedResidueMap_algebraMap019 π hπ hNil P (M i j)
    rw [hMmap]
    exact injective_matrix_map_localization007 (Q P).asIdeal.primeCompl
      (M.map π) hresinj
  · intro P
    have hMmap :
        ((M.map (algebraMap A (Localization.AtPrime P.asIdeal))).map (ρ P)) =
          (M.map π).map (algebraMap A₀ (C P)) := by
      ext i j
      exact localizedResidueMap_algebraMap019 π hπ hNil P (M i j)
    have hrow :
        (fun i => ρ P (algebraMap A (Localization.AtPrime P.asIdeal) (a i))) =
          (fun i => algebraMap A₀ (C P) (π (a i))) := by
      funext i
      exact localizedResidueMap_algebraMap019 π hπ hNil P (a i)
    rw [hMmap, hrow]
    exact (LinearMap.exact_iff.mp
      (exact_matrix_row_map_localization008 (Q P).asIdeal.primeCompl
        (M.map π) (fun i => π (a i))
        (LinearMap.exact_iff.mpr hresrange.symm))).symm

end AllCharacteristics

end
