import PfaffianDescent.RelativeChosenMatrixCofactorEquality318
import PfaffianDescent.HilbertBurchFiniteFlatLift318
import PfaffianDescent.HilbertBurchRowLocalization318
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Flat.Stability

/-!
Apply local Artin-surface cofactor comparison to one chosen matrix at every
maximal ideal and reflect whole-ideal equality. No global regular pair,
scalar factor, or cofactor-ideal equality is assumed. Residual matrix
exactness and injectivity are explicit inputs here; localized base change
and the original flat quotient supply them in the subsequent consumers.
-/

noncomputable section
namespace AllCharacteristics
open LinearMap Matrix HilbertSurfaceDraft
universe u v w t

theorem cofactorIdeal_eq_of_localized_regularSurface_fibers318
    {S : Type u} {A : Type v} {ι : Type t}
    [CommRing S] [CommRing A] [Algebra S A] [Module.Flat S A]
    [Fintype ι] [DecidableEq ι]
    (I : Ideal S) [I.IsMaximal] (hI : IsNilpotent I)
    (J : Ideal A) (M : Matrix (Option ι) ι A) (a : Option ι → A)
    (hJa : J = Ideal.span (Set.range a))
    (hMrange : LinearMap.range M.mulVecLin = LinearMap.ker (rowFunctional008 a))
    (C : MaximalSpectrum A → Type w)
    [∀ P, CommRing (C P)] [∀ P, IsRegularLocalRing (C P)]
    (π : ∀ P : MaximalSpectrum A, Localization.AtPrime P.asIdeal →+* C P)
    (hπ : ∀ P, Function.Surjective (π P))
    (hker : ∀ P, RingHom.ker (π P) =
      I.map (algebraMap S (Localization.AtPrime P.asIdeal)))
    (hdim : ∀ P, ringKrullDim (C P) = 2)
    (hartin : ∀ P, IsArtinianRing
      ((C P) ⧸ (J.map (algebraMap A (Localization.AtPrime P.asIdeal))).map (π P)))
    (hresinj : ∀ P, Function.Injective
      (((M.map (algebraMap A (Localization.AtPrime P.asIdeal))).map (π P)).mulVecLin))
    (hresrange : ∀ P,
      LinearMap.range
        (((M.map (algebraMap A (Localization.AtPrime P.asIdeal))).map (π P)).mulVecLin) =
      LinearMap.ker (rowFunctional008
        (fun i => π P (algebraMap A (Localization.AtPrime P.asIdeal) (a i))))) :
    Ideal.span (Set.range (PfaffianDescent.hilbertBurchCofactors318 M)) = J := by
  apply Ideal.eq_of_localization_maximal
  intro P hP
  letI : P.IsMaximal := hP
  let PM : MaximalSpectrum A := ⟨P, hP⟩
  let B := Localization.AtPrime P
  let loc : A →+* B := algebraMap A B
  letI : Module.Flat S B := Module.Flat.trans S A B
  letI : IsArtinianRing ((C PM) ⧸ (J.map loc).map (π PM)) := hartin PM
  have hJloc : J.map loc = Ideal.span (Set.range (fun i => loc (a i))) := by
    rw [hJa, Ideal.map_span, ← Set.range_comp]
    rfl
  have hex : Function.Exact M.mulVecLin (rowFunctional008 a) :=
    LinearMap.exact_iff.mpr hMrange.symm
  have hexloc : Function.Exact (M.map loc).mulVecLin
      (rowFunctional008 (fun i => loc (a i))) :=
    exact_matrix_row_map_localization008 (S := B) P.primeCompl M a hex
  have hMloc : LinearMap.range (M.map loc).mulVecLin =
      LinearMap.ker (rowFunctional008 (fun i => loc (a i))) :=
    (LinearMap.exact_iff.mp hexloc).symm
  have hlocal : Ideal.span
      (Set.range (PfaffianDescent.hilbertBurchCofactors318 (M.map loc))) = J.map loc :=
    cofactorIdeal_eq_of_relative_presentation_and_exact_fiber318
      I hI (π PM) (hπ PM) (hker PM) (hdim PM) (J.map loc)
      (M.map loc) (fun i => loc (a i)) hJloc hMloc (hresinj PM) (hresrange PM)
  rw [PfaffianDescent.hilbertBurchCofactorIdeal_map318]
  exact hlocal

end AllCharacteristics
end
