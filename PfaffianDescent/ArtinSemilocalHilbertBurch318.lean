import PfaffianDescent.ArtinSemilocalSurfacePresentation318
import PfaffianDescent.ChosenPresentationReduction318
import PfaffianDescent.HilbertBurchSemilocalResidueCofactor318
import PfaffianDescent.CofactorExactnessOfIdealEquality318

/-!
Intrinsic semilocal Hilbert--Burch existence for an arbitrary original
finite-flat ideal family on a relative surface over a local Artin ring.
No presentation, syzygy basis, scalar normalization, cofactor equality,
or family of localized residue maps is a hypothesis.
-/

noncomputable section
namespace AllCharacteristics
open Module LinearMap Matrix HilbertSurfaceDraft
universe u v w

theorem exists_actual_artin_semilocal_hilbertBurch_resolution318
    {S : Type u} {A : Type v} {A₀ : Type w}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A]
    [IsLocalRing S] [IsArtinianRing S] [hFlat : Module.Flat S A]
    [IsNoetherianRing A₀] [Finite (MaximalSpectrum A₀)]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = (IsLocalRing.maximalIdeal S).map (algebraMap S A))
    (hreg : ∀ (p : Ideal A₀) (_ : p.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime p))
    (hdim : ∀ (p : Ideal A₀) (_ : p.IsMaximal),
      ringKrullDim (Localization.AtPrime p) = 2)
    (J : Ideal A) [hFlatQ : Module.Flat S (A ⧸ J)] [hFiniteQ : Module.Finite S (A ⧸ J)] :
    ∃ (m : ℕ) (M : Matrix (Option (Fin m)) (Fin m) A),
      Function.Injective M.mulVecLin ∧
      J = Ideal.span (Set.range (PfaffianDescent.hilbertBurchCofactors318 M)) ∧
      LinearMap.range M.mulVecLin = LinearMap.ker
        (rowFunctional008 (PfaffianDescent.hilbertBurchCofactors318 M)) := by
  letI : Algebra S A₀ := (π.comp (algebraMap S A)).toAlgebra
  let πS : A →ₐ[S] A₀ := { __ := π, commutes' := fun _ => rfl }
  let J₀ := J.map π
  let q : (A ⧸ J) →ₐ[S] (A₀ ⧸ J₀) :=
    Ideal.quotientMapₐ J₀ πS Ideal.le_comap_map
  have hq : Function.Surjective q :=
    Ideal.quotientMap_surjective (H := Ideal.le_comap_map) hπ
  letI : Module.Finite S (A₀ ⧸ J₀) := Module.Finite.of_surjective q.toLinearMap hq
  letI : IsArtinianRing (A₀ ⧸ J₀) := IsArtinianRing.of_finite S (A₀ ⧸ J₀)
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal S) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥]
    · exact IsArtinianRing.isNilpotent_jacobson_bot
    · exact bot_ne_top
  obtain ⟨m, a, M, hJa, hMinj, hMrange⟩ :=
    exists_actual_artin_semilocal_surface_presentation318 π hπ hker hreg hdim J
  obtain ⟨hresinj, hresrange⟩ := chosen_idealPresentation_reduction_exact318
    π hπ (IsLocalRing.maximalIdeal S) hker J a hJa M hMinj hMrange
  have hJcof : J = Ideal.span
      (Set.range (PfaffianDescent.hilbertBurchCofactors318 M)) :=
    (cofactorIdeal_eq_of_relative_presentation_and_regularSurface_residue020
      (IsLocalRing.maximalIdeal S) hnil π hπ hker J M a hJa hMrange
      hresinj hresrange hreg hdim).symm
  have hcofexact := cofactor_exact_of_original_presentation_and_ideal_equality318
    J M a hJa hMrange hJcof
  exact ⟨m, M, hMinj, hJcof, hcofexact⟩

/-- The intrinsic construction in the coefficient form consumed by the
finite-flat matrix-lifting theorem: every relation comes from the actual
chosen matrix. The ideal can be an arbitrary non-lci finite-flat family. -/
theorem exists_actual_artin_semilocal_hilbertBurch318
    {S : Type u} {A : Type v} {A₀ : Type w}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A]
    [IsLocalRing S] [IsArtinianRing S] [hFlat : Module.Flat S A]
    [IsNoetherianRing A₀] [Finite (MaximalSpectrum A₀)]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = (IsLocalRing.maximalIdeal S).map (algebraMap S A))
    (hreg : ∀ (p : Ideal A₀) (_ : p.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime p))
    (hdim : ∀ (p : Ideal A₀) (_ : p.IsMaximal),
      ringKrullDim (Localization.AtPrime p) = 2)
    (J : Ideal A) [hFlatQ : Module.Flat S (A ⧸ J)] [hFiniteQ : Module.Finite S (A ⧸ J)] :
    ∃ (m : ℕ) (M : Matrix (Option (Fin m)) (Fin m) A),
      J = Ideal.span (Set.range (PfaffianDescent.hilbertBurchCofactors318 M)) ∧
      (∀ a : Option (Fin m) → A,
        (∑ i, a i * PfaffianDescent.hilbertBurchCofactors318 M i) = 0 →
        ∃ b : Fin m → A, ∀ i, a i = ∑ j, M i j * b j) := by
  obtain ⟨m, M, _, hJcof, hcofexact⟩ :=
    exists_actual_artin_semilocal_hilbertBurch_resolution318 π hπ hker hreg hdim J
  refine ⟨m, M, hJcof, fun a ha => ?_⟩
  have hker : a ∈ LinearMap.ker
      (rowFunctional008 (PfaffianDescent.hilbertBurchCofactors318 M)) := by
    change (∑ i, PfaffianDescent.hilbertBurchCofactors318 M i * a i) = 0
    simpa only [mul_comm] using ha
  rw [← hcofexact] at hker
  obtain ⟨b, hb⟩ := hker
  exact ⟨b, fun i => (congrFun hb i).symm⟩

end AllCharacteristics
end
