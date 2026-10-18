import PfaffianDescent.LiftChosenResiduePresentation318
import PfaffianDescent.HilbertBurchSemilocalIdealPresentation318
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Finiteness.Basic

/-!
Construct the whole relative free ideal presentation over a local Artin
coefficient ring when the actual residue ring is a semilocal regular surface.
All original ideal, generator, basis, and matrix data are constructed.
-/

noncomputable section
namespace AllCharacteristics
open Module LinearMap Matrix HilbertSurfaceDraft
universe u v w

theorem exists_actual_artin_semilocal_surface_presentation318
    {S : Type u} {A : Type v} {A₀ : Type w}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A]
    [IsLocalRing S] [IsArtinianRing S] [Module.Flat S A]
    [IsNoetherianRing A₀] [Finite (MaximalSpectrum A₀)]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = (IsLocalRing.maximalIdeal S).map (algebraMap S A))
    (hreg : ∀ (p : Ideal A₀) (_ : p.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime p))
    (hdim : ∀ (p : Ideal A₀) (_ : p.IsMaximal),
      ringKrullDim (Localization.AtPrime p) = 2)
    (J : Ideal A) [Module.Flat S (A ⧸ J)] [Module.Finite S (A ⧸ J)] :
    ∃ (m : ℕ) (a : Option (Fin m) → A)
      (M : Matrix (Option (Fin m)) (Fin m) A),
      J = Ideal.span (Set.range a) ∧ Function.Injective M.mulVecLin ∧
      LinearMap.range M.mulVecLin = LinearMap.ker (rowFunctional008 a) := by
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
  obtain ⟨m, a₀, M₀, hJ₀, hM₀inj, hM₀range⟩ :=
    PfaffianDescent.semilocalSurface_exists_wholeIdeal_exact_option_presentation018 J₀ hreg hdim
  obtain ⟨M, a, _, _, hJa, hMinj, hMrange⟩ :=
    exists_actual_relative_presentation_lifting_residue318 πS hπ
      (IsLocalRing.maximalIdeal S) hnil hker J M₀ a₀ hJ₀ hM₀inj hM₀range
  exact ⟨m, a, M, hJa, hMinj, hMrange⟩

end AllCharacteristics
end
