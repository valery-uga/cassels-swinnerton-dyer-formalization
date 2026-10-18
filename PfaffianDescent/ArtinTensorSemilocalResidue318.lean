import PfaffianDescent.SemilocalResidueReduction318
import PfaffianDescent.HilbertBurchFiniteSupportLocalSurfaceTransport318
import PfaffianDescent.ActualArtinianQuotientLocalizationIso
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.HopkinsLevitzki
import PfaffianDescent.LocalizedQuotientBaseFlat318

/-!
Canonical residue map for the original Artin-base
ambient algebra and the ring properties needed by intrinsic semilocal
Hilbert--Burch. Local surface properties are assumed only on the actual
residue support; finite prime avoidance supplies all maximal localizations.
-/
noncomputable section
namespace PfaffianDescent
open scoped TensorProduct
universe u

abbrev artinTensorResidueRing318
    (S A : Type u) [CommRing S] [CommRing A] [IsLocalRing S] [Algebra S A] :=
  IsLocalRing.ResidueField S ⊗[S] A

def artinTensorResidueMap318
    (S A : Type u) [CommRing S] [CommRing A] [IsLocalRing S] [Algebra S A] :
    A →+* artinTensorResidueRing318 S A :=
  (affineTensorFiberReduction174 (R := S) (S := IsLocalRing.ResidueField S)
    (A := A)).toRingHom

theorem artinTensorResidueMap_surjective318
    (S A : Type u) [CommRing S] [CommRing A] [IsLocalRing S] [Algebra S A] :
    Function.Surjective (artinTensorResidueMap318 S A) :=
  affineTensorFiberReduction174_surjective (R := S) (S := IsLocalRing.ResidueField S)
    IsLocalRing.residue_surjective

theorem artinTensorResidueMap_ker318
    (S A : Type u) [CommRing S] [CommRing A] [IsLocalRing S] [Algebra S A] :
    RingHom.ker (artinTensorResidueMap318 S A) =
      (IsLocalRing.maximalIdeal S).map (algebraMap S A) := by
  simpa only [artinTensorResidueMap318, IsLocalRing.ResidueField.algebraMap_eq,
    IsLocalRing.ker_residue] using
    affineTensorFiberReduction174_kernel (R := S) (S := IsLocalRing.ResidueField S)
      (A := A) IsLocalRing.residue_surjective

theorem artinTensorResidueMap_nilpotent318
    (S A : Type u) [CommRing S] [CommRing A] [IsLocalRing S]
    [IsArtinianRing S] [Algebra S A] :
    IsNilpotent (RingHom.ker (artinTensorResidueMap318 S A)) := by
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal S) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥]
    · exact IsArtinianRing.isNilpotent_jacobson_bot
    · exact bot_ne_top
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  rw [artinTensorResidueMap_ker318, ← Ideal.map_pow, hn]
  simp only [Ideal.zero_eq_bot, Ideal.map_bot]

/-- Finite type of the original affine algebra supplies Noetherianity of
its ACTUAL tensor residue without a separate residual-ring hypothesis. -/
theorem artinTensorResidueRing_noetherian318
    (S A : Type u) [CommRing S] [CommRing A] [IsLocalRing S]
    [IsArtinianRing S] [Algebra S A] [Algebra.FiniteType S A] :
    IsNoetherianRing (artinTensorResidueRing318 S A) := by
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing S A
  exact isNoetherianRing_of_surjective A _ (artinTensorResidueMap318 S A)
    (artinTensorResidueMap_surjective318 S A)

/-- Original finite coefficient quotients and their actual tensor residues
are Artinian. No finite support assumption is needed as an input. -/
theorem artinTensorResidueQuotient_artinian318
    (S A : Type u) [CommRing S] [CommRing A] [IsLocalRing S]
    [IsArtinianRing S] [Algebra S A] (J : Ideal A)
    [Module.Finite S (A ⧸ J)] :
    IsArtinianRing (artinTensorResidueRing318 S A ⧸
      J.map (artinTensorResidueMap318 S A)) := by
  let πS := affineTensorFiberReduction174
    (R := S) (S := IsLocalRing.ResidueField S) (A := A)
  let J₀ := J.map πS.toRingHom
  let q : (A ⧸ J) →ₐ[S] (artinTensorResidueRing318 S A ⧸ J₀) :=
    Ideal.quotientMapₐ J₀ πS Ideal.le_comap_map
  have hq : Function.Surjective q :=
    Ideal.quotientMap_surjective (H := Ideal.le_comap_map)
      (artinTensorResidueMap_surjective318 S A)
  letI : Module.Finite S (artinTensorResidueRing318 S A ⧸ J₀) :=
    Module.Finite.of_surjective q.toLinearMap hq
  change IsArtinianRing (artinTensorResidueRing318 S A ⧸ J₀)
  exact IsArtinianRing.of_finite S (artinTensorResidueRing318 S A ⧸ J₀)

/-- Every necessary residual-ring property is derived for the CONSTRUCTED
residual semilocalization from original residual support local rings. -/
theorem finiteSupportResidueLocalization_surfaceProperties318
    {A A₀ : Type u} [CommRing A] [CommRing A₀] [IsNoetherianRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    (t : Finset (MaximalSpectrum A)) (ht : t.Nonempty)
    (hreg : ∀ Q ∈ residueFiniteSupport318 π hπ hker t,
      IsRegularLocalRing (Localization.AtPrime Q.asIdeal))
    (hdim : ∀ Q ∈ residueFiniteSupport318 π hπ hker t,
      ringKrullDim (Localization.AtPrime Q.asIdeal) = 2) :
    IsNoetherianRing (Localization (finiteSupportDenominators001
      (residueFiniteSupport318 π hπ hker t))) ∧
    Finite (MaximalSpectrum (Localization (finiteSupportDenominators001
      (residueFiniteSupport318 π hπ hker t)))) ∧
    ∀ (P : Ideal (Localization (finiteSupportDenominators001
      (residueFiniteSupport318 π hπ hker t)))) (_ : P.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime P) ∧
        ringKrullDim (Localization.AtPrime P) = 2 := by
  have ht₀ := residueFiniteSupport_nonempty318 π hπ hker t ht
  refine ⟨inferInstance,
    finiteSupportLocalization_finite_maximalSpectrum001 _ ht₀, ?_⟩
  exact finiteSupportLocalization_maximal_localSurface021 _ ht₀ hreg hdim

/-- Specialize the support-property transport to the ORIGINAL whole ideal.
The residual support is identified with the actual support of J.map π. -/
theorem actualSupportResidueLocalization_surfaceProperties318
    {A A₀ : Type u} [CommRing A] [CommRing A₀] [IsNoetherianRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π)) (J : Ideal A)
    [IsArtinianRing (A ⧸ J)] [Nontrivial (A ⧸ J)]
    [IsArtinianRing (A₀ ⧸ J.map π)]
    (hreg : ∀ Q ∈ actualArtinianQuotientSupport001 (J.map π),
      IsRegularLocalRing (Localization.AtPrime Q.asIdeal))
    (hdim : ∀ Q ∈ actualArtinianQuotientSupport001 (J.map π),
      ringKrullDim (Localization.AtPrime Q.asIdeal) = 2) :
    IsNoetherianRing (Localization (finiteSupportDenominators001
      (residueFiniteSupport318 π hπ hker (actualArtinianQuotientSupport001 J)))) ∧
    Finite (MaximalSpectrum (Localization (finiteSupportDenominators001
      (residueFiniteSupport318 π hπ hker (actualArtinianQuotientSupport001 J))))) ∧
    ∀ (P : Ideal (Localization (finiteSupportDenominators001
      (residueFiniteSupport318 π hπ hker (actualArtinianQuotientSupport001 J)))))
      (_ : P.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime P) ∧
        ringKrullDim (Localization.AtPrime P) = 2 := by
  apply finiteSupportResidueLocalization_surfaceProperties318 π hπ hker
    (actualArtinianQuotientSupport001 J) (actualArtinianQuotientSupport_nonempty001 J)
  · simpa only [residueFiniteSupport_actualSupport318 π hπ hker J] using hreg
  · simpa only [residueFiniteSupport_actualSupport318 π hπ hker J] using hdim

/-- Semilocalizing around the actual support preserves original coefficient
flatness and finiteness of the WHOLE quotient. -/
theorem actualSupportLocalization_originalFiniteFlat318
    {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
    [Module.Flat S A] (J : Ideal A) [IsArtinianRing (A ⧸ J)]
    [Module.Flat S (A ⧸ J)] [Module.Finite S (A ⧸ J)] :
    Module.Flat S (Localization (finiteSupportDenominators001
      (actualArtinianQuotientSupport001 J))) ∧
    Module.Flat S (Localization (finiteSupportDenominators001
      (actualArtinianQuotientSupport001 J)) ⧸ J.map (algebraMap A
        (Localization (finiteSupportDenominators001 (actualArtinianQuotientSupport001 J))))) ∧
    Module.Finite S (Localization (finiteSupportDenominators001
      (actualArtinianQuotientSupport001 J)) ⧸ J.map (algebraMap A
        (Localization (finiteSupportDenominators001 (actualArtinianQuotientSupport001 J))))) := by
  let M := finiteSupportDenominators001 (actualArtinianQuotientSupport001 J)
  let L := Localization M
  let Q := L ⧸ J.map (algebraMap A L)
  have hflat : Module.Flat S L := Module.Flat.trans S A L
  have hqflat : Module.Flat S Q := AllCharacteristics.localizedQuotient_baseFlat318 M J
  let e := (actualArtinianQuotientSemilocalIso001 J).restrictScalars S
  have hqfinite : Module.Finite S Q := Module.Finite.of_surjective e.toLinearMap e.surjective
  exact ⟨hflat, hqflat, hqfinite⟩

end PfaffianDescent
end
