import PfaffianDescent.FiniteSchemeAlgebra
import PfaffianDescent.ClosedImmersionPointLift
import PfaffianDescent.LengthEightLocalSeparableDualClassification
import AllCharacteristics.ClosedPointAlgebra
import AllCharacteristics.FiniteLocalClosedImmersion
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.FieldTheory.Perfect

/-! The ACTUAL global algebra of a supplied finite closed subscheme supported
at one closed point is local. Its residue map onto the ambient point's actual
residue field is surjective. Both facts are derived from the given immersion. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u
variable {X Z : Scheme.{u}}

/-- A source point of the given immersion above its specified full support. -/
def singleSupportSourcePoint (i : Z ⟶ X) (p : X)
    (hSupport : Set.range i = {p}) : Z := by
  have hp : p ∈ Set.range i := by rw [hSupport]; exact Set.mem_singleton p
  exact hp.choose

theorem singleSupportSourcePoint_spec (i : Z ⟶ X) (p : X)
    (hSupport : Set.range i = {p}) :
    i (singleSupportSourcePoint i p hSupport) = p := by
  have hp : p ∈ Set.range i := by rw [hSupport]; exact Set.mem_singleton p
  exact hp.choose_spec

/-- Closed-immersion injectivity and the ACTUAL singleton support force the
source itself to have one point. No reduced replacement is used. -/
theorem singleSupport_subsingleton (i : Z ⟶ X) [IsClosedImmersion i]
    (p : X) (hSupport : Set.range i = {p}) : Subsingleton Z := by
  refine ⟨fun x y => i.isClosedEmbedding.injective ?_⟩
  have hi (z : Z) : i z = p := by
    apply Set.mem_singleton_iff.mp
    rw [← hSupport]
    exact Set.mem_range_self z
  exact (hi x).trans (hi y).symm

/-- An affine supplied singleton-support scheme has a local GLOBAL algebra.
Its actual isoSpec identifies all prime ideals, then maximal ideal uniqueness
supplies the local-ring structure. -/
theorem singleSupport_globalSections_isLocalRing [IsAffine Z]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (p : X) (hSupport : Set.range i = {p}) : IsLocalRing Γ(Z, ⊤) := by
  letI : Subsingleton Z := singleSupport_subsingleton i p hSupport
  letI : Subsingleton (PrimeSpectrum Γ(Z, ⊤)) :=
    Z.isoSpec.inv.homeomorph.injective.subsingleton
  let z := singleSupportSourcePoint i p hSupport
  letI : Nontrivial Γ(Z, ⊤) := PrimeSpectrum.nontrivial (Z.isoSpec.hom z)
  obtain ⟨M, hM⟩ := Ideal.exists_maximal Γ(Z, ⊤)
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨M, hM, ?_⟩
  intro N hN
  exact congrArg PrimeSpectrum.asIdeal
    (Subsingleton.elim (⟨N, hN.isPrime⟩ : PrimeSpectrum Γ(Z, ⊤))
      (⟨M, hM.isPrime⟩ : PrimeSpectrum Γ(Z, ⊤)))

def singleClosedSupportResidueLift (i : Z ⟶ X) [IsClosedImmersion i]
    (p : closedPoints X) (hSupport : Set.range i = {p.1}) :
    Spec (X.residueField p.1) ⟶ Z :=
  let z := singleSupportSourcePoint i p.1 hSupport
  let hz := singleSupportSourcePoint_spec i p.1 hSupport
  Spec.map (X.residueFieldCongr hz).hom ≫ closedImmersionResidueLift i z

theorem singleClosedSupportResidueLift_comp (i : Z ⟶ X) [IsClosedImmersion i]
    (p : closedPoints X) (hSupport : Set.range i = {p.1}) :
    singleClosedSupportResidueLift i p hSupport ≫ i = X.fromSpecResidueField p.1 := by
  dsimp only [singleClosedSupportResidueLift]
  rw [Category.assoc, closedImmersionResidueLift_comp]
  exact Scheme.residueFieldCongr_fromSpecResidueField
    (singleSupportSourcePoint_spec i p.1 hSupport)

/-- The lifted residue point is itself a closed immersion, hence its actual
map on the global algebra is surjective. -/
theorem singleClosedSupportResidueLift_isClosedImmersion
    (i : Z ⟶ X) [IsClosedImmersion i]
    (p : closedPoints X) (hSupport : Set.range i = {p.1}) :
    IsClosedImmersion (singleClosedSupportResidueLift i p hSupport) := by
  let z := singleSupportSourcePoint i p.1 hSupport
  have hz : i z = p.1 := singleSupportSourcePoint_spec i p.1 hSupport
  have hpre : i ⁻¹' {p.1} = {z} := by
    ext y
    change i y = p.1 ↔ y = z
    exact ⟨fun h => i.isClosedEmbedding.injective (h.trans hz.symm), fun h => h ▸ hz⟩
  have hclosed : IsClosed ({z} : Set Z) := hpre ▸ p.2.preimage i.continuous
  letI : IsClosedImmersion (Z.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hclosed
  letI : IsIso (i.residueFieldMap z) :=
    AllCharacteristics.isIso_residueFieldMap_of_surjectiveOnStalks i z
  dsimp only [singleClosedSupportResidueLift, closedImmersionResidueLift]
  infer_instance

section Finite
variable {k : Type u} [Field k] (i : Z ⟶ X) [IsClosedImmersion i]
  (f : X ⟶ Spec (.of k)) [IsFinite (i ≫ f)]
  (p : closedPoints X) (hSupport : Set.range i = {p.1})

/-- The actual residue restriction onto k(P), with its real structure maps. -/
def singleClosedSupportResidueAlgHom :
    letI := finiteSchemeCoefficientAlgebra (i ≫ f)
    letI := AllCharacteristics.pointAlgebra f p.1
    Γ(Z, ⊤) →ₐ[k] X.residueField p.1 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ f)
  letI := AllCharacteristics.pointAlgebra f p.1
  let q := singleClosedSupportResidueLift i p hSupport
  have hq : q ≫ (i ≫ f) = Spec.map (CommRingCat.ofHom
      (algebraMap k (X.residueField p.1))) := by
    rw [← Category.assoc, singleClosedSupportResidueLift_comp,
      AllCharacteristics.pointAlgebra_spec]
  exact finiteSchemePointAlgHom (i ≫ f) q (algebraMap k (X.residueField p.1)) hq

set_option backward.isDefEq.respectTransparency false in
theorem singleClosedSupportResidueAlgHom_surjective :
    letI := finiteSchemeCoefficientAlgebra (i ≫ f)
    letI := AllCharacteristics.pointAlgebra f p.1
    Function.Surjective (singleClosedSupportResidueAlgHom i f p hSupport) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ f)
  letI := AllCharacteristics.pointAlgebra f p.1
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ f)
  letI : IsClosedImmersion (singleClosedSupportResidueLift i p hSupport) :=
    singleClosedSupportResidueLift_isClosedImmersion i p hSupport
  letI : IsClosedImmersion Z.isoSpec.hom := inferInstance
  letI : IsClosedImmersion (singleClosedSupportResidueLift i p hSupport ≫ Z.isoSpec.hom) :=
    IsClosedImmersion.comp _ _
  exact AllCharacteristics.spec_preimage_surjective_of_closedImmersion
    (singleClosedSupportResidueLift i p hSupport ≫ Z.isoSpec.hom)

/-- For an arbitrary supplied rank-eight scheme supported at an actual
separable quartic point, its OWN global algebra is dual numbers over k(P).
Locality, residue surjectivity, and the coefficient-field section are derived. -/
theorem singleClosedSupport_rankEight_dualAlgebra [PerfectField k]
    [LocallyOfFiniteType f] (hSupport : Set.range i = {p.1})
    (hP : f.residueDegree p.1 = 4)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ f) = 8) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ f)
    letI := AllCharacteristics.pointAlgebra f p.1
    Nonempty (DualNumber (X.residueField p.1) ≃ₐ[k] Γ(Z, ⊤)) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ f)
  letI := AllCharacteristics.pointAlgebra f p.1
  letI := finiteSchemeCoefficient_finite (i ≫ f)
  letI := AllCharacteristics.closedPoint_moduleFinite f p
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ f)
  letI : IsLocalRing Γ(Z, ⊤) := singleSupport_globalSections_isLocalRing i p.1 hSupport
  have hL : finrank k (X.residueField p.1) = 4 :=
    (AllCharacteristics.closedPoint_finrank_eq_residueDegree f p).trans hP
  have hA : finrank k Γ(Z, ⊤) = 8 :=
    (finiteSchemeCoefficient_finrank (i ≫ f)).trans hZ
  exact lengthEightLocal_quarticResidue_dual_equiv
    (singleClosedSupportResidueAlgHom i f p hSupport)
    (singleClosedSupportResidueAlgHom_surjective i f p hSupport) hL hA

end Finite
end PfaffianDescent
